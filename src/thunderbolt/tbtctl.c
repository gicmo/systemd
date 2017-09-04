/***
  This file is part of systemd.

  Copyright 2017 Christian J. Kellner

  systemd is free software; you can redistribute it and/or modify it
  under the terms of the GNU Lesser General Public License as published by
  the Free Software Foundation; either version 2.1 of the License, or
  (at your option) any later version.

  systemd is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
  Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public License
  along with systemd; If not, see <http://www.gnu.org/licenses/>.
***/

#include "thunderbolt.h"

#include <getopt.h>
#include <linux/fs.h>
#include <locale.h>
#include <sys/ioctl.h>
#include <sys/sendfile.h>

#include "conf-parser.h"
#include "chattr-util.h"
#include "dirent-util.h"
#include "efivars.h"
#include "fd-util.h"
#include "fs-util.h"
#include "fileio.h"
#include "hash-funcs.h"
#include "io-util.h"
#include "locale-util.h"
#include "mkdir.h"
#include "parse-util.h"
#include "random-util.h"
#include "set.h"
#include "stdio-util.h"
#include "string-table.h"
#include "string-util.h"
#include "terminal-util.h"
#include "udev-util.h"
#include "umask-util.h"
#include "util.h"

struct CtlCmd {
        const char *name;
        int       (*func) (struct udev *udev, int argc, char *argv[]);
        const char *desc;
        bool        root;
};


#define FORMAT_SECURITY_MAX 2 /* one digit plus nul */
#define HEX_BYTES 3            /* xx plus nul */
#define KEY_BYTES 32
#define KEY_CHARS 64          /* KEY_BYTES hex encoded */


/* the strings here correspond to the values reported
 * in sysfs ('security' attribute) for the domain  */
static const char* const security_table[_SECURITY_MAX] = {
        [SECURITY_NONE]    = "none",
        [SECURITY_USER]    = "user",
        [SECURITY_SECURE]  = "secure",
        [SECURITY_DPONLY]  = "dponly",
};
DEFINE_PRIVATE_STRING_TABLE_LOOKUP(security, SecurityLevel);

void auth_reset(Auth *a) {
        a->key = string_free_erase(a->key);
        a->level = AUTH_MISSING;
        a->store = 0;
}

void auth_generate_key_string(Auth *a) {
        uint8_t rnddata[KEY_BYTES];
        char *keydata;
        int i;

        random_bytes(rnddata, KEY_BYTES);

        keydata = malloc(KEY_CHARS + 1);
        for (i = 0; i < KEY_BYTES; i++)
                snprintf(keydata + i*2, HEX_BYTES, "%02hhx", rnddata[i]);

        a->key = keydata;
        a->store = STORE_NONE;
}

void tb_device_free(TbDevice **device) {
        TbDevice *d;

        if (!*device)
                return;

        d = *device;

        free(d->uuid);
        free(d->name);
        free(d->vendor);

        if (d->udev)
                udev_device_unref(d->udev);
        if (d->devdir)
                (void) closedir(d->devdir);

        free(d);
        *device = NULL;
}

// -1, a < b; 0, a == b; 1, a > b
int tb_device_compare(const void *ia, const void *ib) {
        const TbDevice *a = ia;
        const TbDevice *b = ib;
        const char *pa, *pb;
        size_t la, lb;

        assert(a);
        assert(b);

        if (!a->udev && !b->udev)
                return strcmp_ptr(a->name, b->name);
        else if (!b->udev)
                return -1;
        else if (!a->udev)
                return 1;

        /* both have udev devices */
        assert(a->udev);
        assert(b->udev);

        pa = udev_device_get_syspath(a->udev);
        pb = udev_device_get_syspath(b->udev);

        la = strlen_ptr(pa);
        lb = strlen_ptr(pb);

        if (la != lb)
                return la - lb;

        /* sysfs path is same length, i.e. siblings */
        return strcmp_ptr(pa, pb);
}

static int tb_device_ptr_compare(const void *pa, const void *pb) {
        const TbDevice **a = (const TbDevice **) pa;
        const TbDevice **b = (const TbDevice **) pb;

        return tb_device_compare(*a, *b);
}

static void tb_device_hash_func(const void *p, struct siphash *state) {
        const TbDevice *d = p;
        siphash24_compress(d->uuid, strlen(d->uuid) + 1, state);
}

const struct hash_ops tb_device_hash_ops = {
        .hash = tb_device_hash_func,
        .compare = tb_device_compare,

};

SecurityLevel tb_device_get_security_level(TbDevice *device) {
        struct udev_device *parent;
        const char *security;
        bool found;

        found = false;
        parent = device->udev;
        do {
                const char *name;
                parent = udev_device_get_parent(parent);
                if (!parent)
                        break;

                name = udev_device_get_sysname(parent);
                found = startswith(name, "domain");

        } while (!found);

        if (!found)
                return _SECURITY_INVALID;

        security = udev_device_get_sysattr_value(parent, "security");
        if (!security)
                return _SECURITY_INVALID;

        return security_from_string(security);
}

static int read_single_line_at(int dirfd, const char *name, char **l_out) {
   _cleanup_fclose_ FILE *fp = NULL;
        char line[LINE_MAX], *l;
        int fd;

        fd = openat(dirfd, name, O_NOFOLLOW|O_CLOEXEC|O_RDONLY);
        if (fd < 0)
                return -errno;

        fp = fdopen(fd, "re");
        if (!fp)
                return -errno;

        l = fgets(line, sizeof(line), fp);
        if (!l) {
                if (ferror(fp))
                        return errno > 0 ? -errno : -EIO;

                line[0] = '\0';
        }

        l = strdup(truncate_nl(line));
        if (!l)
                return -ENOMEM;

        *l_out = l;
        return 0;
}

static char *get_sysattr_name(struct udev_device *udev, const char *attr) {
        char *s;
        const char *v;

        s = strjoina(attr, "_name");
        v = udev_device_get_sysattr_value(udev, s);
        if (v == NULL)
                v = udev_device_get_sysattr_value(udev, attr);
        if (v == NULL)
                return NULL;

        return strdup(v);
}

int tb_device_new_from_udev(struct udev_device *udev, TbDevice **ret) {
        _cleanup_tb_device_free_ TbDevice *d = NULL;
        _cleanup_free_ char *val = NULL;
        const char *syspath;
        int r;

        d = new0(TbDevice, 1);
        if (!d)
                return -ENOMEM;

        syspath = udev_device_get_syspath(udev);
        d->devdir = opendir(syspath);
        if (!d->devdir)
                return -errno;

        r = read_single_line_at(dirfd(d->devdir), "unique_id", &d->uuid);
        if (r < 0)
                return r;

        r = read_single_line_at(dirfd(d->devdir), "authorized", &val);
        if (r < 0)
                return r;

        r = safe_atoi(val, &d->authorized);
        if (r < 0)
                return r;

        d->udev = udev_device_ref(udev);
        d->name = get_sysattr_name(udev, "device");
        d->vendor = get_sysattr_name(udev, "vendor");

        if (!d->name || !d->vendor)
                return -ENOMEM;

        *ret = d;
        d = NULL;

        return 0;
}

int tb_device_new_from_syspath(struct udev *udev, const char *path, TbDevice **d) {
        _cleanup_udev_device_unref_ struct udev_device *udevice = NULL;

        udevice = udev_device_new_from_syspath(udev, path);
        if (udevice == NULL)
                return -ENODEV;

        return tb_device_new_from_udev(udevice, d);
}

int tb_device_authorize(TbDevice *dev, Auth *auth) {
        char buf[FORMAT_SECURITY_MAX];
        _cleanup_close_ int fd = -1;
        AuthLevel l;
        ssize_t n;
        int dfd;

        assert(dev);
        assert(auth);
        assert(auth->level > 0);

        if (dev->devdir == NULL)
                return -EINVAL;

        dfd = dirfd(dev->devdir);
        l = auth->level;

        if (l == AUTH_KEY) {
                _cleanup_close_ int key_fd = -1;

                if (auth->key == NULL)
                        return -EINVAL;

                key_fd = openat(dfd, "key", O_WRONLY|O_CLOEXEC);
                if (key_fd < 0)
                        return -errno;

                n = write(key_fd, auth->key, KEY_CHARS);

                if (n < 0)
                        return -errno;
                else if (n != KEY_CHARS)
                        return -EIO;

                /* if the key is not stored, we need to use
                 * AUTH_USER to write the new key to the device */
                if (auth->store == STORE_NONE)
                        l = AUTH_USER;

        }

        fd = openat(dfd, "authorized", O_WRONLY|O_CLOEXEC);
        if (fd < 0)
                return -errno;

        xsprintf(buf, "%hhu", (uint8_t) l);
        n = write(fd, buf, 1);

        if (n < 0)
                return -errno;
        else if (n != 1)
                return -EIO;

        return 0;
}

bool tb_device_is_online(TbDevice *dev) {
        assert(dev);

        return dev->udev != NULL;
}

void tb_store_free(TbStore **store) {
        TbStore *s;

        if (!store)
                return;

        s = *store;

        free(s->path);
        free(s);
        *store = NULL;
}

int tb_store_new(TbStore **ret) {
        _cleanup_tb_store_free_ TbStore *s = NULL;
        const char *val;

        s = new0(TbStore, 1);
        if (!s)
                return -ENOMEM;

        val = getenv("SYSTEMD_THUNDERBOLT_DB_PATH");

        if (val)
                s->path = strdup(val);
        else
                s->path = strdup(TB_STORE_PATH);

        s->store = STORE_EFIVARS;

        *ret = s;
        s = NULL;

        return 0;
}


static int tb_store_parse_device(TbStore *store, TbDevice *device) {
        const ConfigTableItem items[] = {
                { "device", "name",    config_parse_string,  0, &device->name    },
                { "device", "vendor",  config_parse_string,  0, &device->vendor  },
                {}
        };
        _cleanup_fclose_ FILE *f = NULL;
        _cleanup_close_ int fd = -1;
        struct stat st;
        char *path;
        int r;

        assert(device);
        assert(device->uuid);

        path = strjoina(store->path, "/devices/", device->uuid);

        fd = open(path, O_RDONLY|O_CLOEXEC|O_NOCTTY|O_NOFOLLOW);
        if (fd < 0)
                return -errno;
        if (fstat(fd, &st) < 0)
                return -errno;
        if (S_ISDIR(st.st_mode))
                return -EISDIR;
        if (!S_ISREG(st.st_mode))
                return -ENOTTY;

        f = fdopen(fd, "re");
        if (f == NULL)
                return -errno;

        r = config_parse(NULL, path, f,
                         NULL,
                         config_item_table_lookup, items,
                         true, true, false, device);
        if (r < 0)
                return log_debug_errno(r, "Failed to parse %s: %m", device->uuid);

        return 0;
}

int tb_store_device_load(TbStore *store, const char *uuid, TbDevice **device) {
        TbDevice *d = NULL;
        int r;

        assert(store);
        assert(device);
        assert(uuid);

        d = new0(TbDevice, 1);
        if (!d) {
                r = -ENOMEM;
                goto out;
        }

        d->uuid = strdup(uuid);
        if (d->uuid == NULL) {
                r = -ENOMEM;
                tb_device_free(&d);
                goto out;
        }

        r = tb_store_parse_device(store, d);
        if (r < 0) {
                tb_device_free(&d);
        }

 out:
        *device = d;
        return r;
}


static int store_efivars_get_auth(const char *uuid, Auth *ret) {
        _cleanup_free_ void *var = NULL;
        sd_id128_t id;
        size_t l;
        int r;

        assert(ret);
        assert(uuid);

        if (sd_id128_from_string(uuid, &id) < 0) {
                return -EINVAL;
        }

        r = efi_get_variable(id, "Thunderbolt", NULL, &var, &l);
        if (r < 0)
                return r;

        ret->store = STORE_EFIVARS;
        if (l == 1) {
                return safe_atoi(var, &ret->level);
        } else if (l == KEY_CHARS) {
                ret->level = AUTH_KEY;
                ret->key = (char *) var;
                var = NULL;
                return 0;
        }

        /* should not happen, because only we write it */
        return -EIO;
}

int store_get_auth(TbStore *store, const char *uuid, Auth *ret) {
        _cleanup_free_ char *p = NULL;
        struct stat st;
        char *path;
        int r;

        if (in_initrd())
                return store_efivars_get_auth(uuid, ret);

        path = strjoina(store->path, "/authorization/", uuid);

        r = lstat(path, &st);
        if (r < 0 && errno == ENOENT) {
                ret->level = AUTH_MISSING;
                return 0;
        }
        if (r < 0)
                return -errno;
        if (S_ISREG(st.st_mode)) {
                ret->level = AUTH_USER;
                ret->store = STORE_FSDB;
                return 0;
        }

        r = readlink_malloc(path, &p);
        if (r < 0)
                return r;

        r = -ENOTSUP;
        if (startswith(p, "/sys/firmware/efi/efivars")) {
                r = store_efivars_get_auth(uuid, ret);
        } else if (startswith(p, store->path)) {
                r = -ENOTSUP;
        }

        if (r == -ENOTSUP) {
                ret->level = AUTH_MISSING;
                ret->store = STORE_NONE;
        }

        return r;
}

#define ID128_UUID_FMT "%02x%02x%02x%02x-%02x%02x-%02x%02x-%02x%02x-%02x%02x%02x%02x%02x%02x"

#define TB_EFIVAR_PATH_PREFIX "/sys/firmware/efi/efivars/Thunderbolt-"
#define TB_EFIVAR_PATH TB_EFIVAR_PATH_PREFIX ID128_UUID_FMT

static int store_efivars_put_auth(TbStore *store,
                                  const char *uuid,
                                  Auth *auth) {
        _cleanup_free_ char *target = NULL;
        char buf[FORMAT_SECURITY_MAX];
        sd_id128_t id;
        char *path;
        int r;


        if (sd_id128_from_string (uuid, &id) < 0) {
                return -EINVAL;
        }

        if (auth->level == AUTH_KEY) {
                r = efi_set_variable(id, "Thunderbolt", auth->key, KEY_CHARS);
        } else {
                xsprintf(buf, "%hhu", (uint8_t) auth->level);
                r = efi_set_variable(id, "Thunderbolt", buf, 1);
        }

        if (r < 0)
                return r;

        if (asprintf(&target, TB_EFIVAR_PATH, SD_ID128_FORMAT_VAL(id)) < 0)
                 return -ENOMEM;

        path = strjoina(store->path, "/authorization/", uuid);

        r = mkdir_parents(path, 0755);
        if (r < 0)
                return r;

        return symlink_idempotent(target, path);
}


static int store_fsdb_put_auth(TbStore *store,
                               const char *uuid,
                               Auth *auth) {

        return -ENOTSUP;
}


static int store_put_device(TbStore *store,
                            TbDevice *device,
                            Auth *auth) {
        _cleanup_fclose_ FILE *f = NULL;
        const char *uuid;
        char *path;
        int r;

        uuid = device->uuid;

        switch (store->store) {
        case STORE_FSDB:
                r = store_fsdb_put_auth(store, uuid, auth);
                break;

        case STORE_EFIVARS:
                r = store_efivars_put_auth(store, uuid, auth);
                break;

        default:
                r = -ENOTSUP;
        }

        if (r < 0)
                return r;

        path = strjoina(store->path, "/devices/", uuid);
        r = mkdir_parents(path, 0644);
        if (r < 0)
                return r;

        f = fopen(path, "we");
        if (f == NULL)
                return -errno;

        fputs("[device]\n", f);
        fputs(" name=", f);
        fputs(device->name, f);
        fputs("\n vendor=", f);
        fputs(device->vendor, f);
        fputs("\n", f);

        return fflush_and_check(f);
}

bool tb_store_have_device(TbStore *store, const char *uuid) {
        char *p;
        struct stat st;

        if (in_initrd()) {
                p = strjoina(TB_EFIVAR_PATH_PREFIX, uuid);
        } else {
                p = strjoina(store->path, "/devices/", uuid);
        }

        return stat(p, &st) == 0;
}

int tb_store_list_ids(TbStore *store, char ***ret) {
        _cleanup_closedir_ DIR *d = NULL;
        struct dirent *de;
        char *p;

        assert(store);
        assert(ret);
        *ret = NULL;

        p = strjoina(store->path, "/devices/");
        d = opendir(p);
        if (!d)
                return errno == ENOENT ? true : -errno;

        FOREACH_DIRENT(de, d, return -errno) {
                strv_extend(ret, de->d_name);
        }

        return 0;
}

static int tb_store_load_missing(TbStore *store, Hashmap *devices) {
        char **ids = NULL;
        char **i;
        TbDevice *device;

        int r;
        r = tb_store_list_ids(store, &ids);
        if (r < 0)
                return r;

        STRV_FOREACH(i, ids) {
                const char *id = *i;
                if (hashmap_contains(devices, id))
                        continue;

                r = tb_store_device_load(store, id, &device);
                if (r < 0) {
                        log_warning_errno(r, "Could not load device %s from DB: %m", id);
                        continue;
                }

                hashmap_put(devices, device->uuid, device);
        }

        return 0;
}

int tb_store_remove_auth(TbStore *store, const char *uuid) {
        _cleanup_free_ char *p = NULL;
        struct stat st;
        char *path;
        int r;

        if (in_initrd())
                return -EPERM;

        path = strjoina(store->path, "/authorization/", uuid);

        r = lstat(path, &st);
        if (r < 0)
                return -errno;

        if (S_ISREG(st.st_mode)) {
                r = unlink(path);
                return r < 0 ? -errno : 0;
        }

        r = readlink_malloc(path, &p);
        if (r < 0)
                return r;

        if (startswith(p, "/sys/firmware/efi/efivars")) {
                r = chattr_path(p, 0, FS_IMMUTABLE_FL);
                if (r < 0)
                        return r;
        }

        r = unlink(p);
        if (r < 0) {
                return -errno;
        }

        r = unlink(path);
        return r < 0 ? -errno : 0;
}

int tb_store_remove_device(TbStore *store, const char *uuid) {
        char *p;
        int r;

        if (in_initrd())
                return -EPERM;

        p = strjoina(store->path, "/devices/", uuid);
        r = unlink(p);
        if (r < 0)
                return -errno;

        return 0;
}

static void device_print(TbStore *store, TbDevice *device)
{
        SecurityLevel security;
        Auth auth = AUTH_INITIALIZER;
        const char *status;
        const char *st_sym, *st_con, *st_coff;
        const char *policy_str;
        int r;
        bool in_store;

        if (device->authorized == AUTH_MISSING) {
                status = "offline";
                st_con = ansi_highlight_blue();;
                st_sym = special_glyph(BLACK_CIRCLE);
        } else if (device->authorized == AUTH_NEEDED) {
                status = "unauthorized";
                st_con = ansi_highlight_yellow();
                st_sym = special_glyph(BLACK_CIRCLE);
        } else if (device->authorized == AUTH_USER) {
                status = "authorized (user)";
                st_con = ansi_highlight_green();
                st_sym = special_glyph(BLACK_CIRCLE);
        } else if (device->authorized ==  AUTH_KEY) {
                status = "authorized (key)";
                st_con = ansi_highlight_green();
                st_sym = special_glyph(BLACK_CIRCLE);
        } else {
                status = "unknown authorization";
                st_con = ansi_highlight_red();
                st_sym = special_glyph(BLACK_CIRCLE);
        }

        st_coff = ansi_normal();

        printf("%s%s%s %s\n", st_con, st_sym, st_coff, device->name);
        printf("  %s vendor:     %s\n", special_glyph(TREE_BRANCH), device->vendor);
        printf("  %s uuid:       %s\n", special_glyph(TREE_BRANCH), device->uuid);
        printf("  %s status:     %s\n", special_glyph(TREE_BRANCH), status);

        if (tb_device_is_online(device)) {
                printf("  %s security:   ", special_glyph(TREE_BRANCH));

                security = tb_device_get_security_level(device);
                if (security == _SECURITY_INVALID)
                        printf("unknown\n");
                else
                        printf("%s\n", security_to_string(security));
        }

        in_store = tb_store_have_device(store, device->uuid);
        printf("  %s in store:   %s\n", special_glyph(TREE_RIGHT), yes_no(in_store));

        if (!in_store)
                goto out;

        r = store_get_auth(store, device->uuid, &auth);
        if (r < 0)
                policy_str = "error";
        else if (!auth_level_can_authorize(auth.level))
                policy_str = "ignore";
        else if (auth.level == AUTH_USER)
                policy_str = "authorize (user)";
        else if (auth.level == AUTH_KEY)
                policy_str = "authorize (key)";

        printf("     %s policy:  %s\n", special_glyph(TREE_BRANCH), policy_str);
        printf("     %s key:     %s\n", special_glyph(TREE_RIGHT), yes_no(!!auth.key));

 out:
        printf("\n");
}

static int list_devices_udev(struct udev *udev, Hashmap **ret) {
        _cleanup_udev_enumerate_unref_ struct udev_enumerate *enumerate = NULL;
        struct udev_list_entry *list_entry = NULL, *first = NULL;
        int r;

        r = hashmap_ensure_allocated(ret, &string_hash_ops);
        if (r < 0)
                return r;

        enumerate = udev_enumerate_new(udev);
        if (enumerate == NULL)
                return -ENOMEM;

        r = udev_enumerate_add_match_subsystem(enumerate, "thunderbolt");
        if (r < 0)
                return r;

        r = udev_enumerate_add_match_sysattr(enumerate, "unique_id", NULL);
        if (r < 0)
                return r;

        r = udev_enumerate_scan_devices(enumerate);
        if (r < 0)
                return r;

        first = udev_enumerate_get_list_entry(enumerate);
        udev_list_entry_foreach(list_entry, first) {
                TbDevice *device;
                const char *name;

                name = udev_list_entry_get_name(list_entry);
                r = tb_device_new_from_syspath(udev, name, &device);
                if (r < 0)
                        continue;

                hashmap_put(*ret, device->uuid, device);
        }

        return 0;
}

static TbDevice **devices_to_sorted_array(Hashmap *devices, unsigned *size) {
        TbDevice **dl = NULL;
        TbDevice *device;
        TbDevice **i;
        Iterator iter;
        unsigned n;

        n = hashmap_size(devices);
        dl = i = new(TbDevice *, n);

        HASHMAP_FOREACH(device, devices, iter)
                *i++ = device;

        qsort(dl, n, sizeof(TbDevice *), tb_device_ptr_compare);
        *size = n;

        return dl;
}

static int list_devices(struct udev *udev, int argc, char *argv[]) {
        _cleanup_hashmap_free_ Hashmap *devices = NULL;
        _cleanup_tb_store_free_ TbStore *store = NULL;
        _cleanup_free_ TbDevice **dl = NULL;
        TbDevice *device = NULL;
        unsigned i, n;
        int c, r;
        bool show_all = false;

        static const struct option options[] = {
                { "all",    no_argument, NULL, 'a' },
                {}

        };

        while ((c = getopt_long(argc, argv, "ah", options, NULL)) >= 0)
                switch (c) {
                case 'a':
                        show_all = true;
                        break;
                case 'h':
                        fprintf(stderr, "FIXME: need help\n");
                        return EXIT_SUCCESS;
                default:
                        return EXIT_FAILURE;

                }

        r = tb_store_new(&store);
        if (r < 0) {
                log_error_errno(r, "Couldn't open store: %m");
                return EXIT_FAILURE;
        }

        r = list_devices_udev(udev, &devices);
        if (r < 0) {
                log_error_errno(r, "Could not list devices from udev: %m");
                return EXIT_FAILURE;
        }

        if (show_all) {
                r = tb_store_load_missing(store, devices);
                if (r < 0)
                        log_error_errno(r, "Could not load devices from DB: %m");
        }

        dl = devices_to_sorted_array(devices, &n);
        if (dl == NULL) {
                log_oom();
                return EXIT_FAILURE;
        }

        for (i = 0; i < n; i++) {
                device = dl[i];
                device_print(store, device);
                tb_device_free(&device);
        }

        return EXIT_SUCCESS;
}

static const struct CtlCmd cmd_list = {
        .name = "list",
        .func = list_devices,
        .desc = "List thunderbolt devices",
};

static int authorize_user(struct udev *udev, int argc, char *argv[]) {
        _cleanup_tb_device_free_ TbDevice *device = NULL;
        _cleanup_auth_reset_ Auth auth = { 0, };
        _cleanup_tb_store_free_ TbStore *store = NULL;
        SecurityLevel sl;
        int r;

        if (argc < 2) {
                fprintf(stderr, "%s: need sysfs path\n",
                        program_invocation_short_name);
                return EXIT_FAILURE;
        }

        r = tb_store_new(&store);
        if (r < 0) {
                log_error_errno(r, "Couldn't open store: %m");
                return EXIT_FAILURE;
        }

        r = tb_device_new_from_syspath(udev, argv[1], &device);
        if (r < 0) {
                log_error_errno(r, "Couldn't open device: %m");
                return EXIT_FAILURE;
        }

        if (device->authorized != AUTH_NEEDED) {
                log_error("Device already authorized");
                return EXIT_FAILURE;
        }

        sl = tb_device_get_security_level(device);
        if (sl < 0) {
                log_error_errno(r, "Failed to get host controller security level");
                return EXIT_FAILURE;
        }
        if (sl != SECURITY_USER && sl != SECURITY_SECURE) {
                log_error("Security level of controller insufficient");
                return EXIT_FAILURE;
        }

        r = store_get_auth(store, device->uuid, &auth);
        if (r < 0) {
                log_error_errno(r, "Failed to read authorization from store: %m");
                return EXIT_FAILURE;
        }

        if (auth.level == AUTH_MISSING)
                auth.level = sl;
        if (auth.level == AUTH_KEY && auth.key == NULL)
                auth_generate_key_string(&auth);

        r = tb_device_authorize(device, &auth);
        if (r < 0) {
                log_error_errno(r, "Failed to authorize device: %m");
                return EXIT_FAILURE;
        }

        if (auth.store != STORE_NONE)
                return EXIT_SUCCESS;

        r = store_put_device(store, device, &auth);
        if (r < 0) {
                log_error_errno(r, "Failed to commit device to store: %m");
                return EXIT_FAILURE;
        }

        return EXIT_SUCCESS;
}

static const struct CtlCmd cmd_authorize = {
        .name = "authorize",
        .func = authorize_user,
        .desc = "Authorize a thunderbolt device",
        .root = true,
};

static int authorize_udev(struct udev *udev, int argc, char *argv[]) {
        _cleanup_tb_device_free_ TbDevice *device = NULL;
        _cleanup_tb_store_free_ TbStore *store = NULL;
        _cleanup_auth_reset_ Auth auth = AUTH_INITIALIZER;
        SecurityLevel sl;
        int r;

        if (argc < 2) {
                fprintf(stderr, "%s: need sysfs path\n",
                        program_invocation_short_name);
                return EXIT_FAILURE;
        }

        r = tb_store_new(&store);
        if (r < 0) {
                log_error_errno(r, "Couldn't open store: %m");
                return EXIT_FAILURE;
        }

        r = tb_device_new_from_syspath(udev, argv[1], &device);
        if (r < 0) {
                log_error_errno(r, "Couldn't open device: %m");
                return EXIT_FAILURE;
        }

        r = store_get_auth(store, device->uuid, &auth);
        if (r < 0) {
                log_error_errno(r, "Failed to load authorization: %m");
                return EXIT_FAILURE;
        }

        if (!auth_level_can_authorize(auth.level)) {
                log_debug("Unknown or ignored device: %s", device->uuid);
                /* Unknown or ignored device */
                return EXIT_SUCCESS;
        }

        sl = tb_device_get_security_level(device);
        if (sl < 0) {
                log_error_errno(sl, "Failed to determine security level");
                return EXIT_FAILURE;
        }

        if (sl != SECURITY_USER && sl != SECURITY_SECURE) {
                log_debug("Security level of controller insufficient");
                /* not an error here */
                return EXIT_SUCCESS;
        }

        auth.level = MIN(auth.level, sl);

        r = tb_device_authorize(device, &auth);
        if (r < 0) {
                log_error_errno(r, "Failed to authorize device: %m");
                return EXIT_FAILURE;
        }

        return EXIT_SUCCESS;
}

static const struct CtlCmd cmd_udev = {
        .name = "udev",
        .func = authorize_udev,
        .desc = "internal command for udev rules",
        .root = true,
};


static int forget_device(struct udev *udev, int argc, char *argv[]) {
        _cleanup_tb_store_free_ TbStore *store = NULL;
        const char *uuid;
        int r;

        if (argc < 2) {
                fprintf(stderr, "%s: need device uuid\n",
                        program_invocation_short_name);
                return EXIT_FAILURE;
        }

        uuid = argv[1];

        r = tb_store_new(&store);
        if (r < 0) {
                log_error_errno(r, "Couldn't open store: %m");
                return EXIT_FAILURE;
        }

        r = tb_store_remove_auth(store, uuid);
        if (r < 0 && errno != -ENOENT) {
                log_error_errno(r, "Could not remove authorization: %m");
                return EXIT_FAILURE;
        }

        r = tb_store_remove_device(store, uuid);
        if (r < 0) {
                log_error_errno(r, "Could not remove device: %m");
                return EXIT_FAILURE;
        }

        return EXIT_SUCCESS;
}

static const struct CtlCmd cmd_forget = {
        .name = "forget",
        .func = forget_device,
        .desc = "Remove a device from the database",
        .root = true,
};

static const struct CtlCmd *ctrl_cmds[] = {
        &cmd_list,
        &cmd_authorize,
        &cmd_forget,

        &cmd_udev
};


static void help(void) {
        unsigned int i;

        printf("%s [--version] [--debug] COMMAND [OPTIONS]\n\n"
               "Manager thunderbolt devices\n\n"
               "  -h --help             Show this help and exit\n"
               "  --version             Print version string and exit\n"
               "\n"
               "Commands:\n"
               , program_invocation_short_name);

        for (i = 0; i < ELEMENTSOF(ctrl_cmds); i++) {
                const struct CtlCmd *cmd = ctrl_cmds[i];
                if (!cmd->desc)
                        continue;

                printf("  %-20s  %s\n", cmd->name, cmd->desc);
        }
}


#define ARG_VERSION 0x100

int main(int argc, char *argv[]) {
        _cleanup_udev_unref_ struct udev *udev = NULL;
        const char *cmdname;
        const struct CtlCmd *cmd;
        static const struct option options[] = {
                { "debug",   no_argument, NULL, 'd' },
                { "help",    no_argument, NULL, 'h' },
                { "version", no_argument, NULL, ARG_VERSION },
                {}
        };
        unsigned int i;
        int c, r;

        setlocale(LC_ALL, "");
        log_parse_environment();
        log_open();

        while ((c = getopt_long(argc, argv, "+dhV", options, NULL)) >= 0)
                switch (c) {

                case 'd':
                        log_set_max_level(LOG_DEBUG);
                        break;

                case 'h':
                        help();
                        return EXIT_SUCCESS;

                case ARG_VERSION:
                        version();
                        return EXIT_SUCCESS;;

                default:
                        assert_not_reached("Unhandled option");
                }


        cmdname = argv[optind];

        if (!cmdname) {
                fprintf(stderr, "%s: need to specify command\n", program_invocation_short_name);
                fprintf(stderr, "  use --help for available commands\n");
                return EXIT_FAILURE;
        }

        cmd = NULL;
        for (i = 0; i < ELEMENTSOF(ctrl_cmds); i++) {
                if (streq(ctrl_cmds[i]->name, cmdname)) {
                        cmd = ctrl_cmds[i];
                        break;
                }
        }

        if (!cmd) {
                fprintf(stderr, "%s: invalid command: %s\n",
                        program_invocation_short_name, cmdname);
                fprintf(stderr, "  use --help for available commands\n");
                return EXIT_FAILURE;
        }

        if (cmd->root && geteuid() != 0) {
                fprintf(stderr, "%s %s must be invoked as root.\n",
                program_invocation_short_name, cmdname);
                return EXIT_FAILURE;
        }

        udev = udev_new();
        if (!udev) {
                log_oom();
                return EXIT_FAILURE;
        }


        argc -= optind;
        argv += optind;
        optind = 0;

        r = cmd->func(udev, argc, argv);

        return r;
}
