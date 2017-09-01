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

#include <getopt.h>
#include <locale.h>
#include <sys/sendfile.h>

#include "libudev.h"

#include "conf-parser.h"
#include "efivars.h"
#include "fd-util.h"
#include "fs-util.h"
#include "fileio.h"
#include "io-util.h"
#include "locale-util.h"
#include "mkdir.h"
#include "parse-util.h"
#include "random-util.h"
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


static inline const char* strunknown(const char *s) {
        return s ? s : "unknown";
}

static int read_one_line_consume_fd(int fd, char **line_out) {
        _cleanup_fclose_ FILE *fp = NULL;
        char line[LINE_MAX], *l;

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

        *line_out = l;
        return 0;
}

/*  */

typedef enum SecurityLevel {
        SECURITY_NONE    = 0,
        SECURITY_USER    = 1,
        SECURITY_SECURE  = 2,
        SECURITY_DPONLY  = 3,
        _SECURITY_MAX,
        _SECURITY_INVALID = -1,
} SecurityLevel;

/* the strings here correspond to the values reported
 * in sysfs ('security' attribute) for the domain  */
static const char* const security_table[_SECURITY_MAX] = {
        [SECURITY_NONE]    = "none",
        [SECURITY_USER]    = "user",
        [SECURITY_SECURE]  = "secure",
        [SECURITY_DPONLY]  = "dponly",
};
DEFINE_PRIVATE_STRING_TABLE_LOOKUP(security, SecurityLevel);

static SecurityLevel device_get_security_level(struct udev_device *device) {
        struct udev_device *parent;
        const char *security;
        bool found;

        found = false;
        parent = device;
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


typedef enum KeyStore {
        TBT_KEYSTORE_EFIVARS,
        TBT_KEYSTORE_FSDB,
} KeyStore;

enum {
        AUTHORIZED_MISSING = 0,
        AUTHORIZED_USER = 1,
        AUTHORIZED_KEY = 2,
};

typedef struct Authorization {
        unsigned level; /* corresponds to sysfs 'authorized' value */
        char *key;
        KeyStore store;
} Authorization;

static void authorization_reset(Authorization *a) {
        a->key = string_free_erase(a->key);
        a->level = AUTHORIZED_MISSING;
        a->store = 0;
}

#define _cleanup_authorization_reset_ _cleanup_(authorization_reset)

typedef struct {

        char *uuid;

        char *name;
        char *vendor;

} TbtDevice;

static void tbt_device_free(TbtDevice **device) {
        TbtDevice *d;

        if (!*device)
                return;

        d = *device;

        free(d->uuid);
        free(d->name);
        free(d->vendor);
        free(d);

        *device = NULL;
}

#define _cleanup_tbt_device_ _cleanup_(tbt_device_free)

#define TBT_STORE_PATH "/var/lib/tbt/"

typedef struct TbtStore TbtStore;

struct TbtStore {
        char *path;
        KeyStore keystore;
};

static void tbt_store_free(TbtStore *s) {
        if (!s)
                return;

        free(s->path);
        free(s);
}

DEFINE_TRIVIAL_CLEANUP_FUNC(TbtStore*, tbt_store_free);
#define _cleanup_store_free_ _cleanup_(tbt_store_freep)

static int tbt_store_new(TbtStore **ret) {
        _cleanup_store_free_ TbtStore *s = NULL;

        s = new0(TbtStore, 1);
        if (!s)
                return -ENOMEM;


        s->path = strdup("/etc/thunderbolt");
        s->keystore = TBT_KEYSTORE_EFIVARS;

        *ret = s;
        s = NULL;

        return 0;
}


static int tbt_store_parse_device(TbtDevice *device) {
        const ConfigTableItem items[] = {
                { "device", "name",         config_parse_string,           0, &device->name       },
                { "device", "vendor-name",  config_parse_string,           0, &device->vendor     },
                {}
        };
        _cleanup_fclose_ FILE *f = NULL;
        _cleanup_close_ int fd = -1;
        struct stat st;
        char *path;
        int r;

        assert(device);
        assert(device->uuid);

        path = strjoina(TBT_STORE_PATH, "devices/", device->uuid);

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

static int tbt_store_device_load(const char *uuid, TbtDevice **device) {
        TbtDevice *d = NULL;
        int r;

        d = new0(TbtDevice, 1);
        if (!d) {
                r = -ENOMEM;
                goto out;
        }

        d->uuid = strdup(uuid);
        if (d->uuid == NULL) {
                r = -ENOMEM;
                tbt_device_free(&d);
                goto out;
        }

        r = tbt_store_parse_device(d);
        if (r < 0) {
                tbt_device_free(&d);
        }

 out:
        *device = d;
        return r;
}

static int tbt_store_have_key(const char *uuid) {
        char *path;
        struct stat st;
        int r;

        assert(uuid);

        path = strjoina(TBT_STORE_PATH, "keys/", uuid);
        r = stat(path, &st);

        if (r == -1)
                return -errno;
        if (S_ISDIR(st.st_mode))
                return -EISDIR;
        if (!S_ISREG(st.st_mode))
                return -ENOTTY;

        return 0;
}

#define HEX_BYTES 3            /* xx plus nul */
#define KEY_BYTES 32
#define KEY_CHARS 64          /* KEY_BYTES hex encoded */

static int tbt_generate_key_string(char **key_out) {
        uint8_t rnddata[KEY_BYTES];
        char *keydata;
        int i, r;

        r = acquire_random_bytes(rnddata, KEY_BYTES, true);
        if (r < 0)
                return r;

        keydata = malloc(KEY_CHARS + 1);
        for (i = 0; i < KEY_BYTES; i++)
                snprintf(keydata + i*2, HEX_BYTES, "%02hhx", rnddata[i]);

        *key_out = keydata;
        return 0;
}

static int device_get_authorized(struct udev_device *device, unsigned *authorized)
{
        const char *str;
        str = udev_device_get_sysattr_value(device, "authorized");
        return safe_atou(str, authorized);
}

static void device_print(struct udev_device *device)
{
        _cleanup_tbt_device_ TbtDevice *tbtdev = NULL;
        const char *name, *uuid, *vendor;
        unsigned authorized;
        int r;
        const char *auth_level;
        const char *auth_sym, *auth_con, *auth_coff;
        const char *store;
        SecurityLevel security;

        uuid = udev_device_get_sysattr_value(device, "unique_id");
        name = udev_device_get_sysattr_value(device, "device_name");
        vendor = udev_device_get_sysattr_value(device, "device_name");

        r = device_get_authorized(device, &authorized);
        if (r < 0) {
                auth_level = "unknown (error)";
                auth_con = ansi_highlight_red();
                auth_sym = special_glyph(BLACK_CIRCLE);
        } else if (authorized == AUTHORIZED_MISSING) {
                auth_level = "no";
                auth_con = ansi_highlight_yellow();
                auth_sym = special_glyph(BLACK_CIRCLE);
        } else if (authorized == AUTHORIZED_USER) {
                auth_level = "yes";
                auth_con = ansi_highlight_green();
                auth_sym = special_glyph(BLACK_CIRCLE);
        } else if (authorized == AUTHORIZED_KEY) {
                auth_level = "yes (key)";
                auth_con = ansi_highlight_green();
                auth_sym = special_glyph(BLACK_CIRCLE);
        } else {
                auth_level = "unknown";
                auth_con = ansi_highlight_red();
                auth_sym = special_glyph(BLACK_CIRCLE);
        }

        auth_coff = ansi_normal();

        printf("%s%s%s %s\n", auth_con, auth_sym, auth_coff, strunknown(name));
        printf("  %s vendor:     %s\n", special_glyph(TREE_BRANCH), strunknown(vendor));
        printf("  %s uuid:       %s\n", special_glyph(TREE_BRANCH), strunknown(uuid));
        printf("  %s authorized: %s\n", special_glyph(TREE_BRANCH), auth_level);

        printf("  %s security:   ", special_glyph(TREE_BRANCH));

        security = device_get_security_level(device);
        if (security == _SECURITY_INVALID)
                printf("unknown\n");
        else
                printf("%s\n", security_to_string(security));

        r = tbt_store_device_load(uuid, &tbtdev);
        if (r < 0 && r != -ENOENT) {
                store = "load error";
        } else if (tbtdev == NULL) {
                store = "no";
        } else {
                store = "yes";
        }
        printf("  %s in store:   %s\n", special_glyph(TREE_RIGHT), store);

        if (tbtdev) {
                const char *key_str;

                r = tbt_store_have_key(uuid);
                if (r > -1)
                        key_str = "yes";
                else if (r == -ENOENT)
                        key_str = "no";
                else
                        key_str = "io error";

                printf("    %s key:      %s\n", special_glyph(TREE_RIGHT), key_str);
        }

        printf("\n");
}

static int list_devices(struct udev *udev, int argc, char *argv[]) {
        _cleanup_udev_enumerate_unref_ struct udev_enumerate *enumerate;
        struct udev_list_entry *list_entry = NULL, *first = NULL;
        int r;

        enumerate = udev_enumerate_new(udev);
        if (enumerate == NULL)
                return -ENOMEM;

        r = udev_enumerate_add_match_subsystem(enumerate, "thunderbolt");
        if (r < 0)
                return r;

        r = udev_enumerate_scan_devices(enumerate);
        if (r < 0)
                return r;

        first = udev_enumerate_get_list_entry(enumerate);
        udev_list_entry_foreach(list_entry, first) {
                _cleanup_udev_device_unref_ struct udev_device *device;
                const char *name, *uuid;

                name = udev_list_entry_get_name(list_entry);
                device = udev_device_new_from_syspath(udev, name);

                if (device == NULL)
                        continue;

                /* devices without unique_id are ignored, most likely
                 * this is the domain */
                uuid = udev_device_get_sysattr_value(device, "unique_id");
                if (!uuid)
                        continue;

                device_print(device);
        }

        return 0;
}

static const struct CtlCmd cmd_list = {
        .name = "list",
        .func = list_devices,
        .desc = "List thunderbolt devices",
};

#define FORMAT_SECURITY_MAX 2 /* one digit plus nul */

static int device_read_uuid_at(int dirfd, char **uuid_out) {
        char *uuid;
        int fd;
        int r;

        fd = openat(dirfd, "unique_id", O_NOFOLLOW|O_CLOEXEC|O_RDONLY);
        if (fd < 0)
                return -errno;

        r = read_one_line_consume_fd(fd, &uuid);
        if (r == 0) {
                *uuid_out = uuid;
                return r;
        }

        return r;
}

static int store_efivars_get_auth(const char *uuid, Authorization *ret) {
        _cleanup_free_ char *var = NULL;
        sd_id128_t id;
        size_t l;
        int r;

        assert(ret);
        assert(uuid);

        if (sd_id128_from_string(uuid, &id) < 0) {
                return -EINVAL;
        }

        r = efi_get_variable_string(id, "Thunderbolt", &var);
        if (r < 0)
                return r;

        ret->store = TBT_KEYSTORE_EFIVARS;

        l = strlen(var);
        if (l == 1) {
                return safe_atou(var, &ret->level);
        } else if (l == KEY_CHARS) {
                ret->level = AUTHORIZED_KEY;
                ret->key = var;
                var = NULL;
                return 0;
        }

        /* should not happen, because we write the it */
        return -EIO;
}

static int store_get_authorization(TbtStore *store, const char *uuid, Authorization *ret) {
        _cleanup_free_ char *p = NULL;
        struct stat st;
        char *path;
        int r;

        if (in_initrd())
                return store_efivars_get_auth(uuid, ret);

        path = strjoina(store->path, "/authorization/", uuid);

        r = lstat(path, &st);
        if (r < 0)
                return -errno;
        if (S_ISREG(st.st_mode)) {
                ret->level = AUTHORIZED_USER;
                ret->store = TBT_KEYSTORE_FSDB;
                return 0;
        }

        r = readlink_malloc(path, &p);
        if (r < 0)
                return r;

        if (startswith(p, "/sys/firmware/efi/efivars")) {
                r = store_efivars_get_auth(uuid, ret);
        } else if (startswith(p, store->path)) {
                r = -ENOSYS;
        }

        return r;
}

static int store_efivars_put_auth(TbtStore *store,
                                  const char *uuid,
                                  Authorization *auth) {
        _cleanup_free_ char *target = NULL;
        char buf[FORMAT_SECURITY_MAX];
        sd_id128_t id;
        char *path;
        int r;


        if (sd_id128_from_string (uuid, &id) < 0) {
                return -EINVAL;
        }

        if (auth->level == AUTHORIZED_KEY) {
                r = efi_set_variable(id, "Thunderbolt", auth->key, KEY_CHARS);
        } else {
                xsprintf(buf, "%hhu", (uint8_t) auth->level);
                r = efi_set_variable(id, "Thunderbolt", buf, 1);
        }

        if (r < 0)
                return r;

        if (asprintf(&target,
                     "/sys/firmware/efi/efivars/Thunderbolt"
                     "-%02x%02x%02x%02x-%02x%02x-%02x%02x-%02x%02x-%02x%02x%02x%02x%02x%02x",
                     SD_ID128_FORMAT_VAL(id)) < 0)
                 return -ENOMEM;

        path = strjoina(store->path, "/authorization/", uuid);

        r = mkdir_parents(path, 0755);
        if (r < 0)
                return r;

        return symlink_idempotent(target, path);
}


static int store_fsdb_put_auth(TbtStore *store,
                               const char *uuid,
                               Authorization *auth) {

        return -ENOTSUP;
}


static int store_put_device(TbtStore *store,
                            struct udev_device *device,
                            Authorization *auth) {
        _cleanup_fclose_ FILE *f = NULL;
        const char *uuid;
        const char *vendor;
        const char *name;
        char *path;
        int r;

        uuid = udev_device_get_sysattr_value(device, "unique_id");
        name = udev_device_get_sysattr_value(device, "device_name");
        vendor = udev_device_get_sysattr_value(device, "vendor_name");

        switch (store->keystore) {
        case TBT_KEYSTORE_FSDB:
                r = store_fsdb_put_auth(store, uuid, auth);
                break;

        case TBT_KEYSTORE_EFIVARS:
                r = store_efivars_put_auth(store, uuid, auth);
                break;
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
        fputs(name, f);
        fputs("\n vendor=", f);
        fputs(vendor, f);
        fputs("\n", f);

        return fflush_and_check(f);
}

static int device_authorize_at(int dirfd, Authorization *auth) {
        char buf[FORMAT_SECURITY_MAX];
        _cleanup_close_ int fd = -1;
        ssize_t l;

        if (auth->level != AUTHORIZED_USER && auth->level != AUTHORIZED_KEY)
                return -EINVAL;

         /* logging? */
        if (auth->level == AUTHORIZED_KEY) {
                _cleanup_close_ int key_fd = -1;

                if (auth->key == NULL)
                        return -EINVAL;

                key_fd = openat(dirfd, "key", O_WRONLY|O_CLOEXEC|O_NOCTTY);
                if (key_fd < 0)
                        return -errno;

                l = write(key_fd, auth->key, KEY_CHARS);

                if (l < 0)
                        return -errno;
                else if (l != KEY_CHARS)
                        return -EIO;

        }

        fd = openat(dirfd, "authorized", O_WRONLY|O_CLOEXEC|O_WRONLY);
        if (fd < 0)
                return -errno;

        snprintf(buf, sizeof(buf), "%hhu", (uint8_t) auth->level);
        l = write(fd, buf, 1);

        if (l < 0)
                return -errno;
        else if (l != 1)
                return -EIO;

        return 0;
}

static int authorize_user(struct udev *udev, int argc, char *argv[]) {
        _cleanup_udev_device_unref_ struct udev_device *device = NULL;
        _cleanup_authorization_reset_ Authorization auth = { 0, };
        _cleanup_closedir_ DIR *devdir = NULL;
        _cleanup_store_free_ TbtStore *store = NULL;
        _cleanup_free_ char *uuid = NULL;
        bool store_put = false;
        const char *syspath;
        unsigned auth_have;
        int auth_ctrl;
        int auth_want = 0;
        int r;

        if (argc < 2) {
                fprintf(stderr, "%s: need sysfs path\n",
                        program_invocation_short_name);
                return EXIT_FAILURE;
        }

        r = tbt_store_new(&store);
        if (r < 0) {
                log_error_errno(r, "Couldn't open store: %m");
                return EXIT_FAILURE;
        }

        syspath = argv[1];
        device = udev_device_new_from_syspath(udev, syspath);

        if (device == NULL) {
                log_error("Couldn't open device at: %s", syspath);
                return EXIT_FAILURE;
        }

        r = device_get_authorized(device, &auth_have);
        if (r < 0) {
                log_error_errno(r, "Failed to get device authorization: %m");
                return EXIT_FAILURE;
        } else if (auth_have != 0) {
                log_error_errno(r, "Device already authorized");
                return EXIT_FAILURE;
        }

        devdir = opendir(syspath);
        if (!devdir) {
                log_error_errno(errno, "Could not open device: %m");
                return EXIT_FAILURE;
        }

        r = device_read_uuid_at(dirfd(devdir), &uuid);
        if (r < 0) {
                log_error_errno(errno, "Could not read device unique id: %m");
                return EXIT_FAILURE;
        }

        auth_ctrl = device_get_security_level(device);
        if (auth_ctrl < 0) {
                log_error_errno(auth_ctrl, "Could not determine security level: %m");
                return EXIT_FAILURE;
        }

        if (auth_want > auth_ctrl) {
                log_error("Requested security level not supported by domain controller");
                return EXIT_FAILURE;
        } else if (auth_want == 0)
                auth_want = auth_ctrl;

        r = store_get_authorization(store, uuid, &auth);
        if (r == -ENOENT) {
                store_put = true;
        } else if (r < 0) {
                log_error_errno(r, "Failed to read authorization from store: %m");
                return EXIT_FAILURE;
        }

        if (auth_want == AUTHORIZED_KEY && auth.level != AUTHORIZED_KEY) {
                r = tbt_generate_key_string(&auth.key);
                if (r < 0) {
                        log_error_errno(auth_ctrl, "Could not generate key: %m");
                        return EXIT_FAILURE;
                }

                auth_want = AUTHORIZED_USER;
                store_put = true;
        }

        r = device_authorize_at(dirfd(devdir), &auth);
        if (r < 0) {
                log_error_errno(r, "Failed to authorize device: %m");
                return EXIT_FAILURE;
        }

        if (!store_put)
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
        _cleanup_udev_device_unref_ struct udev_device *device = NULL;
        _cleanup_closedir_ DIR *devdir = NULL;
        _cleanup_store_free_ TbtStore *store = NULL;
        _cleanup_authorization_reset_ Authorization auth = { 0, };
        _cleanup_free_ char *uuid = NULL;
        const char *syspath;
        int auth_ctrl;
        int r;

        if (argc < 2) {
                fprintf(stderr, "%s: need sysfs path\n",
                        program_invocation_short_name);
                return EXIT_FAILURE;
        }

        r = tbt_store_new(&store);
        if (r < 0) {
                log_error_errno(r, "Couldn't open store: %m");
                return EXIT_FAILURE;
        }

        syspath = argv[1];
        device = udev_device_new_from_syspath(udev, syspath);

        if (device == NULL) {
                log_error("Couldn't open device at: %s", syspath);
                return EXIT_FAILURE;
        }

        devdir = opendir(syspath);
        if (!devdir) {
                log_error_errno(errno, "Could not open device: %m");
                return EXIT_FAILURE;
        }

        r = device_read_uuid_at(dirfd(devdir), &uuid);
        if (r < 0) {
                log_error_errno(errno, "Could not read device unique id: %m");
                return EXIT_FAILURE;
        }

        r = store_get_authorization(store, uuid, &auth);
        if (r < 0 && r != -ENOENT) {
                log_error_errno(r, "Failed to read authorization from store: %m");
                return EXIT_FAILURE;
        } else if (r == -ENOENT || auth.level == AUTHORIZED_MISSING) {
                /* Unknown or ignored device */
                return EXIT_SUCCESS;
        }

        auth_ctrl = device_get_security_level(device);
        if (auth_ctrl < 0) {
                log_error_errno(auth_ctrl, "Could not determine security level: %m");
                return EXIT_FAILURE;
        }

        auth.level = MIN((unsigned) auth_ctrl, auth.level);

        r = device_authorize_at(dirfd(devdir), &auth);
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


static const struct CtlCmd *ctrl_cmds[] = {
        &cmd_list,
        &cmd_authorize,

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
                fprintf(stderr, "%s %s must be invoked as root.",
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
