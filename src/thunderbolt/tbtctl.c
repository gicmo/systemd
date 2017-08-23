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
#include "fd-util.h"
#include "fileio.h"
#include "io-util.h"
#include "locale-util.h"
#include "mkdir.h"
#include "parse-util.h"
#include "random-util.h"
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

typedef enum Policy {
        POLICY_IGNORE,
        POLICY_AUTO,
        _POLICY_MAX,
        POLICY_UNKNOWN = -1,
} Policy;

static const char* const policy_table[_POLICY_MAX] = {
        [POLICY_IGNORE] = "ignore",
        [POLICY_AUTO]   = "auto",
};

DEFINE_PRIVATE_STRING_TABLE_LOOKUP(policy, Policy);
static DEFINE_CONFIG_PARSE_ENUM(config_parse_policy, policy, Policy, "Failed to parse policy setting");


typedef enum Security {
        SECURITY_NONE    = 0,
        SECURITY_USER    = 1, /* corresponds to sysfs 'authorized value' ("1") */
        SECURITY_SECURE  = 2, /* corresponds to sysfs 'authorized value' ("2") */
        SECURITY_DPONLY  = 3,
        _SECURITY_MAX,
        _SECURITY_INVALID = -1,
} Security;

/* the strings here correspond to the values reported
 * in sysfs ('security' attribute) for the domain  */
static const char* const security_table[_SECURITY_MAX] = {
        [SECURITY_NONE]    = "none",
        [SECURITY_USER]    = "user",
        [SECURITY_SECURE]  = "secure",
        [SECURITY_DPONLY]  = "dponly",
};
DEFINE_PRIVATE_STRING_TABLE_LOOKUP(security, Security);

static Security security_for_device(struct udev_device *device) {
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

typedef struct {

        char *uuid;

        char *name;
        char *vendor;

        Policy policy;

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

#define TBT_STORE_PATH "/var/lib/tbt/"
#define _cleanup_tbt_device_ _cleanup_(tbt_device_free)

static int tbt_store_parse_device(TbtDevice *device) {
        const ConfigTableItem items[] = {
                { "device", "name",         config_parse_string,           0, &device->name       },
                { "device", "vendor-name",  config_parse_string,           0, &device->vendor     },
                { "user",   "policy",       config_parse_policy,           0, &device->policy     },
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
#define FORMAT_SECURITY_MAX 2 /* one digit plus nul */

static int tbt_store_create_key(const char *uuid) {
        _cleanup_fclose_ FILE *f = NULL;
        uint8_t rnddata[KEY_BYTES];
        char self[strlen("/proc/self/fd/") + DECIMAL_STR_MAX(int)];
        char keydata[KEY_CHARS + 1];
        char *path;
        int fd, r, i;

        r = acquire_random_bytes(rnddata, KEY_BYTES, true);
        if (r < 0)
                return r;

        path = strjoina(TBT_STORE_PATH, "keys/", uuid);

        r = mkdir_parents(path, 0755);
        if (r < 0)
                return r;

        RUN_WITH_UMASK(0077)
                f = fopen(path, "we");
        if (!f)
                return -errno;

        /* hexencode the random data, make sure we have enough
         * space for the nul character as well */
        assert(KEY_BYTES * 2 == KEY_CHARS);
        assert(sizeof(keydata) == KEY_CHARS + 1);

        for (i = 0; i < KEY_BYTES; i++)
                snprintf(keydata + i*2, HEX_BYTES, "%02hhx", rnddata[i]);

        fputs(keydata, f);
        r = fflush_and_check(f);
        if (r < 0)
                return r;

        snprintf(self, sizeof(self), "/proc/self/fd/%i", fileno(f));
        fd = open(path, O_RDONLY|O_CLOEXEC|O_NOCTTY);
        if (fd < 0)
                return -errno;

        return fd;
}

static int tbt_store_key_open(const char *uuid, bool create, bool *created) {
        char *path;
        int fd;

        assert(uuid);
        assert(created);

        *created = false;

        path = strjoina(TBT_STORE_PATH, "keys/", uuid);
        fd = open(path, O_RDONLY|O_CLOEXEC|O_NOCTTY);
        if (fd > -1)
                return fd;
        else if (errno != ENOENT || !create)
                return -errno;

        fd = tbt_store_create_key(uuid);
        *created = fd > -1;
        return fd;
}

static int device_is_authorized(struct udev_device *device, int *authorized)
{
        const char *str;
        str = udev_device_get_sysattr_value(device, "authorized");
        return safe_atoi(str, authorized);
}

static void device_print(struct udev_device *device)
{
        _cleanup_tbt_device_ TbtDevice *tbtdev = NULL;
        const char *name, *uuid, *vendor;
        int r, authorized;
        const char *auth_level;
        const char *auth_sym, *auth_con, *auth_coff;
        const char *store;
        Security security;

        uuid = udev_device_get_sysattr_value(device, "unique_id");
        name = udev_device_get_sysattr_value(device, "device_name");
        vendor = udev_device_get_sysattr_value(device, "device_name");

        r = device_is_authorized(device, &authorized);
        if (r < 0) {
                auth_level = "unknown (error)";
                auth_con = ansi_highlight_red();
                auth_sym = special_glyph(BLACK_CIRCLE);
        } else if (authorized == 0) {
                auth_level = "no";
                auth_con = ansi_highlight_yellow();
                auth_sym = special_glyph(BLACK_CIRCLE);
        } else if (authorized == 1) {
                auth_level = "yes";
                auth_con = ansi_highlight_green();
                auth_sym = special_glyph(BLACK_CIRCLE);
        } else if (authorized == 2) {
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

        security = security_for_device(device);
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
                const char *policy_str;
                const char *key_str;

                if (tbtdev->policy < 0)
                        policy_str = "unknown";
                else
                        policy_str = policy_to_string(tbtdev->policy);

                printf("    %s policy:   %s\n", special_glyph(TREE_BRANCH), policy_str);

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

static int write_security(int fd, Security security) {
        char buf[FORMAT_SECURITY_MAX];

        if (security < SECURITY_USER || security > SECURITY_SECURE)
                return -EINVAL;

        snprintf(buf, sizeof(buf), "%hhu", (uint8_t) security);
        return loop_write(fd, buf, 1, false);
}

static int write_security_at (int dirfd, Security security) {
        int fd, r;

        fd = openat(dirfd, "authorized", O_NOFOLLOW|O_CLOEXEC|O_WRONLY);
        if (fd < 0)
                return -errno;

        r = write_security(fd, security);
        if (r < 0) {
                (void) close(fd);
                return r;
        }

        return close_nointr(fd);
}

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


static int device_authorize(struct udev_device *device, bool genkey, bool force) {
        _cleanup_closedir_ DIR *devdir = NULL;
        _cleanup_free_ char *uuid = NULL;
        const char *syspath;
        Security security;
        int r;

        /* the unlikely event of invalid security will
         * be handled in write_security down below */
        security = security_for_device(device);
        syspath = udev_device_get_syspath(device);

        assert(syspath);

        devdir = opendir(syspath);
        if (!devdir)
                return -errno;

        r = device_read_uuid_at(dirfd(devdir), &uuid);
        if (r < 0)
                return r;

        if (security == SECURITY_SECURE) {
                _cleanup_close_ int key_from = -1;
                int key_to = -1;
                bool created = false;
                ssize_t n;

                key_from = tbt_store_key_open(uuid, genkey, &created);
                if (key_from < 0)
                        return key_from;

                key_to = openat(dirfd(devdir), "key", O_NOFOLLOW|O_CLOEXEC|O_WRONLY);
                if (key_to < 0)
                        return -errno;

                /* if we don't copy all the data in one go, we will get a error
                 * returned, so there is no need to check if we copied the exact
                 * key bytes */
                n = sendfile(key_to, key_from, NULL, KEY_CHARS);
                if (n < 0) {
                        safe_close(key_to);
                        return -errno;
                }

                r = close_nointr(key_to);
                if (r < 0)
                        return r;

                /* in case the key was created, i.e. new or changed, we need
                 * to trigger a write of it to the NVM of the thunderbolt device
                 * which is done by writing '1' (SECURITY_USER) to 'authorized' */
                if (created)
                        security = SECURITY_USER;
        }

        return write_security_at(dirfd(devdir), security);
}

static int authorize_device(struct udev *udev, int argc, char *argv[]) {
        _cleanup_udev_device_unref_ struct udev_device *device;
        const char *syspath;
        int r;

        if (argc < 1) {
                fprintf(stderr, "%s: need sysfs path\n",
                        program_invocation_short_name);
                return EXIT_FAILURE;
        }

        syspath = argv[1];
        device = udev_device_new_from_syspath(udev, syspath);

        if (device == NULL) {
                log_error("Could not open device at: %s", syspath);
                return EXIT_FAILURE;
        }

        r = device_authorize(device, false, false);
        if (r < 0) {
                log_error_errno(r, "Could not authorize device: %m");
                return EXIT_FAILURE;
        }

        return EXIT_SUCCESS;
}

static const struct CtlCmd cmd_authorize = {
        .name = "authorize",
        .func = authorize_device,
        .desc = "Authorize a thunderbolt device",
        .root = true,
};

static int selftest(struct udev *udev, int argc, char *argv[]) {
        bool created;
        const char *uuid = "aaabbbcccdddeeee";
        int r = tbt_store_key_open(uuid, false, &created);
        fprintf(stderr, "no key, create: false: %d [created: %d]\n", r, created);
        r = tbt_store_key_open(uuid, true, &created);
        fprintf(stderr, "no key, create: true: %d [created: %d]\n", r, created);
        r = tbt_store_key_open(uuid, true, &created);
        fprintf(stderr, "w  key, create: true: %d [created: %d]\n", r, created);
        r = tbt_store_key_open(uuid, false, &created);
        fprintf(stderr, "w  key, create: false: %d [created: %d]\n", r, created);
        return r < 0 ? EXIT_FAILURE : EXIT_SUCCESS;
}

static const struct CtlCmd cmd_selftest = {
        .name = "selftest",
        .func = selftest,
};



static const struct CtlCmd *ctrl_cmds[] = {
        &cmd_list,
        &cmd_authorize,

        &cmd_selftest
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
