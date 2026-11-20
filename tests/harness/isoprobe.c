/* The isolation probe of `test_sandbox.py` (§11), run as a prover (`setup`, a request, a oneshot)
 * and as a badge (`verify --serve`). It checks, from inside the sandbox, what the runner promises:
 *
 *   - /proc's top level: every entry but the pid directories, `self` and `thread-self` is masked (a
 *     file reads as empty, a directory lists nothing); links are left and listed;
 *   - /sys/devices/system/cpu: everything but its static description is masked (the same rule as
 *     `rfh.sandbox`'s allowlists, written out here again);
 *   - `socket` and `socketpair` fail with EPERM for every domain but AF_UNIX (a UDP socket among
 *     them), and work for AF_UNIX;
 *   - the other machine-wide counters are out of reach: `statfs`, `fstatfs`, `statvfs` and `ustat`
 *     fail with ENOSYS (free disk space), while `pathconf` still answers (glibc's defaults); every
 *     way to a pidfd (pidfs inode numbers count every process the machine started) fails with EPERM:
 *     `pidfd_open`, `clone` with CLONE_PIDFD, `SO_PEERPIDFD`, `SO_PASSPIDFD`; `clone3` fails with
 *     ENOSYS, while `fork` and `pthread_create` (libc falls back to `clone`) work; `SO_COOKIE`
 *     fails with EPERM; `setsid` in a child fails with EPERM (the autogroup counter); `madvise` with
 *     MADV_COLD or MADV_PAGEOUT, `process_madvise`, `quotactl_fd` and `open_tree_attr` fail with
 *     EPERM, other advice works; `mbind`, `migrate_pages`, `move_pages` and
 *     `set_mempolicy_home_node` fail with ENOSYS (a tmpfs file's shared memory policy, review LR5
 *     H1), while `get_mempolicy` and `set_mempolicy` (the task's own) work;
 *   - the timestamps of a shared inode cannot be set: `utime`, `utimes`, `futimesat` and `utimensat`
 *     (a path, and an fd of /dev/null; NULL times and UTIME_NOW) fail with EPERM, and /dev/null's
 *     times do not move; `inotify_init`, `inotify_init1` and `inotify_add_watch` fail with EPERM
 *     (inotify's machine-wide rename cookie); `madvise` MADV_COLLAPSE fails with EPERM;
 *   - the devices work: /dev/zero reads zeros, /dev/urandom and /dev/random read bytes, /dev/null
 *     takes a write, /dev/full refuses one with ENOSPC;
 *   - the mount table (`/proc/self/mountinfo`): every read-write mount is a fresh superblock of the
 *     sandbox's own (a tmpfs, devpts, proc or mqueue mounted at its root, `/`), but the six device
 *     nodes bubblewrap binds from the host's devtmpfs (`null`, `zero`, `full`, `random`, `urandom`,
 *     `tty`), each a single node whose one writable state, its timestamps, the filter closes; each
 *     read-write mount is reported as `rw MAJ:MIN FSTYPE MOUNTPOINT` (`rw LIST` counts those whose
 *     superblock is in LIST: the test passes the host's).
 *
 * Request modes (the request's input `mode`, read at `go`): `probe` (the checks), `mlock N` (lock N
 * pages, which raises the machine-wide `unevictable_pgs_mlocked` by N), `ino K` (the inode number
 * and inode generation of /work's first file, then K more files), `inos` (on every CPU of its
 * affinity, the inode numbers of a new pipe and a new memfd), `pipes K` (on every CPU, K pipes and K
 * memfds made and closed), `negw DIR N TAG` (look up the absent names DIR/nTAG_i for the i of a
 * pseudo-random half), `negr DIR N TAG` (time one lookup of each name and classify it: the share
 * guessed right, 0.5 by chance), `fold FILE R BITS` (for each 2 MiB region i < R of FILE whose bit i
 * of BITS is set: POSIX_FADV_DONTNEED, a MADV_HUGEPAGE mapping touched, MADV_COLLAPSE, MADV_PAGEOUT;
 * the page-cache folio shape, review LR4 H2), `pmd FILE R` (each region's FilePmdMapped in
 * /proc/self/smaps), `setsid K` (K children each try `setsid`), `autogroup` (/proc/self/autogroup),
 * `polw FILE N TAG` (map N pages of FILE read-only and MAP_SHARED, and `mbind` MPOL_PREFERRED on the
 * pages whose bit is 1: the file's shared memory policy, review LR5 H1), `polr FILE N TAG` (read each
 * page's policy back with `get_mempolicy(MPOL_F_ADDR)`: the share of bits right, 0.5 by chance).
 * `rw LIST` (the read-write mounts, `rwshared=N` the number of them, the device nodes aside, whose
 * MAJ:MIN is in the comma-separated LIST; a badge answers N). Several modes may be given, separated
 * by `;`. A oneshot `inoK` does `ino K` without the handshake.
 * The report is `proof.bin` (a request), `/setup/report.txt` (setup), `/work/ino.txt` (a oneshot),
 * or the badge's answer: for a checked file that begins with `mode `, the modes it names are run
 * and the answer is `accept R`, R the last `polr`'s count of bits right (or `polw`'s of policies
 * set); otherwise `accept` when every check passed (the report on stderr). */
#define _GNU_SOURCE
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <sched.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/statfs.h>
#include <sys/statvfs.h>
#include <sys/syscall.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

#ifndef SO_PASSPIDFD
#define SO_PASSPIDFD 76
#endif
#ifndef SO_PEERPIDFD
#define SO_PEERPIDFD 77
#endif
#ifndef CLONE_PIDFD
#define CLONE_PIDFD 0x1000
#endif

static char rep[1 << 17];
static size_t len;
static int fails;

static void add(const char *fmt, ...) {
    va_list a;
    va_start(a, fmt);
    int n = vsnprintf(rep + len, sizeof rep - len, fmt, a);
    va_end(a);
    if (n > 0) len += (size_t)n < sizeof rep - len ? (size_t)n : sizeof rep - len - 1;
}

#define FAIL(...) (fails++, add("FAIL " __VA_ARGS__))

static int in(const char *n, const char *const *l) {
    for (; *l; l++)
        if (!strcmp(n, *l)) return 1;
    return 0;
}
static int digits(const char *n, size_t from) {
    if (!n[from]) return 0;
    for (const char *p = n + from; *p; p++)
        if (*p < '0' || *p > '9') return 0;
    return 1;
}

static const char *const PROC_KEEP[] = {"self", "thread-self", 0};
static const char *const CPU_KEEP[] = {"online", "possible", "present", "offline", "kernel_max", "isolated",
                                       "nohz_full", "enabled", "housekeeping", "smt", "vulnerabilities", "hotplug",
                                       "crash_hotplug", "modalias", "uevent", 0};
static const char *const CPU_N_KEEP[] = {"topology", "cache", "online", "cpu_capacity", "hotplug", "crash_notes",
                                         "crash_notes_size", "uevent", 0};
static int keep_proc(const char *n) { return digits(n, 0) || in(n, PROC_KEEP); }
static int keep_cpu(const char *n) { return in(n, CPU_KEEP) || (!strncmp(n, "cpu", 3) && digits(n, 3)); }
static int keep_cpu_n(const char *n) { return in(n, CPU_N_KEEP); }

/* every entry of `root` that `keep` refuses is a link, an empty directory or a file that reads as
 * empty; the number of masked entries */
static int masked(const char *root, int (*keep)(const char *)) {
    DIR *d = opendir(root);
    if (!d) {
        FAIL("opendir %s: %s\n", root, strerror(errno));
        return 0;
    }
    struct dirent *e;
    int n = 0;
    while ((e = readdir(d))) {
        if (!strcmp(e->d_name, ".") || !strcmp(e->d_name, "..") || keep(e->d_name)) continue;
        char p[600];
        snprintf(p, sizeof p, "%s/%s", root, e->d_name);
        struct stat st;
        if (lstat(p, &st)) {
            FAIL("lstat %s: %s\n", p, strerror(errno));
            continue;
        }
        if (S_ISLNK(st.st_mode)) {
            add("link %s\n", p);
            continue;
        }
        n++;
        if (S_ISDIR(st.st_mode)) {
            DIR *s = opendir(p);
            if (!s) {
                FAIL("opendir %s: %s\n", p, strerror(errno));
                continue;
            }
            int k = 0;
            struct dirent *f;
            while ((f = readdir(s)))
                if (strcmp(f->d_name, ".") && strcmp(f->d_name, "..")) k++;
            closedir(s);
            if (k) FAIL("%s lists %d entries\n", p, k);
        } else {
            int fd = open(p, O_RDONLY | O_NONBLOCK);
            if (fd < 0) {
                FAIL("open %s: %s\n", p, strerror(errno));
                continue;
            }
            char b[256];
            ssize_t r = read(fd, b, sizeof b);
            close(fd);
            if (r != 0) FAIL("%s reads %zd bytes\n", p, r);
        }
    }
    closedir(d);
    return n;
}

static long readable(const char *p) {
    int fd = open(p, O_RDONLY);
    if (fd < 0) return -1;
    char b[4096];
    ssize_t r = read(fd, b, sizeof b);
    close(fd);
    return r;
}

static void *nop(void *a) { return a; }

/* a shared inode's timestamps (review R4b HIGH 1), inotify (HIGH 2), MADV_COLLAPSE (LOW 6) */
static void times_and_events(void) {
    struct stat a, b;
    int fd = open("/dev/null", O_WRONLY);
    if (fd < 0 || fstat(fd, &a)) FAIL("/dev/null: %s\n", strerror(errno));
    struct timespec now[2] = {{0, UTIME_NOW}, {0, UTIME_NOW}};
    struct timeval tv[2] = {{1, 0}, {1, 0}};
    struct { long nr; const char *name; long a, b, c, d; } ut[] = {
        {132, "utime /dev/null", (long)"/dev/null", 0, 0, 0},
        {235, "utimes /dev/null", (long)"/dev/null", 0, 0, 0},
        {235, "utimes /dev/null (times)", (long)"/dev/null", (long)tv, 0, 0},
        {261, "futimesat /dev/null", AT_FDCWD, (long)"/dev/null", 0, 0},
        {280, "utimensat /dev/null", AT_FDCWD, (long)"/dev/null", 0, 0},
        {280, "utimensat /dev/null UTIME_NOW", AT_FDCWD, (long)"/dev/null", (long)now, 0},
        {280, "utimensat fd of /dev/null (futimens)", fd, 0, (long)now, 0},
        {280, "utimensat fd 0", 0, 0, 0, 0},
        {280, "utimensat /tmp", AT_FDCWD, (long)"/tmp", 0, 0}};
    for (size_t i = 0; i < sizeof ut / sizeof *ut; i++) {
        long r = syscall(ut[i].nr, ut[i].a, ut[i].b, ut[i].c, ut[i].d);
        if (r == 0 || errno != EPERM) FAIL("%s: %ld (%s), not EPERM\n", ut[i].name, r, r ? strerror(errno) : "done");
    }
    int r = futimens(fd, 0);
    if (r == 0 || errno != EPERM) FAIL("futimens /dev/null: %d (%s), not EPERM\n", r, r ? strerror(errno) : "done");
    if (fd >= 0 && (fstat(fd, &b) || a.st_mtim.tv_sec != b.st_mtim.tv_sec || a.st_mtim.tv_nsec != b.st_mtim.tv_nsec
                    || a.st_atim.tv_nsec != b.st_atim.tv_nsec || a.st_ctim.tv_nsec != b.st_ctim.tv_nsec))
        FAIL("/dev/null's timestamps moved\n");
    if (fd >= 0) close(fd);
    if (syscall(253 /* inotify_init */) >= 0 || errno != EPERM) FAIL("inotify_init: %s\n", strerror(errno));
    if (syscall(294 /* inotify_init1 */, 0) >= 0 || errno != EPERM) FAIL("inotify_init1: %s\n", strerror(errno));
    if (syscall(254 /* inotify_add_watch */, 0, "/tmp", 0xfff) >= 0 || errno != EPERM) FAIL("inotify_add_watch: %s\n", strerror(errno));
    char *m = mmap(0, 2L << 20, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (m != MAP_FAILED) {
        m[0] = 1;
        if (madvise(m, 2L << 20, 25 /* MADV_COLLAPSE */) == 0 || errno != EPERM) FAIL("madvise MADV_COLLAPSE: %s\n", strerror(errno));
        munmap(m, 2L << 20);
    }
}

/* the device nodes still work for data */
static void devices(void) {
    unsigned char b[64];
    int fd = open("/dev/zero", O_RDONLY);
    ssize_t r = fd >= 0 ? read(fd, b, sizeof b) : -1;
    int zero = r == (ssize_t)sizeof b;
    for (ssize_t i = 0; zero && i < r; i++) zero = !b[i];
    if (!zero) FAIL("/dev/zero: %zd bytes (%s)\n", r, strerror(errno));
    if (fd >= 0) close(fd);
    static const char *const rnd[] = {"/dev/urandom", "/dev/random", 0};
    for (const char *const *p = rnd; *p; p++) {
        fd = open(*p, O_RDONLY | O_NONBLOCK);
        r = fd >= 0 ? read(fd, b, 16) : -1;
        if (r != 16) FAIL("%s: %zd bytes (%s)\n", *p, r, strerror(errno));
        if (fd >= 0) close(fd);
    }
    fd = open("/dev/null", O_WRONLY);
    if (fd < 0 || write(fd, b, sizeof b) != (ssize_t)sizeof b) FAIL("/dev/null: a write: %s\n", strerror(errno));
    if (fd >= 0) close(fd);
    fd = open("/dev/full", O_WRONLY);
    if (fd < 0 || write(fd, b, 1) != -1 || errno != ENOSPC) FAIL("/dev/full: a write not ENOSPC: %s\n", strerror(errno));
    if (fd >= 0) close(fd);
    add("devices: zero, urandom, random, null, full work\n");
}

/* the mount table: every read-write mount a fresh superblock of the sandbox's own, but the device
 * nodes; with `shared` (MAJ:MIN,…), the number of read-write mounts whose superblock is in it */
static const char *const DEVNODES[] = {"/dev/null", "/dev/zero", "/dev/full", "/dev/random", "/dev/urandom", "/dev/tty", 0};
static const char *const FRESH[] = {"tmpfs", "devpts", "proc", "mqueue", 0};
static void unescape(char *s) {
    char *o = s;
    for (; *s; s++)
        if (s[0] == '\\' && s[1] >= '0' && s[1] <= '7' && s[2] && s[3]) *o++ = (char)((s[1] - '0') * 64 + (s[2] - '0') * 8 + (s[3] - '0')), s += 3;
        else *o++ = *s;
    *o = 0;
}
static long mounts(const char *shared, int report) {
    FILE *f = fopen("/proc/self/mountinfo", "r");
    if (!f) {
        FAIL("/proc/self/mountinfo: %s\n", strerror(errno));
        return -1;
    }
    char line[4096];
    long n = 0, rw = 0, in_list = 0, dev = 0;
    while (fgets(line, sizeof line, f)) {
        char id[32], parent[32], mm[32], root[1024], mp[1024], opts[512], *sep = strstr(line, " - ");
        char fstype[64] = "?";
        if (sscanf(line, "%31s %31s %31s %1023s %1023s %511s", id, parent, mm, root, mp, opts) != 6 || !sep) continue;
        sscanf(sep + 3, "%63s", fstype);
        unescape(root), unescape(mp);
        n++;
        char o[520];
        snprintf(o, sizeof o, ",%s,", opts);
        if (!strstr(o, ",rw,")) continue;
        rw++;
        int node = in(mp, DEVNODES);
        if (node) {
            dev++;
            if (strcmp(fstype, "devtmpfs") || strcmp(root, mp + 4)) FAIL("rw %s: a %s mount of %s, not a single node of the host's devtmpfs\n", mp, fstype, root);
            continue;
        }
        if (!in(fstype, FRESH) || strcmp(root, "/")) FAIL("rw %s: %s %s at %s, not a fresh superblock of the sandbox's own\n", mm, fstype, root, mp);
        if (report) add("rw %s %s %s\n", mm, fstype, mp);
        if (shared) {
            char l[8200], k[40];
            snprintf(l, sizeof l, ",%s,", shared);
            snprintf(k, sizeof k, ",%s,", mm);
            if (strstr(l, k)) in_list++, add("rw %s %s %s: a superblock in the list\n", mm, fstype, mp);
        }
    }
    fclose(f);
    if (!shared) add("mounts: %ld, %ld read-write (%ld of them the device nodes)\n", n, rw, dev);
    if (dev != 6) FAIL("%ld read-write device nodes, not the six\n", dev);
    if (shared) add("rwshared=%ld\n", in_list);
    return in_list;
}

static void checks(void) {
    int n = masked("/proc", keep_proc);
    add("/proc: %d masked entries\n", n);
    if (n < 20) FAIL("only %d masked entries in /proc\n", n);
    if (readable("/proc/self/status") <= 0) FAIL("/proc/self/status unreadable (the allowlist)\n");
    if (readable("/proc/stat") != 0) FAIL("/proc/stat is not empty\n");
    DIR *d = opendir("/sys/devices/system/cpu");
    if (d) {
        int m = masked("/sys/devices/system/cpu", keep_cpu), cpus = 0;
        struct dirent *e;
        while ((e = readdir(d)))
            if (!strncmp(e->d_name, "cpu", 3) && digits(e->d_name, 3)) {
                char p[300];
                snprintf(p, sizeof p, "/sys/devices/system/cpu/%s", e->d_name);
                m += masked(p, keep_cpu_n);
                cpus++;
            }
        closedir(d);
        add("/sys/devices/system/cpu: %d cpus, %d masked entries\n", cpus, m);
        if (readable("/sys/devices/system/cpu/online") <= 0) FAIL("/sys/devices/system/cpu/online unreadable\n");
    }
    static const struct { int dom, type; const char *name; } refused[] = {
        {AF_INET, SOCK_DGRAM, "udp"}, {AF_INET, SOCK_STREAM, "tcp"}, {AF_INET6, SOCK_DGRAM, "udp6"},
        {AF_NETLINK, SOCK_RAW, "netlink"}, {AF_PACKET, SOCK_DGRAM, "packet"}, {AF_VSOCK, SOCK_STREAM, "vsock"}};
    for (size_t i = 0; i < sizeof refused / sizeof *refused; i++) {
        int s = socket(refused[i].dom, refused[i].type, 0);
        if (s >= 0 || errno != EPERM) FAIL("socket %s: %d (%s)\n", refused[i].name, s, strerror(errno));
        else add("socket %s refused: %s\n", refused[i].name, strerror(errno));
        int sp[2];
        int r = socketpair(refused[i].dom, refused[i].type, 0, sp);
        if (r == 0 || errno != EPERM) FAIL("socketpair %s: %d (%s)\n", refused[i].name, r, strerror(errno));
    }
    /* the domain in the upper half of the register: the kernel reads an int, the filter its low word */
    long s = syscall(SYS_socket, (1L << 32) | AF_INET, SOCK_DGRAM, 0);
    if (s >= 0 || errno != EPERM) FAIL("socket udp with high bits: %ld (%s)\n", s, strerror(errno));
    int u = socket(AF_UNIX, SOCK_STREAM, 0), sp[2];
    if (u < 0) FAIL("socket AF_UNIX: %s\n", strerror(errno));
    else close(u);
    if (socketpair(AF_UNIX, SOCK_STREAM, 0, sp)) FAIL("socketpair AF_UNIX: %s\n", strerror(errno));
    else {
        long v = 0;
        int one = 1;
        socklen_t n = sizeof v;
        if (getsockopt(sp[0], SOL_SOCKET, SO_COOKIE, &v, &n) == 0 || errno != EPERM)
            FAIL("getsockopt SO_COOKIE: %s\n", strerror(errno));
        n = sizeof v;
        if (getsockopt(sp[0], SOL_SOCKET, SO_PEERPIDFD, &v, &n) == 0 || errno != EPERM)
            FAIL("getsockopt SO_PEERPIDFD: %s\n", strerror(errno));
        if (setsockopt(sp[0], SOL_SOCKET, SO_PASSPIDFD, &one, sizeof one) == 0 || errno != EPERM)
            FAIL("setsockopt SO_PASSPIDFD: %s\n", strerror(errno));
        n = sizeof v;
        if (getsockopt(sp[0], SOL_SOCKET, SO_TYPE, &v, &n)) FAIL("getsockopt SO_TYPE: %s\n", strerror(errno));
        close(sp[0]), close(sp[1]);
    }
    /* free disk space: statfs and its relatives (ENOSYS, so that glibc's pathconf keeps its defaults) */
    struct statfs sf;
    struct statvfs sv;
    char ub[64];
    if (statfs("/", &sf) == 0 || errno != ENOSYS) FAIL("statfs /: %s\n", strerror(errno));
    if (statvfs(".", &sv) == 0 || errno != ENOSYS) FAIL("statvfs .: %s\n", strerror(errno));
    int rfd = open("/", O_RDONLY | O_DIRECTORY);
    if (rfd >= 0 && (fstatfs(rfd, &sf) == 0 || errno != ENOSYS)) FAIL("fstatfs /: %s\n", strerror(errno));
    if (rfd >= 0) close(rfd);
    if (syscall(SYS_ustat, 0, ub) == 0 || errno != ENOSYS) FAIL("ustat: %s\n", strerror(errno));
    long nm = pathconf("/", _PC_NAME_MAX), lm = pathconf("/", _PC_LINK_MAX), fb = pathconf("/", _PC_FILESIZEBITS);
    if (nm <= 0 || lm <= 0 || fb <= 0) FAIL("pathconf: NAME_MAX %ld LINK_MAX %ld FILESIZEBITS %ld (%s)\n", nm, lm, fb, strerror(errno));
    else add("pathconf: NAME_MAX %ld LINK_MAX %ld FILESIZEBITS %ld\n", nm, lm, fb);
    /* the autogroup counter: no new session */
    pid_t sp_ = fork();
    if (sp_ == 0) _exit(setsid() < 0 && errno == EPERM ? 0 : 1);
    int sws = 0;
    if (sp_ < 0 || waitpid(sp_, &sws, 0) != sp_ || !WIFEXITED(sws) || WEXITSTATUS(sws)) FAIL("setsid in a child was not refused with EPERM\n");
    /* page reclaim of shared pages, quotas, open_tree_attr */
    char *am = mmap(0, 1 << 16, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (am != MAP_FAILED) {
        am[0] = 1;
        if (madvise(am, 1 << 16, 21 /* MADV_PAGEOUT */) == 0 || errno != EPERM) FAIL("madvise MADV_PAGEOUT: %s\n", strerror(errno));
        if (madvise(am, 1 << 16, 20 /* MADV_COLD */) == 0 || errno != EPERM) FAIL("madvise MADV_COLD: %s\n", strerror(errno));
        if (madvise(am, 1 << 16, MADV_DONTNEED)) FAIL("madvise MADV_DONTNEED: %s\n", strerror(errno));
        munmap(am, 1 << 16);
    }
    if (syscall(440 /* process_madvise */, -10000 /* PIDFD_SELF */, 0, 0, 21, 0) == 0 || errno != EPERM)
        FAIL("process_madvise: %s\n", strerror(errno));
    if (syscall(443 /* quotactl_fd */, 0, 0, 0, 0) == 0 || errno != EPERM) FAIL("quotactl_fd: %s\n", strerror(errno));
    if (syscall(467 /* open_tree_attr */, -100, "/", 0, 0, 0) >= 0 || errno != EPERM) FAIL("open_tree_attr: %s\n", strerror(errno));
    /* the mbind family: ENOSYS; the task's own policy calls work */
    static const struct { long nr; const char *name; } nopol[] = {
        {237, "mbind"}, {256, "migrate_pages"}, {279, "move_pages"}, {450, "set_mempolicy_home_node"}};
    for (size_t i = 0; i < sizeof nopol / sizeof *nopol; i++)
        if (syscall(nopol[i].nr, 0, 0, 0, 0, 0, 0) == 0 || errno != ENOSYS) FAIL("%s: %s (not ENOSYS)\n", nopol[i].name, strerror(errno));
    int pm = -1;
    if (syscall(239 /* get_mempolicy */, &pm, 0, 0, 0, 0)) FAIL("get_mempolicy: %s\n", strerror(errno));
    if (syscall(238 /* set_mempolicy */, 0 /* MPOL_DEFAULT */, 0, 0)) FAIL("set_mempolicy: %s\n", strerror(errno));
    /* pidfs: no pidfd, by any way */
    if (syscall(SYS_pidfd_open, getpid(), 0) >= 0 || errno != EPERM) FAIL("pidfd_open: %s\n", strerror(errno));
    if (syscall(SYS_clone3, NULL, 0) == 0 || errno != ENOSYS) FAIL("clone3: %s (not ENOSYS)\n", strerror(errno));
    int pfd = -1;
    long c = syscall(SYS_clone, CLONE_PIDFD | SIGCHLD, 0, &pfd, 0, 0);
    if (c == 0) _exit(0);
    if (c > 0) FAIL("clone with CLONE_PIDFD: a child, pidfd %d\n", pfd), waitpid((pid_t)c, 0, 0);
    else if (errno != EPERM) FAIL("clone with CLONE_PIDFD: %s\n", strerror(errno));
    pid_t f = fork();
    if (f == 0) _exit(7);
    int ws = 0;
    if (f < 0 || waitpid(f, &ws, 0) != f || !WIFEXITED(ws) || WEXITSTATUS(ws) != 7) FAIL("fork: %s\n", strerror(errno));
    pthread_t th;
    if (pthread_create(&th, 0, nop, 0) || pthread_join(th, 0)) FAIL("pthread_create\n");
    times_and_events();
    devices();
    mounts(0, 1);
    add("%s\n", fails ? "checks failed" : "checks passed");
}

/* every CPU of the affinity, in turn: the inode numbers of a new pipe and a new memfd (`inos`), or K
 * pipes and K memfds made and closed (`pipes K`) */
static long ino_pipe(void) {
    int p[2];
    struct stat st;
    if (pipe(p)) return -1;
    long r = fstat(p[0], &st) ? -1 : (long)st.st_ino;
    close(p[0]), close(p[1]);
    return r;
}
static long ino_memfd(void) {
    struct stat st;
    int fd = memfd_create("probe", 0);
    if (fd < 0) return -1;
    long r = fstat(fd, &st) ? -1 : (long)st.st_ino;
    close(fd);
    return r;
}
static void percpu(long k, int report) {
    cpu_set_t all, one;
    if (sched_getaffinity(0, sizeof all, &all)) {
        FAIL("sched_getaffinity: %s\n", strerror(errno));
        return;
    }
    for (int c = 0; c < CPU_SETSIZE; c++) {
        if (!CPU_ISSET(c, &all)) continue;
        CPU_ZERO(&one);
        CPU_SET(c, &one);
        if (sched_setaffinity(0, sizeof one, &one)) {
            FAIL("pin to cpu %d: %s\n", c, strerror(errno));
            continue;
        }
        for (long i = 0; i < k; i++) ino_pipe(), ino_memfd();
        if (report) add("cpu=%d pipe=%ld memfd=%ld\n", c, ino_pipe(), ino_memfd());
    }
}

/* negative dentries (review LR4 H1): a write looks up the absent names DIR/n<tag>_<i> for the i whose
 * bit is 1; a read times one lookup of each name and classifies it at the midpoint of the quartiles */
static unsigned bit(long i, long tag) {
    unsigned long x = (unsigned long)i * 0x9E3779B97F4A7C15ul ^ (unsigned long)tag;
    x ^= x >> 29, x *= 0xBF58476D1CE4E5B9ul, x ^= x >> 32;
    return x & 1;
}
static void negw(const char *dir, long n, long tag) {
    char p[300];
    struct stat st;
    long k = 0;
    for (long i = 0; i < n; i++)
        if (bit(i, tag)) snprintf(p, sizeof p, "%s/n%ld_%ld", dir, tag, i), stat(p, &st), k++;
    add("negw %s %ld\n", dir, k);
}
static int cmpu(const void *a, const void *b) {
    unsigned long long x = *(const unsigned long long *)a, y = *(const unsigned long long *)b;
    return x < y ? -1 : x > y;
}
static unsigned long long ns(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec * 1000000000ull + t.tv_nsec;
}
static void negr(const char *dir, long n, long tag) {
    static unsigned long long t[1 << 18], s[1 << 18];
    char p[300];
    struct stat st;
    if (n > (1 << 18)) n = 1 << 18;
    for (long i = 0; i < n; i++) {
        snprintf(p, sizeof p, "%s/n%ld_%ld", dir, tag, i);
        unsigned long long a = ns();
        stat(p, &st);
        t[i] = ns() - a;
    }
    memcpy(s, t, n * sizeof *t);
    qsort(s, n, sizeof *s, cmpu);
    unsigned long long th = (s[n / 4] + s[3 * n / 4]) / 2;
    long ok = 0;
    for (long i = 0; i < n; i++) ok += (t[i] < th) == bit(i, tag);
    add("negr n=%ld right=%ld share=%.4f q1=%llu q3=%llu\n", n, ok, (double)ok / n, s[n / 4], s[3 * n / 4]);
}

/* the page-cache folio shape (review LR4 H2) */
#define H2M (2L << 20)
static void fold(const char *f, long regions, long bits) {
    int fd = open(f, O_RDONLY);
    if (fd < 0) { add("fold %s: %s\n", f, strerror(errno)); return; }
    for (long r = 0; r < regions; r++) {
        if (!(bits >> r & 1)) continue;
        int a = posix_fadvise(fd, r * H2M, H2M, POSIX_FADV_DONTNEED);
        char *m = mmap(0, H2M, PROT_READ, MAP_SHARED, fd, r * H2M);
        if (m == MAP_FAILED) { add("fold mmap: %s\n", strerror(errno)); continue; }
        int b = madvise(m, H2M, MADV_HUGEPAGE);
        for (long i = 0; i < H2M; i += 4096) { volatile char c = m[i]; (void)c; }
        int c = madvise(m, H2M, 25 /* MADV_COLLAPSE */), ce = errno;
        int d = madvise(m, H2M, 21 /* MADV_PAGEOUT */), de = errno;
        add("fold %ld: fadvise %d hugepage %d collapse %d(%d) pageout %d(%d)\n", r, a, b, c, c ? ce : 0, d, d ? de : 0);
        munmap(m, H2M);
    }
    close(fd);
}
static long smaps_field(void *addr, const char *key) {
    FILE *f = fopen("/proc/self/smaps", "r");
    char line[512];
    int in = 0;
    long v = -1;
    while (f && fgets(line, sizeof line, f)) {
        unsigned long lo, hi;
        if (sscanf(line, "%lx-%lx ", &lo, &hi) == 2 && line[strcspn(line, " ")] == ' ' && strchr(line, '-') < strchr(line, ' ')) {
            in = lo <= (unsigned long)addr && (unsigned long)addr < hi;
            continue;
        }
        if (in && !strncmp(line, key, strlen(key))) { v = atol(line + strlen(key)); break; }
    }
    if (f) fclose(f);
    return v;
}
static void pmd(const char *f, long regions) {
    int fd = open(f, O_RDONLY);
    if (fd < 0) { add("pmd %s: %s\n", f, strerror(errno)); return; }
    char *base = mmap(0, 2 * H2M, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    char *al = (char *)(((unsigned long)base + H2M - 1) & ~(H2M - 1));
    munmap(base, 2 * H2M);
    add("pmd");
    for (long r = 0; r < regions; r++) {
        char *m = mmap(al, H2M, PROT_READ, MAP_PRIVATE | MAP_FIXED, fd, r * H2M);
        if (m == MAP_FAILED) { add(" E%d", errno); continue; }
        madvise(m, H2M, MADV_HUGEPAGE);
        volatile char c = m[0];
        (void)c;
        add(" %ld", smaps_field(m, "FilePmdMapped:"));
        munmap(m, H2M);
    }
    add("\n");
    close(fd);
}

/* a tmpfs file's shared memory policy (review LR5 H1): set per page by `mbind` on a read-only
 * MAP_SHARED mapping, kept in the inode, read back by another process's mapping */
static long answer;
static void polw(const char *p, long n, long tag) {
    int fd = open(p, O_RDONLY);
    if (fd < 0) { add("polw open %s: %s\n", p, strerror(errno)); return; }
    char *m = mmap(0, n * 4096, PROT_READ, MAP_SHARED, fd, 0);
    if (m == MAP_FAILED) { add("polw mmap %s: %s\n", p, strerror(errno)); close(fd); return; }
    unsigned long mask = 1;
    long ok = 0, bad = 0, err = 0;
    for (long i = 0; i < n; i++)
        if (bit(i, tag)) {
            if (syscall(237, m + i * 4096, 4096, 1 /* MPOL_PREFERRED */, &mask, 64, 0)) bad++, err = errno;
            else ok++;
        }
    add("polw %s n=%ld set=%ld failed=%ld errno=%ld\n", p, n, ok, bad, err);
    answer = ok;
    munmap(m, n * 4096);
    close(fd);
}
static void polr(const char *p, long n, long tag) {
    int fd = open(p, O_RDONLY);
    if (fd < 0) { add("polr open %s: %s\n", p, strerror(errno)); return; }
    char *m = mmap(0, n * 4096, PROT_READ, MAP_SHARED, fd, 0);
    if (m == MAP_FAILED) { add("polr mmap %s: %s\n", p, strerror(errno)); close(fd); return; }
    long right = 0, pref = 0, err = 0;
    for (long i = 0; i < n; i++) {
        int mode = -1;
        unsigned long mask = 0;
        if (syscall(239 /* get_mempolicy */, &mode, &mask, 64, m + i * 4096, 2 /* MPOL_F_ADDR */)) { err++; continue; }
        unsigned g = mode == 1;
        pref += g, right += g == bit(i, tag);
    }
    add("polr %s n=%ld preferred=%ld right=%ld share=%.4f errors=%ld\n", p, n, pref, right, (double)right / n, err);
    answer = right;
    munmap(m, n * 4096);
    close(fd);
}

static void ino(long k) {
    int fd = open("a", O_WRONLY | O_CREAT | O_EXCL, 0644);
    struct stat st;
    if (fd < 0 || fstat(fd, &st)) {
        FAIL("the first file: %s\n", strerror(errno));
        return;
    }
    close(fd);
    for (long i = 0; i < k; i++) {
        char n[32];
        snprintf(n, sizeof n, "f%ld", i);
        close(open(n, O_WRONLY | O_CREAT, 0644));
    }
    add("ino=%lu\n", (unsigned long)st.st_ino);      /* free counts: statvfs is refused (checks) */
}

static void put(const char *path) {
    int fd = open(path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
    if (fd >= 0) {
        if (write(fd, rep, len) < 0) _exit(5);
        close(fd);
    }
}

static void run_mode(const char *mode) {
    while (*mode == ' ') mode++;
    if (!strncmp(mode, "probe", 5)) checks();
    else if (!strncmp(mode, "ino ", 4)) ino(atol(mode + 4));
    else if (!strncmp(mode, "inos", 4)) percpu(0, 1);
    else if (!strncmp(mode, "pipes ", 6)) percpu(atol(mode + 6), 0);
    else if (!strncmp(mode, "negw ", 5) || !strncmp(mode, "negr ", 5)) {
        char d[256];
        long n = 0, tag = 0;
        if (sscanf(mode + 5, "%255s %ld %ld", d, &n, &tag) == 3) (mode[3] == 'w' ? negw : negr)(d, n, tag);
    } else if (!strncmp(mode, "fold ", 5) || !strncmp(mode, "pmd ", 4)) {
        char f[256];
        long r = 0, bits = 0;
        if (mode[0] == 'f' && sscanf(mode + 5, "%255s %ld %ld", f, &r, &bits) == 3) fold(f, r, bits);
        else if (mode[0] == 'p' && sscanf(mode + 4, "%255s %ld", f, &r) == 2) pmd(f, r);
    } else if (!strncmp(mode, "setsid ", 7)) {
        long k = atol(mode + 7), ok = 0;
        for (long i = 0; i < k; i++) {
            pid_t c = fork();
            if (c == 0) _exit(setsid() < 0 ? 1 : 0);
            int w = 0;
            if (c > 0 && waitpid(c, &w, 0) == c && WIFEXITED(w) && !WEXITSTATUS(w)) ok++;
        }
        add("setsid %ld of %ld\n", ok, k);
    } else if (!strncmp(mode, "autogroup", 9)) {
        char b2[128] = {0};
        int a = open("/proc/self/autogroup", O_RDONLY);
        if (a >= 0 && read(a, b2, sizeof b2 - 1) > 0) add("autogroup %s", b2);
        if (a >= 0) close(a);
    } else if (!strncmp(mode, "mlock ", 6)) {
        long n = atol(mode + 6), pg = sysconf(_SC_PAGESIZE);
        char *m = mmap(0, n * pg, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        if (m == MAP_FAILED || mlock(m, n * pg)) FAIL("mlock %ld pages: %s\n", n, strerror(errno));
        else add("mlocked %ld pages\n", n), munlock(m, n * pg);
    } else if (!strncmp(mode, "rw ", 3)) {
        char l[8192];
        if (sscanf(mode + 3, "%8191s", l) == 1) answer = mounts(l, 1) + (fails ? 1000000 : 0);
    } else if (!strncmp(mode, "polw ", 5) || !strncmp(mode, "polr ", 5)) {
        char f[256];
        long n = 0, tag = 0;
        if (sscanf(mode + 5, "%255s %ld %ld", f, &n, &tag) == 3) (mode[3] == 'w' ? polw : polr)(f, n, tag);
    }
}
static void run_modes(char *modes) {
    char *save, *m = strtok_r(modes, ";\n", &save);
    for (; m; m = strtok_r(0, ";\n", &save)) run_mode(m);
}

int main(int argc, char **argv) {
    if (argc > 1 && !strcmp(argv[1], "--serve")) {          /* the badge */
        char line[4096];
        while (fgets(line, sizeof line, stdin)) {
            fails = 0, len = 0;
            char vk[80], st[80], path[1024], m[8192] = {0};
            int f = sscanf(line, "%79s %79s %1023s", vk, st, path) == 3 ? open(path, O_RDONLY) : -1;
            long k = f >= 0 ? read(f, m, sizeof m - 1) : -1;
            if (f >= 0) close(f);
            if (k > 5 && !strncmp(m, "mode ", 5)) {
                answer = 0;
                run_modes(m + 5);
                fputs(rep, stderr);
                printf("accept %ld\n", answer);
            } else {
                checks();
                fputs(rep, stderr);
                printf("%s 1\n", fails ? "reject" : "accept");
            }
            fflush(stdout);
        }
        return fails ? 3 : 0;
    }
    if (argc > 1 && !strcmp(argv[1], "setup")) {
        checks();
        put("/setup/report.txt");
        return 0;
    }
    if (argc > 1 && !strncmp(argv[1], "ino", 3)) {          /* a oneshot, no handshake */
        ino(atol(argv[1] + 3));
        put("/work/ino.txt");
        return 0;
    }
    puts("ready");
    fflush(stdout);
    char b[8], mode[8192] = {0};
    if (!fgets(b, sizeof b, stdin)) return 9;
    int fd = open("mode", O_RDONLY);
    if (fd < 0 || read(fd, mode, sizeof mode - 1) < 0) return 8;
    close(fd);
    run_modes(mode);
    put("proof.bin");
    puts("done");
    fflush(stdout);
    return 0;
}
