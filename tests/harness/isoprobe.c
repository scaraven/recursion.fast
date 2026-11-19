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
 *     fail with EPERM (free disk space), and so does every way to a pidfd (pidfs inode numbers count
 *     every process the machine started): `pidfd_open`, `clone` with CLONE_PIDFD, `SO_PEERPIDFD`,
 *     `SO_PASSPIDFD`; `clone3` fails with ENOSYS, while `fork` and `pthread_create` (libc falls back
 *     to `clone`) work; `SO_COOKIE` fails with EPERM.
 *
 * Request modes (the request's input `mode`, read at `go`): `probe` (the checks), `mlock N` (lock N
 * pages, which raises the machine-wide `unevictable_pgs_mlocked` by N), `ino K` (the inode number
 * and inode generation of /work's first file, then K more files), `inos` (on every CPU of its
 * affinity, the inode numbers of a new pipe and a new memfd), `pipes K` (on every CPU, K pipes and K
 * memfds made and closed). A oneshot `inoK` does `ino K` without the handshake. The report is `proof.bin` (a request), `/setup/report.txt`
 * (setup), `/work/ino.txt` (a oneshot), or the badge's answer (`accept` when every check passed;
 * the report on stderr). */
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
#include <sys/wait.h>
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
    /* free disk space: statfs and its relatives */
    struct statfs sf;
    struct statvfs sv;
    char ub[64];
    if (statfs("/", &sf) == 0 || errno != EPERM) FAIL("statfs /: %s\n", strerror(errno));
    if (statvfs(".", &sv) == 0 || errno != EPERM) FAIL("statvfs .: %s\n", strerror(errno));
    int rfd = open("/", O_RDONLY | O_DIRECTORY);
    if (rfd >= 0 && (fstatfs(rfd, &sf) == 0 || errno != EPERM)) FAIL("fstatfs /: %s\n", strerror(errno));
    if (rfd >= 0) close(rfd);
    if (syscall(SYS_ustat, 0, ub) == 0 || errno != EPERM) FAIL("ustat: %s\n", strerror(errno));
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

int main(int argc, char **argv) {
    if (argc > 1 && !strcmp(argv[1], "--serve")) {          /* the badge */
        char line[4096];
        while (fgets(line, sizeof line, stdin)) {
            fails = 0, len = 0;
            checks();
            fputs(rep, stderr);
            printf("%s 1\n", fails ? "reject" : "accept");
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
    char b[8], mode[64] = {0};
    if (!fgets(b, sizeof b, stdin)) return 9;
    int fd = open("mode", O_RDONLY);
    if (fd < 0 || read(fd, mode, sizeof mode - 1) < 0) return 8;
    close(fd);
    if (!strncmp(mode, "probe", 5)) checks();
    else if (!strncmp(mode, "ino ", 4)) ino(atol(mode + 4));
    else if (!strncmp(mode, "inos", 4)) percpu(0, 1);
    else if (!strncmp(mode, "pipes ", 6)) percpu(atol(mode + 6), 0);
    else if (!strncmp(mode, "mlock ", 6)) {
        long n = atol(mode + 6), pg = sysconf(_SC_PAGESIZE);
        char *m = mmap(0, n * pg, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        if (m == MAP_FAILED || mlock(m, n * pg)) FAIL("mlock %ld pages: %s\n", n, strerror(errno));
        else add("mlocked %ld pages\n", n), munlock(m, n * pg);
    }
    put("proof.bin");
    puts("done");
    fflush(stdout);
    return 0;
}
