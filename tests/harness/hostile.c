/*
 * A hostile "prover" for the sandbox tests (tests/harness/test_sandbox.py). In `tree` mode it tries
 * what an untrusted prover must not be able to do and writes one line per attempt to
 * /work/report.txt ("NAME ok" when the attempt failed as it should, "NAME LEAK ..." otherwise).
 * Then it plants outputs that must not be read through: a symbolic link to a host file, a FIFO,
 * and a directory component that is a link; and leaves a detached child running.
 * In `mem` mode it allocates and touches the given number of MiB.
 */
#define _GNU_SOURCE
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <sched.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <sys/mman.h>
#include <sys/ptrace.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/uio.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <linux/bpf.h>
#include <linux/perf_event.h>
#include <linux/userfaultfd.h>

static FILE *rep;
static void line(const char *name, int leak, const char *detail) {
    fprintf(rep, "%s %s %s\n", name, leak ? "LEAK" : "ok", detail ? detail : "");
    fflush(rep);
}

int main(int argc, char **argv) {
    if (argc == 3 && !strcmp(argv[1], "mem")) {
        size_t n = (size_t)atol(argv[2]) << 20;
        char *p = malloc(n);
        for (size_t i = 0; p && i < n; i += 4096) p[i] = 1;
        long s = 0;
        for (size_t i = 0; p && i < n; i += 4096) s += p[i];
        printf("touched %ld pages\n", s);
        return 0;
    }
    if (argc != 3 || strcmp(argv[1], "tree")) return 0;
    rep = fopen("/work/report.txt", "w");
    if (!rep) return 3;
    char buf[256];

    /* processes visible */
    int nproc = 0;
    DIR *d = opendir("/proc");
    struct dirent *e;
    while (d && (e = readdir(d))) if (e->d_name[0] >= '0' && e->d_name[0] <= '9') nproc++;
    if (d) closedir(d);
    snprintf(buf, sizeof buf, "%d processes visible", nproc);
    line("proc-visible", nproc > 3, buf);

    /* ptrace and memory reads of every pid number up to 4 million that might exist */
    int hits = 0;
    for (int pid = 2; pid < 4194304 && hits == 0; pid += (pid < 70000 ? 1 : 997)) {
        if (pid == getpid()) continue;
        char path[64];
        snprintf(path, sizeof path, "/proc/%d/mem", pid);
        int fd = open(path, O_RDONLY);
        if (fd >= 0) { hits++; close(fd); }
    }
    line("proc-mem", hits > 0, NULL);
    errno = 0;
    long r = ptrace(PTRACE_ATTACH, 1, 0, 0);
    snprintf(buf, sizeof buf, "ptrace(pid 1)=%ld %s", r, strerror(errno));
    line("ptrace", r == 0, buf);
    struct iovec lo = {buf, 8}, re = {(void *)0x400000, 8};
    errno = 0;
    r = process_vm_readv(1, &lo, 1, &re, 1, 0);
    snprintf(buf, sizeof buf, "process_vm_readv=%ld %s", r, strerror(errno));
    line("process_vm_readv", r >= 0, buf);
    errno = 0;
    r = syscall(SYS_bpf, BPF_PROG_LOAD, NULL, 0);
    snprintf(buf, sizeof buf, "bpf errno %s", strerror(errno));
    line("bpf", errno != EPERM, buf);
    struct perf_event_attr pa;
    memset(&pa, 0, sizeof pa);
    pa.size = sizeof pa;
    errno = 0;
    r = syscall(SYS_perf_event_open, &pa, 0, -1, -1, 0);
    snprintf(buf, sizeof buf, "perf_event_open=%ld %s", r, strerror(errno));
    line("perf_event_open", r >= 0, buf);
    errno = 0;
    r = syscall(SYS_userfaultfd, 0);
    line("userfaultfd", r >= 0, strerror(errno));
    errno = 0;
    r = syscall(SYS_io_uring_setup, 1, buf);
    line("io_uring_setup", r >= 0, strerror(errno));
    errno = 0;
    r = unshare(CLONE_NEWUSER);
    line("unshare-user", r == 0, strerror(errno));
    errno = 0;
    r = syscall(SYS_keyctl, 0, 0, 0, 0, 0);
    line("keyctl", errno != EPERM, strerror(errno));

    /* network */
    int s = socket(AF_INET, SOCK_STREAM, 0);
    struct sockaddr_in in;
    memset(&in, 0, sizeof in);
    in.sin_family = AF_INET;
    in.sin_port = htons(80);
    in.sin_addr.s_addr = htonl(0x01010101);
    errno = 0;
    r = s >= 0 ? connect(s, (struct sockaddr *)&in, sizeof in) : -1;
    line("network", r == 0, strerror(errno));

    /* filesystem */
    const char *ro[] = {"/prover/x", "/run/rf/x", "/setup/x", "/x", "/usr/x", "/sys/devices/system/cpu/x"};
    for (int i = 0; i < 6; i++) {
        int fd = open(ro[i], O_WRONLY | O_CREAT, 0644);
        snprintf(buf, sizeof buf, "write %s", ro[i]);
        line("fs-write", fd >= 0, buf);
        if (fd >= 0) close(fd);
    }
    const char *hidden[] = {"/etc/passwd", "/home", "/root", "/usr/bin/sh", "/bin/sh", "/var", "/proc/1/environ"};
    for (int i = 0; i < 7; i++) {
        int ok = access(hidden[i], F_OK) == 0;
        snprintf(buf, sizeof buf, "exists %s", hidden[i]);
        line("fs-hidden", ok && i != 6, buf);
    }
    int fd = open("/work/ok.txt", O_WRONLY | O_CREAT, 0644);
    line("work-writable", fd < 0, NULL);
    if (fd >= 0) close(fd);
    if (getenv("HOSTILE_ENV_LEAK") || getenv("GITHUB_TOKEN") || getenv("HOME") == NULL ||
        strcmp(getenv("HOME"), "/work"))
        line("env", 1, "an outside variable is visible");
    else
        line("env", 0, NULL);

    /* the service survives garbage */
    int u = socket(AF_UNIX, SOCK_STREAM, 0);
    struct sockaddr_un a;
    memset(&a, 0, sizeof a);
    a.sun_family = AF_UNIX;
    strncpy(a.sun_path, getenv("RF_ORACLE") ? getenv("RF_ORACLE") : "", sizeof a.sun_path - 1);
    if (connect(u, (struct sockaddr *)&a, sizeof a) == 0) {
        unsigned char junk[16] = {9, 9, 9, 9, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255};
        if (write(u, junk, 16) != 16) line("service-garbage", 1, "write failed");
        close(u);
        line("service-garbage", 0, "sent");
    }

    /* plant outputs that must not be read through */
    mkdir("/work/proofs", 0755);
    if (symlink("/etc/hostname", "/work/root.bin")) line("plant", 1, "symlink failed");
    mkfifo("/work/proofs/L0.bin", 0644);
    if (symlink("/etc", "/work/proofs/L1.bin")) line("plant", 1, "symlink failed");
    mkdir("/work/sub", 0755);
    if (symlink("/etc", "/work/proofs/sub")) line("plant", 1, "symlink failed");

    /* a detached grandchild that would outlive the run */
    if (fork() == 0) {
        setsid();
        if (fork() == 0) {
            FILE *f = fopen("/work/orphan.pid", "w");
            if (f) { fprintf(f, "alive\n"); fclose(f); }
            for (;;) pause();
        }
        _exit(0);
    }
    wait(NULL);
    usleep(100000);
    fclose(rep);
    return 0;
}
