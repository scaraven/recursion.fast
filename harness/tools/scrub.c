/* The runner's scrub of the per-CPU inode counters (TRUSTED RUNTIME; `rfh.bench.Bench.scrub`), run
 * before every request with no entry process alive.
 *
 *   scrub [B]    one thread per CPU it can pin itself to (every CPU a prover could use); B, a
 *                power of two up to 65536 (default 0): also take U uniform in [0, B) fresh batches
 *                of each kind from the machine-wide counters, U drawn from the CSPRNG per kind
 *
 * The inode numbers of pipes, sockets, procfs and other pseudo files (`get_next_ino`) and of memfds
 * (the kernel's internal tmpfs) come from per-CPU counters handed out in batches of 1024 from a
 * machine-wide one. A request pinned to a CPU that makes K pipes moves that CPU's counter by K, and
 * a later request on the CPU reads K from its first pipe's inode number: about 10 bits per CPU and
 * counter, every request. On each CPU this program reads both counters, takes each to the end of its
 * batch (so that the CPU's next number comes from a fresh batch) and then draws `r` uniform in
 * [0, 1024) from the CSPRNG and makes `r` more: a later request finds each CPU's offset uniform and
 * independent of what an earlier request did there. Which batch a CPU holds still reflects the
 * machine-wide count of batches; with B (before every timed request, the season's `scrub_batches`)
 * the threads first make U·1024 more of each kind between them, which takes exactly U fresh
 * batches machine-wide, so that count reaches a later request only under a uniform noise of B
 * batches (it is not closed: AGENTS.md §12 says what is left and what it is worth).
 *
 * Output: `cpus=N pipes=P memfds=F batches=B` on success (exit 0); a message and exit 1 otherwise. */
#define _GNU_SOURCE
#include <fcntl.h>
#include <pthread.h>
#include <sched.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <sys/random.h>
#include <sys/stat.h>
#include <unistd.h>

#define BATCH 1024

struct job {
    int cpu, err;
    long pipes, memfds;
    long more_pipes, more_memfds;      /* whole batches to take first (`scrub B`) */
};

static long ino_pipe(void) {
    int p[2];
    struct stat st;
    if (pipe2(p, O_CLOEXEC)) return -1;
    long r = fstat(p[0], &st) ? -1 : (long)st.st_ino;
    close(p[0]);
    close(p[1]);
    return r;
}

static long ino_memfd(void) {
    struct stat st;
    int f = memfd_create("rf-scrub", MFD_CLOEXEC);
    if (f < 0) return -1;
    long r = fstat(f, &st) ? -1 : (long)st.st_ino;
    close(f);
    return r;
}

static unsigned draw(void) {
    unsigned r;
    if (getrandom(&r, sizeof r, 0) != sizeof r) return 0xFFFFFFFFu;
    return r % BATCH;
}

/* make one number, then as many as end its batch (`last` is the offset of a batch's last number:
 * get_next_ino's batches end at 0 mod 1024, the internal tmpfs's at 1023), then r uniform more */
static long scrub(long (*make)(void), long last, int *err) {
    long v = make(), n = 1;
    unsigned r = draw();
    if (v < 0 || r == 0xFFFFFFFFu) {
        *err = 1;
        return n;
    }
    long k = ((last - v) % BATCH + BATCH) % BATCH + r;
    for (long i = 0; i < k; i++, n++)
        if (make() < 0) {
            *err = 1;
            return n;
        }
    return n;
}

static void *run(void *a) {
    struct job *j = a;
    cpu_set_t s;
    CPU_ZERO(&s);
    CPU_SET(j->cpu, &s);
    if (sched_setaffinity(0, sizeof s, &s)) {
        j->err = 1;
        return 0;
    }
    /* the machine-wide batches first, then the CPU's own offset (so it stays uniform) */
    for (long i = 0; i < j->more_pipes * BATCH && !j->err; i++, j->pipes++)
        if (ino_pipe() < 0) j->err = 1;
    for (long i = 0; i < j->more_memfds * BATCH && !j->err; i++, j->memfds++)
        if (ino_memfd() < 0) j->err = 1;
    j->pipes += scrub(ino_pipe, 0, &j->err);
    j->memfds += scrub(ino_memfd, BATCH - 1, &j->err);
    return 0;
}

/* U uniform in [0, b) from the CSPRNG (b a power of two divides 2^32: no bias), -1 on failure */
static long draw_below(long b) {
    unsigned r;
    if (b <= 1) return 0;
    if (getrandom(&r, sizeof r, 0) != sizeof r) return -1;
    return (long)(r % (unsigned)b);
}

int main(int argc, char **argv) {
    long B = 0;
    if (argc > 2 || (argc == 2 && ((B = strtol(argv[1], 0, 10)) < 1 || B > 65536 || (B & (B - 1))))) {
        fprintf(stderr, "usage: scrub [B]   (B a power of two, 1 to 65536)\n");
        return 1;
    }
    /* every CPU a process may be pinned to, not only this one's affinity: a prover may widen its
     * own (sched_setaffinity) where the job's CPUs are set by taskset rather than by a cpuset; a
     * CPU no process here can use (offline, outside the cpuset) refuses the pin and is skipped */
    static struct job jobs[CPU_SETSIZE];
    static pthread_t th[CPU_SETSIZE];
    int n = 0, bad = 0;
    for (int c = 0; c < CPU_SETSIZE; c++) {
        cpu_set_t one;
        CPU_ZERO(&one);
        CPU_SET(c, &one);
        if (sched_setaffinity(0, sizeof one, &one) == 0) jobs[n] = (struct job){.cpu = c}, n++;
    }
    if (!n) {
        fprintf(stderr, "scrub: no CPU to pin to\n");
        return 1;
    }
    long up = draw_below(B), um = draw_below(B);
    if (up < 0 || um < 0) {
        fprintf(stderr, "scrub: a random draw failed\n");
        return 1;
    }
    for (int i = 0; i < n; i++)      /* U batches of each kind, spread over the threads */
        jobs[i].more_pipes = up / n + (i < up % n), jobs[i].more_memfds = um / n + (i < um % n);
    for (int i = 0; i < n; i++)
        if (pthread_create(&th[i], 0, run, &jobs[i])) jobs[i].err = 1, th[i] = 0;
    long p = 0, f = 0;
    for (int i = 0; i < n; i++) {
        if (th[i]) pthread_join(th[i], 0);
        bad |= jobs[i].err;
        p += jobs[i].pipes, f += jobs[i].memfds;
    }
    if (bad) {
        fprintf(stderr, "scrub: a pipe, a memfd, a random draw or a CPU pin failed\n");
        return 1;
    }
    printf("cpus=%d pipes=%ld memfds=%ld batches=%ld\n", n, p, f, B);
    return 0;
}
