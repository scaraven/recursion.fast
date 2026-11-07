/* A memory-bound loop for the timing-stability test (infra/tests/noise.sh): THREADS threads (default 4),
 * each running PASSES (default 20) STREAM-triad passes a[i] = b[i] + 3 c[i] over its own three
 * 64 MiB arrays (far beyond the L3). Prints `memloop ns=NS threads=T passes=P sum=X`: NS is the wall
 * time from a barrier that starts every thread to the last one's end. */
#define _GNU_SOURCE
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#define N (8u << 20) /* doubles per array: 64 MiB */
static int passes;
static pthread_barrier_t bar;
static double sums[256];
static uint64_t ns(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec * 1000000000ull + t.tv_nsec; }
static void *work(void *arg) {
    long id = (long)arg;
    double *a = malloc(N * sizeof *a), *b = malloc(N * sizeof *b), *c = malloc(N * sizeof *c);
    for (size_t i = 0; i < N; i++) { a[i] = 0; b[i] = i; c[i] = id; }
    pthread_barrier_wait(&bar);
    for (int p = 0; p < passes; p++)
        for (size_t i = 0; i < N; i++) a[i] = b[i] + 3.0 * c[i] + p;
    double s = 0; for (size_t i = 0; i < N; i += 4096) s += a[i];
    sums[id] = s; free(a); free(b); free(c);
    return NULL;
}
int main(int argc, char **argv) {
    int t = argc > 1 ? atoi(argv[1]) : 4; passes = argc > 2 ? atoi(argv[2]) : 20;
    if (t < 1 || t > 256) return 2;
    pthread_t th[256]; pthread_barrier_init(&bar, NULL, t + 1);
    for (long i = 0; i < t; i++) pthread_create(&th[i], NULL, work, (void *)i);
    pthread_barrier_wait(&bar);
    uint64_t t0 = ns();
    for (int i = 0; i < t; i++) pthread_join(th[i], NULL);
    uint64_t dt = ns() - t0; double s = 0; for (int i = 0; i < t; i++) s += sums[i];
    printf("memloop ns=%llu threads=%d passes=%d sum=%g\n", (unsigned long long)dt, t, passes, s);
    return 0;
}
