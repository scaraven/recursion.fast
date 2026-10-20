// C1 cost probe: keyed BLAKE2s PRF (oracle service) throughput, in-process and over shared memory.
// Build: gcc -O3 -march=native -pthread svc.c -o svc
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <pthread.h>
#include <stdatomic.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <sys/syscall.h>
#include <linux/futex.h>
#include <unistd.h>
#include <immintrin.h>

static const uint32_t IV[8] = {0x6A09E667,0xBB67AE85,0x3C6EF372,0xA54FF53A,0x510E527F,0x9B05688C,0x1F83D9AB,0x5BE0CD19};
static const uint8_t SG[10][16] = {
 {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15},{14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3},
 {11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4},{7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8},
 {9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13},{2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9},
 {12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11},{13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10},
 {6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5},{10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0}};
#define R(x,n) (((x)>>(n))|((x)<<(32-(n))))
#define G(a,b,c,d,x,y) do{a+=b+x;d=R(d^a,16);c+=d;b=R(b^c,12);a+=b+y;d=R(d^a,8);c+=d;b=R(b^c,7);}while(0)
static inline void compress(uint32_t h[8], const uint8_t *blk, uint64_t t, int last){
  uint32_t m[16], v[16];
  memcpy(m, blk, 64);
  for(int i=0;i<8;i++){v[i]=h[i];v[i+8]=IV[i];}
  v[12]^=(uint32_t)t; v[13]^=(uint32_t)(t>>32); if(last) v[14]=~v[14];
  for(int r=0;r<10;r++){const uint8_t*s=SG[r];
    G(v[0],v[4],v[8],v[12],m[s[0]],m[s[1]]); G(v[1],v[5],v[9],v[13],m[s[2]],m[s[3]]);
    G(v[2],v[6],v[10],v[14],m[s[4]],m[s[5]]); G(v[3],v[7],v[11],v[15],m[s[6]],m[s[7]]);
    G(v[0],v[5],v[10],v[15],m[s[8]],m[s[9]]); G(v[1],v[6],v[11],v[12],m[s[10]],m[s[11]]);
    G(v[2],v[7],v[8],v[13],m[s[12]],m[s[13]]); G(v[3],v[4],v[9],v[14],m[s[14]],m[s[15]]);}
  for(int i=0;i<8;i++) h[i]^=v[i]^v[i+8];
}
typedef struct { uint32_t h[8]; } mid_t;
static void prf_init(mid_t *md, const uint8_t key[32]){
  for(int i=0;i<8;i++) md->h[i]=IV[i];
  md->h[0]^=0x01010000u ^ (32u<<8) ^ 32u;
  uint8_t b[64]={0}; memcpy(b,key,32); compress(md->h,b,64,0);   // key block, cached once (midstate)
}
// keyed BLAKE2s-256 of a non-empty message, from the cached midstate
static inline void prf(const mid_t *md, const uint8_t *msg, size_t len, uint8_t out[32]){
  uint32_t h[8]; memcpy(h,md->h,32); uint64_t t=64;
  while(len>64){ t+=64; compress(h,msg,t,0); msg+=64; len-=64; }
  uint8_t b[64]={0}; memcpy(b,msg,len); t+=len; compress(h,b,t,1); memcpy(out,h,32);
}
static double now(void){struct timespec ts;clock_gettime(CLOCK_MONOTONIC,&ts);return ts.tv_sec+ts.tv_nsec*1e-9;}
static size_t nblocks(size_t len){ return (len+63)/64; }

static mid_t MD;
// ---------- in-process multithreaded ----------
typedef struct { int len; long n; uint8_t acc; } targ_t;
static void* worker(void*p){ targ_t*a=p; uint8_t q[4096], o[32]; memset(q,7,sizeof q); uint8_t acc=0;
  for(long i=0;i<a->n;i++){ memcpy(q,&i,8); prf(&MD,q,a->len,o); acc^=o[0]; } a->acc=acc; return 0; }
static double inproc(int len,long n,int T){ pthread_t th[64]; targ_t a[64]; double t0=now();
  for(int i=0;i<T;i++){a[i].len=len;a[i].n=n;pthread_create(&th[i],0,worker,&a[i]);}
  for(int i=0;i<T;i++) pthread_join(th[i],0); return now()-t0; }

// ---------- shared-memory service ----------
#define MAXB 8192
#define MAXLEN 2112
typedef struct {
  _Atomic uint32_t req;      // batch sequence number posted by the client
  _Atomic uint32_t done;     // batch sequence number completed by the server
  _Atomic uint32_t fin;      // workers finished on the current batch
  _Atomic int stop;
  int B, len, W, futex;
  uint8_t q[MAXB][MAXLEN];
  uint8_t a[MAXB][32];
} shm_t;
static shm_t *S;
static long fx(_Atomic uint32_t *addr,int op,uint32_t val){ return syscall(SYS_futex,(uint32_t*)addr,op,val,0,0,0); }
typedef struct { int id; } sarg_t;
static void* sworker(void*p){ int id=((sarg_t*)p)->id; uint32_t seen=0;
  for(;;){
    uint32_t r;
    if(S->futex){ while((r=atomic_load(&S->req))==seen){ if(atomic_load(&S->stop)) return 0; fx(&S->req,FUTEX_WAIT,seen);} }
    else { while((r=atomic_load_explicit(&S->req,memory_order_acquire))==seen){ if(atomic_load(&S->stop)) return 0; _mm_pause(); } }
    seen=r; int B=S->B, W=S->W, len=S->len; int lo=(long)B*id/W, hi=(long)B*(id+1)/W;
    for(int i=lo;i<hi;i++) prf(&MD,S->q[i],len,S->a[i]);
    if(atomic_fetch_add(&S->fin,1)+1==(uint32_t)W){ atomic_store(&S->fin,0); atomic_store_explicit(&S->done,r,memory_order_release); if(S->futex) fx(&S->done,FUTEX_WAKE,1);} }
}
static void server(int W){ pthread_t th[64]; sarg_t a[64];
  for(int i=0;i<W;i++){a[i].id=i;pthread_create(&th[i],0,sworker,&a[i]);} for(int i=0;i<W;i++) pthread_join(th[i],0); }

// client: copy B queries in, post, wait, copy answers out; repeat until n calls
static double client(int B,int len,long n,uint8_t *acc){
  static uint8_t qs[MAXB][MAXLEN], as[MAXB][32]; for(int i=0;i<B;i++) memset(qs[i],i,len);
  uint32_t seq=atomic_load(&S->done); double t0=now(); long calls=0; uint8_t x=0;
  while(calls<n){
    for(int i=0;i<B;i++){ memcpy(qs[i],&calls,8); memcpy(S->q[i],qs[i],len); calls++; }
    seq++; atomic_store_explicit(&S->req,seq,memory_order_release);
    if(S->futex){ fx(&S->req,FUTEX_WAKE,64); while(atomic_load(&S->done)!=seq) fx(&S->done,FUTEX_WAIT,seq-1); }
    else while(atomic_load_explicit(&S->done,memory_order_acquire)!=seq) _mm_pause();
    memcpy(as,S->a,(size_t)B*32); x^=as[B-1][0];
  }
  *acc=x; return (now()-t0)/calls;
}
static void run_service(int B,int len,int W,int fut,long n){
  S->B=B;S->len=len;S->W=W;S->futex=fut;atomic_store(&S->stop,0);atomic_store(&S->req,0);atomic_store(&S->done,0);atomic_store(&S->fin,0);
  pid_t pid=fork(); if(pid==0){ server(W); _exit(0); }
  uint8_t acc; client(B,len,(long)B*8,&acc);         // warm-up
  double per=client(B,len,n,&acc);
  atomic_store(&S->stop,1); atomic_fetch_add(&S->req,1); fx(&S->req,FUTEX_WAKE,64); waitpid(pid,0,0);
  printf("service %-5s W=%2d B=%5d len=%4d : %9.1f ns/call  %8.3f Mcalls/s  %6.2f GB/s query bytes (acc %u)\n",
         fut?"futex":"spin",W,B,len,per*1e9,1e-6/per,len/per*1e-9,acc);
  fflush(stdout);
}

int main(int argc,char**argv){
  uint8_t key[32]; for(int i=0;i<32;i++) key[i]=i; prf_init(&MD,key);
  // known answer: keyed BLAKE2s(key=00..1f, msg = "abc"), checked against python hashlib
  { uint8_t o[32]; prf(&MD,(const uint8_t*)"abc",3,o); printf("KAT keyed blake2s(00..1f,'abc') = "); for(int i=0;i<32;i++)printf("%02x",o[i]); printf("\n"); }
  int lens[]={33,63,64,65,97,2049};
  printf("== in-process, one thread\n");
  for(int k=0;k<6;k++){ int len=lens[k]; long n=len>1000?200000:4000000; double t=inproc(len,n,1);
    printf("inproc T=1 len=%4d : %7.1f ns/call  %6.1f ns/compression (%zu blocks)  %6.3f GB/s\n",len,t/n*1e9,t/n*1e9/nblocks(len),nblocks(len),len*n/t*1e-9); }
  printf("== in-process, T threads (aggregate)\n");
  int Ts[]={1,2,4,8,16,24,32};
  for(int k=0;k<7;k++){ int T=Ts[k]; long n=2000000; double t=inproc(65,n,T);
    printf("inproc T=%2d len=  65 : %8.2f Mcalls/s  %6.1f ns/compression/thread\n",T,T*n/t*1e-6,t/n*1e9/2); }
  for(int k=0;k<7;k++){ int T=Ts[k]; long n=100000; double t=inproc(2049,n,T);
    printf("inproc T=%2d len=2049 : %8.3f Mcalls/s  %6.2f GB/s\n",T,T*n/t*1e-6,2049.0*T*n/t*1e-9); }
  S=mmap(0,sizeof(shm_t),PROT_READ|PROT_WRITE,MAP_SHARED|MAP_ANONYMOUS,-1,0);
  printf("== shared-memory service (client process <-> server process, W server threads)\n");
  run_service(1,65,1,1,200000);
  run_service(1,65,1,0,1000000);
  int Bs[]={16,256,4096};
  for(int b=0;b<3;b++) run_service(Bs[b],65,1,0,4000000);
  for(int b=0;b<3;b++) run_service(Bs[b],65,1,1,4000000);
  int Ws[]={4,8,16,24};
  for(int w=0;w<4;w++) run_service(4096,65,Ws[w],0,16000000);
  for(int w=0;w<4;w++) run_service(4096,65,Ws[w],1,16000000);
  run_service(256,2049,1,0,400000);
  for(int w=0;w<4;w++) run_service(1024,2049,Ws[w],0,1600000);
  return 0;
}
