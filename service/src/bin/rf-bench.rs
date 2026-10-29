//! `rf-bench`: measurement client for `rf-oracle` (untrusted tooling, not part of the runtime).
//!
//!   rf-bench SOCKET latency N                          round trip of one 32-byte QUERY, N times
//!   rf-bench SOCKET throughput THREADS BATCH SIZE SECS QUERY batches of BATCH queries of SIZE bytes
//!   rf-bench SOCKET sign THREADS ITEMS SECS            SIGN of ITEMS 64-byte queries
//!   rf-bench SOCKET check                              one SIGN, verified against VK
//!
//! Output: one line of `key=value` pairs.

use rf_oracle::proto::Client;
use rf_oracle::{trace_digest, wots};
use std::time::{Duration, Instant};

fn arg<T: std::str::FromStr>(a: &[String], i: usize) -> T {
    a.get(i).and_then(|s| s.parse().ok()).unwrap_or_else(|| {
        eprintln!("rf-bench: bad or missing argument {i}");
        std::process::exit(2)
    })
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let sock: String = arg(&a, 1);
    let mode: String = arg(&a, 2);
    match mode.as_str() {
        "latency" => {
            let n: usize = arg(&a, 3);
            let mut c = Client::connect(&sock).unwrap();
            let q = [7u8; 32];
            for _ in 0..1000.min(n) {
                c.query(&[&q]).unwrap();
            }
            let mut ts: Vec<f64> = (0..n)
                .map(|_| {
                    let t = Instant::now();
                    c.query(&[&q]).unwrap();
                    t.elapsed().as_secs_f64() * 1e6
                })
                .collect();
            ts.sort_by(|x, y| x.partial_cmp(y).unwrap());
            let mean = ts.iter().sum::<f64>() / n as f64;
            println!(
                "mode=latency n={n} median_us={:.2} p10_us={:.2} p99_us={:.2} mean_us={mean:.2}",
                ts[n / 2],
                ts[n / 10],
                ts[n * 99 / 100]
            );
        }
        "throughput" | "sign" => {
            let threads: usize = arg(&a, 3);
            let batch: usize = arg(&a, 4);
            let (size, secs): (usize, f64) = if mode == "sign" { (64, arg(&a, 5)) } else { (arg(&a, 5), arg(&a, 6)) };
            let dur = Duration::from_secs_f64(secs);
            let res: Vec<(u64, u64, f64)> = std::thread::scope(|s| {
                let hs: Vec<_> = (0..threads)
                    .map(|t| {
                        let sock = sock.clone();
                        let mode = mode.clone();
                        s.spawn(move || {
                            let mut c = Client::connect(&sock).unwrap();
                            let data: Vec<Vec<u8>> =
                                (0..batch).map(|i| (0..size).map(|k| (i * 31 + k * 7 + t) as u8).collect()).collect();
                            let refs: Vec<&[u8]> = data.iter().map(|d| d.as_slice()).collect();
                            let (mut calls, mut reqs) = (0u64, 0u64);
                            let t0 = Instant::now();
                            while t0.elapsed() < dur {
                                if mode == "sign" {
                                    // all 2^16 one-time keys used: the measurement ends there
                                    if c.sign(&refs).is_err() {
                                        break;
                                    }
                                } else {
                                    c.query(&refs).unwrap();
                                }
                                calls += batch as u64;
                                reqs += 1;
                            }
                            (calls, reqs, t0.elapsed().as_secs_f64())
                        })
                    })
                    .collect();
                hs.into_iter().map(|h| h.join().unwrap()).collect()
            });
            let calls: u64 = res.iter().map(|r| r.0).sum();
            let reqs: u64 = res.iter().map(|r| r.1).sum();
            let el = res.iter().map(|r| r.2).fold(0.0, f64::max);
            println!(
                "mode={mode} threads={threads} batch={batch} size={size} requests_per_s={:.0} calls_per_s={:.0} MB_per_s={:.1} us_per_request={:.2}",
                reqs as f64 / el,
                calls as f64 / el,
                calls as f64 * size as f64 / el / 1e6,
                el * 1e6 * threads as f64 / reqs as f64
            );
        }
        "local" => {
            // in-process hashing speed (no socket): rf-bench - local BATCH SIZE
            let batch: usize = arg(&a, 3);
            let size: usize = arg(&a, 4);
            let kd = rf_oracle::blake2s::Keyed::new(&[9u8; 32]);
            let data: Vec<Vec<u8>> = (0..batch).map(|i| (0..size).map(|k| (i * 31 + k * 7) as u8).collect()).collect();
            let refs: Vec<&[u8]> = data.iter().map(|d| d.as_slice()).collect();
            let mut out = vec![[0u8; 32]; batch];
            let t0 = Instant::now();
            let mut reps = 0u64;
            while t0.elapsed() < Duration::from_secs(1) {
                kd.eval_many(&refs, &mut out);
                reps += 1;
            }
            let el = t0.elapsed().as_secs_f64();
            let blocks = (size.div_ceil(64).max(1) * batch) as f64 * reps as f64;
            println!(
                "mode=local batch={batch} size={size} simd={} ns_per_query={:.1} ns_per_block={:.1}",
                rf_oracle::blake2s::has_avx2(),
                el * 1e9 / (reps as f64 * batch as f64),
                el * 1e9 / blocks
            );
        }
        "check" => {
            let mut c = Client::connect(&sock).unwrap();
            let vk = c.vk().unwrap();
            let qs: Vec<Vec<u8>> = (0..5).map(|i| vec![i as u8; i * 40]).collect();
            let refs: Vec<&[u8]> = qs.iter().map(|q| q.as_slice()).collect();
            let (ans, sig) = c.sign(&refs).unwrap();
            assert_eq!(ans, c.query(&refs).unwrap());
            let ok = wots::verify(&vk, &trace_digest(&refs, &ans), &sig);
            println!("mode=check idx={} verified={ok}", sig.idx);
            if !ok {
                std::process::exit(1)
            }
        }
        _ => {
            eprintln!("rf-bench: unknown mode {mode}");
            std::process::exit(2)
        }
    }
}
