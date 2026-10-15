#!/usr/bin/env python3
"""S9 incentives probe: the record rule against noise, and the level-2 majority of S_rec.

  python3 -I probes/s9/incentives/noise_sim.py [--trials 20000] [--seed 1]

Noise model (relative, Gaussian; a step's time is mu_level * (1 + e_sess + e_run + e_step)):
  e_sess  one draw per evaluation (session drift: thermal state, frequency, memory placement,
          background; the same for every run of the evaluation),
  e_run   one draw per run,
  e_step  one draw per step.
The score is the runner's: S = median over runs of the per-run median over the 31 node steps of
levels >= 2 (16 + 8 + 4 + 2 + 1). Calibration from the only measurement there is (Stage 6b, a
shared VM, 0.17 s steps, harness/reference-machine.md §5): single processes vary by 13-26 %
(max-min of 10), i.e. sigma_step ~ 5-8 %; three evaluations' S moved by 1.8-5.9 % (max-min of 3),
i.e. sigma_S ~ 1-3.5 %. Since the median over 93 step times would bring sigma_step = 6 % down to
~0.8 %, most of the measured spread is correlated (session/run) noise, which more runs in the same
session do not remove.

Part A: false-record probability. Two entries with the SAME true speed; the challenger is a record
iff S_new <= (1 - m) * S_old. Unpaired = the standing record's number is from another session (the
current rule, DESIGN §6.4); paired = both are evaluated in one session, interleaved run by run on
the same instances, and the record test uses the median over runs of the per-run ratio (session
drift cancels; the run-level drift is shared by adjacent runs to a degree `share`).
Part B: power: a challenger truly 5 % / 10 % faster, same rules.
Part C: sybil: probability that at least one of k identical resubmissions takes the record.
Part D: S_rec under the "pre-digested level 2" schedule of finding S9I-M2, and under the proposed
statistic max over levels {2, 3, 4-6} of the per-level medians; the noise inflation of that
statistic for an honest uniform entry.
"""
import argparse, random, statistics as st

LEVELS = [(2, 16), (3, 8), (4, 4), (5, 2), (6, 1)]


def score_runs(rng, mu_by_level, R, s_sess, s_run, s_step, sess=None, runs=None):
    """Per-run step lists; returns (per-run medians, per-run per-level medians)."""
    e_s = rng.gauss(0, s_sess) if sess is None else sess
    out, lv = [], []
    for r in range(R):
        e_r = rng.gauss(0, s_run) if runs is None else runs[r]
        steps, per = [], {}
        for level, cnt in LEVELS:
            xs = [mu_by_level[level] * (1 + e_s + e_r + rng.gauss(0, s_step)) for _ in range(cnt)]
            steps += xs
            per[level] = xs
        out.append(st.median(steps))
        lv.append(per)
    return out, lv


def false_record(rng, trials, R, m, s_sess, s_run, s_step, paired, share=0.5, gain=0.0):
    mu = {l: 1.0 for l, _ in LEVELS}
    muC = {l: 1.0 - gain for l, _ in LEVELS}
    hits = 0
    for _ in range(trials):
        if paired:
            sess = rng.gauss(0, s_sess)
            common = [rng.gauss(0, s_run) * share ** 0.5 for _ in range(R)]
            ownA = [c + rng.gauss(0, s_run) * (1 - share) ** 0.5 for c in common]
            ownB = [c + rng.gauss(0, s_run) * (1 - share) ** 0.5 for c in common]
            a, _ = score_runs(rng, mu, R, s_sess, s_run, s_step, sess=sess, runs=ownA)
            b, _ = score_runs(rng, muC, R, s_sess, s_run, s_step, sess=sess, runs=ownB)
            ratio = st.median([y / x for x, y in zip(a, b)])
            hits += ratio <= 1 - m
        else:
            a, _ = score_runs(rng, mu, R, s_sess, s_run, s_step)
            b, _ = score_runs(rng, muC, R, s_sess, s_run, s_step)
            hits += st.median(b) <= (1 - m) * st.median(a)
    return hits / trials


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--trials", type=int, default=20000)
    ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    T = a.trials

    print("# Part A/B/C: record rule. sigma = (session, run, step), relative")
    regimes = [("VM placeholder (S6b)", 0.02, 0.01, 0.06),
               ("reference, plausible", 0.01, 0.005, 0.03),
               ("reference, quiet", 0.005, 0.003, 0.02)]
    rules = [("current: unpaired, R=3, m=3%", False, 3, 0.03),
             ("unpaired, R=5, m=5%", False, 5, 0.05),
             ("paired, R=3, m=3%", True, 3, 0.03),
             ("paired, R=5, m=3%", True, 5, 0.03)]
    for name, ss, sr, sp in regimes:
        print(f"\n## {name}: sigma_sess={ss:.1%} sigma_run={sr:.1%} sigma_step={sp:.1%}")
        print("| rule | P(false record), 1 try | P(false record), 10 tries | power, 5 % faster | power, 10 % faster |")
        print("|---|---:|---:|---:|---:|")
        for rname, paired, R, m in rules:
            p0 = false_record(rng, T, R, m, ss, sr, sp, paired)
            p5 = false_record(rng, T // 4, R, m, ss, sr, sp, paired, gain=0.05)
            p10 = false_record(rng, T // 4, R, m, ss, sr, sp, paired, gain=0.10)
            print(f"| {rname} | {p0:.2%} | {1 - (1 - p0) ** 10:.1%} | {p5:.1%} | {p10:.1%} |")

    print("\n# Part D: S_rec statistics (relative to the steady-state step cost 1.0)")
    # S9I-M2 schedule: W steps emit 'cheap-to-verify' proofs (mode B, unranked); level 2 verifies
    # them (cost c2 < 1) and emits ordinary proofs; levels >= 3 pay the steady-state 1.0.
    for c2 in (0.75, 0.5, 0.25):
        mu = {2: c2, 3: 1.0, 4: 1.0, 5: 1.0, 6: 1.0}
        meds, maxs = [], []
        for _ in range(T // 10):
            runs, lv = score_runs(rng, mu, 3, 0.0, 0.005, 0.03)
            meds.append(st.median(runs))
            per = {g: st.median([st.median(sum((r[l] for l in g), [])) for r in lv])
                   for g in ((2,), (3,), (4, 5, 6))}
            maxs.append(max(per.values()))
        print(f"level-2 cost {c2:.2f}: current S_rec (median over 31) = {st.median(meds):.3f}; "
              f"proposed max(m2, m3, m4-6) = {st.median(maxs):.3f}")
    # inflation of the proposed statistic for an honest uniform entry
    for ss, sr, sp in ((0.0, 0.005, 0.03), (0.0, 0.01, 0.06)):
        mu = {l: 1.0 for l, _ in LEVELS}
        meds, maxs, mx_sd, md_sd = [], [], [], []
        for _ in range(T // 10):
            runs, lv = score_runs(rng, mu, 3, ss, sr, sp)
            meds.append(st.median(runs))
            per = [st.median([st.median(sum((r[l] for l in g), [])) for r in lv]) for g in ((2,), (3,), (4, 5, 6))]
            maxs.append(max(per))
        print(f"uniform entry, sigma_run={sr:.1%} sigma_step={sp:.1%}: median-over-31 mean {st.mean(meds):.4f} "
              f"(sd {st.pstdev(meds):.2%}); max-of-3-groups mean {st.mean(maxs):.4f} (sd {st.pstdev(maxs):.2%})")


if __name__ == "__main__":
    main()
