// f2.rs : F2 author (own code, written 2026-11-25). Modes: ctl | lem | dc | alg | thr
// Units: t in R/Z; window J(D)=[a/D-1/K, a/D+1/K], K=(2N-1)N^2, a*r=1 mod D; Bad_w={t: ||w t||<1/N};
// cov_w(D)=|Bad_w cap J(D)|/|J(D)| (exact rational ov/(2 N w D), ov integer, i128).
use std::env;

fn gcd(a: i64, b: i64) -> i64 { if b == 0 { a.abs() } else { gcd(b, a % b) } }
fn inv(r: i64, d: i64) -> i64 {
    let (mut t, mut nt, mut rr, mut nr) = (0i64, 1i64, d, r.rem_euclid(d));
    while nr != 0 { let q = rr / nr; let x = t - q * nt; t = nt; nt = x; let y = rr - q * nr; rr = nr; nr = y; }
    assert!(rr == 1);
    t.rem_euclid(d)
}
// exact overlap numerator and number of arcs with positive overlap
fn cov_num(n: i128, d: i128, a: i128, w: i128) -> (i128, u32) {
    let k = (2 * n - 1) * n * n;
    let jl = a * k - d; let jr = a * k + d; let dk = d * k;
    let cmin = (jl * w).div_euclid(dk) - 1; let cmax = (jr * w).div_euclid(dk) + 1;
    let (jlw, jrw) = (jl * n * w, jr * n * w);
    let mut ov = 0i128; let mut na = 0u32;
    let mut c = cmin;
    while c <= cmax {
        let lo = std::cmp::max((c * n - 1) * dk, jlw); let hi = std::cmp::min((c * n + 1) * dk, jrw);
        if hi > lo { ov += hi - lo; na += 1; }
        c += 1;
    }
    (ov, na)
}
fn cov(n: i64, d: i64, a: i64, w: i64) -> (f64, u32) {
    let (ov, na) = cov_num(n as i128, d as i128, a as i128, w as i128);
    (ov as f64 / (2.0 * n as f64 * w as f64 * d as f64), na)
}
fn window(n: i64, r: i64) -> Vec<(i64, i64)> { // (D, a)
    let mut v = vec![];
    for d in (n + 1 + r)..=(2 * n - 1) { if gcd(d, r) == 1 { v.push((d, inv(r, d))); } }
    v
}
fn is_osc(n: i64, w: i64) -> bool { 2 * (w as i128) >= ((2 * n - 1) * n * (n - 2)) as i128 }

struct Bb { n: usize, comp: Vec<u128>, w: Vec<f64>, best: f64, nodes: u64, cap: u64, cur: Vec<usize>, bestset: Vec<usize> }
impl Bb {
    fn rec(&mut self, cand: u128, cur: f64) {
        self.nodes += 1;
        if cur > self.best { self.best = cur; self.bestset = self.cur.clone(); }
        if self.nodes > self.cap || cand == 0 { return; }
        let mut rem = 0.0; let mut c = cand;
        while c != 0 { let i = c.trailing_zeros() as usize; rem += self.w[i]; c &= c - 1; }
        if cur + rem <= self.best + 1e-12 { return; }
        let i = cand.trailing_zeros() as usize;
        let ci = cand & !(1u128 << i);
        let inc = ci & self.comp[i];
        self.cur.push(i); self.rec(inc, cur + self.w[i]); self.cur.pop();
        self.rec(ci, cur);
    }
}
// max weight pairwise coprime subset. items sorted by weight desc internally. returns (best, resolved)
fn maxcop(items: &[(i64, f64)], cap: u64) -> (f64, bool) { let (a, b, _) = maxcop_set(items, cap); (a, b) }
fn maxcop_set(items: &[(i64, f64)], cap: u64) -> (f64, bool, Vec<i64>) {
    let mut it: Vec<(i64, f64)> = items.iter().cloned().filter(|x| x.1 > 0.0).collect();
    it.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
    let n = it.len();
    assert!(n <= 128, "too many items {}", n);
    let mut comp = vec![0u128; n];
    for i in 0..n { for j in 0..n { if i != j && gcd(it[i].0, it[j].0) == 1 { comp[i] |= 1u128 << j; } } }
    let all: u128 = if n == 128 { !0 } else { (1u128 << n) - 1 };
    let mut b = Bb { n, comp, w: it.iter().map(|x| x.1).collect(), best: 0.0, nodes: 0, cap, cur: vec![], bestset: vec![] };
    let _ = b.n;
    b.rec(all, 0.0);
    let set: Vec<i64> = b.bestset.iter().map(|&i| it[i].0).collect();
    (b.best, b.nodes <= cap, set)
}

struct Rng(u64);
impl Rng { fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 } fn below(&mut self, m: u64) -> u64 { self.next() % m } }

fn arg(a: &Vec<String>, i: usize) -> i64 { a[i].parse().unwrap() }

fn ctl() {
    // (1) grid control of cov against a brute grid
    let mut rng = Rng(88172645463325252);
    let mut maxdiff = 0.0f64; let mut cases = 0;
    for _ in 0..1500 {
        let n = 12 + rng.below(60) as i64; let r = 1 + rng.below((n - 2) as u64) as i64;
        let win = window(n, r); if win.is_empty() { continue; }
        let (d, a) = win[rng.below(win.len() as u64) as usize];
        let w = n + 1 + rng.below((3 * n * n * n) as u64) as i64;
        let (c, _) = cov(n, d, a, w);
        let k = ((2 * n - 1) * n * n) as f64;
        let m = 40001;
        let mut cnt = 0;
        for j in 0..m {
            let t = a as f64 / d as f64 + (-1.0 + 2.0 * (j as f64 + 0.5) / m as f64) / k;
            let x = w as f64 * t; let dist = (x - x.round()).abs();
            if dist < 1.0 / n as f64 { cnt += 1; }
        }
        let g = cnt as f64 / m as f64;
        maxdiff = maxdiff.max((g - c).abs()); cases += 1;
    }
    println!("ctl1 grid control: {} cases, max |grid-exact| = {:.3e} (grid step 2.5e-5 per edge)", cases, maxdiff);
    // (2) planted known exceptions: dead windows
    let dead = |n: i64, r: i64, ws: &[i64]| -> Vec<(i64, f64)> {
        window(n, r).iter().map(|&(d, a)| (d, ws.iter().map(|&w| cov(n, d, a, w).0).sum::<f64>())).collect()
    };
    for (n, r, ws) in [(13i64, 6i64, vec![69i64]), (20, 6, vec![29, 31]), (21, 6, vec![29, 31]), (29, 12, vec![31, 94, 98])] {
        let v = dead(n, r, &ws);
        let s: Vec<String> = v.iter().map(|(d, c)| format!("{}:{:.4}", d, c)).collect();
        let dd: Vec<(i64, f64)> = v.iter().filter(|x| x.1 >= 1.0 - 1e-9).map(|x| (x.0, 1.0)).collect();
        let (mx, _) = maxcop(&dd, 3_000_000);
        println!("ctl2 [{}]-{}+{:?}: acc per modulus {} ; max pairwise-coprime dead = {}", n, r, ws, s.join(" "), mx);
    }
}

fn lem(n0: i64, n1: i64, wfac: i64) {
    let mut viol = 0u64; let mut unres = 0u64;
    let mut total_cases = 0u64;
    for n in n0..=n1 {
        let wmax = if wfac > 0 { wfac * n * n * n } else { (-wfac) * n * n };
        let mut best_cop = 0.0f64; let mut arg = (0, 0, 0); let mut best_plain = 0.0f64; let mut osc_max = 0.0f64; let mut maxpos = 0usize;
        let mut ncase = 0u64; let mut nosc = 0u64; let mut arcviol = 0u64;
        for r in 1..=(n - 2) {
            let win = window(n, r); if win.is_empty() { continue; }
            for w in (n + 1)..=wmax {
                let osc = is_osc(n, w);
                let mut items: Vec<(i64, f64)> = Vec::with_capacity(win.len());
                let mut plain = 0.0;
                for &(d, a) in &win {
                    let (c, na) = cov(n, d, a, w);
                    if osc { let x = c * n as f64; if x > osc_max { osc_max = x; } if x > 7.0 { viol += 1; } }
                    else { if na > 1 { arcviol += 1; } }
                    if c > 0.0 { items.push((d, c)); plain += c; }
                }
                ncase += 1;
                if osc { nosc += 1; continue; }
                if items.len() > maxpos { maxpos = items.len(); }
                if plain > best_plain { best_plain = plain; }
                if plain > best_cop + 1e-9 {
                    let (b, ok) = maxcop(&items, 3_000_000);
                    if !ok { unres += 1; }
                    if b > best_cop { best_cop = b; arg = (n, r, w); }
                    if b > 8.0 + 1e-9 { viol += 1; }
                }
            }
        }
        total_cases += ncase;
        println!("N={} cases={} (osc {}) maxCoprimeTotal={:.4} at (N,r,w)={:?} maxPlainTotal={:.3} maxPosModuli={} maxOscCov*N={:.3} arcviol={}", n, ncase, nosc, best_cop, arg, best_plain, maxpos, osc_max, arcviol);
        viol += arcviol;
    }
    println!("LEM done N={}..{} wmax={}N^3 cases={} violations={} unresolved_bb={}", n0, n1, wfac, total_cases, viol, unres);
}

// double-count adversary
fn dc(k: usize, n: i64, r: i64, wmax: i64, pool_p: usize, beam_b: usize, seed: u64) {
    let win = window(n, r); let m = win.len();
    if m == 0 { println!("DC k={} N={} r={} empty window", k, n, r); return; }
    let omega = ((2 * n - 1) * n * (n - 2)) / 2; // floor; osc iff 2w>=(2N-1)N(N-2)
    let mut rng = Rng(seed);
    // small pool (non-oscillating)
    let top = wmax.min(omega - 1);
    let mut sums: Vec<(f64, i64)> = Vec::new();
    for w in (n + 1)..=top {
        let mut s = 0.0; for &(d, a) in &win { s += cov(n, d, a, w).0; }
        if s > 0.0 { sums.push((s, w)); }
    }
    sums.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
    let mut small: Vec<i64> = sums.iter().take(pool_p).map(|x| x.1).collect();
    // add structured: 2r, and speeds near multiples of moduli
    if 2 * r > n { small.push(2 * r); }
    for &(d, _) in win.iter().take(8) { for e in -3i64..=3 { let w = d * (n + 1 + e.abs()) + e * r; if w > n && w < omega { small.push(w); } } }
    small.sort(); small.dedup();
    let covvec = |w: i64| -> Vec<f64> { win.iter().map(|&(d, a)| cov(n, d, a, w).0).collect() };
    let small_v: Vec<(i64, Vec<f64>)> = small.iter().map(|&w| (w, covvec(w))).collect();
    // oscillating pool
    let mut osc: Vec<i64> = vec![];
    for _ in 0..300 { osc.push(omega + 1 + rng.below((2 * omega) as u64) as i64); }
    let mut osc_v: Vec<(i64, Vec<f64>)> = osc.iter().map(|&w| (w, covvec(w))).collect();
    osc_v.sort_by(|a, b| { let sa: f64 = a.1.iter().sum(); let sb: f64 = b.1.iter().sum(); sb.partial_cmp(&sa).unwrap() });
    osc_v.truncate(60);
    let mut osc_cov_n = 0.0f64; for (_, v) in &osc_v { for c in v { osc_cov_n = osc_cov_n.max(c * n as f64); } }
    let mut small_cov_max = 0.0f64; for (_, v) in &small_v { for c in v { small_cov_max = small_cov_max.max(*c); } }
    let score = |acc: &Vec<f64>| -> f64 { acc.iter().map(|x| x.min(1.0)).sum::<f64>() };
    println!("DC k={} N={} r={} m={} smallpool={} oscpool={} max osc cov*N={:.3} (7)", k, n, r, m, small_v.len(), osc_v.len(), osc_cov_n);
    for pp in 0..=k {
        // beam over small pool for k-pp steps, then greedy osc for pp steps
        let mut beams: Vec<(Vec<usize>, Vec<f64>)> = vec![(vec![], vec![0.0; m])];
        for _step in 0..(k - pp) {
            let mut cands: Vec<(f64, Vec<usize>, Vec<f64>)> = vec![];
            for (idx, acc) in &beams {
                for (j, (_, v)) in small_v.iter().enumerate() {
                    if idx.contains(&j) { continue; }
                    let na: Vec<f64> = acc.iter().zip(v).map(|(x, y)| x + y).collect();
                    let mut ni = idx.clone(); ni.push(j); ni.sort();
                    cands.push((score(&na), ni, na));
                }
            }
            cands.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
            let mut nb: Vec<(Vec<usize>, Vec<f64>)> = vec![];
            for c in cands { if nb.iter().any(|x| x.0 == c.1) { continue; } nb.push((c.1, c.2)); if nb.len() >= beam_b { break; } }
            beams = nb;
        }
        // osc steps
        let mut final_sets: Vec<(Vec<usize>, Vec<usize>, Vec<f64>)> = vec![];
        for (idx, acc) in &beams {
            let mut acc = acc.clone(); let mut oi: Vec<usize> = vec![];
            for _ in 0..pp {
                let mut bj = 0; let mut bs = -1.0;
                for (j, (_, v)) in osc_v.iter().enumerate() {
                    if oi.contains(&j) { continue; }
                    let na: Vec<f64> = acc.iter().zip(v).map(|(x, y)| x + y).collect();
                    let s = score(&na); if s > bs { bs = s; bj = j; }
                }
                for (x, y) in acc.iter_mut().zip(&osc_v[bj].1) { *x += y; }
                oi.push(bj);
            }
            final_sets.push((idx.clone(), oi, acc));
        }
        let mut best = (0.0f64, vec![], vec![], 0.0f64, 0.0f64); let mut near = 0; let mut unres = 0;
        for (idx, oi, acc) in &final_sets {
            let dead: Vec<(i64, f64)> = win.iter().zip(acc).filter(|(_, a)| **a >= 1.0 - 1e-9).map(|(wd, _)| (wd.0, 1.0)).collect();
            for a in acc { if (*a - 1.0).abs() < 1e-6 { near += 1; } }
            let (mx, ok, fam) = maxcop_set(&dead, 3_000_000); if !ok { unres += 1; }
            if mx > best.0 {
                // sum of Q over the best dead family F* (Q = small-speed coverage only)
                let fset: Vec<i64> = fam.clone();
                let mut qs = 0.0; let mut os = 0.0;
                for (j, &(d, _)) in win.iter().enumerate() { if fset.contains(&d) { for &s in idx { qs += small_v[s].1[j]; } for &o in oi { os += osc_v[o].1[j]; } } }
                best = (mx, idx.clone(), oi.clone(), qs, os);
            }
        }
        let bound = if pp == 0 { 8.0 * k as f64 } else { 8.0 * (k - pp) as f64 / (1.0 - 7.0 * pp as f64 / n as f64) };
        let ws: Vec<i64> = best.1.iter().map(|&i| small_v[i].0).collect();
        let os: Vec<i64> = best.2.iter().map(|&i| osc_v[i].0).collect();
        println!("  p'={} deadmax(pairwise-coprime dead, lower bound over basis)={} bound 8p/(1-7p'/N)={:.2} 8k={} ratio={:.3} | sumQ over dead set={:.2} (<=8p={}) | W_small={:?} W_osc={:?} near-ties={} unresolved={}",
            pp, best.0, bound, 8 * k, best.0 / (8 * k) as f64, best.3, 8 * (k - pp), ws, os, near, unres);
        if best.0 > bound + 1e-9 { println!("  *** VIOLATION of the double count bound ***"); }
    }
}

fn alg() {
    // exact integer check: for N > 7k, 0<=p'<=k: dead-bound 8(k-p')/(1-7p'/N) <= 8k  <=>  (k-p') N <= k (N - 7p')
    let mut bad = 0u64; let mut cnt = 0u64;
    for k in 1i64..=300 { for n in (7 * k + 1)..=(7 * k + 4000) { for pp in 0..=k {
        cnt += 1;
        if (k - pp) * n > k * (n - 7 * pp) { bad += 1; }
    } } }
    println!("ALG1 (k-p')N <= k(N-7p') for k<=300, 7k<N<=7k+4000, 0<=p'<=k: {} cases, {} violations", cnt, bad);
    // and the boundary: at N=7k it is an equality, at N=7k-1 it fails for p'>=1
    let mut f = 0; for k in 1i64..=300 { let n = 7 * k; for pp in 1..=k { if (k - pp) * n != k * (n - 7 * pp) { f += 1; } } }
    println!("ALG1b equality at N=7k (p'>=1): mismatches {}", f);
    let mut g = 0; let mut c2 = 0; for k in 1i64..=300 { let n = 7 * k - 1; for pp in 1..=k { c2 += 1; if (k - pp) * n > k * (n - 7 * pp) { g += 1; } } }
    println!("ALG1c at N=7k-1 the inequality (k-p')N<=k(N-7p') fails for {} of {} (p'>=1) cases", g, c2);
    // pairwise coprime F in [N+2,2N-1] with |F|>=8k+1 forces N-2>=8k+1
    println!("ALG2 forced N >= 8k+3: k=1:{} k=2:{} k=6:{}", 8 + 3, 16 + 3, 48 + 3);
    // S+ : c(D)=4+8(D+1)/(D-3), D=D*; need strict D+1 > k*c(D). integer form: (D+1)(D-3) > k(4(D-3)+8(D+1)) = k(12D-4+... )
    // 4(D-3)+8(D+1)=12D-4
    println!("S+ strict condition (D*+1)(D*-3) > k(12D*-4); minimal D*+1 per k, versus forced D*+1 >= 16k+6, and 12k+3 heuristic:");
    let mut bad2 = 0;
    for k in [1i64, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 30, 40, 50, 100, 200, 1000] {
        let mut d = 4i64; while !((d + 1) * (d - 3) > k * (12 * d - 4)) { d += 1; }
        let forced = 16 * k + 5; // D* >= 16k+5
        // check forced D satisfies strict condition and all larger
        let mut okf = true; for dd in forced..(forced + 5000) { if !((dd + 1) * (dd - 3) > k * (12 * dd - 4)) { okf = false; } }
        if !okf { bad2 += 1; }
        println!("  k={:4} minimal D*+1 = {:6}  (12k+3 = {:6})  forced D*+1 >= {:6}  forced range satisfies condition: {}", k, d + 1, 12 * k + 3, forced + 1, okf);
    }
    println!("S+ forced-range violations: {}", bad2);
    // check the reference value at D*+1=110: c = 4 + 8*110/106
    println!("c(D*) at D*+1=110: {:.4}; at 232: {:.4}; limit 12", 4.0 + 8.0 * 110.0 / 106.0, 4.0 + 8.0 * 232.0 / 228.0);
}

fn thr() {
    let m: usize = 12_000_001;
    let mut sieve = vec![true; m + 1]; sieve[0] = false; sieve[1] = false;
    let mut i = 2; while i * i <= m { if sieve[i] { let mut j = i * i; while j <= m { sieve[j] = false; j += i; } } i += 1; }
    let mut pi = vec![0u32; m + 1]; let mut c = 0u32; for i in 0..=m { if sieve[i] { c += 1; } pi[i] = c; }
    drop(sieve);
    let cn = |n: usize| -> i64 { pi[2 * n] as i64 - pi[n + n / 2] as i64 };
    let nmax_p = 6_000_000usize;
    let nmax_c: usize = 1 << 23;
    let cheb_fail = |t: i64, n: usize| -> bool { let l = (63 - (n as u64).leading_zeros() as i64) + 2; !(6 * l * (t + 3 * l + 60) + 1200 <= n as i64) };
    let lastp = |t: i64| -> usize { let mut last = 0; for n in 1..=nmax_p { if cn(n) < t { last = n; } } last + 1 };
    let lastc = |t: i64| -> usize { let mut last = 0; for n in 1..=nmax_c { if cheb_fail(t, n) { last = n; } } last + 1 };
    println!("k | T=8k+1 | prime N*(T) | prime N*(8k+1) max(7k+1,10) | Cheb N_C(T) | Cheb max(7k+1,10) || controls: T_S=3k(k+1)+1 prime, Cheb | 9k+1 (max 63k) prime, Cheb | 19k+1 (max 133k) prime, Cheb");
    for k in 1i64..=40 {
        let t8 = 8 * k + 1; let ts = 3 * k * (k + 1) + 1; let t9 = 9 * k + 1; let t19 = 19 * k + 1;
        let p8 = lastp(t8); let c8 = lastc(t8);
        let floor = std::cmp::max(7 * k + 1, 10) as usize;
        let ps = lastp(ts); let cs = lastc(ts); let p9 = std::cmp::max(lastp(t9), (63 * k) as usize); let c9 = std::cmp::max(lastc(t9), (63 * k) as usize);
        let p19 = std::cmp::max(lastp(t19), (133 * k) as usize); let c19 = std::cmp::max(lastc(t19), (133 * k) as usize);
        let t18 = 18 * k + 1; let p18 = lastp(t18); let c18 = lastc(t18);
        println!("{} | {} | {} | {} | {} | {} || S {} {} | 9k+1 {} {} | 19k+1 {} {} | 18k+1 {} {}", k, t8, p8, std::cmp::max(p8, floor), c8, std::cmp::max(c8, floor), ps, cs, p9, c9, p19, c19, p18, c18);
    }
    // sanity: the last prime failure is far below the sieve end
    println!("thr sieve end N<= {} (prime), Chebyshev scan N<= {}", nmax_p, nmax_c);
}

fn main() {
    let a: Vec<String> = env::args().collect();
    match a[1].as_str() {
        "ctl" => ctl(),
        "lem" => lem(arg(&a, 2), arg(&a, 3), arg(&a, 4)),
        "dc" => dc(arg(&a, 2) as usize, arg(&a, 3), arg(&a, 4), arg(&a, 5), arg(&a, 6) as usize, arg(&a, 7) as usize, arg(&a, 8) as u64),
        "alg" => alg(),
        "thr" => thr(),
        _ => println!("modes: ctl lem dc alg thr"),
    }
}
