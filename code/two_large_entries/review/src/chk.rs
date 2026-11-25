// Review checker for the accompanying code (Theorem W). Own code, exact i128 integer arithmetic.
// Decision procedure ("left-endpoint candidates"): G = {t in [0,1]: ||v t|| >= tau for all v in V} is closed; if nonempty its
// minimum t* > 0 is the right endpoint of an open band {||v t|| < tau} of some v, i.e. t* = (k tq + tp)/(v tq), k >= 0; by the
// symmetry t -> 1-t we may take t* <= 1/2.  So ML(V) >= tau  iff  some such candidate has ||u t|| >= tau for every u in V.
// (This differs from the author's method A, a complement sweep, and from method B, candidates k/(vi+vj).)
// Exact ML (for planted values only): method B written independently here.
use std::cmp::Ordering;
use std::env;
use std::collections::BTreeSet;

type F = (i128, i128); // num, den>0

fn fcmp(a: F, b: F) -> Ordering { (a.0 * b.1).cmp(&(b.0 * a.1)) }
fn ge_tau(u: i128, t: F, tau: F) -> bool {
    let (a, b) = t;
    let m = (u * a).rem_euclid(b);
    let d = m.min(b - m);
    d * tau.1 >= tau.0 * b
}
fn cdiv(a: i128, b: i128) -> i128 { -((-a).div_euclid(b)) } // ceil, b>0
fn fdiv(a: i128, b: i128) -> i128 { a.div_euclid(b) }

// brute decision: candidates from every speed of V
fn decide_brute(v: &[i128], tau: F) -> bool {
    let (tp, tq) = tau;
    for &x in v {
        let den = x * tq;
        let mut k = 0i128;
        loop {
            let num = k * tq + tp;
            if 2 * num > den { break; }
            let t = (num, den);
            if v.iter().all(|&u| ge_tau(u, t, tau)) { return true; }
            k += 1;
        }
    }
    false
}

// closed components of {t in [0,1/2]: ||v t|| >= tau for all v in ret}
fn comps(ret: &[i128], tau: F) -> Vec<(F, F)> {
    let (tp, tq) = tau;
    let mut bands: Vec<(F, F)> = Vec::new();
    for &v in ret {
        let den = v * tq;
        let mut k = 0i128;
        loop {
            let lo = (k * tq - tp, den);
            if 2 * lo.0 > den { break; }
            bands.push((lo, (k * tq + tp, den)));
            k += 1;
        }
    }
    bands.sort_by(|a, b| fcmp(a.0, b.0));
    let mut res = Vec::new();
    let mut hi = bands[0].1;
    for b in bands.iter().skip(1) {
        if fcmp(b.0, hi) != Ordering::Less {
            res.push((hi, b.0));
            hi = b.1;
        } else if fcmp(b.1, hi) == Ordering::Greater {
            hi = b.1;
        }
    }
    if 2 * hi.0 <= hi.1 { res.push((hi, (1, 2))); }
    res
}

// right endpoints of the bands of speed w that lie inside the closed components
fn endpoints(w: i128, tau: F, cs: &[(F, F)]) -> Vec<F> {
    let (tp, tq) = tau;
    let mut out = Vec::new();
    for (a, b) in cs {
        let kmin = cdiv(a.0 * w * tq - tp * a.1, tq * a.1).max(0);
        let kmax = fdiv(b.0 * w * tq - tp * b.1, tq * b.1);
        let mut k = kmin;
        while k <= kmax {
            out.push((k * tq + tp, w * tq));
            k += 1;
        }
    }
    out
}

fn pair_ok(cs: &[(F, F)], e1: &[F], e2: &[F], w1: i128, w2: i128, tau: F) -> bool {
    for (a, _) in cs { if ge_tau(w1, *a, tau) && ge_tau(w2, *a, tau) { return true; } }
    for t in e1 { if ge_tau(w2, *t, tau) { return true; } }
    for t in e2 { if ge_tau(w1, *t, tau) { return true; } }
    false
}

// exact ML by candidate times k/(vi+vj) (independent re-implementation of "method B")
fn ml_exact(v: &[i128]) -> F {
    let mut sums = BTreeSet::new();
    for i in 0..v.len() { for j in i..v.len() { sums.insert(v[i] + v[j]); } }
    let mut best: F = (0, 1);
    for &s in &sums {
        for k in 1..=(s / 2) {
            let mut m: F = (s, s); // placeholder > any
            let mut first = true;
            for &x in v {
                let r = (x * k).rem_euclid(s);
                let d = r.min(s - r);
                let f = (d, s);
                if first || fcmp(f, m) == Ordering::Less { m = f; first = false; }
                if fcmp(m, best) != Ordering::Greater { break; }
            }
            if fcmp(m, best) == Ordering::Greater { best = m; }
        }
    }
    best
}

fn gcd(a: i128, b: i128) -> i128 { if b == 0 { a } else { gcd(b, a % b) } }
fn red(f: F) -> F { let g = gcd(f.0, f.1); (f.0 / g, f.1 / g) }
fn plus_eps(f: F) -> F { (f.0 * 1000003 + 1, f.1 * 1000003) }
fn minus_eps(f: F) -> F { (f.0 * 1000003 - 1, f.1 * 1000003) }

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 }
    fn below(&mut self, n: u64) -> u64 { self.next() % n }
}

fn setv(n: i128, removed: &[i128], ins: &[i128]) -> Vec<i128> {
    let mut v: Vec<i128> = (1..=n).filter(|x| !removed.contains(x)).collect();
    v.extend_from_slice(ins);
    v
}

fn is_prime(n: u64) -> bool { if n < 2 { return false; } let mut d = 2; while d * d <= n { if n % d == 0 { return false; } d += 1; } true }

fn selftest() {
    let mut fails = 0;
    // planted values (one-sided checks with the exact ML from method B and the decision procedure)
    let planted: Vec<(&str, Vec<i128>, F)> = vec![
        ("T1 {1,3,4,7}", vec![1, 3, 4, 7], (1, 5)),
        ("T2 {1,3,4,5,9}", vec![1, 3, 4, 5, 9], (1, 6)),
        ("[8]", (1..=8).collect(), (1, 9)),
        ("{1,4,5,6,7,11,13}", vec![1, 4, 5, 6, 7, 11, 13], (1, 8)),
        ("13;6->69", setv(13, &[6], &[69]), (3, 40)),
        ("13;12->36", setv(13, &[12], &[36]), (3, 41)),
        ("13;12->24", setv(13, &[12], &[24]), (1, 14)),
        ("8;2,3;11,13", setv(8, &[2, 3], &[11, 13]), (2, 17)),
        ("8;2,8;11,32", setv(8, &[2, 8], &[11, 32]), (4, 33)),
        ("8;3,4;11,13", setv(8, &[3, 4], &[11, 13]), (2, 17)),
        ("12;4,6;17,19", setv(12, &[4, 6], &[17, 19]), (2, 25)),
        ("13;6,10;20,69", setv(13, &[6, 10], &[20, 69]), (3, 40)),
        ("73;70,72;140,144", setv(73, &[70, 72], &[140, 144]), (1, 74)),
    ];
    for (name, v, exp) in &planted {
        let ml = red(ml_exact(v));
        let ok_val = ml == *exp;
        let g0 = decide_brute(v, ml);
        let g1 = decide_brute(v, plus_eps(ml));
        let g2 = decide_brute(v, minus_eps(ml));
        let ok = ok_val && g0 && !g1 && g2;
        println!("planted {:<20} ML(B)={}/{} expected {}/{} ge(ML)={} ge(ML+eps)={} ge(ML-eps)={} {}", name, ml.0, ml.1, exp.0, exp.1, g0, g1, g2, if ok { "OK" } else { "FAIL" });
        if !ok { fails += 1; }
    }
    // random sets: decision vs exact ML at value and one step either side
    let mut rng = Rng(88172645463325252);
    let mut cnt = 0;
    for _ in 0..4000 {
        let n = 3 + rng.below(8) as usize;
        let mut set = BTreeSet::new();
        while set.len() < n { set.insert(1 + rng.below(90) as i128); }
        let v: Vec<i128> = set.into_iter().collect();
        let ml = red(ml_exact(&v));
        let a = decide_brute(&v, ml);
        let b = decide_brute(&v, plus_eps(ml));
        let c = decide_brute(&v, minus_eps(ml));
        cnt += 1;
        if !(a && !b && c) { println!("RANDOM FAIL {:?} ML {:?} {} {} {}", v, ml, a, b, c); fails += 1; }
    }
    println!("random sets brute-vs-B: {} sets, failures so far {}", cnt, fails);
    // sweep-based decision (comps + endpoints) vs brute on random structured sets
    let mut mism = 0; let mut tot = 0; let mut nneg = 0;
    for _ in 0..3000 {
        let n = 8 + rng.below(30) as i128;
        let r = 1 + rng.below(n as u64) as i128;
        let w1 = n + 1 + rng.below(400) as i128;
        let w2 = w1 + 1 + rng.below(400) as i128;
        let tau = (1, n);
        let ret = setv(n, &[r], &[]);
        let cs = comps(&ret, tau);
        let e1 = endpoints(w1, tau, &cs);
        let e2 = endpoints(w2, tau, &cs);
        let a = pair_ok(&cs, &e1, &e2, w1, w2, tau);
        let v = setv(n, &[r], &[w1, w2]);
        let b = decide_brute(&v, tau);
        tot += 1; if !b { nneg += 1; }
        if a != b { mism += 1; println!("SWEEP MISMATCH n={} r={} w1={} w2={} sweep={} brute={}", n, r, w1, w2, a, b); }
    }
    println!("sweep-vs-brute at tau=1/N on random N<=39 sets: {} sets ({} with ML<1/N), mismatches {}", tot, nneg, mism);
    // tau other than 1/N (check generality of comps/endpoints): tau = 2/(2N+1)
    let mut mism2 = 0; let mut neg2 = 0;
    for _ in 0..3000 {
        let n = 6 + rng.below(25) as i128;
        let r = 1 + rng.below(n as u64) as i128;
        let w1 = n + 1 + rng.below(200) as i128;
        let w2 = w1 + 1 + rng.below(200) as i128;
        let tau = (3, 3 * n + 4);
        let ret = setv(n, &[r], &[]);
        let cs = comps(&ret, tau);
        let e1 = endpoints(w1, tau, &cs);
        let e2 = endpoints(w2, tau, &cs);
        let a = pair_ok(&cs, &e1, &e2, w1, w2, tau);
        let b = decide_brute(&setv(n, &[r], &[w1, w2]), tau);
        if !b { neg2 += 1; }
        if a != b { mism2 += 1; }
    }
    println!("sweep-vs-brute at tau=3/(3N+4): 3000 sets ({} negative), mismatches {}", neg2, mism2);
    if mism > 0 || mism2 > 0 { fails += 1; }
    println!("SELFTEST {}", if fails == 0 { "PASS" } else { "FAIL" });
}

// V' form: [N]\{r} u {w1,w2}, all N<w1<w2<=wmax. returns (sets, failures)
fn scan_vprime(n: i128, r: i128, wmax: i128, print: bool) -> (u64, u64) {
    let tau = (1, n);
    let ret = setv(n, &[r], &[]);
    let cs = comps(&ret, tau);
    let mut e: Vec<Vec<F>> = vec![Vec::new(); (wmax + 1) as usize];
    for w in (n + 1)..=wmax { e[w as usize] = endpoints(w, tau, &cs); }
    let mut sets = 0u64; let mut fail = 0u64;
    for w1 in (n + 1)..=wmax {
        for w2 in (w1 + 1)..=wmax {
            sets += 1;
            if !pair_ok(&cs, &e[w1 as usize], &e[w2 as usize], w1, w2, tau) {
                fail += 1;
                if print && fail <= 6 { println!("  FAIL N={} r={} w1={} w2={}", n, r, w1, w2); }
            }
        }
    }
    (sets, fail)
}


// pieces of (union of closed comps) minus the open bands of speed w
fn restrict(cs: &[(F, F)], w: i128, tau: F) -> Vec<(F, F)> {
    let (tp, tq) = tau;
    let mut out = Vec::new();
    for (a, b) in cs {
        let kmin = fdiv(a.0 * w * tq - tp * a.1, tq * a.1) + 1;
        let kmax = cdiv(b.0 * w * tq + tp * b.1, tq * b.1) - 1;
        let mut cur = *a;
        let mut k = kmin.max(0);
        let mut dead = false;
        while k <= kmax {
            let lo = (k * tq - tp, w * tq);
            let hi = (k * tq + tp, w * tq);
            if fcmp(lo, *b) != Ordering::Less { break; }
            if fcmp(hi, cur) == Ordering::Greater || (fcmp(hi, cur) != Ordering::Greater && false) {
                // band overlaps or lies right of cur
                if fcmp(lo, cur) != Ordering::Less {
                    // lo >= cur: piece [cur, lo]
                    out.push((cur, lo));
                }
                cur = hi;
                if fcmp(cur, *b) == Ordering::Greater { dead = true; break; }
            }
            k += 1;
        }
        if !dead && fcmp(cur, *b) != Ordering::Greater { out.push((cur, *b)); }
    }
    out
}
fn flen(c: &(F, F)) -> F { (c.1 .0 * c.0 .1 - c.0 .0 * c.1 .1, c.1 .1 * c.0 .1) }
fn longest(cs: &[(F, F)]) -> Option<F> {
    let mut best: Option<F> = None;
    for c in cs { let l = flen(c); if best.is_none() || fcmp(l, best.unwrap()) == Ordering::Greater { best = Some(l); } }
    best
}

// unconditional certificate for all N<w1<w2 (no cap): M1 for w1,w2>=W0 on the longest piece of G0, M2 for w2>=W2(w1), exact below.
// returns (pairs_tested_exactly, failures, flags, maxW0)
fn cert_one(n: i128, removed: &[i128], print: bool) -> (u64, u64, u64, i128) {
    let tau = (1, n);
    let ret = setv(n, removed, &[]);
    let cs0 = comps(&ret, tau);
    let l0 = match longest(&cs0) { Some(l) if l.0 > 0 => l, _ => { if print { println!("  FLAG G0 empty/point N={} R={:?}", n, removed); } return (0, 0, 1, 0); } };
    // W0 = floor(4(N+2)/(N(N-4) l)) + 1, l = l0.0/l0.1
    let w0 = (4 * (n + 2) * l0.1) / (n * (n - 4) * l0.0) + 1;
    let mut tested = 0u64; let mut fails = 0u64; let mut flags = 0u64;
    for w1 in (n + 1)..w0 {
        let cs1 = restrict(&cs0, w1, tau);
        let l1 = match longest(&cs1) { Some(l) if l.0 > 0 => l, _ => { flags += 1; if print { println!("  FLAG G1 empty/point N={} R={:?} w1={}", n, removed, w1); } continue; } };
        // w2 >= 2/(N l1)
        let w2min = cdiv(2 * l1.1, n * l1.0);
        for w2 in (w1 + 1)..w2min {
            tested += 1;
            let e2 = endpoints(w2, tau, &cs1);
            let mut ok = e2.len() > 0;
            if !ok { for (a, _) in &cs1 { if ge_tau(w2, *a, tau) { ok = true; break; } } }
            if !ok { fails += 1; if print && fails <= 5 { println!("  FAIL N={} R={:?} w1={} w2={}", n, removed, w1, w2); } }
        }
    }
    (tested, fails, flags, w0)
}


fn egcd(a: i128, b: i128) -> (i128, i128, i128) { if b == 0 { (a, 1, 0) } else { let (g, x, y) = egcd(b, a % b); (g, y, x - (a / b) * y) } }
fn inv_mod(a: i128, m: i128) -> i128 { let (_, x, _) = egcd(a.rem_euclid(m), m); x.rem_euclid(m) }
fn fmax(a: F, b: F) -> F { if fcmp(a, b) == Ordering::Less { b } else { a } }
fn fmin(a: F, b: F) -> F { if fcmp(a, b) == Ordering::Greater { b } else { a } }
// witness formula of the draft: ML = max(1/A [if A divides neither w], max_{r in R, m>=2, m r in W} min(m/D, ||a w'/D||)), D = m r + beta, a r = -1 mod D
fn formula(n: i128, rr: &[i128], ww: &[i128; 2]) -> F {
    let a_ = n + 1;
    let mut best: F = (0, 1);
    if ww[0] % a_ != 0 && ww[1] % a_ != 0 { best = (1, a_); }
    for &r in rr {
        let s = a_ - r;
        let mut beta = s; while gcd(beta, r) != 1 { beta += 1; }
        for i in 0..2 {
            let w = ww[i]; if w % r != 0 || w / r < 2 { continue; }
            let m = w / r; let d = m * r + beta;
            let a = (d - inv_mod(r, d)) % d; // a r = -1 mod d
            let wp = ww[1 - i];
            let x = (a * wp).rem_euclid(d); let dist = (x.min(d - x), d);
            let l = fmin((m, d), dist);
            best = fmax(best, l);
        }
    }
    best
}

fn excl(n0: i128, n1: i128, off: i128) {
    let mut total = 0u64; let (mut eqf, mut neqf) = (0u64, 0u64); let mut minmlN: F = (1, 1); let mut minat = 0;
    for n in n0..=n1 {
        let tau = (1, n);
        let wmax = if n <= 40 { 2000 } else { 600 };
        let mut cnt = 0u64;
        for r1 in (n - off).max(1)..n {
            for r2 in (r1 + 1)..=n {
                let ret = setv(n, &[r1, r2], &[]);
                let cs = comps(&ret, tau);
                let mut e: Vec<Vec<F>> = vec![Vec::new(); (wmax + 1) as usize];
                for w in (n + 1)..=wmax { e[w as usize] = endpoints(w, tau, &cs); }
                for w1 in (n + 1)..=wmax {
                    for w2 in (w1 + 1)..=wmax {
                        if !pair_ok(&cs, &e[w1 as usize], &e[w2 as usize], w1, w2, tau) {
                            cnt += 1;
                            let ml = red(ml_exact(&setv(n, &[r1, r2], &[w1, w2])));
                            let fo = red(formula(n, &[r1, r2], &[w1, w2]));
                            if ml == fo { eqf += 1; } else { neqf += 1; }
                            let mlN = (ml.0 * n, ml.1);
                            if fcmp(mlN, minmlN) == Ordering::Less { minmlN = red(mlN); minat = n; }
                            println!("EXC\t{}\t{}\t{}\t{}\t{}\t{}/{}\tformula={}/{}\t{}", n, r1, r2, w1, w2, ml.0, ml.1, fo.0, fo.1, if ml == fo { "EQ" } else { "NEQ" });
                        }
                    }
                }
            }
        }
        total += cnt;
        println!("EXCN N={} r1>=N-{} exceptions={}", n, off, cnt);
    }
    println!("EXCL TOTAL={} formula_equal={} formula_not_equal={} min(ML*N)={}/{} at N={}", total, eqf, neqf, minmlN.0, minmlN.1, minat);
}

fn vform(n0: i128, n1: i128, wmax: i128) {
    // r1 <= N/2, r2 in (r1,N], N<w1<w2<=wmax ; exceptions = ML < 1/N
    for n in n0..=n1 {
        let tau = (1, n);
        let mut exc = 0u64; let mut sets = 0u64;
        let mut by_r1: Vec<(i128, i128, i128, i128)> = Vec::new();
        for r1 in 1..=(n / 2) {
            for r2 in (r1 + 1)..=n {
                let ret = setv(n, &[r1, r2], &[]);
                let cs = comps(&ret, tau);
                let mut e: Vec<Vec<F>> = vec![Vec::new(); (wmax + 1) as usize];
                for w in (n + 1)..=wmax { e[w as usize] = endpoints(w, tau, &cs); }
                for w1 in (n + 1)..=wmax {
                    for w2 in (w1 + 1)..=wmax {
                        sets += 1;
                        if !pair_ok(&cs, &e[w1 as usize], &e[w2 as usize], w1, w2, tau) {
                            exc += 1;
                            if by_r1.len() < 40 { by_r1.push((r1, r2, w1, w2)); }
                        }
                    }
                }
            }
        }
        print!("VFORM N={} w<={} sets={} exceptions(r1<=N/2)={}", n, wmax, sets, exc);
        for (a, b, c, d) in by_r1.iter().take(30) {
            let ml = red(ml_exact(&setv(n, &[*a, *b], &[*c, *d])));
            print!(" [r={},{} w={},{} ML={}/{}]", a, b, c, d, ml.0, ml.1);
        }
        println!();
    }
}

fn sieve(lim: usize) -> Vec<bool> {
    let mut s = vec![true; lim + 1]; s[0] = false; if lim >= 1 { s[1] = false; }
    let mut i = 2; while i * i <= lim { if s[i] { let mut j = i * i; while j <= lim { s[j] = false; j += i; } } i += 1; }
    s
}

fn primes_check() {
    let lim = 20_000_000usize;
    let s = sieve(lim);
    let mut pi = vec![0u32; lim + 1];
    let mut c = 0u32; for i in 0..=lim { if s[i] { c += 1; } pi[i] = c; }
    let primes: Vec<usize> = (0..=lim).filter(|&i| s[i]).collect();
    // count in [N+1+floor(N/2), 2N-1]
    let mut last_bad = 0; let mut minc_after = u32::MAX; let mut argmin = 0;
    let mut cnt_lt = [0usize; 3];
    for n in 14..=10_000_000usize {
        let a = n + 1 + n / 2; let b = 2 * n - 1;
        let cnt = pi[b] - pi[a - 1];
        if cnt < 10 { last_bad = n; }
        if n >= 114 && cnt < minc_after { minc_after = cnt; argmin = n; }
        if cnt < 7 { cnt_lt[0] += 1; }
    }
    println!("PRIMES: last N in [14,1e7] with <10 primes in [N+1+floor(N/2),2N-1]: {}; min count for N in [114,1e7] = {} at N={}", last_bad, minc_after, argmin);
    // r_10(N): largest r with >=10 primes in [N+1+r, 2N-1]; N - r_10 = N - (q10 - N - 1) with q10 = 10th largest prime <= 2N-1
    let mut maxd = 0usize; let mut argd = 0usize; let mut maxd_1e7 = 0usize; let mut argd_1e7 = 0usize;
    for n in 114..=10_000_000usize {
        let idx = pi[2 * n - 1] as usize; // number of primes <= 2N-1
        let q10 = primes[idx - 10];
        let r10 = q10 as i64 - n as i64 - 1; // may be negative if hypothetically none
        let d = (n as i64 - r10) as usize;
        if n <= 2_000_000 && d > maxd { maxd = d; argd = n; }
        if d > maxd_1e7 { maxd_1e7 = d; argd_1e7 = n; }
        if r10 < 1 { println!("NOTE r_10<1 at N={}", n); }
    }
    println!("PRIMES: max (N - r_10(N)) for 114<=N<=2e6 = {} at N={}; for N<=1e7 = {} at N={}", maxd, argd, maxd_1e7, argd_1e7);
    let _ = cnt_lt;
    // counts at small N
    for n in [113usize, 114, 115, 126, 130] {
        let a = n + 1 + n / 2; let b = 2 * n - 1;
        println!("  N={} primes in [{},{}] = {}", n, a, b, pi[b] - pi[a - 1]);
    }
}

fn ineq_check() {
    let mut bad = 0u64;
    for n in 114i128..=10_000_000 {
        let wm = (2 * (n + 2) * n * (2 * n - 19)) / (19 * (n - 4)) + 1;
        let i1 = wm <= (n + 2) * (n + 2) - 1;
        let i2 = (2 * n - 13) * wm <= 13 * ((n + 2) * (n + 2) * (n + 2) - 2);
        if !(i1 && i2) { bad += 1; println!("INEQ FAIL N={} Wm={}", n, wm); }
    }
    println!("INEQ (I1),(I2) for N=114..1e7: failures {}", bad);
    println!("  Wm(114) = {}", (2 * 116 * 114 * (2 * 114 - 19)) / (19 * 110) + 1);
    // Dusart chain sanity (float, evidence only): 10 successive primes after x=1.5N within (x, x(1+1/(25 ln^2 x))]^10
    for &n in &[264_492f64, 1e6, 1e7, 1e8, 1e12] {
        let mut x = 1.5 * n;
        for _ in 0..10 { x *= 1.0 + 1.0 / (25.0 * x.ln() * x.ln()); }
        println!("  Dusart chain N={:e}: after 10 steps from 1.5N reaches {:.6}*N (needs <= 2N-1)", n, x / n);
    }
    // RS/Dusart(6.5) counting chain, float evidence: f(N)=2N(M+1)/M^2 - 1.5N(L+1.2762)/L^2
    for &n in &[1e7f64, 1e8, 1e10, 1e15] {
        let l = (1.5 * n).ln(); let m = (2.0 * n).ln();
        let f = 2.0 * n * (m + 1.0) / (m * m) - 1.5 * n * (l + 1.2762) / (l * l);
        println!("  Dusart(6.5) count lower bound at N={:e}: {:.1}", n, f);
    }
}

// primes list in window
fn window_primes(n: i128, r: i128) -> Vec<i128> {
    let mut p = Vec::new();
    let mut d = n + 1 + r;
    while d <= 2 * n - 1 { if is_prime(d as u64) { p.push(d); } d += 1; }
    p
}
fn bad_for(d: i128, r: i128, w: i128) -> bool { let m = w.rem_euclid(d); m == 0 || m == r.rem_euclid(d) || m == (d - r.rem_euclid(d)) % d }

// W(D) of the proof, exact integer
fn w_of_d(n: i128, d: i128) -> i128 { (2 * (n + 2) * n * d) / ((n - 4) * (2 * n - d)) + 1 }

fn crt2(a1: i128, m1: i128, a2: i128, m2: i128) -> (i128, i128) {
    // solve x = a1 mod m1, x = a2 mod m2, coprime moduli
    let mut x = a1.rem_euclid(m1);
    let mm = m1 * m2;
    loop { if (x - a2).rem_euclid(m2) == 0 { return (x, mm); } x += m1; if x > mm * 2 { panic!("crt"); } }
}

// structured families for Theorem W regime and below; report failures and case-by-case logic checks (streaming, no big vectors)
struct Acc { sets: u64, fails_p10: u64, fails_other: u64, casebad: u64, ca: u64, cb1: u64, cb2: u64 }

fn one_test(n: i128, r: i128, p: &[i128], cs: &[(F, F)], tau: F, w1: i128, w2: i128,
            cache: &mut std::collections::HashMap<i128, Vec<F>>, ccount: &mut usize, acc: &mut Acc) {
    if *ccount > 200_000 { cache.clear(); *ccount = 0; }
    for &w in &[w1, w2] { if !cache.contains_key(&w) { let ev = endpoints(w, tau, cs); *ccount += ev.len() + 1; cache.insert(w, ev); } }
    let ok = pair_ok(cs, &cache[&w1], &cache[&w2], w1, w2, tau);
    acc.sets += 1;
    if !ok { if p.len() >= 10 { acc.fails_p10 += 1; println!("  !!! THEOREM-W COUNTEREXAMPLE? N={} r={} w1={} w2={}", n, r, w1, w2); } else { acc.fails_other += 1; } }
    if p.len() >= 10 && n >= 114 {
        let w_p1 = w_of_d(n, p[0]);
        if w1 >= w_p1 { acc.ca += 1; }
        else {
            let bad1 = p.iter().filter(|&&d| bad_for(d, r, w1)).count();
            if bad1 > 3 { acc.casebad += 1; println!("  !!! >3 bad primes for w1: N={} r={} w1={} bad={}", n, r, w1, bad1); }
            match p.iter().cloned().find(|&d| !bad_for(d, r, w1)) {
                None => { acc.casebad += 1; println!("  !!! no good prime for w1"); }
                Some(dg) => {
                    if dg > p[3] { acc.casebad += 1; println!("  !!! D_g beyond p_4"); }
                    if w2 * (2 * n - dg) >= dg * w1 { acc.cb1 += 1; }
                    else {
                        acc.cb2 += 1;
                        let bad2 = p.iter().filter(|&&d| bad_for(d, r, w2)).count();
                        if bad2 > 6 { acc.casebad += 1; println!("  !!! >6 bad primes for w2: N={} r={} w2={} bad={}", n, r, w2, bad2); }
                        let both = p.iter().filter(|&&d| !bad_for(d, r, w1) && !bad_for(d, r, w2)).count();
                        if both == 0 { acc.casebad += 1; println!("  !!! no prime good for both"); }
                    }
                }
            }
        }
    }
}

fn structured(n0: i128, n1: i128, seed: u64) {
    let mut rng = Rng(seed);
    for n in n0..=n1 {
        let tau = (1, n);
        let mut acc = Acc { sets: 0, fails_p10: 0, fails_other: 0, casebad: 0, ca: 0, cb1: 0, cb2: 0 };
        for r in 1..=(n - 2) {
            let p = window_primes(n, r);
            let ret = setv(n, &[r], &[]);
            let cs = comps(&ret, tau);
            let mut cache: std::collections::HashMap<i128, Vec<F>> = std::collections::HashMap::new();
            let mut ccount = 0usize;
            // ratio family, streaming per w1
            for w1 in (n + 1)..=(12 * n) {
                let mut w2s: Vec<i128> = Vec::new();
                for d in (n + 1 + r)..=(2 * n - 1) {
                    let base = (d * w1) / (2 * n - d);
                    for j in -2i128..=2 { w2s.push(base + j); }
                }
                for j in -3i128..=3 { w2s.push(n * w1 + j); }
                for j in 1..=5 { w2s.push(w1 + j); }
                w2s.sort(); w2s.dedup();
                for &w2 in &w2s { if w2 > w1 && w2 <= 3_000_000 { one_test(n, r, &p, &cs, tau, w1, w2, &mut cache, &mut ccount, &mut acc); } }
            }
            // CRT family
            if p.len() >= 3 {
                for _ in 0..300 {
                    let mut pick = |kk: usize, rng: &mut Rng| -> (i128, i128) {
                        let mut mods: Vec<i128> = Vec::new();
                        while mods.len() < kk { let c = p[rng.below(p.len() as u64) as usize]; if !mods.contains(&c) { mods.push(c); } }
                        let mut x = 0i128; let mut m = 1i128; let mut first = true;
                        for &d in &mods {
                            let e = [0, r, -r][rng.below(3) as usize];
                            if first { x = e.rem_euclid(d); m = d; first = false; } else { let (xx, mm) = crt2(x, m, e.rem_euclid(d), d); x = xx; m = mm; }
                        }
                        (x, m)
                    };
                    let k1 = 2 + rng.below(2) as usize; let k2 = 2 + rng.below(2) as usize;
                    let (x1, m1) = pick(k1.min(p.len()), &mut rng); let (x2, m2) = pick(k2.min(p.len()), &mut rng);
                    let lim = 3_000_000i128;
                    let mut a = x1; while a <= n { a += m1; }
                    let mut b = x2; while b <= n { b += m2; }
                    let mut wa = Vec::new(); let mut wb = Vec::new();
                    for _ in 0..3 { if a <= lim { wa.push(a); } a += m1; }
                    for _ in 0..3 { if b <= lim { wb.push(b); } b += m2; }
                    for &u in &wa { for &v in &wb { if u != v { one_test(n, r, &p, &cs, tau, u.min(v), u.max(v), &mut cache, &mut ccount, &mut acc); } } }
                }
            }
        }
        println!("STRUCT N={} sets={} fails(|P|>=10)={} fails(|P|<10)={} caselogic_violations={} (case A {}, B1 {}, B2 {} among |P|>=10 tests)", n, acc.sets, acc.fails_p10, acc.fails_other, acc.casebad, acc.ca, acc.cb1, acc.cb2);
    }
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let cmd = a.get(1).map(|s| s.as_str()).unwrap_or("");
    let num = |i: usize| -> i128 { a[i].parse().unwrap() };
    match cmd {
        "selftest" => selftest(),
        "scanp" => {
            // scanp N0 N1 wmax off : r in 1..=N-off (V' form)
            let (n0, n1, wmax, off) = (num(2), num(3), num(4), num(5));
            let mut total = 0u64; let mut totf = 0u64;
            for n in n0..=n1 {
                let mut sn = 0u64; let mut fn_ = 0u64; let mut first_fail_r = 0;
                for r in 1..=(n - off) {
                    let (s, f) = scan_vprime(n, r, wmax, f_print(f_off(n, off)));
                    sn += s; fn_ += f;
                    if f > 0 && first_fail_r == 0 { first_fail_r = r; }
                }
                println!("SCANP N={} r<=N-{} w<={} sets={} failures={} first_failing_r={}", n, off, wmax, sn, fn_, first_fail_r);
                total += sn; totf += fn_;
            }
            println!("SCANP TOTAL sets={} failures={}", total, totf);
        }
        "negctl" => {
            // negative control: V' form at N=14..20 for ALL r<=N-1, report failures per r (they exist per the author's table)
            for n in 14i128..=20 {
                for r in 1..=n {
                    let (s, f) = scan_vprime(n, r, 600, false);
                    if f > 0 { println!("NEGCTL N={} r={} w<=600 sets={} failures={}", n, r, s, f); }
                }
            }
        }
        "vform" => vform(num(2), num(3), num(4)),
        "excl" => excl(num(2), num(3), num(4)),
        "cert" => {
            // cert N0 N1 mode : mode 0 = V' (remove r<=N/2), mode 1 = V (remove r1<=N/2 and every r2>r1)
            let (n0, n1, mode) = (num(2), num(3), num(4));
            let (mut gt, mut gf, mut gfl) = (0u64, 0u64, 0u64);
            for n in n0..=n1 {
                let (mut t, mut f, mut fl, mut mw) = (0u64, 0u64, 0u64, 0i128);
                let mut pairs = 0u64;
                let rtop = if mode == 2 { n - 9 } else { n / 2 };
                for r1 in 1..=rtop {
                    if mode == 0 || mode == 2 { let x = cert_one(n, &[r1], true); t += x.0; f += x.1; fl += x.2; mw = mw.max(x.3); pairs += 1; }
                    else { for r2 in (r1 + 1)..=n { let x = cert_one(n, &[r1, r2], true); t += x.0; f += x.1; fl += x.2; mw = mw.max(x.3); pairs += 1; } }
                }
                println!("CERT mode={} N={} (N,R) cases={} exact pairs={} failures={} flags={} maxW0={}", mode, n, pairs, t, f, fl, mw);
                gt += t; gf += f; gfl += fl;
            }
            println!("CERT TOTAL exact pairs={} failures={} flags={}", gt, gf, gfl);
        }
        "primes" => primes_check(),
        "ineq" => ineq_check(),
        "struct" => structured(num(2), num(3), num(4) as u64),
        _ => println!("usage: selftest | scanp N0 N1 wmax off | negctl | vform N0 N1 wmax | primes | ineq | struct N0 N1 seed"),
    }
}
fn f_off(_n: i128, off: i128) -> i128 { off }
fn f_print(_o: i128) -> bool { true }
