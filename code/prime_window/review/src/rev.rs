// REV: independent exact-integer engine for the the accompanying code Theorem S review.
// Own code; me/eng*.rs NOT read. Decision procedure: "ML(V) >= s/T" exactly, V = R u W.
//   time t = P/(v*T) stored as (P,v); tau = s/T.
//   Step 1: closed good set G of the "base" speeds R = union of closed gaps between open bands
//           ((cT-s)/(vT),(cT+s)/(vT)), c=1..v, plus the c=0 band folded into the start value s/(vmin T).
//   Step 2: for each gap [a,b] run a forward jump iteration over the extra speeds W:
//           if frac(u t) < s/T jump to (f+s/T)/u ; if frac(u t) > 1-s/T jump to (f+1+s/T)/u ; stop when all good or t>b.
// All arithmetic u128 with checked ops (panic on overflow, never wraps).
use std::cmp::Ordering;
use std::env;
use std::io::Write;

type U = u128;
#[inline] fn mul(a: U, b: U) -> U { a.checked_mul(b).expect("overflow mul") }
#[inline] fn add(a: U, b: U) -> U { a.checked_add(b).expect("overflow add") }

#[derive(Clone, Copy)]
struct Tau { s: U, t: U }
type Tm = (U, U); // P/(v*T)

fn tcmp(a: Tm, b: Tm) -> Ordering { mul(a.0, b.1).cmp(&mul(b.0, a.1)) }

fn gaps(base: &[u64], tau: Tau) -> Vec<(Tm, Tm)> {
    let mut bands: Vec<(U, U, U)> = Vec::new(); // (leftP, rightP, v)
    for &v in base {
        for c in 1..=v as U {
            let l = mul(c, tau.t) - tau.s; // s <= T/2 < T so >0
            let r = add(mul(c, tau.t), tau.s);
            bands.push((l, r, v as U));
        }
    }
    bands.sort_by(|a, b| mul(a.0, b.2).cmp(&mul(b.0, a.2)));
    let vmin = *base.iter().min().unwrap() as U;
    let mut cur: Tm = (tau.s, vmin);
    let mut out = Vec::new();
    for b in &bands {
        let l: Tm = (b.0, b.2);
        let r: Tm = (b.1, b.2);
        if tcmp(l, cur) != Ordering::Less { out.push((cur, l)); }
        if tcmp(r, cur) == Ordering::Greater { cur = r; }
    }
    assert!(tcmp(cur, (tau.t, 1)) == Ordering::Greater, "tail not covered");
    out
}

fn jump(t: Tm, u: U, tau: Tau) -> Option<Tm> {
    let x = mul(u, t.0);
    let y = mul(t.1, tau.t);
    let f = x / y;
    let rho = x % y;
    if mul(rho, tau.t) < mul(tau.s, y) {
        Some((add(mul(f, tau.t), tau.s), u))
    } else if mul(y - rho, tau.t) < mul(tau.s, y) {
        Some((add(mul(f + 1, tau.t), tau.s), u))
    } else {
        None
    }
}

fn gap_good(g: &(Tm, Tm), w: &[U], tau: Tau) -> bool {
    let mut t = g.0;
    loop {
        let mut changed = false;
        for &u in w {
            if let Some(nt) = jump(t, u, tau) {
                t = nt;
                changed = true;
                if tcmp(t, g.1) == Ordering::Greater { return false; }
            }
        }
        if !changed { return true; }
    }
}

fn ml_ge(gs: &[(Tm, Tm)], w: &[U], tau: Tau) -> bool {
    gs.iter().any(|g| gap_good(g, w, tau))
}

// brute exact ML via candidate times m/(vi+vj)
fn ml_brute(v: &[u64]) -> (u64, u64) {
    let mut best = (0u64, 1u64);
    for i in 0..v.len() {
        for j in i..v.len() {
            let q = v[i] + v[j];
            for m in 1..q {
                let mut mn = q;
                for &x in v {
                    let rho = (x * m) % q;
                    let d = rho.min(q - rho);
                    if d < mn { mn = d; if mn == 0 { break; } }
                }
                if (mn as u128) * (best.1 as u128) > (best.0 as u128) * (q as u128) { best = (mn, q); }
            }
        }
    }
    let g = gcd(best.0, best.1);
    (best.0 / g, best.1 / g)
}
fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 { self.0 ^= self.0 >> 12; self.0 ^= self.0 << 25; self.0 ^= self.0 >> 27; self.0.wrapping_mul(0x2545F4914F6CDD1D) }
    fn range(&mut self, a: u64, b: u64) -> u64 { a + self.next() % (b - a + 1) } // inclusive
    fn logu(&mut self, a: f64, b: f64) -> u128 { let x = (self.next() >> 11) as f64 / (1u64 << 53) as f64; (a.ln() + x * (b.ln() - a.ln())).exp() as u128 }
}

fn sieve(n: usize) -> Vec<bool> {
    let mut p = vec![true; n + 1];
    p[0] = false; if n >= 1 { p[1] = false; }
    let mut i = 2;
    while i * i <= n { if p[i] { let mut j = i * i; while j <= n { p[j] = false; j += i; } } i += 1; }
    p
}
fn window_primes(isp: &[bool], n: u64, r: u64) -> Vec<u64> {
    let lo = n + 1 + r; let hi = 2 * n - 1;
    if lo > hi { return vec![]; }
    (lo..=hi).filter(|&x| isp[x as usize]).collect()
}
fn inv_mod(a: i128, m: i128) -> i128 {
    let (mut r0, mut r1, mut s0, mut s1) = (a.rem_euclid(m), m, 1i128, 0i128);
    while r1 != 0 { let q = r0 / r1; let t = r0 - q * r1; r0 = r1; r1 = t; let t = s0 - q * s1; s0 = s1; s1 = t; }
    assert!(r0 == 1, "not invertible");
    s0.rem_euclid(m)
}
fn crt(mods: &[U], res: &[U]) -> (U, U) {
    let (mut x, mut m) = (0u128, 1u128);
    for (&p, &rr) in mods.iter().zip(res) {
        let cur = x % p;
        let diff = (rr % p + p - cur) % p;
        let k = (diff * (inv_mod((m % p) as i128, p as i128) as u128)) % p;
        x = add(x, mul(m, k));
        m = mul(m, p);
    }
    (x, m)
}

// proof chain (BO the accompanying notes Lemma C,S): returns (i, clean prime option)
fn chain_clean(n: u64, r: u64, k: u64, w: &[U], pl: &[u64]) -> (usize, Option<u64>) {
    let mut wprev = n as U; let mut i = 0usize;
    while i < w.len() { if w[i] > mul(mul(8 * k as U, n as U), wprev) { break; } wprev = w[i]; i += 1; }
    for &d in pl {
        let d128 = d as U; let mut clean = true;
        for j in 0..i {
            let wj = w[j];
            let m0 = wj % d128; let mr = (wj + d128 - (r as U % d128)) % d128; let mp = (wj + r as U) % d128;
            if m0 == 0 || mr == 0 || mp == 0 { clean = false; break; }
        }
        if clean { return (i, Some(d)); }
    }
    (i, None)
}

// Lemma Lip endpoint check: exact ||x t|| >= 1/N at t0, t0 +- delta for x in retained (<=N, !=r) and w_j, j<=i.
fn lip_check(n: u64, r: u64, d: u64, w: &[U], i: usize) -> Option<bool> {
    let l: U = if i == 0 { n as U } else { w[i - 1].max(n as U) };
    if l > 10u128.pow(13) { return None; }
    let a = inv_mod(r as i128, d as i128) as U;
    let den = mul(mul(d as U, n as U), l);
    let base = mul(mul(a, n as U), l);
    let step = (2 * n - d) as U;
    let mut speeds: Vec<U> = (1..=n as U).filter(|&x| x != r as U).collect();
    for j in 0..i { speeds.push(w[j]); }
    for tnum in [base, base + step, base - step] {
        for &x in &speeds {
            let rho = mul(x, tnum) % den;
            if mul(rho, n as U) < den || mul(den - rho, n as U) < den { return Some(false); }
        }
    }
    Some(true)
}

fn flush() { let _ = std::io::stdout().flush(); }

fn sub_thr(args: &[String]) {
    let maxn: usize = args[0].parse().unwrap();
    let isp = sieve(2 * maxn + 2);
    let ks: Vec<u64> = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 20, 30, 50, 100, 150, 200, 300];
    let mut last_fail = vec![0usize; ks.len()];
    let mut first_ok = vec![0usize; ks.len()];
    // c(N) = pi(2N) - pi(N + N/2); incremental
    let mut pi2: u64 = 0; let mut p2pos = 0usize; // counted primes <= p2pos
    let mut pi1: u64 = 0; let mut p1pos = 0usize;
    for n in 2..=maxn {
        while p2pos < 2 * n { p2pos += 1; if isp[p2pos] { pi2 += 1; } }
        let m = n + n / 2;
        while p1pos < m { p1pos += 1; if isp[p1pos] { pi1 += 1; } }
        let c = pi2 - pi1;
        for (idx, &k) in ks.iter().enumerate() {
            let tk = 3 * k * (k + 1) + 1;
            if c < tk { last_fail[idx] = n; } else if first_ok[idx] == 0 { first_ok[idx] = n; }
        }
    }
    println!("# thr maxN={} (exact sieve to {})", maxn, 2 * maxn + 2);
    println!("# k T_k Nstar(last_fail+1) firstN_ok  Nstar/(k^2 ln k)  [Nstar = 1 + last N<=maxN with c(N)<T_k; valid only if last_fail << maxN]");
    for (idx, &k) in ks.iter().enumerate() {
        let tk = 3 * k * (k + 1) + 1;
        let lnk = (k as f64).ln().max(1e-9);
        println!("k={} T={} Nstar={} first_ok={} ratio={:.3} lastfail/maxN={:.4}", k, tk, last_fail[idx] + 1, first_ok[idx], (last_fail[idx] + 1) as f64 / (k as f64 * k as f64 * lnk), last_fail[idx] as f64 / maxn as f64);
    }
    // Dusart analytic (float evidence): smallest N>=300 with (N/L)*Hlow >= T_k, L=ln(1.5N)
    println!("# Dusart-(6.5) analytic threshold (float): first N>=300 with (N/L)(1/2 - 1.9143/L - 0.57538/L^2) >= T_k");
    for &k in &ks {
        let tk = (3 * k * (k + 1) + 1) as f64;
        let mut lo = 300f64; let mut hi = 1e13f64;
        let f = |n: f64| { let l = (1.5 * n).ln(); n / l * (0.5 - 1.9143 / l - 0.57538 / (l * l)) };
        for _ in 0..200 { let mid = (lo + hi) / 2.0; if f(mid) >= tk { hi = mid } else { lo = mid } }
        println!("k={} N_D={:.0}", k, hi.ceil());
    }
    // direct check: for N<=3000 min over r<=N/2 of |P(N,r)| is at r=floor(N/2)
    let mut bad = 0;
    for n in 4..=3000u64 {
        let mut mn = u64::MAX; let mut at = 0;
        for r in 1..=n / 2 { let c = window_primes(&isp, n, r).len() as u64; if c < mn { mn = c; at = r; } }
        let c2 = window_primes(&isp, n, n / 2).len() as u64;
        if mn != c2 { bad += 1; println!("MIN-NOT-AT-FLOOR N={} min={} at r={}", n, mn, at); }
    }
    println!("# window-min-at-floor check N=4..3000: {} violations", bad);
}

fn sub_ctl(_args: &[String]) {
    let mut fails = 0;
    // planted: (name, N, r, W, expected ML fraction)
    let planted: Vec<(&str, u64, u64, Vec<u64>, (u64, u64))> = vec![
        ("[20]-6+{29,31}", 20, 6, vec![29, 31], (2, 41)),
        ("[13]-6+69", 13, 6, vec![69], (3, 40)),
        ("[13]-12+36", 13, 12, vec![36], (3, 41)),
        ("[29]-12+{31,94,98}", 29, 12, vec![31, 94, 98], (0, 0)), // value computed, compare vs 1/29
        ("[21]-6+{29,31}", 21, 6, vec![29, 31], (0, 0)),
        ("[8]", 8, 100, vec![], (1, 9)),
    ];
    for (name, n, r, w, exp) in &planted {
        let v: Vec<u64> = if *r > *n { (1..=*n).collect() } else { (1..=*n).filter(|x| x != r).collect::<Vec<_>>() }.into_iter().chain(w.iter().cloned()).collect();
        let (p, q) = ml_brute(&v);
        // engine at thresholds
        let base: Vec<u64> = v.iter().cloned().filter(|&x| x <= *n).collect();
        let big: Vec<U> = v.iter().cloned().filter(|&x| x > *n).map(|x| x as U).collect();
        let kk = 1000u128;
        let at = |s: U, t: U| { let tau = Tau { s, t }; let g = gaps(&base, tau); ml_ge(&g, &big, tau) };
        let e0 = at(p as U, q as U);
        let e_up = at(mul(p as U, kk) + 1, mul(q as U, kk));
        let e_dn = at(mul(p as U, kk) - 1, mul(q as U, kk));
        let lt_n = !at(1, *n as U);
        let ok = e0 && !e_up && e_dn;
        if !ok { fails += 1; }
        println!("PLANT {:22} brute ML={}/{} (exp {:?}) engine: ge(ML)={} ge(ML+eps)={} ge(ML-eps)={} ML<1/N={} -> {}", name, p, q, exp, e0, e_up, e_dn, lt_n, if ok { "OK" } else { "FAIL" });
        if exp.1 != 0 && (p, q) != *exp { fails += 1; println!("  MISMATCH expected value"); }
    }
    println!("CTL planted failures: {}", fails);
    // random small sets: engine vs brute at exact value and one step either side
    let mut rng = Rng(0x9E3779B97F4A7C15);
    let mut mism = 0u64; let mut tot = 0u64;
    for _ in 0..6000 {
        let n = rng.range(3, 9);
        let mut v: Vec<u64> = (0..n).map(|_| rng.range(1, 80)).collect();
        v.sort(); v.dedup();
        if v.len() < 2 { continue; }
        let (p, q) = ml_brute(&v);
        let split = rng.range(1, v.len() as u64 - 1) as usize;
        let base = &v[..split]; let big: Vec<U> = v[split..].iter().map(|&x| x as U).collect();
        let kk = 997u128;
        let at = |s: U, t: U| { let tau = Tau { s, t }; let g = gaps(base, tau); ml_ge(&g, &big, tau) };
        tot += 1;
        if !at(p as U, q as U) || at(mul(p as U, kk) + 1, mul(q as U, kk)) || !at(mul(p as U, kk) - 1, mul(q as U, kk)) { mism += 1; println!("MISMATCH v={:?} ml={}/{}", v, p, q); }
    }
    println!("XVAL random small sets: {} tested, {} mismatches", tot, mism);
    // one-hole sets with extras: [N]\{r} u W, N<=24
    let mut mism2 = 0u64; let mut tot2 = 0u64;
    for _ in 0..1500 {
        let n = rng.range(6, 24); let r = rng.range(1, n);
        let kx = rng.range(1, 3);
        let mut w: Vec<u64> = (0..kx).map(|_| rng.range(n + 1, 4 * n + 20)).collect();
        w.sort(); w.dedup();
        let mut v: Vec<u64> = (1..=n).filter(|&x| x != r).collect();
        v.extend(w.iter());
        let (p, q) = ml_brute(&v);
        let base: Vec<u64> = (1..=n).filter(|&x| x != r).collect();
        let big: Vec<U> = w.iter().map(|&x| x as U).collect();
        let kk = 997u128;
        let at = |s: U, t: U| { let tau = Tau { s, t }; let g = gaps(&base, tau); ml_ge(&g, &big, tau) };
        tot2 += 1;
        if !at(p as U, q as U) || at(mul(p as U, kk) + 1, mul(q as U, kk)) || !at(mul(p as U, kk) - 1, mul(q as U, kk)) { mism2 += 1; println!("MISMATCH1 N={} r={} w={:?} ml={}/{}", n, r, w, p, q); }
    }
    println!("XVAL one-hole+W sets N=6..24: {} tested, {} mismatches", tot2, mism2);
    // CRT / chain self-test: crt helper
    let (x, m) = crt(&[7, 11, 13], &[3, 5, 9]);
    assert!(x % 7 == 3 && x % 11 == 5 && x % 13 == 9 && m == 1001);
    println!("CRT selftest ok x={} m={}", x, m);
}

// shared per-(N,r) record
struct Stats { jd_tot: u64, jd_fail: u64, tot: u64, ok: u64, notok: u64, clean: u64, clean_notok: u64, lip_fail: u64, lip_skip: u64, hyp_notok: u64 }
impl Stats { fn new() -> Self { Stats { jd_tot: 0, jd_fail: 0, tot: 0, ok: 0, notok: 0, clean: 0, clean_notok: 0, lip_fail: 0, lip_skip: 0, hyp_notok: 0 } } }

fn eval_set(n: u64, r: u64, k: u64, gs: &[(Tm, Tm)], pl: &[u64], w: &[U], st: &mut Stats, hyp: bool, do_lip: bool) {
    let tau = Tau { s: 1, t: n as U };
    let ok = ml_ge(gs, w, tau);
    st.tot += 1;
    if ok { st.ok += 1 } else {
        st.notok += 1;
        if hyp { st.hyp_notok += 1; }
        println!("NOTOK N={} r={} k={} W={:?} |P|={} hyp(|P|>=T_k)={}", n, r, k, w, pl.len(), hyp);
    }
    let (i, cl) = if 8 * k <= n { chain_clean(n, r, k, w, pl) } else { (0, None) };
    if let Some(d) = cl {
        st.clean += 1;
        if !ok { st.clean_notok += 1; println!("LEMMA-LEVEL DEFECT: clean prime {} exists but ML<1/N N={} r={} W={:?}", d, n, r, w); }
        if do_lip && i <= w.len() {
            // lemma-level (Lip+M) check for the first and the LAST clean window prime: J_D must contain a time good for all large speeds
            let mut cands: Vec<u64> = Vec::new();
            for &dd in pl { let mut c = true; for j in 0..i { let wj = w[j]; let d128 = dd as U; if wj % d128 == 0 || (wj + d128 - (r as U % d128)) % d128 == 0 || (wj + r as U) % d128 == 0 { c = false; break; } } if c { cands.push(dd); } }
            let lcap = 10u128.pow(12);
            let l: U = if i == 0 { n as U } else { w[i - 1].max(n as U) };
            if l <= lcap && !cands.is_empty() {
                for &dd in [cands[0], *cands.last().unwrap()].iter() {
                    let a = inv_mod(r as i128, dd as i128) as U;
                    let v = mul(dd as U, l);
                    let pc = mul(mul(a, n as U), l);
                    let step = (2 * n - dd) as U;
                    let jg: (Tm, Tm) = ((pc - step, v), (pc + step, v));
                    let large: Vec<U> = w[i..].to_vec();
                    st.jd_tot += 1;
                    if !gap_good(&jg, &large, tau) { st.jd_fail += 1; println!("JD FAIL (Lip+M lemma-level) N={} r={} D={} W={:?}", n, r, dd, w); }
                }
            }
        }
        if do_lip {
            match lip_check(n, r, d, w, i) { Some(true) => {}, Some(false) => { st.lip_fail += 1; println!("LIP FAIL N={} r={} D={} W={:?}", n, r, d, w); }, None => st.lip_skip += 1 }
        }
    }
}

fn sub_mid(args: &[String]) {
    // all pairs w1<w2<=wmax, k=2, N in [nlo,nhi]; r<=N/2 or |P(N,r)|>=19
    let nlo: u64 = args[0].parse().unwrap(); let nhi: u64 = args[1].parse().unwrap(); let wmax: u64 = args[2].parse().unwrap();
    let isp = sieve(4 * nhi as usize + 10);
    let k = 2u64; let tk = 3 * k * (k + 1) + 1;
    let mut gst = Stats::new();
    let t0 = std::time::Instant::now();
    for n in nlo..=nhi {
        let mut nrs = 0u64; let mut nhyp = 0u64;
        for r in 1..=n - 2 {
            let pl = window_primes(&isp, n, r);
            let hyp = pl.len() as u64 >= tk;
            if !(2 * r <= n || hyp) { continue; }
            nrs += 1; if hyp { nhyp += 1; }
            let base: Vec<u64> = (1..=n).filter(|&x| x != r).collect();
            let tau = Tau { s: 1, t: n as U };
            let mut gs = gaps(&base, tau);
            gs.sort_by(|a, b| { let la = (a.1 .0 as f64) / (a.1 .1 as f64) - (a.0 .0 as f64) / (a.0 .1 as f64); let lb = (b.1 .0 as f64) / (b.1 .1 as f64) - (b.0 .0 as f64) / (b.0 .1 as f64); lb.partial_cmp(&la).unwrap() });
            if gs.is_empty() { println!("EMPTY-G N={} r={} (ML([N]\\r)<1/N already)", n, r); gst.notok += 1; continue; }
            let mut st = Stats::new();
            for w1 in n + 1..=wmax {
                for w2 in w1 + 1..=wmax {
                    // fast path: engine only; chain implication checked on a thin subsample
                    let w = [w1 as U, w2 as U];
                    let tau = Tau { s: 1, t: n as U };
                    st.tot += 1;
                    if ml_ge(&gs, &w, tau) { st.ok += 1; } else {
                        st.notok += 1; if hyp { st.hyp_notok += 1; }
                        println!("NOTOK N={} r={} W={:?} |P|={} hyp={}", n, r, w, pl.len(), hyp);
                    }
                    if (w1 * 31 + w2) % 97 == 0 {
                        let (_, cl) = chain_clean(n, r, k, &w, &pl);
                        if cl.is_some() { st.clean += 1; if st.notok > 0 && !ml_ge(&gs, &w, tau) { st.clean_notok += 1; println!("LEMMA-LEVEL DEFECT N={} r={} W={:?}", n, r, w); } }
                    }
                }
            }
            gst.tot += st.tot; gst.ok += st.ok; gst.notok += st.notok; gst.hyp_notok += st.hyp_notok; gst.clean += st.clean; gst.clean_notok += st.clean_notok;
        }
        println!("N={} (N,r) pairs={} (with |P|>=19: {}) cum sets={} cum notok={} cum hyp_notok={} elapsed={:.0}s", n, nrs, nhyp, gst.tot, gst.notok, gst.hyp_notok, t0.elapsed().as_secs_f64());
        flush();
    }
    println!("MID DONE N={}..{} wmax={}: sets={} ok={} notok={} hyp_notok={} (clean-prime subsample {} , lemma-level defects {})", nlo, nhi, wmax, gst.tot, gst.ok, gst.notok, gst.hyp_notok, gst.clean, gst.clean_notok);
}

// structured generator; returns sorted distinct W (all > N), size 1..=k
fn gen_struct(rng: &mut Rng, n: u64, r: u64, k: u64, pl: &[u64], cap: U) -> Vec<U> {
    let mut w: Vec<U> = Vec::new();
    let fam = rng.range(0, 7);
    let m = rng.range(1, k) as usize;
    // helper: product spoiler from slice of primes
    let spoil = |rng: &mut Rng, ps: &[u64]| -> U {
        let mods: Vec<U> = ps.iter().map(|&p| p as U).collect();
        let mode = rng.range(0, 2);
        if mode == 0 {
            // common class e: w = c*prod + e r
            let e = rng.range(0, 2) as i64 - 1; let c = rng.range(1, 3) as U;
            let prod = mods.iter().fold(1u128, |a, &b| a.checked_mul(b).unwrap_or(u128::MAX / 4));
            let base = c.saturating_mul(prod) as i128 + (e * r as i64) as i128;
            base.max(n as i128 + 1) as U
        } else {
            let res: Vec<U> = mods.iter().map(|_| { let e = rng.range(0, 2) as i64 - 1; ((e * r as i64).rem_euclid(1 << 40)) as U }).collect();
            // residues must be e*r mod p
            let res2: Vec<U> = mods.iter().zip(res.iter()).map(|(&p, _)| { let e = rng.range(0, 2) as i64 - 1; (((e * r as i64) % p as i64 + p as i64) % p as i64) as U }).collect();
            let (x, mm) = crt(&mods, &res2);
            let mut x = x; while x <= n as U { x = x.saturating_add(mm); } x
        }
    };
    let np = pl.len();
    match fam {
        0 | 1 => {
            // disjoint contiguous groups of smallest primes, sizes random
            let mut start = if rng.range(0, 3) == 0 { rng.range(0, np as u64 / 2) as usize } else { 0 };
            for _ in 0..m {
                let sz = rng.range(1, 6) as usize;
                if start + sz > np { break; }
                w.push(spoil(rng, &pl[start..start + sz]));
                start += sz;
            }
        }
        2 => {
            // lacunary: w1 small spoiler or random, then ratios near 8kN
            let sz = rng.range(0, 3) as usize;
            let w1 = if sz == 0 || sz > np { rng.range(n + 1, 40 * n) as U } else { spoil(rng, &pl[..sz]) };
            w.push(w1);
            let mut prev = w1;
            for _ in 1..m {
                let ratio = mul(8 * k as U, n as U) as i128 + rng.range(0, 40) as i128 - 20;
                let nxt = (prev as i128 * ratio.max(2)) + rng.range(0, 20) as i128 - 10;
                prev = nxt.max(n as i128 + 1) as U; w.push(prev);
            }
        }
        3 => {
            // equal mod a spoil modulus: w2 = w1 + j * prod(subset)
            let sz = rng.range(1, 4) as usize;
            if sz <= np {
                let w1 = spoil(rng, &pl[..sz]);
                w.push(w1);
                let prod: U = pl[..sz].iter().fold(1u128, |a, &b| a * b as u128);
                for _ in 1..m { w.push(w1 + prod * rng.range(1, 6) as U); }
            }
        }
        5 | 6 => {
            // adversarial large speeds: multiples of the LARGEST window prime D (so ||u t0||=0 or 1/D at its window), just above 8kN*L
            let d = *pl.last().unwrap() as U;
            let sz = rng.range(0, 2) as usize;
            let w1 = if sz == 0 || sz > pl.len() { None } else { Some(spoil(rng, &pl[..sz])) };
            let mut l = n as U;
            if let Some(x) = w1 { w.push(x); l = x.max(l); }
            let thr = mul(mul(8 * k as U, n as U), l);
            let base = (thr / d + 1 + rng.range(0, 3) as U) * d;
            let cnt = if w1.is_some() { m.saturating_sub(1).max(1) } else { m.max(1) };
            for _ in 0..cnt {
                let e = rng.range(0, 2) as i64 - 1;
                let uu = (base as i128 + (e * r as i64) as i128 + (rng.range(0, 4) as i128) * d as i128) as U;
                w.push(uu);
                let _ = rng.range(0, 1);
            }
        }
        _ => {
            // multiples of a window prime D times near-threshold, plus random
            let d = pl[rng.range(0, np as u64 - 1) as usize] as U;
            w.push(d * rng.range(1, 30) as U + (rng.range(0, 2) as U).saturating_sub(1).min(1) * 0);
            for _ in 1..m { w.push(rng.logu(n as f64 + 1.0, 1e9)); }
        }
    }
    w.retain(|&x| x > n as U && x <= cap);
    w.sort(); w.dedup();
    if w.is_empty() { w.push(rng.logu(n as f64 + 1.0, 1e6)); }
    w
}

fn sub_struct(args: &[String]) {
    // struct k Nlo Nhi nsamp seed rmode
    let k: u64 = args[0].parse().unwrap(); let nlo: u64 = args[1].parse().unwrap(); let nhi: u64 = args[2].parse().unwrap();
    let nsamp: u64 = args[3].parse().unwrap(); let seed: u64 = args[4].parse().unwrap(); let rmode: String = args[5].clone();
    let isp = sieve(4 * nhi as usize + 10);
    let tk = 3 * k * (k + 1) + 1;
    let mut rng = Rng(seed | 1);
    let mut gst = Stats::new();
    let t0 = std::time::Instant::now();
    for n in nlo..=nhi {
        let mut rs: Vec<u64> = Vec::new();
        match rmode.as_str() {
            "pick" => { rs = vec![1, 2, 3, 5, 17, n / 5, n / 3, n / 2 - 1, n / 2]; }
            "all" => { rs = (1..=n / 2).collect(); }
            "rand" => { for _ in 0..12 { rs.push(rng.range(1, n / 2)); } }
            _ => panic!(),
        }
        rs.retain(|&r| r >= 1 && r + 2 <= n); rs.sort(); rs.dedup();
        for &r in &rs {
            let pl = window_primes(&isp, n, r);
            let hyp = pl.len() as u64 >= tk;
            let base: Vec<u64> = (1..=n).filter(|&x| x != r).collect();
            let tau = Tau { s: 1, t: n as U };
            let mut gs = gaps(&base, tau);
            gs.sort_by(|a, b| { let la = (a.1 .0 as f64) / (a.1 .1 as f64) - (a.0 .0 as f64) / (a.0 .1 as f64); let lb = (b.1 .0 as f64) / (b.1 .1 as f64) - (b.0 .0 as f64) / (b.0 .1 as f64); lb.partial_cmp(&la).unwrap() });
            let mut st = Stats::new();
            if gs.is_empty() { println!("EMPTY-G N={} r={}", n, r); continue; }
            for _ in 0..nsamp {
                let w = gen_struct(&mut rng, n, r, k, &pl, 10u128.pow(15));
                eval_set(n, r, k, &gs, &pl, &w, &mut st, hyp, true);
            }
            gst.tot += st.tot; gst.ok += st.ok; gst.notok += st.notok; gst.hyp_notok += st.hyp_notok; gst.clean += st.clean; gst.clean_notok += st.clean_notok; gst.lip_fail += st.lip_fail; gst.lip_skip += st.lip_skip; gst.jd_tot += st.jd_tot; gst.jd_fail += st.jd_fail;
            println!("N={} r={} |P|={} hyp={} sets={} ok={} notok={} clean={} clean_notok={} lip_fail={} lip_skip={} t={:.0}s", n, r, pl.len(), hyp, st.tot, st.ok, st.notok, st.clean, st.clean_notok, st.lip_fail, st.lip_skip, t0.elapsed().as_secs_f64());
            flush();
        }
    }
    println!("STRUCT DONE k={} N={}..{} : sets={} ok={} notok={} hyp_notok={} clean={} clean_notok={} lip_fail={} lip_skip={} JD_checks={} JD_fail={}", k, nlo, nhi, gst.tot, gst.ok, gst.notok, gst.hyp_notok, gst.clean, gst.clean_notok, gst.lip_fail, gst.lip_skip, gst.jd_tot, gst.jd_fail);
}

fn sub_rand(args: &[String]) {
    // rand k Nlo Nhi nNR nsamp wcap seed
    let k: u64 = args[0].parse().unwrap(); let nlo: u64 = args[1].parse().unwrap(); let nhi: u64 = args[2].parse().unwrap();
    let nnr: u64 = args[3].parse().unwrap(); let nsamp: u64 = args[4].parse().unwrap(); let wcap: f64 = args[5].parse().unwrap(); let seed: u64 = args[6].parse().unwrap();
    let isp = sieve(4 * nhi as usize + 10);
    let tk = 3 * k * (k + 1) + 1;
    let mut rng = Rng(seed | 1);
    let mut gst = Stats::new();
    let t0 = std::time::Instant::now();
    for it in 0..nnr {
        let n = rng.range(nlo, nhi);
        let r = if rng.range(0, 9) < 7 { rng.range(1, n / 2) } else { rng.range(1, n - 2) };
        let pl = window_primes(&isp, n, r);
        let hyp = pl.len() as u64 >= tk;
        if !(2 * r <= n || hyp) { continue; }
        let base: Vec<u64> = (1..=n).filter(|&x| x != r).collect();
        let tau = Tau { s: 1, t: n as U };
        let mut gs = gaps(&base, tau);
        gs.sort_by(|a, b| { let la = (a.1 .0 as f64) / (a.1 .1 as f64) - (a.0 .0 as f64) / (a.0 .1 as f64); let lb = (b.1 .0 as f64) / (b.1 .1 as f64) - (b.0 .0 as f64) / (b.0 .1 as f64); lb.partial_cmp(&la).unwrap() });
        if gs.is_empty() { println!("EMPTY-G N={} r={}", n, r); continue; }
        let mut st = Stats::new();
        for _ in 0..nsamp {
            let w = if rng.range(0, 1) == 0 {
                let mut v: Vec<U> = (0..rng.range(1, k)).map(|_| rng.logu(n as f64 + 1.0, wcap)).collect(); v.sort(); v.dedup(); v
            } else { gen_struct(&mut rng, n, r, k, &pl, wcap as U) };
            let w: Vec<U> = w.into_iter().filter(|&x| x > n as U).collect();
            if w.is_empty() { continue; }
            eval_set(n, r, k, &gs, &pl, &w, &mut st, hyp, true);
        }
        gst.tot += st.tot; gst.ok += st.ok; gst.notok += st.notok; gst.hyp_notok += st.hyp_notok; gst.clean += st.clean; gst.clean_notok += st.clean_notok; gst.lip_fail += st.lip_fail; gst.lip_skip += st.lip_skip; gst.jd_tot += st.jd_tot; gst.jd_fail += st.jd_fail;
        if it % 50 == 0 { println!("it={} N={} r={} |P|={} cum sets={} notok={} hyp_notok={} clean_notok={} lip_fail={} t={:.0}s", it, n, r, pl.len(), gst.tot, gst.notok, gst.hyp_notok, gst.clean_notok, gst.lip_fail, t0.elapsed().as_secs_f64()); flush(); }
    }
    println!("RAND DONE k={} N={}..{} wcap={:e}: sets={} ok={} notok={} hyp_notok={} clean={} clean_notok={} lip_fail={} lip_skip={}", k, nlo, nhi, wcap, gst.tot, gst.ok, gst.notok, gst.hyp_notok, gst.clean, gst.clean_notok, gst.lip_fail, gst.lip_skip);
}


fn sub_spoilall(args: &[String]) {
    // spoilall k Nlo Nhi nsamp seed maxprod_log10
    let k: u64 = args[0].parse().unwrap(); let nlo: u64 = args[1].parse().unwrap(); let nhi: u64 = args[2].parse().unwrap();
    let nsamp: u64 = args[3].parse().unwrap(); let seed: u64 = args[4].parse().unwrap(); let lg: u32 = args[5].parse().unwrap();
    let cap: U = 10u128.pow(lg);
    let isp = sieve(4 * nhi as usize + 10);
    let tk = 3 * k * (k + 1) + 1;
    let mut rng = Rng(seed | 1);
    let mut gst = Stats::new(); let mut noclean = 0u64; let mut pairs = 0u64;
    let t0 = std::time::Instant::now();
    for n in nlo..=nhi {
        for r in 1..=n / 2 {
            let pl = window_primes(&isp, n, r);
            if pl.is_empty() { continue; }
            // feasibility: balanced groups of the smallest primes must fit under cap
            let g = (pl.len() as u64 + k - 1) / k;
            let mut prod: U = 1; let mut fits = true;
            for &p in pl.iter().rev().take(g as usize) { match prod.checked_mul(p as U) { Some(x) => prod = x, None => { fits = false; break; } } }
            if !fits || prod > cap { continue; }
            let base: Vec<u64> = (1..=n).filter(|&x| x != r).collect();
            let tau = Tau { s: 1, t: n as U };
            let mut gs = gaps(&base, tau);
            gs.sort_by(|a, b| { let la = (a.1 .0 as f64) / (a.1 .1 as f64) - (a.0 .0 as f64) / (a.0 .1 as f64); let lb = (b.1 .0 as f64) / (b.1 .1 as f64) - (b.0 .0 as f64) / (b.0 .1 as f64); lb.partial_cmp(&la).unwrap() });
            if gs.is_empty() { println!("EMPTY-G N={} r={}", n, r); continue; }
            pairs += 1;
            let hyp = pl.len() as u64 >= tk;
            let mut st = Stats::new();
            for _ in 0..nsamp {
                // random partition of ALL window primes into k groups (sizes balanced +-1), random e per prime
                let mut idx: Vec<usize> = (0..pl.len()).collect();
                for i in (1..idx.len()).rev() { let j = rng.range(0, i as u64) as usize; idx.swap(i, j); }
                let mut w: Vec<U> = Vec::new(); let mut okgen = true;
                for gi in 0..k as usize {
                    let grp: Vec<U> = idx.iter().enumerate().filter(|(pos, _)| pos % k as usize == gi).map(|(_, &i)| pl[i] as U).collect();
                    if grp.is_empty() { continue; }
                    let res: Vec<U> = grp.iter().map(|&p| { let e = rng.range(0, 2) as i64 - 1; (((e * r as i64) % p as i64 + p as i64) % p as i64) as U }).collect();
                    let (x, m) = crt(&grp, &res);
                    let mut x = x; let sh = rng.range(0, 2) as U;
                    while x <= n as U { x = x.saturating_add(m); }
                    x = x.saturating_add(m * sh);
                    if x > cap * 100 { okgen = false; break; }
                    w.push(x);
                }
                if !okgen { continue; }
                w.sort(); w.dedup();
                let (_, cl) = chain_clean(n, r, k, &w, &pl);
                if cl.is_none() { noclean += 1; }
                eval_set(n, r, k, &gs, &pl, &w, &mut st, hyp, true);
            }
            gst.tot += st.tot; gst.ok += st.ok; gst.notok += st.notok; gst.hyp_notok += st.hyp_notok; gst.clean += st.clean; gst.clean_notok += st.clean_notok; gst.lip_fail += st.lip_fail; gst.lip_skip += st.lip_skip; gst.jd_tot += st.jd_tot; gst.jd_fail += st.jd_fail;
        }
        if n % 10 == 0 { println!("N={} pairs={} sets={} notok={} noclean_sets={} clean_notok={} t={:.0}s", n, pairs, gst.tot, gst.notok, noclean, gst.clean_notok, t0.elapsed().as_secs_f64()); flush(); }
    }
    println!("SPOILALL DONE k={} N={}..{} : (N,r) pairs={} sets={} ok={} notok={} sets_with_NO_clean_prime(chain)={} hyp_notok={} clean_notok={} lip_fail={}", k, nlo, nhi, pairs, gst.tot, gst.ok, gst.notok, noclean, gst.hyp_notok, gst.clean_notok, gst.lip_fail);
}

fn sub_jdctl(_a: &[String]) {
    // negative control for the lemma-level JD check: u = D*m (so ||u t0||=0). Predicted: J_D fully covered iff delta < 1/(N u), i.e. u < D*L/(2N-D)
    let isp = sieve(5000);
    for &(n, r) in &[(100u64, 10u64), (150, 20), (221, 55)] {
        let pl = window_primes(&isp, n, r);
        let d = *pl.last().unwrap();
        let l = n as U; let tau = Tau { s: 1, t: n as U };
        let a = inv_mod(r as i128, d as i128) as U;
        let v = mul(d as U, l); let pc = mul(mul(a, n as U), l); let step = (2 * n - d) as U;
        let jg: (Tm, Tm) = ((pc - step, v), (pc + step, v));
        let thr = (d as U * l) / (2 * n as U - d as U); // single band covers J iff u < thr
        let (mut fail_below, mut tot_below, mut fail_above, mut tot_above, mut first_ok_above) = (0, 0, 0, 0, 0u128);
        for m in 1..(200 * n as U) {
            let u = d as U * m;
            let bad = !gap_good(&jg, &[u], tau);
            if u * 10 < thr * 9 { tot_below += 1; if bad { fail_below += 1; } }
            else if u > thr * 11 / 10 { tot_above += 1; if bad { fail_above += 1; } else if first_ok_above == 0 { first_ok_above = u; } }
        }
        println!("JDCTL N={} r={} D={} thr(single-band cover)={} : below thr (u<0.9thr) fails {}/{} ; above 1.1thr fails {}/{} ; first passing u above={}  [8kN L for k=1 = {}]", n, r, d, thr, fail_below, tot_below, fail_above, tot_above, first_ok_above, 8 * n as U * l);
    }
}

fn main() {
    let a: Vec<String> = env::args().collect();
    match a[1].as_str() {
        "thr" => sub_thr(&a[2..]),
        "ctl" => sub_ctl(&a[2..]),
        "mid" => sub_mid(&a[2..]),
        "struct" => sub_struct(&a[2..]),
        "rand" => sub_rand(&a[2..]),
        "jdctl" => sub_jdctl(&a[2..]),
        "spoilall" => sub_spoilall(&a[2..]),
        _ => panic!("unknown"),
    }
}
