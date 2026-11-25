// pw.rs: three small exact/evidence checks.
//   pw b     : route B (arithmetic-progression coprime family) thresholds + exhaustive check of the lemma
//   pw cheb  : Chebyshev-30 inequalities C4..C7 checked numerically (f64 logs, evidence only) to n = LIM
//   pw wit   : exact enumeration of ALL rational witness times a/D, D <= 6N, against the lattice family
// Memory: cheb allocates 3 f64 arrays of LIM+1 (LIM = 4e6 -> ~100 MB). Others: negligible.
use std::env;

fn gcd(mut a: u64, mut b: u64) -> u64 { while b != 0 { let t = a % b; a = b; b = t; } a }
fn is_prime(n: u64) -> bool { if n < 2 { return false; } let mut d = 2; while d * d <= n { if n % d == 0 { return false; } d += 1; } true }

fn route_b() {
    // Scheme: m >= T, P = product of primes < m, D_i = P*(a0+i)+1, i=0..m-1, a0 = ceil((N+r)/P).
    // In-window for all r<=N/2 iff 2*P*m + 2 <= N.  Coprime-to-r loss <= #primes >= m dividing r <= s,
    // where s = m - T is enough iff (product of the m-T+1 smallest primes >= m) > N/2.
    println!("== route B intervals I_m = [2Pm+2, 2Q_m) (ln values; exact when < 2^120)");
    for &t in &[7u64, 10, 19, 37, 61] {
        let mut ivs: Vec<(f64, f64, u64)> = Vec::new();
        for m in t..(t + 80) {
            let mut lnp = 0f64; let mut pex: u128 = 1; let mut ok = true;
            for p in 2..m { if is_prime(p) { lnp += (p as f64).ln(); if ok { match pex.checked_mul(p as u128) { Some(v) => pex = v, None => ok = false } } } }
            let mut lnq = 0f64; let mut qex: u128 = 1; let mut okq = true; let mut cnt = 0; let mut q = m;
            while cnt < m - t + 1 { if is_prime(q) { lnq += (q as f64).ln(); cnt += 1; if okq { match qex.checked_mul(q as u128) { Some(v) => qex = v, None => okq = false } } } q += 1; }
            let lo = (2.0f64).ln() + (m as f64).ln() + lnp; let hi = (2.0f64).ln() + lnq;
            if m < t + 14 {
                let los = if ok && pex < (1u128 << 100) { format!("{}", 2 * pex * (m as u128) + 2) } else { format!("e^{:.2}", lo) };
                let his = if okq && qex < (1u128 << 100) { format!("{}", 2 * qex) } else { format!("e^{:.2}", hi) };
                println!("T={} m={} lo={} hi={} nonempty={}", t, m, los, his, hi > lo);
            }
            ivs.push((lo, hi, m));
        }
        // coverage: smallest start m0 such that from m0 on, intervals are nonempty and hi(m) >= lo(m+1) for all later m in range
        let n = ivs.len(); let mut start = n;
        for i in (0..n).rev() {
            let nonempty = ivs[i].1 > ivs[i].0;
            let chain = i + 1 >= n || ivs[i].1 >= ivs[i + 1].0;
            if nonempty && chain { start = i; } else { break; }
        }
        if start < n { println!("T={} : contiguous cover from m={} i.e. N >= e^{:.3} = {:.4e} (checked through m={})", t, ivs[start].2, ivs[start].0, ivs[start].0.exp(), ivs[n - 1].2); }
        else { println!("T={} : no contiguous cover found", t); }
    }
    // exhaustive check of the lemma itself for T=7: for each N, smallest m in 7..=17 such that for ALL r<=N/2
    // the block has >= 7 terms coprime to r, all inside [N+1+r, 2N-1], pairwise coprime.
    println!("== route B exhaustive, T=7: per N (79..=40000) does some m in 7..=17 work for all 1<=r<=N/2 ?");
    let mut last_fail = 0u64; let mut fails = 0u64; let mut pw_bad = 0u64;
    let ms: Vec<(u64, u64)> = (7u64..=17).map(|m| { let mut p = 1u64; for q in 2..m { if is_prime(q) { p *= q; } } (m, p) }).collect();
    for n in 79u64..=40000 {
        let mut okn = false;
        for &(m, p) in &ms {
            if 2 * p * m + 2 > n { continue; }
            let mut allr = true;
            for r in 1..=(n / 2) {
                let a0 = (n + r + p - 1) / p;
                let mut good = 0;
                for i in 0..m { let d = p * (a0 + i) + 1; if d < n + 1 + r || d > 2 * n - 1 { pw_bad += 1; } if gcd(d, r) == 1 { good += 1; } }
                if good < 7 { allr = false; break; }
            }
            if allr { okn = true; break; }
        }
        if !okn { last_fail = n; fails += 1; }
    }
    println!("T=7: failing N count={} last failing N={} window violations={}", fails, last_fail, pw_bad);
    // pairwise coprimality of P*(a0+i)+1 blocks: brute check
    let mut pc_bad = 0u64; let mut pc_tests = 0u64;
    for &(m, p) in &ms { for a0 in 1..400u64 { for i in 0..m { for j in (i + 1)..m { pc_tests += 1; if gcd(p * (a0 + i) + 1, p * (a0 + j) + 1) != 1 { pc_bad += 1; } } } } }
    println!("pairwise-coprime tests={} failures={}", pc_tests, pc_bad);
    // negative control: P replaced by P/2 (drop the prime 2) must produce failures
    let mut nc = 0u64; for a0 in 1..50u64 { for i in 0..11u64 { for j in (i + 1)..11 { if gcd(105 * (a0 + i) + 1, 105 * (a0 + j) + 1) != 1 { nc += 1; } } } }
    println!("negative control (modulus 105 instead of 210, m=11): non-coprime pairs={}", nc);
}

fn cheb() {
    const LIM: usize = 4_000_000;
    let mut lam = vec![0f64; LIM + 1];
    let mut comp = vec![false; LIM + 1];
    for p in 2..=LIM { if !comp[p] { let lp = (p as f64).ln(); let mut q = p; loop { lam[q] = lp; if q > LIM / p { break; } q *= p; } let mut j = p * p; while j <= LIM { comp[j] = true; j += p; } } }
    drop(comp);
    let mut psi = vec![0f64; LIM + 1]; let mut lf = vec![0f64; LIM + 1];
    for n in 1..=LIM { psi[n] = psi[n - 1] + lam[n]; lf[n] = lf[n - 1] + (n as f64).ln(); }
    let a = 2f64.ln() / 2.0 + 3f64.ln() / 3.0 + 5f64.ln() / 5.0 - 30f64.ln() / 30.0;
    println!("A = {:.10}  6A/5 = {:.10}", a, 1.2 * a);
    // control: psi(100) = ln lcm(1..100)
    println!("control psi(100)={:.6} (ln lcm(1..100)=94.0453...)  psi(10)={:.6} (ln 2520=7.832014)", psi[100], psi[10]);
    let ilog6 = |mut n: usize| { let mut k = 0; while n >= 6 { n /= 6; k += 1; } k as f64 };
    let (mut v4a, mut v4b, mut v5, mut v6) = (0u64, 0u64, 0u64, 0u64);
    let (mut w5, mut w6) = (0f64, 0f64); let mut last5 = 0usize;
    let eps = 1e-6;
    for n in 1..=LIM {
        let b = lf[n] - lf[n / 2] - lf[n / 3] - lf[n / 5] + lf[n / 30];
        if psi[n] - psi[n / 6] > b + eps { v4a += 1; }
        if b > psi[n] + eps { v4b += 1; }
        let e = 5.0 * ((n as f64).ln() + 1.0);
        let d = (b - a * n as f64).abs();
        if d > e { v5 += 1; last5 = n; }
        if d / e > w5 { w5 = d / e; }
        let ub = 1.2 * a * n as f64 + e * (ilog6(n) + 1.0);
        if psi[n] > ub + eps { v6 += 1; }
        if n >= 100 { let rr = (psi[n] - 1.2 * a * n as f64) / (e * (ilog6(n) + 1.0)); if rr > w6 { w6 = rr; } }
    }
    println!("C4 lower (psi(n)-psi(n/6) <= B(n)) violations: {}   C4 upper (B(n) <= psi(n)) violations: {}", v4a, v4b);
    println!("C5 |B(n)-A n| <= 5(ln n+1): violations {} (last at n={}), worst ratio {:.4}", v5, last5, w5);
    println!("C6 psi(n) <= 1.2 A n + 5(ln n+1)(ilog6 n+1): violations {}, worst slack ratio (n>=100) {:.4}", v6, w6);
    // C7 and counts
    let al = 0.91f64; // Lean-friendly lower bound for A
    let lb = |n: usize, aa: f64| -> f64 { let m = n + n / 2; 0.2 * aa * n as f64 - 5.0 * ((2.0 * n as f64).ln() + 1.0) - 5.0 * ((m as f64).ln() + 1.0) * (ilog6(m) + 1.0) };
    let ts = [7usize, 10, 19, 37, 61, 91, 127];
    let mut lastfail_exact = [0usize; 7]; let mut lastfail_lb = [0usize; 7]; let mut lastfail_pp = [0usize; 7];
    let mut v7 = 0u64; let mut v8 = 0u64;
    // sliding count of prime powers and primes in (N+N/2, 2N]
    let mut cpp = vec![0u32; LIM + 1]; let mut cpr = vec![0u32; LIM + 1];
    for n in 1..=LIM { cpp[n] = cpp[n - 1] + if lam[n] > 0.0 { 1 } else { 0 }; let isp = lam[n] > 0.0 && ((n as f64).ln() - lam[n]).abs() < 1e-12; cpr[n] = cpr[n - 1] + if isp { 1 } else { 0 }; }
    for n in 2..=(LIM / 2) {
        let m = n + n / 2;
        let w = psi[2 * n] - psi[m];
        if w + eps < lb(n, a) { v7 += 1; }
        let cnt = (cpp[2 * n] - cpp[m]) as f64; let cp = (cpr[2 * n] - cpr[m]) as usize;
        if cnt * (2.0 * n as f64).ln() + eps < w { v8 += 1; }
        let loss = ((n / 2).max(1) as f64).log2().floor();
        for (i, &t) in ts.iter().enumerate() {
            if cp < t { lastfail_exact[i] = n; }
            if cnt - loss < t as f64 { lastfail_pp[i] = n; }
            if lb(n, al) / (2.0 * n as f64).ln() < t as f64 + (n as f64).log2() { lastfail_lb[i] = n; }
        }
    }
    println!("C7 psi(2N)-psi(N+N/2) >= LB(N): violations {}   C8 count*ln(2N) >= window psi: violations {}", v7, v8);
    for (i, &t) in ts.iter().enumerate() {
        println!("T={:3}: last N with <T primes in (N+N/2,2N] = {}   | last N with (prime powers - floor(log2(N/2))) < T = {}   | last N (<= {}) where PROVABLE bound LB(N;A>=0.91)/ln(2N) < T+log2 N = {}", t, lastfail_exact[i], lastfail_pp[i], LIM / 2, lastfail_lb[i]);
    }
    // hypothesis shape "N >= N1 and c*T^2 <= N": check g(N) = LB/ln(2N) - log2 N - sqrt(N/c) > 0 on a geometric grid
    for &(n1, c) in &[(1.0e5f64, 67.0f64), (2.0e4, 67.0), (1.0e4, 100.0), (5.0e3, 150.0)] {
        let mut x = n1; let mut ming = f64::INFINITY; let mut argm = 0f64;
        while x < 1e40 { let m = 1.5 * x; let l6 = (m.ln() / 6f64.ln()).floor() + 1.0; let lbv = 0.2 * al * x - 5.0 * ((2.0 * x).ln() + 1.0) - 5.0 * (m.ln() + 1.0) * l6; let g = lbv / (2.0 * x).ln() - x.log2() - (x / c).sqrt(); if g < ming { ming = g; argm = x; } x *= 1.01; }
        println!("shape N>={:.0}, {}*T^2<=N : min over grid of [LB/ln(2N) - log2 N - sqrt(N/{})] = {:.2} at N={:.3e}", n1, c, c, ming, argm);
    }
}

fn wit() {
    println!("== witness-time enumeration: valid (D,a) iff for all x in [N]\\{{r}}: N*min(xa mod D, D - xa mod D) > D");
    let (mut tot_valid, mut tot_pred, mut v_not_p, mut p_not_v, mut naive3) = (0u64, 0u64, 0u64, 0u64, 0u64);
    let mut beyond2n = 0u64; let mut pairs = 0u64;
    for n in 10u64..=40 {
        for r in 1..=(n / 2) {
            pairs += 1;
            let mut line_max = 0u64; let mut cnt_b = 0u64;
            for d in (n + 1)..=(6 * n) {
                let mut valid = false;
                for a in 1..d {
                    let mut ok = true;
                    for x in 1..=n { if x == r { continue; } let y = (x * a) % d; let m = y.min(d - y); if n * m <= d { ok = false; break; } }
                    if ok { valid = true;
                        // naive m=3 claim: a*r == 1 mod d with d in (2N,3N)
                        if (a * r) % d == 1 && d > 2 * n { naive3 += 1; }
                        break; }
                }
                let mut pred = false;
                'o: for s in 1..=12u64 { for v in 1..=24u64 { if r * v >= d { break; } let t = d - r * v; if t % s != 0 { continue; } let u = t / s; if u >= n + 1 && gcd(u, r) == 1 && (s + v) * n > d && 2 * s * n > d { pred = true; break 'o; } } }
                if valid { tot_valid += 1; if d > 2 * n { cnt_b += 1; beyond2n += 1; } if d > line_max { line_max = d; } }
                if pred { tot_pred += 1; }
                if valid && !pred { v_not_p += 1; if v_not_p <= 12 { println!("  valid-not-predicted: N={} r={} D={}", n, r, d); } }
                if pred && !valid { p_not_v += 1; if p_not_v <= 12 { println!("  predicted-not-valid: N={} r={} D={}", n, r, d); } }
            }
            if 2 * r == n || (n % 2 == 1 && 2 * r + 1 == n) { println!("N={} r={} : valid D in (2N,6N]: {}  max valid D = {} ({:.2} N)", n, r, cnt_b, line_max, line_max as f64 / n as f64); }
        }
    }
    println!("(N,r) pairs={} valid D total={} (of which D>2N: {}) predicted total={} valid-not-predicted={} predicted-not-valid={}", pairs, tot_valid, beyond2n, tot_pred, v_not_p, p_not_v);
    println!("naive m=3 claim (a r = 1 mod D, D>2N valid): occurrences={}", naive3);
    // s=1 control: valid D in [N+1, 2N] must be exactly {D : D-r >= N+1, D <= 2N-1, gcd(D-r, r)=1}
    let mut ctl_bad = 0u64;
    for n in 10u64..=40 { for r in 1..=(n / 2) { for d in (n + 1)..=(2 * n) {
        let mut valid = false;
        for a in 1..d { let mut ok = true; for x in 1..=n { if x == r { continue; } let y = (x * a) % d; let m = y.min(d - y); if n * m <= d { ok = false; break; } } if ok { valid = true; break; } }
        let exp = d >= n + 1 + r && d <= 2 * n - 1 && gcd(d - r, r) == 1;
        if valid != exp { ctl_bad += 1; if ctl_bad <= 8 { println!("  s=1 control mismatch N={} r={} D={} valid={} expected={}", n, r, d, valid, exp); } }
    } } }
    println!("s=1 control (valid D<=2N  <=>  N+1+r<=D<=2N-1 and gcd(D,r)=1): mismatches={}", ctl_bad);
}

fn cheb30() {
    // multiples-of-30 form (the Lean-ready statements C5', C4', C6', C11 of the accompanying notes), f64 evidence
    const LIM: usize = 6_000_000;
    let mut lam = vec![0f64; LIM + 1];
    let mut comp = vec![false; LIM + 1];
    for p in 2..=LIM { if !comp[p] { let lp = (p as f64).ln(); let mut q = p; loop { lam[q] = lp; if q > LIM / p { break; } q *= p; } let mut j = p * p; while j <= LIM { comp[j] = true; j += p; } } }
    drop(comp);
    let mut psi = vec![0f64; LIM + 1]; let mut lf = vec![0f64; LIM + 1]; let mut cpp = vec![0u32; LIM + 1];
    for n in 1..=LIM { psi[n] = psi[n - 1] + lam[n]; lf[n] = lf[n - 1] + (n as f64).ln(); cpp[n] = cpp[n - 1] + if lam[n] > 0.0 { 1 } else { 0 }; }
    let a = 2f64.ln() / 2.0 + 3f64.ln() / 3.0 + 5f64.ln() / 5.0 - 30f64.ln() / 30.0;
    let clog6 = |m: usize| { let mut k = 0usize; let mut p = 1usize; while p < m { p *= 6; k += 1; } k as f64 };
    let (mut v5lo, mut v5up, mut v4lo, mut v4up, mut v6) = (0u64, 0u64, 0u64, 0u64, 0u64);
    let eps = 1e-6;
    for m in 1..=(LIM / 30) {
        let b = lf[30 * m] - lf[15 * m] - lf[10 * m] - lf[6 * m] + lf[m];
        let l = (30.0 * m as f64).ln();
        if b + eps < 30.0 * a * m as f64 - 3.0 * l - 3.0 { v5lo += 1; }
        if b > 30.0 * a * m as f64 + 2.0 * l + 2.0 + eps { v5up += 1; }
        if psi[30 * m] - psi[5 * m] > b + eps { v4lo += 1; }
        if b > psi[30 * m] + eps { v4up += 1; }
        if psi[30 * m] > 36.0 * a * m as f64 + (36.0 * a + 2.0 * l + 2.0) * clog6(m) + 100.0 + eps { v6 += 1; }
    }
    println!("C5' lower viol {} upper viol {} | C4' lower viol {} upper viol {} | C6' viol {}  (m <= {})", v5lo, v5up, v4lo, v4up, v6, LIM / 30);
    // C11: hypothesis H(N,T): 4*l*(T + 2*l + 50) + 1100 <= N with l = floor(log2 N) + 2.  Conclusion: T + floor(log2 N) + 1 <= #primepowers in (N+N/2, 2N].
    // check (i) the conclusion on exact counts for the maximal T allowed, (ii) the PROVABLE chain with A in [0.91,0.95].
    let (mut bad_exact, mut bad_chain) = (0u64, 0u64); let mut first_n = 0usize; let mut worst = f64::INFINITY;
    for n in 1200usize..=(LIM / 2) {
        let lg = (usize::BITS - 1 - n.leading_zeros()) as usize; let l = lg + 2;
        if 4 * l * (2 * l + 50) + 1100 > n { continue; }
        let tmax = (n - 1100) / (4 * l) - 2 * l - 50;
        if first_n == 0 { first_n = n; }
        let cnt = (cpp[2 * n] - cpp[n + n / 2]) as usize;
        if tmax + lg + 1 > cnt { bad_exact += 1; }
        let m1 = (2 * n) / 30; let m2 = (n + n / 2 + 29) / 30;
        let lo = 30.0 * 0.91 * m1 as f64 - 3.0 * (30.0 * m1 as f64).ln() - 3.0;
        let up = 36.0 * 0.91 * m2 as f64 + (36.0 * 0.91 + 2.0 * (30.0 * m2 as f64).ln() + 2.0) * clog6(m2) + 100.0; // coefficient of A is 30m1-36m2-36clog > 0 here, so A=0.91 is the worst case
        let up95 = 36.0 * 0.95 * m2 as f64 + (36.0 * 0.95 + 2.0 * (30.0 * m2 as f64).ln() + 2.0) * clog6(m2) + 100.0;
        let lo95 = 30.0 * 0.95 * m1 as f64 - 3.0 * (30.0 * m1 as f64).ln() - 3.0;
        let need = (tmax + lg + 1) as f64 * (2.0 * n as f64).ln();
        let s = (lo - up).min(lo95 - up95) - need;
        if s < 0.0 { bad_chain += 1; }
        if s / (n as f64) < worst { worst = s / n as f64; }
    }
    println!("C11: first N where hypothesis admits T>=0: {} ; exact-count violations {} ; provable-chain violations {} ; min slack/N {:.4}  (N <= {})", first_n, bad_exact, bad_chain, worst, LIM / 2);
    for &t in &[7usize, 19, 37, 61, 91, 127, 300, 1000] {
        let mut n0 = 0usize; for n in (1200usize..=(LIM / 2)).rev() { let lg = (usize::BITS - 1 - n.leading_zeros()) as usize; let l = lg + 2; if 4 * l * (t + 2 * l + 50) + 1100 > n { n0 = n + 1; break; } }
        println!("  hypothesis threshold N_A(T={}) = {}", t, n0);
    }
}

fn main() {
    let a: Vec<String> = env::args().collect();
    match a.get(1).map(|s| s.as_str()) { Some("b") => route_b(), Some("cheb") => cheb(), Some("wit") => wit(), Some("cheb30") => cheb30(), _ => eprintln!("usage: pw b|cheb|wit") }
}
