// mm2.rs: corrected upper bound for NON-coprime-free R (pairs with gcd 1 allowed).
// UBc = max(1/A, max_i tau*_i, max_{unblocked (i,j)} E_ij)
//   tau*_i = m_i/(m_i r_i + beta*_i), beta*_i = min over unit classes u mod r_i that contain a RETAINED x in [1,N] of (largest retained x in the class)
//   unblocked (i,j): class u = r_j mod r_i (r_j < r_i, gcd 1) has no retained representative in [1,N]
//   E_ij = max_{eta in [0,1/A]} min( ||m_i eta||, ||m_j (1 - r_j eta)/r_i|| )   (exact rational candidate enumeration)
// build: rustc -O -o bin/mm2 src/mm2.rs
use std::env;
type F = (i128, i128); // num/den, den>0, reduced
fn g128(a: i128, b: i128) -> i128 { let (mut a, mut b) = (a.abs(), b.abs()); while b != 0 { let t = a % b; a = b; b = t; } a }
fn nf(n: i128, d: i128) -> F { let (n, d) = if d < 0 { (-n, -d) } else { (n, d) }; let g = g128(n, d).max(1); (n / g, d / g) }
fn add(a: F, b: F) -> F { nf(a.0 * b.1 + b.0 * a.1, a.1 * b.1) }
fn sub(a: F, b: F) -> F { nf(a.0 * b.1 - b.0 * a.1, a.1 * b.1) }
fn mul(a: F, b: F) -> F { nf(a.0 * b.0, a.1 * b.1) }
fn div(a: F, b: F) -> F { nf(a.0 * b.1, a.1 * b.0) }
fn lt(a: F, b: F) -> bool { a.0 * b.1 < b.0 * a.1 }
fn le(a: F, b: F) -> bool { a.0 * b.1 <= b.0 * a.1 }
fn eqf(a: F, b: F) -> bool { a.0 * b.1 == b.0 * a.1 }
fn mxf(a: F, b: F) -> F { if lt(a, b) { b } else { a } }
fn mnf(a: F, b: F) -> F { if lt(a, b) { a } else { b } }
fn fl(a: F) -> i128 { a.0.div_euclid(a.1) }
fn dist(a: F) -> F { let f = sub(a, (fl(a), 1)); mnf(f, sub((1, 1), f)) } // ||a||
fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }
fn build(n: u64, rs: &[(u64, u64)]) -> Vec<u64> {
    let mut v: Vec<u64> = (1..=n).filter(|x| !rs.iter().any(|&(r, _)| r == *x)).collect();
    for &(r, m) in rs { v.push(m * r); }
    v.sort(); v.dedup(); v
}
fn ml_exact(v: &[u64]) -> F {
    let mut best: F = (0, 1);
    let mut ds: Vec<u64> = Vec::new();
    for i in 0..v.len() { for j in i..v.len() { ds.push(v[i] + v[j]); } }
    ds.sort(); ds.dedup();
    let mut vs = v.to_vec(); vs.sort();
    for &d in &ds { for p in 1..=(d / 2) {
        let mut cur: F = (1, 2); let mut ok = true;
        for &x in &vs { let y = (p * x) % d; let y = y.min(d - y); let f: F = (y as i128, d as i128);
            if !lt(best, f) { ok = false; break; } if lt(f, cur) { cur = f; } }
        if ok && lt(best, cur) { best = nf(cur.0, cur.1); }
    } }
    best
}
fn eij(n: u64, ri: u64, mi: u64, rj: u64, mj: u64) -> F {
    let aa: F = (1, (n + 1) as i128);
    let (ri_, mi_, rj_, mj_) = (ri as i128, mi as i128, rj as i128, mj as i128);
    let y0: F = (mj_, ri_); let kap: F = (mj_ * rj_, ri_);
    let f_ = |e: F| dist(mul((mi_, 1), e));
    let g_ = |e: F| dist(sub(y0, mul(kap, e)));
    let mut cands: Vec<F> = vec![(0, 1), aa];
    // breakpoints of f: m_i eta = n/2 ; of g: y0 - kap eta = n/2
    let n1max = (mi_ * 2) / ((n + 1) as i128) + 3;
    for k in 0..=n1max { cands.push(nf(k, 2 * mi_)); }
    let ylo = sub(y0, mul(kap, aa)); let (n2lo, n2hi) = (2 * fl(ylo) - 2, 2 * fl(y0) + 4);
    for k in n2lo..=n2hi { cands.push(div(sub(y0, (k, 2)), kap)); }
    // crossings: s1 (m_i e - n1) = s2 (y0 - kap e - n2)
    for n1 in 0..=(n1max / 2 + 2) { for n2 in (n2lo / 2 - 1)..=(n2hi / 2 + 1) { for &s1 in &[1i128, -1] { for &s2 in &[1i128, -1] {
        // s1*m_i e - s1*n1 = s2*y0 - s2*kap e - s2*n2  -> e (s1 m_i + s2 kap) = s2 y0 - s2 n2 + s1 n1
        let coef = add((s1 * mi_, 1), mul((s2, 1), kap)); if coef.0 == 0 { continue; }
        let rhs = add(sub(mul((s2, 1), y0), (s2 * n2, 1)), (s1 * n1, 1));
        cands.push(div(rhs, coef));
    } } } }
    let mut best: F = (0, 1);
    for c in cands { if lt(c, (0, 1)) || lt(aa, c) { continue; } let v = mnf(f_(c), g_(c)); best = mxf(best, v); }
    best
}
fn subsets(lo: u64, hi: u64, k: usize, cur: &mut Vec<u64>, out: &mut Vec<Vec<u64>>) {
    if cur.len() == k { out.push(cur.clone()); return; }
    let start = if let Some(&l) = cur.last() { l + 1 } else { lo };
    for x in start..=hi { cur.push(x); subsets(lo, hi, k, cur, out); cur.pop(); }
}
fn main() {
    let a: Vec<String> = env::args().collect();
    let n0: u64 = a[1].parse().unwrap(); let n1: u64 = a[2].parse().unwrap(); let k: usize = a[3].parse().unwrap(); let mmax: u64 = a[4].parse().unwrap(); let gm: u64 = a[5].parse().unwrap();
    // gm 0: at least one coprime pair; 2: all sets
    let mut gtot = [0u64; 8]; // blocked: sets, UBc viol, UBc eq ; unblocked: sets, viol, eq ; naive U viol (all) ; sets total
    for n in n0..=n1 {
        let lo = n / 2 + 1; let aa = n + 1;
        let mut subs = Vec::new(); subsets(lo, n, k, &mut Vec::new(), &mut subs);
        let mut c = [0u64; 8]; let mut shown = 0;
        for sub in subs {
            let mut cop = false; for i in 0..k { for j in i + 1..k { if gcd(sub[i], sub[j]) == 1 { cop = true; } } }
            if gm == 0 && !cop { continue; }
            let mut ms = vec![2u64; k];
            loop {
                let rs: Vec<(u64, u64)> = sub.iter().zip(ms.iter()).map(|(&r, &m)| (r, m)).collect();
                let v = build(n, &rs);
                let mut ub: F = (1, aa as i128); let mut naive: F = (1, aa as i128); let mut unbl = false;
                for &(r, m) in &rs {
                    // naive tau with true beta
                    let s = n + 1 - r; let mut b = s; while gcd(b, r) != 1 { b += 1; }
                    naive = mxf(naive, (m as i128, (m * r + b) as i128));
                    // beta*: min over unit classes u of largest retained rep
                    let mut bstar: Option<u64> = None;
                    for u in 1..r { if gcd(u, r) != 1 { continue; }
                        let mut x = u; let mut best_rep: Option<u64> = None;
                        while x <= n { if !rs.iter().any(|&(rr, _)| rr == x) { best_rep = Some(x); } x += r; }
                        match best_rep { Some(bx) => { bstar = Some(match bstar { Some(c0) => c0.min(bx), None => bx }); }
                                         None => { unbl = true; // the class is r_j mod r (r_j<r); find j
                                             for &(rj, mj) in &rs { if rj != r && rj % r == u && rj < r { let e = eij(n, r, m, rj, mj); ub = mxf(ub, e); } } } }
                    }
                    if let Some(b) = bstar { ub = mxf(ub, (m as i128, (m * r + b) as i128)); }
                }
                let mlv = ml_exact(&v);
                if lt(naive, mlv) { c[6] += 1; }
                let idx = if unbl { 3 } else { 0 };
                c[idx] += 1;
                if lt(ub, mlv) { c[idx + 1] += 1; if shown < 10 { println!("VIOL N={} rs={:?} ML={:?} UBc={:?} unbl={}", n, rs, mlv, ub, unbl); shown += 1; } }
                else if eqf(ub, mlv) { c[idx + 2] += 1; }
                c[7] += 1;
                let mut p = 0; loop { if p == k { break; } if ms[p] < mmax { ms[p] += 1; break; } else { ms[p] = 2; p += 1; } }
                if p == k { break; }
            }
        }
        for i in 0..8 { gtot[i] += c[i]; }
        println!("N={} total={} naiveU_viol={} | allblocked: sets={} UBc_viol={} UBc_eq={} | unblocked: sets={} UBc_viol={} UBc_eq={}", n, c[7], c[6], c[0], c[1], c[2], c[3], c[4], c[5]);
    }
    println!("TOTAL total={} naiveU_viol={} | allblocked: sets={} UBc_viol={} UBc_eq={} | unblocked: sets={} UBc_viol={} UBc_eq={}", gtot[7], gtot[6], gtot[0], gtot[1], gtot[2], gtot[3], gtot[4], gtot[5]);
}
