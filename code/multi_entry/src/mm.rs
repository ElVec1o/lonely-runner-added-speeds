// mm.rs: exact ML for V = ([1,N] \ R) u {m_i r_i}, R = {r_1..r_K} in (N/2, N].
// build: rustc -O -o bin/mm src/mm.rs
// units: N = number of speeds, A = N+1; fractions are (num,den) u64; ML via candidate times p/d, d in {v_i+v_j}, ALL p in 1..=d/2 (no coprimality restriction).
use std::env;
type F = (u128, u128); // num/den, not reduced
fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }
fn lt(a: F, b: F) -> bool { a.0 * b.1 < b.0 * a.1 }
fn eqf(a: F, b: F) -> bool { a.0 * b.1 == b.0 * a.1 }
fn mx(a: F, b: F) -> F { if lt(a, b) { b } else { a } }
fn mn(a: F, b: F) -> F { if lt(a, b) { a } else { b } }
fn inv(a: u64, m: u64) -> u64 { let (mut r0, mut r1, mut s0, mut s1) = (m as i64, (a % m) as i64, 0i64, 1i64);
    while r1 != 0 { let q = r0 / r1; let t = r0 - q * r1; r0 = r1; r1 = t; let t = s0 - q * s1; s0 = s1; s1 = t; }
    ((s0 % m as i64 + m as i64) % m as i64) as u64 }
fn val_at(v: &[u64], p: u64, d: u64) -> F { // min_v ||p v / d||
    let mut best = (1u128, 2u128);
    for &x in v { let y = (p * x) % d; let y = y.min(d - y); let f = (y as u128, d as u128); if lt(f, best) { best = f; } }
    best
}
fn ml_exact(v: &[u64], start: F) -> F {
    let mut best = start;
    let mut ds: Vec<u64> = Vec::new();
    for i in 0..v.len() { for j in i..v.len() { ds.push(v[i] + v[j]); } }
    ds.sort(); ds.dedup();
    let mut vs = v.to_vec(); vs.sort();
    for &d in &ds { for p in 1..=(d / 2) {
        let mut cur = (1u128, 2u128); let mut ok = true;
        for &x in &vs { let y = (p * x) % d; let y = y.min(d - y); let f = (y as u128, d as u128);
            if !lt(best, f) { ok = false; break; } if lt(f, cur) { cur = f; } }
        if ok && lt(best, cur) { best = cur; }
    } }
    best
}
fn beta(n: u64, r: u64) -> u64 { let s = n + 1 - r; let mut b = s; while gcd(b, r) != 1 { b += 1; }
    if std::env::var("NEGBETA").is_ok() { b += 1; while gcd(b, r) != 1 { b += 1; } } b }
fn build(n: u64, rs: &[(u64, u64)]) -> Vec<u64> {
    let mut v: Vec<u64> = (1..=n).filter(|x| !rs.iter().any(|&(r, _)| r == *x)).collect();
    for &(r, m) in rs { v.push(m * r); }
    v.sort(); v.dedup(); v
}
fn pairwise_gcd_gt1(rs: &[(u64, u64)]) -> bool { for i in 0..rs.len() { for j in i + 1..rs.len() { if gcd(rs[i].0, rs[j].0) == 1 { return false; } } } true }
fn fnorm(f: F) -> (u128, u128) { let g = gcd(f.0 as u64, f.1 as u64).max(1) as u128; (f.0 / g, f.1 / g) }

// subsets of size k from lo..=hi
fn subsets(cands: &[u64], k: usize, from: usize, cur: &mut Vec<u64>, out: &mut Vec<Vec<u64>>) {
    if cur.len() == k { out.push(cur.clone()); return; }
    for idx in from..cands.len() { cur.push(cands[idx]); subsets(cands, k, idx + 1, cur, out); cur.pop(); }
}
fn main() {
    let a: Vec<String> = env::args().collect();
    let mode = a[1].as_str();
    if mode == "selftest" {
        // known values
        let t = |v: &[u64], e: (u128, u128)| { let r = fnorm(ml_exact(v, (0, 1))); assert!(r == e, "selftest {:?} got {:?} want {:?}", v, r, e); };
        t(&[1], (1, 2)); t(&[1, 2], (1, 3)); t(&[1, 2, 3], (1, 4)); t(&[1, 3], (1, 2)); t(&[1, 2, 3, 4], (1, 5));
        for n in 1..=24u64 { let v: Vec<u64> = (1..=n).collect(); t(&v, (1, (n + 1) as u128)); }
        // Theorem V values (the accompanying code the accompanying notes section 8): (N,r,m) -> ML
        let tv = |n: u64, r: u64, m: u64, e: (u128, u128)| { let v = build(n, &[(r, m)]); let g = fnorm(ml_exact(&v, (0, 1))); assert!(g == e, "TV {} {} {} got {:?}", n, r, m, g); };
        tv(13, 12, 2, (1, 14)); tv(13, 12, 3, (3, 41)); tv(31, 30, 2, (1, 32)); tv(31, 30, 4, (4, 127)); tv(7, 6, 3, (3, 23)); tv(40, 40, 2, (2, 81));
        println!("selftest PASS"); return;
    }
    // scan N0 N1 K MMAX GMODE  (GMODE 1: pairwise gcd>1 ; 0: at least one coprime pair ; 2: all)
    let n0: u64 = a[2].parse().unwrap(); let n1: u64 = a[3].parse().unwrap(); let k: usize = a[4].parse().unwrap(); let mmax: u64 = a[5].parse().unwrap(); let gm: u64 = a[6].parse().unwrap();
    for n in n0..=n1 {
        let lo = match std::env::var("LOWR") { Ok(x) => x.parse::<u64>().unwrap(), Err(_) => n / 2 + 1 }; let aa = n + 1;
        let tightr = std::env::var("TIGHTR").is_ok();
        let cands: Vec<u64> = (lo..=n).filter(|&r| !tightr || beta(n, r) >= 2 * (n + 1 - r)).collect();
        let mut subs = Vec::new(); subsets(&cands, k, 0, &mut Vec::new(), &mut subs);
        let (mut tot, mut ub_viol, mut eq_u, mut lt_u, mut lbfail, mut wm_eq_ml, mut wm_lt_ml, mut crit_t, mut crit_f_eq, mut crit_f_lt, mut wcr_cnt) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
        let mut shown = 0; let (mut nt_tot, mut nt_eq, mut lrc_bad) = (0u64, 0u64, 0u64);
        for sub in subs {
            let base: Vec<(u64, u64)> = sub.iter().map(|&r| (r, 2)).collect();
            let g1 = pairwise_gcd_gt1(&base);
            if gm == 1 && !g1 { continue; } if gm == 0 && g1 { continue; }
            let mut ms = vec![2u64; k];
            loop {
                let rs: Vec<(u64, u64)> = sub.iter().zip(ms.iter()).map(|(&r, &m)| (r, m)).collect();
                let v = build(n, &rs);
                // U = max(1/A, tau_i)
                let mut u: F = (1, aa as u128);
                let mut taus: Vec<(F, u64, u64, u64)> = Vec::new(); // tau_i, D_i, a_i, beta_i
                for &(r, m) in &rs { let b = beta(n, r); let d = m * r + b; let t = (m as u128, d as u128); u = mx(u, t); let ai = (d - inv(r, d)) % d; taus.push((t, d, ai, b)); }
                // witness values
                let mut wmax: F = (0, 1);
                let cond0 = rs.iter().all(|&(r, m)| (m * (aa - r)) % aa != 0);
                let w0 = if cond0 { (1, aa as u128) } else { (0, 1) };
                // actual value at time 1/A
                let act0 = val_at(&v, 1, aa); assert!(eqf(act0, w0) || (!cond0 && act0.0 == 0), "time 1/A mismatch");
                wmax = mx(wmax, act0);
                let mut crit = cond0 && eqf(u, (1, aa as u128));
                for (idx, &(r, m)) in rs.iter().enumerate() {
                    let (t, d, ai, _b) = taus[idx];
                    let actv = val_at(&v, ai, d as u64);
                    // predicted LB_i = min(tau_i, min_{j!=i} ||w_j a_i / D_i||)
                    let mut pred = t;
                    for (jdx, &(r2, m2)) in rs.iter().enumerate() { if jdx == idx { continue; } let y = (ai * (m2 * r2)) % (d as u64); let y = y.min(d as u64 - y); pred = mn(pred, (y as u128, d as u128)); }
                    if !eqf(pred, actv) { lbfail += 1; if shown < 5 { println!("LBFAIL N={} rs={:?} i={} pred={:?} act={:?}", n, rs, idx, fnorm(pred), fnorm(actv)); shown += 1; } }
                    wmax = mx(wmax, actv);
                    if eqf(t, u) && eqf(pred, u) { crit = true; }
                }
                let _ = &taus;
                let mlv = ml_exact(&v, wmax);
                tot += 1;
                if lt(u, mlv) { ub_viol += 1; if shown < 12 && gm == 1 { println!("UBVIOL N={} rs={:?} ML={:?} U={:?}", n, rs, fnorm(mlv), fnorm(u)); shown += 1; } }
                else if eqf(u, mlv) { eq_u += 1; } else { lt_u += 1; }
                if eqf(wmax, mlv) { wm_eq_ml += 1; } else { wm_lt_ml += 1; }
                // criterion: crit <=> ML == U ?
                let eqml = eqf(u, mlv); if lt(mlv, (1, aa as u128)) { lrc_bad += 1; println!("BELOW-1/A N={} rs={:?} ML={:?}", n, rs, fnorm(mlv)); } if lt((1, aa as u128), u) { nt_tot += 1; if eqml { nt_eq += 1; } }
                if crit && eqml { crit_t += 1; } else if !crit && eqml { crit_f_eq += 1; if shown < 20 { println!("CRIT-NOT-NECESSARY N={} rs={:?} ML=U={:?}", n, rs, fnorm(u)); shown += 1; } } else if crit && !eqml { wcr_cnt += 1; println!("CRIT-NOT-SUFFICIENT N={} rs={:?}", n, rs); } else { crit_f_lt += 1; }
                // next m tuple
                let mut p = 0; loop { if p == k { break; } if ms[p] < mmax { ms[p] += 1; break; } else { ms[p] = 2; p += 1; } }
                if p == k { break; }
            }
        }
        println!("N={} K={} mmax={} gmode={} sets={} ML>U:{} ML=U:{} ML<U:{} | LBFAIL:{} | max-witness==ML:{} witness<ML:{} | crit&eq:{} !crit&eq:{} crit&!eq:{} !crit&!eq:{} | nontight(U>1/A): sets={} ML=U:{} | ML<1/A:{}", n, k, mmax, gm, tot, ub_viol, eq_u, lt_u, lbfail, wm_eq_ml, wm_lt_ml, crit_t, crit_f_eq, wcr_cnt, crit_f_lt, nt_tot, nt_eq, lrc_bad);
    }
}
