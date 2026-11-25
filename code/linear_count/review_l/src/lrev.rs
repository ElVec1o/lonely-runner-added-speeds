// lrev: independent exact engine for the review of THEOREM_L (own code, not L/src, not br.rs).
// Conventions: K=(2N-1)N^2, window J(D)=[a/D-1/K, a/D+1/K], a r = 1 mod D.
use std::env; use std::sync::atomic::{AtomicU64, Ordering}; static CAP: AtomicU64 = AtomicU64::new(3_000_000);
type I = i128;
fn gcd(a: i64, b: i64) -> i64 { if b == 0 { a.abs() } else { gcd(b, a % b) } }
fn inv(a: i64, m: i64) -> i64 {
    let (mut r0, mut r1, mut s0, mut s1) = (m, a % m, 0i64, 1i64);
    while r1 != 0 { let q = r0 / r1; let t = r0 - q * r1; r0 = r1; r1 = t; let t = s0 - q * s1; s0 = s1; s1 = t; }
    assert!(r0 == 1, "not invertible"); ((s0 % m) + m) % m
}
fn fdiv(a: I, b: I) -> I { let q = a / b; if a % b != 0 && ((a < 0) != (b < 0)) { q - 1 } else { q } }
#[derive(Clone, Copy)]
struct Dm { d: i64, a: i64 }
fn kk(n: i64) -> I { (2 * n as I - 1) * (n as I) * (n as I) }
fn dlist(n: i64, r: i64) -> Vec<Dm> {
    let mut v = vec![];
    for d in (n + 1 + r)..=(2 * n - 1) { if gcd(d, r) == 1 { v.push(Dm { d, a: inv(r % d, d) }); } }
    v
}
// exact overlap of Bad_w={||w t||<1/N} with J(D), scaled: returns (overlap, 2W, #arcs with positive overlap, rho)
fn cover(n: i64, dm: Dm, w: i64) -> (I, I, u32, i64) {
    let d = dm.d as I; let k = kk(n); let nn = n as I;
    let rho = (((w % dm.d) as I * dm.a as I) % d) as i64;
    let a_ = d * k; let b_ = nn * k; let c_ = d * nn * k; let ww = w as I * d * nn;
    let mut m = fdiv(rho as I * b_ - a_ - ww, c_) - 1;
    let (mut ov, mut cnt) = (0 as I, 0u32);
    loop {
        let lo = m * c_ - rho as I * b_ - a_; let hi = lo + 2 * a_;
        if lo >= ww { break; }
        let o = hi.min(ww) - lo.max(-ww);
        if o > 0 { ov += o; cnt += 1; }
        m += 1;
    }
    (ov, 2 * ww, cnt, rho)
}
// S+ cover: level theta=2/P (P=D*+1), window radius d*=theta/(N D*), D<=D*.
fn cover_sp(n: i64, ds: i64, dm: Dm, w: i64) -> (I, I, u32, i64) {
    let d = dm.d as I; let nn = n as I; let p = ds as I + 1; let dsi = ds as I;
    let rho = (((w % dm.d) as I * dm.a as I) % d) as i64;
    let unit = d * p * nn * dsi; // common scale
    let a_ = 2 * d * nn * dsi; let b_ = p * nn * dsi; let c_ = unit; let ww = 2 * w as I * d;
    let mut m = fdiv(rho as I * b_ - a_ - ww, c_) - 1; let (mut ov, mut cnt) = (0 as I, 0u32);
    loop { let lo = m * c_ - rho as I * b_ - a_; let hi = lo + 2 * a_; if lo >= ww { break; }
        let o = hi.min(ww) - lo.max(-ww); if o > 0 { ov += o; cnt += 1; } m += 1; }
    (ov, 2 * ww, cnt, rho)
}
fn omega_osc(n: i64, w: i64) -> bool { 2 * w as I >= (2 * n as I - 1) * n as I * (n as I - 2) } // oscillating iff 2w >= (2N-1)N(N-2)
fn gfun(x: f64, rho: f64) -> f64 { let lo = (x - rho).max(-1.0); let hi = (x + rho).min(1.0); (hi - lo).max(0.0) / 2.0 }
// max weight pairwise coprime subset (weights f64). returns (best, nodes_exceeded)
fn max_cop(items: &Vec<(i64, f64)>) -> (f64, bool) {
    let mut it = items.clone(); it.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
    let n = it.len(); let mut suf = vec![0.0; n + 1];
    for i in (0..n).rev() { suf[i] = suf[i + 1] + it[i].1; }
    let mut best = 0.0; let mut nodes = 0u64; let mut ch: Vec<i64> = vec![];
    fn rec(i: usize, cur: f64, it: &Vec<(i64, f64)>, suf: &Vec<f64>, ch: &mut Vec<i64>, best: &mut f64, nodes: &mut u64) {
        *nodes += 1; if *nodes > CAP.load(Ordering::Relaxed) { return; }
        if cur > *best { *best = cur; }
        if i >= it.len() || cur + suf[i] <= *best + 1e-12 { return; }
        if ch.iter().all(|&c| gcd(c, it[i].0) == 1) { ch.push(it[i].0); rec(i + 1, cur + it[i].1, it, suf, ch, best, nodes); ch.pop(); }
        rec(i + 1, cur, it, suf, ch, best, nodes);
    }
    rec(0, 0.0, &it, &suf, &mut ch, &mut best, &mut nodes);
    (best, nodes > CAP.load(Ordering::Relaxed))
}
#[derive(Default)]
struct St { cases: u64, v_arc: u64, v_div: u64, v_ebound: u64, v_ebound2: u64, v_cov: u64, v_gam: u64, v_grp: u64, v_sum8: u64, v_sum18: u64, v_osc: u64, v_zero: u64,
    max_all: f64, max_cop: f64, max_cop_at: (i64, i64, i64), maxpos: usize, maxosc: f64, unres: u64, nonosc: u64, osc: u64, zero_cases: u64, l12_viol: u64, l12_checked: u64 }
fn check_lemma12(n: i64, r: i64, dl: &Vec<Dm>, s: &mut St) {
    let k = kk(n);
    for dm in dl {
        s.l12_checked += 1;
        let d = dm.d;
        for x in 1..=n { if x == r { continue; }
            let y = ((x as I * dm.a as I) % d as I) as i64;
            if y < 2 || y > d - 2 { s.l12_viol += 1; } }
        // margin 2/D - N/K - 1/N >= 0  <=> 2NK - N^2 D - D K >= 0
        let nn = n as I;
        if 2 * nn * k - nn * nn * d as I - d as I * k < 0 { s.l12_viol += 1; }
    }
}
fn check_w(n: i64, r: i64, dl: &Vec<Dm>, w: i64, s: &mut St) {
    s.cases += 1;
    let k = kk(n); let nn = n as I; let osc = omega_osc(n, w);
    let q = w as f64 / (n as f64 * n as f64);
    let mut pos: Vec<(i64, f64)> = vec![]; let mut es: Vec<(i64, i64)> = vec![]; let mut sall = 0.0;
    if osc { s.osc += 1 } else { s.nonosc += 1 }
    for dm in dl {
        let (ov, tw, cnt, rho) = cover(n, *dm, w);
        if osc { if ov * nn > 7 * tw { s.v_osc += 1; } let c = ov as f64 / tw as f64 * n as f64; if c > s.maxosc { s.maxosc = c; } continue; }
        if cnt > 1 { s.v_arc += 1; }
        if ov > 0 {
            let d = dm.d;
            // centred residue
            let e: i64 = if 2 * rho < d { rho } else { rho - d };
            if 2 * rho == d { s.v_arc += 1; }
            if ((w as I - e as I * r as I) % d as I) != 0 { s.v_div += 1; }
            let ea = (e as I).abs();
            if !(ea * nn * nn < w as I + 2 * nn * nn - nn) { s.v_ebound += 1; }
            if !(ea * k * nn < d as I * (w as I * nn + k)) { s.v_ebound2 += 1; }
            // cov <= min(1, K/(N w)):  ov*N*w <= tw*K
            if ov * nn * (w as I) > tw * k { s.v_cov += 1; }
            let cov = ov as f64 / tw as f64;
            let gam = gfun(ea as f64 / q, 2.0 / q);
            if cov > gam + 1e-9 { s.v_gam += 1; }
            pos.push((d, cov)); es.push((d, e)); sall += cov;
            if 2 * r == w && d != 2 * n - 1 { s.v_zero += 1; }
            if 2 * r == w && cov >= 0.5 { s.v_zero += 1; }
        }
    }
    if osc { return; }
    if 2 * r == w { s.zero_cases += 1; }
    if pos.len() > s.maxpos { s.maxpos = pos.len(); }
    if sall > s.max_all { s.max_all = sall; }
    // group check: within each e (with w - e r != 0) at most 2 pairwise coprime moduli
    if pos.len() >= 3 {
        for i in 0..es.len() { for j in i + 1..es.len() { if es[i].1 != es[j].1 || gcd(es[i].0, es[j].0) != 1 { continue; }
            for l in j + 1..es.len() { if es[l].1 == es[i].1 && gcd(es[i].0, es[l].0) == 1 && gcd(es[j].0, es[l].0) == 1 && (w as I - es[i].1 as I * r as I) != 0 { s.v_grp += 1; } } } }
    }
    if sall > 3.5 {
        let (b, ex) = max_cop(&pos); if ex { s.unres += 1; }
        if b > s.max_cop { s.max_cop = b; s.max_cop_at = (n, r, w); }
        if b > 8.0 + 1e-9 { s.v_sum8 += 1; } if b > 18.0 { s.v_sum18 += 1; }
    }
}
fn pr_st(tag: &str, s: &St) {
    println!("{} cases={} nonosc={} osc={} zero_w=2r={} | viol: arc={} div={} ebound={} ebound2={} cov={} gamma={} group={} sum8={} sum18={} osc7={} zero={} lemma12={} (of {} D-checks) | max_all={:.4} max_coprime_total={:.4} at {:?} maxpos={} maxosc*N={:.3} unres={}",
        tag, s.cases, s.nonosc, s.osc, s.zero_cases, s.v_arc, s.v_div, s.v_ebound, s.v_ebound2, s.v_cov, s.v_gam, s.v_grp, s.v_sum8, s.v_sum18, s.v_osc, s.v_zero, s.l12_viol, s.l12_checked, s.max_all, s.max_cop, s.max_cop_at, s.maxpos, s.maxosc, s.unres);
}
fn brute_ge(vs: &[i64], num: i64, den: i64) -> bool {
    // exists t with ||v t|| >= num/den for all v : candidates t=(m*den +- num)/(v*den)
    for &v in vs { let q = v as I * den as I;
        for m in 0..=v as I { for sg in [-1i128, 1] {
            let p = m * den as I + sg * num as I; let p = ((p % q) + q) % q;
            if vs.iter().all(|&u| { let x = (u as I * p) % q; let x = x.min(q - x); x * den as I >= num as I * q }) { return true; } } } }
    false
}
fn rng(s: &mut u64) -> u64 { *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17; *s }
fn dead_union(n: i64, dm: Dm, ws: &[i64]) -> bool {
    // is J(D) covered by the union of the open arcs {||w t||<1/N}, w in ws ?  exact rationals (num,den)
    let k = kk(n); let d = dm.d as I; let nn = n as I;
    let mut arcs: Vec<((I, I), (I, I))> = vec![];
    for &w in ws {
        let rho = (((w % dm.d) as I * dm.a as I) % d) as I; let den = d * nn * w as I;
        let mut m = fdiv(rho * nn - d - den / k, d * nn) - 2;
        loop {
            let lo = (m * d * nn - rho * nn - d, den); let hi = (m * d * nn - rho * nn + d, den);
            if lo.0 * k >= lo.1 { break; }
            if hi.0 * k > -hi.1 { arcs.push((lo, hi)); }
            m += 1;
        }
    }
    let lt = |x: (I, I), y: (I, I)| x.0 * y.1 < y.0 * x.1;
    let mut p: (I, I) = (-1, k); let end: (I, I) = (1, k);
    loop {
        let mut best: Option<(I, I)> = None;
        for a in &arcs { if lt(a.0, p) && lt(p, a.1) { if best.map_or(true, |b| lt(b, a.1)) { best = Some(a.1); } } }
        match best { None => return false, Some(h) => { p = h; if lt(end, p) { return true; } } }
    }
}
fn main() {
    let a: Vec<String> = env::args().collect();
    match a[1].as_str() {
        "lem" => { // lem N0 N1 wmult : all r in 1..=N-2, all w in (N, wmult N^3]
            let (n0, n1, wm): (i64, i64, i64) = (a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap());
            let mut tot = St::default();
            for n in n0..=n1 { let mut s = St::default();
                for r in 1..=(n - 2) { let dl = dlist(n, r); if dl.is_empty() { continue; } check_lemma12(n, r, &dl, &mut s);
                    for w in (n + 1)..=(wm * n * n * n) { check_w(n, r, &dl, w, &mut s); } }
                pr_st(&format!("N={}", n), &s);
                tot.cases += s.cases; tot.v_arc += s.v_arc; tot.v_div += s.v_div; tot.v_ebound += s.v_ebound; tot.v_ebound2 += s.v_ebound2; tot.v_cov += s.v_cov; tot.v_gam += s.v_gam; tot.v_grp += s.v_grp; tot.v_sum8 += s.v_sum8; tot.v_sum18 += s.v_sum18; tot.v_osc += s.v_osc; tot.v_zero += s.v_zero; tot.l12_viol += s.l12_viol; tot.l12_checked += s.l12_checked; tot.zero_cases += s.zero_cases; tot.nonosc += s.nonosc; tot.osc += s.osc; tot.unres += s.unres;
                if s.max_all > tot.max_all { tot.max_all = s.max_all } if s.max_cop > tot.max_cop { tot.max_cop = s.max_cop; tot.max_cop_at = s.max_cop_at } if s.maxpos > tot.maxpos { tot.maxpos = s.maxpos } if s.maxosc > tot.maxosc { tot.maxosc = s.maxosc }
            }
            pr_st("TOTAL", &tot);
        }
        "big" => { // big N r count seed : structured/random large w, all D, same lemma checks
            let (n, r, cnt, mut seed): (i64, i64, usize, u64) = (a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap(), a[5].parse().unwrap());
            let dl = dlist(n, r); let mut s = St::default(); check_lemma12(n, r, &dl, &mut s);
            let wmax: i64 = 1_000_000_000; let ds: Vec<i64> = dl.iter().map(|x| x.d).collect();
            for _ in 0..cnt {
                let mode = rng(&mut seed) % 5;
                let pick = |sd: &mut u64| ds[(rng(sd) % ds.len() as u64) as usize];
                let w: i64 = match mode {
                    0 => { let e = (rng(&mut seed) % 5) as i64 - 2; let (d1, d2) = (pick(&mut seed), pick(&mut seed)); if gcd(d1, d2) != 1 { continue; } let m = 1 + (rng(&mut seed) % 40) as i64; d1 * d2 * m + e * r }
                    1 => { // CRT lift of 3 moduli with offsets e_i r, smallest positive
                        let mut cs = vec![]; for _ in 0..3 { let d = pick(&mut seed); if cs.iter().any(|&(x, _)| gcd(x, d) != 1) { continue; } cs.push((d, (rng(&mut seed) % 7) as i64 - 3)); }
                        let (mut x, mut m) = (0i64, 1i64);
                        for &(d, e) in &cs { let target = ((e * r) % d + d) % d; let mut t = x; while t % d != target { t += m; if t > 4 * wmax { break; } } x = t; m *= d; if m > 4 * wmax { break; } }
                        x }
                    2 => { let d = pick(&mut seed); d * (1 + (rng(&mut seed) % 3000) as i64) + ((rng(&mut seed) % 5) as i64 - 2) * r }
                    3 => { let u = (rng(&mut seed) % 1_000_000) as f64 / 1e6; ((n as f64).powf(1.0 + u * 5.0)) as i64 }
                    _ => { n + 1 + (rng(&mut seed) % (4 * n as u64 * n as u64)) as i64 }
                };
                if w <= n || w > wmax { continue; }
                check_w(n, r, &dl, w, &mut s);
            }
            pr_st(&format!("big N={} r={}", n, r), &s);
        }
        "k1" => { // theorem-level k=1: N0..N1, all r<=N/2 (or all r with flag), all w in (N,3N^3]: exists alive D? exact certificate; fallback count
            let (n0, n1): (i64, i64) = (a[2].parse().unwrap(), a[3].parse().unwrap());
            let wm: i64 = a[4].parse().unwrap(); let rall = a.len() > 5;
            for n in n0..=n1 { let (mut cases, mut fallback, mut maxtried) = (0u64, 0u64, 0usize);
                let rmax = if rall { n - 2 } else { n / 2 };
                for r in 1..=rmax { let dl = dlist(n, r); if dl.is_empty() { continue; }
                    let k = kk(n); let nn = n as I;
                    let mut ok_l12 = St::default(); check_lemma12(n, r, &dl, &mut ok_l12); assert!(ok_l12.l12_viol == 0);
                    for w in (n + 1)..=(wm * n * n * n) { cases += 1; let mut tried = 0usize; let mut alive = false;
                        for dm in &dl { tried += 1; let d = dm.d as I;
                            let rho = (((w % dm.d) as I * dm.a as I) % d) as I; // J inside one arc  <=> ||w a/D|| < 1/N - w/K
                            let dist = rho.min(d - rho);
                            // dist/D < 1/N - w/K  <=> dist*N*K < D*(K - w N)   (K - wN may be <=0)
                            let covered = (k - w as I * nn) > 0 && dist * nn * k < d * (k - w as I * nn);
                            if !covered { alive = true; break; } }
                        if tried > maxtried { maxtried = tried; }
                        if !alive { fallback += 1; println!("FALLBACK n={} r={} w={}", n, r, w); } } }
                println!("k1 N={} rmax={} cases={} fallback(all windows covered)={} max_windows_tried={}", n, rmax, cases, fallback, maxtried); }
        }
        "dead1" => { // dead1 N0 N1 rall wmax_mult : single speed, max pairwise coprime dead set over all w<=wmax_mult*N^2 (dead requires w<K/N)
            let (n0, n1, wm): (i64, i64, i64) = (a[2].parse().unwrap(), a[3].parse().unwrap(), a[5].parse().unwrap()); let rall = a[4] == "all";
            for n in n0..=n1 { let mut best = 0usize; let mut at = (0, 0); let mut hist = vec![0u64; 12]; let k = kk(n); let nn = n as I;
                let rmax = if rall { n - 2 } else { n / 2 };
                for r in 1..=rmax { let dl = dlist(n, r); if dl.is_empty() { continue; }
                    for w in (n + 1)..=(wm * n * n) {
                        if (k - w as I * nn) <= 0 { break; } // beyond K/N no single arc contains a window
                        let mut dead: Vec<(i64, f64)> = vec![];
                        for dm in &dl { let d = dm.d as I; let rho = (((w % dm.d) as I * dm.a as I) % d) as I; let dist = rho.min(d - rho);
                            if dist * nn * k < d * (k - w as I * nn) { dead.push((dm.d, 1.0)); } }
                        if dead.is_empty() { continue; }
                        let (b, _) = max_cop(&dead); let c = b as usize; if c < hist.len() { hist[c] += 1; }
                        if c > best { best = c; at = (r, w); } } }
                println!("dead1 N={} max_coprime_dead_single_speed={} at(r,w)={:?} hist={:?}", n, best, at, hist); }
        }
        "adv" => { // adv N r k M : pool all w in (N,4N^2], top M by total coverage, exact union dead sets; k=2 pairs / k=3 greedy on top pairs
            let (n, r, kq, mm): (i64, i64, usize, usize) = (a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap(), a[5].parse().unwrap());
            let dl = dlist(n, r); let nd = dl.len(); let wmax = 4 * n * n;
            let mut pool: Vec<(f64, i64)> = vec![]; // (total coverage, w)
            for w in (n + 1)..=wmax { let mut t = 0.0; for dm in &dl { let (ov, tw, _, _) = cover(n, *dm, w); t += ov as f64 / tw as f64; } pool.push((t, w)); }
            pool.sort_by(|x, y| y.0.partial_cmp(&x.0).unwrap()); pool.truncate(mm);
            let cv: Vec<Vec<f32>> = pool.iter().map(|&(_, w)| dl.iter().map(|dm| { let (ov, tw, _, _) = cover(n, *dm, w); (ov as f64 / tw as f64) as f32 }).collect()).collect();
            let ws: Vec<i64> = pool.iter().map(|x| x.1).collect();
            let deadset = |idx: &[usize]| -> usize { // exact: D dead under speeds idx ; return max pairwise-coprime dead family size
                let mut dead: Vec<(i64, f64)> = vec![];
                for (j, dm) in dl.iter().enumerate() { let s: f32 = idx.iter().map(|&i| cv[i][j]).sum(); if s < 1.0 - 1e-5 { continue; }
                    let wl: Vec<i64> = idx.iter().map(|&i| ws[i]).collect(); if dead_union(n, *dm, &wl) { dead.push((dm.d, 1.0)); } }
                max_cop(&dead).0 as usize };
            let mut best1 = 0; let mut b1w = 0; for i in 0..ws.len() { let c = deadset(&[i]); if c > best1 { best1 = c; b1w = ws[i]; } }
            println!("adv N={} r={} nD={} pool={} top_total_cov={:.3}  k=1 best coprime-dead={} (w={})", n, r, nd, pool.len(), pool[0].0, best1, b1w);
            if kq >= 2 {
                let mut best2 = 0; let mut b2 = (0, 0); let mut pairs: Vec<(usize, usize, usize)> = vec![];
                for i in 0..ws.len() { for j in i + 1..ws.len() {
                    let mut ok = false; for d in 0..nd { if cv[i][d] + cv[j][d] >= 1.0 - 1e-5 { ok = true; break; } } if !ok { continue; }
                    let c = deadset(&[i, j]); if c > 0 { pairs.push((c, i, j)); } if c > best2 { best2 = c; b2 = (ws[i], ws[j]); } } }
                println!("adv N={} r={} k=2 best coprime-dead={} (W={:?}) [bound 2k={} floor, proof 8k={}, L* 9k={}]", n, r, best2, b2, 4, 16, 18);
                if kq >= 3 { pairs.sort_by(|x, y| y.0.cmp(&x.0)); pairs.truncate(40); let mut best3 = 0; let mut b3 = (0, 0, 0);
                    for &(_, i, j) in &pairs { for l in 0..ws.len() { if l == i || l == j { continue; } let c = deadset(&[i, j, l]); if c > best3 { best3 = c; b3 = (ws[i], ws[j], ws[l]); } } }
                    println!("adv N={} r={} k=3 best coprime-dead={} (W={:?}) [2k=6 floor, 8k=24, 9k=27] (beam over top-40 pairs x pool)", n, r, best3, b3); }
            }
        }
        "lemq" => { // lemq N0 N1 rstep wm2 : w in (N, wm2*N^2], r in 1..=N-2 step rstep
            let (n0, n1, rs, wm): (i64, i64, i64, i64) = (a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap(), a[5].parse().unwrap());
            for n in n0..=n1 { let mut s = St::default(); let mut r = 1; while r <= n - 2 { let dl = dlist(n, r); if !dl.is_empty() { check_lemma12(n, r, &dl, &mut s);
                    for w in (n + 1)..=(wm * n * n) { check_w(n, r, &dl, w, &mut s); } } r += rs; }
                pr_st(&format!("lemq N={} rstep={}", n, rs), &s); }
        }
        "bigsw" => { // bigsw N r : sweep w in [Omega-5N^2, Omega+5N^2] (regime boundary) plus multiples-of-D neighbourhoods
            let (n, r): (i64, i64) = (a[2].parse().unwrap(), a[3].parse().unwrap()); let dl = dlist(n, r); let mut s = St::default();
            let om = ((2 * n - 1) * n * (n - 2)) / 2; for w in (om - 5 * n * n)..=(om + 5 * n * n) { check_w(n, r, &dl, w, &mut s); }
            pr_st(&format!("bigsw boundary N={} r={} Omega={}", n, r, om), &s);
        }
        "splus" => { // splus N0 N1 wmult : for each r with >=6 window moduli, D* in {6th smallest, 12th, max} (of those coprime to r); F = all moduli <= D*
            let (n0, n1, wm): (i64, i64, i64) = (a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap());
            let (mut cases, mut vret, mut varc, mut vdiv, mut veb, mut vgam, mut vsum, mut vosc, mut vzero, mut vgrp) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
            let (mut maxcop, mut maxosc, mut maxall) = (0.0f64, 0.0f64, 0.0f64);
            for n in n0..=n1 { for r in 1..=(n - 2) { let full = dlist(n, r); if full.len() < 6 { continue; }
                let mut dstars = vec![full[5].d]; if full.len() > 12 { dstars.push(full[11].d); } dstars.push(full[full.len() - 1].d);
                for &ds in &dstars { let dl: Vec<Dm> = full.iter().cloned().filter(|x| x.d <= ds).collect(); let p = ds as I + 1; let nn = n as I;
                    // retained speeds: ||x a/D||>=2/D and 2/D - N d* >= theta  <=> (exact) 2 N Dstar - N^2 D... check: 2/D - 2N/(P N D*) >= 2/P  <=> 2/D >= 2/P + 2/(P D*) = 2(D*+1)/(P D*) = 2/D*  <=> D<=D*
                    for dm in &dl { for x in 1..=n { if x == r { continue; } let y = ((x as I * dm.a as I) % dm.d as I) as i64; if y < 2 || y > dm.d - 2 { vret += 1; } } if dm.d > ds { vret += 1; } }
                    for w in (n + 1)..=(wm * n * n * n) { cases += 1;
                        let osc = !((4 * (w as I)) < nn * (ds as I) * (p - 4));
                        let qp = 2.0 * w as f64 / (n as f64 * p as f64);
                        let mut pos: Vec<(i64, f64)> = vec![]; let mut es: Vec<(i64, i64)> = vec![]; let mut sall = 0.0;
                        for dm in &dl { let (ov, tw, cnt, rho) = cover_sp(n, ds, *dm, w); let cov = ov as f64 / tw as f64;
                            if osc { let c = cov * p as f64; if c > maxosc { maxosc = c; } if c > 12.31 { vosc += 1; } continue; }
                            if cnt > 1 { varc += 1; }
                            if ov > 0 { let d = dm.d; let e: i64 = if 2 * rho < d { rho } else { rho - d };
                                if ((w as I - e as I * r as I) % d as I) != 0 { vdiv += 1; }
                                if !((e as f64).abs() < qp + 2.0) { veb += 1; }
                                let gam = gfun((e as f64).abs() / qp, 2.0 / qp); if cov > gam + 1e-9 { vgam += 1; }
                                if 2 * r == w && (d != ds || cov >= 0.5) { vzero += 1; }
                                pos.push((d, cov)); es.push((d, e)); sall += cov; } }
                        if osc { continue; }
                        if sall > maxall { maxall = sall; }
                        if pos.len() >= 3 { for i in 0..es.len() { for j in i + 1..es.len() { if es[i].1 != es[j].1 || gcd(es[i].0, es[j].0) != 1 { continue; }
                            for l in j + 1..es.len() { if es[l].1 == es[i].1 && gcd(es[i].0, es[l].0) == 1 && gcd(es[j].0, es[l].0) == 1 && (w as I - es[i].1 as I * r as I) != 0 { vgrp += 1; } } } } }
                        if sall > 3.5 { let (b, _) = max_cop(&pos); if b > maxcop { maxcop = b; } if b > 8.0 + 1e-9 { vsum += 1; } } } } } }
            println!("splus N={}..{} cases={} viol: retained/margin={} arc={} div={} ebound={} gamma={} group={} sum8={} osc12.31={} zero={} | max_all={:.3} max_coprime_total={:.3} max_osc_cov*(D*+1)={:.3}", n0, n1, cases, vret, varc, vdiv, veb, vgam, vgrp, vsum, vosc, vzero, maxall, maxcop, maxosc);
        }
        "climb" => { // climb N r restarts steps seed : hill-climb w (non-oscillating) to maximise exact max pairwise-coprime total sum cov ; also runs the lemma checks on every visited w
            let (n, r, rst, steps, mut seed): (i64, i64, usize, usize, u64) = (a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap(), a[5].parse().unwrap(), a[6].parse().unwrap());
            CAP.store(40_000, Ordering::Relaxed); let dl = dlist(n, r); let om = ((2 * n - 1) * n * (n - 2)) / 2; let ds: Vec<i64> = dl.iter().map(|x| x.d).collect(); let mut s = St::default(); let mut gbest = 0.0f64; let mut gw = 0i64;
            let obj = |w: i64| -> f64 { let mut pos = vec![]; let mut tot = 0.0; for dm in &dl { let (ov, tw, _, _) = cover(n, *dm, w); if ov > 0 { let c = ov as f64 / tw as f64; pos.push((dm.d, c)); tot += c; } } if tot < 2.0 { return tot * 0.3; } max_cop(&pos).0 };
            for _ in 0..rst { let lo = n * n; let mut w = lo + (rng(&mut seed) % (om as u64 - lo as u64)) as i64; if rng(&mut seed) % 2 == 0 { w = n * n + (rng(&mut seed) % (8 * n as u64 * n as u64)) as i64; } let mut cur = obj(w);
                for _ in 0..steps { let mv = rng(&mut seed) % 4; let mut w2 = w;
                    match mv { 0 => { w2 += (rng(&mut seed) % 41) as i64 - 20; } 1 => { let d = ds[(rng(&mut seed) % ds.len() as u64) as usize]; w2 += d * ((rng(&mut seed) % 7) as i64 - 3); } 2 => { let d = ds[(rng(&mut seed) % ds.len() as u64) as usize]; let e = (rng(&mut seed) % 9) as i64 - 4; w2 = ((w2 / d) * d + e * r).max(n + 1); } _ => { let d1 = ds[(rng(&mut seed) % ds.len() as u64) as usize]; let d2 = ds[(rng(&mut seed) % ds.len() as u64) as usize]; w2 += d1 * d2 * ((rng(&mut seed) % 3) as i64 - 1); } }
                    if w2 <= n || w2 >= om { continue; }
                    let o2 = obj(w2); check_w(n, r, &dl, w2, &mut s); if o2 >= cur { cur = o2; w = w2; if cur > gbest { gbest = cur; gw = w; } } } }
            pr_st(&format!("climb N={} r={} restarts={} steps={} best_obj={:.4} at w={}", n, r, rst, steps, gbest, gw), &s);
        }
        "ctl" => { // controls
            // C1: cover() vs brute grid on random cases
            let mut seed = 88172645463325252u64; let mut maxdiff = 0.0f64;
            for _ in 0..3000 { let n = 14 + (rng(&mut seed) % 40) as i64; let r = 1 + (rng(&mut seed) % (n as u64 - 2)) as i64; let dl = dlist(n, r); if dl.is_empty() { continue; }
                let dm = dl[(rng(&mut seed) % dl.len() as u64) as usize]; let w = n + 1 + (rng(&mut seed) % (6 * n as u64 * n as u64)) as i64;
                let (ov, tw, _, _) = cover(n, dm, w); let ex = ov as f64 / tw as f64;
                let g = 4001; let mut bad = 0; let k = kk(n);
                for i in 0..g { // t = a/D + s, s in [-1/K,1/K]: exact integer test ||w t||<1/N with common denominator D*K*(g-1)
                    let sn: I = -(g as I - 1) + 2 * i as I; let den = dm.d as I * k * (g as I - 1);
                    let num = w as I * (dm.a as I * k * (g as I - 1) + sn * dm.d as I) ; let q = den; let x = ((num % q) + q) % q; let x = x.min(q - x);
                    if x * (n as I) < q { bad += 1; } }
                let est = bad as f64 / g as f64; let diff = (est - ex).abs(); if diff > maxdiff { maxdiff = diff; } }
            println!("ctl1 cover() vs exact-grid: max abs diff {:.5} (grid resolution 2.5e-4 per arc edge)", maxdiff);
            // C2: planted exact ML decisions
            let mut v13: Vec<i64> = (1..=13).filter(|&x| x != 6).collect(); v13.push(69);
            let mut v20: Vec<i64> = (1..=20).filter(|&x| x != 6).collect(); v20.push(29); v20.push(31);
            let mut v21: Vec<i64> = (1..=21).filter(|&x| x != 6).collect(); v21.push(29); v21.push(31);
            let mut v29: Vec<i64> = (1..=29).filter(|&x| x != 12).collect(); v29.extend([31, 94, 98]);
            let base13: Vec<i64> = (1..=13).filter(|&x| x != 6).collect();
            println!("ctl2 [13]-6+69: ge(1/13)={} ge(3/40)={} ge(4/53)={}  (expect false,true,false)", brute_ge(&v13, 1, 13), brute_ge(&v13, 3, 40), brute_ge(&v13, 4, 53));
            println!("ctl2 [20]-6+29,31: ge(1/20)={} ge(2/41)={} ge(3/61)={} (expect false,true,false); [21]-6+29,31: ge(1/21)={} (expect true)", brute_ge(&v20, 1, 20), brute_ge(&v20, 2, 41), brute_ge(&v20, 3, 61), brute_ge(&v21, 1, 21));
            println!("ctl2 [29]-12+31,94,98: ge(1/29)={} (expect false); [13]-6: ge(1/13)={} (expect true)", brute_ge(&v29, 1, 29), brute_ge(&base13, 1, 13));
            // C3: dead windows of the planted failures via dead_union
            for (n, r, w) in [(13i64, 6i64, vec![69i64]), (20, 6, vec![29, 31]), (21, 6, vec![29, 31]), (29, 12, vec![31, 94, 98])] {
                let dl = dlist(n, r); let dead: Vec<i64> = dl.iter().filter(|dm| dead_union(n, **dm, &w)).map(|x| x.d).collect();
                let items: Vec<(i64, f64)> = dead.iter().map(|&d| (d, 1.0)).collect();
                println!("ctl3 N={} r={} W={:?}: window moduli {:?}, dead {:?}, max pairwise-coprime dead = {}", n, r, w, dl.iter().map(|x| x.d).collect::<Vec<_>>(), dead, max_cop(&items).0);
            }
        }
        "planted1" => { // planted negative: drop pairwise coprimality: window divisors of one speed (cov = 1 each)
            for &(n, r) in &[(400i64, 1i64), (1000, 1), (2000, 1), (5000, 1), (400, 7)] {
                let lim = (2 * n - 1) * n; let dl = dlist(n, r); let mut cnt = vec![0u16; lim as usize + 1];
                for dm in &dl { let mut m = dm.d; while m <= lim { cnt[m as usize] += 1; m += dm.d; } }
                let (mut bw, mut bc) = (0usize, 0u16); for (w, &c) in cnt.iter().enumerate() { if c > bc { bc = c; bw = w; } }
                let w = bw as i64; let mut sum = 0.0; let mut items = vec![];
                for dm in &dl { let (ov, tw, _, _) = cover(n, *dm, w); let c = ov as f64 / tw as f64; sum += c; if c > 0.0 { items.push((dm.d, c)); } }
                println!("planted1 N={} r={}: w={} window-divisors={} ; S(w)=sum cov={:.4} (bound 8 {}) ; max pairwise-coprime subset total={:.3}", n, r, w, bc, sum, if sum > 8.0 { "FAILS" } else { "holds" }, max_cop(&items).0);
            }
        }
        "sums" => { // dead-window and S+ osc-constant arithmetic
            for dp in [110.0f64, 232.0] { let th = 2.0 / dp; let c = 2.0 * th * dp + 2.0 * 4.0 / (1.0 - 2.0 * th); println!("S+ osc const at D*+1={}: 4+8/(1-2theta)={:.4}", dp, 4.0 + 8.0 / (1.0 - 2.0 * th)); let _ = c; }
            for k in [1.0f64, 10.0, 100.0, 129.0, 130.0, 143.0, 200.0, 1000.0] { let o = 12.3 * k / (110.0 * k); println!("k={} S+(9k+1): crude dead bound 8k/(1-O)={:.4} vs 9k+1={}", k, 8.0 * k / (1.0 - o), 9.0 * k + 1.0); }
        }
        _ => println!("unknown"),
    }
}
