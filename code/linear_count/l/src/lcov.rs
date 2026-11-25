// lcov.rs: own exact engine for Theorem L. Not br.rs. All load-bearing arithmetic in i128/u128 integers.
use std::env;

fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }
fn egcd(a: i128, b: i128) -> (i128, i128, i128) { if b == 0 { (a, 1, 0) } else { let (g, x, y) = egcd(b, a % b); (g, y, x - (a / b) * y) } }
fn modinv(a: i128, m: i128) -> i128 { let (g, x, _) = egcd(((a % m) + m) % m, m); assert!(g == 1, "not invertible"); ((x % m) + m) % m }
fn centered(u: i128, d: i128) -> i128 { let u = ((u % d) + d) % d; if 2 * u > d { u - d } else { u } }

// level theta = p/q, window half-width d = u/v
#[derive(Clone, Copy)]
struct Par { p: i128, q: i128, u: i128, v: i128 }

// exact bad measure of speed w inside J(D) = [a/D - d, a/D + d]  (a r = 1 mod D). returns (num, den), cov = num/den, den = 2 D w q u.
// None if more than cap arcs would be enumerated.
fn cov_exact(par: &Par, dd: i128, a: i128, w: i128, cap: i128) -> Option<(i128, i128)> {
    let y0 = centered(w % dd * (a % dd) % dd, dd);
    let wn = dd * w * par.q * par.u; // window half width scaled by S = D w q v
    // |y| q v < D p v + D w q u (roughly): number of j each side
    let ymax = (dd * w * par.q * par.u / par.v + dd * par.p) / par.q + dd; // generous
    let jm = ymax / dd + 2;
    if 2 * jm + 1 > cap { return None; }
    let mut num: i128 = 0;
    let mut j = -jm;
    while j <= jm {
        let y = y0 + j * dd;
        let lo = -(y * par.q + dd * par.p) * par.v;
        let hi = (-y * par.q + dd * par.p) * par.v;
        let l2 = if lo > -wn { lo } else { -wn };
        let h2 = if hi < wn { hi } else { wn };
        if h2 > l2 { num += h2 - l2; }
        j += 1;
    }
    Some((num, 2 * wn))
}

fn window(n: i128, r: i128) -> Vec<i128> { (n + 1 + r..=2 * n - 1).filter(|&d| gcd(d as u64, r as u64) == 1).collect() }

// max weight pairwise coprime subset (exact branch and bound, node cap 3e6; returns best found, cap hit counted in UNRES)
static UNRES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
fn maxw(items: &[(i128, f64)]) -> f64 {
    let mut best = 0.0f64; let mut nodes = 0u64;
    fn rec(items: &[(i128, f64)], i: usize, chosen: &mut Vec<i128>, cur: f64, rest: &[f64], best: &mut f64, nodes: &mut u64) {
        *nodes += 1; if *nodes > 3_000_000 { return; }
        if cur > *best { *best = cur; }
        if i >= items.len() || cur + rest[i] <= *best { return; }
        let (d, wgt) = items[i];
        if chosen.iter().all(|&c| gcd(c as u64, d as u64) == 1) {
            chosen.push(d);
            rec(items, i + 1, chosen, cur + wgt, rest, best, nodes);
            chosen.pop();
        }
        rec(items, i + 1, chosen, cur, rest, best, nodes);
    }
    let mut it: Vec<(i128, f64)> = items.to_vec(); it.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
    let mut rest = vec![0.0; it.len() + 1];
    for i in (0..it.len()).rev() { rest[i] = rest[i + 1] + it[i].1; }
    let mut ch = Vec::new();
    rec(&it, 0, &mut ch, 0.0, &rest, &mut best, &mut nodes);
    if nodes > 3_000_000 { UNRES.fetch_add(1, std::sync::atomic::Ordering::Relaxed); println!("UNRESOLVED maxw (node cap) list={}", it.len()); }
    best
}
// max size pairwise coprime subset (exact), of the ds
fn maxsz(ds: &[i128]) -> usize { let it: Vec<(i128, f64)> = ds.iter().map(|&d| (d, 1.0)).collect(); maxw(&it).round() as usize }

// greedy large pairwise coprime subset of the window (primes first, then others by prime-support disjointness)
fn greedy_cop(c: &[i128]) -> Vec<i128> {
    let mut v: Vec<i128> = c.to_vec();
    // order: fewer distinct prime factors first, then smaller
    fn nd(mut x: i128) -> usize { let mut c = 0; let mut p = 2; while p * p <= x { if x % p == 0 { c += 1; while x % p == 0 { x /= p; } } p += 1; } if x > 1 { c += 1; } c }
    v.sort_by_key(|&x| (nd(x), x));
    let mut out: Vec<i128> = vec![];
    for x in v { if out.iter().all(|&o| gcd(o as u64, x as u64) == 1) { out.push(x); } }
    out.sort();
    out
}

// ---------------- mode scan: per-speed coverage totals, all w in (N, wmax*N^3], r <= N/2
fn scan(nlo: i128, nhi: i128, wfac: i128, rstep: i128) {
    println!("# scan N={}..{} w<= {}*N^3 (non-oscillating range N<w<Omega checked via arcs; w>=Omega checked per D vs 7/N)", nlo, nhi, wfac);
    let mut gmax_all = 0.0f64; let mut gmax_cop = 0.0f64; let mut garg = (0, 0, 0, 0usize);
    let mut gmax_nz = 0usize; let mut viol = 0u64; let mut gmax_osc = 0.0f64;
    let mut tot = 0u64;
    let mut maxfe_le = 0usize; // max pairwise coprime group size with the same e, w <= N^2+N
    let mut maxfe_all = 0usize;
    for n in nlo..=nhi {
        let kk = (2 * n - 1) * n * n;
        let par = Par { p: 1, q: n, u: 1, v: kk };
        let wmax = if wfac > 0 { wfac * n * n * n } else { (-wfac) * n * n };
        let mut nmax_all = 0.0f64; let mut nmax_cop = 0.0f64;
        let mut r = 1;
        while r <= n / 2 {
            let c = window(n, r);
            let avals: Vec<i128> = c.iter().map(|&d| modinv(r, d)).collect();
            for w in n + 1..=wmax {
                // non-oscillating: 2 w < (2N-1) N (N-2)
                let nonosc = 2 * w < (2 * n - 1) * n * (n - 2);
                let mut list: Vec<(i128, f64)> = vec![]; let mut es: Vec<(i128, i128)> = vec![];
                let mut sum = 0.0f64;
                for (idx, &d) in c.iter().enumerate() {
                    let y = centered((w % d) * avals[idx] % d, d);
                    if nonosc {
                        // prefilter: |y| K < D (w + (2N-1) N)
                        if y.abs() * kk >= d * (w + (2 * n - 1) * n) { continue; }
                    }
                    let (nu, de) = match cov_exact(&par, d, avals[idx], w, 100000) { Some(x) => x, None => { println!("CAP w={}", w); continue; } };
                    if nu == 0 { continue; }
                    let cv = nu as f64 / de as f64;
                    if nonosc {
                        // claimed integer facts
                        if y.abs() * n * n > w + 2 * n * n { viol += 1; println!("VIOL e-bound N={} r={} w={} D={} y={}", n, r, w, d, y); }
                        if nu > 2 * d * n * n * (2 * n - 1) { viol += 1; println!("VIOL cov<=(2N-1)N/w N={} r={} w={} D={}", n, r, w, d); }
                        if nu > de { viol += 1; println!("VIOL cov<=1"); }
                        if (w - y * r) % d != 0 { viol += 1; println!("VIOL D | w - e r"); }
                        // refined per-modulus bound (Lemma 5'): cov <= (1/2)|[x-rho, x+rho] cap [-1,1]|, x = |e|/q, rho = 2/q, q = w/N^2
                        { let qq = w as f64 / (n * n) as f64; let x = y.abs() as f64 / qq; let rho = 2.0 / qq;
                          let hi = (x + rho).min(1.0); let lo = (x - rho).max(-1.0); let g = 0.5 * (hi - lo).max(0.0);
                          if cv > g + 1e-9 { viol += 1; println!("VIOL refined per-D bound N={} r={} w={} D={} cov={} g={}", n, r, w, d, cv, g); } }
                        list.push((d, cv)); es.push((d, y)); sum += cv;
                    } else {
                        if cv * (n as f64) > 7.0 + 1e-12 { viol += 1; println!("VIOL osc cov>7/N N={} r={} w={} D={} cov*N={}", n, r, w, d, cv * n as f64); }
                        if cv * (n as f64) > gmax_osc { gmax_osc = cv * n as f64; }
                    }
                }
                if !nonosc { continue; }
                tot += 1;
                if list.is_empty() { continue; }
                if sum > nmax_all { nmax_all = sum; }
                if sum > gmax_all { gmax_all = sum; }
                if list.len() > gmax_nz { gmax_nz = list.len(); }
                let b = if sum <= nmax_cop { 0.0 } else { maxw(&list) };
                if b > nmax_cop { nmax_cop = b; }
                if b > gmax_cop { gmax_cop = b; garg = (n as i64, r as i64, w as i64, list.len()); }
                // group by e: pairwise coprime group size
                if list.len() >= 2 {
                    let mut es2 = es.clone(); es2.sort_by_key(|x| x.1);
                    let mut i = 0;
                    while i < es2.len() {
                        let mut j = i; while j < es2.len() && es2[j].1 == es2[i].1 { j += 1; }
                        if j - i >= 2 {
                            let ds: Vec<i128> = es2[i..j].iter().map(|x| x.0).collect();
                            let s = maxsz(&ds);
                            if s > maxfe_all { maxfe_all = s; }
                            if w <= n * n + n && s > maxfe_le { maxfe_le = s; }
                            if s > 2 { viol += 1; println!("VIOL |F_e|>2 N={} r={} w={}", n, r, w); }
                            if w <= n * n + n && s > 1 { viol += 1; println!("VIOL |F_e|>1 for w<=N^2+N N={} r={} w={}", n, r, w); }
                        }
                        i = j;
                    }
                }
            }
            r += rstep;
        }
        println!("N={} max total (all D, no coprimality) = {:.4}  max total over pairwise-coprime F = {:.4}", n, nmax_all, nmax_cop);
    }
    println!("SUMMARY scan: (N,r,w) tested (non-osc) = {}; max total all-D = {:.4}; max total coprime-F = {:.4} at (N,r,w,#pos)={:?}; max #D with cov>0 = {}; max |F_e| overall = {} ; for w<=N^2+N = {}; max osc cov*N = {:.4} (bound 7); VIOLATIONS = {}", tot, gmax_all, gmax_cop, garg, gmax_nz, maxfe_all, maxfe_le, gmax_osc, viol);
}


// ---------------- S+ (value form) lemma-level scan: level theta = 2/(Dm+1), window half-width d = 2/(N Dm (Dm+1)), moduli = window elements <= Dm
fn scanp(nlo: i128, nhi: i128, wfac: i128, rstep: i128, tt: usize) {
    println!("# scanplus N={}..{} w<= {}*N^3 ; Dm = max of window (kind A) and Dm = max of the T={} smallest greedy pairwise coprime (kind B)", nlo, nhi, wfac, tt);
    let mut gmax = [0.0f64; 2]; let mut gcop = [0.0f64; 2]; let mut viol = 0u64; let mut gosc = 0.0f64; let mut tot = 0u64; let mut gnz = 0usize;
    for n in nlo..=nhi {
        let mut r = 1;
        while r <= n / 2 {
            let call = window(n, r);
            if call.len() < tt { r += rstep; continue; }
            let dms = [*call.last().unwrap(), *small_cop(&call, tt).last().unwrap()];
            for (kind, &dm) in dms.iter().enumerate() {
                let c: Vec<i128> = call.iter().cloned().filter(|&d| d <= dm).collect();
                let avals: Vec<i128> = c.iter().map(|&d| modinv(r, d)).collect();
                let par = Par { p: 2, q: dm + 1, u: 2, v: n * dm * (dm + 1) };
                let wmax = wfac * n * n * n;
                for w in n + 1..=wmax {
                    let nonosc = 2 * w * par.q * par.u < (par.q - 2 * par.p) * par.v;
                    let mut list: Vec<(i128, f64)> = vec![]; let mut sum = 0.0f64;
                    for (idx, &d) in c.iter().enumerate() {
                        let y = centered((w % d) * avals[idx] % d, d);
                        if nonosc && y.abs() * par.q * par.v >= d * par.p * par.v + d * w * par.q * par.u { continue; }
                        let (nu, de) = match cov_exact(&par, d, avals[idx], w, 100000) { Some(x) => x, None => continue };
                        if nu == 0 { continue; }
                        let cv = nu as f64 / de as f64;
                        if nonosc {
                            if y.abs() * n * (dm + 1) >= 2 * w + 2 * n * (dm + 1) { viol += 1; println!("VIOL e-bound(S+) N={} r={} w={} D={} y={}", n, r, w, d, y); }
                            if nu > 2 * d * par.q * par.u * n * dm { viol += 1; println!("VIOL cov<=N Dm/w (S+) N={} r={} w={}", n, r, w); }
                            if nu > de { viol += 1; }
                            list.push((d, cv)); sum += cv;
                        } else {
                            let v = cv * (dm + 1) as f64; if v > gosc { gosc = v; }
                            if v > 12.25 + 1e-12 { viol += 1; println!("VIOL osc(S+) N={} r={} w={} D={} cov*(Dm+1)={}", n, r, w, d, v); }
                        }
                    }
                    if !nonosc || list.is_empty() { continue; }
                    tot += 1; if sum > gmax[kind] { gmax[kind] = sum; } if list.len() > gnz { gnz = list.len(); }
                    if sum > gcop[kind] { let b = maxw(&list); if b > gcop[kind] { gcop[kind] = b; } }
                }
            }
            r += rstep;
        }
        println!("N={} so far: max total all-D {:.4}/{:.4}, coprime-F {:.4}/{:.4} (kinds A/B)", n, gmax[0], gmax[1], gcop[0], gcop[1]);
    }
    println!("SUMMARY scanplus: (N,r,w,kind) tested {} ; max all-D total A/B = {:.4}/{:.4}; max coprime-F total A/B = {:.4}/{:.4}; max #pos {}; max osc cov*(Dm+1) = {:.4} (bound 12.25); VIOLATIONS = {}", tot, gmax[0], gmax[1], gcop[0], gcop[1], gnz, gosc, viol);
}

// ---------------- mode alive: the proof's own conclusion. F = smallest greedy pairwise coprime window set of size T = 9k+1; adversary picks k speeds greedily
// to maximise sum_D min(1, accumulated coverage); report dead moduli (accumulated coverage >= 1) and min accumulated coverage over F. Claim: dead <= 8kN/(N-7k) < |F|.
fn alive(n: i128, r: i128, k: usize, rounds: u64, seed: u64) {
    let kk = (2 * n - 1) * n * n; let par = Par { p: 1, q: n, u: 1, v: kk };
    let c = window(n, r); let t = 9 * k + 1; let f = small_cop(&c, t);
    if f.len() < t { println!("alive N={} r={} k={}: window has only {} pairwise coprime (need {})", n, r, k, f.len(), t); return; }
    let avals: Vec<i128> = f.iter().map(|&d| modinv(r, d)).collect();
    let cf = greedy_cop(&c);
    let mut s = seed; let mut maxdead = 0usize; let mut minmin = 1e9f64; let mut maxacc_sum = 0.0f64;
    for _ in 0..rounds {
        let mut acc = vec![0.0f64; f.len()]; let mut ws: Vec<i128> = vec![];
        for _step in 0..k {
            let mut best: (f64, i128, Vec<f64>) = (-1.0, 0, vec![]);
            for _cand in 0..400 {
                let kind = lcg(&mut s) % 4;
                let w: i128 = match kind {
                    0 => n + 1 + (lcg(&mut s) % (6 * (n * n) as u64)) as i128,
                    1 => { let a = cf[(lcg(&mut s) % cf.len() as u64) as usize]; let b = cf[(lcg(&mut s) % cf.len() as u64) as usize]; let m = (lcg(&mut s) % 3 + 1) as i128; let e = (lcg(&mut s) % 5) as i128 - 2; (a * b * m + e * r).max(n + 1) }
                    2 => { let a = cf[(lcg(&mut s) % cf.len() as u64) as usize]; let m = (lcg(&mut s) % (6 * n as u64)) as i128 + 1; let e = (lcg(&mut s) % 7) as i128 - 3; (a * m + e * r).max(n + 1) }
                    _ => { let mut x: i128 = 0; let mut md: i128 = 1; for _ in 0..3 { let d = cf[(lcg(&mut s) % cf.len() as u64) as usize]; if md % d == 0 { continue; } if gcd(md as u64, d as u64) != 1 { continue; } let e = (lcg(&mut s) % 7) as i128 - 3; let target = ((e * r) % d + d) % d; let j = ((target - x) % d + d) % d * modinv(md % d, d) % d; x += md * j; md *= d; } let mut w = x; if w <= n { w += md * ((n - w) / md + 1); } w }
                };
                if ws.contains(&w) { continue; }
                let mut cv = vec![0.0f64; f.len()]; let mut obj = 0.0;
                for (i, &d) in f.iter().enumerate() { if let Some((nu, de)) = cov_exact(&par, d, avals[i], w, 200000) { cv[i] = nu as f64 / de as f64; } obj += (acc[i] + cv[i]).min(1.0); }
                if obj > best.0 { best = (obj, w, cv); }
            }
            ws.push(best.1); for i in 0..f.len() { acc[i] += best.2[i]; }
        }
        let dead = acc.iter().filter(|&&a| a >= 1.0).count();
        let mn = acc.iter().cloned().fold(1e9f64, f64::min); let sm: f64 = acc.iter().map(|&a| a.min(1.0)).sum();
        if dead > maxdead { maxdead = dead; } if mn < minmin { minmin = mn; } if sm > maxacc_sum { maxacc_sum = sm; }
    }
    let bound = 8.0 * k as f64 * n as f64 / (n as f64 - 7.0 * k as f64);
    println!("alive N={} r={} k={} |F|={} (D* = {}), {} greedy-adversarial rounds: max #dead = {} (proof: <= {:.2}), min over F of accumulated coverage (worst round) = {:.4} (<1 means an alive modulus exists), max sum min(1,acc) = {:.2}", n, r, k, f.len(), f.last().unwrap(), rounds, maxdead, bound, minmin, maxacc_sum);
}
// ---------------- mode big: structured and random large w, per-D coverage vs 7/N (w>=Omega) and sums
fn lcg(s: &mut u64) -> u64 { *s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); *s >> 11 }
fn big(n: i128, r: i128, samples: u64, seed: u64) {
    let kk = (2 * n - 1) * n * n; let par = Par { p: 1, q: n, u: 1, v: kk };
    let c = window(n, r); let avals: Vec<i128> = c.iter().map(|&d| modinv(r, d)).collect();
    let f = greedy_cop(&c);
    let mut s = seed; let mut worst_osc = 0.0f64; let mut worst_sum = 0.0f64; let mut viol = 0; let mut worst_nonosc_sum = 0.0f64; let mut maxpos = 0usize;
    let omega2 = (2 * n - 1) * n * (n - 2); // osc iff 2w >= omega2
    for it in 0..samples {
        // w kinds: 0 log-uniform to 1e11; 1 multiple of product of 2 random f elems (+ e r); 2 CRT of 3 moduli with offsets
        let kind = it % 3;
        let w: i128 = match kind {
            0 => { let e = (lcg(&mut s) % 3600) as f64 / 100.0; let v = 10f64.powf(e / 7.2); (n as f64 * v) as i128 + 1 + n }
            1 => { let a = f[(lcg(&mut s) % f.len() as u64) as usize]; let b = f[(lcg(&mut s) % f.len() as u64) as usize]; let m = (lcg(&mut s) % 4000 + 1) as i128; let e = (lcg(&mut s) % 9) as i128 - 4; (a * b * m + e * r).max(n + 1) }
            _ => { // CRT: w = e_i r mod D_i for 3 random distinct moduli of f
                let mut idx = [0usize; 3]; for t in 0..3 { idx[t] = (lcg(&mut s) % f.len() as u64) as usize; }
                if idx[0] == idx[1] || idx[1] == idx[2] || idx[0] == idx[2] { continue; }
                let mut x: i128 = 0; let mut md: i128 = 1;
                for t in 0..3 { let d = f[idx[t]]; let e = (lcg(&mut s) % 9) as i128 - 4; let target = ((e * r) % d + d) % d;
                    // solve x + md*j = target mod d
                    let j = ((target - x) % d + d) % d * modinv(md % d, d) % d; x += md * j; md *= d; }
                let mut w = x; if w <= n { w += md * ((n - w) / md + 1); } w
            }
        };
        let nonosc = 2 * w < omega2;
        let mut sum = 0.0f64; let mut pos = 0usize; let mut items = vec![];
        for (idx, &d) in c.iter().enumerate() {
            if let Some((nu, de)) = cov_exact(&par, d, avals[idx], w, 3_000_000) {
                if nu == 0 { continue; }
                let cv = nu as f64 / de as f64;
                if !nonosc { if cv * n as f64 > worst_osc { worst_osc = cv * n as f64; } if cv * n as f64 > 7.0 + 1e-12 { viol += 1; println!("VIOL osc N={} r={} w={} D={}", n, r, w, d); } }
                else { sum += cv; pos += 1; items.push((d, cv)); }
            }
        }
        if nonosc { let b = if sum <= 8.0 { sum } else { maxw(&items) }; if b > worst_nonosc_sum { worst_nonosc_sum = b; } if b > 8.0 + 1e-9 { viol += 1; println!("VIOL coprime-F sum>8 N={} r={} w={}", n, r, w); } if pos > maxpos { maxpos = pos; } }
        if sum > worst_sum { worst_sum = sum; }
    }
    println!("big N={} r={} |window coprime to r|={} |greedy F|={} samples={} : worst osc cov*N={:.4} (bound 7), worst nonosc coprime-F total={:.4} (refined bound 8), max #pos={}, viol={}", n, r, c.len(), f.len(), samples, worst_osc, worst_nonosc_sum, maxpos, viol);
}


// independent instrument check: grid count of bad points in J(D) vs cov_exact (exact integer test of ||w t|| < 1/N at grid points)
fn xcheck(trials: u64, grid: i128, seed: u64) {
    let mut s = seed; let mut worst = 0.0f64; let mut done = 0;
    for _ in 0..trials {
        let n = 12 + (lcg(&mut s) % 60) as i128; let r = 1 + (lcg(&mut s) % (n as u64 / 2)) as i128;
        let c = window(n, r); if c.is_empty() { continue; }
        let d = c[(lcg(&mut s) % c.len() as u64) as usize]; let a = modinv(r, d);
        let w = n + 1 + (lcg(&mut s) % (3 * (n * n * n) as u64)) as i128;
        let kk = (2 * n - 1) * n * n; let par = Par { p: 1, q: n, u: 1, v: kk };
        let (nu, de) = match cov_exact(&par, d, a, w, 100000) { Some(x) => x, None => continue };
        let cv = nu as f64 / de as f64;
        // grid: t = a/D + (j/grid) * (1/K), j in -grid..grid  ; t = (a K + j D / grid * ...) use common denominator D*K*grid
        let den = d * kk * grid; let mut bad = 0i128;
        for j in -grid..=grid { let tn = a * kk * grid + j * d; // t = tn/den
            let m = w * tn; // w t = m/den
            let cc = (2 * m + den) / (2 * den); let diff = (m - cc * den).abs();
            if diff * n < den { bad += 1; } }
        let est = bad as f64 / (2 * grid + 1) as f64;
        let e = (est - cv).abs(); if e > worst { worst = e; } done += 1;
    }
    println!("xcheck: {} random (N,r,D,w) cases, grid {} pts each, max |grid fraction - cov_exact| = {:.3e}", done, 2 * grid + 1, worst);
}
// ---------------- theorem-level machinery, general level theta = p/q (arcs ((c q - p)/(x q), (c q + p)/(x q)))
#[derive(Clone, Copy, Debug)]
struct Q { n: u128, d: u128 }
fn qlt(a: Q, b: Q) -> bool { a.n * b.d < b.n * a.d }
fn qle(a: Q, b: Q) -> bool { a.n * b.d <= b.n * a.d }
fn qf(a: Q) -> f64 { a.n as f64 / a.d as f64 }
fn qmin(a: Q, b: Q) -> Q { if qlt(b, a) { b } else { a } }

fn base_gaps(n: u128, r: u128, p: u128, q: u128) -> Vec<(Q, Q)> {
    let mut arcs: Vec<(i128, i128, i128)> = vec![];
    for x in 1..=n { if x == r { continue; } for c in 0..=x { arcs.push((c as i128 * q as i128 - p as i128, c as i128 * q as i128 + p as i128, (x * q) as i128)); } }
    arcs.sort_by(|a, b| (a.0 * b.2).cmp(&(b.0 * a.2)));
    let mut gaps = vec![];
    let (mut rn, mut rd): (i128, i128) = (-1, 1);
    for &(l, rr, d) in &arcs {
        if l * rd >= rn * d {
            let gl = (rn, rd); let gr = (l, d);
            if gr.0 >= 0 {
                let gln = if gl.0 < 0 { Q { n: 0, d: 1 } } else { Q { n: gl.0 as u128, d: gl.1 as u128 } };
                let grq = Q { n: gr.0 as u128, d: gr.1 as u128 };
                let half = Q { n: 1, d: 2 };
                if qle(gln, half) { gaps.push((gln, qmin(grq, half))); }
            }
        }
        if rr * rd > rn * d { rn = rr; rd = d; }
    }
    gaps
}
// minimal t >= gl good (||w t|| >= p/q) for all speeds in ws; None if beyond gr or cap
fn first_good(gl: Q, gr: Q, ws: &[u128], p: u128, q: u128) -> Option<Q> {
    let mut t = gl; let mut it = 0;
    loop {
        let mut ch = false;
        for &w in ws {
            let m = w * t.n; let c = (2 * m + t.d) / (2 * t.d);
            let cd = c * t.d; let diff = if m >= cd { m - cd } else { cd - m };
            if diff * q < p * t.d { t = Q { n: c * q + p, d: w * q }; ch = true; if qlt(gr, t) { return None; } }
        }
        if !ch { return Some(t); }
        it += 1; if it > 2_000_000 { return None; }
    }
}
fn ml_ge(gaps: &[(Q, Q)], ws: &[u128], p: u128, q: u128) -> bool { gaps.iter().any(|&(l, r)| first_good(l, r, ws, p, q).is_some()) }
fn restrict(iv: &[(Q, Q)], w: u128, p: u128, q: u128) -> Vec<(Q, Q)> {
    let mut out = vec![];
    for &(l, r) in iv {
        let mut t = l; let mut guard = 0;
        loop {
            if qlt(r, t) { break; }
            guard += 1; if guard > 100000 { break; }
            let g = match first_good(t, r, &[w], p, q) { Some(g) => g, None => break };
            let c1 = (w * g.n) / g.d + 1;
            let end = Q { n: c1 * q - p, d: w * q };
            out.push((g, qmin(end, r)));
            if !qlt(end, r) { break; }
            t = Q { n: c1 * q + p, d: w * q };
        }
    }
    out
}
fn measure(iv: &[(Q, Q)]) -> f64 { iv.iter().map(|&(l, r)| qf(r) - qf(l)).sum() }

fn small_cop(c: &[i128], t: usize) -> Vec<i128> {
    let mut out: Vec<i128> = vec![];
    for &x in c { if out.iter().all(|&o| gcd(o as u64, x as u64) == 1) { out.push(x); if out.len() == t { break; } } }
    out
}

// exhaustive single speed w in (N, wmax]; level (p,q); returns failures
fn single(n: u128, r: u128, wmax: u128, p: u128, q: u128) -> (usize, Vec<u128>) {
    let mut gaps = base_gaps(n, r, p, q);
    gaps.sort_by(|a, b| { let wa = qf(a.1) - qf(a.0); let wb = qf(b.1) - qf(b.0); wb.partial_cmp(&wa).unwrap() });
    let mut fails = vec![];
    if gaps.is_empty() { return (0, vec![0]); }
    for w in n + 1..=wmax { if !ml_ge(&gaps, &[w], p, q) { fails.push(w); if fails.len() > 20 { break; } } }
    (gaps.len(), fails)
}

// beam adversary for k speeds at level 1/N. pool kinds: 0 all w in (N,B]; 1 CRT lifts of 2-3 window moduli up to B (random, P samples)
fn adv(n: u128, r: u128, k: usize, bmax: u128, pool_n: usize, beam: usize, kind: u32, seed: u64) {
    let gaps0 = base_gaps(n, r, 1, n);
    let m0 = measure(&gaps0);
    let c = window(n as i128, r as i128);
    let f = greedy_cop(&c);
    let mut s = seed;
    let mut pool: Vec<u128> = vec![];
    if kind == 0 { pool.extend(n + 1..=bmax); }
    else {
        let nn = n as i128; let e_max = 4i128;
        while pool.len() < pool_n {
            let nm = 2 + (lcg(&mut s) % 2) as usize;
            let mut x: i128 = 0; let mut md: i128 = 1; let mut used = vec![];
            for _ in 0..nm { let d = f[(lcg(&mut s) % f.len() as u64) as usize]; if used.contains(&d) { continue; } used.push(d);
                let e = (lcg(&mut s) % (2 * e_max as u64 + 1)) as i128 - e_max; let target = (((e * r as i128) % d) + d) % d;
                let j = (((target - x) % d) + d) % d * modinv(md % d, d) % d; x += md * j; md *= d; }
            let mut w = x; if w <= nn { w += md * ((nn - w) / md + 1); }
            while w as u128 <= bmax && pool.len() < pool_n { pool.push(w as u128); w += md; if md as u128 > bmax { break; } }
        }
    }
    pool.sort(); pool.dedup();
    println!("adv N={} r={} k={} base gaps={} base measure={:.6e} pool={} (kind {}, B={}) beam={}", n, r, k, gaps0.len(), m0, pool.len(), kind, bmax, beam);
    let mut states: Vec<(Vec<(Q, Q)>, Vec<u128>)> = vec![(gaps0, vec![])];
    for step in 1..=k {
        let mut cand: Vec<(f64, usize, u128, Vec<(Q, Q)>)> = vec![];
        for (si, (iv, ws)) in states.iter().enumerate() {
            let mut top: Vec<(f64, u128, Vec<(Q, Q)>)> = vec![];
            for &w in &pool { if ws.contains(&w) { continue; }
                let ni = restrict(iv, w, 1, n);
                if ni.is_empty() { println!("FAILURE FOUND (ML<1/N): N={} r={} W={:?}+{}", n, r, ws, w); return; }
                let m = measure(&ni);
                if top.len() < beam || m < top[top.len() - 1].0 {
                    top.push((m, w, ni)); top.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap()); if top.len() > beam { top.pop(); } }
            }
            for (m, w, ni) in top { cand.push((m, si, w, ni)); }
        }
        cand.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
        let mut ns: Vec<(Vec<(Q, Q)>, Vec<u128>)> = vec![];
        for (_, si, w, ni) in cand { let mut ws = states[si].1.clone(); ws.push(w); let mut key = ws.clone(); key.sort();
            if ns.iter().any(|(_, o)| { let mut ok = o.clone(); ok.sort(); ok == key }) { continue; }
            ns.push((ni, ws)); if ns.len() >= beam { break; } }
        let best = &ns[0];
        println!("  step {}: best remaining measure ratio = {:.3e} ({} intervals) W={:?}; ML>=1/N holds (nonempty)", step, measure(&best.0) / m0, best.0.len(), best.1);
        states = ns;
    }
    println!("  RESULT: no ML<1/N found for k={} (adversary lower bound only)", k);
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let p = |i: usize| -> i128 { a[i].parse().unwrap() };
    match a[1].as_str() {
        "scan" => scan(p(2), p(3), p(4), p(5)),
        "alive" => alive(p(2), p(3), p(4) as usize, p(5) as u64, p(6) as u64),
        "scanp" => scanp(p(2), p(3), p(4), p(5), p(6) as usize),
        "big" => big(p(2), p(3), p(4) as u64, p(5) as u64),
        "xcheck" => xcheck(p(2) as u64, p(3), 7),
        "ctl" => {
            let chk = |n: u128, r: u128, ws: &[u128], expect_ge: bool| {
                let g = base_gaps(n, r, 1, n);
                let got = ml_ge(&g, ws, 1, n);
                println!("ctl [{}]-{}+{:?}: ML>=1/N = {} (expected {}) {}", n, r, ws, got, expect_ge, if got == expect_ge { "OK" } else { "FAIL" });
            };
            chk(13, 6, &[69], false); chk(20, 6, &[29, 31], false); chk(21, 6, &[29, 31], true); chk(29, 12, &[31, 94, 98], false);
            chk(13, 6, &[], true); chk(8, 0, &[], false); chk(9, 0, &[], false); chk(20, 0, &[], false);
        }
        "single" => { // single N rlo rhi wfac mode(0: level 1/N ; 1: S+ level 2/(Dm+1) with F = 20 smallest greedy pairwise coprime) T
            let (n, rlo, rhi, wf, mode, tt) = (p(2) as u128, p(3) as u128, p(4) as u128, p(5) as u128, p(6), p(7) as usize); let wmax = wf * n * n * n;
            let mut nf = 0; let mut tested = 0; let mut maxdm = 0;
            for r in rlo..=rhi {
                let (pp, qq) = if mode == 0 { (1u128, n) } else {
                    let c = window(n as i128, r as i128); let f = small_cop(&c, tt); if f.len() < tt { continue; }
                    let dm = *f.last().unwrap() as u128; if dm > maxdm { maxdm = dm; } (2u128, dm + 1) };
                tested += 1;
                let (ng, f) = single(n, r, wmax, pp, qq); if !f.is_empty() { nf += 1; println!("N={} r={} level {}/{} gaps={} FAILS(first)={:?}", n, r, pp, qq, ng, &f[..f.len().min(6)]); } }
            println!("single N={} r={}..{} w<={}N^3 mode {} T={}: (N,r) tested={} with a failing w = {} (max Dm {})", n, rlo, rhi, wf, mode, tt, tested, nf, maxdm); }
        "hunt1" => { let (nlo, nhi) = (p(2) as u128, p(3) as u128);
            for n in nlo..=nhi { for r in 1..=n / 2 { let (_, f) = single(n, r, 3 * n * n * n, 1, n); if !f.is_empty() {
                let c: Vec<i128> = window(n as i128, r as i128); let mc = maxsz(&c);
                println!("EXC k=1 N={} r={} first w={} (#fails<=3N^3: {}) max pairwise-coprime window size={}", n, r, f[0], f.len(), mc); } } } }
        "pair" => { // all pairs N<w1<w2<=B, N in range, r<=N/2 ; list exceptions with window size
            let (nlo, nhi, bb) = (p(2) as u128, p(3) as u128, p(4) as u128);
            for n in nlo..=nhi { let mut cnt = 0u64; let mut lastexc = String::new();
                for r in 1..=n / 2 { let mut g = base_gaps(n, r, 1, n); g.sort_by(|a, b| { let wa = qf(a.1) - qf(a.0); let wb = qf(b.1) - qf(b.0); wb.partial_cmp(&wa).unwrap() });
                    let c: Vec<i128> = window(n as i128, r as i128); let mc = maxsz(&c);
                    for w1 in n + 1..=bb { for w2 in w1 + 1..=bb { if !ml_ge(&g, &[w1, w2], 1, n) { cnt += 1; lastexc = format!("r={} W=({},{}) maxcop={}", r, w1, w2, mc); } } } }
                println!("pair N={} B={}: #exceptions (pairs with ML<1/N) = {} last: {}", n, bb, cnt, lastexc); } }
        "adv" => adv(p(2) as u128, p(3) as u128, p(4) as usize, p(5) as u128, p(6) as usize, p(7) as usize, p(8) as u32, p(9) as u64),
        _ => println!("modes: scan big xcheck ctl single hunt1 pair adv"),
    }
}
