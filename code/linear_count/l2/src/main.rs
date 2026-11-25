// l2: own engine for THEOREM_L lemma-level coverage totals, joint double count, planted negatives.
// All window / arc arithmetic in exact i128 integers; only the final ratio cov = over/wl is f64.
// Units: window J(D) = [a/D - 1/K, a/D + 1/K], K=(2N-1)N^2, a r = 1 mod D. cov_w(D) = |{t in J: ||wt||<1/N}| / |J| (a FRACTION of the window).
use std::env;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::thread;

fn gcd(a: i64, b: i64) -> i64 { if b == 0 { a.abs() } else { gcd(b, a % b) } }
fn inv(r: i64, m: i64) -> i64 {
    let (mut a, mut b, mut x0, mut x1) = (r.rem_euclid(m), m, 1i64, 0i64);
    while b != 0 { let q = a / b; let t = a - q * b; a = b; b = t; let t2 = x0 - q * x1; x0 = x1; x1 = t2; }
    x0.rem_euclid(m)
}
fn fdiv(a: i128, b: i128) -> i128 { let q = a / b; if a % b != 0 && ((a < 0) != (b < 0)) { q - 1 } else { q } }
fn cdiv(a: i128, b: i128) -> i128 { -fdiv(-a, b) }

#[derive(Clone, Copy)]
struct Cv { over: i128, wl: i128, narcs: usize, c: i128 }
fn kk(n: i64) -> i128 { (2 * n as i128 - 1) * (n as i128) * (n as i128) }
fn cov(n: i64, d: i64, a: i64, w: i64) -> Cv {
    let (n_, d_, a_, w_) = (n as i128, d as i128, a as i128, w as i128);
    let k = kk(n);
    let lo = a_ * k - d_; let hi = a_ * k + d_;
    let cmin = fdiv(w_ * lo, d_ * k) - 1; let cmax = cdiv(w_ * hi, d_ * k) + 1;
    let wlo = lo * w_ * n_; let whi = hi * w_ * n_;
    let mut sum = 0i128; let mut narcs = 0; let mut cc = 0;
    let mut c = cmin;
    while c <= cmax {
        let alo = (c * n_ - 1) * d_ * k; let ahi = (c * n_ + 1) * d_ * k;
        let l = if wlo > alo { wlo } else { alo }; let h = if whi < ahi { whi } else { ahi };
        if h > l { sum += h - l; narcs += 1; cc = c; }
        c += 1;
    }
    Cv { over: sum, wl: whi - wlo, narcs, c: cc }
}
fn gfun(x: f64, rho: f64) -> f64 { let lo = (x - rho).max(-1.0); let hi = (x + rho).min(1.0); 0.5 * (hi - lo).max(0.0) }

fn moduli(n: i64, r: i64) -> Vec<(i64, i64)> {
    let mut v = vec![];
    for d in (n + 1 + r)..=(2 * n - 1) { if gcd(d, r) == 1 { v.push((d, inv(r, d))); } }
    v
}
// max weight pairwise coprime subset; items (D, weight)
fn max_cop(items: &Vec<(i64, f64)>, card: bool) -> (f64, Vec<i64>) {
    let mut it = items.clone();
    it.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
    let mut suf = vec![0.0; it.len() + 1];
    for i in (0..it.len()).rev() { suf[i] = suf[i + 1] + if card { 1.0 } else { it[i].1 }; }
    let mut best = 0.0; let mut bs = vec![]; let mut cur = vec![];
    fn rec(i: usize, it: &Vec<(i64, f64)>, suf: &Vec<f64>, cur: &mut Vec<i64>, cw: f64, best: &mut f64, bs: &mut Vec<i64>, card: bool) {
        if cw > *best { *best = cw; *bs = cur.clone(); }
        if i >= it.len() || cw + suf[i] <= *best + 1e-15 { return; }
        for j in i..it.len() {
            if cw + suf[j] <= *best + 1e-15 { return; }
            if cur.iter().all(|&x| gcd(x, it[j].0) == 1) {
                cur.push(it[j].0);
                rec(j + 1, it, suf, cur, cw + if card { 1.0 } else { it[j].1 }, best, bs, card);
                cur.pop();
            }
        }
    }
    rec(0, &it, &suf, &mut cur, 0.0, &mut best, &mut bs, card);
    (best, bs)
}

#[derive(Default, Clone)]
struct St {
    cases: u64, small: u64, osc: u64, w2r: u64,
    v_arc: u64, v_div: u64, v_ebound: u64, v_g: u64, v_grp: u64, v_s8: u64, v_osc: u64,
    max_cop: f64, max_cop_at: (i64, i64, i64), max_all: f64, max_all_at: (i64, i64, i64),
    max_osc: f64, max_osc_at: (i64, i64, i64), max_pos: usize, max_g_ratio: f64,
    ex: Vec<String>,
}
impl St {
    fn merge(&mut self, o: &St) {
        self.cases += o.cases; self.small += o.small; self.osc += o.osc; self.w2r += o.w2r;
        self.v_arc += o.v_arc; self.v_div += o.v_div; self.v_ebound += o.v_ebound; self.v_g += o.v_g; self.v_grp += o.v_grp; self.v_s8 += o.v_s8; self.v_osc += o.v_osc;
        if o.max_cop > self.max_cop { self.max_cop = o.max_cop; self.max_cop_at = o.max_cop_at; }
        if o.max_all > self.max_all { self.max_all = o.max_all; self.max_all_at = o.max_all_at; }
        if o.max_osc > self.max_osc { self.max_osc = o.max_osc; self.max_osc_at = o.max_osc_at; }
        if o.max_pos > self.max_pos { self.max_pos = o.max_pos; }
        if o.max_g_ratio > self.max_g_ratio { self.max_g_ratio = o.max_g_ratio; }
        for e in &o.ex { if self.ex.len() < 10 { self.ex.push(e.clone()); } }
    }
}

// one (N,r,w) lemma-level check
fn check(n: i64, r: i64, w: i64, mods: &Vec<(i64, i64)>, st: &mut St) {
    st.cases += 1;
    let nn = n as i128;
    let osc = 2 * (w as i128) >= (2 * nn - 1) * nn * (nn - 2);
    let q = w as f64 / (n as f64 * n as f64);
    let mut items: Vec<(i64, f64)> = vec![]; let mut tot = 0.0;
    let mut grp: Vec<(i128, i64)> = vec![];
    let w2r = w == 2 * r;
    if osc { st.osc += 1 } else { st.small += 1; if w2r { st.w2r += 1 } }
    for &(d, a) in mods {
        let cv = cov(n, d, a, w);
        if cv.over == 0 { continue; }
        let c = cv.over as f64 / cv.wl as f64;
        if osc {
            if c * (n as f64) > st.max_osc { st.max_osc = c * n as f64; st.max_osc_at = (n, r, w); }
            if c > 7.0 / n as f64 + 1e-12 { st.v_osc += 1; if st.ex.len() < 10 { st.ex.push(format!("osc N={} r={} w={} D={} cov={}", n, r, w, d, c)); } }
            continue;
        }
        items.push((d, c)); tot += c;
        if !w2r {
            if cv.narcs != 1 { st.v_arc += 1; if st.ex.len() < 10 { st.ex.push(format!("arc N={} r={} w={} D={} narcs={}", n, r, w, d, cv.narcs)); } continue; }
            let e = (a as i128) * (w as i128) - cv.c * (d as i128);
            if ((w as i128) - e * (r as i128)).rem_euclid(d as i128) != 0 { st.v_div += 1; if st.ex.len() < 10 { st.ex.push(format!("div N={} r={} w={} D={} e={}", n, r, w, d, e)); } }
            let ae = (e.abs() as f64) ; let abound = q + 2.0 - 1.0 / n as f64;
            if ae >= abound + 1e-12 { st.v_ebound += 1; if st.ex.len() < 10 { st.ex.push(format!("ebound N={} r={} w={} D={} e={}", n, r, w, d, e)); } }
            let g = gfun(ae / q, 2.0 / q);
            if c > g + 1e-9 { st.v_g += 1; if st.ex.len() < 10 { st.ex.push(format!("G N={} r={} w={} D={} cov={} G={}", n, r, w, d, c, g)); } }
            if g > 0.0 { let ratio = c / g; if ratio > st.max_g_ratio { st.max_g_ratio = ratio; } }
            grp.push((e, d));
        }
    }
    if osc { return; }
    if items.len() > st.max_pos { st.max_pos = items.len(); }
    if tot > st.max_all { st.max_all = tot; st.max_all_at = (n, r, w); }
    if !w2r {
        // groups: no three pairwise coprime moduli with the same e (Lemma 4)
        grp.sort();
        let mut i = 0;
        while i < grp.len() {
            let mut j = i; while j < grp.len() && grp[j].0 == grp[i].0 { j += 1; }
            let g = &grp[i..j];
            if g.len() >= 3 {
                'o: for x in 0..g.len() { for y in x + 1..g.len() { if gcd(g[x].1, g[y].1) != 1 { continue; } for z in y + 1..g.len() {
                    if gcd(g[x].1, g[z].1) == 1 && gcd(g[y].1, g[z].1) == 1 { st.v_grp += 1; if st.ex.len() < 10 { st.ex.push(format!("grp N={} r={} w={} e={} D={},{},{}", n, r, w, g[0].0, g[x].1, g[y].1, g[z].1)); } break 'o; } } } }
            }
            i = j;
        }
    }
    if tot > st.max_cop {
        let (s, _) = max_cop(&items, false);
        if s > st.max_cop { st.max_cop = s; st.max_cop_at = (n, r, w); }
        if s > 8.0 + 1e-9 { st.v_s8 += 1; if st.ex.len() < 10 { st.ex.push(format!("S8 N={} r={} w={} S={}", n, r, w, s)); } }
    }
}

fn run_threads<F: Fn(i64) -> St + Sync>(rs: Vec<i64>, nth: usize, f: F) -> St {
    let idx = AtomicUsize::new(0);
    let tot = Mutex::new(St::default());
    thread::scope(|s| {
        for _ in 0..nth {
            s.spawn(|| {
                loop {
                    let i = idx.fetch_add(1, Ordering::SeqCst);
                    if i >= rs.len() { break; }
                    let st = f(rs[i]);
                    tot.lock().unwrap().merge(&st);
                }
            });
        }
    });
    tot.into_inner().unwrap()
}
fn report(tag: &str, st: &St) {
    println!("{} cases={} small={} osc={} w2r={} | viol: arc={} div={} ebound={} G={} grp={} S8={} osc7/N={} | max_cop_S={:.4} at {:?} | max_allmod_S={:.4} at {:?} | max_osc*N={:.4} at {:?} (bound 7) | max_pos_moduli={} | max cov/G={:.6}",
        tag, st.cases, st.small, st.osc, st.w2r, st.v_arc, st.v_div, st.v_ebound, st.v_g, st.v_grp, st.v_s8, st.v_osc, st.max_cop, st.max_cop_at, st.max_all, st.max_all_at, st.max_osc, st.max_osc_at, st.max_pos, st.max_g_ratio);
    for e in &st.ex { println!("   EX {}", e); }
}

fn cmd_lem(n0: i64, n1: i64, fac: i64, nth: usize) {
    for n in n0..=n1 {
        let wmax = fac * n * n * n;
        let rs: Vec<i64> = (1..=n - 2).collect();
        let st = run_threads(rs, nth, |r| {
            let mods = moduli(n, r); let mut st = St::default();
            for w in (n + 1)..=wmax { check(n, r, w, &mods, &mut st); }
            st
        });
        report(&format!("LEM N={} w<={}N^3", n, fac), &st);
    }
}
// structured / large N: all w <= wf*N^2 plus CRT lifts for chosen r
fn crt2(a1: i64, m1: i64, a2: i64, m2: i64) -> i64 { // x = a1 mod m1, a2 mod m2, coprime
    let i = inv(m1.rem_euclid(m2), m2) as i128;
    let x = a1 as i128 + (m1 as i128) * ((((a2 - a1) as i128) * i).rem_euclid(m2 as i128));
    x as i64
}
fn cmd_big(n: i64, wf: i64, rsel: &str, nth: usize, eb: i64) {
    let rs: Vec<i64> = if rsel == "all" { (1..=n - 2).collect() } else { rsel.split(',').map(|x| x.parse::<i64>().unwrap()).filter(|&r| r >= 1 && r <= n - 2).collect() };
    let omega = ((2 * n as i128 - 1) * (n as i128) * (n as i128 - 2) / 2) as i64;
    let st = run_threads(rs, nth, |r| {
        let mods = moduli(n, r); let mut st = St::default();
        for w in (n + 1)..=(wf * n * n) { check(n, r, w, &mods, &mut st); }
        // CRT: triples with distinct e in [-eb,eb], pairs with common-lift multiples, quadruple ignored (product > omega)
        let ds: Vec<i64> = mods.iter().map(|x| x.0).collect();
        let m = ds.len();
        for i in 0..m { for j in i + 1..m { if gcd(ds[i], ds[j]) != 1 { continue; }
            let p = ds[i] * ds[j];
            for e1 in -eb..=eb { for e2 in -eb..=eb {
                let w0 = crt2((e1 * r).rem_euclid(ds[i]), ds[i], (e2 * r).rem_euclid(ds[j]), ds[j]);
                if e1 == e2 { let mut w = if w0 <= n { w0 + ((n - w0) / p + 1) * p } else { w0 }; while w <= 4 * omega { check(n, r, w, &mods, &mut st); w += p; } }
                else if w0 > n && w0 <= 4 * omega { check(n, r, w0, &mods, &mut st); }
                // third modulus
                for l in j + 1..m { if gcd(ds[l], ds[i]) != 1 || gcd(ds[l], ds[j]) != 1 { continue; }
                    for e3 in -eb..=eb {
                        let w1 = crt2(w0, p, (e3 * r).rem_euclid(ds[l]), ds[l]);
                        if w1 > n && w1 <= 4 * omega { check(n, r, w1, &mods, &mut st); }
                    } }
            } }
        } }
        st
    });
    report(&format!("BIG N={} w<={}N^2 + CRT eb={} rsel={}", n, wf, eb, rsel), &st);
}

// ---------- exact decision: exists t with ||v t|| >= 1/N for all v in V ----------
fn good_exists(n: i64, vs: &Vec<i64>) -> bool {
    let mut arcs: Vec<(i128, i128, i128)> = vec![];
    let n_ = n as i128;
    for &v in vs { let den = (v as i128) * n_; for c in 0..=(v as i128) { arcs.push((c * n_ - 1, c * n_ + 1, den)); } }
    arcs.sort_by(|x, y| (x.0 * y.2).cmp(&(y.0 * x.2)));
    let (mut cn, mut cd) = (0i128, 1i128);
    for &(l, h, d) in &arcs {
        if l * cd >= cn * d && cn < cd { return true; }
        if h * cd > cn * d { cn = h; cd = d; }
    }
    cn < cd
}
fn vset(n: i64, r: i64, w: &[i64]) -> Vec<i64> {
    let mut v: Vec<i64> = (1..=n).filter(|&x| x != r).collect();
    for &x in w { if !v.contains(&x) { v.push(x); } }
    v
}
fn window_dead_all(n: i64, r: i64, w: &[i64]) -> (usize, usize) { // (#valid moduli, #moduli with window fully covered by union of added-speed bad sets (checked by single sum==1 only if one speed))
    let mods = moduli(n, r); let mut dead = 0;
    for &(d, a) in &mods {
        let mut s = 0.0; for &x in w { let c = cov(n, d, a, x); s += c.over as f64 / c.wl as f64; }
        if s >= 1.0 - 1e-12 { dead += 1; }
    }
    (mods.len(), dead)
}
fn cmd_ctl() {
    // control 1: cov vs brute grid
    let mut seed = 12345u64; let mut maxdiff = 0.0f64;
    for _ in 0..3000 {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); let n = 10 + ((seed >> 33) % 31) as i64;
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); let r = 1 + ((seed >> 33) % (n as u64 - 2)) as i64;
        let mods = moduli(n, r); if mods.is_empty() { continue; }
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); let (d, a) = mods[((seed >> 33) as usize) % mods.len()];
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); let w = n + 1 + ((seed >> 33) % (3 * (n * n * n) as u64)) as i64;
        let c = cov(n, d, a, w); let exact = c.over as f64 / c.wl as f64;
        // grid: 4001 points midpoints in window, exact rational test ||w t|| < 1/N  <=> |w*num - c*den*...|
        let k = kk(n); let g = 4001i128; let mut hit = 0;
        for i in 0..g {
            // t = a/D - 1/K + (2/K)(i+0.5)/g  = ( (aK - D) g*2 + 2D(2i+1) ... ) common denom 2*g*D*K
            let den = 2 * g * (d as i128) * k;
            let num = (a as i128 * k - d as i128) * 2 * g + 2 * (d as i128) * (2 * i + 1);
            // ||w t||<1/N: let y = (w*num) mod den ; dist = min(y,den-y)/den < 1/N <=> N*min(y,den-y) < den
            let y = ((w as i128) * num).rem_euclid(den); let m = if y < den - y { y } else { den - y };
            if (n as i128) * m < den { hit += 1; }
        }
        let gr = hit as f64 / g as f64; let dd = (gr - exact).abs(); if dd > maxdiff { maxdiff = dd; }
    }
    println!("CTL1 cov_exact vs 4001-point exact-rational grid, 3000 random (N,r,D,w<=3N^3): max |diff| = {:.2e} (grid resolution ~ {:.1e})", maxdiff, 1.0 / 4001.0 * 1.0);
    // control 2: known exceptions and non-exceptions through the exact decision
    let cases: Vec<(i64, i64, Vec<i64>, bool)> = vec![
        (13, 6, vec![69], false), (9, 4, vec![30], false), (20, 6, vec![29, 31], false), (29, 12, vec![31, 94, 98], false),
        (13, 6, vec![], true), (21, 6, vec![29, 31], true), (20, 6, vec![], true), (8, 3, vec![], true), (9, 4, vec![], true),
    ];
    let mut ok = 0;
    for (n, r, w, expect) in &cases {
        let v = vset(*n, *r, w); let g = good_exists(*n, &v);
        let (nm, dd) = window_dead_all(*n, *r, w);
        println!("CTL2 [{}]-{}+{:?}: ML>=1/N ? {} (expected {}) | valid moduli {} fully-dead(sum cov>=1) {}", n, r, w, g, expect, nm, dd);
        if g == *expect { ok += 1; }
    }
    println!("CTL2 {}/{} agree", ok, cases.len());
}
// k=1 exhaustive: windows test then exact decision for the survivors; report exceptions and nu(N,r)=max pairwise coprime moduli
fn cmd_exc1(n0: i64, n1: i64, nth: usize) {
    for n in n0..=n1 {
        let rs: Vec<i64> = (1..=n - 2).collect();
        let out = Mutex::new(Vec::<String>::new()); let stw = Mutex::new((0u64, 0u64)); // (cases, window-dead cases)
        let idx = AtomicUsize::new(0);
        thread::scope(|s| { for _ in 0..nth { s.spawn(|| loop {
            let i = idx.fetch_add(1, Ordering::SeqCst); if i >= rs.len() { break; }
            let r = rs[i]; let mods = moduli(n, r);
            let (mut cs, mut wd) = (0u64, 0u64);
            for w in (n + 1)..=(3 * n * n * n) {
                cs += 1;
                let mut alive = false;
                for &(d, a) in &mods { let c = cov(n, d, a, w); if c.over < c.wl { alive = true; break; } }
                if alive { continue; }
                wd += 1;
                let g = good_exists(n, &vset(n, r, &[w]));
                if !g {
                    let it: Vec<(i64, f64)> = mods.iter().map(|x| (x.0, 1.0)).collect();
                    let (nu, _) = max_cop(&it, true);
                    out.lock().unwrap().push(format!("EXC N={} r={} w={} nu(N,r)={} (#valid moduli {})", n, r, w, nu, mods.len()));
                }
            }
            let mut g = stw.lock().unwrap(); g.0 += cs; g.1 += wd;
        }); } });
        let mut o = out.into_inner().unwrap(); o.sort();
        let g = stw.into_inner().unwrap();
        println!("EXC1 N={} cases={} all-windows-dead cases={} exceptions(ML<1/N)={}", n, g.0, g.1, o.len());
        for l in o { println!("   {}", l); }
    }
}

// ---------- double count with adversarial pool ----------
struct Cand { w: i64, osc: bool, cv: Vec<f64> }
fn is_osc(n: i64, w: i64) -> bool { let nn = n as i128; 2 * (w as i128) >= (2 * nn - 1) * nn * (nn - 2) }
fn cmd_dc(k: usize, n: i64, rsel: &str, wf: i64, beam: usize, nth: usize) {
    let rs: Vec<i64> = if rsel == "all" { (1..=n - 2).collect() } else { rsel.split(',').map(|x| x.parse::<i64>().unwrap()).filter(|&r| r >= 1 && r <= n - 2).collect() };
    let force: Option<usize> = env::var("L2_FORCE_OSC").ok().and_then(|x| x.parse().ok());
    let res = Mutex::new(Vec::<(usize, i64, String, bool)>::new());
    let idx = AtomicUsize::new(0);
    thread::scope(|s| { for _ in 0..nth { s.spawn(|| loop {
        let i = idx.fetch_add(1, Ordering::SeqCst); if i >= rs.len() { break; }
        let r = rs[i]; let mods = moduli(n, r); let m = mods.len(); if m == 0 { continue; }
        let wmax = wf * n * n * n;
        let mut ps: Vec<(f64, Cand)> = vec![]; let mut po: Vec<(f64, Cand)> = vec![];
        let trunc = |v: &mut Vec<(f64, Cand)>, cap: usize| { v.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap()); v.truncate(cap); };
        for w in (n + 1)..=wmax {
            let mut cv = vec![0.0; m]; let mut tot = 0.0;
            for (j, &(d, a)) in mods.iter().enumerate() { let c = cov(n, d, a, w); if c.over > 0 { let x = c.over as f64 / c.wl as f64; cv[j] = x; tot += x; } }
            if tot < 0.4 { continue; }
            let o = is_osc(n, w);
            if o { po.push((tot, Cand { w, osc: true, cv })); if po.len() > 6000 { trunc(&mut po, 500); } }
            else { ps.push((tot, Cand { w, osc: false, cv })); if ps.len() > 20000 { trunc(&mut ps, 3000); } }
        }
        trunc(&mut ps, 3000); trunc(&mut po, 500);
        let pool: Vec<Cand> = ps.into_iter().chain(po.into_iter()).map(|x| x.1).collect();
        // beam: state = (picks, cumQ, cumO)
        let mut beamv: Vec<(Vec<usize>, Vec<f64>, Vec<f64>)> = vec![(vec![], vec![0.0; m], vec![0.0; m])];
        let mut best_line = String::new(); let mut best_dead = 0usize; let mut viol = false; let mut best_bound_ok = true;
        for lvl in 1..=k {
            let mut next: Vec<(f64, f64, usize, usize)> = vec![];
            for (bi, (pk, cq, co)) in beamv.iter().enumerate() {
                for (pi, c) in pool.iter().enumerate() {
                    if pk.contains(&pi) { continue; }
                    if let Some(x) = force { if lvl <= x && !c.osc { continue; } if lvl > x && c.osc { continue; } }
                    let mut dead = 0.0; let mut sm = 0.0;
                    for j in 0..m { let t = cq[j] + co[j] + c.cv[j]; if t >= 1.0 - 1e-12 { dead += 1.0; } sm += t.min(1.0); }
                    next.push((dead, sm, bi, pi));
                    if next.len() > 400000 { next.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap().then(b.1.partial_cmp(&a.1).unwrap())); next.truncate(20000); }
                }
            }
            next.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap().then(b.1.partial_cmp(&a.1).unwrap()));
            let mut nb: Vec<(Vec<usize>, Vec<f64>, Vec<f64>)> = vec![]; let mut seen = std::collections::HashSet::new();
            for x in next {
                let (pk, cq, co) = &beamv[x.2]; let c = &pool[x.3];
                let mut np = pk.clone(); np.push(x.3); np.sort();
                if seen.insert(np.clone()) {
                    let mut nq = cq.clone(); let mut no = co.clone();
                    for j in 0..m { if c.osc { no[j] += c.cv[j]; } else { nq[j] += c.cv[j]; } }
                    nb.push((np, nq, no)); if nb.len() >= beam { break; }
                }
            }
            beamv = nb;
            // evaluate top states of this level exactly
            for (pk, cq, co) in beamv.iter().take(6) {
                let dead: Vec<(i64, f64)> = (0..m).filter(|&j| cq[j] + co[j] >= 1.0 - 1e-12).map(|j| (mods[j].0, 1.0)).collect();
                let (nd, fd) = max_cop(&dead, true);
                let p = pk.iter().filter(|&&q| !pool[q].osc).count(); let pp = pk.len() - p;
                // chain checks on Fd
                let sq: f64 = fd.iter().map(|d| { let j = mods.iter().position(|x| x.0 == *d).unwrap(); cq[j] }).sum();
                let mut ok = sq <= 8.0 * p as f64 + 1e-9;
                for j in 0..m { if co[j] > 7.0 * pp as f64 / n as f64 + 1e-12 { ok = false; } }
                let lhs = nd * (1.0 - 7.0 * pp as f64 / n as f64);
                if lhs > sq + 1e-9 { ok = false; }
                let mut bound_ok = true;
                if (n as f64) > 7.0 * pp as f64 { let b = 8.0 * p as f64 / (1.0 - 7.0 * pp as f64 / n as f64); if nd > b + 1e-9 { bound_ok = false; } }
                if (n as f64) > 7.0 * k as f64 && nd > 8.0 * k as f64 + 1e-9 { bound_ok = false; }
                if !ok || !bound_ok { viol = true; }
                if (nd as usize) > best_dead || (nd as usize == best_dead && best_line.is_empty()) {
                    best_dead = nd as usize; best_bound_ok = bound_ok && ok;
                    let ws: Vec<String> = pk.iter().map(|&q| format!("{}{}", pool[q].w, if pool[q].osc { "o" } else { "" })).collect();
                    best_line = format!("lvl={} W={{{}}} p={} p'={} deadcop={} sumQ(Fd)={:.3} bound8p/(1-7p'/N)={:.3}", lvl, ws.join(","), p, pp, nd, sq, if (n as f64) > 7.0 * pp as f64 { 8.0 * p as f64 / (1.0 - 7.0 * pp as f64 / n as f64) } else { f64::NAN });
                }
            }
        }
        res.lock().unwrap().push((best_dead, r, best_line, viol || !best_bound_ok));
    }); } });
    let mut v = res.into_inner().unwrap(); v.sort_by(|a, b| b.0.cmp(&a.0));
    let nviol = v.iter().filter(|x| x.3).count();
    let maxdead = v.first().map(|x| x.0).unwrap_or(0);
    println!("DC k={} N={} (|F|>=8k+1 needs N>=8k+3={}) r-count={} max dead coprime windows over r = {} (= {:.2}k; chain/bound violations in {} r-values) ; top: r={} {}", k, n, 8 * k + 3, v.len(), maxdead, maxdead as f64 / k as f64, nviol, v.first().map(|x| x.1).unwrap_or(0), v.first().map(|x| x.2.clone()).unwrap_or_default());
}

// ---------- planted negatives: drop pairwise coprimality ----------
fn cmd_neg(n: i64, wf: i64, nth: usize) {
    // r=1: every D in [N+2,2N-1] valid. S_all(w) and #windows fully covered by the single speed w.
    let mods = moduli(n, 1);
    let ws: Vec<i64> = ((n + 1)..=(wf * n * n)).collect();
    let chunk = 20000usize; let nch = (ws.len() + chunk - 1) / chunk;
    let idx = AtomicUsize::new(0);
    let best = Mutex::new((0.0f64, 0i64, 0usize, 0i64));
    thread::scope(|s| { for _ in 0..nth { s.spawn(|| loop {
        let c = idx.fetch_add(1, Ordering::SeqCst); if c >= nch { break; }
        let (mut bs, mut bw, mut bd, mut bdw) = (0.0f64, 0i64, 0usize, 0i64);
        for &w in &ws[c * chunk..((c + 1) * chunk).min(ws.len())] {
            let mut s = 0.0; let mut dead = 0;
            for &(d, a) in &mods { let cv = cov(n, d, a, w); if cv.over > 0 { s += cv.over as f64 / cv.wl as f64; if cv.over == cv.wl { dead += 1; } } }
            if s > bs { bs = s; bw = w; } if dead > bd { bd = dead; bdw = w; }
        }
        let mut b = best.lock().unwrap();
        if bs > b.0 { b.0 = bs; b.1 = bw; } if bd > b.2 { b.2 = bd; b.3 = bdw; }
    }); } });
    let b = best.into_inner().unwrap();
    println!("NEG1 (no coprimality) N={} r=1 w<={}N^2: max S_all(w)={:.3} at w={} (bound 8 for coprime F); max #windows fully covered by ONE speed = {} at w={}", n, wf, b.0, b.1, b.2, b.3);
}
fn cmd_neg_sieve(n: i64, wf: i64) {
    // divisor-count sieve: for w <= wf*N^2 count D in [N+2,2N-1] dividing w (e=0 windows; each has cov=1 when w<=(2N-1)N)
    let wmax = (wf * n * n) as usize; let mut cnt = vec![0u8; wmax + 1];
    for d in (n + 2)..=(2 * n - 1) { let mut x = d as usize; while x <= wmax { cnt[x] = cnt[x].saturating_add(1); x += d as usize; } }
    let (mut bw, mut bc) = (0usize, 0u8);
    for w in (n as usize + 1)..=wmax { if cnt[w] > bc { bc = cnt[w]; bw = w; } }
    // restrict to cov=1 range w<=(2N-1)N
    let lim = ((2 * n - 1) * n) as usize; let (mut bw1, mut bc1) = (0usize, 0u8);
    for w in (n as usize + 1)..=lim { if cnt[w] > bc1 { bc1 = cnt[w]; bw1 = w; } }
    // verify with exact cov for bw1
    let mods = moduli(n, 1); let mut dead = 0;
    for &(d, a) in &mods { let c = cov(n, d, a, bw1 as i64); if c.over == c.wl { dead += 1; } }
    println!("NEG2 sieve N={} r=1: max #divisors in [N+2,2N-1] for w<={}N^2: {} at w={}; in w<=(2N-1)N: {} at w={}; exact cov check: {} windows fully covered by that single speed w", n, wf, bc, bw, bc1, bw1, dead);
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let nth: usize = env::var("L2_THREADS").ok().and_then(|x| x.parse().ok()).unwrap_or(3);
    match a[1].as_str() {
        "ctl" => cmd_ctl(),
        "lem" => cmd_lem(a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap(), nth),
        "big" => cmd_big(a[2].parse().unwrap(), a[3].parse().unwrap(), &a[4], nth, a[5].parse().unwrap()),
        "exc1" => cmd_exc1(a[2].parse().unwrap(), a[3].parse().unwrap(), nth),
        "dc" => cmd_dc(a[2].parse().unwrap(), a[3].parse().unwrap(), &a[4], a[5].parse().unwrap(), a[6].parse().unwrap(), nth),
        "neg" => cmd_neg(a[2].parse().unwrap(), a[3].parse().unwrap(), nth),
        "negs" => cmd_neg_sieve(a[2].parse().unwrap(), a[3].parse().unwrap()),
        _ => eprintln!("modes: ctl lem big exc1 dc neg negs"),
    }
}
