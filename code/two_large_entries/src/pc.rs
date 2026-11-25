// pc.rs : "Peng corollary" engine, own code. Exact i128 integers/rationals only.
// Serves: the accompanying code Question: for N = 5..30 (3,4 capped), every 1 <= r1 <= N/2, every r1 < r2 <= N,
// every N < w1 < w2 (NO cap on w), which V = ([N] \ {r1,r2}) u {w1,w2} have ML(V) < 1/N ?  (exact value of each, tight = 1/(N+1)).
//
// Method (independent of w2.rs `cert1`):  tau = 1/N.  Good set G(S) = {t in [0,1/2] : ||v t|| >= tau for all v in S}
// = complement of open bands ((kN-1)/(vN), (kN+1)/(vN)); closed pieces with rational endpoints.
//   G0 = G(B), B = [N]\{r1,r2}.  M1 (measure, N >= 5): if l0 = longest piece, any w1,w2 >= W0 = floor(4(N+2)/(N(N-4) l0)) + 1 is good.
//   For w1 < W0: G1 = G(B u {w1}). If G1 has a nondegenerate piece of length l'', every w2 >= ceil(2/(N l'')) is good (M2);
//   the finitely many smaller w2 are tested exactly piece by piece.  If G1 is empty or only points: infinite family in w2,
//   decided by residues of w2 modulo the lcm of the point denominators.
// Modes:  cert N0 N1 | brute N0 N1 WMAX (+compare) | ctl
use std::env;

type F = (i128, i128); // n/d, d > 0
fn lt(a: F, b: F) -> bool { a.0 * b.1 < b.0 * a.1 }
fn le(a: F, b: F) -> bool { a.0 * b.1 <= b.0 * a.1 }
fn gcd(a: i128, b: i128) -> i128 { if b == 0 { a.abs() } else { gcd(b, a % b) } }
fn sub(a: F, b: F) -> F { (a.0 * b.1 - b.0 * a.1, a.1 * b.1) }
fn cdiv(a: i128, b: i128) -> i128 { // ceil(a/b), b>0
    let q = a.div_euclid(b);
    if a.rem_euclid(b) == 0 { q } else { q + 1 }
}

/// open bad bands in t in [0,1/2] of speed v at threshold tp/tq
fn bands(tp: i128, tq: i128, v: i128, out: &mut Vec<(F, F)>) {
    let mut k = 0i128;
    loop {
        // lo = (k tq - tp)/(v tq) ; need lo <= 1/2  <=> 2(k tq - tp) <= v tq
        if 2 * (k * tq - tp) > v * tq { break; }
        out.push(((k * tq - tp, v * tq), (k * tq + tp, v * tq)));
        k += 1;
    }
}

/// closed good pieces in [0,1/2] = complement of the union of the open bands
fn pieces(bs: &mut Vec<(F, F)>) -> Vec<(F, F)> {
    bs.sort_by(|a, b| (a.0 .0 * b.0 .1).cmp(&(b.0 .0 * a.0 .1)));
    let half: F = (1, 2);
    let mut res = Vec::new();
    let mut c: Option<F> = None;
    for &(lo, hi) in bs.iter() {
        match c {
            None => { c = Some(hi); }
            Some(cc) => {
                if le(cc, lo) {
                    if lt(half, cc) { return res; }
                    let end = if lt(half, lo) { half } else { lo };
                    res.push((cc, end));
                }
                if lt(cc, hi) { c = Some(hi); }
            }
        }
    }
    if let Some(cc) = c { if le(cc, half) { res.push((cc, half)); } }
    res
}

fn good_set(speeds: &[i128], tp: i128, tq: i128) -> Vec<(F, F)> {
    let mut bs = Vec::new();
    for &v in speeds { bands(tp, tq, v, &mut bs); }
    pieces(&mut bs)
}

/// does the closed piece [a,b] contain a t with ||w t|| >= 1/N ?  (tp=1, tq=N general tp ok)
fn piece_has_good(a: F, b: F, w: i128, tp: i128, tq: i128) -> bool {
    // good intervals of w: [(k tq + tp)/(w tq), ((k+1) tq - tp)/(w tq)].
    // smallest k with ((k+1) tq - tp) >= a * w * tq :  (k+1) tq >= tp + a w tq
    // a = an/ad : k+1 >= ceil((tp*ad + an*w*tq)/(tq*ad))
    let k1 = cdiv(tp * a.1 + a.0 * w * tq, tq * a.1);
    let k = k1 - 1;
    // need (k tq + tp)/(w tq) <= b  <=> (k tq + tp) * bd <= bn * w * tq
    (k * tq + tp) * b.1 <= b.0 * w * tq
}

fn any_piece_good(ps: &[(F, F)], w: i128, tp: i128, tq: i128) -> bool {
    ps.iter().any(|&(a, b)| piece_has_good(a, b, w, tp, tq))
}

/// exact ML via candidate times k/L, L = v_i+v_j, every numerator (project standard, ml_standard.py twin)
fn ml_exact(v: &[i128]) -> (i128, i128) {
    let mut ls: Vec<i128> = Vec::new();
    for i in 0..v.len() { for j in i..v.len() { ls.push(v[i] + v[j]); } }
    ls.sort(); ls.dedup();
    let (mut bn, mut bd) = (0i128, 1i128);
    for &l in &ls {
        for k in 0..=(l / 2) {
            let mut m = i128::MAX;
            for &a in v {
                let x = (a * k) % l;
                let d = if x < l - x { x } else { l - x };
                if d < m { m = d; if m * bd <= bn * l { break; } }
            }
            if m * bd > bn * l { bn = m; bd = l; }
        }
    }
    let g = gcd(bn, bd);
    (bn / g, bd / g)
}

fn cls(n: i128, ml: (i128, i128)) -> &'static str {
    // compare ml with 1/(n+1)
    let c = ml.0 * (n + 1);
    if c == ml.1 { "TIGHT" } else if c < ml.1 { "BELOW" } else { "ABOVE" }
}

struct Exc { r1: i128, r2: i128, w1: i128, w2: i128 }

fn base(n: i128, r1: i128, r2: i128) -> Vec<i128> { (1..=n).filter(|&x| x != r1 && x != r2).collect() }

/// engine for one (N,r1,r2). Appends sets with ML<1/N (no cap on w). Families printed. Returns (status string).
fn cert_one(n: i128, r1: i128, r2: i128, exc: &mut Vec<Exc>, fams: &mut Vec<String>, wcap: i128) -> String {
    let b = base(n, r1, r2);
    let g0 = good_set(&b, 1, n);
    if g0.is_empty() { return format!("ALL(B has ML<1/N)"); }
    let mut l0: F = (0, 1);
    for &(a, c) in &g0 { let d = sub(c, a); if lt(l0, d) { l0 = d; } }
    if l0.0 == 0 { return format!("POINT0(G0 points only: {} pieces)", g0.len()); }
    // W0 = floor(4(N+2) ld / (N (N-4) ln)) + 1
    let w0 = (4 * (n + 2) * l0.1) / (n * (n - 4) * l0.0) + 1;
    if w0 > wcap { return format!("UNRESOLVED W0={}", w0); }
    let mut bs0 = Vec::new();
    for &v in &b { bands(1, n, v, &mut bs0); }
    let mut status = format!("ok W0={}", w0);
    let mut maxb2 = 0i128;
    for w1 in (n + 1)..w0 {
        let mut bs = bs0.clone();
        bands(1, n, w1, &mut bs);
        let g1 = pieces(&mut bs);
        if g1.is_empty() {
            fams.push(format!("FAM N={} r1={} r2={} w1={} ALL w2>{} (B u {{w1}} has ML<1/N)", n, r1, r2, w1, w1));
            continue;
        }
        let mut l1: F = (0, 1);
        for &(a, c) in &g1 { let d = sub(c, a); if lt(l1, d) { l1 = d; } }
        if l1.0 == 0 {
            // points only: family in w2 by residues modulo lcm of reduced denominators
            let mut l: i128 = 1;
            let mut pts: Vec<F> = Vec::new();
            for &(a, _) in &g1 { let g = gcd(a.0, a.1); pts.push((a.0 / g, a.1 / g)); }
            for p in &pts { let g = gcd(l, p.1); l = l / g * p.1; if l > 20_000_000 { status = format!("UNRESOLVED lcm>2e7 at w1={}", w1); break; } }
            if l > 20_000_000 { continue; }
            let mut res = Vec::new();
            for c in 0..l {
                let ok = pts.iter().all(|p| {
                    let x = (c * p.0).rem_euclid(p.1);
                    let d = if x < p.1 - x { x } else { p.1 - x };
                    d * n < p.1 // ||c p|| < 1/N
                });
                if ok { res.push(c); }
            }
            if !res.is_empty() {
                fams.push(format!("FAM N={} r1={} r2={} w1={} w2 = c mod {} for c in {:?} (w2>{}), points={:?}", n, r1, r2, w1, l, res, w1, pts));
            }
            continue;
        }
        // nondegenerate: w2 >= B2 = ceil(2 ld/(N ln)) all good
        let b2 = cdiv(2 * l1.1, n * l1.0);
        if b2 > maxb2 { maxb2 = b2; }
        if b2 > wcap { status = format!("UNRESOLVED B2={} at w1={}", b2, w1); continue; }
        for w2 in (w1 + 1)..b2 {
            if !any_piece_good(&g1, w2, 1, n) { exc.push(Exc { r1, r2, w1, w2 }); }
        }
    }
    format!("{} maxB2={}", status, maxb2)
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let mode = a.get(1).map(|s| s.as_str()).unwrap_or("");
    match mode {
        "ctl" => ctl(),
        "cert" => {
            let n0: i128 = a[2].parse().unwrap();
            let n1: i128 = a[3].parse().unwrap();
            let wcap: i128 = a.get(4).map(|s| s.parse().unwrap()).unwrap_or(2_000_000);
            for n in n0..=n1 { run_cert(n, wcap, true); }
        }
        "brute" => {
            let n0: i128 = a[2].parse().unwrap();
            let n1: i128 = a[3].parse().unwrap();
            let wmax: i128 = a[4].parse().unwrap();
            for n in n0..=n1 { run_brute(n, wmax); }
        }
        "low" => {
            // N = 3,4 only: CAPPED scan (UNRESOLVED beyond the cap), all r1<=N/2, r2, N<w1<w2<=WMAX
            let n: i128 = a[2].parse().unwrap();
            let wmax: i128 = a[3].parse().unwrap();
            let mut tot = 0; let mut tight = 0; let mut below = 0; let mut r1one = 0; let mut r1one_tight = 0; let mut shown = 0;
            for r1 in 1..=(n / 2) { for r2 in (r1 + 1)..=n { for w1 in (n + 1)..wmax { for w2 in (w1 + 1)..=wmax {
                let mut v = base(n, r1, r2); v.push(w1); v.push(w2);
                if !ml_ge(&v, n) {
                    tot += 1; let ml = ml_exact(&v); let c = cls(n, ml);
                    if c == "TIGHT" { tight += 1; } if c == "BELOW" { below += 1; }
                    if r1 == 1 { r1one += 1; if c != "ABOVE" { r1one_tight += 1; } }
                    if c != "ABOVE" && shown < 25 { println!("LOW N={} r1={} r2={} w1={} w2={} ML={}/{} {}", n, r1, r2, w1, w2, ml.0, ml.1, c); shown += 1; }
                }
            } } } }
            println!("LOWSUMMARY N={} CAPPED wmax={} exceptions(ML<1/N)={} tight={} below={} | r1=1: {} of which ML<=1/(N+1): {}", n, wmax, tot, tight, below, r1one, r1one_tight);
        }
        _ => eprintln!("usage: pc ctl | cert N0 N1 [wcap] | brute N0 N1 WMAX"),
    }
}

fn run_cert(n: i128, wcap: i128, print: bool) -> (Vec<Exc>, Vec<String>) {
    let mut exc = Vec::new();
    let mut fams = Vec::new();
    let mut flagged = 0;
    let mut pairs = 0;
    let mut sts: Vec<String> = Vec::new();
    for r1 in 1..=(n / 2) {
        for r2 in (r1 + 1)..=n {
            pairs += 1;
            let s = cert_one(n, r1, r2, &mut exc, &mut fams, wcap);
            if !s.starts_with("ok") { flagged += 1; sts.push(format!("  STATUS N={} r1={} r2={}: {}", n, r1, r2, s)); }
        }
    }
    if print {
        println!("CERT N={} triples(r1<=N/2,r2)={} flagged_not_ok={} exceptions(finite list)={} families={}", n, pairs, flagged, exc.len(), fams.len());
        for s in &sts { println!("{}", s); }
        for f in &fams {
            println!("{}", f);
            // sample ML of family members (w2 <= 3000): distinct values, tight count
            if let Some(p) = f.find("w2 = c mod ") {
                let head = &f[..p];
                let grab = |key: &str| -> i128 { let i = head.find(key).unwrap() + key.len(); head[i..].split(' ').next().unwrap().parse().unwrap() };
                let (fr1, fr2, fw1) = (grab("r1="), grab("r2="), grab("w1="));
                let rest = &f[p + 11..];
                let l: i128 = rest.splitn(2, ' ').next().unwrap().parse().unwrap();
                let lb = rest.find('[').unwrap(); let rb = rest.find(']').unwrap();
                let cs: Vec<i128> = rest[lb + 1..rb].split(',').filter(|s| !s.trim().is_empty()).map(|s| s.trim().parse().unwrap()).collect();
                let mut vals: Vec<(i128, i128)> = Vec::new(); let mut cnt = 0; let mut tight = 0; let mut mn = (1i128, 1i128); let mut mx = (0i128, 1i128);
                for w2 in (fw1 + 1)..=3000 {
                    if !cs.contains(&(w2 % l)) { continue; }
                    let mut v = base(n, fr1, fr2); v.push(fw1); v.push(w2);
                    let ml = ml_exact(&v); cnt += 1;
                    if cls(n, ml) == "TIGHT" { tight += 1; }
                    if ml.0 * mn.1 < mn.0 * ml.1 { mn = ml; }
                    if ml.0 * mx.1 > mx.0 * ml.1 { mx = ml; }
                    if !vals.contains(&ml) && vals.len() < 12 { vals.push(ml); }
                }
                println!("   FAMML members(w2<=3000)={} tight={} min={}/{} max={}/{} (max vs 1/N: {}) first_values={:?}", cnt, tight, mn.0, mn.1, mx.0, mx.1, if mx.0 * n < mx.1 { "all < 1/N" } else { "NOT all < 1/N: BUG" }, vals);
            }
        }
        let cap = 60usize;
        let mut tight = 0; let mut below = 0;
        let mut shown = 0;
        for e in &exc {
            let mut v = base(n, e.r1, e.r2); v.push(e.w1); v.push(e.w2);
            let ml = ml_exact(&v);
            let c = cls(n, ml);
            if c == "TIGHT" { tight += 1; }
            if c == "BELOW" { below += 1; }
            if shown < cap || c != "ABOVE" { println!("EXC N={} r1={} r2={} w1={} w2={} ML={}/{} {}", n, e.r1, e.r2, e.w1, e.w2, ml.0, ml.1, c); shown += 1; }
        }
        let mut r1one = 0; let mut r1one_tight = 0;
        for e in &exc { if e.r1 == 1 { r1one += 1; let mut v = base(n, e.r1, e.r2); v.push(e.w1); v.push(e.w2); let ml = ml_exact(&v); if cls(n, ml) != "ABOVE" { r1one_tight += 1; } } }
        println!("SUMMARY N={} exceptions={} tight(=1/(N+1))={} below(<1/(N+1))={} | r1=1: exceptions(ML<1/N)={} of which ML<=1/(N+1): {}", n, exc.len(), tight, below, r1one, r1one_tight);
    }
    (exc, fams)
}

fn run_brute(n: i128, wmax: i128) {
    // brute: every (r1<=N/2, r2, N<w1<w2<=wmax); ML >= 1/N decided by candidate times with early exit; compare with engine
    let (exc, fams) = run_cert(n, 2_000_000, false);
    let mut eng: std::collections::BTreeSet<(i128, i128, i128, i128)> = Default::default();
    for e in &exc { if e.w2 <= wmax { eng.insert((e.r1, e.r2, e.w1, e.w2)); } }
    // expand families up to wmax: ALL and residue families
    let mut famcount = 0usize;
    // (families are re-derived inside brute comparison by direct check; here we only need engine's finite list for non-family w1)
    for f in &fams { let _ = f; famcount += 1; }
    let mut br: std::collections::BTreeSet<(i128, i128, i128, i128)> = Default::default();
    for r1 in 1..=(n / 2) {
        for r2 in (r1 + 1)..=n {
            let b = base(n, r1, r2);
            // candidate list of L depends on the pair; do generic ML>=1/N test via good_set (independent of ml_exact)
            for w1 in (n + 1)..wmax {
                for w2 in (w1 + 1)..=wmax {
                    let mut v = b.clone(); v.push(w1); v.push(w2);
                    // brute decision by candidate times (early exit): exists candidate t with all ||vt||>=1/N ?
                    if !ml_ge(&v, n) { br.insert((r1, r2, w1, w2)); }
                }
            }
        }
    }
    // families: members of families (w1 with FAM) are in brute but not in eng; account for them
    let only_brute: Vec<_> = br.difference(&eng).cloned().collect();
    let only_eng: Vec<_> = eng.difference(&br).cloned().collect();
    // explain only_brute by families: collect w1 / residues from fams
    let mut explained = 0usize;
    let mut unexplained: Vec<(i128, i128, i128, i128)> = Vec::new();
    for &(r1, r2, w1, w2) in &only_brute {
        let tag = format!("N={} r1={} r2={} w1={} ", n, r1, r2, w1);
        let mut ok = false;
        for f in &fams {
            if f.starts_with(&format!("FAM {}", tag.trim_end())) || f.starts_with(&format!("FAM {}", tag)) {
                if f.contains("ALL") { ok = true; }
                else {
                    // parse "w2 = c mod L for c in [..]"
                    if let Some(p) = f.find("w2 = c mod ") {
                        let rest = &f[p + 11..];
                        let sp: Vec<&str> = rest.splitn(2, ' ').collect();
                        let l: i128 = sp[0].parse().unwrap();
                        let lb = rest.find('[').unwrap(); let rb = rest.find(']').unwrap();
                        let cs: Vec<i128> = rest[lb + 1..rb].split(',').filter(|s| !s.trim().is_empty()).map(|s| s.trim().parse().unwrap()).collect();
                        if cs.contains(&(w2 % l)) { ok = true; }
                    }
                }
            }
        }
        if ok { explained += 1; } else { unexplained.push((r1, r2, w1, w2)); }
    }
    println!("BRUTE N={} wmax={} brute_exceptions={} engine_finite_exceptions(w2<=wmax)={} families={} only_brute_explained_by_family={} only_brute_UNEXPLAINED={} only_engine={}", n, wmax, br.len(), eng.len(), famcount, explained, unexplained.len(), only_eng.len());
    for u in unexplained.iter().take(10) { println!("  UNEXPLAINED {:?}", u); }
    for u in only_eng.iter().take(10) { println!("  ONLY_ENGINE {:?}", u); }
}

/// ML(v) >= 1/N ?  via candidate times, early exit
fn ml_ge(v: &[i128], n: i128) -> bool {
    let mut ls: Vec<i128> = Vec::new();
    for i in 0..v.len() { for j in i..v.len() { ls.push(v[i] + v[j]); } }
    ls.sort(); ls.dedup();
    for &l in &ls {
        'k: for k in 0..=(l / 2) {
            for &a in v {
                let x = (a * k) % l;
                let d = if x < l - x { x } else { l - x };
                if d * n < l { continue 'k; }
            }
            return true;
        }
    }
    false
}

fn ctl() {
    let mut fails = 0;
    let mut chk = |name: &str, v: Vec<i128>, e: (i128, i128)| {
        let r = ml_exact(&v);
        // independent: interval method at tau = r (must have good set) and at tau slightly above (must be empty)
        let g_at = good_set(&v, r.0, r.1);
        let up = (r.0 * 1000 + 1, r.1 * 1000);
        let g_up = good_set(&v, up.0, up.1);
        let ok = r == e && !g_at.is_empty() && g_up.is_empty();
        if !ok { fails += 1; }
        println!("CTL {} ML={}/{} expected {}/{} interval_at={} interval_above_empty={} {}", name, r.0, r.1, e.0, e.1, !g_at.is_empty(), g_up.is_empty(), if ok { "OK" } else { "FAIL" });
    };
    chk("Zhang tight one-entry (n=3,r=1,w=4): [2]_{1->4}={2,4}", vec![2, 4], (1, 3));
    chk("Peng 5.3 doubled {2,4,6,8}=[4]\\{1,3}+{6,8}", vec![2, 4, 6, 8], (1, 5));
    chk("[5]\\{1,3,5}+... {2,4,6,8,10}", vec![2, 4, 6, 8, 10], (1, 6));
    chk("N=3 [3]\\{1,3}+{4,6}={2,4,6}", vec![2, 4, 6], (1, 4));
    chk("N=13 exception (13;6,10;20,69)", { let mut v = base(13, 6, 10); v.push(20); v.push(69); v }, (3, 40));
    chk("N=8 (8;2,3;11,13)", { let mut v = base(8, 2, 3); v.push(11); v.push(13); v }, (2, 17));
    chk("N=8 (8;2,8;11,32)", { let mut v = base(8, 2, 8); v.push(11); v.push(32); v }, (4, 33));
    chk("N=12 (12;4,6;17,19)", { let mut v = base(12, 4, 6); v.push(17); v.push(19); v }, (2, 25));
    chk("Wills T1 {1,3,4,7}", vec![1, 3, 4, 7], (1, 5));
    chk("[8]", (1..=8).collect(), (1, 9));
    chk("{1,2,3,4,5,7,12}", vec![1, 2, 3, 4, 5, 7, 12], (1, 8));
    chk("{1,4,5,6,7,11,13}", vec![1, 4, 5, 6, 7, 11, 13], (1, 8));
    chk("Zhang Example 5.2 (73;70,72;140,144)", { let mut v = base(73, 70, 72); v.push(140); v.push(144); v }, (1, 74));
    // random two-method agreement: ML_exact vs interval method at the value and just above
    let mut seed: u64 = 20261125;
    let mut rnd = |m: u64| -> i128 { seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); ((seed >> 33) % m) as i128 };
    let mut bad = 0; let trials = 3000;
    for _ in 0..trials {
        let k = 2 + rnd(5) as usize;
        let mut v: Vec<i128> = Vec::new();
        while v.len() < k { let x = 1 + rnd(40); if !v.contains(&x) { v.push(x); } }
        let r = ml_exact(&v);
        let g_at = good_set(&v, r.0, r.1);
        let up = (r.0 * 1000 + 1, r.1 * 1000);
        let g_up = good_set(&v, up.0, up.1);
        if g_at.is_empty() || !g_up.is_empty() { bad += 1; }
    }
    println!("CTL random {} sets: ML_exact vs interval-method mismatches = {}", trials, bad);
    // engine negative control: cert at N=13 must contain the planted exception; at N=14 none for r1<=N/2
    let (e13, _) = run_cert(13, 2_000_000, false);
    let has = e13.iter().any(|e| e.r1 == 6 && e.r2 == 10 && e.w1 == 20 && e.w2 == 69);
    println!("CTL engine N=13 contains planted (13;6,10;20,69): {} ({} exceptions)", has, e13.len());
    let (e14, _) = run_cert(14, 2_000_000, false);
    println!("CTL engine N=14: exceptions r1<=N/2 = {} (expected 0)", e14.len());
    if fails > 0 || bad > 0 || !has || !e14.is_empty() { println!("CTL RESULT: FAIL"); } else { println!("CTL RESULT: PASS"); }
}
