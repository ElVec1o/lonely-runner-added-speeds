// the accompanying code engine (own code, exact integers). Two-entry sets V = ([N] \ {r1,r2}) u {w1,w2}.
// ML(V) = max_t min_v ||t v||.  tau = p/q.  All quantities exact (i128 fractions).
// Method A (gap engine): good_pieces(V,p,q) = closed pieces of {t in [0,1/2] : ||v t|| >= tau for all v}
//   = complement of the union of the OPEN bands ((kq-p)/(vq),(kq+p)/(vq)).  ML(V) >= tau iff pieces nonempty.
// Method B (exact ML): candidates t = k/(vi+vj), 0<k<=(vi+vj)/2, value min_v ||v t||, maximised exactly.
// Units: N number of speeds; tau rational; times are rationals in [0,1/2].
use std::cmp::Ordering;
use std::env;
type I = i128;

#[derive(Clone, Copy, Debug)]
struct Fr { n: I, d: I } // d > 0
fn fr(n: I, d: I) -> Fr { Fr { n, d } }
fn cmpf(a: Fr, b: Fr) -> Ordering { (a.n * b.d).cmp(&(b.n * a.d)) }
fn gcd(a: I, b: I) -> I { if b == 0 { a.abs() } else { gcd(b, a % b) } }
fn ceil_div(a: I, b: I) -> I { // b>0
    -((-a).div_euclid(b))
}
fn red(a: Fr) -> Fr { let g = gcd(a.n, a.d).max(1); fr(a.n / g, a.d / g) }

// good pieces of the speeds in `vs` at tau=p/q, inside [0,1/2]
fn good_pieces(vs: &[i64], p: I, q: I) -> Vec<(Fr, Fr)> {
    let mut bands: Vec<(Fr, Fr)> = Vec::new();
    for &v in vs {
        let v = v as I;
        let mut k: I = 0;
        loop {
            // lo=(kq-p)/(vq); stop when lo >= 1/2 : 2(kq-p) >= vq
            if 2 * (k * q - p) >= v * q { break; }
            bands.push((fr(k * q - p, v * q), fr(k * q + p, v * q)));
            k += 1;
        }
    }
    bands.sort_by(|a, b| cmpf(a.0, b.0));
    let half = fr(1, 2);
    let mut out = Vec::new();
    if bands.is_empty() { out.push((fr(0, 1), half)); return out; }
    let mut h = bands[0].1;
    // the first band has lo<0 (k=0 band of every speed), so t=0 is bad
    for b in bands.iter().skip(1) {
        if cmpf(b.0, h) == Ordering::Less { if cmpf(b.1, h) == Ordering::Greater { h = b.1; } }
        else {
            // piece [h, b.0] clipped to 1/2
            if cmpf(h, half) != Ordering::Greater {
                let r = if cmpf(b.0, half) == Ordering::Greater { half } else { b.0 };
                out.push((h, r));
            }
            h = b.1;
        }
    }
    if cmpf(h, half) != Ordering::Greater { out.push((h, half)); }
    out
}

// subtract the bad bands of speed w from pieces: returns pieces where ||w t|| >= tau
fn sub_speed(pc: &[(Fr, Fr)], w: I, p: I, q: I) -> Vec<(Fr, Fr)> {
    let mut out = Vec::new();
    for &(a, b) in pc {
        // smallest j with ((j+1)q-p)/(wq) >= a : j >= (a w q + p)/q - 1
        let j0 = ceil_div(a.n * w * q + p * a.d - q * a.d, a.d * q);
        let mut j = j0;
        loop {
            let lo = fr(j * q + p, w * q);
            if cmpf(lo, b) == Ordering::Greater { break; }
            let hi = fr((j + 1) * q - p, w * q);
            let l2 = if cmpf(lo, a) == Ordering::Less { a } else { lo };
            let h2 = if cmpf(hi, b) == Ordering::Greater { b } else { hi };
            if cmpf(l2, h2) != Ordering::Greater { out.push((l2, h2)); }
            j += 1;
        }
    }
    out
}

fn has_good(pc: &[(Fr, Fr)], w: I, p: I, q: I) -> bool {
    for &(a, b) in pc {
        let j0 = ceil_div(a.n * w * q + p * a.d - q * a.d, a.d * q);
        // lo=(j0 q+p)/(w q) <= b
        if (j0 * q + p) * b.d <= b.n * w * q { return true; }
    }
    false
}

fn len(a: Fr, b: Fr) -> Fr { red(fr(b.n * a.d - a.n * b.d, a.d * b.d)) }

// exact ML via candidate times (method B)
fn ml_exact(vs: &[i64]) -> Fr {
    let mut best = fr(0, 1);
    let mut seen = std::collections::HashSet::new();
    for i in 0..vs.len() {
        for j in i..vs.len() {
            let d = (vs[i] + vs[j]) as I;
            if !seen.insert(d) { continue; }
            let mut k: I = 1;
            while 2 * k <= d {
                // min_v ||v k/d||
                let mut m = d; // numerator of min, denominator d
                for &v in vs {
                    let r = (k * v as I) % d;
                    let x = if r < d - r { r } else { d - r };
                    if x < m { m = x; if m * best.d <= best.n * d { break; } }
                }
                if m * best.d > best.n * d { best = fr(m, d); }
                k += 1;
            }
        }
    }
    red(best)
}

fn witnessed(n: I, r: I, w1: I, w2: I) -> bool {
    // Lemma W: D in [n+1+r, 2n], gcd(D,r)=1, w1,w2 not in {0,r,-r} mod D  => ML >= 2/D >= 1/n
    let mut d = n + 1 + r;
    while d <= 2 * n {
        if gcd(d, r) == 1 {
            let a = w1 % d; let b = w2 % d;
            let ok = |x: I| x != 0 && x != r % d && x != (d - r % d) % d;
            if ok(a) && ok(b) { return true; }
        }
        d += 1;
    }
    false
}

fn set_of(n: i64, r1: i64, r2: i64, w1: i64, w2: i64) -> Vec<i64> {
    let mut v: Vec<i64> = (1..=n).filter(|&x| x != r1 && x != r2).collect();
    v.push(w1); v.push(w2); v
}

fn show(f: Fr) -> String { let g = red(f); format!("{}/{}", g.n, g.d) }

// tiny xorshift
struct Rng(u64);
impl Rng { fn next(&mut self) -> u64 { let mut x = self.0; x ^= x << 13; x ^= x >> 7; x ^= x << 17; self.0 = x; x }
    fn below(&mut self, m: u64) -> u64 { self.next() % m } }

fn main() {
    let a: Vec<String> = env::args().collect();
    let cmd = a.get(1).map(|s| s.as_str()).unwrap_or("");
    match cmd {
        "ctl" => ctl(),
        "grid" => grid(a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap(), a.get(5).map(|s| s.parse().unwrap()).unwrap_or(1)),
        "loggrid" => loggrid(a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap(), a[5].parse().unwrap()),
        "proofsim" => proofsim(a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap()),
        "k12check" => k12check(a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap()),
        "theta" => theta(a[2].parse().unwrap(), a[3].parse().unwrap()),
        "cert1" => cert1(a[2].parse().unwrap(), a[3].parse().unwrap()),
        "ml" => { // ml N r1 r2 w1 w2
            let v = set_of(a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap(), a[5].parse().unwrap(), a[6].parse().unwrap());
            println!("ML = {}", show(ml_exact(&v)));
        }
        _ => eprintln!("usage"),
    }
}

// negative controls
fn ctl() {
    let fails = std::cell::Cell::new(0);
    let chk = |name: &str, v: Vec<i64>, val: (I, I)| {
        let (p, q) = val;
        let ge = !good_pieces(&v, p, q).is_empty();
        let up = !good_pieces(&v, p * 1000003 + 1, q * 1000003).is_empty();
        let dn = !good_pieces(&v, p * 1000003 - 1, q * 1000003).is_empty();
        let mb = ml_exact(&v);
        let okb = mb.n * q == p * mb.d;
        let ok = ge && !up && dn && okb;
        println!("ctl {} ML={}/{} ge={} ge(+eps)={} ge(-eps)={} methodB={} {}", name, p, q, ge, up, dn, show(mb), if ok { "OK" } else { "FAIL" });
        if !ok { fails.set(fails.get() + 1); }
    };
    // planted: Zhang Example 5.2 N=73 {70,72}->{140,144}: tight, ML=1/74
    chk("N73 R{70,72} W{140,144}", set_of(73, 70, 72, 140, 144), (1, 74));
    // reference list, N,(r1,r2;w1,w2); values computed by method B inside chk must equal; supply expected values below
    for (n, r1, r2, w1, w2) in [(8, 2, 3, 11, 13), (8, 2, 8, 11, 32), (8, 3, 4, 11, 13), (12, 4, 6, 17, 19), (13, 6, 10, 20, 69)] {
        let v = set_of(n, r1, r2, w1, w2);
        let m = ml_exact(&v);
        let lt = m.n * (n as I) < m.d; // ML < 1/N
        let up = !good_pieces(&v, m.n * 1000003 + 1, m.d * 1000003).is_empty();
        let ge = !good_pieces(&v, m.n, m.d).is_empty();
        let ok = lt && ge && !up;
        println!("ctl planted N={} R=({},{}) W=({},{}) ML={} ML<1/N:{} {}", n, r1, r2, w1, w2, show(m), lt, if ok { "OK" } else { "FAIL" });
        if !ok { fails.set(fails.get() + 1); }
    }
    // Wills sets {1,3,4,7}=1/5, [8]=1/9
    chk("T1", vec![1, 3, 4, 7], (1, 5));
    chk("[8]", (1..=8).collect(), (1, 9));
    chk("{1,4,5,6,7,11,13}", vec![1, 4, 5, 6, 7, 11, 13], (1, 8));
    // random A vs B
    let mut rng = Rng(88172645463325252);
    let mut mism = 0; let tot = 3000;
    for _ in 0..tot {
        let k = 3 + rng.below(8) as usize;
        let mut v: Vec<i64> = Vec::new();
        while v.len() < k { let x = 1 + rng.below(70) as i64; if !v.contains(&x) { v.push(x); } }
        let m = ml_exact(&v);
        let ge = !good_pieces(&v, m.n, m.d).is_empty();
        let up = !good_pieces(&v, m.n * 1000003 + 1, m.d * 1000003).is_empty();
        let dn = !good_pieces(&v, m.n * 1000003 - 1, m.d * 1000003).is_empty();
        if !(ge && !up && dn) { mism += 1; }
    }
    println!("ctl random A-vs-B sets={} mismatches={}", tot, mism);
    // sweep consistency: has_good / sub_speed vs full good_pieces on random two-entry sets
    let mut m2 = 0; let mut t2 = 0;
    for _ in 0..4000 {
        let n = 6 + rng.below(20) as i64;
        let r1 = 1 + rng.below(n as u64) as i64; let mut r2 = 1 + rng.below(n as u64) as i64; if r2 == r1 { r2 = if r1 == n { 1 } else { r1 + 1 }; }
        let w1 = n + 1 + rng.below(60) as i64; let mut w2 = n + 1 + rng.below(200) as i64; if w1 == w2 { w2 += 1; }
        let ret: Vec<i64> = (1..=n).filter(|&x| x != r1 && x != r2).collect();
        let g0 = good_pieces(&ret, 1, n as I);
        let g1 = sub_speed(&g0, w1 as I, 1, n as I);
        let sweep = has_good(&g1, w2 as I, 1, n as I);
        let full = !good_pieces(&set_of(n, r1, r2, w1, w2), 1, n as I).is_empty();
        // also witness consistency
        let wt = witnessed(n as I, r1 as I, w1 as I, w2 as I) || witnessed(n as I, r2 as I, w1 as I, w2 as I);
        t2 += 1;
        if sweep != full || (wt && !full) { m2 += 1; }
    }
    println!("ctl sweep-vs-full + witness-implies-ge sets={} mismatches={}", t2, m2);
    println!("CTL TOTAL FAILS = {}", fails.get() + mism + m2);
}

// full grid: all N in [n0,n1], all 1<=r1<r2<=N, N<w1<w2<=wmax; report every set with ML<1/N.
// rfilter: 1 = all r1; 2 = only r1 <= N/2
fn grid(n0: i64, n1: i64, wmax: i64, rfilter: i64) {
    for n in n0..=n1 {
        let nn = n as I;
        let mut total: u64 = 0; let mut wit: u64 = 0; let mut sweep: u64 = 0; let mut exc_low: Vec<String> = Vec::new(); let mut exc_hi = 0u64; let mut min_r1_exc = i64::MAX;
        let mut exc_hi_list: Vec<String> = Vec::new();
        for r1 in 1..n {
            if rfilter == 2 && 2 * r1 > n { break; }
            let nr2 = (n - r1) as usize;
            let g0s: Vec<Vec<(Fr, Fr)>> = ((r1 + 1)..=n).map(|r2| { let ret: Vec<i64> = (1..=n).filter(|&x| x != r1 && x != r2).collect(); good_pieces(&ret, 1, nn) }).collect();
            for w1 in (n + 1)..wmax {
                let mut g1s: Vec<Option<Vec<(Fr, Fr)>>> = vec![None; nr2];
                for w2 in (w1 + 1)..=wmax {
                    total += nr2 as u64;
                    if witnessed(nn, r1 as I, w1 as I, w2 as I) { wit += nr2 as u64; continue; }
                    for (k, r2) in ((r1 + 1)..=n).enumerate() {
                        if witnessed(nn, r2 as I, w1 as I, w2 as I) { wit += 1; continue; }
                        if g1s[k].is_none() { g1s[k] = Some(sub_speed(&g0s[k], w1 as I, 1, nn)); }
                        sweep += 1;
                        if !has_good(g1s[k].as_ref().unwrap(), w2 as I, 1, nn) {
                            let ml = ml_exact(&set_of(n, r1, r2, w1, w2));
                            let s = format!("({};{},{};{},{}) ML={}", n, r1, r2, w1, w2, show(ml));
                            if 2 * r1 <= n { exc_low.push(s); } else { exc_hi += 1; if exc_hi_list.len() < 400 { exc_hi_list.push(s); } }
                            if r1 < min_r1_exc { min_r1_exc = r1; }
                        }
                    }
                }
            }
        }
        println!("GRID N={} wmax={} sets={} witnessed={} swept={} | ML<1/N with r1<=N/2: {} | with r1>N/2: {} | min r1 among exceptions: {}", n, wmax, total, wit, sweep, exc_low.len(), exc_hi, if min_r1_exc == i64::MAX { -1 } else { min_r1_exc });
        for s in &exc_low { println!("  LOW {}", s); }
        for s in &exc_hi_list { println!("  HI  {}", s); }
    }
}

// w1 <= w1max (full), w2 on a geometric grid up to wcap (ratio ~1.03) plus structured neighbours
fn loggrid(n0: i64, n1: i64, w1max: i64, wcap: i64) {
    for n in n0..=n1 {
        let nn = n as I;
        let mut total: u64 = 0; let mut exc = 0u64; let mut exc_low: Vec<String> = Vec::new();
        for r1 in 1..n {
            if 2 * r1 > n { break; }
            for r2 in (r1 + 1)..=n {
                let ret: Vec<i64> = (1..=n).filter(|&x| x != r1 && x != r2).collect();
                let g0 = good_pieces(&ret, 1, nn);
                for w1 in (n + 1)..=w1max {
                    let g1 = sub_speed(&g0, w1 as I, 1, nn);
                    let mut w2f = (w1 + 1) as f64;
                    let mut w2 = w1 + 1;
                    while w2 <= wcap {
                        for dw in 0..3 {
                            let x = w2 + dw;
                            if x <= w1 || x > wcap { continue; }
                            total += 1;
                            if !has_good(&g1, x as I, 1, nn) {
                                exc += 1;
                                if exc_low.len() < 50 { exc_low.push(format!("({};{},{};{},{})", n, r1, r2, w1, x)); }
                            }
                        }
                        w2f = (w2f * 1.03).max(w2f + 1.0);
                        w2 = w2f as i64;
                    }
                }
            }
        }
        println!("LOGGRID N={} w1<={} w2 geometric<= {} tests={} ML<1/N (r1<=N/2): {}", n, w1max, wcap, total, exc);
        for s in &exc_low { println!("  EXC {}", s); }
    }
}

// certified-complete (all w) for V' = ([N] \ {r1}) u {w1,w2} at tau=1/N, then r2-specific test of unresolved pairs.
fn cert1(n0: i64, n1: i64) {
    for n in n0..=n1 {
        let nn = n as I;
        let mut agg_unres: u64 = 0; let mut agg_exc: u64 = 0; let mut max_w0: I = 0; let mut flagged = 0u64; let mut pairs_n = 0u64;
        let mut exc_list: Vec<String> = Vec::new(); let mut max_w2_explicit: I = 0;
        for r1 in 1..=(n / 2) {
            pairs_n += 1;
            let ret: Vec<i64> = (1..=n).filter(|&x| x != r1).collect();
            let g0 = good_pieces(&ret, 1, nn);
            if g0.is_empty() { println!("  N={} r1={} G0' EMPTY (V' has ML<1/N for all w; r2-specific needed for ALL)", n, r1); flagged += 1; continue; }
            // longest piece l = a/b
            let mut l = fr(0, 1);
            for &(a, b) in &g0 { let x = len(a, b); if cmpf(x, l) == Ordering::Greater { l = x; } }
            if l.n == 0 { println!("  N={} r1={} POINT-ONLY G0'", n, r1); flagged += 1; continue; }
            // K1: W0 = floor(4 tau (1+2tau) / (l (1-4tau))) + 1 , tau = 1/N : 4(N+2)/(N(N-4)) / l
            if n <= 4 { println!("tau>=1/4"); return; }
            let num = 4 * (nn + 2) * l.d; let den = nn * (nn - 4) * l.n;
            let w0 = num / den + 1;
            if w0 > max_w0 { max_w0 = w0; }
            let wstart = nn + 1;
            let mut w1 = wstart;
            let mut unres: Vec<(I, I)> = Vec::new();
            while w1 < w0 {
                let g1 = sub_speed(&g0, w1, 1, nn);
                if g1.is_empty() {
                    // every w2 > w1 fails V' (V' has no good time even with w1 alone): the pair (w1, any w2) is unresolved for V'
                    flagged += 1; println!("  FLAG N={} r1={} w1={} (V' has no good time with w1 alone)", n, r1, w1); unres.push((w1, -1)); w1 += 1; continue;
                }
                let mut l2 = fr(0, 1);
                for &(a, b) in &g1 { let x = len(a, b); if cmpf(x, l2) == Ordering::Greater { l2 = x; } }
                if l2.n == 0 { flagged += 1; unres.push((w1, -2)); w1 += 1; continue; }
                // w2 >= ceil(2 tau / l2) is fine (K2); explicit test below that
                let wb = ceil_div(2 * l2.d, nn * l2.n); // 2/(N l2)
                if wb > max_w2_explicit { max_w2_explicit = wb; }
                let mut w2 = w1 + 1;
                while w2 < wb {
                    if !has_good(&g1, w2, 1, nn) { unres.push((w1, w2)); }
                    w2 += 1;
                }
                w1 += 1;
            }
            // r2-specific: for every unresolved pair of V', test V = V' minus r2 for every r2 in (r1,N]
            for &(u1, u2) in &unres {
                agg_unres += 1;
                if u2 < 0 {
                    // flagged w1: certified-complete over w2 for each r2 separately (K2 on V = [N]\{r1,r2} u {w1})
                    for r2 in (r1 + 1)..=n {
                        let ret2: Vec<i64> = (1..=n).filter(|&x| x != r1 && x != r2).collect();
                        let g02 = good_pieces(&ret2, 1, nn);
                        let g12 = sub_speed(&g02, u1, 1, nn);
                        if g12.is_empty() { println!("  FLAG2 N={} r1={} r2={} w1={} no good time for any w2", n, r1, r2, u1); agg_exc += 1; continue; }
                        let mut l2 = fr(0, 1);
                        for &(a, b) in &g12 { let x = len(a, b); if cmpf(x, l2) == Ordering::Greater { l2 = x; } }
                        if l2.n == 0 { println!("  FLAG2 N={} r1={} r2={} w1={} point-only", n, r1, r2, u1); continue; }
                        let wb = ceil_div(2 * l2.d, nn * l2.n);
                        let mut w2 = u1 + 1;
                        while w2 < wb {
                            if !has_good(&g12, w2, 1, nn) {
                                agg_exc += 1;
                                let ml = ml_exact(&set_of(n, r1, r2, u1 as i64, w2 as i64));
                                exc_list.push(format!("({};{},{};{},{}) ML={}", n, r1, r2, u1, w2, show(ml)));
                            }
                            w2 += 1;
                        }
                    }
                    continue;
                }
                for r2 in (r1 + 1)..=n {
                    let v = set_of(n, r1, r2, u1 as i64, u2 as i64);
                    if good_pieces(&v, 1, nn).is_empty() {
                        agg_exc += 1;
                        let ml = ml_exact(&v);
                        exc_list.push(format!("({};{},{};{},{}) ML={}", n, r1, r2, u1, u2, show(ml)));
                    }
                }
            }
        }
        println!("CERT1 N={} r1<=N/2 pairs={} maxW0={} max2/(N l'')={} unresolvedV'pairs={} flagged={} | exceptions ML<1/N (all r2, ALL w): {}", n, pairs_n, max_w0, max_w2_explicit, agg_unres, flagged, agg_exc);
        for s in exc_list.iter().take(60) { println!("  EXC {}", s); }
    }
}

// Theta(N,r): for ALL w1<w2 (>N): ML([N]\{r} u {w1,w2}) >= 1/N ?  certified-complete via K1/K2 (V' = only r removed).
// prints for each N the list of r where Theta is FALSE or unresolved (flagged / W0 too big), and the number of such r.
fn theta(n0: i64, n1: i64) {
    for n in n0..=n1 {
        if n <= 4 { continue; }
        let nn = n as I;
        let mut falses: Vec<String> = Vec::new();
        let mut first_false = -1i64; let mut last_true_prefix = 0i64; let mut prefix_ok = true;
        for r in 1..n {
            let ret: Vec<i64> = (1..=n).filter(|&x| x != r).collect();
            let g0 = good_pieces(&ret, 1, nn);
            let mut status = String::new();
            let mut ok = true;
            if g0.is_empty() { status = "G0empty".to_string(); ok = false; }
            else {
                let mut l = fr(0, 1);
                for &(a, b) in &g0 { let x = len(a, b); if cmpf(x, l) == Ordering::Greater { l = x; } }
                if l.n == 0 { status = "pointonly".to_string(); ok = false; }
                else {
                    let w0 = 4 * (nn + 2) * l.d / (nn * (nn - 4) * l.n) + 1;
                    if w0 > 4000 { status = format!("W0big{}", w0); ok = false; }
                    else {
                        let mut unres = 0u64; let mut flag = 0u64;
                        let mut w1 = nn + 1;
                        while w1 < w0 {
                            let g1 = sub_speed(&g0, w1, 1, nn);
                            if g1.is_empty() { flag += 1; w1 += 1; continue; }
                            let mut l2 = fr(0, 1);
                            for &(a, b) in &g1 { let x = len(a, b); if cmpf(x, l2) == Ordering::Greater { l2 = x; } }
                            if l2.n == 0 { flag += 1; w1 += 1; continue; }
                            let wb = ceil_div(2 * l2.d, nn * l2.n);
                            let mut w2 = w1 + 1;
                            while w2 < wb { if !has_good(&g1, w2, 1, nn) { unres += 1; } w2 += 1; }
                            w1 += 1;
                            if unres > 100000 { break; }
                        }
                        if unres > 0 || flag > 0 { ok = false; status = format!("unres{}flag{}", unres, flag); }
                    }
                }
            }
            if !ok { if first_false < 0 { first_false = r; } falses.push(format!("{}:{}", r, status)); prefix_ok = false; }
            else if prefix_ok { last_true_prefix = r; }
        }
        println!("THETA N={} first r with Theta false/unresolved = {} ; Theta true for all r<= {} ; #bad r = {} / {}", n, first_false, last_true_prefix, falses.len(), n - 1);
        if n <= 40 || n % 25 == 0 { println!("   bad r: {}", falses.iter().take(40).cloned().collect::<Vec<_>>().join(" ")); }
    }
}

fn is_prime(x: I) -> bool { if x < 2 { return false; } let mut d = 2; while d * d <= x { if x % d == 0 { return false; } d += 1; } true }

// Simulation of the case analysis of the analytic proof (K=10): decides each sampled (N,r,w1,w2) by case A / B1 / B2 / goodboth, FAIL otherwise.
// Samples include CRT-built "bad" w (w = e*r mod D for several D in P).  Every decided set is then CONFIRMED by the exact engine (ge(1/N)).
fn proofsim(n0: i64, n1: i64, samples: u64) {
    let mut rng = Rng(0x9E3779B97F4A7C15);
    let k = 10usize;
    for n in n0..=n1 {
        let nn = n as I;
        let mut cnt = [0u64; 5]; let mut fail = 0u64; let mut confirm_fail = 0u64; let mut nr = 0u64;
        for r in 1..n {
            let q = nn + 1 + r as I;
            let primes: Vec<I> = (q..=(2 * nn - 1)).filter(|&x| is_prime(x)).collect();
            if primes.len() < k { continue; }
            nr += 1;
            let p1 = primes[0];
            let wp1 = 2 * (nn + 2) * nn * p1 / ((nn - 4) * (2 * nn - p1)) + 1;
            let wm = 2 * (nn + 2) * nn * (2 * nn - 19) / ((nn - 4) * 19) + 1;
            for _ in 0..samples {
                let mk = |rng: &mut Rng, hi: I, nbad: usize| -> I {
                    // random w in (n, hi], optionally CRT-adjusted to be bad at nbad random primes
                    let mut w = nn + 1 + (rng.below((hi - nn) as u64) as I);
                    if rng.below(2) == 0 && nbad > 0 {
                        // CRT by brute force lift: find w' in (n, hi] with w' = e*r mod D for chosen primes (search via stepping product)
                        let mut m: I = 1; let mut x: I = 0; let mut ok = true;
                        for _ in 0..nbad {
                            let d = primes[rng.below(primes.len() as u64) as usize];
                            let e = [0, 1, -1][rng.below(3) as usize];
                            let target = ((e * r as I) % d + d) % d;
                            if m % d == 0 { continue; }
                            // solve x + m*t = target mod d
                            let mut t = 0; while (x + m * t) % d != target && t < d { t += 1; }
                            if (x + m * t) % d != target { ok = false; break; }
                            x += m * t; m *= d; if m > hi * 4 { break; }
                        }
                        if ok && m <= hi * 4 { let mut c = x; while c <= nn { c += m; } if c <= hi { w = c; } }
                    }
                    w
                };
                let hi1 = (wp1 + 2000).max(nn + 50);
                let a = mk(&mut rng, hi1, 3); let hi2 = (2 * nn) * hi1 / 13 + 1000;
                let mut b = mk(&mut rng, hi2.max(a + 10), 6);
                let (mut w1, mut w2) = (a, b);
                if w1 == w2 { b += 1; w2 = b; }
                if w1 > w2 { std::mem::swap(&mut w1, &mut w2); }
                let mut decided = 0usize;
                if w1 >= wp1 { decided = 1; }
                else {
                    let bad = |w: I, d: I| { let m = w % d; m == 0 || m == (r as I) % d || m == (d - (r as I) % d) % d };
                    let dg = primes.iter().find(|&&d| !bad(w1, d));
                    match dg {
                        None => { decided = 0; }
                        Some(&d) => {
                            if w2 * (2 * nn - d) >= d * w1 { decided = 2; }
                            else if primes.iter().any(|&d2| !bad(w1, d2) && !bad(w2, d2)) { decided = 3; }
                        }
                    }
                }
                if decided == 0 { fail += 1; } else { cnt[decided] += 1; }
                if decided > 0 && w2 < 3_000_000 {
                    // confirm by exact engine on V' = [N]\{r} u {w1,w2}
                    let mut v: Vec<i64> = (1..=n).filter(|&x| x != r).collect(); v.push(w1 as i64); v.push(w2 as i64);
                    if good_pieces(&v, 1, nn).is_empty() { confirm_fail += 1; }
                }
            }
        }
        println!("PROOFSIM N={} (r with >=10 primes: {}) samples/r={} caseA={} B1={} B2/goodboth={} undecided(FAIL)={} engine-confirm-failures={}", n, nr, samples, cnt[1], cnt[2], cnt[3], fail, confirm_fail);
    }
}

// Negative control for K1/K2: brute-force every V' pair (w1<w2<=wmax) for r1<=N/2 and compare with the certified-complete claim.
// A brute failure with w1>=W0, or with w2>=ceil(2/(N l2'')), would refute K1/K2 in the implementation.
fn k12check(n0: i64, n1: i64, wmax: i64) {
    for n in n0..=n1 {
        let nn = n as I;
        let (mut brute_fail, mut in_unres, mut violations, mut pairs) = (0u64, 0u64, 0u64, 0u64);
        for r1 in 1..=(n / 2) {
            let ret: Vec<i64> = (1..=n).filter(|&x| x != r1).collect();
            let g0 = good_pieces(&ret, 1, nn);
            if g0.is_empty() { continue; }
            let mut l = fr(0, 1);
            for &(a, b) in &g0 { let x = len(a, b); if cmpf(x, l) == Ordering::Greater { l = x; } }
            if l.n == 0 { continue; }
            let w0 = 4 * (nn + 2) * l.d / (nn * (nn - 4) * l.n) + 1;
            for w1 in (nn + 1)..(wmax as I) {
                let g1 = sub_speed(&g0, w1, 1, nn);
                let wb = if g1.is_empty() { I::MAX } else {
                    let mut l2 = fr(0, 1);
                    for &(a, b) in &g1 { let x = len(a, b); if cmpf(x, l2) == Ordering::Greater { l2 = x; } }
                    if l2.n == 0 { I::MAX } else { ceil_div(2 * l2.d, nn * l2.n) } };
                for w2 in (w1 + 1)..=(wmax as I) {
                    pairs += 1;
                    let fails = !has_good(&g1, w2, 1, nn);
                    if fails {
                        brute_fail += 1;
                        if w1 < w0 && w2 < wb { in_unres += 1; } else { violations += 1; }
                    }
                }
            }
        }
        println!("K12CHECK N={} wmax={} pairs={} brute-failures={} explained-by-unresolved-list={} VIOLATIONS(K1/K2 refuted)={}", n, wmax, pairs, brute_fail, in_unres, violations);
    }
}
