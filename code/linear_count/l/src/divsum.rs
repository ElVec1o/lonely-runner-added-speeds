// divsum.rs: planted negative for dropping pairwise coprimality. For w <= (2N-1)N and D | w (D in window, gcd(D,r)=1) the arc of w is centred at
// t0 and wider than J(D), so cov_w(D) = 1 EXACTLY. S(w) = #{D | w} for the non-coprime family; Lemma 5's bound 18 fails once some w has >= 19 window divisors.
// Also reports the pairwise-coprime restriction (Lemma 4: <= 2).
fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }
fn maxcop(ds: &[u64]) -> usize { // exact max pairwise coprime subset (small lists)
    fn rec(ds: &[u64], i: usize, ch: &mut Vec<u64>, best: &mut usize) {
        if ch.len() > *best { *best = ch.len(); }
        if i >= ds.len() || ch.len() + (ds.len() - i) <= *best { return; }
        if ch.iter().all(|&c| gcd(c, ds[i]) == 1) { ch.push(ds[i]); rec(ds, i + 1, ch, best); ch.pop(); }
        rec(ds, i + 1, ch, best);
    }
    let mut b = 0; rec(ds, 0, &mut vec![], &mut b); b
}
fn main() {
    let a: Vec<String> = std::env::args().collect();
    for s in &a[1..] {
        let n: u64 = s.parse().unwrap();
        for &r in &[1u64, 2, 6] {
            let wmax = (2 * n - 1) * n; // cov = 1 region
            let c: Vec<u64> = (n + 1 + r..=2 * n - 1).filter(|&d| gcd(d, r) == 1).collect();
            let mut cnt = vec![0u8; wmax as usize + 1];
            for &d in &c { let mut m = d; while m <= wmax { cnt[m as usize] = cnt[m as usize].saturating_add(1); m += d; } }
            let (mut bw, mut bc) = (0u64, 0u8);
            for w in n + 1..=wmax { if cnt[w as usize] > bc { bc = cnt[w as usize]; bw = w; } }
            let ds: Vec<u64> = c.iter().cloned().filter(|d| bw % d == 0).collect();
            // exact check cov = 1 for each divisor: arc half-width 1/(N w) >= d = 1/K  <=> K >= N w ... K = (2N-1)N^2, N w <= (2N-1)N^2 iff w <= (2N-1)N
            let ok = ds.iter().all(|_| (n as u128) * (bw as u128) <= (2 * n as u128 - 1) * (n as u128) * (n as u128));
            println!("N={} r={}: window moduli coprime to r = {}, best w <= (2N-1)N = {} has {} window divisors (each cov = 1: {}), S(w) = {} {} 18 ; max pairwise-coprime subset of those divisors = {}",
                n, r, c.len(), bw, bc, ok, bc, if bc > 18 { ">" } else { "<=" }, maxcop(&ds));
        }
    }
}
