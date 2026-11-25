// cw.rs: max size of a pairwise coprime subset of {D in [N+1+r, 2N-1], gcd(D,r)=1} for the known exceptions (lower bounds for the linear constant)
fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }
fn maxcop(ds: &[u64]) -> usize {
    fn rec(ds: &[u64], i: usize, ch: &mut Vec<u64>, best: &mut usize) {
        if ch.len() > *best { *best = ch.len(); }
        if i >= ds.len() || ch.len() + (ds.len() - i) <= *best { return; }
        if ch.iter().all(|&c| gcd(c, ds[i]) == 1) { ch.push(ds[i]); rec(ds, i + 1, ch, best); ch.pop(); }
        rec(ds, i + 1, ch, best);
    }
    let mut b = 0; rec(ds, 0, &mut vec![], &mut b); b
}
fn main() {
    // (N, r, k, description) from REPORT sec. 3 hunt and BO/BM
    let ex = [(13u64, 6u64, 1u64, "[13]-6+{69}"), (20, 6, 2, "[20]-6+{29,31}"), (29, 12, 3, "[29]-12+{37,43,94} (hunt) / {31,94,98} (BO)"), (38, 12, 4, "[38]-12+{53,55,59,61}")];
    for (n, r, k, s) in ex {
        let c: Vec<u64> = (n + 1 + r..=2 * n - 1).filter(|&d| gcd(d, r) == 1).collect();
        let m = maxcop(&c);
        println!("exception {} (k={}): window coprime-to-r size {}, max pairwise coprime subset = {}  (= {:.2} k)", s, k, c.len(), m, m as f64 / k as f64);
    }
}
