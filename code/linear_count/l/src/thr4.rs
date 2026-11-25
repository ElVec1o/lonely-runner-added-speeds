// thr4.rs: best use of Theorem L* : for given N the needed family size is T(N,k) = floor(8 k N / (N - 7k)) + 1 (N > 7k).
// last failing N for (a) prime count c(N) = pi(2N)-pi(N+N/2) >= T(N,k); (b) Chebyshev 6 l (T + 3 l + 60) + 1200 <= N, l = log2 N + 2.
fn main() {
    let lim: usize = 12_000_000;
    let mut comp = vec![false; lim + 1]; comp[0] = true; comp[1] = true;
    let mut i = 2; while i * i <= lim { if !comp[i] { let mut j = i * i; while j <= lim { comp[j] = true; j += i; } } i += 1; }
    let mut pi = vec![0u32; lim + 1]; for x in 1..=lim { pi[x] = pi[x - 1] + if comp[x] { 0 } else { 1 }; }
    let nmax = lim / 2;
    println!("k | optN*_prime | optN*_cheb(exact) | for comparison T_S prime N* | 9k+1 prime N*(N>=63k) ; T(N*,k) at the prime threshold");
    for k in [1usize, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 30, 40] {
        let mut lastp = 0usize; let mut lastc = 0u64;
        for n in (7 * k + 1)..=nmax {
            let t = (8 * k as u64 * n as u64) / (n as u64 - 7 * k as u64) + 1;
            let c = (pi[2 * n] - pi[n + n / 2]) as u64;
            if c < t { lastp = n; }
        }
        for n in (7 * k as u64 + 1)..=(1u64 << 23) {
            let t = (8 * k as u64 * n) / (n - 7 * k as u64) + 1;
            let l = 63 - n.leading_zeros() as u64 + 2;
            if 6 * l * (t + 3 * l + 60) + 1200 > n { lastc = n; }
        }
        // small n region below 7k+1 trivially fails
        let np = std::cmp::max(lastp + 1, 7 * k + 1); let nc = std::cmp::max(lastc + 1, 7 * k as u64 + 1);
        let tn = (8 * k as u64 * np as u64) / (np as u64 - 7 * k as u64) + 1;
        println!("{} | {} | {} | T(N*)={}", k, np, nc, tn);
    }
}
