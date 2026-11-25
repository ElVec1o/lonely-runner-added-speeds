// prime-window counts: c(N,r) = #primes in [N+1+r, 2N-1].  For r=floor(N/2) (worst case r<=N/2).
// Also: for each K, rmax_K(N) = largest r with >= K primes in [N+1+r,2N-1]; report min over N in a range of N - rmax_K(N) etc.
fn main() {
    let lim: usize = 20_000_100;
    let mut sv = vec![true; lim + 1]; sv[0] = false; sv[1] = false;
    let mut i = 2; while i * i <= lim { if sv[i] { let mut j = i * i; while j <= lim { sv[j] = false; j += i; } } i += 1; }
    let mut pi = vec![0u32; lim + 1]; for k in 1..=lim { pi[k] = pi[k - 1] + if sv[k] { 1 } else { 0 }; }
    let nmax: usize = 10_000_000;
    for &k in &[7u32, 10, 13, 19] {
        let mut last_bad = 0usize; let mut minc = u32::MAX; let mut argmin = 0;
        for n in 14..=nmax {
            let lo = n + 1 + n / 2; let hi = 2 * n - 1;
            let c = pi[hi] - pi[lo - 1];
            if c < k { last_bad = n; }
            if n > 100 && c < minc { minc = c; argmin = n; }
        }
        println!("K={} : last N<=1e7 with count(r=N/2) < K is {} ; min count over 100<N<=1e7 is {} at N={}", k, last_bad, minc, argmin);
    }
    // rmax_K(N): largest r<=N-2 with >=K primes in [N+1+r,2N-1], i.e. number of primes in [N+1+r, 2N-1]
    for &k in &[10u32] {
        let mut worst = 0usize; let mut wn = 0usize; let mut hist = std::collections::BTreeMap::new();
        for n in 20..=2_000_000usize {
            // largest r with count >=k : need k-th largest prime p_k <= 2N-1 ; r = p_k - N - 1
            let hi = 2 * n - 1; let tot = pi[hi];
            if tot < k { continue; }
            // find k-th prime from the top: index tot-k+1 -th prime; scan down
            let mut cnt = 0u32; let mut p = hi;
            while cnt < k { if sv[p] { cnt += 1; if cnt == k { break; } } p -= 1; }
            let r = p - n - 1; let gap = n - r; // N - rmax
            if gap > worst { worst = gap; wn = n; }
            *hist.entry(gap / 10 * 10).or_insert(0u64) += 1;
        }
        println!("K={} rmax_K(N) : max over 20<=N<=2e6 of N - rmax_K(N) = {} at N = {} ; histogram of N-rmax by decade {:?}", k, worst, wn, hist);
    }
}
