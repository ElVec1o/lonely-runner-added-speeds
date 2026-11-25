// thr.rs: exact thresholds. prime-window count c(N) = pi(2N) - pi(N + floor(N/2)) (= min over r<=N/2 of #primes in [N+1+r,2N-1]),
// last N with c(N) < T; Chebyshev condition 6 l (T + 3 l + 60) + 1200 <= N, l = floor(log2 N), last failing N <= 2^23.
fn main() {
    let lim: usize = 12_000_000;
    let mut comp = vec![false; lim + 1]; comp[0] = true; comp[1] = true;
    let mut i = 2; while i * i <= lim { if !comp[i] { let mut j = i * i; while j <= lim { comp[j] = true; j += i; } } i += 1; }
    let mut pi = vec![0u32; lim + 1]; for x in 1..=lim { pi[x] = pi[x - 1] + if comp[x] { 0 } else { 1 }; }
    let nmax = lim / 2;
    let mut ts: Vec<(&str, usize, u64)> = vec![]; // (family, k, T)
    for k in 1..=40usize {
        let kk = k as u64;
        ts.push(("S", k, 3 * kk * (kk + 1) + 1)); ts.push(("L19", k, 19 * kk + 1)); ts.push(("L10", k, 10 * kk + 1)); ts.push(("L5", k, 5 * kk + 1));
    }
    let mut last = vec![0usize; ts.len()];
    for n in 1..=nmax {
        let c = (pi[2 * n] - pi[n + n / 2]) as u64;
        for (i, t) in ts.iter().enumerate() { if c < t.2 { last[i] = n; } }
    }
    // Chebyshev last failing
    let mut lastc = vec![0u64; ts.len()];
    for n in 1u64..=(1 << 23) {
        let l = 63 - n.leading_zeros() as u64 + 2; // Lean: Nat.log 2 N + 2
        for (i, t) in ts.iter().enumerate() { if 6 * l * (t.2 + 3 * l + 60) + 1200 > n { lastc[i] = n; } }
    }
    println!("# control: MCheb(S,k) from Lean for k=1,2,3,4,5,6 = 11280 12360 13980 17424 20304 23760 ; N*(S,k)=79 222 517 895 1410 2067 ; N*(L19,k=2,3,6,12,24,30,50)=526 889 1912 4261 8896 11311 19924");
    println!("k | T_S | T_L19 | primeN*_S | primeN*_L19(+133k) | primeN*_L10 | primeN*_L5 | ChebM_S | ChebM_L19 | Cheb(67T^2,1e5)_S | _L19 | winner(prime) | winner(cheb)");
    let idx = |fam: &str, k: usize| ts.iter().position(|t| t.0 == fam && t.1 == k).unwrap();
    for k in 1..=40usize {
        let (is, i19, i10, i5) = (idx("S", k), idx("L19", k), idx("L10", k), idx("L5", k));
        let ns = last[is] + 1; let nl = std::cmp::max(last[i19] + 1, 133 * k); let n10 = last[i10] + 1; let n5 = last[i5] + 1;
        let cs = lastc[is] + 1; let cl = std::cmp::max(lastc[i19] + 1, 133 * k as u64);
        let ps = std::cmp::max(100000u64, 67 * ts[is].2 * ts[is].2); let pl = std::cmp::max(100000u64, 67 * ts[i19].2 * ts[i19].2);
        println!("{} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {}", k, ts[is].2, ts[i19].2, ns, nl, n10, n5, cs, cl, ps, pl,
            if (nl as usize) < ns { "L" } else { "S" }, if cl < cs { "L" } else { "S" });
    }
    // sanity: last failures are far below the sieve limit
    let mx = last.iter().cloned().max().unwrap(); println!("max last-failing N over all families = {} (sieve covers N <= {})", mx, nmax);
}
