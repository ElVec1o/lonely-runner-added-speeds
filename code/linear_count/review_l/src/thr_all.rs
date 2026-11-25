// thr: independent threshold tables. sieve to 6e6, c(N)=pi(2N)-pi(N+floor(N/2)); N <= 3e6
fn main() {
    let lim: usize = 6_000_000; let nmax: usize = 3_000_000;
    let mut comp = vec![false; lim + 1]; comp[0] = true; comp[1] = true;
    let mut i = 2; while i * i <= lim { if !comp[i] { let mut j = i * i; while j <= lim { comp[j] = true; j += i; } } i += 1; }
    let mut pi = vec![0u32; lim + 1]; for x in 1..=lim { pi[x] = pi[x - 1] + if comp[x] { 0 } else { 1 }; }
    let c = |n: usize| -> i64 { pi[2 * n] as i64 - pi[n + n / 2] as i64 };
    let lastfail = |t: i64| -> usize { let mut n = nmax; while n > 0 { if c(n) < t { return n; } n -= 1; } 0 };
    let cheb_fail = |t: u64, n: u64| -> bool { let l = 64 - n.leading_zeros() as u64 - 1 + 2; !(6 * l * (t + 3 * l + 60) + 1200 <= n) };
    let lastcheb = |t: u64| -> u64 { let mut n: u64 = 1 << 23; while n > 0 { if cheb_fail(t, n) { return n; } n -= 1; } 0 };
    // opt (N-dependent size): fails if N<=7k or c(N) < floor(8kN/(N-7k))+1
    let lastopt = |k: i64| -> usize { let mut n = nmax; while n > 0 { let ni = n as i64; if ni <= 7 * k || c(n) < (8 * k * ni) / (ni - 7 * k) + 1 { return n; } n -= 1; } 0 };
    println!("k | T_S T_9 T_19 T_8 | prime N*: S 9k+1(>=63k) 19k+1(>=133k) 8k+1(>=7k+1,>=10) opt | Cheb exact: S 9k+1 19k+1 8k+1");
    let mcheb = [11280u64, 12360, 13980, 17424, 20304, 23760, 27792, 34656, 40164, 46284, 53016, 60360, 72588, 81660];
    for k in 1..=40usize {
        let kk = k as i64; let ts = 3 * kk * (kk + 1) + 1; let t9 = 9 * kk + 1; let t19 = 19 * kk + 1; let t8 = 8 * kk + 1;
        let ps = lastfail(ts) + 1; let p9 = (lastfail(t9) + 1).max(63 * k); let p19 = (lastfail(t19) + 1).max(133 * k); let p8 = (lastfail(t8) + 1).max(7 * k + 1).max(10);
        let po = lastopt(kk) + 1;
        let cs = lastcheb(ts as u64) + 1; let c9 = (lastcheb(t9 as u64) + 1).max(63 * k as u64); let c19 = (lastcheb(t19 as u64) + 1).max(133 * k as u64); let c8 = (lastcheb(t8 as u64) + 1).max(7 * k as u64 + 1);
        let mc = if k <= 14 { format!("{}", if mcheb[k - 1] == cs { "MCheb-ok" } else { "MCheb-MISMATCH" }) } else { "-".into() };
        println!("{} | {} {} {} {} | {} {} {} {} {} | {} {} {} {} {}", k, ts, t9, t19, t8, ps, p9, p19, p8, po, cs, c9, c19, c8, mc);
    }
}
