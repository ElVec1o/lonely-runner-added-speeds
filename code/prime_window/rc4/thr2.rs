// rc4/thr2.rs : exact sieve thresholds N*(k) and exact Chebyshev thresholds M_k, k = 1..KMAX  (extends rc2/thr.rs).
// N*(k)  = 1 + last N <= NMAX with  #primes in [N+1+N/2, 2N-1] < T   (T = 3k(k+1)+1; worst r = floor(N/2); exact integers).
// chebG(T,j) = 6 (j+2) (T + 3 (j+2) + 60) + 1200 ;  cond(N) : chebG(T, floor(log2 N)) <= N.
// Mex(k) = 1 + last N <= 2^23 with NOT cond(N)  (exact, brute force);  J = least j with chebG(T,j) <= 2^j;
// Mtab(k) = max_{j<J} min(2^(j+1), chebG(T,j))  (the table M used by Lean's cheb_hyp_ge; must equal Mex, checked).
// blocks[N*, Mtab-1]: the greedy block cover of genblk4.rs (stats only); table = primes from first block's p_min to 2*lo_last.
// Negative control: N*(1..12) must equal 79,222,517,895,1410,2067,2920,3937,4891,6240,7570,9060 (RobustKAll.Nstar) and
// Mtab(4..12) = 17424,20304,23760,27792,34656,40164,46284,53016,60360 (FinalCore).
// Memory: bool sieve 3 MB + u32 pi 12 MB + a few vectors.  usage: thr2 KMAX NMAX
use std::env;
fn chebg(t:u64,j:u64)->u64{ 6*(j+2)*(t+3*(j+2)+60)+1200 }
fn main(){
    let a:Vec<String>=env::args().collect();
    let kmax:usize=a[1].parse().unwrap(); let nmax:usize=a[2].parse().unwrap();
    let lim=2*nmax+10;
    let mut is=vec![true;lim+1]; is[0]=false; is[1]=false;
    let mut i=2; while i*i<=lim { if is[i]{ let mut j=i*i; while j<=lim {is[j]=false;j+=i;} } i+=1; }
    let mut pi=vec![0u32;lim+1]; let mut c=0u32; for x in 0..=lim { if is[x]{c+=1;} pi[x]=c; }
    println!("k | T | Nstar | Mex | Mtab | J | NCheb_old=max(1e5,67T^2) | ratio Mtab/Nstar | blocks[Nstar,Mtab-1] | table_primes | first_pmin");
    let expn=[0,79,222,517,895,1410,2067,2920,3937,4891,6240,7570,9060];
    let expm=[0,0,0,0,17424,20304,23760,27792,34656,40164,46284,53016,60360];
    for k in 1..=kmax {
        let t=(3*k*(k+1)+1) as u64;
        // N*: primes in [N+1+N/2, 2N-1]  == pi(2N-1)-pi(N+N/2)
        let mut last=0usize;
        for n in 4..=nmax { let cn=(pi[2*n-1]-pi[n+n/2]) as u64; if cn<t {last=n;} }
        assert!(last+1000<nmax, "sieve limit too small: last failing N {} near NMAX",last);
        let nstar=last+1;
        // Chebyshev exact
        let top:u64=1<<23; let mut lastbad=0u64;
        // N from 2 up; log2 floor
        for n in 2..=top { let l=63-n.leading_zeros() as u64; if chebg(t,l)>n {lastbad=n;} }
        let mex=lastbad+1;
        let mut jj=0u64; while chebg(t,jj)>(1u64<<jj) {jj+=1;}
        let mut mtab=0u64; for j in 0..jj { let v=std::cmp::min(1u64<<(j+1),chebg(t,j)); if v>mtab {mtab=v;} }
        let old=std::cmp::max(100000u64,67*t*t);
        if k<=12 { assert_eq!(nstar,expn[k],"N* control failed k={}",k); }
        if k>=4 && k<=12 { assert_eq!(mtab,expm[k],"M control failed k={}",k); }
        // greedy blocks over [nstar, mtab-1]
        let n1=(mtab as usize).saturating_sub(1);
        let mut lo=nstar; let mut nb=0usize; let mut pfirst=0usize; let mut lasthi=0usize; let mut lastlo=0usize;
        if n1>=nstar {
            while lo<=n1 {
                let mut ps:Vec<usize>=vec![]; let mut p=2*lo;
                while ps.len()<t as usize { if is[p]{ps.push(p);} p-=1; }
                ps.reverse(); let pmin=ps[0];
                let mut hi=lo; while (hi+1)+1+(hi+1)/2<=pmin { hi+=1; }
                assert!(pmin>=lo+1+lo/2,"block empty");
                if nb==0 {pfirst=pmin;}
                nb+=1; lastlo=lo; lasthi=hi; lo=hi+1;
            }
        }
        let tp = if nb>0 { pi[2*lastlo]-pi[pfirst-1] } else {0};
        println!("{} | {} | {} | {} | {} | {} | {} | {:.2} | {} (last hi {}) | {} | {}",k,t,nstar,mex,mtab,jj,old,(mtab as f64)/(nstar as f64),nb,lasthi,tp,pfirst);
        if k>=1 && mex!=mtab { println!("   NOTE: Mex {} != Mtab {} (table M is not the exact threshold)",mex,mtab); }
    }
}
