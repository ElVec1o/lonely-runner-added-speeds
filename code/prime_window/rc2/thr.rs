// rc2/thr.rs : threshold table for PrimeWin k (T_k = 3k(k+1)+1), k = 1..KMAX.
// N*(k): exact sieve (last N with pi(2N)-pi(N+N/2) < T, plus 1), sieve limit 2*NMAX+10.
// implicit: least N0 >= 732 with 8 T ln(1.5 N) <= 3 N for all N >= N0 (f64, evidence only).
// closed form: 3.2 T (ln(24 T) - 1).  tangent: best integer m, E_m = floor(2.7182818283^m).
// blocks: number of genblk blocks covering [N*, N1] (same greedy as rc/genblk.rs).
// negative control: k=1 must give N* = 79, k=2: 222, k=3: 517 (the accompanying notes section 6).
fn main(){
    let nmax:usize=600000; let lim=2*nmax+10;
    let mut is=vec![true;lim+1]; is[0]=false; is[1]=false;
    let mut i=2; while i*i<=lim { if is[i]{ let mut j=i*i; while j<=lim {is[j]=false;j+=i;} } i+=1; }
    let mut pi=vec![0u32;lim+1]; let mut c=0u32; for x in 0..=lim { if is[x]{c+=1;} pi[x]=c; }
    println!("k | T | Nstar | old_disch=max(1e5,67T^2) | implicit | closedform | m,E,N1(tangent) | blocks[Nstar,N1] | blocks_to_1e5");
    for k in 1..=12usize {
        let t=3*k*(k+1)+1;
        let mut last=0usize;
        for n in 4..=nmax { let cn=(pi[2*n]-pi[n+n/2]) as usize; if cn<t {last=n;} }
        let nstar=last+1;
        let old=std::cmp::max(100000usize,67*t*t);
        let tf=t as f64;
        // implicit
        let mut imp=732usize; while 8.0*tf*(1.5*(imp as f64)).ln() > 3.0*(imp as f64) { imp+=1; }
        let cf=(3.2*tf*((24.0*tf).ln()-1.0)).ceil() as usize;
        // tangent
        let mut best=(0usize,0u64,usize::MAX);
        for m in 5..=20usize {
            let e=(2.7182818283f64).powi(m as i32).floor();
            let den=3.0-12.0*tf/e; if den<=0.0 {continue;}
            let nt=((8.0*tf*((m as f64)-1.0))/den).ceil() as usize+2;
            let nt=std::cmp::max(nt,732);
            if nt<best.2 {best=(m,e as u64,nt);}
        }
        let n1=std::cmp::max(best.2,nstar);
        let cnt=|lo0:usize,n1:usize|->usize{
            let mut lo=lo0; let mut nb=0;
            while lo<=n1 {
                let mut ps:Vec<usize>=vec![]; let mut p=2*lo;
                while ps.len()<t { if is[p]{ps.push(p);} p-=1; }
                ps.reverse(); let pmin=ps[0];
                let mut hi=lo; while (hi+1)+1+(hi+1)/2<=pmin { hi+=1; }
                assert!(pmin>=lo+1+lo/2,"block empty");
                nb+=1; lo=hi+1;
            } nb };
        let b=cnt(nstar,n1);
        let b5=if nstar<=100000 {cnt(nstar,100000)} else {0};
        println!("{} | {} | {} | {} | {} | {} | m={},E={},N1={} | {} | {}",k,t,nstar,old,imp,cf,best.0,best.1,n1,b,b5);
    }
}
