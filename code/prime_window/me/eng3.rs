// eng.rs. OWN exact engine (not st.rs / hb.rs / oe.rs).
// Everything is exact i128 rational arithmetic; no floats in any decision.
// Conventions: speeds are positive integers; N = size of base interval [N]; ML(V)=max_t min_v ||tv||.
// ge(V,p,q): ML(V) >= p/q.  Bands: speed x is BAD at t iff ||x t|| < p/q, i.e. t in union_c ((cq-p)/(qx),(cq+p)/(qx)) (open).
// Method A (gap engine): GOOD set of the base speeds in [0,1/2] = complement of union of open bands = list of CLOSED gaps; then a gap is
//   intersected with the good set of the extra speeds W by a second sweep restricted to the gap.  Termination: a gap with more than CAP bands => UNRESOLVED (counted).
// Method C (candidate times): exact ML = max over t=k/(vi+vj) (i<=j) of min_v dist(k v mod m)/m.  Used for controls and cross-validation (small sets only).
use std::env;
type F=(i128,i128);
fn lt(a:F,b:F)->bool{ a.0*b.1 < b.0*a.1 }
fn le(a:F,b:F)->bool{ a.0*b.1 <= b.0*a.1 }
fn gcd(a:i128,b:i128)->i128{ if b==0 {a.abs()} else {gcd(b,a%b)} }
struct Rng(u64);
impl Rng{ fn next(&mut self)->u64{ let mut x=self.0; x^=x<<13; x^=x>>7; x^=x<<17; self.0=x; x }
  fn below(&mut self,n:u64)->u64{ self.next()%n } }
const CAP:usize=200_000;
use std::sync::atomic::{AtomicUsize,Ordering};
static CAPV:AtomicUsize=AtomicUsize::new(200_000);
use std::cell::RefCell;
thread_local!{ static BUF:RefCell<Vec<(F,F)>>=RefCell::new(Vec::with_capacity(CAP+8)); }
// bands of speed x overlapping [a,b] (a=an/ad, b=bn/bd), threshold p/q. pushes (L,R) with L=(cq-p)/(qx), R=(cq+p)/(qx).
fn bands(x:i128,p:i128,q:i128,a:F,b:F,out:&mut Vec<(F,F)>)->bool{
    let cmin=(a.0*q*x - p*a.1).div_euclid(q*a.1)+1;
    let m=b.0*q*x + p*b.1; let n=q*b.1; let cmax=(m-1).div_euclid(n);
    if cmax<cmin {return true;}
    if ((cmax-cmin+1) as usize)+out.len()>CAPV.load(Ordering::Relaxed) {return false;}
    let mut c=cmin; while c<=cmax { out.push((((c*q-p),(q*x)),((c*q+p),(q*x)))); c+=1; }
    true
}
fn sort_bands(v:&mut Vec<(F,F)>){ v.sort_unstable_by(|u,w|{ (u.0.0*w.0.1).cmp(&(w.0.0*u.0.1)) }); }
// closed gaps in [0,1/2] of the good set of the base speeds
fn gaps_of(sp:&[i128],p:i128,q:i128)->Option<Vec<(F,F)>>{
    let mut v:Vec<(F,F)>=Vec::new(); let half:F=(1,2);
    for &x in sp { if !bands(x,p,q,(0,1),half,&mut v) {return None;} }
    sort_bands(&mut v);
    let mut r:F=(0,1); let mut g=Vec::new();
    for &(l,rr) in v.iter() { if lt(half,r) {break;}
        if le(r,l) { let e= if lt(half,l) {half} else {l}; g.push((r,e)); }
        if lt(r,rr) {r=rr;} }
    if le(r,half) { g.push((r,half)); }
    Some(g)
}
// 0 = no good point, 1 = good point exists, 2 = unresolved (cap)
fn good_in(a:F,b:F,ws:&[i128],p:i128,q:i128)->u8{
    BUF.with(|bb|{ let mut v=bb.borrow_mut(); v.clear();
    for &w in ws { if !bands(w,p,q,a,b,&mut v) {return 2;} }
    sort_bands(&mut v);
    let mut r=a;
    for &(l,rr) in v.iter() { if lt(b,r) {return 0;} if le(r,l) {return 1;} if lt(r,rr) {r=rr;} }
    if le(r,b) {1} else {0} })
}
// ML(base u W) >= p/q ; returns (0/1/2)
fn ge_split(gaps:&[(F,F)],ws:&[i128],p:i128,q:i128)->u8{
    if ws.is_empty() { return if gaps.is_empty() {0} else {1}; }
    let mut unres=false;
    for &(a,b) in gaps { match good_in(a,b,ws,p,q) {1=>return 1, 2=>unres=true, _=>{}} }
    if unres {2} else {0}
}
fn ge_full(sp:&[i128],p:i128,q:i128)->u8{ match gaps_of(sp,p,q) { None=>2, Some(g)=> if g.is_empty() {0} else {1} } }
// Method C: exact ML as fraction (num,den) unreduced
fn ml_c(sp:&[i128])->F{
    let mut best:F=(0,1);
    for i in 0..sp.len() { for j in i..sp.len() { let m=sp[i]+sp[j];
        for k in 1..=(m/2) { let mut mn=i128::MAX;
            for &v in sp { let y=(k*v)%m; let d= if y<m-y {y} else {m-y}; if d<mn {mn=d;} }
            if lt(best,(mn,m)) {best=(mn,m);} } } }
    best
}
fn isprime(x:i128)->bool{ if x<2 {return false;} let mut d=2; while d*d<=x { if x%d==0 {return false;} d+=1; } true }
fn base(n:i128,r:i128)->Vec<i128>{ (1..=n).filter(|&x|x!=r).collect() }
// window primes
fn wprimes(n:i128,r:i128)->Vec<i128>{ ((n+1+r)..=(2*n-1)).filter(|&x|isprime(x)).collect() }
// chain split for declared k, gap constant num/den (default 8): i = least index with i==m or w_{i+1} > cn*k*N*w_i/cd. returns (i, w_i)
fn chain(n:i128,k:i128,w:&[i128],cn:i128,cd:i128)->(usize,i128){
    let mut i=0usize; let mut wi=n;
    while i<w.len() && !(w[i]*cd > cn*k*n*wi) { wi=w[i]; i+=1; }
    (i,wi)
}
fn clean(d:i128,r:i128,small:&[i128])->bool{ for &w in small { for e in [-1i128,0,1] { if (w-e*r)%d==0 {return false;} } } true }

fn modinv(a:i128,m:i128)->i128{ let (mut t,mut nt,mut r,mut nr)=(0i128,1i128,m,a.rem_euclid(m)); while nr!=0 { let q=r/nr; let x=t-q*nt; t=nt; nt=x; let y=r-q*nr; r=nr; nr=y; } t.rem_euclid(m) }
// candidate speeds relative to a previous speed w (or None), for ratio constant K
fn rel(w:Option<i128>,n:i128,k:i128,crt:&[i128],rg:&mut Rng,lim:i128)->Vec<i128>{
    let mut v:Vec<i128>=Vec::new();
    match w { None=>{ for d in 1..=60 { v.push(n+d); } for _ in 0..12 { v.push(n+1+(rg.below((8*k*n*n) as u64) as i128)); } for &c in crt.iter().take(40) { v.push(c); }
            for _ in 0..12 { let e=(rg.below(1000) as f64)/1000.0*((lim as f64).ln()-((n+1) as f64).ln()); v.push(((n+1) as f64*e.exp()) as i128); } }
        Some(w)=>{ for d in 1..=25 { v.push(w+d); } for j in 2..=30 { v.push(j*w); v.push(j*w+1); }
            for d in -3..=3 { v.push(8*k*n*w+d); } for d in -2..=2 { v.push((8*k*n+1)*w+d); v.push(4*k*n*w+d); v.push(16*k*n*w+d); v.push(n*w+d); v.push(n*n*w+d); }
            for &c in crt.iter().take(30) { v.push(c); if c< lim/ (w.max(1)) { v.push(c*w); } }
            for _ in 0..16 { let e=(rg.below(1000) as f64)/1000.0*((lim as f64).ln()-(w as f64).ln()).max(0.0); v.push(((w as f64)*e.exp()) as i128+1); }
            // powers of N near the chain boundary
            let mut pw=n*n; for _ in 0..6 { v.push(pw); v.push(pw+1); v.push(pw-1); if pw>lim/n {break;} pw*=n; } } }
    v.retain(|&x| x>n && x<=lim); v.sort(); v.dedup(); v
}
fn crt_list(n:i128,r:i128,ps:&[i128],lim:i128)->Vec<i128>{ let mut v=Vec::new(); for &p in ps { for e in [-1i128,0,1] { let res=(e*r).rem_euclid(p); let mut w=res; while w<=n {w+=p;} for _ in 0..4 { if w<=lim {v.push(w);} w+=p; } } }
    // pairs of primes simultaneous (CRT)
    for i in 0..ps.len().min(8) { for j in (i+1)..ps.len().min(8) { for e1 in [-1i128,0,1] { for e2 in [-1i128,0,1] { let (p1,p2)=(ps[i],ps[j]); let r1=(e1*r).rem_euclid(p1); let r2=(e2*r).rem_euclid(p2);
        let mut w=r1; while w%p2!=r2 { w+=p1; } while w<=n {w+=p1*p2;} for _ in 0..3 { if w<=lim {v.push(w);} w+=p1*p2; } } } } }
    v.sort(); v.dedup(); v }
fn main(){
    let a:Vec<String>=env::args().collect(); if let Ok(c)=env::var("CAPV") { CAPV.store(c.parse().unwrap(),Ordering::Relaxed); }
    match a[1].as_str() {
    "ctl" => {
        let mut ok=0; let mut tot=0;
        let mut t=|name:&str,sp:Vec<i128>,p:i128,q:i128,exp:u8|{ let g=ge_full(&sp,p,q); tot+=1; let good=g==exp; if good {ok+=1;} println!("ctl {} ge {}/{} = {} expected {} {}",name,p,q,g,exp,if good {"OK"} else {"FAIL"}); };
        t("[8]",(1..=8).collect(),1,9,1); t("[8]",(1..=8).collect(),1001,9000,0);
        let mut v=base(13,6); v.push(69); t("[13]-6+69",v.clone(),3,40,1); t("[13]-6+69",v.clone(),3001,40000,0); t("[13]-6+69",v.clone(),1,13,0);
        let mut v=base(14,6); v.push(69); t("[14]-6+69",v.clone(),1,14,1);
        t("T1",vec![1,3,4,7],1,5,1); t("T1",vec![1,3,4,7],1001,5000,0);
        t("T2",vec![1,3,4,5,9],1,6,1); t("T2",vec![1,3,4,5,9],1001,6000,0);
        let mut v=base(20,6); v.push(29); v.push(31); t("[20]-6+29+31",v.clone(),1,20,0); println!("   ML_C([20]-6+29+31) = {:?} (<1/20 expected)",{let m=ml_c(&v); (m.0,m.1)});
        let mut v=base(13,6); v.push(69); println!("   ML_C([13]-6+69) = {:?} (3/40 expected)",{let m=ml_c(&v); (m.0,m.1)});
        let mut v=base(21,6); v.push(29); v.push(31); t("[21]-6+29+31",v.clone(),1,21,1);
        let mut v=base(13,12); v.push(36); println!("   ML_C([13]-12+36) = {:?} (3/41 expected)",{let m=ml_c(&v); (m.0,m.1)});
        println!("ctl summary {}/{} OK",ok,tot);
    }
    "xval" => { // A vs C on random small sets
        let ns:u64=a[2].parse().unwrap(); let mut rg=Rng(0x9E3779B97F4A7C15); let mut bad=0u64; let mut tot=0u64;
        for _ in 0..ns { let n=3+rg.below(7) as usize; let mx=(n as u64+4)+rg.below(70); let mut s:Vec<i128>=Vec::new(); while s.len()<n { let x=(1+rg.below(mx)) as i128; if !s.contains(&x) {s.push(x);} }
            let m=ml_c(&s); let g=gcd(m.0,m.1); let (p,q)=(m.0/g,m.1/g);
            let kk=1009i128; let up=ge_full(&s,p*kk+1,q*kk); let eq=ge_full(&s,p,q); let dn= if p*kk>1 {ge_full(&s,p*kk-1,q*kk)} else {1};
            tot+=1; if !(eq==1 && up==0 && dn==1) { bad+=1; if bad<10 {println!("MISMATCH {:?} C={}/{} eq={} up={} dn={}",s,p,q,eq,up,dn);} } }
        println!("xval sets={} mismatches={}",tot,bad);
    }
    "spoil" => { // number of window primes dividing w - e r  vs  bound: (N+2)^c <= w+r
        let n1:i128=a[2].parse().unwrap(); let n2:i128=a[3].parse().unwrap(); let wmax:usize=a[4].parse().unwrap();
        let mut viol=0u64; let mut gmax=0usize; let mut gw=0usize; let mut hits:Vec<usize>=Vec::new();
        for n in n1..=n2 { let mut nmax=[0usize;8];
            for r in 1..=(n-2) { let ps=wprimes(n,r); if ps.is_empty() {continue;}
                for e in [-1i128,0,1] { hits.clear();
                    for &p in &ps { let res=((e*r)%p+p)%p; let mut w=res as usize; if w==0 {w=p as usize;} while w<=wmax { if w as i128>n {hits.push(w);} w+=p as usize; } }
                    hits.sort_unstable(); let mut i=0; while i<hits.len() { let mut j=i; while j<hits.len() && hits[j]==hits[i] {j+=1;} let c=j-i; let w=hits[i]; i=j;
                        let mut pw:i128=1; for _ in 0..c { pw=pw.saturating_mul(n+2); }
                        if pw>(w as i128)+r { viol+=1; if viol<10 {println!("VIOL n={} r={} e={} w={} c={}",n,r,e,w,c);} }
                        let cl=(((w as f64).ln()/((n+2) as f64).ln()) as usize).min(7); if c>nmax[cl] {nmax[cl]=c;}
                        if c>gmax {gmax=c; gw=w;} } } }
            if n%25==0 || n==n2 { println!("N={} max #window-primes dividing w-er, by floor(log_(N+2) w) = index: {:?}",n,nmax); } }
        println!("spoil N={}..{} r<=N-2 w<={}: bound violations={} ; global max c={} at w={}",n1,n2,wmax,viol,gmax,gw);
    }
    "meas" => { // integer test of: measure{t in [a,b]: ||u t||<1/N} <= 2 l/N + 4/(N u)
        let trials:u64=a[2].parse().unwrap(); let mut rg=Rng(0xDEADBEEFCAFEF00D); let mut viol=0u64; let mut worst:f64=0.0; let mut skipped=0u64;
        for tr in 0..trials { let n=(3+rg.below(200)) as i128; let sh1=1+rg.below(40); let u=(1+rg.below(1u64<<sh1)) as i128; let sh2=1+rg.below(30); let d=(1+rg.below(1u64<<sh2)) as i128;
            // J = [an/d, bn/d] ; adversarial alignments in 1/3 of trials: an = round(d*c/u)
            let mut an=(rg.below((d as u64).min(1<<40)) as i128)%(d+1); let len=(rg.below((d as u64).min(1<<40)/4+1)) as i128 ; let mut bn=an+len;
            if tr%3==1 { let c=rg.below(u as u64) as i128; an=(d*c)/u; bn=an+ (rg.below(5) as i128)*(d/(u.max(1))+1); }
            if tr%3==2 { let c=rg.below(u as u64) as i128; an=(d*c)/u - 1; if an<0 {an=0;} bn=an+2; }
            let au=an*n*u; let bu=bn*n*u; let c0=(au - d).div_euclid(n*d*1)-1; // generous start
            // centers c/u ; band units: [ (cN-1)d , (cN+1)d ] in units 1/(N u d)
            let cmin=((an*n*u - d).div_euclid(n*d))-1; let cmax=((bn*n*u + d).div_euclid(n*d))+2; let _=c0;
            if (cmax-cmin)>300_000 { skipped+=1; continue; } let mut m:i128=0; let mut c=cmin; while c<=cmax { let lu=(c*n-1)*d; let ru=(c*n+1)*d; let lo= if lu>au {lu} else {au}; let hi= if ru<bu {ru} else {bu}; if hi>lo { m+=hi-lo; } c+=1; }
            let rhs=2*u*(bn-an)+4*d; if m>rhs { viol+=1; if viol<10 {println!("VIOL n={} u={} d={} an={} bn={} m={} rhs={}",n,u,d,an,bn,m,rhs);} }
            let ratio=(m as f64)/(rhs as f64); if ratio>worst {worst=ratio;} }
        println!("meas trials={} skipped(huge)={} violations={} worst measure/bound={:.6}",trials,skipped,viol,worst);
    }

    "core" => { // core N1 N2 K SAMPLEW1 CN CD LIM : lemma-level test of the proof: for EVERY clean prime D, the closed window J_D contains a good time of V.
        let n1:i128=a[2].parse().unwrap(); let n2:i128=a[3].parse().unwrap(); let k:i128=a[4].parse().unwrap(); let sw:usize=a[5].parse().unwrap();
        let cn:i128=a[6].parse().unwrap(); let cd:i128=a[7].parse().unwrap(); let lim:i128=a[8].parse().unwrap();
        let mut rg=Rng(0x234567ABCDEF0123u64 ^ (n1 as u64*7919));
        let (mut gsets,mut gclean,mut gfail,mut gunres,mut gnoclean,mut gnoc_bad,mut gunc_bad,mut gctl_fail,mut gctl_n)=(0u64,0u64,0u64,0u64,0u64,0u64,0u64,0u64,0u64);
        for n in n1..=n2 {
            let (mut sets,mut sclean,mut fail,mut unres,mut noclean,mut noc_bad)=(0u64,0u64,0u64,0u64,0u64,0u64); let (mut lt_,mut lf_,mut lu_)=(0u64,0u64,0u64); let mut ex=String::new(); let mut exn=String::new();
            let rtop= if a.len()>9 && a[9]=="half" {n/2} else {n-2};
            for r in 1..=rtop { let ps=wprimes(n,r); let crt=crt_list(n,r,&ps,lim); let bs=base(n,r);
                let gaps=gaps_of(&bs,1,n);
                // enumerate W of size 1..=k by chains
                let mut stack:Vec<Vec<i128>>=Vec::new();
                let l1=rel(None,n,k,&crt,&mut rg,lim); let mut first:Vec<i128>=l1.clone(); while first.len()>sw { let idx=rg.below(first.len() as u64) as usize; first.swap_remove(idx); }
                for &w1 in &first { stack.push(vec![w1]); }
                let mut work:Vec<Vec<i128>>=Vec::new();
                while let Some(wv)=stack.pop() { work.push(wv.clone());
                    if (wv.len() as i128)<k { let mut nxt=rel(Some(*wv.last().unwrap()),n,k,&crt,&mut rg,lim); nxt.retain(|&x| x>*wv.last().unwrap());
                        let cap= if wv.len()==1 { sw.max(20) } else { 12 }; while nxt.len()>cap { let idx=rg.below(nxt.len() as u64) as usize; nxt.swap_remove(idx); }
                        for x in nxt { let mut u=wv.clone(); u.push(x); stack.push(u); } } }
                for wv in work.iter() { sets+=1;
                    let (i,wi)=chain(n,k,wv,cn,cd); let small=&wv[..i];
                    let mut allsp=bs.clone(); allsp.extend_from_slice(wv);
                    let cleanps:Vec<i128>=ps.iter().cloned().filter(|&d| clean(d,r,small)).collect();
                    if cleanps.is_empty() { noclean+=1;
                        if let Some(g)=&gaps { let st=ge_split(g,wv,1,n); if st==0 { noc_bad+=1; if exn.len()<200 {exn.push_str(&format!(" ({};{:?})",r,wv));} } }
                        continue; }
                    sclean+=1;
                    for &d in &cleanps { let ainv=modinv(r,d); let dd=d*n*wi; let num=ainv*n*wi; let a_=(num-(2*n-d),dd); let b_=(num+(2*n-d),dd);
                        let large= i<wv.len(); match good_in(a_,b_,&allsp,1,n) { 1=>{ if large {lt_+=1;} }, 2=>{unres+=1; if large {lu_+=1;}}, _=>{ fail+=1; if large {lf_+=1;} if ex.len()<300 {ex.push_str(&format!(" (N{} r{} D{} W{:?} i{})",n,r,d,wv,i));} } } }
                    // negative control: a NON-clean prime (spoiled by a small speed) used the same way; the instrument must be able to fail
                    for &d in ps.iter() { if clean(d,r,small) {continue;} let ainv=modinv(r,d); let dd=d*n*wi; let num=ainv*n*wi; let a_=(num-(2*n-d),dd); let b_=(num+(2*n-d),dd);
                        gctl_n+=1; if good_in(a_,b_,&allsp,1,n)==0 { gctl_fail+=1; } }
                }
            }
            println!("CORE N={} K={} cn/cd={}/{} sets={} with_clean_prime={} J_fail={} J_unresolved={} no_clean_prime={} (of which ML<1/N: {}) LARGE-speed J tests: resolved_ok={} fail={} unresolved={} |{}|{}",n,k,cn,cd,sets,sclean,fail,unres,noclean,noc_bad,lt_,lf_,lu_,ex,exn);
            gsets+=sets; gclean+=sclean; gfail+=fail; gunres+=unres; gnoclean+=noclean; gnoc_bad+=noc_bad; let _=gunc_bad;
        }
        println!("CORE TOTAL N={}..{} K={} cn/cd={}/{}: sets={} with_clean={} J_FAIL={} J_UNRES={} no_clean={} (ML<1/N among them {}) ; neg-control (spoiled prime, J test): {} of {} fail",n1,n2,k,cn,cd,gsets,gclean,gfail,gunres,gnoclean,gnoc_bad,gctl_fail,gctl_n);
    }

    "mid" => { // mid N1 N2 K WCAP LIM : statement test (exact engine, gap method) for K=2 pairs: exhaustive pairs N<w1<w2<=WCAP (prefiltered by Lemma W with ANY admissible D coprime to r) + CRT-structured pairs up to LIM; r<=N/2.
        let n1:i128=a[2].parse().unwrap(); let n2:i128=a[3].parse().unwrap(); let wcap:usize=a[4].parse().unwrap(); let lim:i128=a[5].parse().unwrap(); let rmode_all= a.len()>6 && a[6]=="all";
        for n in n1..=n2 { let (mut tot,mut unw,mut bad,mut unres,mut pfail)=(0u64,0u64,0u64,0u64,0u64); let mut ex=String::new(); let mut badr:Vec<i128>=Vec::new(); let mut minpr=usize::MAX;
            let rmax= if rmode_all {n-2} else {n/2};
            for r in 1..=rmax { let ps=wprimes(n,r); if ps.len()<minpr {minpr=ps.len();}
                let adm:Vec<i128>=((n+1+r)..=(2*n-1)).filter(|&d| gcd(d,r)==1).collect();
                let nd=adm.len(); let words=(nd+63)/64; let bs=base(n,r); let gaps=match gaps_of(&bs,1,n){Some(g)=>g,None=>continue};
                if nd>0 && nd<=256 {
                    let mask=|w:i128|->[u64;4]{ let mut m=[0u64;4]; for (i,&d) in adm.iter().enumerate() { let y=w%d; if y!=0 && y!=r%d && y!=(d-r%d)%d { m[i/64]|=1<<(i%64);} } m };
                    let ms:Vec<[u64;4]>=((n+1)..=(wcap as i128)).map(|w|mask(w)).collect(); let _=words;
                    for i in 0..ms.len() { if rmode_all && 2*r>n && ((n+1+i as i128)%r==0) {continue;}
                        for j in (i+1)..ms.len() { if rmode_all && 2*r>n && ((n+1+j as i128)%r==0) {continue;} tot+=1;
                        let m=(ms[i][0]&ms[j][0])|(ms[i][1]&ms[j][1])|(ms[i][2]&ms[j][2])|(ms[i][3]&ms[j][3]); if m!=0 {continue;} unw+=1;
                        let wv=[n+1+i as i128,n+1+j as i128]; match ge_split(&gaps,&wv,1,n) { 0=>{bad+=1; if !badr.contains(&r) {badr.push(r);} if ex.len()<300 {ex.push_str(&format!(" ({};{},{})",r,wv[0],wv[1]));}}, 2=>{unres+=1;}, _=>{} } } }
                    // prefilter validation: sample witnessed pairs, check engine ge(2/D) for a witnessing D
                    let mut rg=Rng(77+(n as u64)*131+(r as u64));
                    for _ in 0..30 { let i=rg.below(ms.len() as u64) as usize; let j=rg.below(ms.len() as u64) as usize; if i==j {continue;}
                        let m=(ms[i][0]&ms[j][0])|(ms[i][1]&ms[j][1])|(ms[i][2]&ms[j][2])|(ms[i][3]&ms[j][3]); if m==0 {continue;}
                        let b=m.trailing_zeros() as usize; let d=adm[b]; let mut sp=bs.clone(); sp.push(n+1+i as i128); sp.push(n+1+j as i128);
                        if ge_full(&sp,2,d)!=1 {pfail+=1;} }
                }
                // CRT structured pairs up to lim
                let crt=crt_list(n,r,&ps,lim); let mut cl:Vec<i128>=crt.clone(); cl.truncate(80);
                for x in 0..cl.len() { for y in (x+1)..cl.len() { if cl[x]==cl[y] {continue;} let (w1,w2)=if cl[x]<cl[y] {(cl[x],cl[y])} else {(cl[y],cl[x])}; tot+=1;
                    match ge_split(&gaps,&[w1,w2],1,n) { 0=>{bad+=1; if !badr.contains(&r) {badr.push(r);} if ex.len()<300 {ex.push_str(&format!(" ({};{},{})",r,w1,w2));}}, 2=>{unres+=1;}, _=>{} } } }
            }
            println!("MID N={} K=2 WCAP={} sets={} unwitnessed(excl. crt)={} ML<1/N:{} unresolved={} min#primes={} prefilter_fail={} bad_r={:?} |{}",n,wcap,tot,unw,bad,unres,minpr,pfail,badr,ex);
        }
    }
    _=>{}
    }
}
