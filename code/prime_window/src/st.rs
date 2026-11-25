// st.rs. Exact integer tests of the conjectured Theorem S (k-robustness):
//   for r <= N/2 and any set W of k further speeds (w != r), ML(([N]\{r}) u W) >= 1/N   (N >= N0(k)).
// N = number of the base interval [N]; ML(V)=max_t min_v ||tv||. ge() copied from BK_more/hb.rs (exact sweep, i128 cross-multiplication).
// modes:
//  ctl                     controls (known values; planted exception [13]\{6} u {69} must be < 1/13)
//  rob2 N1 N2 WCAP [RMODE] exhaustive pairs N < w1 < w2 <= WCAP ; RMODE=low (r<=N/2, default) or all (every r<=N-2)
//  rob3 N1 N2 WCAP         exhaustive triples, r <= N/2
//  crt2 N1 N2 WMAX         adversarial: every assignment of the window primes to (j,e), j in {1,2}, e in {0,1,-1}; CRT lifts <= WMAX
// witness prefilter: (D,j), N+2 <= D <= 2N, all retained x have (j x mod D) in [2,D-2]; a set is witnessed if some (D,j) also has every w there (then ML >= 2/D >= 1/N).
use std::env;
fn gcd(a:u64,b:u64)->u64{ if b==0 {a} else {gcd(b,a%b)} }
fn ge(v:&[u64], p:u64, q:u64, buf:&mut Vec<(i64,i64,i64)>) -> bool {
    buf.clear();
    let vmin=*v.iter().min().unwrap();
    for &x in v { let kmax=x/2+1; for k in 1..=kmax { buf.push(((k*q) as i64 - p as i64, (k*q+p) as i64, (x*q) as i64)); } }
    buf.sort_unstable_by(|a,b| ((a.0 as i128)*(b.2 as i128)).cmp(&((b.0 as i128)*(a.2 as i128))));
    let mut rn:i128=p as i128; let mut rd:i128=(vmin*q) as i128;
    for &(lo,hi,d) in buf.iter() {
        if 2*rn>rd { return false; }
        if (lo as i128)*rd >= rn*(d as i128) { return true; }
        if (hi as i128)*rd > rn*(d as i128) { rn=hi as i128; rd=d as i128; }
    }
    2*rn<=rd
}
fn wits(n:u64,r:u64)->Vec<(u64,u64)>{ let mut l=Vec::new();
    for d in (n+2)..=(2*n) { for j in 1..=d/2 { if (1..=n).filter(|&x|x!=r).all(|x|{let y=(j*x)%d; y>=2&&y<=d-2}) { l.push((d,j)); } } } l }
fn mask(l:&[(u64,u64)],w:u64)->[u64;4]{ let mut m=[0u64;4]; for (i,&(d,j)) in l.iter().enumerate() { if i>=256 {break;} let y=((w%d)*j)%d; if y>=2&&y<=d-2 { m[i/64]|=1<<(i%64); } } m }
fn and(a:&[u64;4],b:&[u64;4])->[u64;4]{ [a[0]&b[0],a[1]&b[1],a[2]&b[2],a[3]&b[3]] }
fn nz(a:&[u64;4])->bool{ a[0]|a[1]|a[2]|a[3]!=0 }
fn isprime(x:u64)->bool{ if x<2 {return false;} let mut d=2; while d*d<=x { if x%d==0 {return false;} d+=1; } true }
fn main(){
    let a:Vec<String>=env::args().collect(); let mut buf:Vec<(i64,i64,i64)>=Vec::new();
    match a[1].as_str() {
    "ctl" => {
        let mut t=|v:Vec<u64>,p:u64,q:u64,exp:bool|{ let g=ge(&v,p,q,&mut buf); println!("ctl max={} n={} >= {}/{} : {} (expected {}) {}",v.iter().max().unwrap(),v.len(),p,q,g,exp,if g==exp{"OK"}else{"FAIL"}); };
        t((1..=8).collect(),1,9,true); t((1..=8).collect(),1001,9000,false);
        let mut v:Vec<u64>=(1..=13).filter(|&x|x!=6).collect(); v.push(69); t(v.clone(),3,40,true); t(v.clone(),3001,40000,false); t(v,1,13,false);
        let mut v:Vec<u64>=(1..=14).filter(|&x|x!=6).collect(); v.push(69); t(v.clone(),1,14,true);
        t(vec![1,3,4,7],1,5,true); t(vec![1,3,4,7],1001,5000,false);
        // witness list sanity: N=14,r=6 must contain D=23 and D=25 with j=r^-1
        let l=wits(14,6); println!("wits(14,6) count={} has D=23:{} D=25:{}",l.len(),l.iter().any(|x|x.0==23),l.iter().any(|x|x.0==25));
    }
    "rob2" => {
        let n1:u64=a[2].parse().unwrap(); let n2:u64=a[3].parse().unwrap(); let wc:u64=a[4].parse().unwrap(); let all=a.len()>5 && a[5]=="all";
        for n in n1..=n2 { let (mut tot,mut unw,mut bad)=(0u64,0u64,0u64); let mut ex=String::new(); let mut minl=usize::MAX; let mut badr:Vec<u64>=Vec::new();
            let rmax=if all {n-2} else {n/2};
            for r in 1..=rmax { let l=wits(n,r); if l.len()<minl {minl=l.len();} let base:Vec<u64>=(1..=n).filter(|&x|x!=r).collect();
                let ms:Vec<[u64;4]>=(0..=wc).map(|w|mask(&l,w)).collect(); let mut badhere=0u64;
                for w1 in (n+1)..=wc { let m1=ms[w1 as usize];
                    // for r > N/2 skip multiples of r (the known multiplicative exceptions) when RMODE=all
                    if all && 2*r>n && w1%r==0 { continue; }
                    for w2 in (w1+1)..=wc { if all && 2*r>n && w2%r==0 { continue; } tot+=1;
                    if nz(&and(&m1,&ms[w2 as usize])) { continue; } unw+=1;
                    let mut v=base.clone(); v.push(w1); v.push(w2);
                    if !ge(&v,1,n,&mut buf) { bad+=1; badhere+=1; if ex.len()<700 { ex.push_str(&format!(" ({};{},{})",r,w1,w2)); } }
                }}
                if badhere>0 { badr.push(r); }
            }
            println!("ROB2 N={} W={} rmax={} sets={} min#wit={} unwitnessed={} ML<1/N:{} bad_r={:?} |{}",n,wc,rmax,tot,minl,unw,bad,badr,ex);
        }
    }
    "rob3" => {
        let n1:u64=a[2].parse().unwrap(); let n2:u64=a[3].parse().unwrap(); let wc:u64=a[4].parse().unwrap();
        for n in n1..=n2 { let (mut tot,mut unw,mut bad)=(0u64,0u64,0u64); let mut ex=String::new();
            for r in 1..=n/2 { let l=wits(n,r); let base:Vec<u64>=(1..=n).filter(|&x|x!=r).collect();
                let ms:Vec<[u64;4]>=(0..=wc).map(|w|mask(&l,w)).collect();
                for w1 in (n+1)..=wc { for w2 in (w1+1)..=wc { let m12=and(&ms[w1 as usize],&ms[w2 as usize]); for w3 in (w2+1)..=wc { tot+=1;
                    if nz(&and(&m12,&ms[w3 as usize])) { continue; } unw+=1;
                    let mut v=base.clone(); v.push(w1); v.push(w2); v.push(w3);
                    if !ge(&v,1,n,&mut buf) { bad+=1; if ex.len()<700 { ex.push_str(&format!(" ({};{},{},{})",r,w1,w2,w3)); } }
                }}}
            }
            println!("ROB3 N={} W={} sets={} unwitnessed={} ML<1/N:{} |{}",n,wc,tot,unw,bad,ex);
        }
    }
    "crt2" => {
        let n1:u64=a[2].parse().unwrap(); let n2:u64=a[3].parse().unwrap(); let wmax:u64=a[4].parse().unwrap();
        for n in n1..=n2 { let (mut tot,mut unw,mut bad,mut skipped)=(0u64,0u64,0u64,0u64); let mut ex=String::new(); let mut minp=usize::MAX;
            for r in 1..=n/2 { let ps:Vec<u64>=((n+1+r)..=(2*n)).filter(|&x|isprime(x)).collect(); if ps.len()<minp {minp=ps.len();}
                if ps.len()>8 { skipped+=1; continue; }
                let l=wits(n,r); let base:Vec<u64>=(1..=n).filter(|&x|x!=r).collect();
                let na=6u64.pow(ps.len() as u32);
                for code in 0..na { let mut c=code; let mut md=[1u64,1u64]; let mut rs=[0u64,0u64]; let mut ok=true;
                    for &p in ps.iter() { let j=(c%2) as usize; c/=2; let e=c%3; c/=3; let res=match e {0=>0,1=>r%p,_=>p-(r%p)};
                        // CRT combine (rs[j] mod md[j]) with (res mod p)
                        if md[j].saturating_mul(p)>wmax { ok=false; break; }
                        let mut x=rs[j]; while x%p!=res { x+=md[j]; } rs[j]=x; md[j]*=p; }
                    if !ok { continue; }
                    for t1 in 0..3u64 { let w1=rs[0]+t1*md[0]; if w1<=n || w1>wmax { continue; }
                    for t2 in 0..3u64 { let w2=rs[1]+t2*md[1]; if w2<=n || w2>wmax || w2==w1 { continue; } tot+=1;
                        if nz(&and(&mask(&l,w1),&mask(&l,w2))) { continue; } unw+=1;
                        let mut v=base.clone(); v.push(w1); v.push(w2);
                        if !ge(&v,1,n,&mut buf) { bad+=1; if ex.len()<700 { ex.push_str(&format!(" ({};{},{})",r,w1,w2)); } }
                    }}
                }
            }
            println!("CRT2 N={} WMAX={} min#primes={} r_skipped={} sets={} unwitnessed={} ML<1/N:{} |{}",n,wmax,minp,skipped,tot,unw,bad,ex);
        }
    }
    _=>{}
    }
}
