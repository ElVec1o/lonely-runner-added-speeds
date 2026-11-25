// lemf.c (PROOF2 Lemma R test).  Unit class of modulus r < A (A = N+1), s = A - r, either FREE (omega = 1/A, any unit c) or with blocker x (unit of r, s <= x <= N, c x = -1 mod r, omega = s/(A x)).
// Bands of speed w in eta (t=(c+eta)/r):  [(zA-r)/(Aw), (zA+r)/(Aw)],  z = -w c (mod r), z >= 0.
// Claim tested (Lemma R, necessary conditions; exact rational sweep): let w = m r (m >= 2), p >= A, p != w, omega > 1/(Am) (i.e. m s > x, or free).  If [0, omega) is covered by the bands of w and p,
// then there is z >= 0, z = -p c (mod r), with  (b) m(zA - r) <= p  and  (c') (zA + r)/p >= min(N/m, A omega)   [A omega = 1 (free) or s/x].
// Also tests Corollary R2: z >= 2 forces m s < 3 x (blocker case).   Control (ctl=1): (b) is strengthened by 1 unit of p (must produce counterexamples).
// usage: lemf AMIN AMAX MMAX PMAX ctl
#include <stdio.h>
#include <stdlib.h>
typedef long long i64; typedef __int128 i128;
static i64 gcd64(i64 a,i64 b){ while(b){ i64 t=a%b; a=b; b=t; } return a<0?-a:a; }
static i64 modinv(i64 a,i64 m){ i64 r0=m,r1=a%m,s0=0,s1=1; while(r1){ i64 q=r0/r1,t=r0-q*r1; r0=r1; r1=t; t=s0-q*s1; s0=s1; s1=t; } s0%=m; if(s0<0) s0+=m; return s0; }
typedef struct { i128 n,d; } fr;
static int cmpf(fr a,fr b){ i128 l=a.n*b.d, r=b.n*a.d; return l<r?-1:(l>r?1:0); }
typedef struct { fr lo,hi; } bd;
static int cmpbd(const void*x,const void*y){ return cmpf(((const bd*)x)->lo,((const bd*)y)->lo); }
static int addbands(bd*b,int nb,i64 A,i64 r,i64 c,i64 w){ i64 z0=(( -( (w%r)*c)%r)+r)%r; for(i64 z=z0; z*A-r<=w; z+=r){ b[nb].lo=(fr){(i128)z*A-r,(i128)A*w}; b[nb].hi=(fr){(i128)z*A+r,(i128)A*w}; nb++; } return nb; }
int main(int argc,char**argv){ i64 a0=atoll(argv[1]),a1=atoll(argv[2]),mm=atoll(argv[3]),pm=atoll(argv[4]); int ctl=atoi(argv[5]);
  i64 tot=0,cov=0,viol=0,viol2=0,condnocov=0,nontriv=0; static bd b[200000];
  for(i64 A=a0;A<=a1;A++){ i64 N=A-1; for(i64 r=N/2+1;r<=N;r++){ i64 s=A-r;
    for(i64 x=0;x<=N;x++){ /* x=0: free class; else blocker x */
      i64 c; fr om;
      if(x==0){ c=1; om=(fr){1,A}; } else { if(x<s||gcd64(x,r)!=1) continue; c=(r-modinv(x,r))%r; om=(fr){s,(i128)A*x}; }
      for(i64 m=2;m<=mm;m++){ i64 w=m*r;
        /* need omega > 1/(A m):  free, or m s > x */
        fr own=(fr){1,(i128)A*m}; if(cmpf(om,own)<=0) continue;
        for(i64 p=A;p<=pm;p++){ if(p==w) continue; tot++;
          int nb=0; nb=addbands(b,nb,A,r,c,w); nb=addbands(b,nb,A,r,c,p); qsort(b,nb,sizeof(bd),cmpbd);
          fr reach=(fr){0,1}; int ok=0;
          for(int i=0;i<nb;i++){ if(cmpf(b[i].lo,reach)>0) break; if(cmpf(b[i].hi,reach)>0) reach=b[i].hi; if(cmpf(reach,om)>=0){ ok=1; break; } }
          i64 z0=(( -( (p%r)*c)%r)+r)%r; int cond=0; i64 zfound=-1;
          for(i64 z=z0; ; z+=r){ i128 lhs=(i128)m*(z*A-r)+(ctl?1:0); if(lhs>p) break;
            /* (c'): (zA+r)/p >= min(N/m, s/x) (blocker) or min(N/m,1) (free).  min(N/m, X) with X = s/x or 1 : (zA+r) >= p*min(N/m,X) */
            i128 lhsC=(i128)(z*A+r);
            /* compare lhsC against p * N/m  and p * X  : need lhsC >= min(...) <=> lhsC >= p N/m  OR  lhsC >= p X */
            int c1 = (lhsC*m >= (i128)p*N);
            int c2 = (x==0) ? (lhsC >= p) : (lhsC*x >= (i128)p*s);
            if(c1||c2){ cond=1; zfound=z; break; } }
          if(ok){ cov++; if(!cond){ viol++; if(viol<=10) printf("COUNTEREXAMPLE(b,c') A=%lld r=%lld x=%lld m=%lld p=%lld covered but conditions fail\n",A,r,x,m,p); }
            if(x>0){ /* R2: any admissible z>=2 must have m s < 3x : test all z satisfying (b),(c') with z>=2 */
              for(i64 z=z0; ; z+=r){ i128 lhs=(i128)m*(z*A-r); if(lhs>p) break; i128 lhsC=(i128)(z*A+r); int c1=(lhsC*m>=(i128)p*N), c2=(lhsC*x>=(i128)p*s); if((c1||c2)&&z>=2){ nontriv++; if(!(m*s<3*x)){ viol2++; if(viol2<=10) printf("COUNTEREXAMPLE(R2) A=%lld r=%lld x=%lld m=%lld p=%lld z=%lld\n",A,r,x,m,p,z); } } } } }
          else if(cond) condnocov++; } } } } }
  printf("DONE lemf A=%lld..%lld m<=%lld p<=%lld control=%d tested=%lld covered=%lld (b,c') violations=%lld R2: admissible z>=2 cases=%lld violations=%lld  cond-but-not-covered=%lld\n",a0,a1,mm,pm,ctl,tot,cov,viol,nontriv,viol2,condnocov); return 0; }
