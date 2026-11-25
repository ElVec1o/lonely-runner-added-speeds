// x2.c (PROOF2 section 5.2/5.3): certified-complete search, NO cap on multipliers, for the class X2' of hypothetical rescued-tight sets (branch A, g>1):
//   exactly one failing entry i, rescued with z >= g (so r_i does not divide w_j and, by Corollary R2, m_i s_i < 3 beta_i), the other entry j non-failing: (9)_j(m_j) with m_j >= 3 (since w_j >= m_i(gA-r_i) > 2A).
// For every N, every tripable entry j (all b in [s_j,3s_j-1] non-units of r_j), every m_j in [3, mu_j], every r_i != r_j with gcd>1, r_i not dividing w_j = m_j r_j, every m_i with beta_i < m_i s_i < 3 beta_i:
//   necessary filter (R_beta: z beta = w_j mod r_i, m_i(zA-r_i) <= w_j, s_i w_j <= beta (zA+r_i)); survivors are tested EXACTLY by cov_dir_ex (the Dirichlet-window engine of lr2.c, valid for every multiplier).
// NOT covered (class X1): some w_j is a multiple of L (z = 0 rescue); counted as 'skipped'.   usage: x2 NMIN NMAX
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long i64; typedef __int128 i128;
static i64 gcd64(i64 a, i64 b){ while(b){ i64 t=a%b; a=b; b=t; } return a<0?-a:a; }
static i64 modinv(i64 a, i64 m){ i64 r0=m,r1=a%m,s0=0,s1=1; while(r1){ i64 q=r0/r1,t=r0-q*r1; r0=r1; r1=t; t=s0-q*s1; s0=s1; s1=t; } s0%=m; if(s0<0) s0+=m; return s0; }
typedef struct { i128 ln, hn, d; } iv;
static int cmp_iv(const void*a,const void*b){ const iv*x=a,*y=b; i128 l=x->ln*y->d, r=y->ln*x->d; return l<r?-1:(l>r?1:0); }
/* Dirichlet-window engine (copied verbatim from lr2.c cov_dir_ex, without the failure report): tau = p/q, here always tau = 1/A */
static int cov_dir(i64 N,i64 r1,i64 r2,i64 w1,i64 w2,i128 p,i128 q,i64*fr_,i64*fc_){
  i64 A=N+1; i64 rr[2]={r1,r2};
  for(int a=0;a<2;a++){ i64 r=rr[a];
    for(i64 c=1;c<r;c++){ if(gcd64(c,r)!=1) continue;
      iv b[256]; int nb=0; i64 u=r-modinv(c,r);
      i64 cand[2]={u,u+r};
      for(int k=0;k<2;k++){ i64 x=cand[k]; if(x<1||x>N||x==r1||x==r2) continue;
        b[nb].d=(i128)q*x; b[nb].ln=q-(i128)r*p; b[nb].hn=q+(i128)r*p; nb++; }
      i64 ws[2]={w1,w2};
      for(int k=0;k<2;k++){ i64 w=ws[k]; i64 z=(r-((w%r)*c)%r)%r;
        for(;;z+=r){ i128 ln=(i128)z*q-(i128)r*p; if((i128)A*ln>q*w) break; if(nb>=250){ fprintf(stderr,"too many bands\n"); exit(2); }
          b[nb].d=(i128)q*w; b[nb].ln=ln; b[nb].hn=(i128)z*q+(i128)r*p; nb++; } }
      for(int i=1;i<nb;i++){ iv t=b[i]; int j=i-1; while(j>=0 && cmp_iv(&b[j],&t)>0){ b[j+1]=b[j]; j--; } b[j+1]=t; }
      i128 rn=0, rd=1; int ok=0;
      for(int i=0;i<nb;i++){ if(b[i].ln*rd>rn*b[i].d) break; if(b[i].hn*rd>rn*b[i].d){ rn=b[i].hn; rd=b[i].d; } if(rn*A>=rd){ ok=1; break; } }
      if(!ok && rn*A>=rd) ok=1;
      if(!ok){ if(fr_){*fr_=r; *fc_=c;} return 0; } } }
  return 1;
}
static i64 beta_of(i64 N,i64 r){ i64 s=N+1-r; i64 b=s; while(gcd64(b,r)!=1) b++; return b; }
int main(int argc,char**argv){ i64 n0=atoll(argv[1]),n1=atoll(argv[2]);
  int pr[400],np=0; for(int x=2;x<=190;x++){ int ok=1; for(int d=2;d*d<=x;d++) if(x%d==0){ok=0;break;} if(ok) pr[np++]=x; }
  i64 nj=0,ntest=0,nsurv=0,ntight=0,nx1=0,ncheck=0;
  for(i64 N=n0;N<=n1;N++){ i64 A=N+1;
    for(i64 s=2;s<=60 && A-s>N/2;s++){ i64 rj=A-s; int ok=1;
      for(int k=0;k<np;k++){ if(pr[k]<s) continue; if(pr[k]>3*s-1) break; if(rj%pr[k]!=0){ ok=0; break; } }
      if(!ok) continue;
      for(i64 b=s;b<=3*s-1;b++) if(gcd64(b,rj)==1){ ok=0; break; }
      if(!ok) continue;
      i64 bj=beta_of(N,rj); i64 muj=bj/s; if(muj<3) continue; nj++;
      for(i64 mj=3;mj<=muj;mj++){ i64 p=mj*rj;
        for(i64 ri=N/2+1;ri<=N;ri++){ if(ri==rj) continue; i64 g=gcd64(ri,rj); if(g==1) continue;
          if(p%ri==0){ nx1++; continue; }
          i64 si=A-ri; i64 bi=beta_of(N,ri); i64 mmin=bi/si+1; if(mmin<2) mmin=2; i64 mmax=(3*bi-1)/si; if(mmin>mmax) continue;
          i64 inv=modinv(bi,ri); i64 z0=((p%ri)*inv)%ri;
          for(i64 mi=mmin;mi<=mmax;mi++){ if(mi*ri==p) continue; ntest++;
            int pass=0; for(i64 z=z0; ; z+=ri){ if((i128)mi*(z*A-ri)>p) break; if((i128)si*p<=(i128)bi*(z*A+ri)){ pass=1; break; } }
            if(!pass) continue; nsurv++;
            i64 r1=ri<rj?ri:rj, r2=ri<rj?rj:ri; i64 w1=(ri<rj)?mi*ri:p, w2=(ri<rj)?p:mi*ri;
            ncheck++; i64 fr_=0,fc_=0; int cv=cov_dir(N,r1,r2,w1,w2,1,A,&fr_,&fc_); if(!cv){ i64 uu=fr_-modinv(fc_,fr_); i64 xx=(uu+fr_<=N)?uu+fr_:uu; i64 sf=A-fr_; i64 mf=(fr_==ri)?mi:mj; printf("SURVIVOR-FAILS N=%lld r=%lld,%lld w=%lld,%lld (entry i: r_i=%lld m_i=%lld beta_i=%lld s_i=%lld; entry j: r_j=%lld m_j=%lld g=%lld) fails in class mod %lld (%s) at unit x=%lld, own m=%lld, m*s=%lld, x<m*s? %d\n",N,r1,r2,w1,w2,ri,mi,bi,si,rj,mj,g,fr_,(fr_==ri)?"entry i":"entry j",xx,mf,mf*sf,(int)(xx<mf*sf)); } if(cv){ ntight++; printf("RESCUED-TIGHT(X2) N=%lld r=%lld,%lld w=%lld,%lld m_i=%lld m_j=%lld\n",N,r1,r2,w1,w2,mi,mj); } } } } }
    if(N%20000==0){ printf("progress N=%lld tripable-entries=%lld tested=%lld survivors=%lld tight=%lld\n",N,nj,ntest,nsurv,ntight); fflush(stdout); } }
  printf("DONE x2 N=%lld..%lld tripable (N,j) pairs=%lld (m_i,m_j,r_i) tested=%lld survivors of necessary filter=%lld exact-tested=%lld TIGHT=%lld skipped(X1: r_i | w_j)=%lld\n",n0,n1,nj,ntest,nsurv,ncheck,ntight,nx1); return 0; }
