// exploration (long double, NOT a proof): for N=4..9 coprime (r1,r2), m1>=r2, m2>=r1:
// does class r2 (t=(c+eta)/r2) / class r1 give eta? does coarse counting (R1) hold?
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long double LD;
typedef struct {LD l,u;} Iv;
static int cmp(const void*a,const void*b){LD x=((Iv*)a)->l,y=((Iv*)b)->l;return x<y?-1:x>y;}
static int cover(Iv*v,int n,LD E){ // is (0,E] covered by open intervals
  qsort(v,n,sizeof(Iv),cmp);
  LD reach=0; int first=1; // need point 0 excluded: reach=0 means points >0 up to reach covered; need l<reach strictly unless reach==0 then l<=0
  for(int i=0;i<n;i++){
    if(first){ if(v[i].l>0) return 0; reach=v[i].u; first=0; if(reach>E) return 1; continue;}
    if(v[i].l>=reach) { if(v[i].l>reach+1e-15L) return 0; else return 0;} // touching point reach is uncovered
    if(v[i].u>reach) reach=v[i].u;
    if(reach>E) return 1;
  }
  return reach>E;
}
static Iv buf[100000];
// does there exist eta in (0,E] with ||a eta||>=tau and ||x0 - al*eta||>=tau ?
static int good(LD tau,LD E,LD a,LD al,LD x0){
  int n=0;
  for(int k=0;(k-tau)/a<E+1e-12L;k++){ buf[n].l=(k==0)?-1:(k-tau)/a; buf[n].u=(k+tau)/a; n++;}
  // phi(eta)=x0-al*eta, bad when |phi-k|<tau: eta in ((x0-k-tau)/al,(x0-k+tau)/al)
  int kmax=(int)floorl(x0+tau)+1;
  for(int k=kmax;k>=-2;k--){ LD l=(x0-k-tau)/al,u=(x0-k+tau)/al; if(u<=0) break; if(l>E) continue; buf[n].l=l; buf[n].u=u; n++; }
  return !cover(buf,n,E);
}
int main(int argc,char**argv){
  int M=atoi(argv[1]);
  for(int N=4;N<=9;N++) for(int r1=N/2+1;r1<=N;r1++) for(int r2=r1+1;r2<=N;r2++){
    int g=r1,h=r2; while(h){int t=g%h;g=h;h=t;} if(g!=1) continue;
    LD tau=1.0L/N, E2=(2.0L*N-r2)/((LD)N*N);
    int u=r2-r1; LD E1=fminl((2.0L*N-r1)/((LD)N*N),(1.0L-(LD)r1/N)/u);
    long tot=0,f_r1coarse=0,fail2=0,fail1=0,failboth=0; int maxm1_fail2=0,maxm2_fail2=0,maxm1_fail1=0,maxm2_fail1=0,maxm1_fb=0,maxm2_fb=0,maxm1_c=0,maxm2_c=0;
    for(int m1=r2;m1<=M;m1++) for(int m2=r1;m2<=M;m2++){
      tot++;
      // coarse inequality: N(N+2)(m1 r1+2 r2 m2) < (2N-r2)(N-4) m1 m2 r1
      __int128 lhs=(__int128)N*(N+2)*((__int128)m1*r1+2*(__int128)r2*m2), rhs=(__int128)(2*N-r2)*(N-4)*m1*(__int128)m2*r1;
      int coarse=lhs<rhs; if(!coarse){f_r1coarse++; if(m1>maxm1_c)maxm1_c=m1; if(m2>maxm2_c)maxm2_c=m2;}
      LD al=(LD)m1*r1/r2, x0=(LD)m1/r2;
      int g2=good(tau,E2,(LD)m2,al,x0);
      // class r1: own mult m1, other m2: phi'=m2(1-r2 eta)/r1 = m2/r1 - (m2 r2/r1) eta
      int g1=good(tau,E1,(LD)m1,(LD)m2*r2/r1,(LD)m2/r1);
      if(!g2){fail2++; if(m1>maxm1_fail2)maxm1_fail2=m1; if(m2>maxm2_fail2)maxm2_fail2=m2;}
      if(!g1){fail1++; if(m1>maxm1_fail1)maxm1_fail1=m1; if(m2>maxm2_fail1)maxm2_fail1=m2;}
      if(!g1&&!g2){failboth++; if(m1>maxm1_fb)maxm1_fb=m1; if(m2>maxm2_fb)maxm2_fb=m2;}
    }
    printf("N=%d (%d,%d) E2=%.4Lf E1=%.4Lf tot=%ld coarseFail=%ld(max m1 %d m2 %d) fail_r2=%ld(max %d,%d) fail_r1=%ld(max %d,%d) failBoth=%ld(max %d,%d)\n",N,r1,r2,E2,E1,tot,f_r1coarse,maxm1_c,maxm2_c,fail2,maxm1_fail2,maxm2_fail2,fail1,maxm1_fail1,maxm2_fail1,failboth,maxm1_fb,maxm2_fb);
  }
}
