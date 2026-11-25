// regions for N=5..9: R1 (coarse count), S2 (class r2, A-piece j=0, B counted), S1 (class r1, A'-piece j=0), leftover box
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long double LD;
static LD mn(LD a,LD b){return a<b?a:b;}
// P2: alpha*l*(1-2tau) > 2tau(1+2tau)
static int P2(LD tau,LD al,LD l){ return l>0 && al*l*(1-2*tau) > 2*tau*(1+2*tau); }
int main(int argc,char**argv){
  int M=atoi(argv[1]);
  for(int N=5;N<=9;N++) for(int r1=N/2+1;r1<=N;r1++) for(int r2=r1+1;r2<=N;r2++){
    int g=r1,h=r2; while(h){int t=g%h;g=h;h=t;} if(g!=1) continue;
    LD tau=1.0L/N, E2=(2.0L*N-r2)/((LD)N*N);
    int u=r2-r1; LD E1=mn((2.0L*N-r1)/((LD)N*N),(1.0L-(LD)r1/N)/u);
    long left=0; int mx1=0,mx2=0; int totR1=0;
    for(int m1=r2;m1<=M;m1++) for(int m2=r1;m2<=M;m2++){
      __int128 lhs=(__int128)N*(N+2)*((__int128)m1*r1+2*(__int128)r2*m2), rhs=(__int128)(2*N-r2)*(N-4)*m1*(__int128)m2*r1;
      int R1=lhs<rhs; // note: this is "coarse holds"
      LD al=(LD)m1*r1/r2; LD y1=tau/m2; LD l=mn((1-tau)/m2,E2)-y1; int S2=P2(tau,al,l);
      LD al1=(LD)m2*r2/r1; LD y1b=tau/m1; LD lb=mn((1-tau)/m1,E1)-y1b; int S1=P2(tau,al1,lb);
      if(!(R1||S2||S1)){left++; if(m1>mx1)mx1=m1; if(m2>mx2)mx2=m2;}
    }
    printf("N=%d (%d,%d) leftover=%ld maxm1=%d maxm2=%d\n",N,r1,r2,left,mx1,mx2);
  }
}
