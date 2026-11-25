// b1.c: search for N, r1<r2 in (N/2,N], g=gcd>1, such that w=L=lcm(r1,r2) (k=1, the weakest multiplier) satisfies criterion (9) for BOTH entries
// (m1=r2/g for r1, m2=r1/g for r2): no unit mod r_i in [s_i, m_i s_i -1].  Also coprime pairs with k=1 (for information).  usage: b1 NMIN NMAX
#include <stdio.h>
#include <stdlib.h>
typedef long long i64;
static i64 gcd(i64 a,i64 b){while(b){i64 t=a%b;a=b;b=t;}return a;}
static i64 beta_of(i64 N,i64 r){i64 s=N+1-r,b=s;while(gcd(b,r)!=1)b++;return b;}
int main(int argc,char**argv){ i64 n0=atoll(argv[1]),n1=atoll(argv[2]); i64 found=0,foundc=0,pairs=0;
 for(i64 N=n0;N<=n1;N++){ i64 A=N+1; 
  for(i64 r1=N/2+1;r1<=N;r1++){ i64 s1=A-r1,b1=beta_of(N,r1);
   for(i64 r2=r1+1;r2<=N;r2++){ i64 g=gcd(r1,r2); i64 s2=A-r2; pairs++;
     i64 m1=r2/g,m2=r1/g; if(g==1){m1=r2;m2=r1;}
     if(b1>=m1*s1){ i64 b2=beta_of(N,r2); if(b2>=m2*s2){ if(g>1){found++; printf("B1 N=%lld r=%lld,%lld g=%lld m=(%lld,%lld) beta=(%lld,%lld) s=(%lld,%lld)\n",N,r1,r2,g,m1,m2,b1,b2,s1,s2);} else {foundc++; printf("B1coprime N=%lld r=%lld,%lld\n",N,r1,r2);} } } } } }
 printf("DONE b1 N=%lld..%lld pairs=%lld B1 gcd>1: %lld  B1 coprime: %lld\n",n0,n1,pairs,found,foundc); return 0; }
