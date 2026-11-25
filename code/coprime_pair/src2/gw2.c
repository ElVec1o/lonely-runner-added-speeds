// gw2.c (PROOF2 G3): complete list of two-entry Goddyn-Wong (9)-sets V = ([N]\{r1,r2}) u {m1 r1, m2 r2}, N/2 < r1 < r2 <= N, m_i >= 2, w1 != w2, with (9) for both entries:
//   (9)_i: no unit b of r_i in [s_i, m_i s_i - 1], s_i = N+1-r_i.   Entry r is "active" iff (9) holds with m=2 : every b in [s,2s-1] has gcd(b,r)>1; its maximal multiplier is mu_r = floor(beta_r/s_r), beta_r = least unit >= s_r.
//   s=1 is never active (b=1).  An active entry needs every prime of [s,2s-1] to divide r (a prime b is its own factor), so s <= S_MAX=60 for N <= 10^9 (product of the >=13 primes in [s,2s-1], s>=61, exceeds 10^23).
//   Prints, for each N in range with >= 2 active entries having gcd>1 (and, separately, any coprime pair of active entries), the pair, mu's and the number of sets.   usage: gw2 NMIN NMAX
#include <stdio.h>
#include <stdlib.h>
typedef long long i64;
static i64 gcd64(i64 a,i64 b){ while(b){ i64 t=a%b; a=b; b=t; } return a<0?-a:a; }
int main(int argc,char**argv){ i64 n0=atoll(argv[1]),n1=atoll(argv[2]);
  int pr[200],np=0; for(int x=2;x<=130;x++){ int ok=1; for(int d=2;d*d<=x;d++) if(x%d==0){ok=0;break;} if(ok) pr[np++]=x; }
  i64 nN=0,nsets=0,ncop=0,nact=0;
  { /* PRECHECK: for every s in [61, n1/2] there are >= 4 primes in [s,2s-1]; each >= 61, so their product >= 61^4 = 13,845,841 > 10^7: no active entry has s >= 61 when N <= 10^7 */
    i64 M=n1+2; if(M>20000000){ fprintf(stderr,"N range too large for the s<=60 argument\n"); return 2; }
    unsigned char*cp=calloc(M+1,1); int*pc=malloc(sizeof(int)*(M+1)); for(i64 i=2;i<=M;i++) cp[i]=1; for(i64 i=2;i*i<=M;i++) if(cp[i]) for(i64 j=i*i;j<=M;j+=i) cp[j]=0;
    pc[0]=0; pc[1]=0; for(i64 i=2;i<=M;i++) pc[i]=pc[i-1]+cp[i];
    i64 bad=0,minc=1000000; for(i64 s=61;2*s-1<=M;s++){ int c=pc[2*s-1]-pc[s-1]; if(c<minc) minc=c; if(c<4) bad++; }
    printf("PRECHECK s in [61,%lld]: min #primes in [s,2s-1] = %lld, s with <4 primes = %lld (must be 0; then s<=60 suffices for N<=10^7)\n",(M+1)/2,minc,bad); free(cp); free(pc); if(bad){ return 3; } }
  for(i64 N=n0;N<=n1;N++){ i64 A=N+1; i64 ar[64],as[64],amu[64]; int na=0;
    for(i64 s=2;s<=60 && s< A-N/2 ;s++){ i64 r=A-s; if(r<=N/2) break; int ok=1;
      for(int k=0;k<np;k++){ if(pr[k]<s) continue; if(pr[k]>2*s-1) break; if(r%pr[k]!=0){ ok=0; break; } }
      if(!ok) continue;
      for(i64 b=s;b<=2*s-1;b++) if(gcd64(b,r)==1){ ok=0; break; }
      if(!ok) continue;
      i64 beta=s; while(gcd64(beta,r)!=1) beta++; ar[na]=r; as[na]=s; amu[na]=beta/s; na++; }
    nact+=na;
    if(na<2) continue;
    for(int i=0;i<na;i++) for(int j=i+1;j<na;j++){ i64 r1=ar[i]<ar[j]?ar[i]:ar[j], r2=ar[i]<ar[j]?ar[j]:ar[i]; i64 mu1=ar[i]<ar[j]?amu[i]:amu[j], mu2=ar[i]<ar[j]?amu[j]:amu[i]; i64 s1=A-r1,s2=A-r2; i64 g=gcd64(r1,r2);
      i64 cnt=0; for(i64 m1=2;m1<=mu1;m1++) for(i64 m2=2;m2<=mu2;m2++) if(m1*r1!=m2*r2) cnt++;
      if(g==1){ ncop++; printf("COPRIME-ACTIVE-PAIR N=%lld r=%lld,%lld mu=%lld,%lld\n",N,r1,r2,mu1,mu2); continue; }
      if(cnt>0){ nN++; nsets+=cnt; printf("N=%lld r=%lld,%lld (s=%lld,%lld) g=%lld mu=%lld,%lld sets=%lld\n",N,r1,r2,s1,s2,g,mu1,mu2,cnt); } } }
  printf("DONE gw2 N=%lld..%lld active entries total=%lld ; pairs with gcd>1 and >=1 set: %lld pairs, %lld sets ; coprime active pairs=%lld\n",n0,n1,nact,nN,nsets,ncop); return 0; }
