// lemz.c: numeric checks of the structural lemmas of PROOF2 (exact integers).
//  Z : for r_i < r_j in (N/2,N], g=gcd(r_i,r_j), gamma=r_j/g:  beta_i < gamma s_i   (so (9)(r_i, mu) fails for all mu >= gamma; entry 1 of any lcm-branch set always fails)
//      also checks the inequality (gamma-1) s_i > r_i that proves it.
//  ZG: for r_i > r_j (the larger entry): reports how often beta_i >= gamma_j' s_i could hold, i.e. is Lemma Z FALSE for the larger entry (it must be false in general; counts the exceptions).
//  usage: lemz NMIN NMAX
#include <stdio.h>
#include <stdlib.h>
typedef long long i64;
static i64 gcd64(i64 a,i64 b){ while(b){ i64 t=a%b; a=b; b=t; } return a<0?-a:a; }
static i64 beta_of(i64 N,i64 r){ i64 s=N+1-r,b=s; while(gcd64(b,r)!=1) b++; return b; }
int main(int argc,char**argv){ i64 n0=atoll(argv[1]),n1=atoll(argv[2]); i64 tot=0,vz=0,vin=0,larger_ok=0,larger_tot=0;
  for(i64 N=n0;N<=n1;N++){ i64 A=N+1; for(i64 ri=N/2+1;ri<=N;ri++){ i64 si=A-ri,bi=beta_of(N,ri);
      for(i64 rj=ri+1;rj<=N;rj++){ i64 g=gcd64(ri,rj),gam=rj/g,alp=ri/g; tot++;
        if(!(bi<gam*si)){ vz++; if(vz<=5) printf("LemmaZ FAIL N=%lld ri=%lld rj=%lld beta=%lld gamma*s=%lld\n",N,ri,rj,bi,gam*si); }
        if(!((gam-1)*si>ri)){ vin++; if(vin<=5) printf("INEQ FAIL N=%lld ri=%lld rj=%lld\n",N,ri,rj); }
        /* larger entry rj, other ri: is beta_j >= alp * s_j possible ? (alp = r_i/g) */
        i64 sj=A-rj,bj=beta_of(N,rj); larger_tot++; if(bj>=alp*sj) larger_ok++; } } }
  printf("DONE lemz N=%lld..%lld pairs=%lld LemmaZ violations=%lld ineq (gamma-1)s>r violations=%lld | larger entry: beta_j >= (r_i/g) s_j holds for %lld of %lld pairs\n",n0,n1,tot,vz,vin,larger_ok,larger_tot); return 0; }
