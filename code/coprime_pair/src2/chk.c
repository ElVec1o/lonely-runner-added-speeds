// chk.c: exact Dirichlet-window test (cov_dir of x2.c) of ONE set: N r1 r2 m1 m2 -> covered at 1/A (Cov) ; witness t=1/A valid iff A does not divide w1, w2 (then ML = 1/A exactly).
#define main x2_main_unused
#include "x2v.c"
#undef main
int main(int argc,char**argv){ i64 N=atoll(argv[1]),r1=atoll(argv[2]),r2=atoll(argv[3]),m1=atoll(argv[4]),m2=atoll(argv[5]); i64 A=N+1,w1=m1*r1,w2=m2*r2;
  int cv=cov_dir(N,r1,r2,w1,w2,1,A,0,0); int wit=(w1%A!=0&&w2%A!=0);
  printf("N=%lld r=%lld,%lld m=%lld,%lld w=%lld,%lld gcd=%lld : Cov(1/A)=%d witness(t=1/A valid)=%d => %s\n",N,r1,r2,m1,m2,w1,w2,gcd64(r1,r2),cv,wit,(cv&&wit)?"ML = 1/(N+1) exactly (tight)":(cv?"ML <= 1/A (witness invalid)":"NOT tight (ML > 1/A)")); return 0; }
