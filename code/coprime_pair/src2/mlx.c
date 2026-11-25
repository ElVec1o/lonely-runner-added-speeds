// mlx.c: exact ML of ([N]\{r1,r2}) u {w1,w2}.  usage: mlx N r1 r2 w1 w2   (candidate times n/(vi+vj), exact integers)
#include <stdio.h>
#include <stdlib.h>
typedef long long i64;
static i64 gcd64(i64 a,i64 b){ while(b){ i64 t=a%b; a=b; b=t; } return a<0?-a:a; }
int main(int argc,char**argv){ i64 N=atoll(argv[1]),r1=atoll(argv[2]),r2=atoll(argv[3]),w1=atoll(argv[4]),w2=atoll(argv[5]); i64 v[4000],cnt=0;
 for(i64 x=1;x<=N;x++) if(x!=r1&&x!=r2) v[cnt++]=x; v[cnt++]=w1; v[cnt++]=w2;
 i64 bn=0,bd=1;
 for(int i=0;i<cnt;i++) for(int j=i;j<cnt;j++){ i64 s=v[i]+v[j]; for(i64 n=1;n<=s/2;n++){ i64 mn=s; for(int k=0;k<cnt;k++){ i64 x=(n*v[k])%s; i64 f=(2*x>s)?s-x:x; if(f<mn){ mn=f; if(mn*bd<=bn*s) break; } } if(mn*bd>bn*s){ bn=mn; bd=s; } } }
 i64 g=gcd64(bn,bd); printf("ML=%lld/%lld = %.6f ; 1/(N+1)=%.6f 1/N=%.6f 2/(2N+1)=%.6f\n",bn/g,bd/g,(double)bn/bd,1.0/(N+1),1.0/N,2.0/(2*N+1)); return 0; }
