// cert.c.  CERTIFIED-COMPLETE finite check over ALL inserted pairs w1 != w2 (integers >= N+1, not only multiples of r_i).
// For N, R={r1,r2}, level tau=p/q:   Ret=[N]\R ;  G0 = {t in [0,1/2] : ||v t|| >= tau for all v in Ret} (finite union of closed intervals, exact rationals).
// Claim checked: for every pair w1 != w2, w_i >= N+1, there is t with ||v t|| >= tau for all v in Ret u {w1,w2}  (i.e. ML(V) >= tau), except the listed exceptions.
// Completeness (no cap on w):  (i) both w >= W0g : two-speed counting lemma,  l (1-4 tau) > 2 tau (1+2 tau)(1/w1+1/w2)  with l = longest interval of G0 (needs q > 4p);
//   (ii) min(w) = w1 < W0g : I1 = G0 minus open bad intervals of w1 (exact);  for w2 >= W1(w1) := ceil(2 tau / l'') (l'' = longest piece of I1, > 0) a closed piece of length l'' cannot lie inside one
//   open bad interval of w2 (length 2 tau/w2), so a good t exists;  w2 < W1 is tested exactly.  If I1 has only point pieces: handled by residues of w2 modulo the denominator (flagged "POINT").
// usage: cert N p q mode [r1 r2]   mode=all (all pairs R in (N/2,N]) | one (given r1 r2)   [prints exceptions, summary per R]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long i64; typedef __int128 i128;
typedef struct { i128 n, d; } fr;            /* d > 0 */
static i128 g128(i128 a,i128 b){ if(a<0)a=-a; while(b){ i128 t=a%b; a=b; b=t; } return a; }
static fr mk(i128 n,i128 d){ fr f; f.n=n; f.d=d; return f; }
static int cmp(fr a,fr b){ i128 l=a.n*b.d, r=b.n*a.d; return l<r?-1:(l>r?1:0); }
typedef struct { fr a,b; } pc;                /* closed piece [a,b], a<=b */
typedef struct { fr lo,hi; } bi;              /* open bad interval */
static int cmpbi(const void*x,const void*y){ return cmp(((const bi*)x)->lo,((const bi*)y)->lo); }
static i64 gcd64(i64 a,i64 b){ while(b){ i64 t=a%b; a=b; b=t; } return a<0?-a:a; }
static i64 P,Q;      /* tau = P/Q */
#define MAXP 20000
static i128 fl(i128 n,i128 d){ i128 q=n/d; if((n%d!=0)&&((n<0)!=(d<0))) q--; return q; }
/* G0 for retained speeds */
static int g0(i64 N,i64 r1,i64 r2,pc*out){
  static bi *b=0; static int cap=0; int need=0; for(i64 v=1;v<=N;v++) need+=(int)(v/2)+3; if(need>cap){ cap=need; b=realloc(b,sizeof(bi)*cap); }
  int nb=0;
  for(i64 v=1;v<=N;v++){ if(v==r1||v==r2) continue; for(i64 j=0;j<=v/2+1;j++){ b[nb].lo=mk((i128)j*Q-P,(i128)Q*v); b[nb].hi=mk((i128)j*Q+P,(i128)Q*v); nb++; } }
  qsort(b,nb,sizeof(bi),cmpbi);
  int ng=0; fr reach=mk(-1,1); int have=0; fr half=mk(1,2);
  for(int i=0;i<nb;i++){ if(cmp(b[i].lo,half)>0) break;
    if(!have){ reach=b[i].hi; have=1; continue; }
    if(cmp(b[i].lo,reach)>=0){ out[ng].a=reach; out[ng].b=b[i].lo; ng++; }
    if(cmp(b[i].hi,reach)>0) reach=b[i].hi; }
  if(have && cmp(reach,half)<=0){ out[ng].a=reach; out[ng].b=half; ng++; }
  /* first gap may start below 0 if no interval covers 0 : v=1 is retained so (-tau,tau) covers 0 */
  return ng; }
/* subtract open bad intervals of w from closed pieces */
static int subw(const pc*in,int n,i64 w,pc*out){
  int no=0;
  for(int k=0;k<n;k++){ fr a=in[k].a,b=in[k].b; fr cur=a;
    /* first j with hi_j > cur : (jQ+P)/(Qw) > a  */
    i128 j=fl(a.n*(i128)Q*w - (i128)P*a.d, a.d*(i128)Q); /* j <= a w - P/Q ... start slightly lower */
    if(j<0) j=0; j-=1; if(j<0) j=0;
    int done=0;
    for(;;j++){ fr lo=mk(j*Q-P,(i128)Q*w), hi=mk(j*Q+P,(i128)Q*w);
      if(cmp(hi,cur)<=0) continue;
      if(cmp(lo,b)>0){ break; }
      if(cmp(lo,cur)>=0){ out[no].a=cur; out[no].b=lo; no++; }
      cur=hi; if(cmp(cur,b)>0){ done=1; break; } }
    if(!done && cmp(cur,b)<=0){ out[no].a=cur; out[no].b=b; no++; }
    if(no>MAXP-100){ fprintf(stderr,"MAXP\n"); exit(3); } }
  return no; }
/* is closed piece [a,b] contained in ONE open bad interval of speed w ?  needs integer j with b w - tau < j < a w + tau */
static int covered(fr a,fr b,i64 w){
  /* X = b w - P/Q = (b.n w Q - P b.d)/(b.d Q) ; j0 = floor(X)+1 ; covered iff j0 < a w + P/Q  <=> j0 * a.d * Q < a.n w Q + P a.d */
  i128 X=fl(b.n*(i128)w*Q-(i128)P*b.d, b.d*(i128)Q); i128 j0=X+1;
  return j0*a.d*Q < a.n*(i128)w*Q+(i128)P*a.d; }
static int goodpair_from_pieces(const pc*pcs,int n,i64 w2){ for(int k=0;k<n;k++) if(!covered(pcs[k].a,pcs[k].b,w2)) return 1; return 0; }
static fr flen(fr a,fr b){ i128 n=b.n*a.d-a.n*b.d, d=a.d*b.d; i128 g=g128(n,d); if(g==0) g=1; return mk(n/g,d/g); }
int main(int argc,char**argv){
  if(argc<5){ fprintf(stderr,"usage\n"); return 1; }
  i64 N=atoll(argv[1]); P=atoll(argv[2]); Q=atoll(argv[3]); const char*mode=argv[4]; i64 A=N+1;
  if(Q<=4*P){ fprintf(stderr,"need q>4p\n"); return 2; }
  static pc G[MAXP],I1[MAXP],tmp[MAXP];

  if(!strcmp(mode,"ctl")){ /* ctl: instrument check.  cert N p q ctl WMAX : for all R, all A<=w1<w2<=WMAX : decision by pieces (this program) vs exact ML (candidate times n/(vi+vj)), "ML>=tau" */
    i64 WM=atoll(argv[5]); i64 tot=0,bad=0,nexc=0;
    for(i64 r1=N/2+1;r1<=N;r1++) for(i64 r2=r1+1;r2<=N;r2++){ int ng=g0(N,r1,r2,G);
      for(i64 w1=A;w1<=WM;w1++){ int n1=subw(G,ng,w1,I1);
        for(i64 w2=w1+1;w2<=WM;w2++){ int d1=(n1>0)&&goodpair_from_pieces(I1,n1,w2);
          /* exact ML */
          i64 v[400],cnt=0; for(i64 x=1;x<=N;x++) if(x!=r1&&x!=r2) v[cnt++]=x; v[cnt++]=w1; v[cnt++]=w2;
          i64 bn=0,bd=1; for(int i=0;i<cnt;i++) for(int j=i;j<cnt;j++){ i64 s=v[i]+v[j]; for(i64 n=1;n<=s/2;n++){ i64 mn=s; for(int k=0;k<cnt;k++){ i64 x=(n*v[k])%s; i64 f=(2*x>s)?s-x:x; if(f<mn){ mn=f; if(mn*bd<=bn*s) break; } } if(mn*bd>bn*s){ bn=mn; bd=s; } } }
          int d2=((i128)bn*Q>=(i128)P*bd); tot++; if(!d2) nexc++; if(d1!=d2){ bad++; if(bad<=10) printf("CTL MISMATCH N=%lld R=%lld,%lld w=%lld,%lld pieces=%d exact=%d ML=%lld/%lld\n",N,r1,r2,w1,w2,d1,d2,bn,bd); } } } }
    printf("DONE ctl N=%lld tau=%lld/%lld w<=%lld pairs=%lld exceptions(exact ML<tau)=%lld mismatches=%lld\n",N,P,Q,WM,tot,nexc,bad); return bad?1:0; }
  i64 R1lo=N/2+1,R1hi=N; if(!strcmp(mode,"one")){ R1lo=atoll(argv[5]); R1hi=R1lo; }
  i64 totExc=0,totR=0,flags=0;
  for(i64 r1=R1lo;r1<=R1hi;r1++){ i64 r2lo=r1+1,r2hi=N; if(!strcmp(mode,"one")){ r2lo=atoll(argv[6]); r2hi=r2lo; }
    for(i64 r2=r2lo;r2<=r2hi;r2++){ if(!strcmp(mode,"allg") && gcd64(r1,r2)==1) continue; totR++;
      int ng=g0(N,r1,r2,G); fr lmax=mk(0,1); int pos=0;
      for(int k=0;k<ng;k++){ fr L=flen(G[k].a,G[k].b); if(cmp(L,lmax)>0) lmax=L; }
      if(lmax.n==0){ printf("FLAG N=%lld R=%lld,%lld : G0 has no positive-length interval (pieces=%d)\n",N,r1,r2,ng); flags++; continue; }
      /* W0g > 4P(Q+2P) b /(Q (Q-4P) a)  with lmax=a/b */
      i128 num=(i128)4*P*(Q+2*P)*lmax.d, den=(i128)Q*(Q-4*P)*lmax.n; i64 W0=(i64)(num/den)+1; if(W0<A) W0=A;
      i64 nexc=0,maxW1=0,pairs=0;
      for(i64 w1=A;w1<W0;w1++){ int n1=subw(G,ng,w1,I1);
        if(n1==0){ printf("EXC-ALL N=%lld R=%lld,%lld gcd=%lld w1=%lld : retained+w1 has NO good t at level %lld/%lld => ML<tau for EVERY w2\n",N,r1,r2,gcd64(r1,r2),w1,P,Q); nexc++; continue; }
        fr l2=mk(0,1); for(int k=0;k<n1;k++){ fr L=flen(I1[k].a,I1[k].b); if(cmp(L,l2)>0) l2=L; }
        if(l2.n==0){ printf("POINT N=%lld R=%lld,%lld w1=%lld : only point pieces (%d); needs residue argument\n",N,r1,r2,w1,n1); flags++; continue; }
        /* W1 = ceil(2 tau / l2) = ceil(2P b/(Q a)) */
        i128 nn=(i128)2*P*l2.d, dd=(i128)Q*l2.n; i64 W1=(i64)((nn+dd-1)/dd); if(W1<A) W1=A; if(W1>maxW1) maxW1=W1;
        for(i64 w2=A;w2<W1;w2++){ if(w2==w1) continue; pairs++;
          if(!goodpair_from_pieces(I1,n1,w2)){ nexc++; if(nexc<=40) printf("EXC N=%lld R=%lld,%lld gcd=%lld w=(%lld,%lld) mult: w1/r=%.3f,%.3f,%.3f,%.3f : no t with all ||vt||>=%lld/%lld\n",N,r1,r2,gcd64(r1,r2),w1,w2,(double)w1/r1,(double)w1/r2,(double)w2/r1,(double)w2/r2,P,Q); } } }
      totExc+=nexc;
      if(nexc>0 || !strcmp(mode,"one")) printf("R=%lld,%lld gcd=%lld : G0 pieces=%d lmax=%lld/%lld W0g=%lld maxW1=%lld pairs_enumerated=%lld exceptions=%lld\n",r1,r2,gcd64(r1,r2),ng,(i64)lmax.n,(i64)lmax.d,W0,maxW1,pairs,nexc);
      else if(totR%50==0){ printf("progress R=%lld,%lld lmax=%lld/%lld W0g=%lld maxW1=%lld\n",r1,r2,(i64)lmax.n,(i64)lmax.d,W0,maxW1); fflush(stdout); }
    } }
  printf("DONE cert N=%lld tau=%lld/%lld pairsR=%lld exceptions(enumerated region)=%lld flags=%lld\n",N,P,Q,totR,totExc,flags); return 0; }
