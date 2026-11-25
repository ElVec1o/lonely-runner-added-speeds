// lr2.c: OWN engine for two-entry accelerations of [N].
// V = ([N] \ {r1,r2}) u {w1,w2}, N/2 < r1 < r2 <= N, w_i = m_i r_i, m_i >= 2.   A = N+1.   All arithmetic exact integers (int128).
// Three independent decision procedures for  Cov(tau) := "every t has some v in V with ||vt|| <= tau"  (<=> ML(V) <= tau):
//   exact : ml_exact   -- ML(V) itself by all candidate times n/(vi+vj)  (brute force, small N only)
//   full  : cov_full   -- sweep of ALL closed bands of ALL speeds on [0,1/2]  (no number theory, small/medium N)
//   dir   : cov_dir    -- Dirichlet reduction to windows around c/r_i, c unit mod r_i  (fast, any N)
//   gcd   : fast_gcd   -- closed-form rescue test, valid only for gcd(r1,r2)>1 and m_i < N
// usage: see main().
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long i64; typedef __int128 i128;
static i64 gcd64(i64 a, i64 b){ while(b){ i64 t=a%b; a=b; b=t; } return a<0?-a:a; }
static i64 modinv(i64 a, i64 m){ i64 r0=m,r1=a%m,s0=0,s1=1; while(r1){ i64 q=r0/r1,t=r0-q*r1; r0=r1; r1=t; t=s0-q*s1; s0=s1; s1=t; } s0%=m; if(s0<0) s0+=m; return s0; }
/* ---------- exact ML by candidate times ---------- */
static void ml_exact(int cnt, const i64*v, i64*on, i64*od){
  i64 bn=0, bd=1;
  for(int i=0;i<cnt;i++) for(int j=i;j<cnt;j++){ i64 s=v[i]+v[j];
    for(i64 n=1;n<=s/2;n++){ i64 mn=s; 
      for(int k=0;k<cnt;k++){ i64 x=(n*v[k])%s; i64 f=(2*x>s)?s-x:x; if(f<mn){ mn=f; if(mn*bd<=bn*s) break; } }
      if(mn*bd>bn*s){ bn=mn; bd=s; } } }
  i64 g=gcd64(bn,bd); *on=bn/g; *od=bd/g;
}
/* ---------- full sweep of all bands ---------- */
typedef struct { i128 ln, hn, d; } iv;
static int cmp_iv(const void*a,const void*b){ const iv*x=a,*y=b; i128 l=x->ln*y->d, r=y->ln*x->d; return l<r?-1:(l>r?1:0); }
static int cov_full(int cnt,const i64*v,i128 p,i128 q){
  int cap=0; for(int i=0;i<cnt;i++) cap+=(int)(v[i]/2)+3;
  iv*b=malloc(sizeof(iv)*cap); int nb=0;
  for(int i=0;i<cnt;i++){ i64 x=v[i]; for(i64 j=0;j<=x/2+1;j++){ i128 d=(i128)x*q, ln=(i128)j*q-p, hn=(i128)j*q+p;
      if(hn<0) continue; if(2*ln>d) continue; b[nb].ln=ln; b[nb].hn=hn; b[nb].d=d; nb++; } }
  qsort(b,nb,sizeof(iv),cmp_iv);
  i128 rn=0, rd=1; int ok=0;
  for(int i=0;i<nb;i++){ if(b[i].ln*rd>rn*b[i].d){ ok=0; goto done; } if(b[i].hn*rd>rn*b[i].d){ rn=b[i].hn; rd=b[i].d; } if(2*rn>=rd){ ok=1; goto done; } }
  ok=(2*rn>=rd);
done: free(b); return ok;
}
/* ---------- Dirichlet-window engine ---------- */
/* Level tau=p/q (>= 1/A), needs r*tau<1 for r=r1,r2 and A*(2q - r p) > q*N.  Uncovered t has ||v t||<=1/A for some v<=N, v in {r1,r2}; by t->-t take t=(c+eta)/r, 0<=eta<=1/A.
   Class c with gcd(c,r)>1 is covered by the retained speed r/g (z=0 band).  Unit class: only retained v == u:=-c^{-1} (mod r) (z=+1) and the bands of w1,w2 matter. */
static int cov_dir_ex(i64 N,i64 r1,i64 r2,i64 w1,i64 w2,i128 p,i128 q,int*failr,int*failc){
  i64 A=N+1; i64 rr[2]={r1,r2};
  for(int a=0;a<2;a++){ i64 r=rr[a];
    if(!(q>(i128)r*p)){ fprintf(stderr,"PRECONDITION r*tau<1 violated\n"); exit(2); }
    if(!((i128)A*(2*q-(i128)r*p) > q*N)){ fprintf(stderr,"PRECONDITION z=2 violated\n"); exit(2); }
    for(i64 c=1;c<r;c++){ if(gcd64(c,r)!=1) continue;
      iv b[64]; int nb=0; i64 u=r-modinv(c,r);
      i64 cand[2]={u,u+r};
      for(int k=0;k<2;k++){ i64 x=cand[k]; if(x<1||x>N||x==r1||x==r2) continue;
        b[nb].d=(i128)q*x; b[nb].ln=q-(i128)r*p; b[nb].hn=q+(i128)r*p; nb++; }
      i64 ws[2]={w1,w2};
      for(int k=0;k<2;k++){ i64 w=ws[k]; i64 z=(r-((w%r)*c)%r)%r;
        for(;;z+=r){ i128 ln=(i128)z*q-(i128)r*p; if((i128)A*ln>q*w) break; if(nb>=62) { fprintf(stderr,"too many bands\n"); exit(2); }
          b[nb].d=(i128)q*w; b[nb].ln=ln; b[nb].hn=(i128)z*q+(i128)r*p; nb++; } }
      for(int i=1;i<nb;i++){ iv t=b[i]; int j=i-1; while(j>=0 && cmp_iv(&b[j],&t)>0){ b[j+1]=b[j]; j--; } b[j+1]=t; }
      i128 rn=0, rd=1; int ok=0;   /* reach = rn/rd ; need to reach 1/A */
      for(int i=0;i<nb;i++){ if(b[i].ln*rd>rn*b[i].d) break; if(b[i].hn*rd>rn*b[i].d){ rn=b[i].hn; rd=b[i].d; } if(rn*A>=rd){ ok=1; break; } }
      if(!ok && rn*A>=rd) ok=1;
      if(!ok){ if(failr){ *failr=(int)r; *failc=(int)c; } return 0; } } }
  return 1;
}
static int cov_dir(i64 N,i64 r1,i64 r2,i64 w1,i64 w2,i128 p,i128 q){ return cov_dir_ex(N,r1,r2,w1,w2,p,q,0,0); }
/* ---------- one-entry arithmetic ---------- */
static i64 beta_of(i64 N,i64 r){ i64 s=N+1-r; i64 b=s; while(gcd64(b,r)!=1) b++; return b; }
static int crit(i64 N,i64 r,i64 m){ i64 s=N+1-r; return beta_of(N,r)>=m*s; }   /* Goddyn-Wong (9): beta >= m s */
static void Gfrac(i64 N,i64*gp,i64*gq){ i64 A=N+1; i64 p=2,q=2*N+1; for(i64 r=N/2+1;r<=N;r++){ i64 s=A-r,b=beta_of(N,r),m=b/s+1,d=m*r+b; if(m*q<p*d){ p=m; q=d; } } *gp=p; *gq=q; }
/* fast closed-form test for gcd(r1,r2)>1, m_i<N: returns 1 iff tight(covered at 1/A). */
static int rescued_unit(i64 N,i64 ri,i64 mi,i64 wj,i64 b){ /* window (1/(A mi), s/(A b)) covered by a band of wj ? b unit mod ri, s<=b<=N, b<m s */
  i64 A=N+1,s=A-ri; i64 k0=((wj%ri)*modinv(b,ri))%ri;   /* z = k0 + t ri, w_j == z b (mod ri) */
  for(i64 z=k0;;z+=ri){ if(mi*(z*A-ri)>wj) break;  /* lower end already beyond: lower bound m(zA-r) grows with z */
     if(s*wj<=b*(z*A+ri)) return 1; }
  return 0;
}
static int fast_gcd(i64 N,i64 r1,i64 m1,i64 r2,i64 m2,int wrong){
  i64 A=N+1; i64 R[2]={r1,r2},M[2]={m1,m2};
  for(int a=0;a<2;a++){ i64 ri=R[a],mi=M[a],wj=M[1-a]*R[1-a],s=A-ri; i64 top=mi*s-1+wrong; if(top>N) top=N;
    for(i64 b=s;b<=top;b++){ if(gcd64(b,ri)!=1) continue; if(!rescued_unit(N,ri,mi,wj,b)) return 0; } }
  return 1;
}
static void put(i64 x){ printf("%lld",x); }
int main(int argc,char**argv){
  if(argc<2){ fprintf(stderr,"usage\n"); return 1; }
  const char*mode=argv[1];
  if(!strcmp(mode,"ctl")){ /* ctl NMIN NMAX MMAX FULLMAX : exact ML vs dir (tight, below-G) ; full sweep for N<=FULLMAX */
    i64 nmin=atoll(argv[2]),nmax=atoll(argv[3]),mm=atoll(argv[4]),fm=atoll(argv[5]); i64 tot=0,tight=0,bad=0,badg=0,badf=0,lrcv=0,below=0,nfull=0; const i64 K=1000000000LL;
    for(i64 N=nmin;N<=nmax;N++){ i64 A=N+1,gp,gq; Gfrac(N,&gp,&gq);
      for(i64 r1=N/2+1;r1<=N;r1++) for(i64 r2=r1+1;r2<=N;r2++) for(i64 m1=2;m1<=mm;m1++) for(i64 m2=2;m2<=mm;m2++){
        i64 w1=m1*r1,w2=m2*r2; if(w1==w2) continue; i64 v[256],c=0; for(i64 x=1;x<=N;x++) if(x!=r1&&x!=r2) v[c++]=x; v[c++]=w1; v[c++]=w2;
        i64 en,ed; ml_exact((int)c,v,&en,&ed); tot++;
        int ex_t=(en*A<=ed); if(en*A<ed){ lrcv++; printf("LRC-VIOLATION N=%lld r=%lld,%lld m=%lld,%lld ML=%lld/%lld\n",N,r1,r2,m1,m2,en,ed); }
        int dt=cov_dir(N,r1,r2,w1,w2,1,A); if(dt!=ex_t){ bad++; printf("MISMATCH tight N=%lld r=%lld,%lld m=%lld,%lld ML=%lld/%lld dir=%d\n",N,r1,r2,m1,m2,en,ed,dt); }
        if(ex_t) tight++;
        i128 gpk=(i128)gp*K-1,gqk=(i128)gq*K; int ex_b=((i128)en*gq<(i128)gp*ed); int db=cov_dir(N,r1,r2,w1,w2,gpk,gqk); if(db!=ex_b){ badg++; printf("MISMATCH belowG N=%lld r=%lld,%lld m=%lld,%lld ML=%lld/%lld G=%lld/%lld dir=%d\n",N,r1,r2,m1,m2,en,ed,gp,gq,db); }
        if(ex_b && !ex_t){ below++; printf("EXACT 1/A<ML<G N=%lld r=%lld,%lld m=%lld,%lld ML=%lld/%lld G=%lld/%lld\n",N,r1,r2,m1,m2,en,ed,gp,gq); }
        if(N<=fm){ nfull++; int ft=cov_full((int)c,v,1,A); if(ft!=ex_t){ badf++; printf("MISMATCH full-sweep N=%lld r=%lld,%lld m=%lld,%lld ML=%lld/%lld full=%d\n",N,r1,r2,m1,m2,en,ed,ft); }
          int fb=cov_full((int)c,v,gpk,gqk); if(fb!=ex_b){ badf++; printf("MISMATCH full-sweep belowG N=%lld r=%lld,%lld m=%lld,%lld\n",N,r1,r2,m1,m2); } }
      } }
    printf("DONE ctl N=%lld..%lld m<=%lld sets=%lld exact-tight=%lld exactBelowG-nontight=%lld mismatches(dir tight)=%lld mismatches(dir belowG)=%lld fullsweep-sets=%lld fullsweep-mismatches=%lld LRC-violations=%lld\n",nmin,nmax,mm,tot,tight,below,bad,badg,nfull,badf,lrcv); return 0; }
  if(!strcmp(mode,"run")){ /* run NMIN NMAX MMAX : tight sets and gap hits with dir engine */
    i64 nmin=atoll(argv[2]),nmax=atoll(argv[3]),mm=atoll(argv[4]); const i64 K=1000000000LL; i64 tot=0,tight=0,gwt=0,resc=0,cop=0,gap=0,gapcop=0,critcopl=0;
    for(i64 N=nmin;N<=nmax;N++){ i64 A=N+1,gp,gq; Gfrac(N,&gp,&gq); i128 gpk=(i128)gp*K-1,gqk=(i128)gq*K; i64 nt=0;
      for(i64 r1=N/2+1;r1<=N;r1++) for(i64 r2=r1+1;r2<=N;r2++){ int cp=(gcd64(r1,r2)==1);
        for(i64 m1=2;m1<=mm;m1++) for(i64 m2=2;m2<=mm;m2++){ i64 w1=m1*r1,w2=m2*r2; if(w1==w2) continue; tot++;
          int cr=crit(N,r1,m1)&&crit(N,r2,m2);
          if(cp&&cr) critcopl++;
          if(cov_dir(N,r1,r2,w1,w2,1,A)){ tight++; nt++; if(cr&&!cp) gwt++; else { resc++; printf("TIGHT-NONCRIT N=%lld r=%lld,%lld m=%lld,%lld gcd=%lld crit=%d\n",N,r1,r2,m1,m2,gcd64(r1,r2),cr); }
            if(cp) { cop++; printf("TIGHT-COPRIME N=%lld r=%lld,%lld m=%lld,%lld\n",N,r1,r2,m1,m2); }
            if(cr&&!cp&&N<=400&&nt<=2) printf("tight GW-type N=%lld r=%lld,%lld m=%lld,%lld\n",N,r1,r2,m1,m2); }
          else if(cov_dir(N,r1,r2,w1,w2,gpk,gqk)){ gap++; if(cp) gapcop++; printf("GAP 1/A<ML<G N=%lld r=%lld,%lld m=%lld,%lld gcd=%lld G=%lld/%lld\n",N,r1,r2,m1,m2,gcd64(r1,r2),gp,gq); } }
      }
      if(nt>0) printf("N=%lld tight sets=%lld\n",N,nt); else if(N%25==0){ printf("N=%lld ok\n",N); fflush(stdout); } fflush(stdout); }
    printf("DONE run N=%lld..%lld m<=%lld sets=%lld tight=%lld tight_GWcrit_gcd>1=%lld tight_nonCrit_or_coprime=%lld tight_coprime=%lld GAP(1/A<ML<G)=%lld GAPcoprime=%lld coprimeSetsSatisfyingBothCrit=%lld\n",nmin,nmax,mm,tot,tight,gwt,resc,cop,gap,gapcop,critcopl); return 0; }
  if(!strcmp(mode,"fast")){ /* fast NMIN NMAX MMAX WRONG : closed-form gcd>1 test vs dir engine; WRONG=1 uses the wrong top (m s instead of m s -1) as negative control */
    i64 nmin=atoll(argv[2]),nmax=atoll(argv[3]),mm=atoll(argv[4]); int wrong=atoi(argv[5]); i64 tot=0,bad=0,tight=0;
    for(i64 N=nmin;N<=nmax;N++){ i64 A=N+1; if(mm>=N){ fprintf(stderr,"need m<N\n"); return 2; }
      for(i64 r1=N/2+1;r1<=N;r1++) for(i64 r2=r1+1;r2<=N;r2++){ if(gcd64(r1,r2)==1) continue;
        for(i64 m1=2;m1<=mm;m1++) for(i64 m2=2;m2<=mm;m2++){ i64 w1=m1*r1,w2=m2*r2; if(w1==w2) continue; tot++;
          int a=fast_gcd(N,r1,m1,r2,m2,wrong), d=cov_dir(N,r1,r2,w1,w2,1,A); if(d) tight++; if(a!=d){ bad++; if(bad<=5) printf("MISMATCH fast=%d dir=%d N=%lld r=%lld,%lld m=%lld,%lld\n",a,d,N,r1,r2,m1,m2); } } } }
    printf("DONE fast N=%lld..%lld m<=%lld wrong=%d gcd>1 sets=%lld tight=%lld mismatches=%lld\n",nmin,nmax,mm,wrong,tot,tight,bad); return 0; }
  if(!strcmp(mode,"lvl")){ /* lvl NMIN NMAX MMAX FULLMAX : at tau=ML exactly (must be covered) and tau=ML-eps (must NOT be covered): validates the level engine away from 1/A */
    i64 nmin=atoll(argv[2]),nmax=atoll(argv[3]),mm=atoll(argv[4]),fm=atoll(argv[5]); i64 tot=0,bad=0,skip=0; const i64 K=1000000000LL;
    for(i64 N=nmin;N<=nmax;N++){ i64 A=N+1;
      for(i64 r1=N/2+1;r1<=N;r1++) for(i64 r2=r1+1;r2<=N;r2++) for(i64 m1=2;m1<=mm;m1++) for(i64 m2=2;m2<=mm;m2++){
        i64 w1=m1*r1,w2=m2*r2; if(w1==w2) continue; i64 v[256],c=0; for(i64 x=1;x<=N;x++) if(x!=r1&&x!=r2) v[c++]=x; v[c++]=w1; v[c++]=w2;
        i64 en,ed; ml_exact((int)c,v,&en,&ed); if(!((i128)ed>(i128)r2*en && (i128)A*(2*(i128)ed-(i128)r2*en)>(i128)ed*N)){ skip++; continue; }
        tot++; int a=cov_dir(N,r1,r2,w1,w2,en,ed); i128 pe=(i128)en*K-1, qe=(i128)ed*K; int b=cov_dir(N,r1,r2,w1,w2,pe,qe);
        if(!a||b){ bad++; printf("LVL MISMATCH N=%lld r=%lld,%lld m=%lld,%lld ML=%lld/%lld at-ML=%d below-ML=%d\n",N,r1,r2,m1,m2,en,ed,a,b); }
        if(N<=fm){ int fa=cov_full((int)c,v,en,ed), fb=cov_full((int)c,v,pe,qe); if(!fa||fb){ bad++; printf("LVL FULL MISMATCH N=%lld r=%lld,%lld m=%lld,%lld\n",N,r1,r2,m1,m2); } } } }
    printf("DONE lvl N=%lld..%lld m<=%lld levelchecks=%lld skipped(precondition)=%lld mismatches=%lld\n",nmin,nmax,mm,tot,skip,bad); return 0; }
  if(!strcmp(mode,"cpmin")){ /* cpmin NMIN NMAX MMAX : exact ML over COPRIME pairs; track min ML*N and min ML*(2N+1)/2 */
    i64 nmin=atoll(argv[2]),nmax=atoll(argv[3]),mm=atoll(argv[4]); i64 tot=0;
    for(i64 N=nmin;N<=nmax;N++){ i64 A=N+1; i64 bn=1000000,bd=1,b2n=1000000,b2d=1; i64 ba[6]={0},b2a[6]={0};
      for(i64 r1=N/2+1;r1<=N;r1++) for(i64 r2=r1+1;r2<=N;r2++){ if(gcd64(r1,r2)!=1) continue; for(i64 m1=2;m1<=mm;m1++) for(i64 m2=2;m2<=mm;m2++){
        i64 w1=m1*r1,w2=m2*r2; if(w1==w2) continue; i64 v[256],c=0; for(i64 x=1;x<=N;x++) if(x!=r1&&x!=r2) v[c++]=x; v[c++]=w1; v[c++]=w2;
        i64 en,ed; ml_exact((int)c,v,&en,&ed); tot++;
        /* ratio ML*N = en*N/ed ; compare with best */
        if((i128)en*N*bd<(i128)bn*ed){ bn=en*N; bd=ed; ba[0]=r1;ba[1]=r2;ba[2]=m1;ba[3]=m2;ba[4]=en;ba[5]=ed; }
        if((i128)en*(2*N+1)*b2d<(i128)b2n*2*ed){ b2n=en*(2*N+1); b2d=2*ed; b2a[0]=r1;b2a[1]=r2;b2a[2]=m1;b2a[3]=m2;b2a[4]=en;b2a[5]=ed; } } }
      if(ba[0]) printf("N=%lld min ML*N=%lld/%lld=%.5f at r=%lld,%lld m=%lld,%lld ML=%lld/%lld | min ML*(2N+1)/2=%.5f at r=%lld,%lld m=%lld,%lld ML=%lld/%lld\n",N,bn,bd,(double)bn/bd,ba[0],ba[1],ba[2],ba[3],ba[4],ba[5],(double)b2n/b2d,b2a[0],b2a[1],b2a[2],b2a[3],b2a[4],b2a[5]); }
    printf("DONE cpmin sets=%lld\n",tot); return 0; }
  if(!strcmp(mode,"cpbig")){ /* cpbig NMIN NMAX MMAX : COPRIME pairs, m_i<=MMAX: is ML >= 1/N ?  (not Cov(1/N - 1/(K N)))  */
    i64 nmin=atoll(argv[2]),nmax=atoll(argv[3]),mm=atoll(argv[4]); const i64 K=1000000000LL; i64 tot=0,viol=0,caseII=0;
    for(i64 N=nmin;N<=nmax;N++){ i128 p=K-1,q=(i128)K*N;
      for(i64 r1=N/2+1;r1<=N;r1++) for(i64 r2=r1+1;r2<=N;r2++){ if(gcd64(r1,r2)!=1) continue;
        for(i64 m1=2;m1<=mm;m1++) for(i64 m2=2;m2<=mm;m2++){ i64 w1=m1*r1,w2=m2*r2; if(w1==w2) continue; tot++; if(m1>=r2&&m2>=r1) caseII++;
          if(cov_dir(N,r1,r2,w1,w2,p,q)){ viol++; if(viol<=10) printf("ML<1/N: N=%lld r=%lld,%lld m=%lld,%lld\n",N,r1,r2,m1,m2); } } } }
    printf("DONE cpbig N=%lld..%lld m<=%lld coprime sets=%lld (of which Case II m1>=r2,m2>=r1: %lld) violations of ML>=1/N: %lld\n",nmin,nmax,mm,tot,caseII,viol); return 0; }
  if(!strcmp(mode,"witness")){ /* witness NMIN NMAX MMAX : explicit times of the Case I / Case I' proof, checked directly: min_v ||v t|| >= 1/N */
    i64 nmin=atoll(argv[2]),nmax=atoll(argv[3]),mm=atoll(argv[4]); i64 nI=0,nIp=0,nII=0,bad=0;
    for(i64 N=nmin;N<=nmax;N++) for(i64 r1=N/2+1;r1<=N;r1++) for(i64 r2=r1+1;r2<=N;r2++){ if(gcd64(r1,r2)!=1) continue;
      for(i64 m1=2;m1<=mm;m1++) for(i64 m2=2;m2<=mm;m2++){ i64 w1=m1*r1,w2=m2*r2; if(w1==w2) continue;
        int useI=(m1<=r2-1), useIp=(m2<=r1-1); if(!useI&&!useIp){ nII++; continue; }
        /* Case I: class mod r2, c*r1 == -1 (mod r2), eta=1/(N m2): t=(c N m2 + 1)/(N m2 r2).  Case I': class mod r1, c*(r2-r1)==-1 (mod r1), eta=1/(N m1) */
        i64 r,mu,c; if(useI){ r=r2; mu=m2; c=r2-modinv(r1,r2); nI++; } else { r=r1; mu=m1; c=r1-modinv((r2-r1)%r1,r1); nIp++; }
        i128 D=(i128)N*mu*r, num=(i128)c*N*mu+1; i64 v[300],cn=0; for(i64 x=1;x<=N;x++) if(x!=r1&&x!=r2) v[cn++]=x; v[cn++]=w1; v[cn++]=w2;
        for(int k=0;k<cn;k++){ i128 x=((i128)v[k]*num)%D; i128 f=(2*x>D)?D-x:x; if(f*N<D){ bad++; printf("WITNESS FAIL N=%lld r=%lld,%lld m=%lld,%lld v=%lld case=%s\n",N,r1,r2,m1,m2,v[k],useI?"I":"I'"); break; } } } }
    printf("DONE witness N=%lld..%lld m<=%lld CaseI=%lld CaseI'only=%lld (explicit time checked) CaseII(not witnessed)=%lld failures=%lld\n",nmin,nmax,mm,nI,nIp,nII,bad); return 0; }
  if(!strcmp(mode,"resc")){ /* resc NMIN NMAX M BRUTEMAX : certified-complete search for tight gcd>1 sets with a FAILING entry (criterion (9) fails), m_i<=M<N.
       Necessary condition (Theorem T at the least failing unit beta_i): w_j rescues beta_i.  Enumerate all (r_j,m_j) satisfying it from the interval structure, then full-test with fast_gcd (all failing units) and confirm with cov_dir. */
    i64 nmin=atoll(argv[2]),nmax=atoll(argv[3]),M=atoll(argv[4]),bmax=atoll(argv[5]); i64 gsurv=0,gfull=0,gtight=0,gbrute=0,gmis=0,gent=0;
    for(i64 N=nmin;N<=nmax;N++){ if(M>=N) continue; i64 A=N+1,lo=N/2+1; i64 surv=0,full=0;
      for(i64 ri=lo;ri<=N;ri++){ i64 s=A-ri,b=beta_of(N,ri); for(i64 mi=2;mi<=M;mi++){ if(b>=mi*s) continue; gent++;
          for(i64 z=0;;z++){ i64 L=mi*(z*A-ri), U=(b*(z*A+ri))/s; if(L>U) break; if(L>M*N) break;
            for(i64 mj=2;mj<=M;mj++){ i64 a=L<1?1:L; i64 rlo=(a+mj-1)/mj; if(rlo<lo) rlo=lo; i64 rhi=U/mj; if(rhi>N) rhi=N;
              for(i64 rj=rlo;rj<=rhi;rj++){ if(rj==ri||gcd64(ri,rj)==1) continue; i64 w=mj*rj; if(w==mi*ri) continue;
                if((w%ri)!=((z%ri)*b)%ri) continue;
                if(z>=ri){ i64 zz=z-ri; if(mi*(zz*A-ri)<=w && s*w<=b*(zz*A+ri)) continue; }  /* count each (r_j,m_j) once: only its least valid z */
                surv++; if(fast_gcd(N,ri,mi,rj,mj,0)){ full++; int d=cov_dir(N,ri<rj?ri:rj,ri<rj?rj:ri,ri<rj?mi*ri:mj*rj,ri<rj?mj*rj:mi*ri,1,A);
                  printf("RESCUED-TIGHT N=%lld r=%lld,%lld m=%lld,%lld direngine=%d\n",N,ri,rj,mi,mj,d); gtight++; } } } } } }
      gsurv+=surv; gfull+=full;
      if(N<=bmax){ i64 bs=0; for(i64 ri=lo;ri<=N;ri++){ i64 s=A-ri,b=beta_of(N,ri); for(i64 mi=2;mi<=M;mi++){ if(b>=mi*s) continue;
          for(i64 rj=lo;rj<=N;rj++){ if(rj==ri||gcd64(ri,rj)==1) continue; for(i64 mj=2;mj<=M;mj++){ i64 w=mj*rj; if(w==mi*ri) continue; if(rescued_unit(N,ri,mi,w,b)) bs++; } } } }
        gbrute+=bs; if(bs!=surv){ gmis++; printf("ENUM/BRUTE MISMATCH N=%lld enum=%lld brute=%lld\n",N,surv,bs); } }
      if(N%100==0){ printf("N=%lld survivors(so far)=%lld\n",N,gsurv); fflush(stdout); } }
    printf("DONE resc N=%lld..%lld M=%lld failing entries scanned=%lld necessary-condition survivors=%lld pass full test=%lld (rescued-tight)=%lld | brute survivors (N<=%lld)=%lld enum/brute mismatches=%lld\n",nmin,nmax,M,gent,gsurv,gfull,gtight,bmax,gbrute,gmis); return 0; }
  if(!strcmp(mode,"gwcount")){ /* gwcount NMIN NMAX M : tight sets with gcd>1 and BOTH entries satisfying (9): list N with count */
    i64 nmin=atoll(argv[2]),nmax=atoll(argv[3]),M=atoll(argv[4]); i64 tot=0,nN=0;
    for(i64 N=nmin;N<=nmax;N++){ i64 A=N+1,lo=N/2+1; i64 cnt=0,ex1=0,ex2=0;
      i64 k[4100]; for(i64 r=lo;r<=N;r++){ i64 s=A-r,b=beta_of(N,r); i64 q=b/s; if(q>M) q=M; k[r]=q>=2?q-1:0; }
      for(i64 r1=lo;r1<=N;r1++){ if(!k[r1]) continue; for(i64 r2=r1+1;r2<=N;r2++){ if(!k[r2]||gcd64(r1,r2)==1) continue; i64 g=gcd64(r1,r2),pc=k[r1]*k[r2]; i64 t1=k[r1]+1,t2=k[r2]+1; /* m ranges 2..t_i */
        for(i64 ka=1;;ka++){ i64 a1=(r2/g)*ka,a2=(r1/g)*ka; if(a1>t1||a2>t2) break; if(a1>=2&&a2>=2) pc--; }
        if(pc>0){ cnt+=pc; if(!ex1){ ex1=r1; ex2=r2; } } } }
      if(cnt){ nN++; tot+=cnt; printf("N=%lld GW-type tight (gcd>1) sets with m<=%lld: %lld  (w1==w2 collisions removed); first pair r=%lld,%lld\n",N,M,cnt,ex1,ex2); } }
    printf("DONE gwcount N=%lld..%lld M=%lld values of N with a GW-type two-entry tight set: %lld total sets %lld\n",nmin,nmax,M,nN,tot); return 0; }
  if(!strcmp(mode,"ineqII")){ /* ineqII NMIN NMAX : check the Case II counting inequality (2N-r2)(N-4) r1 > 3N(N+2) for every coprime pair */
    i64 nmin=atoll(argv[2]),nmax=atoll(argv[3]); i64 tot=0,fail=0,lastfailN=0;
    for(i64 N=nmin;N<=nmax;N++){ i64 nf=0; for(i64 r1=N/2+1;r1<=N;r1++) for(i64 r2=r1+1;r2<=N;r2++){ if(gcd64(r1,r2)!=1) continue; tot++;
        if(!((i128)(2*N-r2)*(N-4)*r1 > (i128)3*N*(N+2))){ fail++; nf++; if(N>=10) printf("INEQ FAIL N=%lld r=%lld,%lld\n",N,r1,r2); } }
      if(nf) { lastfailN=N; if(N<=12) printf("N=%lld: %lld coprime pairs fail the inequality\n",N,nf); } }
    printf("DONE ineqII N=%lld..%lld coprime pairs=%lld failing=%lld largest N with a failure=%lld\n",nmin,nmax,tot,fail,lastfailN); return 0; }
  if(!strcmp(mode,"one")){ /* one N r1 r2 m1 m2 : dir engine, full band sweep (no number theory), fast_gcd, and witness t=1/A (needs A not dividing w_i) */
    i64 N=atoll(argv[2]),r1=atoll(argv[3]),r2=atoll(argv[4]),m1=atoll(argv[5]),m2=atoll(argv[6]); i64 A=N+1,w1=m1*r1,w2=m2*r2; i64*v=malloc(sizeof(i64)*(N+4)),c=0;
    for(i64 x=1;x<=N;x++) if(x!=r1&&x!=r2) v[c++]=x; v[c++]=w1; v[c++]=w2;
    int d=cov_dir(N,r1,r2,w1,w2,1,A), f=cov_full((int)c,v,1,A), g=fast_gcd(N,r1,m1,r2,m2,0); int wit=(w1%A!=0&&w2%A!=0);
    printf("N=%lld r=%lld,%lld m=%lld,%lld w=%lld,%lld : covered(dir)=%d covered(full sweep)=%d fast_gcd=%d witness t=1/A valid=%d  gcd(r1,r2)=%lld  => %s\n",N,r1,r2,m1,m2,w1,w2,d,f,g,wit,gcd64(r1,r2),(d&&f&&wit)?"ML = 1/(N+1) exactly":"see flags"); return 0; }
  if(!strcmp(mode,"planted")){ i64 N=73,r1=70,r2=72; int fails=0;
    struct { i64 m1,m2; int want; } T[]={{2,2,1},{2,3,0},{3,2,0},{3,3,0},{2,4,0}};
    for(int k=0;k<5;k++){ i64 w1=T[k].m1*r1,w2=T[k].m2*r2; i64 v[256],c=0; for(i64 x=1;x<=N;x++) if(x!=r1&&x!=r2) v[c++]=x; v[c++]=w1; v[c++]=w2; i64 en,ed; ml_exact((int)c,v,&en,&ed);
      int d=cov_dir(N,r1,r2,w1,w2,1,N+1), f=cov_full((int)c,v,1,N+1), g=fast_gcd(N,r1,T[k].m1,r2,T[k].m2,0), ex=(en*(N+1)==ed);
      printf("N=73 R={70,72} m=(%lld,%lld): exact ML=%lld/%lld tight_exact=%d dir=%d full=%d fast=%d expected=%d crit1=%d crit2=%d\n",T[k].m1,T[k].m2,en,ed,ex,d,f,g,T[k].want,crit(N,r1,T[k].m1),crit(N,r2,T[k].m2));
      if(ex!=T[k].want||d!=ex||f!=ex||g!=ex) fails++; }
    printf("planted failures=%d\n",fails); return fails; }
  fprintf(stderr,"unknown mode\n"); return 1;
}
