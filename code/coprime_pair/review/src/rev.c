// rev.c : independent exact-integer engine, fresh-session review of the accompanying code (REVIEW2).
// Written from scratch from the mathematical definitions only (not lr2.c, not src2/).
// Core object: pieces = finite union of CLOSED rational intervals; subtract OPEN bad intervals
// ((jq-p)/(qw), (jq+p)/(qw)) of a speed w at level p/q.  A point t survives iff ||v t|| >= p/q for all v.
// Units: all quantities are exact rationals an/ad with an, ad < 2^31 (checked), int64 arithmetic, i128 for compares.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef long long ll;
typedef __int128 i128;

static ll fdiv(ll a, ll b) { ll q = a / b; if ((a % b) < 0) q--; return q; }
static ll cdiv(ll a, ll b) { return -fdiv(-a, b); }
static ll gcdll(ll a, ll b) { if (a < 0) a = -a; if (b < 0) b = -b; while (b) { ll t = a % b; a = b; b = t; } return a; }
static ll modinv(ll a, ll m) { // a unit mod m, m>=2
  ll g = m, x = 0, y = 1, aa = a % m; ll r0 = m, r1 = aa, s0 = 0, s1 = 1;
  while (r1) { ll qq = r0 / r1; ll t = r0 - qq * r1; r0 = r1; r1 = t; t = s0 - qq * s1; s0 = s1; s1 = t; }
  (void)g; (void)x; (void)y;
  if (r0 != 1) { fprintf(stderr, "modinv: not a unit %lld %lld\n", a, m); exit(3); }
  s0 %= m; if (s0 < 0) s0 += m; return s0;
}

typedef struct { ll an, ad, bn, bd; } Pc;
#define CAP (1 << 18)
static Pc G0[CAP], P1[CAP], T1[CAP], T2[CAP], T3[CAP];

static inline int cmpq(ll an, ll ad, ll bn, ll bd) { i128 x = (i128)an * bd, y = (i128)bn * ad; return x < y ? -1 : (x > y ? 1 : 0); }
static inline void chk(ll v) { if (v >= (1LL << 31) || v <= -(1LL << 31)) { fprintf(stderr, "RANGE OVERFLOW %lld\n", v); exit(4); } }

static int sub(const Pc *in, int n, ll w, ll p, ll q, Pc *out) {
  int m = 0;
  for (int i = 0; i < n; i++) {
    ll an = in[i].an, ad = in[i].ad, bn = in[i].bn, bd = in[i].bd;
    ll cn = an, cd = ad;
    ll X = an * q * w - p * ad, Y = ad * q;
    ll jmin = fdiv(X, Y) + 1;
    ll X2 = bn * q * w + p * bd, Y2 = bd * q;
    ll jmax = fdiv(X2 - 1, Y2);
    ll D = q * w; chk(D);
    for (ll j = jmin; j <= jmax; j++) {
      ll Ln = j * q - p, Rn = j * q + p;
      if (cmpq(cn, cd, Ln, D) <= 0) {
        if (m >= CAP) { fprintf(stderr, "PIECE OVERFLOW\n"); exit(5); }
        chk(Ln); out[m].an = cn; out[m].ad = cd; out[m].bn = Ln; out[m].bd = D; m++;
      }
      if (cmpq(Rn, D, cn, cd) > 0) { chk(Rn); cn = Rn; cd = D; }
    }
    if (cmpq(cn, cd, bn, bd) <= 0) {
      if (m >= CAP) { fprintf(stderr, "PIECE OVERFLOW\n"); exit(5); }
      out[m].an = cn; out[m].ad = cd; out[m].bn = bn; out[m].bd = bd; m++;
    }
  }
  return m;
}
static int has_pos(const Pc *P, int n) { for (int i = 0; i < n; i++) if (cmpq(P[i].an, P[i].ad, P[i].bn, P[i].bd) < 0) return 1; return 0; }
// longest positive-length piece: returns index or -1, length as num/den (ll)
static int longest(const Pc *P, int n, ll *num, ll *den) {
  int bi = -1; ll bn = 0, bd = 1;
  for (int i = 0; i < n; i++) {
    ll ln = P[i].bn * P[i].ad - P[i].an * P[i].bd, ld = P[i].bd * P[i].ad;
    if (ln <= 0) continue;
    if (bi < 0 || (i128)ln * bd > (i128)bn * ld) { bi = i; bn = ln; bd = ld; }
  }
  *num = bn; *den = bd; return bi;
}
// good set G0 in [0,1/2] for speeds in list vs[0..nv) at level p/q ; result in G0buf, return count
static int good_of(const ll *vs, int nv, ll p, ll q, Pc *res) {
  Pc *a = T1, *b = T2; int n = 1; a[0].an = 0; a[0].ad = 1; a[0].bn = 1; a[0].bd = 2;
  for (int i = 0; i < nv && n > 0; i++) { n = sub(a, n, vs[i], p, q, b); Pc *t = a; a = b; b = t; }
  memcpy(res, a, sizeof(Pc) * n); return n;
}
static int retained(int N, ll r1, ll r2, ll *vs) { int k = 0; for (ll v = 1; v <= N; v++) if (v != r1 && v != r2) vs[k++] = v; return k; }

// exact ML by candidate times n/(vi+vj)
static void ml_exact(const ll *V, int n, ll *mn, ll *md) {
  ll bn = 0, bd = 1;
  for (int i = 0; i < n; i++) for (int j = i; j < n; j++) {
    ll D = V[i] + V[j];
    for (ll k = 1; 2 * k <= D; k++) {
      ll mind = D; int ok = 1;
      for (int u = 0; u < n; u++) {
        ll x = ((V[u] % D) * k) % D; ll d = x < D - x ? x : D - x;
        if (d < mind) { mind = d; if ((i128)mind * bd <= (i128)bn * D) { ok = 0; break; } }
      }
      if (ok && (i128)mind * bd > (i128)bn * D) { bn = mind; bd = D; }
    }
  }
  ll g = gcdll(bn, bd); *mn = bn / g; *md = bd / g;
}

static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

// ---------------------------------------------------------------- mode A
static int modeA(int lo, int hi, int M) {
  ll viol = 0, tested = 0, noG0 = 0;
  for (int N = lo; N <= hi; N++) {
    ll vs[3100]; ll nsets = 0, nviol = 0; ll p = 1, q = N;
    for (int r1 = N / 2 + 1; r1 <= N; r1++) for (int r2 = r1 + 1; r2 <= N; r2++) {
      if (gcdll(r1, r2) != 1) continue;
      int nv = retained(N, r1, r2, vs);
      int n0 = good_of(vs, nv, p, q, G0);
      if (n0 == 0) { noG0++; nviol++; continue; }
      for (int m1 = 2; m1 <= M; m1++) {
        ll w1 = (ll)m1 * r1;
        int n1 = sub(G0, n0, w1, p, q, P1);
        for (int m2 = 2; m2 <= M; m2++) {
          ll w2 = (ll)m2 * r2; if (w2 == w1) continue;
          nsets++;
          int n2 = n1 ? sub(P1, n1, w2, p, q, T3) : 0;
          if (n2 == 0) { nviol++; printf("VIOL N=%d R=(%d,%d) m=(%d,%d)\n", N, r1, r2, m1, m2); }
        }
      }
    }
    tested += nsets; viol += nviol;
    if (N % 10 == 0 || N == hi) { printf("A N=%d sets=%lld viol=%lld cum_sets=%lld cum_viol=%lld\n", N, nsets, nviol, tested, viol); fflush(stdout); }
  }
  printf("A DONE N=%d..%d M<=%d sets=%lld violations(ML<1/N)=%lld emptyG0pairs=%lld\n", lo, hi, M, tested, viol, noG0);
  return 0;
}

// ---------------------------------------------------------------- mode B1: one R, all w1<w2<=cap, level p/q
static ll b_exc = 0, b_all = 0, b_cap = 0, b_point = 0, b_maxT = 0, b_maxW0 = 0, b_cnt = 0;
static void runR(int N, int r1, int r2, ll cap, ll p, ll q, int prune, int verbose) {
  ll vs[3100]; int nv = retained(N, r1, r2, vs);
  int n0 = good_of(vs, nv, p, q, G0);
  ll lnum, lden; int li = longest(G0, n0, &lnum, &lden);
  if (li >= 0 && q > 4 * p) {
    i128 W0 = (i128)4 * p * (q + 2 * p) * lden / ((i128)q * (q - 4 * p) * lnum) + 1;
    if (W0 > b_maxW0) b_maxW0 = (ll)W0;
  }
  ll A = N + 1;
  if (n0 == 0) { printf("EMPTYG0 N=%d R=(%d,%d)\n", N, r1, r2); b_all++; return; }
  if (li < 0) { b_point++; printf("G0POINTONLY N=%d R=(%d,%d)\n", N, r1, r2); }
  for (ll w1 = A; w1 <= cap; w1++) {
    int n1 = sub(G0, n0, w1, p, q, P1);
    if (n1 == 0) { b_all++; printf("ALLW2 N=%d R=(%d,%d) w1=%lld\n", N, r1, r2, w1); continue; }
    ll hi2 = cap;
    if (prune) {
      ll ln, ld; int bi = longest(P1, n1, &ln, &ld);
      if (bi < 0) { b_point++; }
      else {
        i128 T = ((i128)2 * p * ld + (i128)q * ln - 1) / ((i128)q * ln);  // ceil(2 p ld / (q ln))
        if (T - 1 > b_maxT) b_maxT = (ll)(T - 1);
        if (T - 1 < hi2) hi2 = (ll)(T - 1); else if (T - 1 > cap) b_cap++;
      }
    }
    for (ll w2 = w1 + 1; w2 <= hi2; w2++) {
      b_cnt++;
      int n2 = sub(P1, n1, w2, p, q, T3);
      if (n2 == 0) {
        b_exc++;
        ll V[3100]; int k = 0; for (int i = 0; i < nv; i++) V[k++] = vs[i]; V[k++] = w1; V[k++] = w2;
        ll mn = 0, md = 1; if (verbose) ml_exact(V, k, &mn, &md);
        printf("EXC N=%d R=(%d,%d) g=%lld w=(%lld,%lld) ML=%lld/%lld level=%lld/%lld\n", N, r1, r2, gcdll(r1, r2), w1, w2, mn, md, p, q);
        fflush(stdout);
      }
    }
  }
}
static int modeB(int lo, int hi, int capmul, int prune) {
  for (int N = lo; N <= hi; N++) {
    b_exc = b_all = b_cap = b_point = b_maxT = b_maxW0 = b_cnt = 0;
    ll cap = (ll)capmul * N * N;
    for (int r1 = N / 2 + 1; r1 <= N; r1++) for (int r2 = r1 + 1; r2 <= N; r2++) runR(N, r1, r2, cap, 2, 2 * N + 1, prune, 1);
    printf("B N=%d cap=%lld pairsTested=%lld exceptions=%lld ALLW2=%lld pointflags=%lld capflags=%lld maxT-1=%lld maxW0g=%lld\n", N, cap, b_cnt, b_exc, b_all, b_point, b_cap, b_maxT, b_maxW0);
    fflush(stdout);
  }
  return 0;
}

static int modeBN(int lo, int hi, int capmul) { // level 1/N, all R, report coprime exceptions separately
  for (int N = lo; N <= hi; N++) {
    ll cap = (ll)capmul * N * N; ll cexc = 0, gexc = 0, cpoint = 0, mw0 = 0, mT = 0;
    for (int r1 = N / 2 + 1; r1 <= N; r1++) for (int r2 = r1 + 1; r2 <= N; r2++) {
      b_exc = b_all = b_cap = b_point = b_maxT = b_maxW0 = b_cnt = 0;
      runR(N, r1, r2, cap, 1, N, 1, 0);
      if (b_maxW0 > mw0) mw0 = b_maxW0; if (b_maxT > mT) mT = b_maxT;
      if (gcdll(r1, r2) == 1) { cexc += b_exc + b_all; cpoint += b_point + b_cap; } else { gexc += b_exc + b_all; }
      if (b_point || b_cap) printf("  flags N=%d R=(%d,%d) g=%lld point=%lld cap=%lld\n", N, r1, r2, gcdll(r1, r2), b_point, b_cap);
    }
    printf("BN N=%d level=1/N cap=%lld coprimeExceptions=%lld coprimeFlags=%lld nonCoprimeExceptions=%lld maxW0g=%lld maxT-1=%lld\n", N, cap, cexc, cpoint, gexc, mw0, mT); fflush(stdout);
  }
  return 0;
}
// ---------------------------------------------------------------- Theorem T machinery
static int beta_of(int r, int s) { int b = s; while (gcdll(b, r) != 1) b++; return b; }
static int rescued(int N, int r, int s, int m, ll w, int b, int *zout, int variant) {
  ll A = N + 1; ll inv = modinv(b % r, r); ll z0 = ((w % r) * inv) % r;
  // z = z0 + k r, z >= 0, m(zA - r) <= w  <=> z <= floor((w + m r)/(m A))
  ll zmax = (w + (ll)m * r) / ((ll)m * A);
  if (zmax < z0) return 0;
  ll z = z0 + ((zmax - z0) / r) * r;
  if (variant == 1) { z = z0 + ((zmax - z0) / r) * r; if (z >= r) z -= r; if (z < 0) return 0; } // wrong: ignores larger z
  *zout = (int)z;
  if (variant == 2) return (ll)s * w < (ll)b * (z * A + r);   // wrong: strict
  return (ll)s * w <= (ll)b * (z * A + r);
}
static int verbose_T = 0, allowbig = 0;
static long long T_zpos_div = 0, T_z0 = 0, T_zpos_nodiv = 0;
static long long T_inst = 0, T_win = 0, T_winmis = 0, T_tightmis = 0, T_tightpred = 0, T_tightex = 0, T_bad_g = 0, T_bad_R2 = 0, T_resc = 0;
static long long T_negmis1 = 0, T_negmis2 = 0, T_Sviol = 0, T_Scheck = 0;
static void testinst(int N, int r1, int r2, int m1, int m2, const Pc *G0cache, int n0cache) {
  ll w1 = (ll)m1 * r1, w2 = (ll)m2 * r2; if (w1 == w2) return;
  int A = N + 1; int rr[2] = {r1, r2}; int mm[2] = {m1, m2}; ll ww[2] = {w1, w2};
  ll vs[3100]; int nv = retained(N, r1, r2, vs);
  // exact tightness at level 1/A (p=1,q=A): tight iff no positive-length surviving piece
  int a1 = sub(G0cache, n0cache, w1, 1, A, T3);
  int a2 = a1 ? sub(T3, a1, w2, 1, A, T1) : 0;
  int tight_ex = !(a2 && has_pos(T1, a2));
  if (!a1) tight_ex = 1;
  int allres = 1, allres1 = 1, allres2 = 1;
  ll g = gcdll(r1, r2);
  ll allv[3100]; int na = 0; for (int i = 0; i < nv; i++) allv[na++] = vs[i]; allv[na++] = w1; allv[na++] = w2;
  for (int i = 0; i < 2; i++) {
    int r = rr[i], s = A - r, m = mm[i]; ll wj = ww[1 - i];
    int top = m * s - 1; if (top > N) top = N;
    int nfail = 0; int zstar = -1; int zmulti = 0;
    for (int b = s; b <= top; b++) {
      if (gcdll(b, r) != 1) continue;
      nfail++;
      int z = 0; int pr = rescued(N, r, s, m, wj, b, &z, 0);
      int pr1 = rescued(N, r, s, m, wj, b, &z, 1), pr2 = rescued(N, r, s, m, wj, b, &z, 2);
      if (!pr) allres = 0;
      if (!pr1) allres1 = 0; if (!pr2) allres2 = 0;
      // exact window coverage
      ll inv = modinv(b % r, r); ll c = (r - inv) % r;
      ll lon = c * A * m + 1, lod = (ll)A * m * r, hin = c * A * b + s, hid = (ll)A * b * r;
      Pc st; st.an = lon; st.ad = lod; st.bn = hin; st.bd = hid;
      int n = 1; Pc *a = T1, *bb = T2; a[0] = st;
      // reflect not needed: sub works on any real interval
      for (int k = 0; k < na && n > 0; k++) { n = sub(a, n, allv[k], 1, A, bb); Pc *t = a; a = bb; bb = t; }
      int covered = !(n && has_pos(a, n));
      T_win++;
      if (verbose_T) printf("  i=%d r=%d s=%d m=%d failing b=%d pred_rescued=%d exact_covered=%d z=%d\n", i, r, s, m, b, pr, covered, z);
      if (covered != pr) { T_winmis++; if (T_winmis < 20) printf("WINMIS N=%d R=(%d,%d) m=(%d,%d) i=%d b=%d pred=%d exact=%d\n", N, r1, r2, m1, m2, i, b, pr, covered); }
      if (covered != pr1) T_negmis1++;
      if (covered != pr2) T_negmis2++;
      if (pr) {
        T_resc++;
        if (z % g != 0) T_bad_g++;
        if (wj % r != 0) { if (zstar < 0) zstar = z; else if (zstar != z) { zmulti = 1; } T_Scheck++; }
        if (wj % r == 0) { if (z > 0) { T_zpos_div++; if (T_zpos_div <= 5) printf("ZPOSDIV N=%d R=(%d,%d) m=(%d,%d) i=%d b=%d z=%d\n", N, r1, r2, m1, m2, i, b, z); } else T_z0++; } else if (z > 0) T_zpos_nodiv++;
        if (z >= 2 && !(m * s < 3 * b)) T_bad_R2++;
      }
    }
    if (zmulti) { T_Sviol++; if (T_Sviol < 10) printf("SVIOL N=%d R=(%d,%d) m=(%d,%d) i=%d\n", N, r1, r2, m1, m2, i); }
  }
  T_inst++;
  if (allres != tight_ex) { T_tightmis++; printf("TIGHTMIS N=%d R=(%d,%d) m=(%d,%d) pred=%d exact=%d\n", N, r1, r2, m1, m2, allres, tight_ex); }
  T_tightpred += allres; T_tightex += tight_ex;
}
static int modeC_sweep(int lo, int hi, int M) {
  for (int N = lo; N <= hi; N++) {
    ll vs[3100]; ll A = N + 1;
    for (int r1 = N / 2 + 1; r1 <= N; r1++) for (int r2 = r1 + 1; r2 <= N; r2++) {
      if (gcdll(r1, r2) == 1) continue;
      int nv = retained(N, r1, r2, vs); int n0 = good_of(vs, nv, 1, A, G0);
      for (int m1 = 2; m1 <= M && (allowbig || m1 <= N - 1); m1++) for (int m2 = 2; m2 <= M && (allowbig || m2 <= N - 1); m2++) testinst(N, r1, r2, m1, m2, G0, n0);
    }
    if (N % 5 == 0 || N == hi) { printf("Lemma S check: windows with r!|w rescued=%lld, entries with two different z=%lld\n", T_Scheck, T_Sviol); printf("zstat: rescued windows with r|w: z>0 %lld, z=0 %lld; r!|w and z>0 %lld\n", T_zpos_div, T_z0, T_zpos_nodiv); printf("C N=%d inst=%lld windows=%lld winmis=%lld tightmis=%lld tightpred=%lld tightex=%lld rescued=%lld badg=%lld badR2=%lld negctl(win mis var1=%lld var2=%lld)\n", N, T_inst, T_win, T_winmis, T_tightmis, T_tightpred, T_tightex, T_resc, T_bad_g, T_bad_R2, T_negmis1, T_negmis2); fflush(stdout); }
  }
  return 0;
}
static int modeC_rand(unsigned long long seed, long iters, int Nmax) {
  rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
  for (long it = 0; it < iters; it++) {
    int N = 14 + (int)(rnd() % (Nmax - 13)); int lo = N / 2 + 1; int cnt = N - lo + 1;
    int r1, r2, tries = 0;
    do { r1 = lo + (int)(rnd() % cnt); r2 = lo + (int)(rnd() % cnt); tries++; } while ((r1 >= r2 || gcdll(r1, r2) == 1) && tries < 1000);
    if (r1 >= r2 || gcdll(r1, r2) == 1) continue;
    // structured bias: with prob 1/2 take r near N
    int mm[2];
    for (int k = 0; k < 2; k++) { unsigned long long x = rnd() % 4; mm[k] = x < 2 ? 2 + (int)(rnd() % 5) : (x == 2 ? 2 + (int)(rnd() % 30) : 2 + (int)(rnd() % (N - 2))); if (mm[k] > N - 1) mm[k] = N - 1; }
    ll vs[3100]; int nv = retained(N, r1, r2, vs); int n0 = good_of(vs, nv, 1, N + 1, G0);
    testinst(N, r1, r2, mm[0], mm[1], G0, n0);
    if ((it + 1) % 200000 == 0) { printf("C rand it=%ld inst=%lld windows=%lld winmis=%lld tightmis=%lld tightpred=%lld tightex=%lld rescued=%lld badg=%lld badR2=%lld negctl(%lld,%lld)\n", it + 1, T_inst, T_win, T_winmis, T_tightmis, T_tightpred, T_tightex, T_resc, T_bad_g, T_bad_R2, T_negmis1, T_negmis2); fflush(stdout); }
  }
  printf("C rand DONE inst=%lld windows=%lld winmis=%lld tightmis=%lld tightpred=%lld tightex=%lld rescued=%lld badg=%lld badR2=%lld negctl(var1=%lld,var2=%lld)\n", T_inst, T_win, T_winmis, T_tightmis, T_tightpred, T_tightex, T_resc, T_bad_g, T_bad_R2, T_negmis1, T_negmis2);
  return 0;
}

// ---------------------------------------------------------------- mode D: (9)-list by brute force
static int modeD(int Nmax) {
  long long totpairs = 0, totsets = 0, coprime_pairs = 0; int lastN = 0;
  static int active[4000], mu[4000];
  for (int N = 14; N <= Nmax; N++) {
    int A = N + 1; int na = 0; int Rs[4000];
    for (int r = N / 2 + 1; r <= N; r++) {
      int s = A - r; int b = beta_of(r, s);
      if (b >= 2 * s) { Rs[na] = r; mu[na] = b / s; na++; }
    }
    for (int i = 0; i < na; i++) for (int j = i + 1; j < na; j++) {
      int r1 = Rs[i], r2 = Rs[j];
      if (gcdll(r1, r2) == 1) { coprime_pairs++; printf("COPRIME ACTIVE PAIR N=%d (%d,%d)\n", N, r1, r2); continue; }
      ll sets = 0;
      for (int m1 = 2; m1 <= mu[i]; m1++) for (int m2 = 2; m2 <= mu[j]; m2++) if ((ll)m1 * r1 != (ll)m2 * r2) sets++;
      totpairs++; totsets += sets;
      // exact tightness verification of every set at level 1/A
      ll vs[3100]; int alltight = -1; int n0 = 0;
      if (N <= 2200) { int nv = retained(N, r1, r2, vs); n0 = good_of(vs, nv, 1, A, G0); alltight = 1; }
      if (N <= 2200) for (int m1 = 2; m1 <= mu[i]; m1++) for (int m2 = 2; m2 <= mu[j]; m2++) {
        ll w1 = (ll)m1 * r1, w2 = (ll)m2 * r2; if (w1 == w2) continue;
        int a1 = sub(G0, n0, w1, 1, A, T3); int a2 = a1 ? sub(T3, a1, w2, 1, A, T1) : 0;
        int tight = !(a2 && has_pos(T1, a2)); if (!tight) alltight = 0;
        if (!a2) { printf("  !! LRC violated? N=%d (%d,%d) m=(%d,%d): no surviving piece at all\n", N, r1, r2, m1, m2); }
      }
      printf("GW N=%d r=(%d,%d) s=(%d,%d) g=%lld mu=(%d,%d) sets=%lld allTightExact=%d\n", N, r1, r2, A - r1, A - r2, gcdll(r1, r2), mu[i], mu[j], sets, alltight);
      lastN = N;
    }
  }
  printf("D DONE N=14..%d pairs(gcd>1)=%lld sets=%lld coprimeActivePairs=%lld\n", Nmax, totpairs, totsets, coprime_pairs);
  (void)active; (void)lastN; return 0;
}

// ---------------------------------------------------------------- mode L: Lemma Z
static int modeL(int Nmax) {
  long long cnt = 0, bad = 0, bad2 = 0, larger_ok = 0;
  for (int N = 4; N <= Nmax; N++) {
    int A = N + 1;
    for (int r1 = N / 2 + 1; r1 <= N; r1++) for (int r2 = r1 + 1; r2 <= N; r2++) {
      ll g = gcdll(r1, r2); ll gam = r2 / g; int s1 = A - r1; cnt++;
      int b1 = beta_of(r1, s1);
      if (!(b1 < gam * s1)) bad++;
      if (!((gam - 1) * s1 > r1)) bad2++;
    }
  }
  printf("L DONE N=4..%d pairs=%lld violations(beta1<gamma*s1)=%lld violations((gamma-1)s1>r1)=%lld\n", Nmax, cnt, bad, bad2);
  (void)larger_ok; return 0;
}

// ---------------------------------------------------------------- mode W: witness times of Theorem C cases I, I', and Lemma 1(a) at several eta
static int modeW(int lo, int hi, int M) {
  long long tested = 0, fail = 0, l1 = 0, l1f = 0, caseII = 0;
  for (int N = lo; N <= hi; N++) for (int r1 = N / 2 + 1; r1 <= N; r1++) for (int r2 = r1 + 1; r2 <= N; r2++) {
    if (gcdll(r1, r2) != 1) continue;
    // Lemma 1(a) at eta = E*j/10, modulus r=r2, rho=r1, c r1 = -1 mod r2
    {
      ll c = (r2 - modinv(r1 % r2, r2)) % r2; ll Nn = N;
      for (int j = 1; j <= 10; j++) {
        // t = (c + eta)/r2, eta = (2N - r2) j /(10 N^2)  ; t = (c*10N^2 + (2N-r2) j) / (10 N^2 r2)
        ll tn = c * 10 * Nn * Nn + (2 * Nn - r2) * j, td = 10 * Nn * Nn * r2;
        for (int v = 1; v <= N; v++) {
          if (v == r1 || v == r2) continue;
          ll x = ((ll)v * tn) % td; ll d = x < td - x ? x : td - x; l1++;
          if (d * N < td) { l1f++; printf("L1FAIL N=%d R=(%d,%d) j=%d v=%d\n", N, r1, r2, j, v); }
        }
      }
    }
    for (int m1 = 2; m1 <= M; m1++) for (int m2 = 2; m2 <= M; m2++) {
      ll w1 = (ll)m1 * r1, w2 = (ll)m2 * r2; if (w1 == w2) continue;
      ll tn, td; int ru; ll Nn = N;
      if (m1 <= r2 - 1) { ll c = (r2 - modinv(r1 % r2, r2)) % r2; tn = c * Nn * m2 + 1; td = Nn * m2 * r2; ru = 1; }
      else if (m2 <= r1 - 1) { ll u = r2 - r1; ll c = (r1 - modinv(u % r1, r1)) % r1; tn = c * Nn * m1 + 1; td = Nn * m1 * r1; ru = 2; }
      else { caseII++; continue; }
      (void)ru; tested++;
      int ok = 1;
      for (int v = 1; v <= N && ok; v++) { if (v == r1 || v == r2) continue; ll x = ((ll)v * tn) % td; ll d = x < td - x ? x : td - x; if (d * N < td) ok = 0; }
      { ll x = (w1 % td) * (tn % td) % td; ll d = x < td - x ? x : td - x; if (d * N < td) ok = 0; }
      { ll x = (w2 % td) * (tn % td) % td; ll d = x < td - x ? x : td - x; if (d * N < td) ok = 0; }
      if (!ok) { fail++; printf("WITFAIL N=%d R=(%d,%d) m=(%d,%d)\n", N, r1, r2, m1, m2); }
    }
  }
  printf("W DONE N=%d..%d M<=%d caseI/I' witnessed=%lld failures=%lld caseII(not witnessed)=%lld ; Lemma1(a) point checks=%lld failures=%lld\n", lo, hi, M, tested, fail, caseII, l1, l1f);
  return 0;
}

// ---------------------------------------------------------------- mode X: instrument self-check vs exact ML
static int modeX(unsigned long long seed, long iters) {
  rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
  long mism = 0, tot = 0;
  for (long it = 0; it < iters; it++) {
    int N = 4 + (int)(rnd() % 10);
    int r1 = N / 2 + 1 + (int)(rnd() % (N - N / 2)), r2 = N / 2 + 1 + (int)(rnd() % (N - N / 2)); if (r1 == r2) continue; if (r1 > r2) { int t = r1; r1 = r2; r2 = t; }
    ll w1 = N + 1 + (int)(rnd() % 60), w2 = N + 1 + (int)(rnd() % 60); if (w1 == w2) continue;
    ll vs[64]; int nv = retained(N, r1, r2, vs); ll V[64]; int k = 0; for (int i = 0; i < nv; i++) V[k++] = vs[i]; V[k++] = w1; V[k++] = w2;
    ll mn, md; ml_exact(V, k, &mn, &md);
    // at level = ML : some piece survives ; at level ML + 1/(1000 md): none ; at level ML - 1/(1000 md): positive piece
    ll K = 1000;
    ll lv[3][2] = { {mn, md}, {mn * K + 1, md * K}, {mn * K - 1, md * K} };
    int res[3];
    for (int z = 0; z < 3; z++) {
      Pc *a = T1, *b = T2; int n = 1; a[0].an = 0; a[0].ad = 1; a[0].bn = 1; a[0].bd = 2;
      for (int i = 0; i < k && n > 0; i++) { n = sub(a, n, V[i], lv[z][0], lv[z][1], b); Pc *t = a; a = b; b = t; }
      res[z] = z == 0 ? (n > 0) : (z == 1 ? (n > 0) : (n > 0 && has_pos(a, n)));
    }
    tot++;
    if (!(res[0] == 1 && res[1] == 0 && res[2] == 1)) { mism++; printf("XMIS N=%d R=(%d,%d) w=(%lld,%lld) ML=%lld/%lld res=%d%d%d\n", N, r1, r2, w1, w2, mn, md, res[0], res[1], res[2]); }
  }
  printf("X DONE sets=%ld mismatches=%ld\n", tot, mism);
  return 0;
}

// ---------------------------------------------------------------- mode R1: single R at arbitrary level p/q, optional prune
int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "modes: A lo hi M | B lo hi capmul prune | R N r1 r2 cap p q prune | Cs lo hi M | Cr seed iters Nmax | D Nmax | L Nmax | W lo hi M | X seed iters\n"); return 1; }
  const char *m = argv[1];
  if (!strcmp(m, "A")) return modeA(atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
  if (!strcmp(m, "B")) return modeB(atoi(argv[2]), atoi(argv[3]), atoi(argv[4]), atoi(argv[5]));
  if (!strcmp(m, "I")) { int N = atoi(argv[2]), r1 = atoi(argv[3]), r2 = atoi(argv[4]), m1 = atoi(argv[5]), m2 = atoi(argv[6]); verbose_T = 1;
    ll vs[3100]; int nv = retained(N, r1, r2, vs); int n0 = good_of(vs, nv, 1, N + 1, G0); testinst(N, r1, r2, m1, m2, G0, n0);
    printf("I tightPred=%lld tightExact=%lld winmis=%lld\n", T_tightpred, T_tightex, T_winmis); return 0; }
  if (!strcmp(m, "Cx")) { allowbig = 1; return modeC_sweep(atoi(argv[2]), atoi(argv[3]), atoi(argv[4])); }
  if (!strcmp(m, "BN")) return modeBN(atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
  if (!strcmp(m, "R")) {
    int N = atoi(argv[2]), r1 = atoi(argv[3]), r2 = atoi(argv[4]); ll cap = atoll(argv[5]), p = atoll(argv[6]), q = atoll(argv[7]); int prune = atoi(argv[8]);
    runR(N, r1, r2, cap, p, q, prune, 1);
    printf("R DONE N=%d R=(%d,%d) cap=%lld level=%lld/%lld pairs=%lld exceptions=%lld ALLW2=%lld pointflags=%lld capflags=%lld maxT-1=%lld maxW0g=%lld\n", N, r1, r2, cap, p, q, b_cnt, b_exc, b_all, b_point, b_cap, b_maxT, b_maxW0);
    return 0;
  }
  if (!strcmp(m, "Cs")) return modeC_sweep(atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
  if (!strcmp(m, "Cr")) return modeC_rand(strtoull(argv[2], 0, 10), atol(argv[3]), atoi(argv[4]));
  if (!strcmp(m, "D")) return modeD(atoi(argv[2]));
  if (!strcmp(m, "L")) return modeL(atoi(argv[2]));
  if (!strcmp(m, "W")) return modeW(atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
  if (!strcmp(m, "X")) return modeX(strtoull(argv[2], 0, 10), atol(argv[3]));
  return 1;
}
