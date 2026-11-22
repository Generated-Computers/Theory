// Round-based evaluator for candidate parallel algorithms on Sequential NOR (NOTE.md §5j).
//
// The candidate family is bounded-support symbolic substitution. Each position i holds an exact
// expression x_i = T_i(x_{v_1}, ..., x_{v_k}) over at most K earlier positions, as a truth table.
// Initially T_i = NOR(x_{i-1}, x_{j_i}). In each synchronous round every position (i) restricts its
// table by variables already known, and (ii) substitutes for some unknown variables v their own
// expressions from the previous round (pointer jumping), when the result, after removing variables
// the table does not depend on, has at most K variables. A position is known when its table is
// constant. Each round is constant depth with polynomial work for constant K, so rounds measure
// parallel time. The genome chooses K, the substitution order, the number of substitutions per
// round, random level gating (pivots that stay symbolic for a while), whether to accept merges
// that exceed K before simplification, and up to three alternative expressions per position, each
// with its own substitution order (a substitution uses the alternative giving the smallest result).
// Modes "kp" and "kpr" report the Kleene-prefix and relevance-pruned round counts (max d, max D) as
// baselines. Mode "newton" runs GF(2) Newton from x = (1,0,...,0) (paper Section 4): each round solves
// the linearised triangular system, an NC^2 step, and the iteration stops at a fixed point, which is
// the true trace; it reports the number of rounds.
//
// Every value is checked against the true trace; an error is a bug and is reported.
// usage: ./engine MODE K ORDERS MAXSUB RHO TL TRYSIMP SEED CAPFACTOR file1.bin [file2.bin ...]
//   MODE = sub | kp | kpr | newton; ORDERS: one digit per alternative expression (1-3 alternatives):
//   0 latest first, 1 earliest first, 2 random, 3 smallest expression first,
//   4 anchored doubling (round t substitutes all variables >= floor(i/2^t)*2^t; ignores MAXSUB)
//   MAXSUB: substitutions per position per round (0 = unlimited); RHO: pivot level parameter
//   (0 = off); TL: rounds per pivot level; TRYSIMP: 1 = allow K+2 before simplification;
//   CAPFACTOR c: round cap = c * log2(n)^2. Output per file:
//   file n rounds finished stuck known_frac mean_k_unknown errors
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

#ifndef KMAX
#define KMAX 6                  // compile with -DKMAX=12 for wide supports (tables of 2^KMAX bits)
#endif
#define UMAX (KMAX + 2)
#define TW (KMAX > 6 ? (1 << (KMAX - 6)) : 1)
#define BW (1 << (UMAX - 6))
typedef struct { int k; int v[KMAX]; uint64_t t[TW]; } Expr;

static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double unif(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int K, MAXSUB, TL, TRYSIMP;
static double RHO;

// table of up to UMAX variables in 4 words
typedef struct { int u; int v[UMAX]; uint64_t w[BW]; } Big;
static inline int bget(const uint64_t *w, int a) { return (w[a >> 6] >> (a & 63)) & 1; }
static inline void bset(uint64_t *w, int a) { w[a >> 6] |= 1ULL << (a & 63); }

// substitute variable index a of E by F; returns 0 if the union exceeds UMAX
static int merge(const Expr *E, int a, const Expr *F, Big *G) {
    int u = 0;
    for (int q = 0; q < E->k; q++) if (q != a) G->v[u++] = E->v[q];
    for (int q = 0; q < F->k; q++) {
        int x = F->v[q], dup = 0;
        for (int r = 0; r < u; r++) if (G->v[r] == x) { dup = 1; break; }
        if (!dup) { if (u == UMAX) return 0; G->v[u++] = x; }
    }
    G->u = u; memset(G->w, 0, sizeof G->w);
    int pe[KMAX], pf[KMAX];
    for (int q = 0; q < E->k; q++) { pe[q] = -1; for (int r = 0; r < u; r++) if (G->v[r] == E->v[q]) pe[q] = r; }
    for (int q = 0; q < F->k; q++) for (int r = 0; r < u; r++) if (G->v[r] == F->v[q]) pf[q] = r;
    for (int al = 0; al < (1 << u); al++) {
        int beta = 0;
        for (int q = 0; q < F->k; q++) beta |= ((al >> pf[q]) & 1) << q;
        int uv = bget(F->t, beta), ga = 0;
        for (int q = 0; q < E->k; q++) ga |= (q == a ? uv : ((al >> pe[q]) & 1)) << q;
        if (bget(E->t, ga)) bset(G->w, al);
    }
    return 1;
}

// remove variables the table does not depend on
static void simplify(Big *G) {
    for (int q = G->u - 1; q >= 0; q--) {
        int dep = 0, N = 1 << G->u;
        for (int al = 0; al < N && !dep; al++) if (!((al >> q) & 1) && bget(G->w, al) != bget(G->w, al | (1 << q))) dep = 1;
        if (dep) continue;
        uint64_t nw[BW]; memset(nw, 0, sizeof nw);
        for (int al = 0; al < N / 2; al++) {
            int lo = al & ((1 << q) - 1), hi = al >> q;
            if (bget(G->w, lo | (hi << (q + 1)))) bset(nw, al);
        }
        memcpy(G->w, nw, sizeof nw);
        for (int r = q; r < G->u - 1; r++) G->v[r] = G->v[r + 1];
        G->u--;
    }
}

static int tobig_fits(const Big *G, Expr *E) {
    if (G->u > K) return 0;
    E->k = G->u; for (int q = 0; q < G->u; q++) E->v[q] = G->v[q];
    memset(E->t, 0, sizeof E->t);
    int words = G->u > 6 ? 1 << (G->u - 6) : 1;
    for (int q = 0; q < words; q++) E->t[q] = G->w[q];
    if (G->u < 6) E->t[0] &= (1ULL << (1 << G->u)) - 1;
    return 1;
}

static int same(const Expr *a, const Expr *b) {
    if (a->k != b->k || memcmp(a->t, b->t, sizeof a->t)) return 0;
    for (int q = 0; q < a->k; q++) if (a->v[q] != b->v[q]) return 0;
    return 1;
}

// restrict by known variables (always fits); NE alternatives per position, all equal once known
static int NE = 1, ORD[3];
static void restrict_known(Expr *E, const Expr *old) {
    for (int again = 1; again;) {
        again = 0;
        for (int q = 0; q < E->k; q++) if (old[(long)E->v[q] * NE].k == 0) {
            Big G; merge(E, q, &old[(long)E->v[q] * NE], &G); simplify(&G); tobig_fits(&G, E); again = 1; break;
        }
    }
}

static int minalt(const Expr *A, int v) {
    int m = A[(long)v * NE].k;
    for (int f = 1; f < NE; f++) if (A[(long)v * NE + f].k < m) m = A[(long)v * NE + f].k;
    return m;
}

// one alternative expression of one position for one round
static void step_expr(Expr *E, const Expr *A, const int *level, int lev, int order, long t, int i) {
    int cand[UMAX], nc = 0;
    restrict_known(E, A);
    // order 4 (anchored doubling): in round t substitute exactly the variables >= floor(i/2^t)*2^t,
    // latest first, so that every expression stays over one cut; once the anchor is 0 this is order 0
    long anchor = 0;
    if (order == 4 && t < 62) anchor = ((long)i >> t) << t;
    for (int q = 0; q < E->k; q++) if (E->v[q] >= anchor) cand[nc++] = E->v[q];
    for (int a = 0; a < nc; a++) for (int b = a + 1; b < nc; b++) {
        int sw = 0, x1 = cand[a], x2 = cand[b];
        if (order == 0 || order == 4) sw = x2 > x1;
        else if (order == 1) sw = x2 < x1;
        else if (order == 3) { int k1 = minalt(A, x1), k2 = minalt(A, x2); sw = k2 < k1 || (k2 == k1 && x2 > x1); }
        if (sw) { cand[a] = x2; cand[b] = x1; }
    }
    if (order == 2) for (int a = nc - 1; a > 0; a--) { int b = rnd() % (a + 1); int tmp = cand[a]; cand[a] = cand[b]; cand[b] = tmp; }
    int subs = 0;
    for (int c = 0; c < nc; c++) {
        if (MAXSUB && subs >= MAXSUB && order != 4) break;
        int v = cand[c], a = -1;
        for (int q = 0; q < E->k; q++) if (E->v[q] == v) a = q;
        if (a < 0 || A[(long)v * NE].k == 0) continue;
        if (RHO > 0 && level[v] > lev) continue;
        Expr best; int bk = 99;
        for (int f = 0; f < NE; f++) {
            const Expr *F = &A[(long)v * NE + f];
            int u = E->k - 1;                                       // union size bound
            for (int q = 0; q < F->k; q++) { int x2 = F->v[q], dup = 0; for (int r = 0; r < E->k; r++) if (r != a && E->v[r] == x2) dup = 1; u += !dup; }
            if (u > (TRYSIMP ? K + 2 : K)) continue;
            Big G; if (!merge(E, a, F, &G)) continue;
            simplify(&G);
            Expr N; if (!tobig_fits(&G, &N)) continue;
            if (N.k < bk) { best = N; bk = N.k; }
        }
        if (bk < 99) { *E = best; subs++; }
    }
    restrict_known(E, A);
}

static void run_sub(int n, const int *j, const char *x, const int *level, long cap,
                    long *rounds, int *fin, int *stuck, double *kf, double *mk, long *err) {
    long sz = (long)(n + 1) * NE;
    Expr *A = malloc(sz * sizeof(Expr)), *Bf = malloc(sz * sizeof(Expr));
    memset(A, 0, sz * sizeof(Expr)); memset(Bf, 0, sz * sizeof(Expr));
    for (int e = 0; e < NE; e++) { A[e].k = 0; A[e].t[0] = 1; }
    for (int i = 1; i <= n; i++) for (int e = 0; e < NE; e++) {
        Expr *E = &A[(long)i * NE + e];
        if (j[i] == i - 1) { E->k = 1; E->v[0] = i - 1; E->t[0] = 0x1; }       // NOT
        else { E->k = 2; E->v[0] = i - 1; E->v[1] = j[i]; E->t[0] = 0x1; }     // NOR: only (0,0) -> 1
    }
    long t; *fin = 0; *stuck = 0;
    for (t = 1; t <= cap; t++) {
        int changed = 0, allk = 1;
        int lev = TL > 0 ? (int)(t / TL) : 1 << 30;
        for (int i = 0; i <= n; i++) {
            Expr *O = &A[(long)i * NE], *N = &Bf[(long)i * NE];
            if (O[0].k == 0) { for (int e = 0; e < NE; e++) N[e] = O[e]; continue; }
            int kn = -1;
            for (int e = 0; e < NE; e++) { N[e] = O[e]; step_expr(&N[e], A, level, lev, ORD[e], t, i); if (N[e].k == 0) kn = e; }
            if (kn >= 0) for (int e = 0; e < NE; e++) N[e] = N[kn];
            for (int e = 0; e < NE; e++) if (!same(&N[e], &O[e])) changed = 1;
            if (N[0].k) allk = 0;
        }
        Expr *tmp = A; A = Bf; Bf = tmp;
        if (allk) { *fin = 1; break; }
        if (!changed) { *stuck = 1; break; }
    }
    *rounds = t > cap ? cap : t;
    long known = 0; double ks = 0; long unk = 0; *err = 0;
    for (int i = 0; i <= n; i++) {
        const Expr *E = &A[(long)i * NE];
        if (E->k == 0) { known++; if ((int)(E->t[0] & 1) != x[i]) (*err)++; }
        else { ks += E->k; unk++; }
    }
    *kf = (double)known / (n + 1); *mk = unk ? ks / unk : 0;
    free(A); free(Bf);
}

int main(int argc, char **argv) {
    if (argc < 11) { fprintf(stderr, "usage: see header\n"); return 1; }
    const char *mode = argv[1];
    K = atoi(argv[2]); NE = (int)strlen(argv[3]); if (NE < 1 || NE > 3) { fprintf(stderr, "1-3 orders\n"); return 1; }
    for (int e = 0; e < NE; e++) ORD[e] = argv[3][e] - '0'; MAXSUB = atoi(argv[4]); RHO = atof(argv[5]);
    TL = atoi(argv[6]); TRYSIMP = atoi(argv[7]); uint64_t seed = strtoull(argv[8], 0, 10); double capf = atof(argv[9]);
    if (K < 1 || K > KMAX) { fprintf(stderr, "K out of range\n"); return 1; }
    for (int f = 10; f < argc; f++) {
        FILE *fh = fopen(argv[f], "rb"); if (!fh) { perror(argv[f]); return 1; }
        int n; if (fread(&n, 4, 1, fh) != 1) return 1;
        int *j = malloc((n + 1) * sizeof(int)); j[0] = 0;
        if (fread(j + 1, 4, n, fh) != (size_t)n) return 1; fclose(fh);
        char *x = malloc(n + 1); x[0] = 1;
        for (int i = 1; i <= n; i++) x[i] = (x[i - 1] == 0 && x[j[i]] == 0);
        long cap = (long)ceil(capf * log2((double)n) * log2((double)n));
        if (!strcmp(mode, "newton")) {
            char *y = calloc(n + 1, 1), *z = calloc(n + 1, 1); y[0] = 1;
            long cap2 = n + 2, t; int fin = 0;
            for (t = 1; t <= cap2; t++) {
                z[0] = 1;
                for (int i = 1; i <= n; i++) {            // x_i = 1 + x_{i-1}(1+y_j) + x_j(1+y_{i-1}) + y_{i-1} y_j
                    int a = i - 1, b = j[i];
                    z[i] = 1 ^ (z[a] & (1 ^ y[b])) ^ (z[b] & (1 ^ y[a])) ^ (y[a] & y[b]);
                }
                if (!memcmp(y, z, n + 1)) { fin = 1; break; }
                memcpy(y, z, n + 1);
            }
            long errs = 0; for (int i = 0; i <= n; i++) errs += y[i] != x[i];
            printf("%s %d %ld %d 0 1.00000 0.000 %ld\n", argv[f], n, fin ? t - 1 : cap2, fin, errs);
            free(y); free(z);
        } else if (!strcmp(mode, "sub")) {
            rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0x2545F4914F6CDD1DULL) ^ (uint64_t)n; if (!rs) rs = 1;
            int *level = malloc((n + 1) * sizeof(int));
            for (int i = 0; i <= n; i++) { int L = 0; if (RHO > 0) while (unif() < RHO && L < 60) L++; level[i] = L; }
            long rounds, err; int fin, st; double kf, mk;
            run_sub(n, j, x, level, cap, &rounds, &fin, &st, &kf, &mk, &err);
            printf("%s %d %ld %d %d %.5f %.3f %ld\n", argv[f], n, rounds, fin, st, kf, mk, err);
            free(level);
        } else {
            int *d = malloc((n + 1) * sizeof(int)), *D = malloc((n + 1) * sizeof(int)), md = 1, mD = 1;
            d[0] = D[0] = 0; d[1] = D[1] = 1;
            for (int i = 2; i <= n; i++) {
                int nt = j[i] != i - 1, rel = x[i - 1] == 0, res = nt && x[j[i]];
                int c = 1 + d[j[i]];
                d[i] = res ? c : (nt ? (d[i - 1] > c ? d[i - 1] : c) : d[i - 1]);
                c = 1 + D[j[i]];
                if (res && rel) D[i] = c; else if (res) D[i] = D[i - 1] < c ? D[i - 1] : c;
                else if (rel && nt) D[i] = D[i - 1] > c ? D[i - 1] : c; else D[i] = D[i - 1];
                if (d[i] > md) md = d[i]; if (D[i] > mD) mD = D[i];
            }
            printf("%s %d %d 1 0 1.00000 0.000 0\n", argv[f], n, strcmp(mode, "kp") ? mD : md);
            free(d); free(D);
        }
        free(j); free(x);
    }
    return 0;
}
