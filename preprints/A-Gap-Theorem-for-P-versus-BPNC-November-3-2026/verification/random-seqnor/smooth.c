// Noise-tolerant embedding of NOR circuits into Sequential NOR, and Newton on smoothed instances.
// Base: positions 0 (x0=1), 1 (x1=0, j1=0 forced), then for each logical gate t=1..s and copy l=1..m
// a cell = complete ternary tree of depth h in post-order; leaf = NOR gadget [x0,a,x1,b],
// internal node = MAJ gadget [x0,a,x1,b,b,g2,c,g4]. Leaf inputs are cells (u,r),(v,r') with r,r' uniform.
// usage: smooth MODE ...
//   smooth embed s m h depthwin eps trials seed maxrounds   (deep random circuit; fidelity + Newton)
//   smooth base  FAMILY n eps trials seed maxrounds [kp]     (FAMILY: wn | im2 | im3 | one | half | sqrt | unif)
//   (embed also takes an optional 10th argument kp: run the Kleene-prefix iteration instead of Newton)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double unif(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static inline long below(long k) { return (long)(rnd() % (uint64_t)k); }

static long n, *J, *Jt; static unsigned char *xs, *x, *d;

static void trace(const long *j) {
    xs[0] = 1;
    for (long i = 1; i <= n; i++) xs[i] = !(xs[i - 1] | xs[j[i]]);
}
static long newton(const long *j, long maxr) {     // rounds from (1,0,...,0) until iterate == trace
    memset(x, 0, n + 1); x[0] = 1;
    for (long t = 0; t <= maxr; t++) {
        if (!memcmp(x, xs, n + 1)) return t;
        d[0] = 0;
        for (long i = 1; i <= n; i++) {
            long p = i - 1, q = j[i];
            unsigned char F = x[i] ^ ((1 ^ x[p]) & (1 ^ x[q]));
            unsigned char sgn = (p == q) ? d[p] : (((1 ^ x[q]) & d[p]) ^ ((1 ^ x[p]) & d[q]));
            d[i] = F ^ sgn;
        }
        for (long i = 0; i <= n; i++) x[i] ^= d[i];
        x[0] = 1;
    }
    return -1;
}

// Kleene-prefix (KP) iteration: certain knowledge only. Gate k is resolved when j_k = k-1 (a NOT gate)
// or x_{j_k} is known; a resolved gate is a reset if j_k != k-1 and x_{j_k} = 1. Position i becomes
// known when every gate between the last resolved reset (or position 0) and i is resolved.
static unsigned char *kn, *kn2, *kv;
static long kp_rounds(const long *j, long maxr) {
    if (!kn) { kn = calloc(n + 1, 1); kn2 = calloc(n + 1, 1); kv = calloc(n + 1, 1); }
    memset(kn, 0, n + 1); kn[0] = 1; kv[0] = 1;
    for (long t = 0; t <= maxr; t++) {
        long cnt = 0; for (long i = 0; i <= n; i++) cnt += kn[i];
        if (cnt == n + 1) {
            for (long i = 0; i <= n; i++) if (kv[i] != xs[i]) { fprintf(stderr, "KP value error at %ld\n", i); exit(3); }
            return t;
        }
        int ok = 1; unsigned char v = 1; kn2[0] = 1;
        for (long i = 1; i <= n; i++) {
            long q = j[i];
            if (q == i - 1) { v ^= 1; }
            else if (kn[q]) { if (kv[q]) { v = 0; ok = 1; } else v ^= 1; }
            else ok = 0;
            kn2[i] = (unsigned char)ok;
            if (ok) { if (kn[i] && kv[i] != v) { fprintf(stderr, "KP inconsistency at %ld\n", i); exit(3); } kv[i] = v; }
            else if (kn[i]) { fprintf(stderr, "KP knowledge lost at %ld\n", i); exit(3); }
        }
        memcpy(kn, kn2, n + 1);
    }
    return -1;
}
static void perturb(double eps) {
    for (long i = 1; i <= n; i++) Jt[i] = (unif() < eps) ? below(i) : J[i];
}
static void alloc(long nn) {
    n = nn; J = calloc(n + 1, sizeof *J); Jt = calloc(n + 1, sizeof *Jt);
    xs = calloc(n + 1, 1); x = calloc(n + 1, 1); d = calloc(n + 1, 1);
}

// ---- embedding ----
static long s, m, h, pos_next, *cellout; // cellout[t*m + l] = output position of cell (t,l)
static int *gu, *gv, *gval;              // logical circuit: input codes: >=1 gate index, 0 const0, -1 const1
static long inpos(int u, long r) { return u >= 1 ? cellout[(long)u * m + r] : (u == 0 ? 1 : 0); }
static void emit(long ptr) { pos_next++; J[pos_next] = ptr; }
static long leaf(long a, long b) { long st = pos_next; emit(0); emit(a); emit(1); emit(b); (void)st; return pos_next; }
static long majg(long a, long b, long c) {
    long g1 = pos_next + 1; emit(0); emit(a); emit(1); emit(b); emit(b); emit(g1 + 1); emit(c); emit(g1 + 3);
    return pos_next;
}
static long tree(int t, int lev) {
    if (lev == 0) return leaf(inpos(gu[t], below(m)), inpos(gv[t], below(m)));
    long a = tree(t, lev - 1), b = tree(t, lev - 1), c = tree(t, lev - 1);
    return majg(a, b, c);
}

int main(int argc, char **argv) {
    if (argc < 2) return 1;
    if (!strcmp(argv[1], "embed")) {
        s = atol(argv[2]); m = atol(argv[3]); h = atol(argv[4]); int win = atoi(argv[5]);
        double eps = atof(argv[6]); int trials = atoi(argv[7]); rs ^= (uint64_t)atoll(argv[8]) * 0x9E3779B97F4A7C15ULL;
        long maxr = atol(argv[9]);
        gu = calloc(s + 1, sizeof *gu); gv = calloc(s + 1, sizeof *gv); gval = calloc(s + 1, sizeof *gval);
        for (int t = 1; t <= s; t++) {             // deep circuit: chain plus a recent second input
            gu[t] = t - 1 >= 1 ? t - 1 : 0;
            int lo = t - win < 1 ? 1 : t - win;
            gv[t] = (t > 1 && unif() < 0.9) ? lo + (int)below(t - lo) : (unif() < 0.5 ? 0 : -1);
            int a = gu[t] >= 1 ? gval[gu[t]] : (gu[t] == 0 ? 0 : 1), b = gv[t] >= 1 ? gval[gv[t]] : (gv[t] == 0 ? 0 : 1);
            gval[t] = !(a | b);
        }
        long cell = 0, p3 = 1; for (int k = 0; k < h; k++) p3 *= 3;
        cell = 8 * p3 - 4;
        alloc(1 + s * m * cell);
        cellout = calloc((s + 1) * m, sizeof *cellout);
        pos_next = 1; J[1] = 0;
        for (int t = 1; t <= s; t++) for (long l = 0; l < m; l++) cellout[(long)t * m + l] = tree(t, (int)h);
        if (pos_next != n) { fprintf(stderr, "layout %ld vs %ld\n", pos_next, n); return 2; }
        int ones = 0; for (int t = 1; t <= s; t++) ones += gval[t];
        long okc = 0, sumr = 0, capped = 0; double worstfrac = 0, meanbad = 0;
        for (int tr = 0; tr < trials; tr++) {
            perturb(eps); trace(Jt);
            okc += (xs[n] == gval[s]);
            double wf = 0, tb = 0;
            for (int t = 1; t <= s; t++) { int bad = 0; for (long l = 0; l < m; l++) bad += xs[cellout[(long)t * m + l]] != gval[t];
                double f = (double)bad / m; tb += f; if (f > wf) wf = f; }
            if (wf > worstfrac) worstfrac = wf; meanbad += tb / s;
            if (maxr > 0) { long r = (argc > 10 && !strcmp(argv[10], "kp")) ? kp_rounds(Jt, maxr) : newton(Jt, maxr);
                if (r < 0) { capped++; sumr += maxr; } else sumr += r; }
        }
        printf("embed s=%ld m=%ld h=%ld n=%ld eps=%.5f  output-correct=%.3f  mean-bad-frac=%.4f  worst-bundle-bad=%.3f",
               s, m, h, n, eps, (double)okc / trials, meanbad / trials, worstfrac);
        if (maxr > 0) printf("  %s-mean=%.1f (capped %ld/%d at %ld)", (argc > 10 && !strcmp(argv[10], "kp")) ? "kp" : "newton",
                             (double)sumr / trials, capped, trials, maxr);
        printf("  [ones among gates %d/%ld]\n", ones, s);
        return 0;
    }
    if (!strcmp(argv[1], "base")) {
        const char *fam = argv[2]; alloc(atol(argv[3])); double eps = atof(argv[4]); int trials = atoi(argv[5]);
        rs ^= (uint64_t)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL; long maxr = atol(argv[7]);
        J[1] = 0;
        for (long i = 2; i <= n; i++) {
            if (!strcmp(fam, "wn")) { long w[6] = {0, 0, 1, 0, 1, 2}; J[i] = i <= 5 ? w[i] : (i % 2 == 0 ? 1 : i - 2); }
            else if (!strcmp(fam, "im2")) J[i] = i - 2 < 0 ? 0 : i - 2;
            else if (!strcmp(fam, "im3")) J[i] = i - 3 < 0 ? 0 : i - 3;
            else if (!strcmp(fam, "one")) J[i] = 1;
            else if (!strcmp(fam, "half")) J[i] = i / 2;
            else if (!strcmp(fam, "sqrt")) J[i] = i - 1 - (long)sqrt((double)i) < 0 ? 0 : i - 1 - (long)sqrt((double)i);
            else J[i] = below(i);
        }
        int usekp = argc > 8 && !strcmp(argv[8], "kp");
        long sumr = 0, capped = 0, mx = 0;
        for (int tr = 0; tr < trials; tr++) { perturb(eps); trace(Jt); long r = usekp ? kp_rounds(Jt, maxr) : newton(Jt, maxr);
            if (r < 0) { capped++; r = maxr; } sumr += r; if (r > mx) mx = r; }
        printf("base %s n=%ld eps=%.4f %s-mean=%.2f max=%ld capped=%ld/%d\n", fam, n, eps, usekp ? "kp" : "newton", (double)sumr / trials, mx, capped, trials);
        return 0;
    }
    return 1;
}
