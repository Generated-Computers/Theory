// Probe the noise threshold of parallel algorithms on smoothed Sequential NOR.
// usage: kp_probe ALG FAMILY n eps trials seed [maxrounds]
//   ALG: kp (Kleene-prefix rounds = dependency depth, O(n) DP) | kpw (window-hypothesis variant, simulated)
//        | newton | phi (reset-set iteration)
//   FAMILY: im2 | log | cbrt | sqrt | spreadD (distance in [D,2D)) | lgu (log-uniform distance) | fixC (distance C) | zero | half
// Prints mean and max rounds over trials (-1 = did not finish within maxrounds).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>

static uint64_t s0 = 0x123456789abcdefULL, s1 = 0xfedcba9876543210ULL;
static inline uint64_t rnd(void) { uint64_t a = s0, b = s1; s0 = b; a ^= a << 23; s1 = a ^ b ^ (a >> 17) ^ (b >> 26); return s1 + b; }
static void seed(uint64_t z) { s0 = z * 0x9E3779B97F4A7C15ULL + 1; s1 = (z + 7) * 0xBF58476D1CE4E5B9ULL + 3; for (int i = 0; i < 20; i++) rnd(); }
static inline double U(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static inline long below(long k) { return (long)(rnd() % (uint64_t)k); }
static inline uint64_t hsh(uint64_t z) { z += 0x9E3779B97F4A7C15ULL; z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; return z ^ (z >> 31); }

static long n, *J, *Jt; static unsigned char *x, *y, *kn, *kv; static int *d; static long maxr;

static void trace(const long *j) { x[0] = 1; for (long i = 1; i <= n; i++) x[i] = !(x[i - 1] | x[j[i]]); }

static long kp(const long *j) {            // max dependency depth = number of KP rounds (Lemma kp)
    d[0] = 0; int M = 0, mx = 0;
    for (long i = 1; i <= n; i++) {
        long q = j[i];
        if (q != i - 1) { if (x[q]) M = d[q]; else if (d[q] > M) M = d[q]; }
        d[i] = 1 + M; if (d[i] > mx) mx = d[i];
    }
    return mx;
}

// Exact round count of the relevance variant in O(n): D(i) = 1 + min over anchors r of
// max(D(j_r), D(j_k) for gates k in (r,i] with x_{k-1} = 0); anchors are 0 and the hits after the
// last hit at a gate with x_{k-1} = 0. m holds the min over anchors of the running max.
static long kprd(const long *j) {
    d[0] = 0; int m = 0, mx = 0;
    for (long i = 1; i <= n; i++) {
        long q = j[i]; int isnot = (q == i - 1), rel = !x[i - 1], hit = !isnot && x[q];
        if (hit && rel) m = d[q];
        else if (hit) { if (d[q] < m) m = d[q]; }
        else if (rel && !isnot) { if (d[q] > m) m = d[q]; }
        d[i] = 1 + m; if (d[i] > mx) mx = d[i];
    }
    return mx;
}

// Window-hypothesis iteration: an anchor is 0 or a gate whose pointer is known with value 1. From the
// smallest live anchor the values are hypothesised to alternate; a gate with x_{i-1} = 0 needs its
// pointer value 0, read either from the hypothesis (pointer >= anchor) or from the known set.
static long kpw(const long *j) {
    memset(kn, 0, n + 1); kn[0] = 1;
    for (long t = 0; t <= maxr; t++) {
        long c = 0; for (long i = 0; i <= n; i++) c += kn[i];
        if (c == n + 1) return t;
        long a = 0;                         // smallest live anchor, -1 if none
        unsigned char *nk = y; nk[0] = 1;
        for (long i = 1; i <= n; i++) {
            long q = j[i]; int isnot = (q == i - 1), rel = !x[i - 1];
            int known_one = !isnot && kn[q] && x[q];
            if (rel) {
                if (x[q] && !isnot) a = -1;            // a reset at a relevant gate breaks every hypothesis
                else if (a >= 0 && q < a && !kn[q]) a = -1;
            }
            if (known_one && a < 0) a = i;             // new anchor
            nk[i] = (a >= 0);
        }
        for (long i = 0; i <= n; i++) { if (kn[i] && !nk[i]) { fprintf(stderr, "kpw lost %ld\n", i); exit(3); } kn[i] = nk[i]; }
    }
    return -1;
}

// Relevance variant (no window hypothesis): from the last resolved reset r, only gates k with
// x_{k-1} = 0 (by alternation from r) need a known pointer value.
static long kpr(const long *j) {
    memset(kn, 0, n + 1); kn[0] = 1; kv[0] = 1;
    for (long t = 0; t <= maxr; t++) {
        long c = 0; for (long i = 0; i <= n; i++) c += kn[i];
        if (c == n + 1) { for (long i = 0; i <= n; i++) if (kv[i] != x[i]) { fprintf(stderr, "kpr value %ld\n", i); exit(3); } return t; }
        int ok = 1; unsigned char v = 1; y[0] = 1;
        for (long i = 1; i <= n; i++) {
            long q = j[i]; int isnot = (q == i - 1), res = isnot || kn[q];
            if (res && !isnot && kv[q]) { v = 0; ok = 1; }
            else { if (v == 0 && !res) ok = 0; v ^= 1; }
            y[i] = (unsigned char)ok;
            if (ok) { if (kn[i] && kv[i] != v) { fprintf(stderr, "kpr incons %ld\n", i); exit(3); } kv[i] = v; }
            else if (kn[i]) { fprintf(stderr, "kpr lost %ld\n", i); exit(3); }
        }
        memcpy(kn, y, n + 1);
    }
    return -1;
}

static long newton(const long *j) {
    memset(y, 0, n + 1); y[0] = 1;
    for (long t = 0; t <= maxr; t++) {
        if (!memcmp(y, x, n + 1)) return t;
        unsigned char *dd = kn; dd[0] = 0;
        for (long i = 1; i <= n; i++) {
            long p = i - 1, q = j[i];
            unsigned char F = y[i] ^ ((1 ^ y[p]) & (1 ^ y[q]));
            unsigned char sg = (p == q) ? dd[p] : (((1 ^ y[q]) & dd[p]) ^ ((1 ^ y[p]) & dd[q]));
            dd[i] = F ^ sg;
        }
        for (long i = 0; i <= n; i++) y[i] ^= dd[i];
        y[0] = 1;
    }
    return -1;
}

static long phi(const long *j) {          // y_{t+1}: alternate from the gates k (non-NOT) with y_t(j_k) = 1
    y[0] = 1; for (long i = 1; i <= n; i++) y[i] = !y[i - 1];
    for (long t = 0; t <= maxr; t++) {
        if (!memcmp(y, x, n + 1)) return t;
        unsigned char v = 1; kv[0] = 1;
        for (long i = 1; i <= n; i++) { long q = j[i]; if (q != i - 1 && y[q]) v = 0; else v ^= 1; kv[i] = v; }
        memcpy(y, kv, n + 1);
    }
    return -1;
}

static void family(const char *f) {
    J[1] = 0;
    for (long i = 2; i <= n; i++) {
        long v;
        if (!strcmp(f, "im2")) v = i - 2;
        else if (!strcmp(f, "log")) v = i - 1 - (long)log((double)i);
        else if (!strcmp(f, "cbrt")) v = i - 1 - (long)cbrt((double)i);
        else if (!strcmp(f, "sqrt")) v = i - 1 - (long)sqrt((double)i);
        else if (!strncmp(f, "spread", 6)) { long D = atol(f + 6); v = i - D - (long)(hsh(i) % (uint64_t)D); }
        else if (!strcmp(f, "lgu")) { double u = (hsh(i) >> 11) * (1.0 / 9007199254740992.0); v = i - 1 - (long)pow((double)i, u); }
        else if (!strncmp(f, "fix", 3)) v = i - atol(f + 3);
        else if (!strcmp(f, "zero")) v = 0;
        else if (!strcmp(f, "half")) v = i / 2;
        else { fprintf(stderr, "unknown family %s\n", f); exit(1); }
        if (v < 0) v = 0; if (v > i - 2) v = i - 2; J[i] = v;
    }
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage\n"); return 1; }
    const char *alg = argv[1], *fam = argv[2]; n = atol(argv[3]); double eps = atof(argv[4]); int T = atoi(argv[5]);
    seed(atoll(argv[6])); maxr = argc > 7 ? atol(argv[7]) : 100000;
    J = calloc(n + 1, sizeof *J); Jt = calloc(n + 1, sizeof *Jt); x = calloc(n + 1, 1); y = calloc(n + 1, 1);
    kn = calloc(n + 1, 1); kv = calloc(n + 1, 1); d = calloc(n + 1, sizeof *d);
    family(fam);
    double s = 0; long mx = 0; int fail = 0;
    for (int t = 0; t < T; t++) {
        Jt[1] = 0; for (long i = 2; i <= n; i++) Jt[i] = (U() < eps) ? below(i) : J[i];
        trace(Jt);
        long r = !strcmp(alg, "kp") ? kp(Jt) : !strcmp(alg, "kpw") ? kpw(Jt) : !strcmp(alg, "kpr") ? kpr(Jt) : !strcmp(alg, "kprd") ? kprd(Jt) : !strcmp(alg, "newton") ? newton(Jt) : phi(Jt);
        if (r < 0) { fail++; r = maxr; }
        s += r; if (r > mx) mx = r;
    }
    printf("%-6s %-9s n=2^%-2d eps=%.2f mean=%8.1f max=%6ld%s\n", alg, fam, (int)lround(log2((double)n)), eps, s / T, mx,
           fail ? " (some capped)" : "");
    return 0;
}
