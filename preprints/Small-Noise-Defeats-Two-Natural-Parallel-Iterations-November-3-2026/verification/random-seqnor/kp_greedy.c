// Greedy adversarial bases against the Kleene-prefix iteration (kp) and its relevance variant (kpr).
// The base is built gate by gate: pointer j_k is chosen from a candidate list to maximise the mean
// depth D(k) over S training smoothings (oblivious: one base for all samples). The base is then
// tested on T fresh smoothings.
// usage: kp_greedy ALG n eps S T seed      (ALG: kp | kpr | last; last = D_last of Remark rem:kpr)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>

static uint64_t s0, s1;
static inline uint64_t rnd(void) { uint64_t a = s0, b = s1; s0 = b; a ^= a << 23; s1 = a ^ b ^ (a >> 17) ^ (b >> 26); return s1 + b; }
static void seed(uint64_t z) { s0 = z * 0x9E3779B97F4A7C15ULL + 1; s1 = (z + 7) * 0xBF58476D1CE4E5B9ULL + 3; for (int i = 0; i < 20; i++) rnd(); }
static inline double U(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static inline long below(long k) { return (long)(rnd() % (uint64_t)k); }

static int kpr, last;
// one gate update for one sample; returns new m (state) and writes x, d at k
static inline int step(unsigned char *x, int *d, int m, long k, long q) {
    int isnot = (q == k - 1), hit = !isnot && x[q];
    x[k] = !(x[k - 1] | x[q]);
    if (last) { if (hit) m = d[q]; else if (!x[k - 1] && !isnot && d[q] > m) m = d[q]; }
    else if (!kpr) { if (!isnot) { if (x[q]) m = d[q]; else if (d[q] > m) m = d[q]; } }
    else {
        int rel = !x[k - 1];
        if (hit && rel) m = d[q];
        else if (hit) { if (d[q] < m) m = d[q]; }
        else if (rel && !isnot) { if (d[q] > m) m = d[q]; }
    }
    d[k] = 1 + m; return m;
}

int main(int argc, char **argv) {
    if (argc < 7) return 1;
    kpr = !strcmp(argv[1], "kpr"); last = !strcmp(argv[1], "last"); long n = atol(argv[2]); double eps = atof(argv[3]);
    int S = atoi(argv[4]), T = atoi(argv[5]); seed(atoll(argv[6]));
    long *J = calloc(n + 1, sizeof *J);
    unsigned char *pi = malloc((size_t)S * (n + 1)); long *rh = malloc((size_t)S * (n + 1) * sizeof(long));
    unsigned char *X = malloc((size_t)S * (n + 1)); int *D = malloc((size_t)S * (n + 1) * sizeof(int)); int *M = calloc(S, sizeof(int));
    double *md1 = calloc(n + 1, sizeof(double)), *md0 = calloc(n + 1, sizeof(double)); // mean depth at ones / zeros
    for (int s = 0; s < S; s++) for (long i = 1; i <= n; i++) { pi[(size_t)s * (n + 1) + i] = U() < eps; rh[(size_t)s * (n + 1) + i] = below(i); }
    for (int s = 0; s < S; s++) { X[(size_t)s * (n + 1)] = 1; D[(size_t)s * (n + 1)] = 0; }
    long b1 = 0, b0 = 0; // positions with best mean depth among ones / zeros (weighted by frequency)
    J[1] = 0;
    for (long k = 1; k <= n; k++) {
        long cand[40]; int nc = 0;
        if (k == 1) cand[nc++] = 0;
        else {
            cand[nc++] = k - 1; cand[nc++] = 0;
            for (long c = 2; c <= 8; c++) if (k - c >= 0) cand[nc++] = k - c;
            if (b1 <= k - 2) cand[nc++] = b1; if (b0 <= k - 2) cand[nc++] = b0;
            for (int r = 0; r < 8; r++) { long lo = k > 64 ? k - 64 : 0; cand[nc++] = lo + below(k - 1 - lo); }
            for (int r = 0; r < 4; r++) cand[nc++] = below(k - 1);
        }
        double best = -1; long bq = cand[0];
        for (int c = 0; c < nc; c++) {
            long q = cand[c]; if (q > k - 1) continue; double v = 0;
            for (int s = 0; s < S; s++) {
                size_t o = (size_t)s * (n + 1); if (pi[o + k]) continue;
                unsigned char xk1 = X[o + k - 1], xq = X[o + q]; int m = M[s], isnot = (q == k - 1), hit = !isnot && xq;
                if (last) { if (hit) m = D[o + q]; else if (!xk1 && !isnot && D[o + q] > m) m = D[o + q]; }
                else if (!kpr) { if (!isnot) { if (xq) m = D[o + q]; else if (D[o + q] > m) m = D[o + q]; } }
                else { int rel = !xk1; if (hit && rel) m = D[o + q]; else if (hit) { if (D[o + q] < m) m = D[o + q]; } else if (rel && !isnot) { if (D[o + q] > m) m = D[o + q]; } }
                v += m;
            }
            if (v > best + 1e-9) { best = v; bq = q; }
        }
        J[k] = bq;
        double s1v = 0, c1 = 0, s0v = 0, c0 = 0;
        for (int s = 0; s < S; s++) {
            size_t o = (size_t)s * (n + 1); long q = pi[o + k] ? rh[o + k] : bq;
            M[s] = step(X + o, D + o, M[s], k, q);
            if (X[o + k]) { s1v += D[o + k]; c1++; } else { s0v += D[o + k]; c0++; }
        }
        md1[k] = s1v / S; md0[k] = s0v / S;
        if (k >= 1) { long p = k; if (md1[p] > md1[b1]) b1 = p; if (md0[p] > md0[b0]) b0 = p; }
    }
    double tr = 0; for (int s = 0; s < S; s++) { int mx = 0; for (long i = 0; i <= n; i++) if (D[(size_t)s * (n + 1) + i] > mx) mx = D[(size_t)s * (n + 1) + i]; tr += mx; }
    // fresh test
    seed(atoll(argv[6]) + 7777);
    long *Jt = calloc(n + 1, sizeof *Jt); unsigned char *x = malloc(n + 1); int *d = malloc((n + 1) * sizeof(int));
    double sm = 0; int mxx = 0;
    for (int t = 0; t < T; t++) {
        Jt[1] = 0; for (long i = 2; i <= n; i++) Jt[i] = U() < eps ? below(i) : J[i];
        x[0] = 1; d[0] = 0; int m = 0, mx = 0;
        for (long i = 1; i <= n; i++) { m = step(x, d, m, i, Jt[i]); if (d[i] > mx) mx = d[i]; }
        sm += mx; if (mx > mxx) mxx = mx;
    }
    printf("greedy-%s n=2^%d eps=%.2f train=%.1f test-mean=%.1f test-max=%d\n", argv[1], (int)lround(log2((double)n)), eps, tr / S, sm / T, mxx);
    return 0;
}
