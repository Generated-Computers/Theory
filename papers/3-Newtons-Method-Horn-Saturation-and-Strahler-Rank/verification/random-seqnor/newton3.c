// Stores every Newton iterate and reports, for each round t with f_t >= 1024 and depth l = 1..8:
//   p_l = |E_{t-l} ∩ [0, f_t)|            (pre-front mass of round t-l)
//   w_l = |E_{t-l} ∩ [f_t, 1.25 f_t)|     (window mass of round t-l)
// It also checks the witness inequality pathwise at every round r >= 1 and every position y:
//   #(S_{r-1} ∩ [1,y)) <= |E_r ∩ [0,y)| + |E_r ∩ [0,y-1)| + #{s < y : j_s ∈ E_r}
// usage: newton3 n seed      output lines: "W t f l p_l w_l"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static uint64_t s;
static uint64_t next(void) {
    uint64_t z = (s += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}
static uint32_t below(uint32_t m) { return (uint32_t)(((__uint128_t)next() * m) >> 64); }

#define MAXR 64
int main(int argc, char **argv) {
    long n = atol(argv[1]); s = strtoull(argv[2], 0, 10);
    uint32_t *j = malloc(sizeof(uint32_t) * (n + 1));
    uint8_t *xs = malloc(n + 1), *d = malloc(n + 1);
    uint8_t *X[MAXR]; long f[MAXR];
    for (long i = 1; i <= n; i++) j[i] = below((uint32_t)i);
    xs[0] = 1;
    for (long i = 1; i <= n; i++) xs[i] = !(xs[i - 1] | xs[j[i]]);
    X[0] = calloc(n + 1, 1); X[0][0] = 1;
    int R = 0;
    for (;;) {
        uint8_t *x = X[R];
        f[R] = -1;
        for (long i = 0; i <= n; i++) if (x[i] != xs[i]) { f[R] = i; break; }
        if (f[R] < 0 || R + 1 >= MAXR) break;
        d[0] = 0;
        for (long i = 1; i <= n; i++) {
            long p = i - 1, q = j[i];
            uint8_t F = x[i] ^ ((1 ^ x[p]) & (1 ^ x[q]));
            uint8_t sv = (p == q) ? d[p] : (((1 ^ x[q]) & d[p]) ^ ((1 ^ x[p]) & d[q]));
            d[i] = F ^ sv;
        }
        X[R + 1] = malloc(n + 1);
        for (long i = 0; i <= n; i++) X[R + 1][i] = x[i] ^ d[i];
        X[R + 1][0] = 1;
        R++;
    }
    // witness inequality, pathwise, every round and every prefix
    long viol = 0, checks = 0;
    for (int r = 1; r <= R; r++) {
        long src = 0, er = 0, er1 = 0, hit = 0;
        for (long y = 1; y <= n; y++) {
            long i = y;                       // extend the prefix by position i and compare
            uint8_t ei = X[r][i] ^ xs[i];
            if ((long)j[i] != i - 1 && ((X[r-1][i-1] ^ xs[i-1]) & (X[r-1][j[i]] ^ xs[j[i]]))) src++;
            if (X[r][j[i]] ^ xs[j[i]]) hit++;
            er += ei; er1 += (X[r][i-1] ^ xs[i-1]);
            checks++;
            if (src > er + er1 + hit) viol++;
        }
    }
    printf("# rounds %d witness_checks %ld violations %ld\n", R, checks, viol);
    for (int t = 1; t <= R; t++) {
        long ft = f[t]; if (ft < 1024) continue;
        long hi = (long)(1.25 * ft); if (hi > n + 1) hi = n + 1;
        for (int l = 1; l <= 8 && t - l >= 0; l++) {
            long p = 0, w = 0; uint8_t *y = X[t - l];
            for (long i = 0; i < ft; i++) p += y[i] ^ xs[i];
            for (long i = ft; i < hi; i++) w += y[i] ^ xs[i];
            printf("W %d %ld %d %ld %ld\n", t, ft, l, p, w);
        }
    }
    return 0;
}
