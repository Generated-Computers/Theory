// GF(2) Newton on random Sequential NOR: x0 = 1, x_i = NOR(x_{i-1}, x_{j_i}), j_i uniform on {0..i-1}.
// Starts from x = (1,0,...,0). Per round t prints: t f_t N_t M_t ratio
//   f_t  first wrong index of x^(t)
//   N_t  round-(t-1) sources (both parents wrong in x^(t-1)) in [f_t, 1.25 f_t)
//   M_t  wrong positions of x^(t) in [f_t, 1.25 f_t)
// usage: newton n seed
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static uint64_t s;
static uint64_t next(void) {  // splitmix64
    uint64_t z = (s += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}
static uint32_t below(uint32_t m) { return (uint32_t)(((__uint128_t)next() * m) >> 64); }

int main(int argc, char **argv) {
    long n = atol(argv[1]); s = strtoull(argv[2], 0, 10);
    uint32_t *j = malloc(sizeof(uint32_t) * (n + 1));
    uint8_t *xs = malloc(n + 1), *x = malloc(n + 1), *xp = malloc(n + 1), *d = malloc(n + 1);
    for (long i = 1; i <= n; i++) j[i] = below((uint32_t)i);
    xs[0] = 1;
    for (long i = 1; i <= n; i++) xs[i] = !(xs[i - 1] | xs[j[i]]);
    long ones = 0; for (long i = 0; i <= n; i++) ones += xs[i];
    memset(x, 0, n + 1); x[0] = 1; memcpy(xp, x, n + 1);
    long prevf = -1;
    for (int t = 0; t < 10000; t++) {
        long f = -1;
        for (long i = 0; i <= n; i++) if (x[i] != xs[i]) { f = i; break; }
        if (f < 0) { printf("# rounds %d n %ld seed %s density %.5f\n", t, n, argv[2], (double)ones / (n + 1)); break; }
        long hi = (long)(1.25 * f); if (hi > n + 1) hi = n + 1;
        long N = 0, M = 0;
        if (t > 0)
            for (long i = f; i < hi; i++) {
                long p = i - 1, q = j[i];
                if (i >= 1 && p != q && (xp[p] ^ xs[p]) && (xp[q] ^ xs[q])) N++;
            }
        for (long i = f; i < hi; i++) M += (x[i] ^ xs[i]);
        printf("%d %ld %ld %ld %.4f\n", t, f, N, M, prevf > 0 ? (double)f / prevf : 0.0);
        prevf = f;
        // Newton step: d solves (I + L(x)) d = F(x)
        d[0] = 0;
        for (long i = 1; i <= n; i++) {
            long p = i - 1, q = j[i];
            uint8_t F = x[i] ^ ((1 ^ x[p]) & (1 ^ x[q]));
            uint8_t sv = (p == q) ? d[p] : (((1 ^ x[q]) & d[p]) ^ ((1 ^ x[p]) & d[q]));
            d[i] = F ^ sv;
        }
        memcpy(xp, x, n + 1);
        for (long i = 0; i <= n; i++) x[i] ^= d[i];
        x[0] = 1;
    }
    return 0;
}
