// Exhaustive worst case of GF(2) Newton on Sequential NOR from the standard start (1,0,...,0).
// Enumerates every parent array j_1..j_n (j_i in {0..i-1}, n! arrays) and reports the maximum
// number of rounds T until the iterate equals the trace, plus one maximising array.
// usage: worstcase N        (prints one line per n = 1..N)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, j[32], best, bestj[32];
static unsigned char xs[32], x[32], d[32];

static int rounds(void) {
    xs[0] = 1;
    for (int i = 1; i <= n; i++) xs[i] = !(xs[i - 1] | xs[j[i]]);
    memset(x, 0, sizeof x); x[0] = 1;
    for (int t = 0;; t++) {
        if (!memcmp(x, xs, (size_t)n + 1)) return t;
        d[0] = 0;
        for (int i = 1; i <= n; i++) {
            int p = i - 1, q = j[i];
            unsigned char F = x[i] ^ ((1 ^ x[p]) & (1 ^ x[q]));
            unsigned char s = (p == q) ? d[p] : (((1 ^ x[q]) & d[p]) ^ ((1 ^ x[p]) & d[q]));
            d[i] = F ^ s;
        }
        for (int i = 0; i <= n; i++) x[i] ^= d[i];
        x[0] = 1;
    }
}

static void rec(int i) {
    if (i > n) {
        int r = rounds();
        if (r > best) { best = r; memcpy(bestj, j, sizeof j); }
        return;
    }
    for (int v = 0; v < i; v++) { j[i] = v; rec(i + 1); }
}

int main(int argc, char **argv) {
    int N = atoi(argv[1]);
    for (n = 1; n <= N; n++) {
        best = -1; rec(1);
        printf("n=%2d  max rounds=%2d  ceil(n/2)=%2d  example j=", n, best, (n + 1) / 2);
        for (int i = 1; i <= n; i++) printf("%d%s", bestj[i], i < n ? "," : "\n");
        fflush(stdout);
    }
    return 0;
}
