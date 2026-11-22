// Round-based evaluator, decision-diagram variant (NOTE.md §5j). As engine.c, but each position's
// expression x_i = f_i(earlier positions) is a reduced ordered BDD (variable order: larger positions
// on top) limited to S internal nodes and VMAX distinct variables, instead of a truth table over at
// most K variables. A BDD can represent, for example, a majority of many copies with few nodes, so
// this family can follow some wide but structured circuits that truth tables cannot.
// Each round, every position restricts by known variables and substitutes for some unknown variables
// v their previous-round expressions (f := ITE(f_v, f|v=1, f|v=0)), keeping the result if it fits.
// For node limit S, a round costs poly(S) work and depth per position.
// usage: ./engine_bdd S VMAX ORDER MAXSUB SEED CAPFACTOR file.bin ...
//   ORDER: 0 latest first, 1 earliest first, 2 random, 4 anchored doubling (round t substitutes all
//   variables >= floor(i/2^t)*2^t). Output per file as engine.c:
//   file n rounds finished stuck known_frac mean_nodes_unknown errors
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

typedef struct { int var, lo, hi; } Node;            // ids: 0 = false, 1 = true, k >= 2 = nodes[k-2]
typedef struct { int nn; Node *nodes; } Bdd;         // nodes in post-order; root id = nn + 1 (or 0/1 if nn = 0)

static int S, VMAX, ORDER, MAXSUB;
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

// ---- temporary pool with hash-consing and an ITE memo ----
#define PCAP (1 << 15)
#define HSZ (1 << 16)
static Node pool[PCAP]; static int pn, plim;         // pool ids: 0,1 terminals; k >= 2 -> pool[k]; plim: per-operation cap
static int uniq[HSZ]; static int uniq_stamp[HSZ]; static int stamp;
typedef struct { int f, g, h, r, st; } Memo;
static Memo memo[HSZ];
static int overflow;

static void pool_reset(void) { pn = 2; stamp++; overflow = 0; plim = PCAP - 1; }
static inline int pvar(int id) { return id < 2 ? -1 : pool[id].var; }
static int mk(int var, int lo, int hi) {
    if (lo == hi) return lo;
    uint32_t h = (uint32_t)(var * 2654435761u ^ lo * 40503u ^ hi * 2246822519u) & (HSZ - 1);
    while (uniq_stamp[h] == stamp) {
        int id = uniq[h];
        if (pool[id].var == var && pool[id].lo == lo && pool[id].hi == hi) return id;
        h = (h + 1) & (HSZ - 1);
    }
    if (pn >= plim) { overflow = 1; return 0; }
    pool[pn].var = var; pool[pn].lo = lo; pool[pn].hi = hi;
    uniq_stamp[h] = stamp; uniq[h] = pn;
    return pn++;
}
// load a stored BDD into the pool, replacing variable sv by constant sc (sv = -1: none)
static int load(const Bdd *b, int sv, int sc) {
    if (b->nn == 0) return b->nodes ? 0 : 0;          // unused path; constants handled by caller
    int *map = malloc((b->nn + 2) * sizeof(int)); map[0] = 0; map[1] = 1;
    for (int k = 0; k < b->nn; k++) {
        const Node *nd = &b->nodes[k];
        int lo = map[nd->lo], hi = map[nd->hi];
        map[k + 2] = nd->var == sv ? (sc ? hi : lo) : mk(nd->var, lo, hi);
        if (overflow) { free(map); return 0; }
    }
    int r = map[b->nn + 1]; free(map); return r;
}
static int ite(int f, int g, int h) {
    if (overflow) return 0;
    if (f == 1) return g;
    if (f == 0) return h;
    if (g == h) return g;
    if (g == 1 && h == 0) return f;
    uint32_t key = (uint32_t)(f * 73856093u ^ g * 19349663u ^ h * 83492791u) & (HSZ - 1);
    for (uint32_t k = key, c = 0; c < 16; c++, k = (k + 1) & (HSZ - 1)) {
        if (memo[k].st != stamp) break;
        if (memo[k].f == f && memo[k].g == g && memo[k].h == h) return memo[k].r;
    }
    int x = pvar(f); if (pvar(g) > x) x = pvar(g); if (pvar(h) > x) x = pvar(h);
    int f1 = pvar(f) == x ? pool[f].hi : f, f0 = pvar(f) == x ? pool[f].lo : f;
    int g1 = pvar(g) == x ? pool[g].hi : g, g0 = pvar(g) == x ? pool[g].lo : g;
    int h1 = pvar(h) == x ? pool[h].hi : h, h0 = pvar(h) == x ? pool[h].lo : h;
    int r1 = ite(f1, g1, h1), r0 = ite(f0, g0, h0);
    int r = mk(x, r0, r1);
    for (uint32_t k = key, c = 0; c < 16; c++, k = (k + 1) & (HSZ - 1))
        if (memo[k].st != stamp) { memo[k].f = f; memo[k].g = g; memo[k].h = h; memo[k].r = r; memo[k].st = stamp; break; }
    return r;
}
// extract the pool BDD at root into a compact stored BDD; returns 0 if over the limits
static int *mapx; static int *seenx; static int seen_stamp; static Node *outn; static int outc;
static int vars_list[4096]; static int nvars;
static int extract_rec(int id) {
    if (id < 2) return id;
    if (seenx[id] == seen_stamp) return mapx[id];
    int lo = extract_rec(pool[id].lo), hi = extract_rec(pool[id].hi);
    if (outc < 0) return 0;
    if (outc >= S) { outc = -1; return 0; }
    outn[outc].var = pool[id].var; outn[outc].lo = lo; outn[outc].hi = hi;
    seenx[id] = seen_stamp; mapx[id] = outc + 2; outc++;
    return outc + 1;
}
static int extract(int root, Bdd *out) {
    if (root < 2) { out->nn = 0; out->nodes = NULL; return root + 2; }   // returns 2 + constant for constants
    seen_stamp++; outc = 0; outn = malloc(S * sizeof(Node));
    extract_rec(root);
    if (outc < 0) { free(outn); return -1; }
    // support size
    nvars = 0;
    for (int k = 0; k < outc; k++) {
        int v = outn[k].var, dup = 0;
        for (int q = 0; q < nvars; q++) if (vars_list[q] == v) { dup = 1; break; }
        if (!dup) { if (nvars >= VMAX) { free(outn); return -1; } vars_list[nvars++] = v; }
    }
    out->nn = outc; out->nodes = realloc(outn, outc * sizeof(Node));
    return 1;
}

// stored expression with explicit constant flag
typedef struct { Bdd b; int c; } Ex;                 // c = 0/1: constant; c = -1: BDD b
static int ex_load(const Ex *e, int sv, int sc) { return e->c >= 0 ? e->c : load(&e->b, sv, sc); }
static void ex_free(Ex *e) { if (e->c < 0) free(e->b.nodes); e->b.nodes = NULL; }
static int ex_from_pool(int root, Ex *out) {
    Bdd b; int r = extract(root, &b);
    if (r < 0) return 0;
    if (r >= 2) { out->c = r - 2; out->b.nn = 0; out->b.nodes = NULL; }
    else { out->c = -1; out->b = b; }
    return 1;
}
static int ex_support(const Ex *e, int *vs) {       // distinct variables, descending
    int n = 0;
    if (e->c >= 0) return 0;
    for (int k = 0; k < e->b.nn; k++) {
        int v = e->b.nodes[k].var, dup = 0;
        for (int q = 0; q < n; q++) if (vs[q] == v) { dup = 1; break; }
        if (!dup && n < 4096) vs[n++] = v;
    }
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) if (vs[b] > vs[a]) { int t = vs[a]; vs[a] = vs[b]; vs[b] = t; }
    return n;
}
static int ex_same(const Ex *a, const Ex *b) {
    if (a->c != b->c) return 0;
    if (a->c >= 0) return 1;
    return a->b.nn == b->b.nn && !memcmp(a->b.nodes, b->b.nodes, a->b.nn * sizeof(Node));
}
static Ex ex_copy(const Ex *a) {
    Ex r = *a;
    if (a->c < 0) { r.b.nodes = malloc(a->b.nn * sizeof(Node)); memcpy(r.b.nodes, a->b.nodes, a->b.nn * sizeof(Node)); }
    return r;
}

// failure cache: an attempt to substitute v into position i is skipped while neither changed since
// it last failed (ver[] counts changes of each position's expression); this saves time only
#define FC 32
static int *ver, *fail_v, *fail_vv, *fail_vi, *fail_ptr;
static int cached_fail(int i, int v) {
    for (int k = 0; k < FC; k++) { long q = (long)i * FC + k; if (fail_v[q] == v && fail_vv[q] == ver[v] && fail_vi[q] == ver[i]) return 1; }
    return 0;
}
static void note_fail(int i, int v) {
    long q = (long)i * FC + fail_ptr[i]; fail_ptr[i] = (fail_ptr[i] + 1) % FC;
    fail_v[q] = v; fail_vv[q] = ver[v]; fail_vi[q] = ver[i];
}

// one round for position i: restrict known variables, then substitute
static Ex step(const Ex *E0, const Ex *A, long t, int i) {
    Ex E = ex_copy(E0);
    int vs[4096], nv, pristine = 1;                  // pristine: E is still the round-start expression
    // restrict known variables (repeat until none)
    for (int again = 1; again && E.c < 0;) {
        again = 0; nv = ex_support(&E, vs);
        for (int q = 0; q < nv; q++) if (A[vs[q]].c >= 0) {
            pool_reset(); int r = load(&E.b, vs[q], A[vs[q]].c);
            Ex N; if (!overflow && ex_from_pool(r, &N)) { ex_free(&E); E = N; again = 1; pristine = 0; }
            break;
        }
    }
    if (E.c >= 0) return E;
    nv = ex_support(&E, vs);
    long anchor = 0;
    if (ORDER == 4 && t < 62) anchor = ((long)i >> t) << t;
    int cand[4096], nc = 0;
    for (int q = 0; q < nv; q++) if (vs[q] >= anchor) cand[nc++] = vs[q];
    if (ORDER == 1) for (int a = 0, b = nc - 1; a < b; a++, b--) { int tt = cand[a]; cand[a] = cand[b]; cand[b] = tt; }
    if (ORDER == 2) for (int a = nc - 1; a > 0; a--) { int b = rnd() % (a + 1); int tt = cand[a]; cand[a] = cand[b]; cand[b] = tt; }
    int subs = 0;
    for (int c = 0; c < nc && E.c < 0; c++) {
        if (MAXSUB && subs >= MAXSUB && ORDER != 4) break;
        int v = cand[c];
        if (A[v].c >= 0) continue;
        if (pristine && cached_fail(i, v)) continue;
        pool_reset();
        int e1 = load(&E.b, v, 1), e0 = overflow ? 0 : load(&E.b, v, 0);
        int f = overflow ? 0 : ex_load(&A[v], -1, 0);
        plim = pn + 4 * S + 16;                      // a result of at most S nodes rarely needs more
        if (plim > PCAP - 1) plim = PCAP - 1;
        int r = overflow ? 0 : ite(f, e1, e0);
        if (overflow) { if (pristine) note_fail(i, v); continue; }
        Ex N; if (!ex_from_pool(r, &N)) { if (pristine) note_fail(i, v); continue; }
        ex_free(&E); E = N; subs++; pristine = 0;
    }
    return E;
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: see header\n"); return 1; }
    S = atoi(argv[1]); VMAX = atoi(argv[2]); ORDER = atoi(argv[3]); MAXSUB = atoi(argv[4]);
    uint64_t seed = strtoull(argv[5], 0, 10); double capf = atof(argv[6]);
    for (int fidx = 7; fidx < argc; fidx++) {
        FILE *fh = fopen(argv[fidx], "rb"); if (!fh) { perror(argv[fidx]); return 1; }
        int n; if (fread(&n, 4, 1, fh) != 1) return 1;
        int *j = malloc((n + 1) * sizeof(int)); j[0] = 0;
        if (fread(j + 1, 4, n, fh) != (size_t)n) return 1; fclose(fh);
        char *x = malloc(n + 1); x[0] = 1;
        for (int i = 1; i <= n; i++) x[i] = (x[i - 1] == 0 && x[j[i]] == 0);
        rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0x2545F4914F6CDD1DULL) ^ (uint64_t)n; if (!rs) rs = 1;
        mapx = calloc(PCAP, sizeof(int)); seenx = calloc(PCAP, sizeof(int));
        Ex *A = calloc(n + 1, sizeof(Ex)), *Bf = calloc(n + 1, sizeof(Ex));
        ver = calloc(n + 1, sizeof(int)); fail_ptr = calloc(n + 1, sizeof(int));
        fail_v = malloc((size_t)(n + 1) * FC * sizeof(int)); fail_vv = malloc((size_t)(n + 1) * FC * sizeof(int));
        fail_vi = malloc((size_t)(n + 1) * FC * sizeof(int));
        for (long q = 0; q < (long)(n + 1) * FC; q++) fail_v[q] = -1;
        A[0].c = 1;
        for (int i = 1; i <= n; i++) {                 // NOR(x_{i-1}, x_{j_i}) or NOT x_{i-1}
            pool_reset();
            int a = mk(i - 1, 1, 0);                     // !x_{i-1}
            int r = j[i] == i - 1 ? a : mk(i - 1, mk(j[i], 1, 0), 0);
            ex_from_pool(r, &A[i]);
        }
        long cap = (long)ceil(capf * log2((double)n) * log2((double)n)), t;
        int fin = 0, stuck = 0;
        for (t = 1; t <= cap; t++) {
            int changed = 0, allk = 1;
            for (int i = 0; i <= n; i++) {
                if (A[i].c >= 0) { Bf[i] = A[i]; continue; }
                Bf[i] = step(&A[i], A, t, i);
                if (!ex_same(&Bf[i], &A[i])) changed = 1;
                if (Bf[i].c < 0) allk = 0;
            }
            for (int i = 0; i <= n; i++) if (!ex_same(&Bf[i], &A[i])) ver[i]++;
            for (int i = 0; i <= n; i++) if (A[i].c < 0) ex_free(&A[i]);   // constants were shared by value
            Ex *tmp = A; A = Bf; Bf = tmp;
            if (allk) { fin = 1; break; }
            if (!changed) { stuck = 1; break; }
        }
        long known = 0, err = 0, unk = 0; double nodes = 0;
        for (int i = 0; i <= n; i++) {
            if (A[i].c >= 0) { known++; if (A[i].c != x[i]) err++; }
            else { unk++; nodes += A[i].b.nn; }
        }
        printf("%s %d %ld %d %d %.5f %.3f %ld\n", argv[fidx], n, t > cap ? cap : t, fin, stuck,
               (double)known / (n + 1), unk ? nodes / unk : 0.0, err);
        fflush(stdout);
        for (int i = 0; i <= n; i++) if (A[i].c < 0) ex_free(&A[i]);
        free(A); free(Bf); free(mapx); free(seenx); free(j); free(x);
        free(ver); free(fail_ptr); free(fail_v); free(fail_vv); free(fail_vi);
    }
    return 0;
}
