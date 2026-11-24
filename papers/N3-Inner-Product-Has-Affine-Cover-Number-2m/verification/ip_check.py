# Largest affine subspace inside the graph H_m of inner product, m = 1, 2, 3 (closure search).
import itertools
def check(m):
    n=2*m+1
    def ip(a,b): return bin(a&b).count('1')&1
    H=set()
    for a in range(1<<m):
        for b in range(1<<m):
            H.add(a|(b<<m)|(ip(a,b)<<(2*m)))
    best=1
    # grow affine subspaces p0 + span(W) greedily over all choices (DFS with canonical direction sets)
    Hl=sorted(H)
    def span_ok(p0,W):
        pts={p0}
        for w in W:
            pts|={p^w for p in pts}
        return pts if pts<=H else None
    def dfs(p0,W,pts):
        nonlocal best
        best=max(best,len(pts))
        for q in Hl:
            w=q^p0
            if w==0 or (q in pts): continue
            if W and w< max(W): continue
            P=span_ok(p0,W+[w])
            if P is not None: dfs(p0,W+[w],P)
    for p0 in Hl: dfs(p0,[],{p0})
    return best, len(H)
for m in (1,2,3):
    b,h=check(m); print("m=%d: |H|=%d, largest affine subspace inside H: %d (2^m=%d), cover lower bound %d"%(m,h,b,2**m,h//b))
