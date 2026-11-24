# Verification scripts

| Script | Source preprint | What it checks |
|---|---|---|
| `ip_check.py` | Inner Product Has Affine-Cover Number 2ᵐ | For $`m=1,2,3`$, enumerates all affine subspaces of $`\mathbb F_2^{2m+1}`$ contained in $`H_m=\{(a,b,a\cdot b)\}`$ (depth-first search over canonical direction sets) and reports the largest; it has $`2^m`$ points, so covering $`H_m`$ needs at least $`2^m`$ pieces (Theorem 4.1). |

Run: `python3 verification/ip_check.py` (Python 3, standard library only; about 9 s).

Output of the run on 24 November 2026:

```
m=1: |H|=4, largest affine subspace inside H: 2 (2^m=2), cover lower bound 2
m=2: |H|=16, largest affine subspace inside H: 4 (2^m=4), cover lower bound 4
m=3: |H|=64, largest affine subspace inside H: 8 (2^m=8), cover lower bound 8
```
