# Verification scripts

| Script | Source preprint | What it checks |
|---|---|---|
| `check_semisort.py` | Stable Semisort Is Exactly as Hard as Padded Sorting | Theorem 3.1 against an adversarial unstable semisort and random padded layouts (2000 trials); every reduction of Theorem 4.1 against a reference stable sort (3000 trials); Lemma 6.2 by computing PAE directly (3000 trials); the formula of Proposition 7.1 exactly for $`f\le 11`$ and the identity $`\mathcal E=\sum R_{g,r}`$; a Monte Carlo run for Theorem 7.2; Theorem 7.3 exhaustively for $`f\le12`$, $`k\le5`$. |

Run: `python3 verification/check_semisort.py` (Python 3, standard library only; about 2.5 s).

Output of the run on 24 November 2026 (the labels use the section numbers of the internal source notes: "Thm 3.3" is Theorem 3.1, "K.1" Theorem 4.1, "M.1" Lemma 6.2, "N.1" Proposition 7.1/Theorem 7.2, "N.2" Theorem 7.3 of the paper):

```
Thm 3.3 closure: 2000 adversarial trials OK
K.1 reductions (IS<-SS, IS<-CPR, IS<-DS, CPR<-IS, DS<-IS): 3000 trials OK
M.1 PAE = collision energy: 3000 trials OK
N.1 E[energy] = f - 2 + 2^(1-f) exactly for f <= 11: OK
N.1 energy = sum of capped zero-runs: OK
N.1 Monte Carlo: max E/n over 200 runs = 1.203 (< 3)
N.2 E >= (f^2/(k+1) - f)/2: exhaustive for f <= 12, k <= 5 OK
```
