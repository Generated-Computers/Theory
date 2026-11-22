# [Sequential NOR Has Exactly Fibonacci-Many Traces](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Sequential-NOR-Has-Exactly-Fibonacci-Many-Traces-November-3-2026,
  author = {{Generated Computers}},
  title = {{Sequential NOR Has Exactly Fibonacci-Many Traces}},
  howpublished = {Generated Computers preprint, manuscript 009d},
  year = {2026}
}
```


## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/009.md`](../../lean/docs/009.md), and the main statements are in the Comparator challenge [`FibonacciManyTraces.lean`](../../lean/ComparatorChallenges/FibonacciManyTraces.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**Sequential NOR has exactly Fibonacci-many traces (009d).** The census theorem (Theorem 2.1) is
formalized in full with the paper's definitions: a word `(x_0, …, x_N)` is a trace iff `x_0 = 1`,
`x_1 = 0` and there are no two adjacent ones (`census_mem_iff`), and the set of traces of length
`N`, over all `N!` legal parent arrays, has exactly `F_{N+1}` elements (`census_card`, with
Mathlib's `Nat.fib`; the statement also holds for `N = 0`). The fibre theorem (Theorem 2.2) is
formalized in full: the fibre of a trace is the product `∏ A_i(x)` (`fibre_eq_piFinset`), the
factor sizes are as stated (`card_A`), every factor is nonempty, and `∑_x ∏_i c_i(x) = N!`
(`sum_prod_card_A`). Causal projection (Lemma 3.1) and the three counting inequalities of
Corollary 3.2 (`|𝓜| ≤ 2^{|D ∩ D_Tr|}`, `|𝓜| ≤ ∏_{i∈D} k_i`, `|𝓜| ≤ F_{N+1}`) are formalized.
Of the list-decoding results only the deterministic case of Theorem 4.2 (`δ = 0`, `B = L`) is
formalized, as an upper bound and an attaining construction, together with the identity
`∑_{n=1}^M F_{n+1} = F_{M+3} - 2`. Randomized decoders (Lemma 4.1, Theorems 4.2 and 5.4 for
`δ > 0`), the adaptive-query capacity `K_{N,q}` (Lemma 5.1, Theorem 5.2, Corollary 5.3), the
spectrum sandwich (Theorem 6.1, Corollary 6.2), Proposition 4.3, the bound `N ≥ h / log₂ φ` and
the potential-function remark are not formalized.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #10 Unrestricted Frontier Report V121 (`SEQNOR_UNRESTRICTED_FRONTIER_REPORT_V121_2026_09_04.pdf`),
  Section 7 (Theorems 7.1–7.2, "V109"), Sections 10–15 (Theorems 10.1, 11.1–11.3, 12.1–12.4,
  13.1–13.4, 14.1–14.2, 15.2, Corollary 15.3; "V111"–"V119"), and Section 4 ("V105"); pp. 7–21.
- #12 Weighted Portfolio Closure V122 (`WEIGHTED_PORTFOLIO_CLOSURE_V122.pdf`), Lemmas 3.2, 4.2 and
  Theorem 5.1.
- #05 30-Page Most Important Results (`SEQNOR_30_PAGE_MOST_IMPORTANT_RESULTS_2026_09_07.pdf`),
  Sections 6.1–6.2 ("V122", "V148"), pp. 15–17.
- Check script: `verification/census_query_checks.py` (census, fibre formula and K_{N,q} for N ≤ 8 by
  enumerating all N! parent arrays; the sandwich of Theorem 6.1 for N ≤ 8).

## Status

- Proved in full: the census F_{N+1}, the product structure of trace fibres, causal projection and
  its charges, the exact list-decoding capacities (one length, lengths up to M, used-length
  tradeoff, average success), the capacity with q adaptive queries K_{N,q}, the fractional-cover
  identity and sandwich for randomized query policies, and the spectrum sandwich
  (1 − 3q(q+1)/N) F_{N+1} N^q ≤ K_{N,q} ≤ F_{N+1}(N)_q with its asymptotic corollaries. The source
  gives only sketches for several of these; the proofs here are complete (the lower bound of the
  sandwich uses the source's block-injection idea with an explicit coupling).
- Left out: the numerical separation of #10 Theorem 14.3 (capacities (1,3,5,4,4) at N = 4), which
  was not re-verified; the exact top-profile recurrence of Theorem 15.1 (an enumerator) and the
  generating-function asymptotics of Corollary 15.3; the V107/V108/V110/V113 constructions of #10
  (not assigned).
- The potential-function closures (V105, V122, V148) are presented only as a remark: they construct
  no wave, and a wave with the stated properties on all inputs would itself place Sequential NOR in
  NC, so they reformulate the open problem. The V148 contraction cannot be iterated (table size
  squares), as the source notes.
- None of the results is a circuit lower bound. Self-scores (8.2/10 etc.) and "accepted" labels are
  dropped.

Not refereed. No human referee has checked it yet; the proofs were developed with the assistance
of an AI system.
