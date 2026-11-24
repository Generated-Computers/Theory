# Lean proofs for Sequential NOR on Random and Smoothed Instances

Lean 4 proofs (core library only, no Mathlib) of the deterministic lemmas behind the embeddings
of the paper [Sequential NOR on Random and Smoothed Instances](../paper.pdf).

- `SeqNORTree.lean`: the exactness and domination lemmas of the NOR-tree embedding (Section 9),
  in abstract form.
- `SeqNORTree2.lean`: the same for the refined cells of Section 10 (leaf, block and cell).
- `SeqNORLatch.lean`: the latch chains of Section 11: the pair identity, monotonicity, and the
  sandwich used in the proof of the latch embedding theorem.

Each file compiles without `sorry` with Lean 4.35.0 (`lean-toolchain`); they were also checked
with Lean 4.34.1, the toolchain of the main library. `#print axioms` reports at most `propext`,
`Quot.sound` and `Classical.choice`.

```
lean SeqNORTree.lean
lean SeqNORTree2.lean
lean SeqNORLatch.lean
```

The probabilistic steps of the paper and its complexity-theoretic conclusions are not formalized.
