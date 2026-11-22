import GC.Computability.SeqNORNormalForms.BinaryCore
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# 006g: depth deletion is long-path hitting; the path formula

For a finite digraph `D = (V, Adj)` (a DAG in the paper), a directed path is a list of
vertices with consecutive arcs (`List.IsChain Adj`), and `depth(D - X) ≤ M` means that every
directed path avoiding `X` has at most `M` vertices. `δ_M(D)` is the least size of such an
`X`.
-/

namespace GC.SeqNORNormalForms

/-- `depth(D - X) ≤ M`. -/
def DepthLE {V : Type*} (Adj : V → V → Prop) (X : Finset V) (M : ℕ) : Prop :=
  ∀ p : List V, p.IsChain Adj → (∀ v ∈ p, v ∉ X) → p.length ≤ M

/-- `δ_M(D) = min {|X| : depth(D - X) ≤ M}`. -/
noncomputable def deletionNumber {V : Type*} (Adj : V → V → Prop) (M : ℕ) : ℕ :=
  sInf {k | ∃ X : Finset V, X.card = k ∧ DepthLE Adj X M}

section DAG

variable {V : Type*} [Fintype V] [DecidableEq V] (Adj : V → V → Prop)

/-- **Theorem 4.1 of 006g (path-hitting identity).** `depth(D - X) ≤ M` iff `X` meets every
directed path of `D` with exactly `M + 1` vertices. -/
theorem path_hitting (X : Finset V) (M : ℕ) :
    DepthLE Adj X M ↔ ∀ p : List V, p.IsChain Adj → p.length = M + 1 → ∃ v ∈ p, v ∈ X := by
  constructor
  · intro h p hp hl
    by_contra hne
    have hne' : ∀ v ∈ p, v ∉ X := fun v hv hvX => hne ⟨v, hv, hvX⟩
    have := h p hp hne'
    omega
  · intro h p hp hX
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨v, hv, hvX⟩ := h (p.take (M + 1)) (hp.take _) (by simp; omega)
    exact hX v (List.mem_of_mem_take hv) hvX

theorem depthLE_univ (M : ℕ) : DepthLE Adj (Finset.univ : Finset V) M := by
  intro p _ hX
  cases p with
  | nil => simp
  | cons v p => exact absurd (Finset.mem_univ v) (hX v (by simp))

theorem deletionNumber_le (M : ℕ) (X : Finset V) (hX : DepthLE Adj X M) :
    deletionNumber Adj M ≤ X.card :=
  Nat.sInf_le ⟨X, rfl, hX⟩

theorem deletionNumber_spec (M : ℕ) :
    ∃ X : Finset V, X.card = deletionNumber Adj M ∧ DepthLE Adj X M :=
  Nat.sInf_mem (s := {k | ∃ X : Finset V, X.card = k ∧ DepthLE Adj X M})
    ⟨_, Finset.univ, rfl, depthLE_univ Adj M⟩

/-- Every deletion set meets each of `q` pairwise disjoint `(M+1)`-vertex paths, so it has at
least `q` elements. -/
theorem packing_lower (M q : ℕ) (ps : Fin q → List V) (hc : ∀ t, (ps t).IsChain Adj)
    (hl : ∀ t, (ps t).length = M + 1) (hdisj : ∀ t t', t ≠ t' → ∀ v ∈ ps t, v ∉ ps t')
    (X : Finset V) (hX : DepthLE Adj X M) : q ≤ X.card := by
  have hhit := (path_hitting Adj X M).1 hX
  choose f hf using fun t => hhit (ps t) (hc t) (hl t)
  have hinj : Function.Injective f := by
    intro t t' h
    by_contra hne
    exact hdisj t t' hne (f t) (hf t).1 (h ▸ (hf t').1)
  have := Finset.card_le_card_of_injOn f (s := Finset.univ) (t := X)
    (fun t _ => (hf t).2) (fun a _ b _ h => hinj h)
  simpa using this

/-- **Theorem 4.3 of 006g (packing sandwich).** If `P_1, …, P_q` is a maximal family of
pairwise disjoint directed paths with `M + 1` vertices each, then
`q ≤ δ_M(D) ≤ (M+1) q`. -/
theorem packing_sandwich (M q : ℕ) (ps : Fin q → List V) (hc : ∀ t, (ps t).IsChain Adj)
    (hl : ∀ t, (ps t).length = M + 1) (hdisj : ∀ t t', t ≠ t' → ∀ v ∈ ps t, v ∉ ps t')
    (hmax : ∀ p : List V, p.IsChain Adj → p.length = M + 1 → ∃ t, ∃ v ∈ p, v ∈ ps t) :
    q ≤ deletionNumber Adj M ∧ deletionNumber Adj M ≤ (M + 1) * q := by
  constructor
  · obtain ⟨X, hX, hXd⟩ := deletionNumber_spec Adj M
    rw [← hX]
    exact packing_lower Adj M q ps hc hl hdisj X hXd
  · let X : Finset V := Finset.univ.biUnion (fun t => (ps t).toFinset)
    have hX : DepthLE Adj X M := by
      rw [path_hitting]
      intro p hp hlen
      obtain ⟨t, v, hv, hvt⟩ := hmax p hp hlen
      exact ⟨v, hv, Finset.mem_biUnion.2 ⟨t, Finset.mem_univ _, List.mem_toFinset.2 hvt⟩⟩
    refine (deletionNumber_le Adj M X hX).trans ?_
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ t : Fin q, (ps t).toFinset.card ≤ ∑ _t : Fin q, (M + 1) :=
          Finset.sum_le_sum fun t _ => (List.toFinset_card_le _).trans (hl t).le
      _ = (M + 1) * q := by simp [Nat.mul_comm]

end DAG

/-! ### The directed path `C_L` (Theorem 5.2) -/

/-- The directed path `C_L` on the vertices `0, …, L-1`. -/
def pathAdj (L : ℕ) (u v : Fin L) : Prop := v.val = u.val + 1

/-- The block path `a, a+1, …, a+len-1` in `C_L`. -/
def blockPath (L : ℕ) : (a len : ℕ) → a + len ≤ L → List (Fin L)
  | _, 0, _ => []
  | a, len + 1, h => ⟨a, by omega⟩ :: blockPath L (a + 1) len (by omega)

theorem blockPath_length (L : ℕ) : ∀ a len h, (blockPath L a len h).length = len := by
  intro a len
  induction len generalizing a with
  | zero => intro h; rfl
  | succ len ih => intro h; simp [blockPath, ih]

theorem blockPath_mem (L : ℕ) : ∀ a len h (v : Fin L),
    v ∈ blockPath L a len h ↔ a ≤ v.val ∧ v.val < a + len := by
  intro a len
  induction len generalizing a with
  | zero => intro h v; show v ∈ ([] : List (Fin L)) ↔ _; simp
  | succ len ih =>
    intro h v
    simp only [blockPath, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨h1, h2⟩) <;> (try simp) <;> omega
    · intro ⟨h1, h2⟩
      by_cases hv : v.val = a
      · left; exact Fin.ext hv
      · right; omega

theorem blockPath_chain (L : ℕ) : ∀ a len h, (blockPath L a len h).IsChain (pathAdj L) := by
  intro a len
  induction len generalizing a with
  | zero => intro h; exact List.IsChain.nil
  | succ len ih =>
    intro h
    cases len with
    | zero => exact List.IsChain.singleton _
    | succ len =>
      simp only [blockPath] at ih ⊢
      exact List.IsChain.cons_cons (by simp [pathAdj]) (ih (a + 1) (by omega))

theorem chain_vals (L : ℕ) : ∀ (p : List (Fin L)), p.IsChain (pathAdj L) →
    ∀ (k : ℕ) (hk : k < p.length), (p[k]).val = (p[0]'(by omega)).val + k := by
  intro p
  induction p with
  | nil => intro _ k hk; simp at hk
  | cons v p ih =>
    intro hp k hk
    cases k with
    | zero => simp
    | succ k =>
      cases p with
      | nil => simp at hk
      | cons w p =>
        rw [List.isChain_cons_cons] at hp
        have := ih hp.2 k (by simp at hk ⊢; omega)
        simp only [List.getElem_cons_succ, List.getElem_cons_zero] at this ⊢
        rw [this, hp.1]; omega

theorem card_multiples_lt (L p : ℕ) :
    ((Finset.range L).filter (fun e => p ∣ e + 1)).card = L / p := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.range_add_one, Finset.filter_insert, Nat.succ_div]
    by_cases h : p ∣ L + 1
    · simp only [h, ↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp), ih]
    · simp only [h, ↓reduceIte]
      rw [ih]; rfl

/-- **Theorem 5.2 of 006g (path formula).** For the directed path `C_L` and every `M`,
`δ_M(C_L) = ⌊L / (M+1)⌋`. -/
theorem path_formula (L M : ℕ) : deletionNumber (pathAdj L) M = L / (M + 1) := by
  apply le_antisymm
  · -- upper bound: delete the vertices in positions `M+1, 2(M+1), …`
    let X : Finset (Fin L) := Finset.univ.filter (fun v => (M + 1) ∣ v.val + 1)
    have hX : DepthLE (pathAdj L) X M := by
      intro p hp hav
      by_contra hlt
      rw [not_le] at hlt
      have h0 : 0 < p.length := by omega
      set a := (p[0]'h0).val
      let k := M - a % (M + 1)
      have hk : k < p.length := by omega
      have hv := chain_vals L p hp k hk
      have hmem : p[k] ∈ X := by
        simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hv]
        have : a + k + 1 = (M + 1) * (a / (M + 1) + 1) := by
          have := Nat.div_add_mod a (M + 1)
          have : a % (M + 1) < M + 1 := Nat.mod_lt _ (by omega)
          simp only [k]
          rw [Nat.mul_add, Nat.mul_one]
          omega
        rw [this]; exact Dvd.intro _ rfl
      exact hav _ (List.getElem_mem hk) hmem
    refine (deletionNumber_le _ M X hX).trans (le_of_eq ?_)
    rw [← card_multiples_lt L (M + 1)]
    rw [← Finset.card_map Fin.valEmbedding]
    congr 1
    ext e
    simp only [X, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨v.isLt, hv⟩
    · rintro ⟨he, hd⟩; exact ⟨⟨e, he⟩, hd, rfl⟩
  · -- lower bound: `⌊L/(M+1)⌋` disjoint consecutive blocks
    obtain ⟨X, hX, hXd⟩ := deletionNumber_spec (pathAdj L) M
    rw [← hX]
    have hb : ∀ t : Fin (L / (M + 1)), t.val * (M + 1) + (M + 1) ≤ L := by
      intro t
      have h1 : (t.val + 1) * (M + 1) ≤ L / (M + 1) * (M + 1) :=
        Nat.mul_le_mul_right _ t.isLt
      have h2 := Nat.div_mul_le_self L (M + 1)
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
    exact packing_lower (pathAdj L) M (L / (M + 1))
      (fun t => blockPath L (t.val * (M + 1)) (M + 1) (hb t))
      (fun t => blockPath_chain L _ _ _) (fun t => blockPath_length L _ _ _)
      (by
        intro t t' hne v hv hv'
        rw [blockPath_mem] at hv hv'
        apply hne
        apply Fin.ext
        by_contra hne'
        rcases Nat.lt_or_gt_of_ne hne' with h | h
        · have : (t.val + 1) * (M + 1) ≤ t'.val * (M + 1) := Nat.mul_le_mul_right _ h
          rw [Nat.add_mul, Nat.one_mul] at this; omega
        · have : (t'.val + 1) * (M + 1) ≤ t.val * (M + 1) := Nat.mul_le_mul_right _ h
          rw [Nat.add_mul, Nat.one_mul] at this; omega)
      X hXd

end GC.SeqNORNormalForms
