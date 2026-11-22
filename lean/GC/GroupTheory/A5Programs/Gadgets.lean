import GC.GroupTheory.A5Programs.Basic
import GC.GroupTheory.A5Programs.Prog

/-!
# Barrington gadgets: Boolean circuits inside `A₅`

With `a = (1 2 3 4 5)`, `b = (1 2 4 5 3)`, `c = (3 5 4)`, `d = (2 4 3)` (paper notation) and the
encoding `false ↦ e`, `true ↦ a`, the terms `NOT(x) = a x⁴` and
`AND(x, y) = d⁻¹ [x, c⁻¹ y c] d` (with `[x, z] = x⁻¹ z⁻¹ x z`) realize the Boolean gates.
Written with multiplications only, NOT uses 3 product gates and AND uses 13. Compiling every gate
of a Boolean circuit gives an `A₅` multiplication circuit of linear size, with sharing preserved,
whose node values encode the Boolean values (manuscripts 004a, Lemma 2.2, and 004g,
Lemma 3.2, Theorem 3.3, Corollary 3.4).
-/

namespace GC.A5Programs

open Equiv

/-- `a = (1 2 3 4 5)`. -/
def aA : Perm (Fin 5) := mk5 ![1,2,3,4,0] ![4,0,1,2,3]
/-- `b = (1 2 4 5 3)`. -/
def bA : Perm (Fin 5) := mk5 ![1,3,0,4,2] ![2,0,4,1,3]
/-- `c = (3 5 4)`. -/
def cA : Perm (Fin 5) := mk5 ![0,1,4,2,3] ![0,1,3,4,2]
/-- `d = (2 4 3)`. -/
def dA : Perm (Fin 5) := mk5 ![0,3,1,2,4] ![0,2,3,1,4]
/-- `(1 4 2 3 5)`. -/
def abComm : Perm (Fin 5) := mk5 ![3,2,4,1,0] ![4,3,1,0,2]

/-- The commutator convention of the papers, `[x, y] = x⁻¹ y⁻¹ x y`. -/
def pcomm (x y : Perm (Fin 5)) : Perm (Fin 5) := x⁻¹ * y⁻¹ * x * y

/-- 004g, Lemma 3.2: the gadget elements are even and satisfy
`c⁻¹ a c = b`, `[a, b] = (1 4 2 3 5)` and `d⁻¹ [a, b] d = a`. -/
theorem gadget_identities :
    (aA ∈ alternatingGroup (Fin 5) ∧ bA ∈ alternatingGroup (Fin 5) ∧
      cA ∈ alternatingGroup (Fin 5) ∧ dA ∈ alternatingGroup (Fin 5)) ∧
    cA⁻¹ * aA * cA = bA ∧ pcomm aA bA = abComm ∧ dA⁻¹ * pcomm aA bA * dA = aA := by
  simp only [Perm.mem_alternatingGroup]
  decide

/-- Encoding of Boolean values: `false ↦ e`, `true ↦ a`. -/
def enc : Bool → Perm (Fin 5)
  | false => 1
  | true => aA

/-- The NOT gadget `a x⁴`. -/
def notGadget (x : Perm (Fin 5)) : Perm (Fin 5) := aA * x ^ 4
/-- The AND gadget `d⁻¹ [x, c⁻¹ y c] d`. -/
def andGadget (x y : Perm (Fin 5)) : Perm (Fin 5) := dA⁻¹ * pcomm x (cA⁻¹ * y * cA) * dA

/-- 004g, Theorem 3.3 (and 004a, Lemma 2.2): the gadgets compute NOT and AND on encodings, and
the multiplication-only form of AND, `d⁻¹ x⁴ (c⁻¹ y⁴ c) x (c⁻¹ y c) d`, agrees with it. -/
theorem gadgets_correct (u v : Bool) :
    notGadget (enc u) = enc (!u) ∧ andGadget (enc u) (enc v) = enc (u && v) ∧
    dA⁻¹ * enc u ^ 4 * (cA⁻¹ * enc v ^ 4 * cA) * enc u * (cA⁻¹ * enc v * cA) * dA =
      enc (u && v) := by
  revert u v; decide

/-! ## Boolean circuits -/

/-- A gate of a Boolean circuit: a constant, or NOT / AND of earlier nodes. -/
inductive BOp where
  | const : Bool → BOp
  | not : ℕ → BOp
  | and : ℕ → ℕ → BOp
  deriving DecidableEq, Repr

def BOp.step (vals : List Bool) : BOp → Bool
  | .const b => b
  | .not i => !(vals.getD i false)
  | .and i j => vals.getD i false && vals.getD j false

/-- Values of all nodes of a Boolean circuit. -/
def evalBool (bs : List BOp) : List Bool :=
  bs.foldl (fun vals b => vals ++ [b.step vals]) []

/-- The value of Boolean node `k`. -/
def bval (bs : List BOp) (k : ℕ) : Bool := (evalBool bs).getD k false

def BOp.WF (k : ℕ) : BOp → Prop
  | .const _ => True
  | .not i => i < k
  | .and i j => i < k ∧ j < k

/-- Every gate reads earlier nodes only. -/
def BWellFormed (bs : List BOp) : Prop := ∀ k (h : k < bs.length), (bs[k]'h).WF k

theorem evalBool_append_single (bs : List BOp) (b : BOp) :
    evalBool (bs ++ [b]) = evalBool bs ++ [b.step (evalBool bs)] := by
  simp [evalBool, List.foldl_append]

@[simp] theorem length_evalBool (bs : List BOp) : (evalBool bs).length = bs.length := by
  induction bs using List.reverseRecOn with
  | nil => rfl
  | append_singleton bs b ih => simp [evalBool_append_single, ih]

theorem bval_snoc (bs : List BOp) (b : BOp) (k : ℕ) :
    bval (bs ++ [b]) k =
      if k < bs.length then bval bs k
      else if k = bs.length then
        (match b with
          | .const v => v
          | .not i => !(bval bs i)
          | .and i j => bval bs i && bval bs j)
      else false := by
  unfold bval
  rw [evalBool_append_single]
  split_ifs with h1 h2
  · rw [List.getD_append _ _ _ _ (by simpa using h1)]
  · subst h2
    rw [List.getD_append_right _ _ _ _ (by simp)]
    cases b <;> simp [BOp.step, bval]
  · rw [List.getD_eq_default]; simp; omega

theorem bWellFormed_append_single (bs : List BOp) (b : BOp) :
    BWellFormed (bs ++ [b]) ↔ BWellFormed bs ∧ b.WF bs.length := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, ?_⟩
    · have := h k (by simp; omega)
      rwa [List.getElem_append_left hk] at this
    · have := h bs.length (by simp)
      simpa using this
  · rintro ⟨h1, h2⟩ k hk
    simp at hk
    rcases Nat.lt_or_ge k bs.length with hk' | hk'
    · rw [List.getElem_append_left hk']; exact h1 k hk'
    · have : k = bs.length := by omega
      subst this; simpa using h2

/-! ## Compilation -/

/-- The NOT block for an operand at node `m`, appended at position `L`:
`L: a`, `L+1: x²`, `L+2: x⁴`, `L+3: a·x⁴`. -/
def notBlock (L m : ℕ) : List (Op (Perm (Fin 5))) :=
  [.leaf aA, .mul m m, .mul (L+1) (L+1), .mul L (L+2)]

/-- The AND block for operands at nodes `i, j`, appended at position `L`: four constants and
13 product gates computing `d⁻¹ x⁴ (c⁻¹ y⁴ c) x (c⁻¹ y c) d`. -/
def andBlock (L i j : ℕ) : List (Op (Perm (Fin 5))) :=
  [.leaf dA⁻¹, .leaf cA⁻¹, .leaf cA, .leaf dA,
   .mul i i, .mul (L+4) (L+4),
   .mul j j, .mul (L+6) (L+6),
   .mul (L+1) (L+7), .mul (L+8) (L+2),
   .mul (L+1) j, .mul (L+10) (L+2),
   .mul L (L+5), .mul (L+12) (L+9), .mul (L+13) i, .mul (L+14) (L+11), .mul (L+15) (L+3)]

/-- One compilation step: the program so far and the node index of every Boolean node. -/
def compileStep (st : List (Op (Perm (Fin 5))) × List ℕ) (b : BOp) :
    List (Op (Perm (Fin 5))) × List ℕ :=
  match b with
  | .const v => (st.1 ++ [.leaf (enc v)], st.2 ++ [st.1.length])
  | .not i => (st.1 ++ notBlock st.1.length (st.2.getD i 0), st.2 ++ [st.1.length + 3])
  | .and i j => (st.1 ++ andBlock st.1.length (st.2.getD i 0) (st.2.getD j 0),
      st.2 ++ [st.1.length + 16])

/-- The `A₅` multiplication circuit of a Boolean circuit, with the node map. -/
def compile (bs : List BOp) : List (Op (Perm (Fin 5))) × List ℕ :=
  bs.foldl compileStep ([], [])

theorem compile_append_single (bs : List BOp) (b : BOp) :
    compile (bs ++ [b]) = compileStep (compile bs) b := by
  simp [compile, List.foldl_append]

/-- A multiplication circuit with constants in `A₅`: no inverse gates, every constant even. -/
def IsMulCircuit (ops : List (Op (Perm (Fin 5)))) : Prop :=
  ∀ op ∈ ops, match op with
    | .leaf g => g ∈ alternatingGroup (Fin 5)
    | .mul _ _ => True
    | .inv _ => False

theorem notBlock_val (ops : List (Op (Perm (Fin 5)))) (m : ℕ) (hm : m < ops.length) :
    val id (ops ++ notBlock ops.length m) (ops.length + 3) =
      aA * (val id ops m * val id ops m * (val id ops m * val id ops m)) := by
  rw [val_append_block]
  simp [notBlock, evalBlock, blockStep, blockLook, hm]

theorem andBlock_val (ops : List (Op (Perm (Fin 5)))) (i j : ℕ) (hi : i < ops.length)
    (hj : j < ops.length) :
    val id (ops ++ andBlock ops.length i j) (ops.length + 16) =
      dA⁻¹ * (val id ops i * val id ops i * (val id ops i * val id ops i)) *
        (cA⁻¹ * (val id ops j * val id ops j * (val id ops j * val id ops j)) * cA) *
        val id ops i * (cA⁻¹ * val id ops j * cA) * dA := by
  rw [val_append_block]
  simp [andBlock, evalBlock, blockStep, blockLook, hi, hj, mul_assoc]

theorem enc_mem (u : Bool) : enc u ∈ alternatingGroup (Fin 5) := by
  cases u
  · exact Subgroup.one_mem _
  · exact gadget_identities.1.1

/-- The compilation invariant. -/
theorem compile_spec (bs : List BOp) (hwf : BWellFormed bs) :
    (compile bs).2.length = bs.length ∧
    (∀ k < bs.length, (compile bs).2.getD k 0 < (compile bs).1.length ∧
        val id (compile bs).1 ((compile bs).2.getD k 0) = enc (bval bs k)) ∧
    (compile bs).1.length ≤ 17 * bs.length ∧
    IsMulCircuit (compile bs).1 ∧ WellFormed (compile bs).1 := by
  induction bs using List.reverseRecOn with
  | nil => simp [compile, IsMulCircuit]
  | append_singleton bs b ih =>
    rw [bWellFormed_append_single] at hwf
    obtain ⟨hlen, hval, hsize, hmul, hwfC⟩ := ih hwf.1
    rw [compile_append_single]
    generalize hC : compile bs = C at *
    obtain ⟨ops, idx⟩ := C
    simp only at hlen hval hsize hmul hwfC ⊢
    -- operand facts
    have hop : ∀ i < bs.length, idx.getD i 0 < ops.length ∧
        val id ops (idx.getD i 0) = enc (bval bs i) := hval
    have hold : ∀ (blk : List (Op (Perm (Fin 5)))) (newIdx : ℕ),
        ∀ k < bs.length, (idx ++ [newIdx]).getD k 0 < (ops ++ blk).length ∧
          val id (ops ++ blk) ((idx ++ [newIdx]).getD k 0) = enc (bval (bs ++ [b]) k) := by
      intro blk newIdx k hk
      have hk' : k < idx.length := by omega
      rw [List.getD_append _ _ _ _ hk', bval_snoc, if_pos hk]
      refine ⟨by rw [List.length_append]; have := (hop k hk).1; omega, ?_⟩
      rw [val_append_of_lt _ _ _ (hop k hk).1]
      exact (hop k hk).2
    have hnew : ∀ (newIdx : ℕ), (idx ++ [newIdx]).getD bs.length 0 = newIdx := by
      intro newIdx; rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hlen]
    cases b with
    | const v =>
      refine ⟨by simp [compileStep, hlen], ?_, ?_, ?_, ?_⟩
      · intro k hk
        simp only [List.length_append, List.length_singleton] at hk
        rcases Nat.lt_or_ge k bs.length with hk' | hk'
        · exact hold _ _ k hk'
        · have : k = bs.length := by omega
          subst this
          simp only [compileStep]
          rw [hnew, bval_snoc, if_neg (lt_irrefl _), if_pos rfl]
          refine ⟨by simp, ?_⟩
          rw [val_snoc, if_neg (lt_irrefl _), if_pos rfl]; rfl
      · simp [compileStep]; omega
      · intro op hop'
        simp only [compileStep, List.mem_append, List.mem_singleton] at hop'
        rcases hop' with h | rfl
        · exact hmul op h
        · exact enc_mem v
      · simp only [compileStep]
        rw [wellFormed_append_single]; exact ⟨hwfC, trivial⟩
    | not i =>
      have hi : i < bs.length := hwf.2
      obtain ⟨hil, hiv⟩ := hop i hi
      refine ⟨by simp [compileStep, hlen], ?_, ?_, ?_, ?_⟩
      · intro k hk
        simp only [List.length_append, List.length_singleton] at hk
        rcases Nat.lt_or_ge k bs.length with hk' | hk'
        · exact hold _ _ k hk'
        · have : k = bs.length := by omega
          subst this
          simp only [compileStep]
          rw [hnew, bval_snoc, if_neg (lt_irrefl _), if_pos rfl]
          refine ⟨by simp [notBlock], ?_⟩
          rw [notBlock_val _ _ hil, hiv]
          have := (gadgets_correct (bval bs i) false).1
          rw [← this, notGadget]; simp [pow_succ, pow_zero, mul_assoc]
      · simp [compileStep, notBlock]; omega
      · intro op hop'
        simp only [compileStep, List.mem_append] at hop'
        rcases hop' with h | h
        · exact hmul op h
        · simp only [notBlock, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl | rfl | rfl
          · exact gadget_identities.1.1
          all_goals trivial
      · simp only [compileStep, notBlock]
        have e : ops ++ [Op.leaf aA, Op.mul (idx.getD i 0) (idx.getD i 0),
            Op.mul (ops.length + 1) (ops.length + 1), Op.mul ops.length (ops.length + 2)] =
            ops ++ [.leaf aA] ++ [.mul (idx.getD i 0) (idx.getD i 0)] ++
            [.mul (ops.length + 1) (ops.length + 1)] ++ [.mul ops.length (ops.length + 2)] := by
          simp
        rw [e]
        simp only [wellFormed_append_single, List.length_append, List.length_singleton, Op.WF]
        refine ⟨⟨⟨⟨hwfC, trivial⟩, by omega, by omega⟩, by omega, by omega⟩, by omega, by omega⟩
    | and i j =>
      have hi : i < bs.length := hwf.2.1
      have hj : j < bs.length := hwf.2.2
      obtain ⟨hil, hiv⟩ := hop i hi
      obtain ⟨hjl, hjv⟩ := hop j hj
      refine ⟨by simp [compileStep, hlen], ?_, ?_, ?_, ?_⟩
      · intro k hk
        simp only [List.length_append, List.length_singleton] at hk
        rcases Nat.lt_or_ge k bs.length with hk' | hk'
        · exact hold _ _ k hk'
        · have : k = bs.length := by omega
          subst this
          simp only [compileStep]
          rw [hnew, bval_snoc, if_neg (lt_irrefl _), if_pos rfl]
          refine ⟨by simp [andBlock], ?_⟩
          rw [andBlock_val _ _ _ hil hjl, hiv, hjv]
          have := (gadgets_correct (bval bs i) (bval bs j)).2.2
          rw [← this]; simp [pow_succ, pow_zero, mul_assoc]
      · simp [compileStep, andBlock]; omega
      · intro op hop'
        simp only [compileStep, List.mem_append] at hop'
        rcases hop' with h | h
        · exact hmul op h
        · simp only [andBlock, List.mem_cons, List.not_mem_nil, or_false] at h
          have hd := gadget_identities.1.2.2.2
          have hc := gadget_identities.1.2.2.1
          rcases h with rfl | rfl | rfl | rfl | h
          · exact Subgroup.inv_mem _ hd
          · exact Subgroup.inv_mem _ hc
          · exact hc
          · exact hd
          · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
              rfl <;> trivial
      · simp only [compileStep, andBlock]
        rw [show ∀ (l : List (Op (Perm (Fin 5)))) (a b c d e f g h i j k l' m n o p q : Op _),
            l ++ [a, b, c, d, e, f, g, h, i, j, k, l', m, n, o, p, q] =
            l ++ [a] ++ [b] ++ [c] ++ [d] ++ [e] ++ [f] ++ [g] ++ [h] ++ [i] ++ [j] ++ [k] ++
            [l'] ++ [m] ++ [n] ++ [o] ++ [p] ++ [q] from by intros; simp]
        simp only [wellFormed_append_single, List.length_append, List.length_singleton, Op.WF]
        refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hwfC, trivial⟩, trivial⟩, trivial⟩, trivial⟩, ?_⟩, ?_⟩, ?_⟩,
          ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> constructor <;> omega

/-- **Linear Boolean-to-`A₅` reduction** (004g, Corollary 3.4; 004a, Lemma 2.2). For every
well-formed Boolean circuit `bs` of size `s`, the compiled program is an `A₅` multiplication
circuit (constants in `A₅`, no inverse gates, operands earlier) of size at most `17 s`, and every
Boolean node `k` has a copy whose value is the encoding of its Boolean value. In particular the
output is `1` iff the copy of the output evaluates to `a`. -/
theorem boolean_to_A5 (bs : List BOp) (hwf : BWellFormed bs) :
    IsMulCircuit (compile bs).1 ∧ WellFormed (compile bs).1 ∧
    (compile bs).1.length ≤ 17 * bs.length ∧
    ∀ k < bs.length, val id (compile bs).1 ((compile bs).2.getD k 0) = enc (bval bs k) := by
  obtain ⟨-, hval, hsize, hmul, hwfC⟩ := compile_spec bs hwf
  exact ⟨hmul, hwfC, hsize, fun k hk => (hval k hk).2⟩

theorem enc_eq_aA_iff (u : Bool) : enc u = aA ↔ u = true := by
  cases u <;> decide

end GC.A5Programs
