import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Basic

/-! Comparator challenge for manuscript 006a (Two Pages Suffice for P-Completeness). -/


/-!
# Sequential NOR: basic definitions

A parent array of length `n` is modelled as a function `j : ℕ → ℕ` with `j i < i` for
`1 ≤ i ≤ n` (the values `j 0` and `j i`, `i > n`, are irrelevant).  Its trace is
`x 0 = 1`, `x i = NOR (x (i-1)) (x (j i))`.

The arc of position `i` (`1 ≤ i ≤ n`) is `(j i, i)`; every position is the right endpoint of
exactly one arc, so a page assignment is a function of the right endpoint.
-/

namespace GC.SeqNORNormalForms

/-- Boolean NOR. -/
def nor (a b : Bool) : Bool := !(a || b)

/-- `j` is a parent array of length `n`: `j i < i` for every `1 ≤ i ≤ n`. -/
def IsParentArray (n : ℕ) (j : ℕ → ℕ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ n → j i < i

/-- The Sequential NOR trace: `x 0 = true` and `x (i+1) = NOR (x i) (x (j (i+1)))`.
(If `j (i+1) ≥ i+1`, which never happens for a parent array, a junk value is used.) -/
def trace (j : ℕ → ℕ) : ℕ → Bool
  | 0 => true
  | i + 1 => nor (trace j i) (if h : j (i + 1) < i + 1 then trace j (j (i + 1)) else true)
termination_by i => i

/-- Two arcs `(a,b)` and `(a',b')` (with `a < b`, `a' < b'`) cross if their endpoints
strictly interleave. -/
def Cross (a b a' b' : ℕ) : Prop :=
  (a < a' ∧ a' < b ∧ b < b') ∨ (a' < a ∧ a < b' ∧ b' < b)

/-- A `k`-page assignment of the arcs `(j i, i)`, `1 ≤ i ≤ n`: arcs on the same page do not
cross. -/
def IsPageAssignment (n : ℕ) (j : ℕ → ℕ) (k : ℕ) (page : ℕ → Fin k) : Prop :=
  ∀ i i', 1 ≤ i → i ≤ n → 1 ≤ i' → i' ≤ n → page i = page i' → ¬ Cross (j i) i (j i') i'

/-- `pg(j) ≤ k`: the arcs of `j` have a `k`-page assignment. -/
def PageNumberLE (n : ℕ) (j : ℕ → ℕ) (k : ℕ) : Prop :=
  ∃ page : ℕ → Fin k, IsPageAssignment n j k page

/-- A NOR circuit with `G ≥ 2` gates: wires `w 0 = 1`, `w 1 = 0` and
`w g = NOR (w (a g)) (w (b g))` for `2 ≤ g ≤ G`, with `a g, b g < g`. -/
structure NorCircuit where
  G : ℕ
  a : ℕ → ℕ
  b : ℕ → ℕ

/-- Well-formedness of a NOR circuit. -/
def NorCircuit.Valid (C : NorCircuit) : Prop :=
  2 ≤ C.G ∧ ∀ g, 2 ≤ g → g ≤ C.G → C.a g < g ∧ C.b g < g

/-- The wire values of a NOR circuit. -/
def NorCircuit.wire (C : NorCircuit) : ℕ → Bool
  | 0 => true
  | 1 => false
  | g + 2 => nor (if h : C.a (g + 2) < g + 2 then C.wire (C.a (g + 2)) else false)
                 (if h : C.b (g + 2) < g + 2 then C.wire (C.b (g + 2)) else false)
termination_by g => g

/-! ### Elementary lemmas -/

/-- **Lemma 2.1 of 006a** (elementary facts). -/
theorem basic_facts (n : ℕ) (j : ℕ → ℕ) (hj : IsParentArray n j) (i : ℕ) (hi : 1 ≤ i)
    (hin : i ≤ n) :
    (trace j i = true ↔ trace j (i - 1) = false ∧ trace j (j i) = false) ∧
    (trace j (i - 1) = true → trace j i = false) ∧
    (trace j (i - 1) = false → trace j i = !trace j (j i)) ∧
    (j i = 0 → trace j i = false) := by
  sorry

end GC.SeqNORNormalForms


/-!
# 006a, Section 3: the five-cell reduction (Okhotin's theorem)

For a NOR circuit with `G ≥ 2` gates put `pos 0 = 0`, `pos 1 = 1`, `pos w = 5w - 5`, and
let `n = 5G - 1`. The parent array is `j_1 = 0`, the block
`j_{i₁} = pos a_w, j_{i₁+1} = 0, j_{i₁+2} = i₁, j_{i₁+3} = pos b_w, j_{i₁+4} = 0`
with `i₁ = 5w - 8` for every gate `w ≥ 2`, and the tail
`j_{5G-3} = pos G, j_{5G-2} = 0, j_{5G-1} = 5G - 3`.
-/

namespace GC.SeqNORNormalForms

/-- `pos(w)`: the position holding wire `w`. -/
def okPos (w : ℕ) : ℕ := if w ≤ 1 then w else 5 * w - 5

/-- The five-cell parent array of a NOR circuit (Section 3 of 006a). -/
def okhotin (C : NorCircuit) (i : ℕ) : ℕ :=
  if i ≤ 1 then 0
  else if i ≤ 5 * C.G - 4 then
    if (i + 8) % 5 = 0 then okPos (C.a ((i + 8) / 5))
    else if (i + 8) % 5 = 1 then 0
    else if (i + 8) % 5 = 2 then i - 2
    else if (i + 8) % 5 = 3 then okPos (C.b ((i + 8) / 5))
    else 0
  else if i = 5 * C.G - 3 then okPos C.G
  else if i = 5 * C.G - 2 then 0
  else 5 * C.G - 3

section

variable (C : NorCircuit)

/-- **Theorem 3.3 of 006a (Okhotin).** The five-cell array of a NOR circuit is a parent
array of length `5G - 1`, every wire is held at `pos(w)`, and `x_n = w_G`. -/
theorem okhotin_correct (hC : C.Valid) :
    IsParentArray (5 * C.G - 1) (okhotin C) ∧
      (∀ w, w ≤ C.G → trace (okhotin C) (okPos w) = C.wire w) ∧
      trace (okhotin C) (5 * C.G - 1) = C.wire C.G := by
  sorry

/-- **Corollary 3.4 of 006a (key step).** If gate `2` is the dummy gate `NOR(w_0, w_0)`
(`a_2 = 0`), then in the five-cell array `j_i ≠ i - 1` for every `2 ≤ i ≤ n`, so `i - 1` and
`j_i` are two distinct smaller neighbours of `i` in the graph `G_j`. -/
theorem okhotin_no_spine (hC : C.Valid) (ha2 : C.a 2 = 0) :
    ∀ i, 2 ≤ i → i ≤ 5 * C.G - 1 → okhotin C i ≠ i - 1 := by
  sorry

end

end GC.SeqNORNormalForms


/-!
# 006a: alternating-direction NOR/OR arrays and the serpentine two-page compilation

Definition 7.1, the sources of a cell (equation (sources) of Section 7.4), the instance `Φ` of Section 7.4 (Table 2), Lemmas 7.6,
7.7 (values), 7.8, 7.9, 7.10 and Theorem 7.11 (two pages).
-/

namespace GC.SeqNORNormalForms

/-- The six cell types of an alternating-direction array. -/
inductive CellType
  | N | C | X | Y | R | O
  deriving DecidableEq, Repr

namespace CellType

/-- Value of a cell from `a = v(t-1,s)` and `b = v(t-1,σ(t,s))`. -/
def eval : CellType → Bool → Bool → Bool
  | N, a, _ => !a
  | C, a, _ => a
  | X, _, b => !b
  | Y, _, b => b
  | R, a, b => nor a b
  | O, a, b => a || b

/-- The types that read the neighbour. -/
def readsNbr : CellType → Bool
  | X => true
  | Y => true
  | R => true
  | O => true
  | _ => false

/-- OR-type cells (`C`, `Y`, `O`); the others are NOR-type. -/
def isOr : CellType → Bool
  | C => true
  | Y => true
  | O => true
  | _ => false

end CellType

/-- The neighbour column `σ(t,s)`: `s - 1` on odd layers, `s + 1` on even layers. -/
def nbr (t s : ℕ) : ℕ := if t % 2 = 1 then s - 1 else s + 1

/-- An alternating-direction NOR/OR array of width `k` and depth `d` (Definition 7.1):
constants `init s = v(0,s)` on layer `0` and a type for every cell `(t,s)`, `t ≥ 1`. -/
structure NorOrArray where
  k : ℕ
  d : ℕ
  init : ℕ → Bool
  type : ℕ → ℕ → CellType

/-- Well-formedness: `k, d ≥ 1`, and types reading the neighbour only where
`0 ≤ σ(t,s) < k`. -/
def NorOrArray.Valid (A : NorOrArray) : Prop :=
  1 ≤ A.k ∧ 1 ≤ A.d ∧
    ∀ t s, 1 ≤ t → t ≤ A.d → s < A.k → (A.type t s).readsNbr = true →
      (t % 2 = 1 → 1 ≤ s) ∧ (t % 2 = 0 → s + 1 < A.k)

/-- The value `v(t,s)` of a cell. -/
def NorOrArray.val (A : NorOrArray) : ℕ → ℕ → Bool
  | 0, s => A.init s
  | t + 1, s => (A.type (t + 1) s).eval (A.val t s) (A.val t (nbr (t + 1) s))

/-- First source `π` of a cell (equation (sources) of 006a, Section 7.4). -/
def src1 (ty : CellType) (t s : ℕ) : ℕ :=
  match ty with
  | CellType.X => nbr t s
  | CellType.Y => nbr t s
  | _ => s

/-- Second source `κ` of a cell (equation (sources) of 006a, Section 7.4). -/
def src2 (ty : CellType) (t s : ℕ) : ℕ :=
  match ty with
  | CellType.N => s
  | CellType.C => s
  | _ => nbr t s

/-- Index `e` of cell `(t,s)` in the emission order of layer `t` (serpentine order: odd
layers right to left, even layers left to right). -/
def emitIdx (k t s : ℕ) : ℕ := if t % 2 = 1 then k - 1 - s else s

/-- Start `c(t,s) = 2 + 2k + 8 (k (t-1) + e)` of the block of cell `(t,s)`. -/
def blockStart (k t s : ℕ) : ℕ := 2 + 2 * k + 8 * (k * (t - 1) + emitIdx k t s)

/-- The output position `o(t,s)`. -/
def NorOrArray.out (A : NorOrArray) : ℕ → ℕ → ℕ
  | 0, s => if A.init s then 2 + 2 * s else 2 + 2 * s + 1
  | t + 1, s => blockStart A.k (t + 1) s + (if (A.type (t + 1) s).isOr then 5 else 4)

/-- Start `m = 2 + 2k + 8kd` of the tail. -/
def NorOrArray.tailStart (A : NorOrArray) : ℕ := 2 + 2 * A.k + 8 * (A.k * A.d)

/-- The length `n = m + 3` of `Φ`. -/
def NorOrArray.len (A : NorOrArray) : ℕ := A.tailStart + 3

/-- Parent of position `c + r` (`r < 8`) inside block number `b` (Table 2); the block
belongs to the cell `(t,s)` emitted `e`-th in layer `t`, with `b = k (t-1) + e`. -/
def NorOrArray.blockEntry (A : NorOrArray) (b r : ℕ) : ℕ :=
  let t := b / A.k + 1
  let e := b % A.k
  let s := if t % 2 = 1 then A.k - 1 - e else e
  let c := 2 + 2 * A.k + 8 * b
  let ty := A.type t s
  if r = 0 then A.out (t - 1) (src1 ty t s)
  else if r ≤ 3 then c
  else if r = 4 then A.out (t - 1) (src2 ty t s)
  else if r = 5 then c + 4
  else c + 5

/-- The instance `Φ` of Section 7.4: positions `0,1` with `j_1 = 0`; constant blocks
`j_c = c-1, j_{c+1} = c` at `c = 2 + 2s`; one 8-position block per cell in serpentine
order; the tail `j_m = o(d, s_out)`, `j_{m+1} = j_{m+2} = j_{m+3} = m`. -/
def NorOrArray.serp (A : NorOrArray) (sout : ℕ) (i : ℕ) : ℕ :=
  if i < 2 then 0
  else if i < 2 + 2 * A.k then i - 1
  else if i < A.tailStart then
    A.blockEntry ((i - (2 + 2 * A.k)) / 8) ((i - (2 + 2 * A.k)) % 8)
  else if i = A.tailStart then A.out A.d sout
  else A.tailStart

/-- The two-page assignment of Theorem 7.11 (page `0` is the paper's page 1): transition
arcs (entering `c` or `c+4` of a block) of odd layers and all short arcs on page `0`,
transition arcs of even layers on page `1`, the tail arc on page `0` iff `d` is even. -/
def NorOrArray.page (A : NorOrArray) (i : ℕ) : Fin 2 :=
  if 2 + 2 * A.k ≤ i ∧ i < A.tailStart ∧
      ((i - (2 + 2 * A.k)) % 8 = 0 ∨ (i - (2 + 2 * A.k)) % 8 = 4) then
    (if ((i - (2 + 2 * A.k)) / 8 / A.k + 1) % 2 = 1 then 0 else 1)
  else if i = A.tailStart then (if A.d % 2 = 0 then 0 else 1)
  else 0

/-! ### The block of Table 2 (Lemma 7.6) -/

/-! ### Arithmetic of the layout -/

/-- Start of the region of layer `t ≥ 1`. -/
def layerBase (k t : ℕ) : ℕ := 2 + 2 * k + 8 * (k * (t - 1))

/-- Block index of the cell `(t,s)`. -/
def cellIdx (k t s : ℕ) : ℕ := k * (t - 1) + emitIdx k t s

/-! ### Decoding `Φ` -/

section Decode

variable (A : NorOrArray) (sout : ℕ)

end Decode

/-! ### Sources -/

/-! ### Values (Lemma 7.7) -/

section Values

variable (A : NorOrArray) (sout : ℕ)

end Values

/-! ### Pages (Lemmas 7.8–7.10, Theorem 7.11) -/

/-- Source column of the transition arc entering position `c(t,s) + r` (`r = 0` or `4`). -/
def NorOrArray.arcSrc (A : NorOrArray) (t s r : ℕ) : ℕ :=
  if r = 0 then src1 (A.type t s) t s else src2 (A.type t s) t s

/-- Positions that occur as parents in `Φ`. -/
def NorOrArray.ParentPos (A : NorOrArray) (y : ℕ) : Prop :=
  y < 2 + 2 * A.k ∨
    (2 + 2 * A.k ≤ y ∧ y < A.tailStart ∧
      ((y - (2 + 2 * A.k)) % 8 = 0 ∨ (y - (2 + 2 * A.k)) % 8 = 4 ∨
        (y - (2 + 2 * A.k)) % 8 = 5)) ∨
    y = A.tailStart

section Pages

variable (A : NorOrArray) (sout : ℕ)

end Pages

/-- **Theorem 7.11 of 006a (serpentine compilation).** For every well-formed
alternating-direction NOR/OR array `A` and output column `s_out < k`, the instance
`Φ = A.serp s_out` of length `n = 2 + 2k + 8kd + 3` is a parent array, its trace satisfies
`x_{o(t,s)} = v(t,s)` for every cell and `x_n = v(d, s_out)`, and `A.page` (transition arcs of
odd layers and all short arcs on one page, transition arcs of even layers on the other, the
tail arc according to the parity of `d`) is a two-page assignment; in particular
`pg(Φ) ≤ 2`. -/
theorem serpentine_two_pages (A : NorOrArray) (hA : A.Valid) (sout : ℕ) (hs : sout < A.k) :
    IsParentArray A.len (A.serp sout) ∧
    (∀ t s, t ≤ A.d → s < A.k → trace (A.serp sout) (A.out t s) = A.val t s) ∧
    trace (A.serp sout) A.len = A.val A.d sout ∧
    IsPageAssignment A.len (A.serp sout) 2 A.page ∧
    PageNumberLE A.len (A.serp sout) 2 := by
  sorry

end GC.SeqNORNormalForms


/-!
# 006a, Sections 7.2–7.3: slot programs, the three-column gadgets, and the end-to-end
two-page reduction

Lemma 7.3 (slot programs), Table 1 and Lemma 7.4 (gadgets), Lemma 7.5 (arrays from slot
programs), and the composition with Theorem 7.11: every NOR circuit is mapped to a parent
array of page number at most 2 whose last trace bit is the circuit output.
-/

namespace GC.SeqNORNormalForms

/-! ### Slot programs (Lemma 7.3) -/

/-- Instructions on adjacent slots `i, i+1`. -/
inductive Instr
  | swap (i : ℕ)
  | copy (i : ℕ)
  | nor (i : ℕ)
  deriving DecidableEq, Repr

/-- The slot an instruction acts on (it acts on slots `i` and `i+1`). -/
def Instr.slot : Instr → ℕ
  | swap i => i
  | copy i => i
  | nor i => i

/-- Semantics of one instruction on `z : ℕ → Bool`. -/
def Instr.run : Instr → (ℕ → Bool) → ℕ → Bool
  | swap i, z => fun m => if m = i then z (i + 1) else if m = i + 1 then z i else z m
  | copy i, z => fun m => if m = i + 1 then z i else z m
  | nor i, z => fun m => if m = i then GC.SeqNORNormalForms.nor (z i) (z (i + 1)) else z m

/-- Run a slot program. -/
def runProg (P : List Instr) (z : ℕ → Bool) : ℕ → Bool :=
  P.foldl (fun z I => I.run z) z

/-- `SWAP(g-1), SWAP(g-2), …, SWAP(a+1)`. -/
def swapsDown (a : ℕ) : ℕ → List Instr
  | 0 => []
  | g + 1 => if g ≤ a then [] else Instr.swap g :: swapsDown a g

/-- `SWAP(a+1), SWAP(a+2), …, SWAP(g-1)`. -/
def swapsUp (a : ℕ) : ℕ → List Instr
  | 0 => []
  | g + 1 => if g ≤ a then [] else swapsUp a g ++ [Instr.swap g]

/-- Steps (1)/(2) of Lemma 7.3: `SWAP(g-1),…,SWAP(a+1); COPY(a); SWAP(a+1),…,SWAP(g-1)`. -/
def moveCopy (a g : ℕ) : List Instr := swapsDown a g ++ Instr.copy a :: swapsUp a g

/-- The program of gate `g`, with sorted inputs `a ≤ b`. -/
def gateProg (C : NorCircuit) (g : ℕ) : List Instr :=
  moveCopy (min (C.a g) (C.b g)) g ++ moveCopy (max (C.a g) (C.b g)) (g + 1) ++ [Instr.nor g]

/-- The slot program of a NOR circuit: the programs of gates `2, …, G` in order. -/
def slotProg (C : NorCircuit) : List Instr :=
  (List.range (C.G - 1)).flatMap (fun k => gateProg C (k + 2))

/-- **Lemma 7.3.** The slot program maps `z = (1,0,0,…)` to a vector with `z_G = w_G`
(indeed `z_g = w_g` for all `g ≤ G`). -/
theorem run_slotProg (C : NorCircuit) (hC : C.Valid) :
    ∀ i, i ≤ C.G → runProg (slotProg C) (fun m => decide (m = 0)) i = C.wire i := by
  sorry

/-! ### The three gadgets (Table 1, Lemma 7.4) -/

/-- The three gadget kinds. -/
inductive GKind
  | swap
  | copy
  | nor
  deriving DecidableEq, Repr

/-- The kind of an instruction. -/
def Instr.kind : Instr → GKind
  | Instr.swap _ => GKind.swap
  | Instr.copy _ => GKind.copy
  | Instr.nor _ => GKind.nor

/-- Number of layers of a gadget: 8 for SWAP, 4 for COPY and NOR. -/
def GKind.height : GKind → ℕ
  | GKind.swap => 8
  | GKind.copy => 4
  | GKind.nor => 4

/-- Number of layers of the gadget of an instruction. -/
def Instr.height (I : Instr) : ℕ := I.kind.height

open CellType in
/-- Table 1: the type of the gadget cell in relative layer `t ∈ {1,…,height}` and relative
column `c ∈ {0,1,2}` (columns `2i, 2i+1, 2i+2`). -/
def gadgetType : GKind → ℕ → ℕ → CellType
  | GKind.copy, 1, 0 => N | GKind.copy, 1, 1 => X | GKind.copy, 1, 2 => N
  | GKind.copy, 2, 0 => N | GKind.copy, 2, 1 => N | GKind.copy, 2, 2 => N
  | GKind.copy, 3, 0 => N | GKind.copy, 3, 1 => N | GKind.copy, 3, 2 => Y
  | GKind.copy, 4, 0 => N | GKind.copy, 4, 1 => R | GKind.copy, 4, 2 => C
  | GKind.nor, 1, 0 => N | GKind.nor, 1, 1 => N | GKind.nor, 1, 2 => N
  | GKind.nor, 2, 0 => N | GKind.nor, 2, 1 => X | GKind.nor, 2, 2 => N
  | GKind.nor, 3, 0 => N | GKind.nor, 3, 1 => O | GKind.nor, 3, 2 => N
  | GKind.nor, 4, 0 => X | GKind.nor, 4, 1 => R | GKind.nor, 4, 2 => N
  | GKind.swap, 1, 0 => N | GKind.swap, 1, 1 => X | GKind.swap, 1, 2 => N
  | GKind.swap, 2, 0 => N | GKind.swap, 2, 1 => R | GKind.swap, 2, 2 => C
  | GKind.swap, 3, 0 => N | GKind.swap, 3, 1 => C | GKind.swap, 3, 2 => R
  | GKind.swap, 4, 0 => R | GKind.swap, 4, 1 => O | GKind.swap, 4, 2 => N
  | GKind.swap, 5, 0 => C | GKind.swap, 5, 1 => R | GKind.swap, 5, 2 => N
  | GKind.swap, 6, 0 => R | GKind.swap, 6, 1 => C | GKind.swap, 6, 2 => C
  | GKind.swap, 7, 0 => N | GKind.swap, 7, 1 => N | GKind.swap, 7, 2 => O
  | GKind.swap, 8, 0 => N | GKind.swap, 8, 1 => R | GKind.swap, 8, 2 => N
  | _, _, _ => C

/-- Local simulation of a gadget on its three columns (relative columns `0,1,2`; columns
`≥ 3` are set to `0`). -/
def lsim (K : GKind) (w : ℕ → Bool) : ℕ → ℕ → Bool
  | 0 => w
  | t + 1 => fun c =>
      if c ≤ 2 then (gadgetType K (t + 1) c).eval (lsim K w t c) (lsim K w t (nbr (t + 1) c))
      else false

/-- **Lemma 7.4 (last claim).** No gadget cell reads a column outside its three columns:
in odd rows column `2i` does not read its neighbour, in even rows column `2i+2` does not. -/
theorem gadget_reads (K : GKind) :
    ∀ t < 9, ∀ c < 3, (gadgetType K t c).readsNbr = true →
      (t % 2 = 1 → 1 ≤ c) ∧ (t % 2 = 0 → c ≤ 1) := by
  sorry

/-- The initial state `(u, 0, v)` of a gadget (with an arbitrary junk value `y` in the fourth
local column). -/
def tri (u v y : Bool) : ℕ → Bool := fun c =>
  if c = 0 then u else if c = 1 then false else if c = 2 then v else y

/-- **Lemma 7.4 (values; Table 1).** Starting from `(u, 0, v)`, after the gadget the three
columns hold `(u, 0, u)` for COPY, `(NOR(u,v), 0, v)` for NOR and `(v, 0, u)` for SWAP. -/
theorem gadget_values (K : GKind) (u v y : Bool) :
    lsim K (tri u v y) K.height 0 = (match K with
      | GKind.copy => u | GKind.nor => nor u v | GKind.swap => v) ∧
    lsim K (tri u v y) K.height 1 = false ∧
    lsim K (tri u v y) K.height 2 = (match K with
      | GKind.copy => u | GKind.nor => v | GKind.swap => u) := by
  sorry

/-! ### Arrays from slot programs (Lemma 7.5) -/

/-- Layer types of the array of a slot program: the gadget of each instruction in turn on the
columns `2i, 2i+1, 2i+2` of its slot `i`, type `C` elsewhere. -/
def progType : List Instr → ℕ → ℕ → CellType
  | [], _, _ => CellType.C
  | I :: P, t, s =>
      if t ≤ I.height then
        (if 2 * I.slot ≤ s ∧ s ≤ 2 * I.slot + 2 then gadgetType I.kind t (s - 2 * I.slot)
          else CellType.C)
      else progType P (t - I.height) s

/-- Total height of a slot program. -/
def progHeight (P : List Instr) : ℕ := (P.map Instr.height).sum

/-- Encoding of a slot vector in an array layer: slot `i` in column `2i`, support columns
`2i+1` hold `0`. -/
def encodeSlots (z : ℕ → Bool) (s : ℕ) : Bool := if s % 2 = 0 then z (s / 2) else false

/-- The array of Lemma 7.5 for a NOR circuit: width `2M = 2(G+2)`, layer `0` equal to
`(1, 0, …, 0)`, and the gadgets of the slot program of Lemma 7.3 in turn. -/
def circuitArray (C : NorCircuit) : NorOrArray where
  k := 2 * (C.G + 2)
  d := progHeight (slotProg C)
  init := fun s => decide (s = 0)
  type := progType (slotProg C)

/-- **Theorem 7.11 of 006a (two pages suffice), correctness of the reduction.** For every NOR
circuit, the parent array `Φ` obtained by the slot program (Lemma 7.3), the three-column
gadgets (Table 1, Lemma 7.4), the array of Lemma 7.5 and the serpentine compilation
(Section 7.4) is a parent array with `pg(Φ) ≤ 2` (with the explicit two-page assignment of
Theorem 7.11), and its last trace bit is the output `w_G` of the circuit. -/
theorem circuit_two_pages (C : NorCircuit) (hC : C.Valid) :
    IsParentArray (circuitArray C).len ((circuitArray C).serp (2 * C.G)) ∧
    trace ((circuitArray C).serp (2 * C.G)) (circuitArray C).len = C.wire C.G ∧
    IsPageAssignment (circuitArray C).len ((circuitArray C).serp (2 * C.G)) 2
      (circuitArray C).page ∧
    PageNumberLE (circuitArray C).len ((circuitArray C).serp (2 * C.G)) 2 := by
  sorry

/-! ### Proposition 7.2: NOR-only arrays are monotone after parity normalization -/

/-- **Proposition 7.2 (algebraic part).** In an array whose types are `N`, `X`, `R` only, the
normalized values `ṽ(t,s) = v(t,s) ⊕ (t mod 2)` satisfy: `N` copies `ṽ(t-1,s)`, `X` copies
`ṽ(t-1,σ)`, and `R` is the OR (odd `t`) or the AND (even `t`) of the two. So `ṽ` is computed
by a monotone circuit of OR, AND and identity gates. -/
theorem nor_only_monotone (A : NorOrArray) (t s : ℕ) :
    let vt : ℕ → ℕ → Bool := fun t s => xor (A.val t s) (decide (t % 2 = 1))
    (A.type (t + 1) s = CellType.N → vt (t + 1) s = vt t s) ∧
    (A.type (t + 1) s = CellType.X → vt (t + 1) s = vt t (nbr (t + 1) s)) ∧
    (A.type (t + 1) s = CellType.R → vt (t + 1) s =
      if (t + 1) % 2 = 1 then (vt t s || vt t (nbr (t + 1) s))
      else (vt t s && vt t (nbr (t + 1) s))) := by
  sorry

/-- **Proposition 7.2 (planar layout).** Place cell `(t,s)` at the point
`(s - (t mod 2)/2, t)`, i.e. at doubled abscissa `X(t,s) = 2s - (t mod 2)`. Every wire into
layer `t` joins points whose abscissas differ by exactly `1/2`, and wires between two
consecutive layers preserve the left-to-right order; hence they meet only at common
endpoints. -/
theorem nor_array_planar (t s u s' u' : ℕ) (ht : 1 ≤ t)
    (hu : u = s ∨ (u = nbr t s ∧ (t % 2 = 1 → 1 ≤ s)))
    (hu' : u' = s' ∨ (u' = nbr t s' ∧ (t % 2 = 1 → 1 ≤ s'))) :
    let X : ℕ → ℕ → ℤ := fun t s => 2 * (s : ℤ) - ((t % 2 : ℕ) : ℤ)
    |X (t - 1) u - X t s| = 1 ∧ (X (t - 1) u < X (t - 1) u' → X t s ≤ X t s') := by
  sorry

end GC.SeqNORNormalForms
