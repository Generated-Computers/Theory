import GC.Computability.SeqNORNormalForms.TwoPages

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

theorem runProg_append (P Q : List Instr) (z : ℕ → Bool) :
    runProg (P ++ Q) z = runProg Q (runProg P z) := by
  simp [runProg, List.foldl_append]

theorem runProg_cons (I : Instr) (P : List Instr) (z : ℕ → Bool) :
    runProg (I :: P) z = runProg P (I.run z) := rfl

theorem runProg_nil (z : ℕ → Bool) : runProg [] z = z := rfl

theorem moveCopy_succ {a g : ℕ} (h : a < g) :
    moveCopy a (g + 1) = Instr.swap g :: (moveCopy a g ++ [Instr.swap g]) := by
  unfold moveCopy
  rw [swapsDown, swapsUp, if_neg (by omega), if_neg (by omega)]
  simp

theorem moveCopy_self (a : ℕ) : moveCopy a (a + 1) = [Instr.copy a] := by
  unfold moveCopy
  rw [swapsDown, swapsUp, if_pos le_rfl, if_pos le_rfl]
  simp

/-- The net effect of steps (1)/(2) of Lemma 7.3: slot `g` receives `z_a`, all other slots
are unchanged. -/
theorem run_moveCopy {a g : ℕ} (h : a < g) (z : ℕ → Bool) :
    runProg (moveCopy a g) z = Function.update z g (z a) := by
  induction g generalizing z with
  | zero => omega
  | succ g ih =>
    rcases Nat.lt_or_ge a g with hag | hag
    · rw [moveCopy_succ hag, runProg_cons, runProg_append, ih hag]
      funext m
      simp only [runProg_cons, runProg_nil, Instr.run, Function.update]
      by_cases h1 : m = g
      · subst h1; simp
      · by_cases h2 : m = g + 1
        · subst h2; simp [show a ≠ g by omega, show a ≠ g + 1 by omega]
        · simp [h1, h2]
    · obtain rfl : a = g := by omega
      rw [moveCopy_self]
      funext m
      simp only [runProg_cons, runProg_nil, Instr.run, Function.update]
      by_cases h1 : m = a + 1 <;> simp [h1]

/-- **Lemma 7.3 (one gate).** If slots `0..g-1` hold `w_0..w_{g-1}`, then after the program
of gate `g` slots `0..g` hold `w_0..w_g`. -/
theorem run_gateProg (C : NorCircuit) (hC : C.Valid) {g : ℕ} (hg : 2 ≤ g) (hgG : g ≤ C.G)
    (z : ℕ → Bool) (hz : ∀ i, i < g → z i = C.wire i) :
    ∀ i, i ≤ g → runProg (gateProg C g) z i = C.wire i := by
  obtain ⟨ha, hb⟩ := hC.2 g hg hgG
  have hmin : min (C.a g) (C.b g) < g := by omega
  have hmax : max (C.a g) (C.b g) < g + 1 := by omega
  intro i hi
  unfold gateProg
  rw [runProg_append, runProg_append, run_moveCopy hmin, run_moveCopy hmax]
  simp only [runProg_cons, runProg_nil, Instr.run]
  have hzmin : z (min (C.a g) (C.b g)) = C.wire (min (C.a g) (C.b g)) := hz _ hmin
  have hzmax : z (max (C.a g) (C.b g)) = C.wire (max (C.a g) (C.b g)) := hz _ (by omega)
  have hbg : max (C.a g) (C.b g) ≠ g := by omega
  by_cases hig : i = g
  · subst hig
    rw [if_pos rfl]
    simp only [Function.update_apply, show i ≠ i + 1 by omega, if_false, hbg, ite_true,
      if_true]
    rw [hzmin, hzmax, NorCircuit.wire_gate C i hg ha hb]
    rcases le_total (C.a i) (C.b i) with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h]
      cases C.wire (C.a i) <;> cases C.wire (C.b i) <;> rfl
  · rw [if_neg hig]
    simp only [Function.update_apply, hig, show i ≠ g + 1 by omega, if_false]
    exact hz i (by omega)

/-- **Lemma 7.3.** The slot program maps `z = (1,0,0,…)` to a vector with `z_G = w_G`
(indeed `z_g = w_g` for all `g ≤ G`). -/
theorem run_slotProg (C : NorCircuit) (hC : C.Valid) :
    ∀ i, i ≤ C.G → runProg (slotProg C) (fun m => decide (m = 0)) i = C.wire i := by
  have hG := hC.1
  -- after the gates `2, …, g+1`
  have key : ∀ g, g + 1 ≤ C.G →
      ∀ i, i ≤ g + 1 → runProg ((List.range g).flatMap (fun k => gateProg C (k + 2)))
        (fun m => decide (m = 0)) i = C.wire i := by
    intro g
    induction g with
    | zero =>
      intro _ i hi
      interval_cases i
      · simp [runProg, NorCircuit.wire_zero]
      · simp [runProg, NorCircuit.wire_one]
    | succ g ih =>
      intro hg i hi
      rw [List.range_succ, List.flatMap_append, runProg_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact run_gateProg C hC (g := g + 2) (by omega) (by omega) _
        (fun i hi => ih (by omega) i (by omega)) i (by omega)
  intro i hi
  have := key (C.G - 1) (by omega) i (by omega)
  simpa [slotProg] using this


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

theorem eval_irrel {ty : CellType} (h : ty.readsNbr = false) (a b b' : Bool) :
    ty.eval a b = ty.eval a b' := by
  cases ty <;> simp_all [CellType.readsNbr, CellType.eval]

/-- **Lemma 7.4 (last claim).** No gadget cell reads a column outside its three columns:
in odd rows column `2i` does not read its neighbour, in even rows column `2i+2` does not. -/
theorem gadget_reads (K : GKind) :
    ∀ t < 9, ∀ c < 3, (gadgetType K t c).readsNbr = true →
      (t % 2 = 1 → 1 ≤ c) ∧ (t % 2 = 0 → c ≤ 1) := by
  cases K <;> decide

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
  cases K <;> cases u <;> cases v <;> cases y <;> decide

theorem lsim_congr (K : GKind) (w w' : ℕ → Bool) (h : ∀ c, c ≤ 3 → w c = w' c) :
    ∀ t c, c ≤ 3 → lsim K w t c = lsim K w' t c := by
  intro t
  induction t with
  | zero => intro c hc; exact h c hc
  | succ t ih =>
    intro c hc
    simp only [lsim]
    split
    · rw [ih c (by omega), ih (nbr (t + 1) c) (by unfold nbr; split <;> omega)]
    · rfl

theorem nbr_add_even {t0 t s : ℕ} (h : t0 % 2 = 0) : nbr (t0 + t) s = nbr t s := by
  unfold nbr
  have : (t0 + t) % 2 = t % 2 := by omega
  rw [this]

theorem height_le (K : GKind) : K.height ≤ 8 := by cases K <;> simp [GKind.height]

/-- Running a gadget inside an arbitrary array: if the layers `t0+1, …, t0+height` carry the
gadget on columns `2i, 2i+1, 2i+2` and type `C` elsewhere (with `t0` even, so that the
gadget starts at an odd layer), the other columns are unchanged and the three gadget columns
follow the local simulation. -/
theorem gadget_run (A : NorOrArray) (K : GKind) (i t0 : ℕ) (ht0 : t0 % 2 = 0)
    (htype : ∀ t s, 1 ≤ t → t ≤ K.height →
      A.type (t0 + t) s = if 2 * i ≤ s ∧ s ≤ 2 * i + 2 then gadgetType K t (s - 2 * i)
        else CellType.C) :
    ∀ t, t ≤ K.height → ∀ s, A.val (t0 + t) s =
      if 2 * i ≤ s ∧ s ≤ 2 * i + 2 then lsim K (fun c => A.val t0 (2 * i + c)) t (s - 2 * i)
      else A.val t0 s := by
  have hh := height_le K
  intro t
  induction t with
  | zero =>
    intro _ s
    simp only [Nat.add_zero, lsim]
    split
    · congr 1; omega
    · rfl
  | succ t ih =>
    intro ht s
    have hval : A.val (t0 + (t + 1)) s = (A.type (t0 + (t + 1)) s).eval (A.val (t0 + t) s)
        (A.val (t0 + t) (nbr (t0 + (t + 1)) s)) := by
      rw [show t0 + (t + 1) = (t0 + t) + 1 by omega]; rfl
    rw [hval, htype (t + 1) s (by omega) ht, nbr_add_even ht0]
    by_cases hs : 2 * i ≤ s ∧ s ≤ 2 * i + 2
    · rw [if_pos hs, if_pos hs]
      obtain ⟨c, rfl⟩ : ∃ c, s = 2 * i + c := ⟨s - 2 * i, by omega⟩
      have hc : 2 * i + c - 2 * i = c := by omega
      rw [hc]
      simp only [lsim, if_pos (show c ≤ 2 by omega)]
      rw [ih (by omega) (2 * i + c), if_pos hs, hc]
      cases hr : (gadgetType K (t + 1) c).readsNbr
      · exact eval_irrel hr _ _ _
      · have := gadget_reads K (t + 1) (by omega) c (by omega) hr
        have hn : nbr (t + 1) (2 * i + c) = 2 * i + nbr (t + 1) c := by
          unfold nbr; split <;> omega
        rw [hn, ih (by omega) (2 * i + nbr (t + 1) c),
          if_pos (by unfold nbr; split <;> omega), show 2 * i + nbr (t + 1) c - 2 * i =
            nbr (t + 1) c by omega]
    · rw [if_neg hs, if_neg hs]
      simp only [CellType.eval]
      rw [ih (by omega) s, if_neg hs]

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

theorem height_even (I : Instr) : I.height % 2 = 0 := by
  cases I <;> simp [Instr.height, Instr.kind, GKind.height]

theorem run_other (I : Instr) (z : ℕ → Bool) (m : ℕ) (h1 : m ≠ I.slot) (h2 : m ≠ I.slot + 1) :
    I.run z m = z m := by
  cases I <;> simp only [Instr.slot] at h1 h2 <;> simp [Instr.run, h1, h2]

theorem gadget_step (A : NorOrArray) (I : Instr) (t0 : ℕ) (ht0 : t0 % 2 = 0) (z : ℕ → Bool)
    (hz : A.val t0 = encodeSlots z)
    (htype : ∀ t s, 1 ≤ t → t ≤ I.height →
      A.type (t0 + t) s = if 2 * I.slot ≤ s ∧ s ≤ 2 * I.slot + 2 then
        gadgetType I.kind t (s - 2 * I.slot) else CellType.C) :
    A.val (t0 + I.height) = encodeSlots (I.run z) := by
  funext s
  rw [gadget_run A I.kind I.slot t0 ht0 htype I.height le_rfl s]
  have hw : ∀ c, c ≤ 3 → A.val t0 (2 * I.slot + c) =
      tri (z I.slot) (z (I.slot + 1)) (A.val t0 (2 * I.slot + 3)) c := by
    intro c hc
    rw [hz]
    interval_cases c <;> simp [encodeSlots, tri] <;> omega
  split
  · next hs =>
    obtain ⟨c, rfl⟩ : ∃ c, s = 2 * I.slot + c := ⟨s - 2 * I.slot, by omega⟩
    have hc2 : c ≤ 2 := by omega
    rw [show 2 * I.slot + c - 2 * I.slot = c by omega,
      lsim_congr I.kind _ _ hw I.height c (by omega)]
    obtain ⟨g0, g1, g2⟩ :=
      gadget_values I.kind (z I.slot) (z (I.slot + 1)) (A.val t0 (2 * I.slot + 3))
    have e : I.height = I.kind.height := rfl
    rw [e]
    interval_cases c
    · rw [g0]
      cases I <;> simp [encodeSlots, Instr.run, Instr.slot, Instr.kind]
    · rw [g1]; simp [encodeSlots]
    · rw [g2]
      have : (2 * I.slot + 2) / 2 = I.slot + 1 := by omega
      cases I <;> simp only [Instr.slot] at this <;>
        simp [encodeSlots, Instr.run, Instr.slot, Instr.kind, this]
  · next hs =>
    rw [hz]
    unfold encodeSlots
    split
    · next he =>
      exact (run_other I z (s / 2) (by omega) (by omega)).symm
    · rfl

/-- **Lemma 7.5 (core).** The array of a slot program, started from the encoding of `z` at an
even layer, ends with the encoding of the result of the program. -/
theorem prog_run (A : NorOrArray) :
    ∀ (P : List Instr) (t0 : ℕ) (z : ℕ → Bool), t0 % 2 = 0 → A.val t0 = encodeSlots z →
      (∀ t s, 1 ≤ t → t ≤ progHeight P → A.type (t0 + t) s = progType P t s) →
      A.val (t0 + progHeight P) = encodeSlots (runProg P z) := by
  intro P
  induction P with
  | nil => intro t0 z _ hz _; simpa [progHeight, runProg] using hz
  | cons I P ih =>
    intro t0 z ht0 hz htype
    have hP : progHeight (I :: P) = I.height + progHeight P := by simp [progHeight]
    have h1 : A.val (t0 + I.height) = encodeSlots (I.run z) := by
      apply gadget_step A I t0 ht0 z hz
      intro t s ht1 ht
      rw [htype t s ht1 (by omega)]
      simp [progType, ht]
    rw [hP, ← Nat.add_assoc, runProg_cons]
    apply ih (t0 + I.height) (I.run z) (by have := height_even I; omega) h1
    intro t s ht1 ht
    rw [show t0 + I.height + t = t0 + (I.height + t) by omega,
      htype _ s (by omega) (by omega)]
    simp [progType, show ¬ (I.height + t ≤ I.height) by omega]

theorem progHeight_append (P Q : List Instr) :
    progHeight (P ++ Q) = progHeight P + progHeight Q := by
  simp [progHeight]

theorem progType_reads :
    ∀ (P : List Instr) (t s : ℕ), 1 ≤ t → t ≤ progHeight P →
      (progType P t s).readsNbr = true →
      ∃ I ∈ P, 2 * I.slot ≤ s ∧ s ≤ 2 * I.slot + 2 ∧
        (t % 2 = 1 → 2 * I.slot + 1 ≤ s) ∧ (t % 2 = 0 → s ≤ 2 * I.slot + 1) := by
  intro P
  induction P with
  | nil => intro t s _ _ h; simp [progType, CellType.readsNbr] at h
  | cons I P ih =>
    intro t s ht1 ht h
    have hP : progHeight (I :: P) = I.height + progHeight P := by simp [progHeight]
    have hh : I.height ≤ 8 := height_le I.kind
    have he := height_even I
    simp only [progType] at h
    split at h
    · next hti =>
      split at h
      · next hs =>
        have := gadget_reads I.kind t (by omega) (s - 2 * I.slot) (by omega) h
        exact ⟨I, List.mem_cons_self, hs.1, hs.2, fun h1 => by have := this.1 h1; omega,
          fun h0 => by have := this.2 h0; omega⟩
      · simp [CellType.readsNbr] at h
    · next hti =>
      obtain ⟨J, hJ, h1, h2, h3, h4⟩ := ih (t - I.height) s (by omega) (by omega) h
      exact ⟨J, List.mem_cons_of_mem _ hJ, h1, h2, fun h' => h3 (by omega),
        fun h' => h4 (by omega)⟩

theorem mem_swapsDown {a g : ℕ} {I : Instr} (h : I ∈ swapsDown a g) : ∃ m < g, I = Instr.swap m := by
  induction g with
  | zero => simp [swapsDown] at h
  | succ g ih =>
    simp only [swapsDown] at h
    split at h
    · simp at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact ⟨g, by omega, rfl⟩
      · obtain ⟨m, hm, rfl⟩ := ih h; exact ⟨m, by omega, rfl⟩

theorem mem_swapsUp {a g : ℕ} {I : Instr} (h : I ∈ swapsUp a g) : ∃ m < g, I = Instr.swap m := by
  induction g with
  | zero => simp [swapsUp] at h
  | succ g ih =>
    simp only [swapsUp] at h
    split at h
    · simp at h
    · rcases List.mem_append.1 h with h | h
      · obtain ⟨m, hm, rfl⟩ := ih h; exact ⟨m, by omega, rfl⟩
      · simp at h; exact ⟨g, by omega, h⟩

theorem mem_moveCopy {a g : ℕ} (hag : a < g) {I : Instr} (h : I ∈ moveCopy a g) :
    I.slot < g := by
  unfold moveCopy at h
  rcases List.mem_append.1 h with h | h
  · obtain ⟨m, hm, rfl⟩ := mem_swapsDown h; exact hm
  · rcases List.mem_cons.1 h with rfl | h
    · exact hag
    · obtain ⟨m, hm, rfl⟩ := mem_swapsUp h; exact hm

/-- All instructions of the slot program act on slots `i, i+1` with `i ≤ G`, so only slots
`0, …, G+1` are used. -/
theorem slotProg_slot (C : NorCircuit) (hC : C.Valid) :
    ∀ I ∈ slotProg C, I.slot ≤ C.G := by
  intro I hI
  simp only [slotProg, List.mem_flatMap, List.mem_range] at hI
  obtain ⟨k, hk, hI⟩ := hI
  obtain ⟨ha, hb⟩ := hC.2 (k + 2) (by omega) (by omega)
  unfold gateProg at hI
  rcases List.mem_append.1 hI with hI | hI
  · rcases List.mem_append.1 hI with hI | hI
    · have := mem_moveCopy (show min (C.a (k + 2)) (C.b (k + 2)) < k + 2 by omega) hI; omega
    · have := mem_moveCopy (show max (C.a (k + 2)) (C.b (k + 2)) < k + 2 + 1 by omega) hI
      omega
  · simp at hI; subst hI; simp [Instr.slot]; omega

theorem slotProg_height (C : NorCircuit) (hC : C.Valid) : 1 ≤ progHeight (slotProg C) := by
  have hG := hC.1
  obtain ⟨m, hm⟩ : ∃ m, C.G - 1 = m + 1 := ⟨C.G - 2, by omega⟩
  unfold slotProg
  rw [hm, List.range_succ_eq_map, List.flatMap_cons, progHeight_append]
  have : progHeight (gateProg C (0 + 2)) ≥ 4 := by
    unfold gateProg
    rw [progHeight_append]
    simp [progHeight, Instr.height, Instr.kind, GKind.height]
  omega

/-- The array of Lemma 7.5 for a NOR circuit: width `2M = 2(G+2)`, layer `0` equal to
`(1, 0, …, 0)`, and the gadgets of the slot program of Lemma 7.3 in turn. -/
def circuitArray (C : NorCircuit) : NorOrArray where
  k := 2 * (C.G + 2)
  d := progHeight (slotProg C)
  init := fun s => decide (s = 0)
  type := progType (slotProg C)

theorem circuitArray_valid (C : NorCircuit) (hC : C.Valid) : (circuitArray C).Valid := by
  refine ⟨by simp [circuitArray]; omega, slotProg_height C hC, ?_⟩
  intro t s ht1 ht hs hr
  obtain ⟨I, hI, h1, h2, h3, h4⟩ := progType_reads (slotProg C) t s ht1 ht hr
  have := slotProg_slot C hC I hI
  simp only [circuitArray] at hs ⊢
  exact ⟨fun h => by have := h3 h; omega, fun h => by have := h4 h; omega⟩

/-- **Lemma 7.5.** The output cell `(d, 2G)` of the array of a NOR circuit holds `w_G`. -/
theorem circuitArray_val (C : NorCircuit) (hC : C.Valid) :
    (circuitArray C).val (circuitArray C).d (2 * C.G) = C.wire C.G := by
  have h := prog_run (circuitArray C) (slotProg C) 0 (fun m => decide (m = 0)) rfl
    (by
      funext s
      simp only [NorOrArray.val, circuitArray, encodeSlots]
      split <;> simp <;> omega)
    (by intro t s _ _; simp [circuitArray])
  simp only [Nat.zero_add] at h
  have : (circuitArray C).d = progHeight (slotProg C) := rfl
  rw [this, h]
  simp only [encodeSlots, show 2 * C.G % 2 = 0 by omega, if_true,
    show 2 * C.G / 2 = C.G by omega]
  exact run_slotProg C hC C.G le_rfl

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
  have hA := circuitArray_valid C hC
  have hs : 2 * C.G < (circuitArray C).k := by simp [circuitArray]
  obtain ⟨h1, -, h3, h4, h5⟩ := serpentine_two_pages (circuitArray C) hA (2 * C.G) hs
  exact ⟨h1, by rw [h3, circuitArray_val C hC], h4, h5⟩

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
  intro vt
  simp only [vt, NorOrArray.val]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [h] <;>
    rcases Nat.mod_two_eq_zero_or_one t with ht | ht <;>
    simp [CellType.eval, nor, ht, show (t + 1) % 2 = 1 - t % 2 by omega] <;>
    cases A.val t s <;> cases A.val t (nbr (t + 1) s) <;> simp

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
  intro X
  simp only [X]
  unfold nbr at hu hu'
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · have h' : (t - 1) % 2 = 1 := by omega
    simp only [h, h'] at hu hu' ⊢
    simp at hu hu'
    rw [abs_eq (by norm_num)]
    omega
  · have h' : (t - 1) % 2 = 0 := by omega
    simp only [h, h'] at hu hu' ⊢
    simp at hu hu'
    rw [abs_eq (by norm_num)]
    omega

end GC.SeqNORNormalForms
