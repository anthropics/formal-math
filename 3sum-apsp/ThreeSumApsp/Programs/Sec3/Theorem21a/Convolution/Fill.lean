/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.NextPair
public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Spec.Sec3.Theorem21a.Convolution

/-!
# Convolution-3SUM from Exact Triangle: writing one instance

Theorem 21(a), after [VW13, Theorem 4.3].  convFill(t, N, s, F, x, ab, bc,
ac) writes the three weight matrices of instance number s of the reduction, each of t² cells, row
by row, to ab, bc, ac: w(a,b) = x[a t + b], w(b,c) = x[c t + s - b], w(a,c) = -x[(a + c) t + s], and
the filler F where the index is out of range.  One loop runs through the t² cells; it keeps the
number of the cell, its row and its column in three counters.

The proof follows the text.  pickStmt reads a cell of x or the filler (`pick_runs`); putStmt
computes an index, picks, and stores (`put_runs`); fillCells does this for the three matrices
(`cells_runs`); then the counters move on.  After q rounds the memory is `A.filled μ q`: the first q
cells of each matrix have been written (`filled_succ` is one round).  The result is
`convFill_meets`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

namespace ConvFill

/-- The local variables of convFill: the arguments t (Side), N (Len), s (Inst), F (Filler), x
(Input), ab, bc, ac (MatAB, MatBC, MatAC); the row, the column and the number of the current cell
(Row, Col, Cell); an index into x and what is picked there (Index, Value); -F (NegFiller) and t²
(Area). -/
abbrev Side : ℕ := 0
@[inherit_doc Side] abbrev Len : ℕ := 1
@[inherit_doc Side] abbrev Inst : ℕ := 2
@[inherit_doc Side] abbrev Filler : ℕ := 3
@[inherit_doc Side] abbrev Input : ℕ := 4
@[inherit_doc Side] abbrev MatAB : ℕ := 5
@[inherit_doc Side] abbrev MatBC : ℕ := 6
@[inherit_doc Side] abbrev MatAC : ℕ := 7
@[inherit_doc Side] abbrev Row : ℕ := 8
@[inherit_doc Side] abbrev Col : ℕ := 9
@[inherit_doc Side] abbrev Cell : ℕ := 10
@[inherit_doc Side] abbrev Index : ℕ := 11
@[inherit_doc Side] abbrev Value : ℕ := 12
@[inherit_doc Side] abbrev NegFiller : ℕ := 13
@[inherit_doc Side] abbrev Area : ℕ := 14

end ConvFill

open ConvFill

/-- Value := x[Index] if 0 ≤ Index < N, and the content of local f, a filler, if not. -/
def pickStmt (f : ℕ) : Stmt :=
  .set Value (v f) ;;
  .ite (v Index <' k 0) .skip
    (.ite (v Index <' v Len) (.set Value (M (v Input +' v Index))) .skip)

/-- Computes the index ze, picks the cell there (or the filler in local f), and stores it, or minus
it if neg is set, into the current cell of the matrix whose address is in local dst. -/
def putStmt (ze : Expr) (f dst : ℕ) (neg : Bool) : Stmt :=
  .set Index ze ;; pickStmt f ;; .store (v dst +' v Cell) (if neg then k 0 -' v Value else v Value)

/-- The current cell of each of the three matrices. -/
def fillCells : Stmt :=
  putStmt (v Cell) Filler MatAB false ;;
  putStmt (v Col *' v Side +' v Inst -' v Row) Filler MatBC false ;;
  putStmt ((v Row +' v Col) *' v Side +' v Inst) NegFiller MatAC true

/-- One round: the current cell of each matrix, and on to the next cell. -/
def fillRound : Stmt :=
  fillCells ;; .set Cell (v Cell +' k 1) ;; nextPair Row Col Side

/-- convFill(t, N, s, F, x, ab, bc, ac). -/
def convFillBody : Stmt :=
  .set NegFiller (k 0 -' v Filler) ;;
  .set Area (v Side *' v Side) ;;
  .set Row (k 0) ;;
  .set Col (k 0) ;;
  .set Cell (k 0) ;;
  .while (v Cell <' v Area) fillRound

/-- The time of convFill. -/
def convFillTime (t : ℕ) : ℕ := 106 * (t * t) + 18

namespace ConvFill

/-! ## Picking and storing

The two lemmas of this section have the form of the rules for blocks: if R holds of the state in
which the part ends, then the part runs, within the limits, into R. -/

section parts

variable {μ : ℕ → ℤ} {R : State → Prop} {N x : ℕ} {F : ℤ} {X : List ℤ}

/-- The list X of N numbers stands at x, within the memory, and addresses fit in a word. -/
structure InputAt (lim : Limits) (μ : ℕ → ℤ) (x N : ℕ) (X : List ℤ) : Prop where
  seg : Seg μ x X
  len : X.length = N
  space : x + N ≤ lim.space
  addr : (lim.space : ℤ) ≤ lim.word

/-- pickStmt puts `cellOr N F X z` into Value and changes nothing else. -/
private theorem pick_runs {loc : ℕ → ℤ} {f : ℕ} (z : ℤ)
    (h : R ⟨Function.update loc Value (cellOr N F X z), μ⟩) (hX : InputAt lim μ x N X)
    (hz : loc Index = z) (hN : loc Len = N) (hx : loc Input = x) (hf : loc f = F) :
    (pickStmt f).Runs lim ⟨loc, μ⟩ R := by
  obtain ⟨hseg, hlen, hspace, haddr⟩ := hX
  unfold pickStmt
  -- Value := f
  refine .seq ⟨trivial, ?_⟩
  by_cases hneg : z < 0
  · -- if Index < 0
    rw [cellOr_of_not (by omega)] at h
    exact .ite_pos ⟨trivial, by simpa [hf] using h⟩ (by simpa [hz] using hneg) (by simp; omega)
  refine .ite_neg ?_ (by simpa [hz] using hneg) (by simp; omega)
  by_cases hlt : z < N
  · -- if Index < N: Value := x[Index]
    obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.1 hneg)
    rw [cellOr_of_lt rfl (by omega), ← hseg.getD (by omega)] at h
    refine .ite_pos ⟨?_, by simpa [hz, hx] using h⟩ (by simpa [hz, hN] using hlt) (by simp)
    simp [hz, hx, Limits.Addr, abs_le]
    omega
  · rw [cellOr_of_not (by omega)] at h
    exact .ite_neg ⟨trivial, by simpa [hf] using h⟩ (by simpa [hz, hN] using hlt) (by simp)

/-- putStmt stores `cellOr N F X z`, or minus it, into cell q of the matrix at D.  Of the locals it
changes only Index and Value. -/
private theorem put_runs {l : List ℤ} {ze : Expr} {f dst : ℕ} {neg : Bool} (z : ℤ) (D q : ℕ)
    (h : R ⟨frame (setLocal (setLocal l Index z) Value (cellOr N F X z)),
      Function.update μ (D + q) (if neg then -cellOr N F X z else cellOr N F X z)⟩)
    (hX : InputAt lim μ x N X) (hD : D + q < lim.space) (hV : |cellOr N F X z| ≤ lim.word)
    (hze : ze.Gives lim ⟨frame l, μ⟩ z := by light_side)
    (hN : frame l Len = N := by rfl) (hx : frame l Input = x := by rfl)
    (hq : frame l Cell = q := by rfl) (hf : frame l f = F := by rfl)
    (hdst : frame l dst = D := by rfl)
    (hne : f ≠ Index ∧ dst ≠ Index ∧ dst ≠ Value := by decide) :
    (putStmt ze f dst neg).Runs lim ⟨frame l, μ⟩ R := by
  rw [← update_frame_setLocal, ← update_frame_setLocal] at h
  generalize frame l = loc at *
  obtain ⟨hfI, hdI, hdV⟩ := hne
  obtain ⟨hsafe, hval⟩ := hze
  have haddr := hX.addr
  unfold putStmt
  -- Index := ze
  refine .seq ⟨hsafe, ?_⟩
  -- Value := x[Index] or the filler
  refine .seq (pick_runs z ?_ hX (by simp [hval]) (by simpa using hN) (by simpa using hx)
    (by simpa [hfI] using hf))
  -- dst[Cell] := Value or -Value
  cases neg
  · refine ⟨?_, by simpa [hval, hdI, hdV, hdst, hq] using h⟩
    simp [hdI, hdV, hdst, hq, Limits.Addr, abs_le]
    omega
  · refine ⟨?_, by simpa [hval, hdI, hdV, hdst, hq] using h⟩
    rw [abs_le] at hV
    simp [hdI, hdV, hdst, hq, Limits.Addr, abs_le]
    omega

end parts

/-! ## The data and the memory -/

/-- The arguments of convFill, with the list X that stands at x. -/
structure Args : Type where
  t : ℕ
  N : ℕ
  s : ℕ
  F : ℤ
  x : ℕ
  ab : ℕ
  bc : ℕ
  ac : ℕ
  X : List ℤ

/-- What convFill assumes: there is at least one row; the input lies below the three matrices, which
follow each other within the memory; V bounds the input and the filler; words hold addresses, V and
the indices. -/
structure Ctx (lim : Limits) (μ : ℕ → ℤ) (A : Args) (V : ℕ) : Prop where
  side : 1 ≤ A.t
  addr : (lim.space : ℤ) ≤ lim.word
  input : Seg μ A.x A.X
  len : A.X.length = A.N
  belowAB : A.x + A.N ≤ A.ab
  belowBC : A.ab + A.t * A.t ≤ A.bc
  belowAC : A.bc + A.t * A.t ≤ A.ac
  space : A.ac + A.t * A.t ≤ lim.space
  inputLe : AbsLe A.X V
  fillerLe : |A.F| ≤ V
  valueLe : (V : ℤ) ≤ lim.word
  indexLe : ((2 * (A.t * A.t) + A.s + 1 : ℕ) : ℤ) ≤ lim.word

/-- What convFill achieves: the three matrices stand in the memory, and no cell before the first or
after the last of them has changed. -/
structure Post (A : Args) (μ μ' : ℕ → ℤ) : Prop where
  segAB : Seg μ' A.ab (convAB A.t A.N A.F A.X)
  segBC : Seg μ' A.bc (convBC A.t A.N A.s A.F A.X)
  segAC : Seg μ' A.ac (convAC A.t A.N A.s A.F A.X)
  same : SameOutside μ μ' A.ab (A.ac + A.t * A.t - A.ab)

/-- The index into x for cell q of the second matrix: c t + s - b for row b and column c. -/
def Args.idxBC (A : Args) (q : ℕ) : ℤ := ((q % A.t : ℕ) : ℤ) * A.t + A.s - ((q / A.t : ℕ) : ℤ)

/-- The index into x for cell q of the third matrix: (a + c) t + s for row a and column c. -/
def Args.idxAC (A : Args) (q : ℕ) : ℤ := (((q / A.t : ℕ) : ℤ) + ((q % A.t : ℕ) : ℤ)) * A.t + A.s

/-- The memory after q rounds: the first q cells of each matrix have been written. -/
def Args.filled (A : Args) (μ : ℕ → ℤ) (q : ℕ) : ℕ → ℤ :=
  wrote (wrote (wrote μ A.ab (fun i => cellOr A.N A.F A.X i) q)
    A.bc (fun i => cellOr A.N A.F A.X (A.idxBC i)) q)
    A.ac (fun i => -cellOr A.N (-A.F) A.X (A.idxAC i)) q

/-- The local variables before round q; z and w are what the last round has left in Index and
Value. -/
abbrev Args.locals (A : Args) (q : ℕ) (z w : ℤ) : List ℤ :=
  [A.t, A.N, A.s, A.F, A.x, A.ab, A.bc, A.ac, (q / A.t : ℕ), (q % A.t : ℕ), q, z, w, -A.F,
    (A.t * A.t : ℕ)]

section memory

variable {μ : ℕ → ℤ} {A : Args} {V q : ℕ}

/-- One round writes cell q of each matrix. -/
private theorem filled_succ (C : Ctx lim μ A V) (hq : q < A.t * A.t) :
    Function.update (Function.update (Function.update (A.filled μ q)
      (A.ab + q) (cellOr A.N A.F A.X q)) (A.bc + q) (cellOr A.N A.F A.X (A.idxBC q)))
      (A.ac + q) (-cellOr A.N (-A.F) A.X (A.idxAC q)) = A.filled μ (q + 1) := by
  obtain ⟨hBC, hAC⟩ := And.intro C.belowBC C.belowAC
  have offBC : A.ab + q < A.bc ∨ A.bc + q ≤ A.ab + q := by omega
  have offAC (y : ℕ) (hy : y ≤ A.bc + q) : y < A.ac ∨ A.ac + q ≤ y := by omega
  unfold Args.filled
  rw [update_wrote (offAC _ (by omega)), update_wrote offBC, wrote_succ,
    update_wrote (offAC _ le_rfl), wrote_succ, wrote_succ]

/-- No cell before the first matrix or after the last one changes. -/
private theorem sameOutside_filled (C : Ctx lim μ A V) (hq : q ≤ A.t * A.t) :
    SameOutside μ (A.filled μ q) A.ab (A.ac + A.t * A.t - A.ab) := fun b hb => by
  obtain ⟨hBC, hAC⟩ := And.intro C.belowBC C.belowAC
  have off (dst : ℕ) (h₁ : A.ab ≤ dst) (h₂ : dst ≤ A.ac) : b < dst ∨ dst + q ≤ b := by
    unfold Outside at hb
    omega
  rw [Args.filled, wrote_rest (off _ (by omega) le_rfl), wrote_rest (off _ (by omega) (by omega)),
    wrote_rest (off _ le_rfl (by omega))]

/-- At the end the three matrices stand in the memory. -/
private theorem post_filled (C : Ctx lim μ A V) : Post A μ (A.filled μ (A.t * A.t)) where
  segAB i hi := by
    obtain ⟨hBC, hAC⟩ := And.intro C.belowBC C.belowAC
    rw [length_convAB] at hi
    rw [Args.filled, wrote_rest (by omega), wrote_rest (by omega), wrote_done hi]
    simp [convAB]
  segBC i hi := by
    have hAC := C.belowAC
    rw [length_convBC] at hi
    rw [Args.filled, wrote_rest (by omega), wrote_done hi]
    simp [convBC, Args.idxBC]
  segAC i hi := by
    rw [length_convAC] at hi
    rw [Args.filled, wrote_done hi]
    simp [convAC, Args.idxAC]
  same := sameOutside_filled C le_rfl

/-- The input is still there after q rounds. -/
private theorem inputAt_filled (C : Ctx lim μ A V) (hq : q ≤ A.t * A.t) :
    InputAt lim (A.filled μ q) A.x A.N A.X where
  seg := C.input.keep (by light_keep [sameOutside_filled C hq, C.len, C.belowAB])
  len := C.len
  space := by
    have hAB := C.belowAB
    have hBC := C.belowBC
    have hAC := C.belowAC
    have hspace := C.space
    omega
  addr := C.addr

/-- A write to a cell of the matrices leaves the input alone. -/
private theorem InputAt.write {μ' : ℕ → ℤ} (hX : InputAt lim μ' A.x A.N A.X) (C : Ctx lim μ A V)
    {b : ℕ} (hb : A.ab ≤ b) (w : ℤ) : InputAt lim (Function.update μ' b w) A.x A.N A.X :=
  { hX with seg := hX.seg.update_out (Or.inr (by have := C.len; have := C.belowAB; omega)) w }

/-- What is picked fits in a word. -/
private theorem abs_cellOr_le_word (C : Ctx lim μ A V) (z : ℤ) :
    |cellOr A.N A.F A.X z| ≤ lim.word ∧ |cellOr A.N (-A.F) A.X z| ≤ lim.word :=
  ⟨(abs_cellOr_le C.inputLe C.fillerLe z).trans C.valueLe,
    (abs_cellOr_le C.inputLe (by rw [abs_neg]; exact C.fillerLe) z).trans C.valueLe⟩

end memory

/-! ## The loop -/

section loop

variable {μ : ℕ → ℤ} {A : Args} {V q : ℕ}

/-- The row and the column of a cell q < t² are below t, so the products that the two index
expressions form lie between 0 and 2t². -/
private structure IndexBounds (t q : ℕ) : Prop where
  row : 0 ≤ (q : ℤ) / t ∧ (q : ℤ) / t < t
  col : 0 ≤ (q : ℤ) % t ∧ (q : ℤ) % t < t
  colSide : 0 ≤ (q : ℤ) % t * t ∧ (q : ℤ) % t * t ≤ t * t
  sumSide : 0 ≤ ((q : ℤ) / t + (q : ℤ) % t) * t ∧ ((q : ℤ) / t + (q : ℤ) % t) * t ≤ 2 * (t * t)
  side : (t : ℤ) ≤ t * t

private theorem indexBounds {t : ℕ} (hq : q < t * t) : IndexBounds t q := by
  have hrow : q / t < t := Nat.div_lt_of_lt_mul hq
  have hcol : q % t < t := Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by simp [h] at hq)
  exact ⟨by exact_mod_cast And.intro (Nat.zero_le _) hrow,
    by exact_mod_cast And.intro (Nat.zero_le _) hcol,
    by exact_mod_cast And.intro (Nat.zero_le _) (Nat.mul_le_mul_right t hcol.le),
    by exact_mod_cast And.intro (Nat.zero_le _) ((Nat.mul_le_mul_right t
      (show q / t + q % t ≤ 2 * t by omega)).trans_eq (Nat.mul_assoc ..)),
    by exact_mod_cast Nat.le_mul_self t⟩

/-- fillCells writes cell q of each matrix. -/
private theorem cells_runs {R : State → Prop} (C : Ctx lim μ A V) (hq : q < A.t * A.t) (z w : ℤ)
    (h : R ⟨frame (A.locals q (A.idxAC q) (cellOr A.N (-A.F) A.X (A.idxAC q))),
      A.filled μ (q + 1)⟩) :
    fillCells.Runs lim ⟨frame (A.locals q z w), A.filled μ q⟩ R := by
  obtain ⟨hrow, hcol, hcolSide, hsumSide, hside⟩ := indexBounds hq
  obtain ⟨hBC, hAC, hspace⟩ := And.intro C.belowBC (And.intro C.belowAC C.space)
  have hidx := C.indexLe
  have hX := inputAt_filled C hq.le
  rw [← filled_succ C hq] at h
  unfold fillCells
  -- ab[q] := x[q] or F
  refine .seq (put_runs (q : ℤ) A.ab q ?_ hX (by omega) (abs_cellOr_le_word C _).1)
  -- bc[q] := x[c t + s - b] or F, for row b and column c
  refine .seq (put_runs (A.idxBC q) A.bc q ?_ (hX.write C (by omega) _) (by omega)
    (abs_cellOr_le_word C _).1 (by light_side [Args.idxBC]))
  -- ac[q] := -(x[(a + c) t + s] or -F), for row a and column c
  exact put_runs (A.idxAC q) A.ac q h ((hX.write C (by omega) _).write C (by omega) _) (by omega)
    (abs_cellOr_le_word C _).2 (by light_side [Args.idxAC])

/-- The invariant of the loop: before round q the counters stand at cell q, and the first q cells of
each matrix have been written. -/
def LoopInv (A : Args) (μ : ℕ → ℤ) (q : ℕ) (σ : State) : Prop :=
  ∃ z w : ℤ, σ = ⟨frame (A.locals q z w), A.filled μ q⟩

/-- Round q: cell q of each matrix is written, and the counters move on to cell q + 1. -/
private theorem round_spec (C : Ctx lim μ A V) (hq : q < A.t * A.t) (z w : ℤ) :
    Ends lim P d fillRound ⟨frame (A.locals q z w), A.filled μ q⟩ fillRound.blockCost
      (LoopInv A μ (q + 1)) := by
  have hidx := C.indexLe
  have hside : A.t ≤ A.t * A.t := Nat.le_mul_self _
  unfold fillRound
  -- the three cells
  refine Ends.next _ (Ends.block (cells_runs C hq z w ?_) le_rfl)
  -- Cell := Cell + 1
  refine Ends.setToThen ((q + 1 : ℕ) : ℤ) ?_ (by light_side) (by simp [nextPair])
  -- on to the next row and column
  exact Ends.nextPair ⟨_, _, rfl⟩ C.side (by omega) (by omega) rfl rfl rfl
    (hT := by simp [nextPair])

end loop

end ConvFill

/-- **convFill** writes the three matrices of instance number s, changes no cell before the first or
after the last of them, and takes O(t²) steps. -/
theorem convFill_meets {p : ℕ} (hp : P[p]? = some convFillBody) {μ : ℕ → ℤ} {A : Args} {V : ℕ}
    (C : Ctx lim μ A V) :
    Meets lim P p d [A.t, A.N, A.s, A.F, A.x, A.ab, A.bc, A.ac] μ (convFillTime A.t)
      fun _ μ' => Post A μ μ' := by
  have hidx := C.indexLe
  have hF := abs_le.1 (C.fillerLe.trans C.valueLe)
  refine .of_body hp ?_
  unfold convFillBody convFillTime
  -- NegFiller := 0 - Filler; Area := Side * Side
  light_set (-A.F)
  light_set (A.t * A.t : ℕ)
  -- Row := 0; Col := 0; Cell := 0
  light_set 0
  light_set 0
  light_set 0
  -- while Cell < Area
  refine Ends.whileConst (LoopInv A μ) (A.t * A.t) fillRound.blockCost ?start ?round ?done
    (by simp [fillRound, fillCells, putStmt, pickStmt, nextPair]; omega)
  case start => exact ⟨0, 0, by simp [Args.filled, wrote_zero, Args.locals]⟩
  case round =>
    rintro q _ hq ⟨z, w, rfl⟩
    exact ⟨by light_side, by light_side, round_spec C hq z w⟩
  case done =>
    rintro _ ⟨z, w, rfl⟩
    exact ⟨by light_side, by light_side, post_filled C⟩

end Light.Sec3
