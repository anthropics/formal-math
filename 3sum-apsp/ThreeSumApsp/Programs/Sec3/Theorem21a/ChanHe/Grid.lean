/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Round

/-!
# The reduction from 3SUM to Convolution-3SUM: the loop over the splittings.  row and grid

A step added to the reduction of [CH20, Theorem 5.1], one of the reductions behind Theorem 21(a):
the reduction from 3SUM on one set to the version with three sets, by the first binary digit in
which two labels differ (the label of a value x is x + V).  Below, "round" is the routine of that
name, which handles one splitting; a round of a loop is called so only in the names rowRound and
gridRound and in their lemmas.

* row runs through the splittings `(β, β', v)` for a fixed `β` and adds up the answers of round
  (`row_spec`; a round of its loop is `rowRound_ends`, and what it does to the sum is
  `RowSum.succ`).
* grid runs through `β` and returns 1 if some row has a positive sum (`grid_spec`,
  `gridRound_ends`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset

variable {lim : Limits} {P : Program}

/-! ## The procedures -/

namespace Row

/-- The local variables of row: the arguments β, nd, val, bt, Λ, A, n, f, cx, fr; the sum; β'; and
the last answer.  Local 0 also takes the result. -/
abbrev Beta : ℕ := 0
@[inherit_doc Beta] abbrev Result : ℕ := 0
@[inherit_doc Beta] abbrev NumValues : ℕ := 1
@[inherit_doc Beta] abbrev Val : ℕ := 2
@[inherit_doc Beta] abbrev Table : ℕ := 3
@[inherit_doc Beta] abbrev Digits : ℕ := 4
@[inherit_doc Beta] abbrev Out0 : ℕ := 5
@[inherit_doc Beta] abbrev MaxLen : ℕ := 6
@[inherit_doc Beta] abbrev Levels : ℕ := 7
@[inherit_doc Beta] abbrev Params : ℕ := 8
@[inherit_doc Beta] abbrev Free : ℕ := 9
@[inherit_doc Beta] abbrev Total : ℕ := 10
@[inherit_doc Beta] abbrev Beta' : ℕ := 11
@[inherit_doc Beta] abbrev Ans : ℕ := 12

end Row

open Row in
/-- A round of row: the answers for (β, β', false) and (β, β', true) are added to the sum. -/
def rowRound (pRound : ℕ) : Stmt :=
  .call pRound
    [v Beta, v Beta', k 0,
      v NumValues, v Val, v Table, v Digits, v Out0, v MaxLen, v Levels, v Params, v Free] Ans ;;
  .set Total (v Total +' v Ans) ;;
  .call pRound
    [v Beta, v Beta', k 1,
      v NumValues, v Val, v Table, v Digits, v Out0, v MaxLen, v Levels, v Params, v Free] Ans ;;
  .set Total (v Total +' v Ans)

open Row in
/-- row(β, nd, val, bt, Λ, A, n, f, cx, fr): sum := 0; a round for each β' < Λ; return the sum. -/
def rowBody (pRound : ℕ) : Stmt :=
  .set Total (k 0) ;;
  .for Beta' (v Digits) (rowRound pRound) ;;
  .set Result (v Total)

namespace Grid

/-- The local variables of grid: the arguments nd, val, bt, Λ, A, n, f, cx, fr; the answer so far;
β; and the sum of the last row.  Local 0 also takes the result. -/
abbrev NumValues : ℕ := 0
@[inherit_doc NumValues] abbrev Result : ℕ := 0
@[inherit_doc NumValues] abbrev Val : ℕ := 1
@[inherit_doc NumValues] abbrev Table : ℕ := 2
@[inherit_doc NumValues] abbrev Digits : ℕ := 3
@[inherit_doc NumValues] abbrev Out0 : ℕ := 4
@[inherit_doc NumValues] abbrev MaxLen : ℕ := 5
@[inherit_doc NumValues] abbrev Levels : ℕ := 6
@[inherit_doc NumValues] abbrev Params : ℕ := 7
@[inherit_doc NumValues] abbrev Free : ℕ := 8
@[inherit_doc NumValues] abbrev Ans : ℕ := 9
@[inherit_doc NumValues] abbrev Beta : ℕ := 10
@[inherit_doc NumValues] abbrev Total : ℕ := 11

end Grid

open Grid in
/-- A round of grid: if the sum of row β is positive, the answer is 1. -/
def gridRound (pRow : ℕ) : Stmt :=
  .call pRow
    [v Beta, v NumValues, v Val, v Table, v Digits, v Out0, v MaxLen, v Levels, v Params, v Free]
    Total ;;
  .ite (k 0 <' v Total) (.set Ans (k 1)) .skip

open Grid in
/-- grid(nd, val, bt, Λ, A, n, f, cx, fr): answer := 0; a round for each β < Λ; return the
answer. -/
def gridBody (pRow : ℕ) : Stmt :=
  .set Ans (k 0) ;;
  .for Beta (v Digits) (gridRound pRow) ;;
  .set Result (v Ans)

/-! ## What the two routines share -/

/-- What row and grid assume provides a word for 2Λ + 16, one more level of calls, and what the
routine one level below assumes. -/
theorem GridPre.down {r : ℕ → ℕ → Need} {a : FrontArgs} {d f e : ℕ}
    (H : GridPre lim r a f (e + 1) d) :
    2 * (a.Λ : ℤ) + 16 ≤ lim.word ∧ d < lim.depth ∧ GridPre lim r a f e (d + 1) := by
  have hV := H.V_pos
  have hword := H.ok.word
  have hdepth := H.ok.depth
  have hlog := Nat.log_lt_self 2 (x := 2 * a.V) (by omega)
  simp only [gridNeed] at hword hdepth
  push_cast at hword
  have hlam : a.Λ ≤ 2 * a.V := by rw [H.lam, Lam]; omega
  exact ⟨by omega, by omega, H.V_pos, H.m_pos, H.lam, H.primes,
    H.ok.mono (by simp [gridNeed]) (by simp [gridNeed]) (by simp only [gridNeed]; omega)⟩

/-! ## row -/

/-- What is known about the sum after the splittings (β, β', v) with β' < i: it lies between 0 and
2i, and it is positive exactly if one of the answers was yes. -/
structure RowSum (S : ℕ → Bool → Prop) (i : ℕ) (acc : ℤ) : Prop where
  nonneg : 0 ≤ acc
  le : acc ≤ 2 * (i : ℤ)
  pos_iff : 0 < acc ↔ ∃ β' < i, ∃ v, S β' v

/-- Adding the answers for (i, false) and (i, true) takes `RowSum S i` to `RowSum S (i + 1)`. -/
theorem RowSum.succ {S : ℕ → Bool → Prop} {i : ℕ} {acc : ℤ} (h : RowSum S i acc) :
    RowSum S (i + 1) (acc + flag (S i false) + flag (S i true)) := by
  have hlow := h.nonneg
  have hhigh := h.le
  have hfalse := flag_mem (S i false)
  have htrue := flag_mem (S i true)
  have hsplit : (∃ β' < i + 1, ∃ v, S β' v) ↔ (∃ β' < i, ∃ v, S β' v) ∨ S i false ∨ S i true := by
    rw [Nat.exists_lt_succ_right, Bool.exists_bool]
  refine ⟨by omega, by push_cast; omega, ?_⟩
  rw [hsplit, ← h.pos_iff]
  by_cases hf : S i false <;> by_cases ht : S i true <;>
    simp [flag_of, flag_of_not, hf, ht] <;> omega

section row

variable {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {a : FrontArgs} {d f β pRound : ℕ} {μ : ℕ → ℤ}

/-- The state before round i of the loop of row: the locals are the arguments, the sum, i, and the
last answer; the sum is as `RowSum` says; and below the free pointer only the 3n cells from A have
changed. -/
def RowInv (μ : ℕ → ℤ) (a : FrontArgs) (f β i : ℕ) (σ : State) : Prop :=
  ∃ (acc x : ℤ) (μ' : ℕ → ℤ), RowSum (a.Yes f β) i acc ∧ KeptBut μ μ' a.fr a.A (3 * a.n) ∧
    σ = ⟨frame ((β : ℤ) :: a.vals f ++ [acc, (i : ℤ), x]), μ'⟩

/-- **A round of row** adds the answers for (β, β', false) and (β, β', true) to the sum. -/
theorem rowRound_ends (hRound : RoundSpec lim P pRound T r) (hmem : FrontMem μ a) (hβ : β < a.Λ)
    (H : GridPre lim r a f 1 d) {i : ℕ} (hi : i < a.Λ) {σ : State} (hσ : RowInv μ a f β i σ) :
    Ends lim P d (rowRound pRound) σ (2 * tRound T a.n a.V a.m a.np f + 36) fun σ' =>
      σ'.loc Row.Beta' = i ∧ RowInv μ a f β (i + 1)
        { σ' with loc := Function.update σ'.loc Row.Beta' ((i : ℤ) + 1) } := by
  obtain ⟨acc, x, μ', hsum, kept, rfl⟩ := hσ
  obtain ⟨hword, hd, H'⟩ := H.down
  have hfalse := flag_mem (a.Yes f β i false)
  have htrue := flag_mem (a.Yes f β i true)
  have hlow := hsum.nonneg
  have hhigh := hsum.le
  -- x := round(β, β', 0, nd, val, bt, Λ, A, n, f, cx, fr)
  light_call (hRound a f β i false μ' (hmem.keptBut kept) hβ hi (d + 1) H')
    with _ μ₁ ⟨rfl, kept₁⟩
  -- sum := sum + x
  light_set (acc + flag (a.Yes f β i false))
  -- x := round(β, β', 1, nd, val, bt, Λ, A, n, f, cx, fr)
  light_call (hRound a f β i true μ₁ (hmem.keptBut (kept.trans kept₁)) hβ hi (d + 1) H')
    with _ μ₂ ⟨rfl, kept₂⟩
  -- sum := sum + x
  light_set (acc + flag (a.Yes f β i false) + flag (a.Yes f β i true))
  exact ⟨by simp, _, _, μ₂, hsum.succ, kept.trans (kept₁.trans kept₂),
      by rw [update_frame_setLocal]; rfl⟩

/-- **row** meets its specification. -/
theorem row_spec {p : ℕ} (hP : P[p]? = some (rowBody pRound))
    (hRound : RoundSpec lim P pRound T r) : RowSpec lim P p T r := by
  intro a f β μ hmem hβ d H
  refine .of_body hP ?_
  have hword := H.down.1
  -- sum := 0
  refine Ends.setToThen 0 ?_ (hT := by simp [tRow])
  -- for β' < Λ
  refine Ends.next _ (Ends.for (RowInv μ a f β) a.Λ (2 * tRound T a.n a.V a.m a.np f + 36)
    ?start ?round ?done ?bound (hT := le_rfl)) (by simp [tRow]; ring_nf; omega)
  case start =>
    -- The last local has not been written yet and is 0.
    exact ⟨0, 0, μ, ⟨le_rfl, by simp, by simp⟩, .refl,
      by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl⟩
  case round => exact fun i σ hi _ hσ => rowRound_ends hRound hmem hβ H hi hσ
  case done =>
    rintro _ - ⟨acc, x, μ', hsum, kept, rfl⟩
    -- return the sum
    exact Ends.setTo acc
      ⟨by simpa using hsum.nonneg, by simpa using hsum.le, by simpa using hsum.pos_iff, kept⟩
      (hT := by simp [tRow]; ring_nf; omega)
  case bound =>
    rintro i _ - - ⟨acc, x, μ', -, -, rfl⟩
    simp

end row

/-! ## grid -/

section grid

variable {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {a : FrontArgs} {d f pRow : ℕ} {μ : ℕ → ℤ}

/-- Some splitting (β, β', v) of row β gives a yes-instance. -/
abbrev FrontArgs.RowYes (a : FrontArgs) (f β : ℕ) : Prop := ∃ β' < a.Λ, ∃ v, a.Yes f β β' v

/-- The state before round i of the loop of grid: the locals are the arguments, the answer so far,
i, and the sum of the last row; the answer tells whether one of the rows below i had a positive sum;
and below the free pointer only the 3n cells from A have changed. -/
def GridInv (μ : ℕ → ℤ) (a : FrontArgs) (f i : ℕ) (σ : State) : Prop :=
  ∃ (x : ℤ) (μ' : ℕ → ℤ), KeptBut μ μ' a.fr a.A (3 * a.n) ∧
    σ = ⟨frame (a.vals f ++ [flag (∃ β < i, a.RowYes f β), (i : ℤ), x]), μ'⟩

/-- **A round of grid** asks for the sum of row i and sets the answer to 1 if it is positive. -/
theorem gridRound_ends (hRow : RowSpec lim P pRow T r) (hmem : FrontMem μ a)
    (H : GridPre lim r a f 2 d) {i : ℕ} (hi : i < a.Λ) {σ : State} (hσ : GridInv μ a f i σ) :
    Ends lim P d (gridRound pRow) σ (tRow T a.n a.V a.m a.np f a.Λ + 18) fun σ' =>
      σ'.loc Grid.Beta = i ∧ GridInv μ a f (i + 1)
        { σ' with loc := Function.update σ'.loc Grid.Beta ((i : ℤ) + 1) } := by
  obtain ⟨x, μ', kept, rfl⟩ := hσ
  obtain ⟨hword, hd, H'⟩ := H.down
  -- sum := row(β, nd, val, bt, Λ, A, n, f, cx, fr)
  light_call (hRow a f i μ' (hmem.keptBut kept) hi (d + 1) H') with sum μ₁ ⟨-, -, hpos, kept₁⟩
  -- if 0 < sum then answer := 1
  refine Ends.iteLast (fun hyes => ?_) (fun hno => ?_)
  · have hrow := hpos.1 (by simpa using hyes)
    exact Ends.setTo 1 ⟨by simp, sum, μ₁, kept.trans kept₁, by
      rw [update_frame_setLocal, flag_of (Nat.exists_lt_succ_right.2 (Or.inr hrow))]; rfl⟩
  · have hrow : ¬ a.RowYes f i := fun h => hno (by simpa using hpos.2 h)
    refine Ends.skip ⟨by simp, sum, μ₁, kept.trans kept₁, ?_⟩
    rw [update_frame_setLocal, flag_congr (Nat.exists_lt_succ_right.trans (or_iff_left hrow))]
    rfl

/-- **grid** meets its specification. -/
theorem grid_spec {p : ℕ} (hP : P[p]? = some (gridBody pRow)) (hRow : RowSpec lim P pRow T r) :
    GridSpec lim P p T r := by
  intro a f μ hmem d H
  refine .of_body hP ?_
  have hword := H.down.1
  -- answer := 0
  refine Ends.setToThen 0 ?_ (hT := by simp [tGrid])
  -- for β < Λ
  refine Ends.next _ (Ends.for (GridInv μ a f) a.Λ (tRow T a.n a.V a.m a.np f a.Λ + 18)
    ?start ?round ?done ?bound (hT := le_rfl)) (by simp [tGrid]; ring_nf; omega)
  case start =>
    exact ⟨0, μ, .refl, by
      rw [update_frame_setLocal, ← frame_append_zeros _ 1, flag_of_not (by simp)]; rfl⟩
  case round => exact fun i σ hi _ hσ => gridRound_ends hRow hmem H hi hσ
  case done =>
    rintro _ - ⟨x, μ', kept, rfl⟩
    -- return the answer
    exact Ends.setTo (flag (∃ β < a.Λ, a.RowYes f β)) ⟨rfl, kept⟩
      (hT := by simp [tGrid]; ring_nf; omega)
  case bound =>
    rintro i _ - - ⟨x, μ', -, rfl⟩
    simp

end grid

end Light.Sec3.ChanHe
