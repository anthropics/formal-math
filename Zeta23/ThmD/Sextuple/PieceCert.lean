/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.Sextuple.KernelInterval

noncomputable section

namespace Zeta23.ThmD.Sextuple

open RatInterval

structure KernelCell where
  box : RatInterval
  turn : ℕ
  deriving DecidableEq, Repr

inductive PieceKind where
  | low
  | zero
  | numeric (cells : List KernelCell)
  deriving DecidableEq, Repr

/-- One piece of the one-dimensional lower envelope
`a + c * (x-q)^2 ≤ 2*k(x)^2`. -/
structure LowerPiece where
  box : RatInterval
  q : ℚ
  a : ℚ
  c : ℚ
  kind : PieceKind
  deriving DecidableEq, Repr

namespace LowerPiece

def model (p : LowerPiece) (x : ℝ) : ℝ := p.a + p.c * (x-p.q)^2

def absLower (i : RatInterval) : ℚ :=
  if 0 ≤ i.lo then i.lo else if i.hi ≤ 0 then -i.hi else 0

def cellModelUpper (p : LowerPiece) (cell : KernelCell) : ℚ :=
  p.a + p.c * (sq (sub cell.box ⟨p.q,p.q⟩)).hi

def cellCheck (p : LowerPiece) (cell : KernelCell) : Bool :=
  decide (2 ≤ cell.box.lo) && decide (cell.box.lo ≤ cell.box.hi) &&
  decide (|reducedMid (((scale (1/2) cell.box).lo +
    (scale (1/2) cell.box).hi)/2) cell.turn| ≤ 1) &&
  decide (0 < (kernelDenRange cell.box).lo) &&
  let kr := kernelRange cell.box cell.turn
  decide (cellModelUpper p cell ≤ 2 * absLower kr ^ 2)

def coverFrom (cur last : ℚ) : List KernelCell → Bool
  | [] => decide (cur = last)
  | cell :: cells => decide (cell.box.lo = cur) && decide (cell.box.lo ≤ cell.box.hi) &&
      coverFrom cell.box.hi last cells

def check (p : LowerPiece) : Bool :=
  decide (p.box.lo ≤ p.box.hi) && decide (0 ≤ p.a) && decide (0 ≤ p.c) &&
  match p.kind with
  | .low => decide (p.box.lo = 0) && decide (p.box.hi = 2) &&
      decide (p.a = 1/4) && decide (p.c = 0)
  | .zero => decide (p.a = 0) && decide (p.c = 0)
  | .numeric cells => decide (cells ≠ []) && coverFrom p.box.lo p.box.hi cells && cells.all (cellCheck p)

lemma absLower_nonneg (i : RatInterval) : 0 ≤ absLower i := by
  simp only [absLower]
  split_ifs <;> linarith

lemma absLower_le_abs {i : RatInterval} {x : ℝ} (hx : Holds i x) :
    ((absLower i : ℚ) : ℝ) ≤ |x| := by
  simp only [absLower]
  split_ifs with hlo hhi
  · exact hx.1.trans (le_abs_self x)
  · have hloR : ((i.lo : ℚ) : ℝ) < 0 := by exact_mod_cast lt_of_not_ge hlo
    have hhiR : ((i.hi : ℚ) : ℝ) ≤ 0 := by exact_mod_cast hhi
    rw [Rat.cast_neg, le_abs]
    exact Or.inr (neg_le_neg hx.2)
  · simp

lemma coverFrom_sound {cur last : ℚ} {cells : List KernelCell} {x : ℝ}
    (hne : cells ≠ []) (hc : coverFrom cur last cells = true)
    (hxlo : (cur:ℝ) ≤ x) (_hxhi : x ≤ (last:ℝ)) :
    ∃ cell ∈ cells, Holds cell.box x := by
  induction cells generalizing cur with
  | nil => exact (hne rfl).elim
  | cons cell cells ih =>
      simp only [coverFrom, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hfirst,hord⟩,hrest⟩ := hc
      subst cur
      by_cases hx : x ≤ (cell.box.hi : ℝ)
      · exact ⟨cell, by simp, hxlo, hx⟩
      · cases cells with
        | nil =>
            simp only [coverFrom, decide_eq_true_eq] at hrest
            have hlast : ((cell.box.hi : ℚ) : ℝ) = (last : ℝ) := by exact_mod_cast hrest
            exact (hx (by rw [hlast]; assumption)).elim
        | cons next rest =>
            obtain ⟨found,hmem,hholds⟩ := ih (by simp) hrest (le_of_not_ge hx)
            exact ⟨found, by simp [hmem], hholds⟩

lemma cellCheck_sound {p : LowerPiece} {cell : KernelCell} {x : ℝ}
    (_ha : 0 ≤ p.a) (hc : 0 ≤ p.c) (hcheck : cellCheck p cell = true)
    (hx : Holds cell.box x) : model p x ≤ 2 * mtKernel x ^ 2 := by
  simp only [cellCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨⟨hlo,hord⟩,hred⟩,hden⟩,hmodel⟩ := hcheck
  have hk := kernelRange_sound cell.turn hlo hord hred hden hx
  have habs := absLower_le_abs hk
  have habs0 : (0:ℝ) ≤ (absLower (kernelRange cell.box cell.turn) : ℚ) := by
    exact_mod_cast absLower_nonneg (kernelRange cell.box cell.turn)
  have hksq : ((absLower (kernelRange cell.box cell.turn) : ℚ) : ℝ)^2 ≤ mtKernel x ^ 2 := by
    rw [← sq_abs (mtKernel x)]
    exact pow_le_pow_left₀ habs0 habs 2
  have hdist := holds_sq (holds_sub hx (holds_point p.q))
  have hcR : (0:ℝ) ≤ (p.c : ℚ) := by exact_mod_cast hc
  have hupper : model p x ≤ (cellModelUpper p cell : ℚ) := by
    simp only [model, cellModelUpper, Rat.cast_add, Rat.cast_mul]
    simpa [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hdist.2 hcR) (p.a : ℝ)
  have hmodelR : ((cellModelUpper p cell : ℚ) : ℝ) ≤
      2 * ((absLower (kernelRange cell.box cell.turn) : ℚ) : ℝ)^2 := by
    exact_mod_cast hmodel
  exact hupper.trans (hmodelR.trans (by nlinarith))

lemma check_sound {p : LowerPiece} (hp : p.check = true) {x : ℝ} (hx : Holds p.box x) :
    p.model x ≤ 2 * mtKernel x ^ 2 := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨hord,ha⟩,hc⟩,hkind⟩ := hp
  cases hk : p.kind with
  | low =>
      simp only [hk, Bool.and_eq_true, decide_eq_true_eq] at hkind
      obtain ⟨⟨⟨hlo,hhi⟩,haeq⟩,hceq⟩ := hkind
      have hloR : ((p.box.lo : ℚ) : ℝ) = 0 := by exact_mod_cast hlo
      have hhiR : ((p.box.hi : ℚ) : ℝ) = 2 := by exact_mod_cast hhi
      have hx0 : 0 ≤ x := by linarith [hx.1]
      have hx2 : x ≤ 2 := by linarith [hx.2]
      rw [model, haeq, hceq]
      norm_num
      exact mtKernel_low_sq hx0 hx2
  | zero =>
      simp only [hk, Bool.and_eq_true, decide_eq_true_eq] at hkind
      obtain ⟨haeq,hceq⟩ := hkind
      simp [model, haeq, hceq, sq_nonneg]
  | numeric cells =>
      simp only [hk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hkind
      obtain ⟨⟨hne,hcover⟩,hall⟩ := hkind
      obtain ⟨cell,hmem,hcell⟩ := coverFrom_sound hne hcover hx.1 hx.2
      exact cellCheck_sound ha hc (hall cell hmem) hcell

end LowerPiece

/-- A contiguous list of pieces covers one outer interval. -/
def piecesCoverFrom (cur last : ℚ) : List LowerPiece → Bool
  | [] => decide (cur = last)
  | p :: ps => decide (p.box.lo = cur) && decide (p.box.lo ≤ p.box.hi) &&
      piecesCoverFrom p.box.hi last ps

def checkPieces (first last : ℚ) (ps : List LowerPiece) : Bool :=
  decide (ps ≠ []) && piecesCoverFrom first last ps && ps.all LowerPiece.check

lemma piecesCoverFrom_sound {cur last : ℚ} {ps : List LowerPiece} {x : ℝ}
    (hne : ps ≠ []) (hc : piecesCoverFrom cur last ps = true)
    (hxlo : (cur:ℝ) ≤ x) (_hxhi : x ≤ (last:ℝ)) :
    ∃ p ∈ ps, Holds p.box x := by
  induction ps generalizing cur with
  | nil => exact (hne rfl).elim
  | cons p ps ih =>
      simp only [piecesCoverFrom, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hfirst,hord⟩,hrest⟩ := hc
      subst cur
      by_cases hx : x ≤ (p.box.hi : ℝ)
      · exact ⟨p, by simp, hxlo, hx⟩
      · cases ps with
        | nil =>
            simp only [piecesCoverFrom, decide_eq_true_eq] at hrest
            have hlast : ((p.box.hi : ℚ) : ℝ) = (last : ℝ) := by exact_mod_cast hrest
            exact (hx (by rw [hlast]; assumption)).elim
        | cons next rest =>
            obtain ⟨found,hmem,hholds⟩ := ih (by simp) hrest (le_of_not_ge hx)
            exact ⟨found, by simp [hmem], hholds⟩

/-- Every accepted piece table supplies a pointwise lower model. -/
theorem checkPieces_sound {first last : ℚ} {ps : List LowerPiece}
    (hc : checkPieces first last ps = true) {x : ℝ}
    (hxlo : (first:ℝ) ≤ x) (hxhi : x ≤ (last:ℝ)) :
    ∃ p ∈ ps, Holds p.box x ∧ p.model x ≤ 2 * mtKernel x ^ 2 := by
  simp only [checkPieces, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨hne,hcover⟩,hall⟩ := hc
  obtain ⟨p,hmem,hp⟩ := piecesCoverFrom_sound hne hcover hxlo hxhi
  exact ⟨p,hmem,hp,LowerPiece.check_sound (hall p hmem) hp⟩

end Zeta23.ThmD.Sextuple
