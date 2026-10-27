/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.ArithInv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # The invariant implies that the pad suffices for the whole descent

`fits_of_inv`: if the invariant `Inv` holds at level j and the
exponent e of the length of the pad dominates four explicit numbers, then `PaddedDescent.F.Fits`
holds for the schedule below level j. No programs occur
here. -/

public section

namespace PaddedDescent.F.Arith

open Groundwork.Prog (nRect)

/-- If the invariant holds at level j ≤ t, then a pad of length F ≥ 2^e suffices for the work list
at level j and for all the steps below it. -/
theorem fits_of_inv {t X Z Qm Wm L Lw e F : ℕ} (hZ : 25 * Kseq t ^ 2 ≤ 2 * Z) (hZQ : Z ≤ Qm) (hL : Qm + 1 ≤ 2 ^ L)
    (hLw : Kseq t * (3 * Wm + 14) + 4 * Qm + 10 ≤ 2 ^ Lw)
    (he1 : 4 * (X + Z) ≤ e) (he2 : L * Kseq t ^ 2 ≤ e) (he3 : Kseq t ≤ e)
    (he4 : L * (2 * Kseq t ^ 2) + (X + Z) + Lw + 1 ≤ e) (hF : 2 ^ e ≤ F) :
    ∀ j, j ≤ t → ∀ lam B cnt, Inv t X Z Qm Wm L j lam B cnt → Fits F (Kseq j) lam B cnt (schedL j) := by
  have up : ∀ {a : ℕ}, a ≤ e → 2 ^ a ≤ F := fun h => (Nat.pow_le_pow_right (by norm_num) h).trans hF
  intro j
  induction j with
  | zero =>
    intro hj lam B cnt h
    exact ⟨(h.work_le hLw hj).trans (up he4), up (h.bottom_le.trans (by omega))⟩
  | succ j ih =>
    intro hj lam B cnt h
    have h' := h.step hZ hZQ hL hj
    simp only [schedL, Fits, List.length_replicate]
    refine ⟨(h.work_le hLw hj).trans (up he4), ⟨?_, ?_, ?_, ?_, ?_⟩, ih (by omega) _ _ _ h'⟩
    · exact (h.pat_le hL hj).trans (up he2)
    · exact (col_le hj).trans (up he3)
    · exact up (h.st_le.trans he1)
    · exact up (h.lab_le.trans (by omega))
    · exact up (le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) (h'.mul_le.trans (by omega)))

end PaddedDescent.F.Arith
