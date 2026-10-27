/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSatRate.Interfaces
import CountKSatRate.Leaf
import all CountKSat.Top.Count
import all PaddedDescent.F.Top

/-! # The number kept by the walk of rounds

Lemmas on the rounds `roundS` of a walk over a tree: one round, and further rounds, do not lower the
number that the walk keeps, and after any number of rounds this number
is at most the sum of the values of the leaves, under the hypothesis `StRoundSEnd` on how the walk
ends. -/

namespace CountKSatRate.Top

open Finset Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F
open Groundwork.Sparsify (PFml leaves round)
open WidthK (theta bsum leafC)

/-! ### The number kept by the walk never goes down -/

/-- One round does not lower the number. -/
theorem le_roundS {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ) (st : List σ × ℕ) : st.2 ≤ (roundS step val st).2 := by
  obtain ⟨l, c⟩ := st
  cases l with
  | nil => exact le_rfl
  | cons s r =>
    rcases h : step s with _ | ⟨l, hh⟩
    · simp [roundS, h]
    · simp [roundS, h]

/-- Further rounds do not lower the number. -/
theorem iterate_le_iterate {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ) (st : List σ × ℕ) (i j : ℕ) :
    ((roundS step val)^[i] st).2 ≤ ((roundS step val)^[j + i] st).2 := by
  induction j with
  | zero => rw [Nat.zero_add]
  | succ j ih =>
    rw [Nat.succ_add, Function.iterate_succ_apply']
    exact ih.trans (le_roundS step val _)

/-- The number after any number of rounds is at most the sum of the values of the leaves. -/
theorem iterate_le_sum (hE : StRoundSEnd) {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ) (d : ℕ) (s : σ)
    (hd : ∀ x ∈ leaves step d s, step x = none) (i : ℕ) : ((roundS step val)^[i] ([s], 0)).2 ≤ ((leaves step d s).map val).sum := by
  have h := iterate_le_iterate step val ([s], 0) i (2 * (leaves step d s).length - 1)
  rwa [hE σ step val d s hd _ (Nat.le_add_right _ _)] at h

end CountKSatRate.Top

namespace CountKSatRate

open Finset Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate.Top
open Groundwork.Sparsify (PFml leaves round)
open WidthK (theta bsum leafC)

end CountKSatRate
