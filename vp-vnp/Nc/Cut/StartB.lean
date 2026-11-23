/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cut.StartA
import Nc.Cut.Codes
import Nc.Cut.Groups

/-!
# Start, II: units

The sum over the segments with staircase support is the sum, over the row data and the numbers of units, of the
values of the starting positions.
-/

set_option linter.unusedSectionVars false

namespace Nc.Cut

open Finset

theorem ite_sum {ι M : Type*} [AddCommMonoid M] (c : Prop) [Decidable c] (s : Finset ι) (f : ι → M) :
    (if c then ∑ i ∈ s, f i else 0) = ∑ i ∈ s, if c then f i else 0 := by
  split_ifs <;> simp

theorem ite_ite_zero {M : Type*} [Zero M] (c d : Prop) [Decidable c] [Decidable d] (a : M) :
    (if c then (if d then a else 0) else 0) = if c ∧ d then a else 0 := by
  by_cases hc : c <;> simp [hc]

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {K U0 E U1 : ℕ} {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {ub : ℕ} {c : ℕ}
  {cb : Option Γ → Fin c → Bool}

end Nc.Cut
