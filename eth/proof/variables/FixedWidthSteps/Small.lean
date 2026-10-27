/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FixedWidthSteps.RouteDefs
import Wrap.ArithRate

/-! # Finitely many n

For n ≥ 4 the exponent n·log log n/(log n)^α is positive, so every number is below 2^{C·n·log log
n/(log n)^α} for some C; for finitely many n take the largest of these C. -/

public section

namespace FixedWidthSteps

open MainTheoremForms FixedWidth

/-- For n ≥ 4: log n ≥ 2 and log log n ≥ 1. -/
theorem lg_facts {n : ℕ} (hn : 4 ≤ n) : 2 ≤ lg n ∧ 1 ≤ lg (lg n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have := Wrap.Arith.lg_add_four_facts m
  push_cast
  exact this

/-- For n ≥ 4 the exponent is positive. -/
theorem expVariables_pos (α : ℝ) {n : ℕ} (hn : 4 ≤ n) : 0 < expVariables α n := by
  obtain ⟨h1, h2⟩ := lg_facts hn
  have h3 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h4 : 0 < lg n ^ α := Real.rpow_pos_of_pos (by linarith) _
  exact div_pos (mul_pos h3 (by linarith)) h4

/-- The bound grows with C. -/
theorem timeVariables_mono (α : ℝ) {C C' n : ℕ} (hn : 4 ≤ n) (h : C ≤ C') : timeVariables α C n ≤ timeVariables α C' n :=
  Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right (Nat.cast_le.2 h) (expVariables_pos α hn).le))

/-- The bound is at most the power that it rounds down. -/
theorem timeVariables_le (α : ℝ) (C n : ℕ) : (timeVariables α C n : ℝ) ≤ (2 : ℝ) ^ ((C : ℝ) * expVariables α n) := Nat.floor_le (by positivity)

/-- For one n ≥ 4, every number is within the bound for some C. -/
theorem exists_le_timeVariables (α : ℝ) {n : ℕ} (hn : 4 ≤ n) (N : ℕ) : ∃ C : ℕ, N ≤ timeVariables α C n := by
  have hE := expVariables_pos α hn
  obtain ⟨C, hC⟩ := exists_nat_ge ((N : ℝ) / expVariables α n)
  refine ⟨C, Nat.le_floor ?_⟩
  rw [div_le_iff₀ hE] at hC
  calc (N : ℝ) ≤ (2 : ℝ) ^ N := by exact_mod_cast Nat.lt_two_pow_self.le
    _ = (2 : ℝ) ^ (N : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two hC

/-- For fixed k and finitely many n, trying all assignments is within the bound. -/
theorem smallCasesAreWithinTheBound : SmallCasesAreWithinTheBound := by
  intro α c k n₀ _
  induction n₀ with
  | zero => exact ⟨0, fun n _ h => absurd h (Nat.not_lt_zero n)⟩
  | succ m ih =>
    obtain ⟨C, hC⟩ := ih
    by_cases hm : 4 ≤ m
    · obtain ⟨C', hC'⟩ := exists_le_timeVariables α hm (2 ^ (c * m) * m ^ (c * k))
      refine ⟨max C C', fun n h4 hlt => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h | rfl
      · exact (hC n h4 h).trans (timeVariables_mono α h4 (le_max_left _ _))
      · exact hC'.trans (timeVariables_mono α h4 (le_max_right _ _))
    · exact ⟨C, fun n h4 hlt => hC n h4 (by omega)⟩

end FixedWidthSteps
