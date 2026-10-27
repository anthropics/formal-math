/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Cal.Defs
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-! # The numbers β_c and θ_c

This file proves six statements of proof/sparsification/SparsificationLemma/Cal/Defs.lean on the
numbers β_c and θ_c of Calabro's dissertation, which the sparsification of Appendix C uses: the
recursion for β_c (`StBetaRec`);
the closed form β_c = 2·(8α)^(c−1)·Cat_(c−1) (`StBetaCat`), by induction with the recursion of the
Catalan numbers; Cat_j ≤ 4^j (`StCatLe`), since (j+1)·Cat_j is the central binomial coefficient;
hence β_c ≤ 2·(32α)^(c−1) (`StBetaLe`); the bound β₁ + … + β_{k−1} ≤ 4·(32α)^(k−2) (`FactIV`), a
geometric sum with ratio at least 2; and the sum of the θ_c (`StDegSum`). -/

public section

namespace SparsificationLemma.Cal

open Finset

/-- The defining equation of β_(c+2). -/
theorem betaC_add_two (α c : ℕ) : betaC α (c + 2) = ∑ h : Fin (c + 1), 4 * α * betaC α (c + 1 - h) * betaC α (h + 1) := by rw [betaC]

/-- β₁ = 2. -/
theorem betaC_one (α : ℕ) : betaC α 1 = 2 := by rw [betaC]

/-- β₀ = 0, the convention of Cal/Defs.lean. -/
theorem betaC_zero (α : ℕ) : betaC α 0 = 0 := by rw [betaC]

/-- θ_c = α·β_c for c ≥ 1. -/
theorem thetaC_of_pos (α : ℕ) {c : ℕ} (hc : 1 ≤ c) : thetaC α c = α * betaC α c := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' hc
  rfl

/-- The recursion for β_c written as a sum over h = 1, …, c−1 (the form of `StBetaRec`), rather than
over `Fin` as in the definition. -/
theorem stBetaRec : StBetaRec := by
  intro α c hc
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' hc
  rw [betaC_add_two, sum_Ico_eq_sum_range, Fin.sum_univ_eq_sum_range (fun h => 4 * α * betaC α (c + 1 - h) * betaC α (h + 1)) (c + 1)]
  refine sum_congr rfl fun h _ => ?_
  rw [show c + 2 - (1 + h) = c + 1 - h by omega, Nat.add_comm 1 h]

/-- β_c = 2·(8α)^(c−1)·Cat_(c−1). -/
theorem stBetaCat : StBetaCat := by
  intro α c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rcases c with _ | c
    · simp [betaC_one]
    rw [betaC_add_two, catalan_succ, mul_sum]
    refine sum_congr rfl fun h _ => ?_
    have hh : (h : ℕ) ≤ c := Nat.lt_succ_iff.1 h.2
    rw [show c + 1 - (h : ℕ) = (c - h) + 1 by omega, ih (c - h) (by omega), ih h (by omega)]
    have e : (8 * α) ^ (c + 1) = 8 * α * ((8 * α) ^ (c - h) * (8 * α) ^ (h : ℕ)) := by
      rw [← pow_add, Nat.sub_add_cancel hh, pow_succ, Nat.mul_comm]
    rw [e]
    ring

/-- Cat_j ≤ 4^j. -/
theorem stCatLe : StCatLe := fun j =>
  (Nat.le_mul_of_pos_left _ (Nat.succ_pos j)).trans ((succ_mul_catalan_eq_centralBinom j).le.trans (Nat.centralBinom_le_four_pow j))

/-- Cat_j ≥ 1. -/
theorem catalan_pos (j : ℕ) : 0 < catalan j := by
  refine Nat.pos_of_ne_zero fun h => ?_
  have e := succ_mul_catalan_eq_centralBinom j
  rw [h, Nat.mul_zero] at e
  exact (Nat.centralBinom_pos j).ne e

/-- β_c ≥ 1 for c ≥ 1, if α ≥ 1. -/
theorem betaC_pos {α : ℕ} (hα : 1 ≤ α) (c : ℕ) : 0 < betaC α (c + 1) := by
  rw [stBetaCat]
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.pow_pos (by omega))) (catalan_pos c)

/-- β_c ≤ 2·(32α)^(c−1). -/
theorem stBetaLe : StBetaLe := by
  intro α c
  rw [stBetaCat]
  calc 2 * (8 * α) ^ c * catalan c ≤ 2 * (8 * α) ^ c * 4 ^ c := Nat.mul_le_mul_left _ (stCatLe c)
    _ = 2 * (32 * α) ^ c := by rw [Nat.mul_assoc, ← mul_pow]; congr 2; ring

/-- 2·(1 + q + … + q^m) ≤ 4·q^m for q ≥ 2. -/
theorem geom_le {q : ℕ} (hq : 2 ≤ q) (m : ℕ) : ∑ i ∈ range (m + 1), 2 * q ^ i ≤ 4 * q ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have h1 : 2 * q ^ m ≤ q ^ (m + 1) := by rw [pow_succ, Nat.mul_comm]; exact Nat.mul_le_mul_left _ hq
    omega

/-- The bound `FactIV`: β₁ + … + β_{k−1} ≤ 4·(32α)^(k−2), for α ≥ 1 and k ≥ 2. -/
theorem factIV : FactIV := by
  intro α k hα hk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [sum_Ico_eq_sum_range]
  refine le_trans (sum_le_sum fun i _ => ?_) (geom_le (q := 32 * α) (by omega) m)
  rw [Nat.add_comm 1 i]
  exact stBetaLe α i

/-- β₀ + β₁ + … + β_{k−1} = β₁ + … + β_{k−1}, for k ≥ 1. -/
theorem sum_range_betaC (α : ℕ) {k : ℕ} (hk : 1 ≤ k) : ∑ c ∈ range k, betaC α c = ∑ c ∈ Ico 1 k, betaC α c := by
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), betaC_zero, Nat.zero_add]

/-- For α ≥ 1 and k ≥ 2: θ₀ + … + θ_{k−1} = 2 + α·(β₁ + … + β_{k−1}), which is at most 2 +
4α·(32α)^(k−2) by `FactIV`; and 8·(2 + 4α·(32α)^(k−2)) = 16 + (32α)^(k−1). -/
theorem stDegSum : StDegSum := by
  intro α k hα hk
  have h1 : ∑ j ∈ range k, thetaC α j = 2 + α * ∑ c ∈ Ico 1 k, betaC α c := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), mul_sum]
    exact congrArg (2 + ·) (sum_congr rfl fun c hc => thetaC_of_pos α (mem_Ico.1 hc).1)
  refine ⟨h1, ?_, ?_⟩
  · rw [h1, Nat.mul_assoc 4, Nat.mul_left_comm 4]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (factIV α k hα hk)) _
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [show m + 2 - 2 = m by omega, show m + 2 - 1 = m + 1 by omega, pow_succ]
    ring

end SparsificationLemma.Cal
