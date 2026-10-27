/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Cal.Defs
import SparsificationLemma.Cal.Beta
import SparsificationLemma.Cal.Thr
import SparsificationLemma.Gen
import SparsificationLemma.Shrink
import SparsificationLemma.Side
import SparsifyWidthK.Thresholds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Facts (i) and (iii) on the tree for Calabro's thresholds

This file proves `FactI` and `FactIIIy` of proof/sparsification/SparsificationLemma/Cal/Defs.lean.
Calabro's thresholds satisfy the conditions `ThrC` with τ = α (`stThrCal`), so the general theorem
`stGen` applies with
D = (β₁ + … + β_{k−1})·n. Its first clause is fact (i).
For fact (iii), `stGen` bounds the number of leaves by Σ_{j ≤ (k−1)n/α} C(D, j). By fact (iv), D ≤
L·n with L = 4·(32α)^(k−2). The estimate `sum_choose_le_two_rpow` of
proof/sparsification/SparsifyWidthK/Thresholds.lean bounds the sum by
2^(yn) as soon as ((k−1)/α)·log₂(e·α·L) ≤ y, and e·α·L ≤ (32α)^(k−1) because 4e ≤ 32; so y =
(k−1)²·log₂(32α)/α will do. -/

public section

namespace SparsificationLemma.Cal

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK

/-- The general theorem for Calabro's thresholds, with τ = α and D = (β₁ + … + β_{k−1})·n. -/
theorem gen {α k n : ℕ} {ψ : PFml} (hα : 1 ≤ α) (hk : 1 ≤ k) (hψ : IsKCNF k n ψ) :
    (∀ x ∈ tree (thetaC α) k (depthC α k n) ψ, stepC (thetaC α) k x = none) ∧
    (outputs (thetaC α) k (depthC α k n) ψ).length ≤ ∑ j ∈ range ((k - 1) * n / α + 1), (depthC α k n).choose j ∧
    (∀ Φ ∈ outputs (thetaC α) k (depthC α k n) ψ, IsKCNF k n Φ ∧ ∀ v, occN Φ v ≤ 2 * (∑ j ∈ range k, thetaC α j) + 2) ∧
    ∀ x ∈ tree (thetaC α) k (depthC α k n) ψ, x.1.length ≤ ψ.length :=
  stGen stSide k α n (depthC α k n) (thetaC α) (betaC α) hk hα (stThrCal α k hα) (le_refl _) ψ hψ

/-- Fact (i), with β₁ + … + β_{k−1}: no path of the tree has more than (β₁ + … + β_{k−1})·n steps. -/
theorem factI : FactI := fun _ _ _ _ hα hk hψ => (gen hα hk hψ).1

/-- ((k−1)/α)·log₂(e·α·L) ≤ y for L = 4·(32α)^(k−2), α ≥ 1 and k ≥ 2. -/
theorem log_le_yC {α k : ℕ} (hα : 1 ≤ α) (hk : 2 ≤ k) :
    (((k - 1 : ℕ) : ℝ) / (α : ℝ)) * Real.logb 2 (Real.exp 1 * (α : ℝ) * ((4 * (32 * α) ^ (k - 2) : ℕ) : ℝ)) ≤ yC k α := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have ha : (1 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have he0 := Real.exp_pos 1
  have hq : (0 : ℝ) < 32 * (α : ℝ) := by positivity
  have hp : (0 : ℝ) < (32 * (α : ℝ)) ^ m := by positivity
  have h1 : Real.exp 1 * (α : ℝ) * ((4 * (32 * α) ^ (m + 2 - 2) : ℕ) : ℝ) ≤ (32 * (α : ℝ)) ^ (m + 1) := by
    rw [show m + 2 - 2 = m by omega, pow_succ]
    push_cast
    have : Real.exp 1 * (α : ℝ) * 4 ≤ 32 * (α : ℝ) := by nlinarith
    calc Real.exp 1 * (α : ℝ) * (4 * (32 * (α : ℝ)) ^ m) = (Real.exp 1 * (α : ℝ) * 4) * (32 * (α : ℝ)) ^ m := by ring
      _ ≤ 32 * (α : ℝ) * (32 * (α : ℝ)) ^ m := mul_le_mul_of_nonneg_right this hp.le
      _ = (32 * (α : ℝ)) ^ m * (32 * (α : ℝ)) := by ring
  have h0 : 0 < Real.exp 1 * (α : ℝ) * ((4 * (32 * α) ^ (m + 2 - 2) : ℕ) : ℝ) := by
    have : (0 : ℝ) < ((4 * (32 * α) ^ (m + 2 - 2) : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (by norm_num) (Nat.pow_pos (by omega))
    positivity
  have h2 := Real.logb_le_logb_of_le one_lt_two h0 h1
  rw [Real.logb_pow] at h2
  have hc : ((m + 2 - 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by
    rw [show m + 2 - 1 = m + 1 by omega]; push_cast; ring
  have hc0 : (0 : ℝ) ≤ ((m : ℝ) + 1) / (α : ℝ) := by positivity
  rw [hc, yC]
  calc ((m : ℝ) + 1) / (α : ℝ) * Real.logb 2 (Real.exp 1 * (α : ℝ) * ((4 * (32 * α) ^ (m + 2 - 2) : ℕ) : ℝ))
      ≤ ((m : ℝ) + 1) / (α : ℝ) * (((m + 1 : ℕ) : ℝ) * Real.logb 2 (32 * (α : ℝ))) := mul_le_mul_of_nonneg_left h2 hc0
    _ = 32 * (((m + 2 : ℕ) : ℝ) - 1) ^ 2 * Real.logb 2 (32 * (α : ℝ)) / (32 * (α : ℝ)) := by
        push_cast
        field_simp
        ring

/-- Fact (iii), first part: the tree has at most 2^(yn) leaves. -/
theorem factIIIy : FactIIIy := by
  intro α k n ψ hα hk hψ
  have h1 := (gen hα (by omega : 1 ≤ k) hψ).2.1
  rw [outputs, List.length_map] at h1
  have hD : depthC α k n ≤ 4 * (32 * α) ^ (k - 2) * n := by
    rw [depthC, sum_range_betaC α (by omega : 1 ≤ k)]
    exact Nat.mul_le_mul_right _ (factIV α k hα hk)
  have h2 : (tree (thetaC α) k (depthC α k n) ψ).length ≤ ∑ j ∈ range ((k - 1) * n / α + 1), (4 * (32 * α) ^ (k - 2) * n).choose j :=
    h1.trans (sum_le_sum fun j _ => Nat.choose_le_choose j hD)
  have hkL : k - 1 ≤ 4 * (32 * α) ^ (k - 2) := by
    have := Nat.lt_pow_self (n := k - 2) (by omega : 1 < 32 * α)
    omega
  exact (Nat.cast_le.2 h2).trans (Thresholds.sum_choose_le_two_rpow hα hkL (log_le_yC hα hk) n)

end SparsificationLemma.Cal
