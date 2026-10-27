/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepSparsify.Defs
import StepSparsify.CalNumbers
import SparsificationLemma.Cal.Alpha
import SparsificationLemma.Cal.Real
import SparsificationLemma.Cal.Facts
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Cutting the paths of the sparsification tree at a later depth

`leaves_eq_of_le` serves the bound 2^(⌊n/2^s⌋+1) on the number of leaves of the tree of Step 5 of
Appendix D with Calabro's thresholds, where ε = 1/2^s and K = max(k, 3).
It holds for every tree: if the procedure has stopped at every node listed when the paths are cut
after D₀ steps, then cutting them after D ≥ D₀ steps gives the same list.
With Calabro's thresholds every path stops within D₀ = (β₁ + … + β_{k−1})·n steps, so for that bound
it suffices to count the leaves for this D₀. -/

public section

namespace StepSparsify

open Finset Groundwork Groundwork.Sparsify CountKSat SparsificationLemma

/-- If the procedure has stopped at every node that is listed when the paths are cut after D₀ steps,
then cutting them after D ≥ D₀ steps gives the same list. -/
theorem leaves_eq_of_le {σ : Type*} (step : σ → Option (σ × σ)) (D₀ : ℕ) : ∀ (D : ℕ) (r : σ), D₀ ≤ D →
    (∀ x ∈ leaves step D₀ r, step x = none) → leaves step D r = leaves step D₀ r := by
  induction D₀ with
  | zero =>
    intro D r _ h
    have hr : step r = none := h r (by simp [leaves])
    cases D with
    | zero => rfl
    | succ D => simp [leaves, hr]
  | succ D₀ ih =>
    intro D r hD h
    obtain ⟨D, rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
    cases hs : step r with
    | none => simp [leaves, hs]
    | some p =>
      obtain ⟨l, g⟩ := p
      simp only [leaves, hs, List.mem_append] at h ⊢
      rw [ih D l (by omega) fun x hx => h x (Or.inl hx), ih D g (by omega) fun x hx => h x (Or.inr hx)]

/-- y grows with k. -/
theorem yC_mono {k K : ℕ} (α : ℕ) (hk : 1 ≤ k) (hK : k ≤ K) (hα : 1 ≤ α) : Cal.yC k α ≤ Cal.yC K α := by
  have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h2 : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have h3 : (1 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα
  have h4 : 0 ≤ Real.logb 2 (32 * (α : ℝ)) := Real.logb_nonneg (by norm_num) (by linarith)
  have h5 : ((k : ℝ) - 1) ^ 2 ≤ ((K : ℝ) - 1) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  unfold Cal.yC
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 (by norm_num)) h4) (by positivity)

/-- y with K = max(k, 3) in the place of k, and with α Calabro's parameter for k and 1/2^s, is at
most 1/2^s. -/
theorem yC_le (k s : ℕ) : Cal.yC (max k 3) (alphaS k s) ≤ 1 / 2 ^ s := by
  obtain ⟨a1, -, -, a4, -⟩ := Cal.stAlpha (max k 3) (1 / 2 ^ s) (le_max_right k 3) (eps_pos s) (eps_le_one s)
  have hx := Cal.xC_cast (max k 3) (1 / 2 ^ s)
  have he : (((1 / 2 ^ s : ℚ)) : ℝ) = 1 / 2 ^ s := by push_cast; rfl
  rw [he] at hx
  refine Cal.stYLe (max k 3) (alphaS k s) (1 / 2 ^ s) (le_trans (by norm_num) (le_max_right k 3)) (by positivity) ?_ ?_
  · rw [← hx]; exact_mod_cast a1
  · rw [← hx]; exact a4

/-- The tree with Calabro's thresholds has at most 2^(⌊n/2^s⌋+1) leaves, wherever the paths are cut
from (β₁ + … + β_{k−1})·n steps on. -/
theorem stCalLeaves : StCalLeaves := by
  intro k n s D ψ hk hD hψ
  have hα : 1 ≤ alphaS k s := le_trans (by norm_num) (le_alphaS k s).1
  have e : tree (thCal k s) k D ψ = tree (Cal.thetaC (alphaS k s)) k (Cal.depthC (alphaS k s) k n) ψ :=
    leaves_eq_of_le _ _ D _ hD (Cal.factI (alphaS k s) k n ψ hα hk hψ)
  rw [e]
  obtain rfl | hk2 : k = 1 ∨ 2 ≤ k := by omega
  · have h := (Cal.gen hα hk hψ).2.1
    rw [outputs, List.length_map] at h
    simp only [Nat.sub_self, Nat.zero_mul, Nat.zero_div, Nat.zero_add, sum_range_one, Nat.choose_zero_right] at h
    exact h.trans Nat.one_le_two_pow
  · have h1 := Cal.factIIIy (alphaS k s) k n ψ hα hk2 hψ
    have hy : Cal.yC k (alphaS k s) ≤ 1 / 2 ^ s := (yC_mono _ hk (le_max_left k 3) hα).trans (yC_le k s)
    have h2 : n < 2 ^ s * (n / 2 ^ s + 1) := Nat.lt_mul_div_succ n (by positivity)
    have h3 : (n : ℝ) ≤ (2 : ℝ) ^ s * ((n / 2 ^ s + 1 : ℕ) : ℝ) := by exact_mod_cast h2.le
    have h4 : (1 : ℝ) / 2 ^ s * (n : ℝ) ≤ ((n / 2 ^ s + 1 : ℕ) : ℝ) := by
      rw [one_div, inv_mul_le_iff₀ (by positivity)]
      exact h3
    have h5 : ((tree (Cal.thetaC (alphaS k s)) k (Cal.depthC (alphaS k s) k n) ψ).length : ℝ) ≤ ((2 ^ (n / 2 ^ s + 1) : ℕ) : ℝ) := by
      calc ((tree (Cal.thetaC (alphaS k s)) k (Cal.depthC (alphaS k s) k n) ψ).length : ℝ) ≤ (2 : ℝ) ^ (Cal.yC k (alphaS k s) * (n : ℝ)) := h1
        _ ≤ (2 : ℝ) ^ (((n / 2 ^ s + 1 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) ((mul_le_mul_of_nonneg_right hy (Nat.cast_nonneg n)).trans h4)
        _ = ((2 ^ (n / 2 ^ s + 1) : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; ring
    exact_mod_cast h5

end StepSparsify
