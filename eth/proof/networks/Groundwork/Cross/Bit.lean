/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import NetworkStatements
public import Mathlib.Data.Nat.Choose.Bounds

/-! Uncrossing for single bits: the one-bit identity X₁ = I₁ − s ⊗ s (theorem `uncross`), the
crossing of two λ-bit diagonals as the sum
of the λ+1 terms A_i, and the bound |A_i| ≤ 2^λ. The paper's Lemma 2 instead cuts the strings into
blocks of 3 bits and uses the eight-square identity. -/

@[expose] public section

namespace Groundwork

open Finset

/-- One bit of the crossing is I minus s ⊗ s. -/
theorem uncross (x y u v : Bool) : X₁ x y u v = I₁ x y u v - s x y * s u v := by
  revert x y u v; decide

/-- A λ-bit crossing is the product of its bits. -/
theorem cross_eq_prod {n : ℕ} (x y u v : Bits n) : cross x y u v = ∏ k, X₁ (x k) (y k) (u k) (v k) := by
  by_cases h : x = v ∧ y = u
  · obtain ⟨rfl, rfl⟩ := h
    simp [cross, X₁]
  · rw [cross, if_neg h]
    have hex : ∃ k, ¬ (x k = v k ∧ y k = u k) := by
      by_contra hc
      push Not at hc
      exact h ⟨funext fun k => (hc k).1, funext fun k => (hc k).2⟩
    obtain ⟨k, hk⟩ := hex
    exact (prod_eq_zero (mem_univ k) (by simp only [X₁, if_neg hk])).symm

/-- Only λ+1 terms: the crossing is A_0 + … + A_λ. -/
theorem sum_A {n : ℕ} (x y u v : Bits n) : ∑ i ∈ range (n + 1), A n i x y u v = cross x y u v := by
  have h : ∀ k, X₁ (x k) (y k) (u k) (v k)
      = -(s (x k) (y k) * s (u k) (v k)) + I₁ (x k) (y k) (u k) (v k) := fun k => by
    rw [uncross]; ring
  rw [cross_eq_prod]
  simp_rw [h]
  rw [prod_add, sum_powerset, card_univ, Fintype.card_fin]
  simp only [A, compl_eq_univ_sdiff]

/-- A product of integers of absolute value at most 1 has absolute value at most 1. -/
theorem abs_prod_le_one {ι : Type} (S : Finset ι) (f : ι → ℤ) (h : ∀ k, |f k| ≤ 1) : |∏ k ∈ S, f k| ≤ 1 := by
  rw [abs_prod]
  exact prod_le_one (fun _ _ => abs_nonneg _) fun k _ => h k

/-- A sum over the sets S of i positions of products of λ integers of absolute value at most 1 has
absolute value at most
C(λ,i) ≤ 2^λ. -/
theorem abs_sum_powersetCard_le {n : ℕ} (i : ℕ) (f1 f0 : Fin n → ℤ) (h1 : ∀ k, |f1 k| ≤ 1) (h0 : ∀ k, |f0 k| ≤ 1) :
    |∑ S ∈ powersetCard i (univ : Finset (Fin n)), (∏ k ∈ S, f1 k) * ∏ k ∈ Sᶜ, f0 k| ≤ 2 ^ n := by
  calc |∑ S ∈ powersetCard i (univ : Finset (Fin n)), (∏ k ∈ S, f1 k) * ∏ k ∈ Sᶜ, f0 k|
      ≤ ∑ S ∈ powersetCard i (univ : Finset (Fin n)), |(∏ k ∈ S, f1 k) * ∏ k ∈ Sᶜ, f0 k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S ∈ powersetCard i (univ : Finset (Fin n)), (1 : ℤ) := by
        refine sum_le_sum fun S _ => ?_
        rw [abs_mul]
        exact mul_le_one₀ (abs_prod_le_one S f1 h1) (abs_nonneg _) (abs_prod_le_one Sᶜ f0 h0)
    _ = (n.choose i : ℤ) := by simp
    _ ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n i

/-- At most C(λ,i) ≤ 2^λ terms, each 0 or ±1. -/
theorem abs_A_le (n i : ℕ) (x y u v : Bits n) : |A n i x y u v| ≤ 2 ^ n := by
  have h1 : ∀ p q a b : Bool, |(-(s p q * s a b))| ≤ 1 := by decide
  have h0 : ∀ p q a b : Bool, |I₁ p q a b| ≤ 1 := by decide
  exact abs_sum_powersetCard_le i _ _ (fun k => h1 (x k) (y k) (u k) (v k)) fun k => h0 (x k) (y k) (u k) (v k)

end Groundwork
