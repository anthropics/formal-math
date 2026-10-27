/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import AppRunningTimeStatement
public import GeneralPieces.Num.PartA
public import GeneralPieces.Num.Asymptotic
public import GeneralPieces.Rec.Rate

/-! # Small assertions of Appendix A

Sentences of Appendix A that assert something and that no proof of the end theorems uses, because
the cost of an algorithm is
rendered here by the length of a pad and not by a count of operations:
small facts before the count of operations in the proof of part (b) (K ≤ Ξ, K^g ≤ Ξ^g and (2|𝓘| + 2)·2^{cλ}
≤ Ξ^{c+1}·τ); and, in the proof of part (c), that the conditions of the theorem in n hold for all
but finitely many n
when k is fixed, and that a formula with k ≤ 2 is read as a 3-CNF.
Each theorem quotes its sentence. -/

@[expose] public section

namespace GeneralPieces.Remarks

open Finset Levels.Gen ClauseBound.Gen AppRunningTime

/-! ## Before the count of operations in the proof of part (b) -/

/-- K_ℓ ≤ Ξ = g²(λ + B). -/
theorem K_le_Xi (x₀ l lam B : ℕ) (hlam : 1 ≤ lam) : K x₀ l ≤ g x₀ l ^ 2 * (lam + B) := by
  have h1 : K x₀ l ≤ g x₀ l := by
    rw [g]; exact Nat.le_mul_of_pos_left _ (by positivity)
  calc K x₀ l ≤ g x₀ l := h1
    _ ≤ g x₀ l ^ 2 := Nat.le_self_pow (by norm_num) _
    _ ≤ g x₀ l ^ 2 * (lam + B) := Nat.le_mul_of_pos_right _ (by omega)

/-- «K^g ≤ Ξ^g». -/
theorem K_pow_le (x₀ l lam B : ℕ) (hlam : 1 ≤ lam) : K x₀ l ^ g x₀ l ≤ (g x₀ l ^ 2 * (lam + B)) ^ g x₀ l :=
  Nat.pow_le_pow_left (K_le_Xi x₀ l lam B hlam) _

/-- «(2|𝓘| + 2)·2^{cλ} ≤ Ξ^{c+1}·τ», where |𝓘| ≤ (2λ)^c, τ = 2^{cλ}·Ξ^{C₂} and Ξ = g²(λ + B) with g
≥ 2. -/
theorem card_term_le (a c lam B I C₂ : ℕ) (ha : 2 ≤ a) (hlam : 1 ≤ lam) (hI : I ≤ (2 * lam) ^ c) :
    (2 * I + 2) * 2 ^ (c * lam) ≤ (a ^ 2 * (lam + B)) ^ (c + 1) * (2 ^ (c * lam) * (a ^ 2 * (lam + B)) ^ C₂) := by
  have h4 : 4 ≤ a ^ 2 := by nlinarith
  have hX : 4 * lam ≤ a ^ 2 * (lam + B) := Nat.mul_le_mul h4 (by omega)
  obtain ⟨X, hXd⟩ : ∃ X, X = a ^ 2 * (lam + B) := ⟨_, rfl⟩
  rw [← hXd] at hX ⊢
  have h1 : (2 * lam) ^ c ≤ X ^ c := Nat.pow_le_pow_left (by omega) c
  have h2 : 1 ≤ X ^ c := Nat.one_le_pow _ _ (by omega)
  have h3 : 2 * I + 2 ≤ X ^ (c + 1) := by
    calc 2 * I + 2 ≤ 4 * X ^ c := by omega
      _ ≤ X * X ^ c := Nat.mul_le_mul_right _ (by omega)
      _ = X ^ (c + 1) := by ring
  have h5 : 1 ≤ X ^ C₂ := Nat.one_le_pow _ _ (by omega)
  calc (2 * I + 2) * 2 ^ (c * lam) ≤ X ^ (c + 1) * (2 ^ (c * lam) * 1) := by rw [mul_one]; exact Nat.mul_le_mul_right _ h3
    _ ≤ X ^ (c + 1) * (2 ^ (c * lam) * X ^ C₂) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h5)

/-! ## The proof of part (c): the bound in n -/

/-- «… whose conditions n ≥ K₀^17 and k ≤ (log n)^{1/4} hold for all but finitely many n when k is
fixed». -/
theorem conditions_eventually (k K₀ : ℕ) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → K₀ ^ 17 ≤ n ∧ (k : ℝ) ≤ Real.logb 2 n ^ (1 / 4 : ℝ) := by
  refine ⟨max (K₀ ^ 17) (2 ^ k ^ 4), fun n hn => ⟨le_trans (le_max_left _ _) hn, ?_⟩⟩
  have h1 : 2 ^ k ^ 4 ≤ n := le_trans (le_max_right _ _) hn
  have h2 : ((k ^ 4 : ℕ) : ℝ) ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast lt_of_lt_of_le (by positivity) h1), Real.rpow_natCast]
    exact_mod_cast h1
  have h3 : (((k ^ 4 : ℕ) : ℝ)) ^ (1 / 4 : ℝ) = k := by
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [← h3]
  exact Real.rpow_le_rpow (by positivity) h2 (by norm_num)

/-- «… and a formula with k ≤ 2 is read as a 3-CNF.» -/
theorem read_as_three {k n : ℕ} (φ : Sat3.CNF n) (hk : k ≤ 3) (h : SatK.IsKCNF k φ) : SatK.IsKCNF 3 φ :=
  ⟨fun C hC => le_trans (h.1 C hC) hk, h.2⟩

end GeneralPieces.Remarks
