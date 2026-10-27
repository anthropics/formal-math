/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.RecursionDefs
public import Printed.Coding
public import ClauseBound.Gen.Rate
import GeneralPieces.Num.PartA
public import StepMachines.Prog.SideBasics
import Mathlib.Tactic

/-! # The bounds of Theorem A (b) for a larger constant

Plain arithmetic about `timeBound` = 2^{e_ℓK_ℓ²λ}·(K_ℓ(λ+B))^{C₀K_ℓ²} and `sizeBound` =
(K_ℓ(λ+B))^{C₀K_ℓ}, for the last steps of the theorem, where several bounds are put into one with a
larger C₀. With X = K_ℓ(λ+B) ≥ 8:
* `timeBound_mono`, `sizeBound_mono`: they grow with C₀; `three_timeBound_le`: three times the bound
  for C₀ is at most the bound for C₀ + 1; `sizeBound_le_timeBound` (by e_ℓ ≥ 0, from «Clearly e_ℓ ≥
  ½ρ^ℓ» in the proof of part (a): `GeneralPieces.PartA.e_ge_half_pow`);
* `size_tableQuery`, `tableQuery_le`: a query to the tables with its answer has size at most K + 2Kλ +
  B + 3, which with 4 more is at most X², so at most `sizeBound` for every C₀ ≥ 1. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-- X = K_ℓ(λ + B) ≥ 8. -/
theorem base_ge {x₀ : ℕ} (hx : 18 ≤ x₀) (l : ℕ) {lam B : ℕ} (hlam : 1 ≤ lam) (hB : 1 ≤ B) : (8 : ℝ) ≤ (Levels.Gen.K x₀ l : ℝ) * ((lam : ℝ) + B) := by
  have hK : (8 : ℝ) ≤ Levels.Gen.K x₀ l := by
    have := ClauseBound.Gen.Rate.big_le_K hx l
    exact_mod_cast (by omega : 8 ≤ Levels.Gen.K x₀ l)
  have h1 : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
  have h2 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  nlinarith

/-- The bound of the theorem grows with C₀. -/
theorem timeBound_mono (ρ : ℝ) {x₀ : ℕ} (hx : 18 ≤ x₀) (l : ℕ) {lam B : ℕ} (hlam : 1 ≤ lam) (hB : 1 ≤ B) {C C' : ℕ} (h : C ≤ C') : timeBound ρ x₀ C l lam B ≤ timeBound ρ x₀ C' l lam B := by
  have hX := base_ge hx l hlam hB
  unfold timeBound
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_right _ h)) (by positivity)

/-- The bound on the sizes grows with C₀. -/
theorem sizeBound_mono {x₀ : ℕ} (hx : 18 ≤ x₀) (l : ℕ) {lam B : ℕ} (hlam : 1 ≤ lam) (hB : 1 ≤ B) {C C' : ℕ} (h : C ≤ C') : sizeBound x₀ C l lam B ≤ sizeBound x₀ C' l lam B := by
  have hX := base_ge hx l hlam hB
  unfold sizeBound
  exact pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_right _ h)

/-- Three times the bound for C₀ is at most the bound for C₀ + 1. -/
theorem three_timeBound_le (ρ : ℝ) {x₀ : ℕ} (hx : 18 ≤ x₀) (l : ℕ) {lam B : ℕ} (hlam : 1 ≤ lam) (hB : 1 ≤ B) (C : ℕ) : 3 * timeBound ρ x₀ C l lam B ≤ timeBound ρ x₀ (C + 1) l lam B := by
  have hX := base_ge hx l hlam hB
  have hK : 1 ≤ Levels.Gen.K x₀ l ^ 2 := Nat.one_le_pow _ _ (by have := ClauseBound.Gen.Rate.big_le_K hx l; omega)
  have h3 : (3 : ℝ) ≤ ((Levels.Gen.K x₀ l : ℝ) * ((lam : ℝ) + B)) ^ (Levels.Gen.K x₀ l ^ 2) := by
    calc (3 : ℝ) ≤ ((Levels.Gen.K x₀ l : ℝ) * ((lam : ℝ) + B)) ^ 1 := by rw [pow_one]; linarith
      _ ≤ _ := pow_le_pow_right₀ (by linarith) hK
  unfold timeBound
  rw [Nat.add_mul, Nat.one_mul, pow_add]
  have hp : 0 ≤ (2 : ℝ) ^ (Levels.Gen.e ρ x₀ l * (Levels.Gen.K x₀ l : ℝ) ^ 2 * lam) * ((Levels.Gen.K x₀ l : ℝ) * ((lam : ℝ) + B)) ^ (C * Levels.Gen.K x₀ l ^ 2) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h3 hp]

/-- The bound on the sizes is at most the bound of the theorem: K_ℓ ≤ K_ℓ² and e_ℓ ≥ 0. -/
theorem sizeBound_le_timeBound {ρ : ℝ} (hρ : 1 / 2 ≤ ρ) {x₀ : ℕ} (hx : 18 ≤ x₀) (l : ℕ) {lam B : ℕ} (hlam : 1 ≤ lam) (hB : 1 ≤ B) (C : ℕ) : sizeBound x₀ C l lam B ≤ timeBound ρ x₀ C l lam B := by
  have hX := base_ge hx l hlam hB
  have hρ0 : (0 : ℝ) ≤ ρ := by linarith
  have he : 0 ≤ Levels.Gen.e ρ x₀ l := le_trans (by positivity) (GeneralPieces.PartA.e_ge_half_pow ρ x₀ l hρ)
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (Levels.Gen.e ρ x₀ l * (Levels.Gen.K x₀ l : ℝ) ^ 2 * lam) := Real.one_le_rpow (by norm_num) (by positivity)
  have h2 : ((Levels.Gen.K x₀ l : ℝ) * ((lam : ℝ) + B)) ^ (C * Levels.Gen.K x₀ l) ≤ ((Levels.Gen.K x₀ l : ℝ) * ((lam : ℝ) + B)) ^ (C * Levels.Gen.K x₀ l ^ 2) :=
    pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _))
  unfold sizeBound timeBound
  exact h2.trans (le_mul_of_one_le_left (by positivity) h1)

/-- A query to the tables that is answered, with its answer, has size at most K + 2Kλ + B + 3. -/
theorem size_tableQuery {K lam B : ℕ} {W : ℕ → List Bool → ℤ} (hW : ∀ w < K, ∀ z ∈ words ((K - 1) * lam), |W w z| < 2 ^ B) {x : TableQuery} {v : Ans} (h : answersOf K lam W x = some v) :
    size x + size v ≤ K + 2 * K * lam + B + 3 := by
  unfold answersOf tables at h
  by_cases hx : x.1 < K ∧ x.2.length = (K - 1) * lam
  · rw [if_pos hx] at h
    obtain rfl : Sum.inl (W x.1 x.2) = v := by simpa using h
    have h1 := size_nat_le x.1
    have h2 := size_bools x.2
    have h3 := size_entry (hW x.1 hx.1 x.2 (mem_words.2 hx.2))
    have h4 : (K - 1) * lam ≤ K * lam := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    rw [size_prod, size_inl, h2, hx.2]
    have h5 : 2 * K * lam = 2 * (K * lam) := Nat.mul_assoc _ _ _
    omega
  · rw [if_neg hx] at h
    simp at h

/-- With 4 more this is at most the bound on the sizes, for every C₀ ≥ 1. -/
theorem tableQuery_le {x₀ : ℕ} (hx : 18 ≤ x₀) (l : ℕ) {lam B : ℕ} (hlam : 1 ≤ lam) (hB : 1 ≤ B) {C : ℕ} (hC : 1 ≤ C) :
    ((Levels.Gen.K x₀ l + 2 * Levels.Gen.K x₀ l * lam + B + 3 + 4 : ℕ) : ℝ) ≤ sizeBound x₀ C l lam B := by
  have hX := base_ge hx l hlam hB
  have hK : (8 : ℝ) ≤ Levels.Gen.K x₀ l := by
    have := ClauseBound.Gen.Rate.big_le_K hx l
    exact_mod_cast (by omega : 8 ≤ Levels.Gen.K x₀ l)
  have h1 : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
  have h2 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have h3 : 2 ≤ C * Levels.Gen.K x₀ l := by
    have := ClauseBound.Gen.Rate.big_le_K hx l
    nlinarith
  unfold sizeBound
  refine le_trans ?_ (pow_le_pow_right₀ (by linarith) h3)
  push_cast
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (Levels.Gen.K x₀ l : ℝ) - 8) (by linarith : (0 : ℝ) ≤ (lam : ℝ) + B - 2), mul_self_nonneg ((Levels.Gen.K x₀ l : ℝ) * ((lam : ℝ) + B) - 8), mul_nonneg (by linarith : (0 : ℝ) ≤ (Levels.Gen.K x₀ l : ℝ)) (by linarith : (0 : ℝ) ≤ (B : ℝ) - 1), mul_nonneg (by linarith : (0 : ℝ) ≤ (Levels.Gen.K x₀ l : ℝ)) (by linarith : (0 : ℝ) ≤ (lam : ℝ) - 1)]

end ExplicitCost
