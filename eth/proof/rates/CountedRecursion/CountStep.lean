/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.LevelBound
public import GeneralPieces.Rec.Count
import Mathlib.Tactic

/-! # The count of one level

Proof of Theorem A (b): «So the total number of operations is at most |𝓘|^{|ℛ|}((K^g +
𝒯·2^{2N/K}τ)Ξ^{(c+4)C₁} + 2Ξ^{C₃}) + (2|𝓘| + 2)2^{cλ} + Ξ^{C₃} ≤ Ξ^{cg⁴/4+g+C₄}·𝒯·2^{2N/K+cλ} ≤
2^{e_{ℓ+1}N}·Ξ^{cg⁴/2+g+K²+C₄+(c+5)C₀K²}.»
The two inequalities in real variables are `GeneralPieces.Count.count_first` and `count_second`.
Here the costs of `RecursionDefs.lean` are brought to the form of the left side (`own_le`):
a query to the pieces costs 2^{cΛ} + 2 and not 2^{cΛ}, a query to the tables t ≥ 1, and a call 2
more than the bound; these go into three more factors Ξ. The bound for 𝒯 is the premise
`BoundBelow`; e_j ≥ 0 is taken from part (a) of the theorem, the premise `Levels.Gen.PartA`. C₄ = 3C +
c + 7. -/

public section

namespace ExplicitCost

open Levels.Gen Printed QueryMachines

/-- The costs of one level, in real variables, in the form of the printed sum; Y stands for Ξ^C and
Z for Ξ³. -/
theorem own_le_aux {Y Z T s u a κ q t : ℝ} (hY : 1 ≤ Y) (hZ : 8 ≤ Z) (hT : 1 ≤ T) (hs : 1 ≤ s) (hu : 1 ≤ u) (ht : 1 ≤ t) (ha : 0 ≤ a) :
    a * (Y * κ) + q + Y + a * ((s * Y * (u + 2) + s * Y * t + 2) * T + 2) ≤ a * ((κ + t * T * s * (u * (Y * Z))) * Y + 2 * Y) + q + Y := by
  obtain ⟨w, hw⟩ : ∃ w, w = s * Y * (u * t) := ⟨_, rfl⟩
  have hut : 1 ≤ u * t := one_le_mul_of_one_le_of_one_le hu ht
  have hsY : 1 ≤ s * Y := one_le_mul_of_one_le_of_one_le hs hY
  have hw1 : 1 ≤ w := by rw [hw]; exact one_le_mul_of_one_le_of_one_le hsY hut
  have h1 : u + 2 + t ≤ 4 * (u * t) := by nlinarith [mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 ht)]
  have h2 : s * Y * (u + 2) + s * Y * t + 2 ≤ 6 * w := by
    have a1 : s * Y * (u + 2 + t) ≤ s * Y * (4 * (u * t)) := mul_le_mul_of_nonneg_left h1 (by linarith)
    have e1 : s * Y * (u + 2) + s * Y * t = s * Y * (u + 2 + t) := by ring
    have e2 : s * Y * (4 * (u * t)) = 4 * w := by rw [hw]; ring
    linarith
  have h3 : 6 * w ≤ Z * Y * w := by
    have a1 : (8 : ℝ) * 1 ≤ Z * Y := mul_le_mul hZ hY (by norm_num) (by linarith)
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h4 : (s * Y * (u + 2) + s * Y * t + 2) * T ≤ Z * Y * w * T := mul_le_mul_of_nonneg_right (h2.trans h3) (by linarith)
  have h5 : (s * Y * (u + 2) + s * Y * t + 2) * T + 2 ≤ t * T * s * (u * (Y * Z)) * Y + 2 * Y := by
    have e : t * T * s * (u * (Y * Z)) * Y = Z * Y * w * T := by rw [hw]; ring
    rw [e]
    linarith
  have h6 := mul_le_mul_of_nonneg_left h5 ha
  have e : a * ((κ + t * T * s * (u * (Y * Z))) * Y + 2 * Y) = a * (Y * κ) + a * (t * T * s * (u * (Y * Z)) * Y + 2 * Y) := by ring
  rw [e]
  linarith

/-- The same with the powers of Ξ. X = Ξ, s = 2^{2N/K}, u = 2^{cΛ}, a the number of functions ι : ℛ
→ 𝓘, κ = K^g, T the bound for the level below (the premise `BoundBelow`), t the price of a query to
the tables. -/
theorem own_le {X T s u a κ q t : ℝ} (C : ℕ) (hX : 2 ≤ X) (hT : 1 ≤ T) (hs : 1 ≤ s) (hu : 1 ≤ u) (ht : 1 ≤ t) (ha : 0 ≤ a) :
    a * (X ^ C * κ) + q + X ^ C + a * ((s * X ^ C * (u + 2) + s * X ^ C * t + 2) * T + 2) ≤
      a * ((κ + t * T * s * (u * X ^ (C + 3))) * X ^ C + 2 * X ^ C) + q + X ^ C := by
  have hX3 : (8 : ℝ) ≤ X ^ 3 := by
    have : (2 : ℝ) ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ (by norm_num) hX 3
    linarith
  rw [pow_add]
  exact own_le_aux (one_le_pow₀ (by linarith)) hX3 hT hs hu ht ha

/-- `CountStepFrom`, with C₄ = 3C + c + 7. -/
theorem countStepFrom : CountStepFrom := by
  intro hL hBB' hA c C
  refine ⟨C + (C + 3) + C + c + 4, fun ρ x₀ C₀ l lam B j t hN hj ht => ?_⟩
  obtain ⟨hΛ, hBB⟩ := pos_of_chainLabel hL hN (by omega : j + 1 ≤ l)
  obtain ⟨hΛj, hBj⟩ := pos_of_chainLabel hL hN (by omega : j ≤ l)
  have hx := hN.x₀_ge
  have hx1 : 1 ≤ x₀ := by omega
  have hXn := four_mul_le_xiAt hx1 ρ c l lam B j hBB
  have hlev := hBB' ρ c x₀ C₀ l lam B j hN hj
  obtain ⟨T, hT⟩ : ∃ T, T = levelBound ρ c x₀ C₀ l lam B j := ⟨_, rfl⟩
  obtain ⟨Λ, hΛd⟩ : ∃ Λ : ℕ, Λ = lamAt ρ c x₀ l lam B (j + 1) := ⟨_, rfl⟩
  obtain ⟨Xn, hXd⟩ : ∃ Xn : ℕ, Xn = xiAt ρ c x₀ l lam B j := ⟨_, rfl⟩
  have hXe : Xn = g x₀ j ^ 2 * (Λ + bitsAt ρ c x₀ l lam B (j + 1)) := by rw [hXd, hΛd]; rfl
  rw [← hT, ← hΛd, ← hXd] at hlev
  rw [← hΛd, ← hXd] at hXn
  rw [← hΛd] at hΛ
  have hg2 : 2 ≤ g x₀ j := le_trans (Nat.pow_le_pow_right (by norm_num) hx1 : 2 ^ 1 ≤ 2 ^ x₀) (two_pow_le_g x₀ j)
  have hKpos : (0 : ℝ) < K x₀ j := by exact_mod_cast K_pos x₀ j
  -- 1 ≤ T
  have hT1 : 1 ≤ T := by
    rw [hT]
    unfold levelBound timeBound
    rw [baseAt_cast]
    have he : 0 ≤ e ρ x₀ j := le_trans (by have := hN.rho_ge; positivity) (hA.e_ge ρ x₀ j hN.rho_ge hN.rho_lt hN.x₀_ge)
    have hb : (1 : ℝ) ≤ (baseAt ρ c x₀ l lam B j : ℝ) := by
      have : 1 ≤ baseAt ρ c x₀ l lam B j := Nat.mul_pos (K_pos x₀ j) (by omega)
      exact_mod_cast this
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by norm_num) (by positivity)) (one_le_pow₀ hb)
  -- the facts on natural numbers
  have f1 : ((2 * Λ) ^ c) ^ ClauseBound.Alg.nRectG (g x₀ j) (g x₀ j) ≤ Xn ^ (c * (g x₀ j ^ 4 / 4)) :=
    calc ((2 * Λ) ^ c) ^ ClauseBound.Alg.nRectG (g x₀ j) (g x₀ j) ≤ (Xn ^ c) ^ ClauseBound.Alg.nRectG (g x₀ j) (g x₀ j) := Nat.pow_le_pow_left (Nat.pow_le_pow_left (by omega) c) _
      _ = Xn ^ (c * ClauseBound.Alg.nRectG (g x₀ j) (g x₀ j)) := by rw [← pow_mul]
      _ ≤ Xn ^ (c * (g x₀ j ^ 4 / 4)) := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ ((Nat.le_div_iff_mul_le (by norm_num)).2 (by
          have := ClauseBound.Gen.Rate.four_nRect_le (g x₀ j)
          omega)))
  have f2 : K x₀ j ^ g x₀ j ≤ Xn ^ g x₀ j := by rw [hXe]; exact GeneralPieces.Remarks.K_pow_le x₀ j Λ _ hΛ
  have f3 : (2 * (2 * Λ) ^ c + 2) * 2 ^ (c * Λ) ≤ Xn ^ (c + 1) * (2 ^ (c * Λ) * Xn ^ C) := by rw [hXe]; exact GeneralPieces.Remarks.card_term_le (g x₀ j) c Λ _ _ C hg2 hΛ le_rfl
  have f4 : K x₀ j * (c * Λ) ≤ g x₀ j ^ 4 * Λ := GeneralPieces.Rate.c_lam_le hx hN.x₀_c j Λ
  -- to real numbers
  obtain ⟨X, hXr⟩ : ∃ X : ℝ, X = (Xn : ℝ) := ⟨_, rfl⟩
  have hX2 : 2 ≤ X := by rw [hXr]; exact_mod_cast (by omega : 2 ≤ Xn)
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have r1 : ((((2 * Λ) ^ c) ^ ClauseBound.Alg.nRectG (g x₀ j) (g x₀ j) : ℕ) : ℝ) ≤ X ^ (c * (g x₀ j ^ 4 / 4)) := by rw [hXr]; exact_mod_cast f1
  have r2 : ((K x₀ j ^ g x₀ j : ℕ) : ℝ) ≤ X ^ g x₀ j := by rw [hXr]; exact_mod_cast f2
  have hu : (1 : ℝ) ≤ (2 : ℝ) ^ (c * Λ) := one_le_pow₀ (by norm_num)
  have hs : (1 : ℝ) ≤ (2 : ℝ) ^ (g x₀ j ^ 3 * Λ * (2 * g x₀ j / K x₀ j)) := one_le_pow₀ (by norm_num)
  have r3 : ((2 * (2 * Λ) ^ c + 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (c * Λ) + 2) ≤ X ^ (c + 1) * ((2 : ℝ) ^ (c * Λ) * X ^ (C + 3)) := by
    have h1 : ((2 * (2 * Λ) ^ c + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (c * Λ) ≤ X ^ (c + 1) * ((2 : ℝ) ^ (c * Λ) * X ^ C) := by rw [hXr]; exact_mod_cast f3
    have h2 : ((2 * (2 * Λ) ^ c + 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (c * Λ) + 2) ≤ 3 * (((2 * (2 * Λ) ^ c + 2 : ℕ) : ℝ) * (2 : ℝ) ^ (c * Λ)) := by
      have : (0 : ℝ) ≤ ((2 * (2 * Λ) ^ c + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [mul_nonneg this (sub_nonneg.2 hu)]
    have h3 : (3 : ℝ) ≤ X ^ 3 := by
      have : (2 : ℝ) ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ (by norm_num) hX2 3
      linarith
    calc ((2 * (2 * Λ) ^ c + 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (c * Λ) + 2) ≤ 3 * (X ^ (c + 1) * ((2 : ℝ) ^ (c * Λ) * X ^ C)) := h2.trans (by linarith)
      _ ≤ X ^ 3 * (X ^ (c + 1) * ((2 : ℝ) ^ (c * Λ) * X ^ C)) := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = X ^ (c + 1) * ((2 : ℝ) ^ (c * Λ) * X ^ (C + 3)) := by ring
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htT : 1 ≤ (t : ℝ) * T := one_le_mul_of_one_le_of_one_le ht' hT1
  have hT0 : 0 ≤ T := by linarith
  -- the left side
  have eL : (solverOwn C ρ c x₀ l lam B (j + 1) : ℝ) + solverCalls ρ c x₀ l lam B (j + 1) * (((entryCost C ρ c x₀ l lam B j t : ℕ) + 2) * T + 2) =
      ((((2 * Λ) ^ c) ^ ClauseBound.Alg.nRectG (g x₀ j) (g x₀ j) : ℕ) : ℝ) * (X ^ C * ((K x₀ j ^ g x₀ j : ℕ) : ℝ)) + ((2 * (2 * Λ) ^ c + 2 : ℕ) : ℝ) * ((2 : ℝ) ^ (c * Λ) + 2) + X ^ C +
        ((((2 * Λ) ^ c) ^ ClauseBound.Alg.nRectG (g x₀ j) (g x₀ j) : ℕ) : ℝ) *
          (((2 : ℝ) ^ (g x₀ j ^ 3 * Λ * (2 * g x₀ j / K x₀ j)) * X ^ C * ((2 : ℝ) ^ (c * Λ) + 2) + (2 : ℝ) ^ (g x₀ j ^ 3 * Λ * (2 * g x₀ j / K x₀ j)) * X ^ C * t + 2) * T + 2) := by
    have e1 : solverOwn C ρ c x₀ l lam B (j + 1) = ((2 * Λ) ^ c) ^ ClauseBound.Alg.nRectG (g x₀ j) (g x₀ j) * (Xn ^ C * K x₀ j ^ g x₀ j) + (2 * (2 * Λ) ^ c + 2) * (2 ^ (c * Λ) + 2) + Xn ^ C := by
      rw [hΛd, hXd]; rfl
    have e2 : solverCalls ρ c x₀ l lam B (j + 1) = ((2 * Λ) ^ c) ^ ClauseBound.Alg.nRectG (g x₀ j) (g x₀ j) := by rw [hΛd]; rfl
    have e3 : entryCost C ρ c x₀ l lam B j t = 2 ^ (g x₀ j ^ 3 * Λ * (2 * g x₀ j / K x₀ j)) * Xn ^ C * (2 ^ (c * Λ) + 2) + 2 ^ (g x₀ j ^ 3 * Λ * (2 * g x₀ j / K x₀ j)) * Xn ^ C * t := by
      rw [hΛd, hXd]; rfl
    rw [e1, e2, e3, hXr]
    push_cast
    ring
  rw [← hT, ← hΛd, ← hXd, ← hXr, eL]
  rw [← hXr] at hlev
  refine (own_le C hX2 hT1 hs hu ht' (Nat.cast_nonneg _)).trans ?_
  have s1 := GeneralPieces.Count.count_first X ((t : ℝ) * T) _ _ _ _ _ (c * (g x₀ j ^ 4 / 4)) (g x₀ j) c C (C + 3) C hX2 htT hs hu r1 (Nat.cast_nonneg _) r2 r3
  refine s1.trans ?_
  -- the powers of 2
  obtain ⟨N, hNd⟩ : ∃ N : ℝ, N = (K x₀ (j + 1) : ℝ) ^ 2 * Λ := ⟨_, rfl⟩
  have eN : N = (g x₀ j : ℝ) ^ 4 * Λ := by
    rw [hNd]
    have : (K x₀ (j + 1) : ℝ) ^ 2 = (g x₀ j : ℝ) ^ 4 := by exact_mod_cast K_succ_sq x₀ j
    rw [this]
  have hsu : (2 : ℝ) ^ (g x₀ j ^ 3 * Λ * (2 * g x₀ j / K x₀ j)) * (2 : ℝ) ^ (c * Λ) ≤ (2 : ℝ) ^ (2 * N / K x₀ j + (c : ℝ) * Λ) := by
    rw [← pow_add, ← Real.rpow_natCast (2 : ℝ) (g x₀ j ^ 3 * Λ * (2 * g x₀ j / K x₀ j) + c * Λ)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have h1 : ((2 * g x₀ j / K x₀ j : ℕ) : ℝ) ≤ ((2 * g x₀ j : ℕ) : ℝ) / K x₀ j := Nat.cast_div_le
    have h2 : ((g x₀ j : ℝ) ^ 3 * Λ) * ((2 * g x₀ j / K x₀ j : ℕ) : ℝ) ≤ ((g x₀ j : ℝ) ^ 3 * Λ) * (((2 * g x₀ j : ℕ) : ℝ) / K x₀ j) := mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : ((g x₀ j : ℝ) ^ 3 * Λ) * (((2 * g x₀ j : ℕ) : ℝ) / K x₀ j) = 2 * N / K x₀ j := by
      rw [eN]
      push_cast
      ring
    have h4 := h2.trans_eq h3
    push_cast
    linarith
  have hcN : (c : ℝ) * Λ ≤ N / K x₀ j := by
    rw [le_div_iff₀ hKpos, eN]
    have : ((K x₀ j * (c * Λ) : ℕ) : ℝ) ≤ ((g x₀ j ^ 4 * Λ : ℕ) : ℝ) := by exact_mod_cast f4
    push_cast at this
    linarith
  have hlev' : T ≤ (2 : ℝ) ^ (e ρ x₀ (j + 1) * N - 3 * N / K x₀ j) * X ^ (c * (g x₀ j ^ 4 / 4) + K x₀ j ^ 2 + (c + 5) * C₀ * K x₀ j ^ 2) := by
    have e1 : e ρ x₀ (j + 1) * N = e ρ x₀ (j + 1) * (K x₀ (j + 1) : ℝ) ^ 2 * Λ := by rw [hNd]; ring
    rw [e1, hNd]
    exact hlev
  have s2 := GeneralPieces.Count.count_second X T _ (2 * N / K x₀ j + (c : ℝ) * Λ) (e ρ x₀ (j + 1) * N) (c * (g x₀ j ^ 4 / 4)) (g x₀ j) (C + (C + 3) + C + c + 4) (K x₀ j ^ 2) ((c + 5) * C₀ * K x₀ j ^ 2) (by linarith) hlev' (by
    have : 3 * N / K x₀ j = 2 * N / K x₀ j + N / K x₀ j := by ring
    linarith)
  have hexp : 2 * (c * (g x₀ j ^ 4 / 4)) + g x₀ j + K x₀ j ^ 2 + (C + (C + 3) + C + c + 4) + (c + 5) * C₀ * K x₀ j ^ 2 ≤
      c * g x₀ j ^ 4 / 2 + g x₀ j + K x₀ j ^ 2 + (C + (C + 3) + C + c + 4) + (c + 5) * C₀ * K x₀ j ^ 2 := by
    have h1 : 2 * (c * (g x₀ j ^ 4 / 4)) ≤ c * g x₀ j ^ 4 / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      have := four_mul_div_g hx1 j
      calc 2 * (c * (g x₀ j ^ 4 / 4)) * 2 = c * (4 * (g x₀ j ^ 4 / 4)) := by ring
        _ = c * g x₀ j ^ 4 := by rw [this]
        _ ≤ c * g x₀ j ^ 4 := le_rfl
    omega
  have hz : (0 : ℝ) < (2 : ℝ) ^ (e ρ x₀ (j + 1) * N) := Real.rpow_pos_of_pos (by norm_num) _
  have eZ : e ρ x₀ (j + 1) * (K x₀ (j + 1) : ℝ) ^ 2 * Λ = e ρ x₀ (j + 1) * N := by rw [hNd, mul_assoc]
  rw [eZ]
  calc X ^ (c * (g x₀ j ^ 4 / 4) + g x₀ j + (C + (C + 3) + C + c + 4)) * ((t : ℝ) * T) * ((2 : ℝ) ^ (g x₀ j ^ 3 * Λ * (2 * g x₀ j / K x₀ j)) * (2 : ℝ) ^ (c * Λ))
      ≤ X ^ (c * (g x₀ j ^ 4 / 4) + g x₀ j + (C + (C + 3) + C + c + 4)) * ((t : ℝ) * T) * (2 : ℝ) ^ (2 * N / K x₀ j + (c : ℝ) * Λ) := mul_le_mul_of_nonneg_left hsu (by positivity)
    _ = t * (X ^ (c * (g x₀ j ^ 4 / 4) + g x₀ j + (C + (C + 3) + C + c + 4)) * T * (2 : ℝ) ^ (2 * N / K x₀ j + (c : ℝ) * Λ)) := by ring
    _ ≤ t * ((2 : ℝ) ^ (e ρ x₀ (j + 1) * N) * X ^ (2 * (c * (g x₀ j ^ 4 / 4)) + g x₀ j + K x₀ j ^ 2 + (C + (C + 3) + C + c + 4) + (c + 5) * C₀ * K x₀ j ^ 2)) := mul_le_mul_of_nonneg_left s2 (by positivity)
    _ ≤ t * ((2 : ℝ) ^ (e ρ x₀ (j + 1) * N) * X ^ (c * g x₀ j ^ 4 / 2 + g x₀ j + K x₀ j ^ 2 + (C + (C + 3) + C + c + 4) + (c + 5) * C₀ * K x₀ j ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 hexp) hz.le) (by positivity)

/-- `CountStep`. -/
theorem countStep : CountStep := countStepFrom chainLabel boundBelow partAPrinted

end ExplicitCost
