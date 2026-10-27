/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedToPadded.Defs
import ToTuring.Lib.Nat1
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-! # The number e′ and the exponent

Proofs of `CutNumberFacts`, `PrecisionCarriesOver`, `NeedSuffices` and `NeedIsSmall` (Defs.lean). -/

public section

namespace QueryMachines.Bridge.Proof

open Groundwork PaddedDescent.F Printed CliqueLevels

/-- n in unary has n units. -/
theorem length_unary (n : ℕ) : (unary n).length = n := List.length_replicate

/-! ### The number e′ -/

/-- log K_ℓ ≥ 1. -/
theorem one_le_logK {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ} (hL : Levels K e C₀) (l : ℕ) : 1 ≤ Real.logb 2 (K l) := by
  have h2 : (2 : ℝ) ≤ K l := by exact_mod_cast hL.K_two l
  rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]
  exact h2

/-- e_ℓ > 0. -/
theorem e_pos {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ} (hL : Levels K e C₀) (l : ℕ) : 0 < e l := by
  have h1 := one_le_logK hL l
  exact lt_of_lt_of_le (by positivity) (hL.e_ge l)

/-- The denominator is not 0. -/
theorem den_pos {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ} {num : U × U → ℕ × ℕ} (hL : Levels K e C₀) (hN : NumberBetween K e num) (l : ℕ) : 0 < (num (unary l, unary (K l))).2 := by
  rcases Nat.eq_zero_or_pos (num (unary l, unary (K l))).2 with h | h
  · have h1 := (hN.2 l).1
    rw [h, Nat.cast_zero, div_zero] at h1
    exact absurd (e_pos hL l) (not_lt.2 h1)
  · exact h

/-! ### Rounding up, and the number of bits -/

/-- ⌈min(a/b, 1)·n⌉ from below, for b > 0. -/
theorem le_ceilMul {a b : ℕ} (hb : 0 < b) (n : ℕ) : min ((a : ℝ) / b) 1 * n ≤ ceilMul a b n := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  unfold ceilMul
  split
  · calc min ((a : ℝ) / b) 1 * n ≤ 1 * n := mul_le_mul_of_nonneg_right (min_le_right _ _) hn
      _ = n := one_mul _
  · have h1 : a * n ≤ b * ((a * n + b - 1) / b) := by
      have := Nat.div_add_mod (a * n + b - 1) b
      have := Nat.mod_lt (a * n + b - 1) hb
      omega
    have h2 : (a : ℝ) * n ≤ b * ((a * n + b - 1) / b : ℕ) := by exact_mod_cast h1
    calc min ((a : ℝ) / b) 1 * n ≤ (a : ℝ) / b * n := mul_le_mul_of_nonneg_right (min_le_left _ _) hn
      _ = (a : ℝ) * n / b := by ring
      _ ≤ _ := by rw [div_le_iff₀ hb']; linarith

/-- ⌈min(a/b, 1)·n⌉ from above, for b > 0. -/
theorem ceilMul_le {a b : ℕ} (hb : 0 < b) (n : ℕ) : (ceilMul a b n : ℝ) ≤ min ((a : ℝ) / b) 1 * n + 1 := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  unfold ceilMul
  split
  · rename_i h
    have h1 : (1 : ℝ) ≤ (a : ℝ) / b := by rw [le_div_iff₀ hb', one_mul]; exact_mod_cast h
    rw [min_eq_right h1]; linarith
  · rename_i h
    have h1 : (a : ℝ) / b ≤ 1 := by rw [div_le_iff₀ hb', one_mul]; exact_mod_cast (not_le.1 h).le
    rw [min_eq_left h1]
    have h2 : (((a * n + b - 1) / b : ℕ) : ℝ) ≤ ((a * n + b - 1 : ℕ) : ℝ) / b := Nat.cast_div_le
    have h3 : ((a * n + b - 1 : ℕ) : ℝ) ≤ (a : ℝ) * n + b := by exact_mod_cast Nat.sub_le _ _
    have h4 : ((a : ℝ) * n + b) / b = (a : ℝ) / b * n + 1 := by field_simp
    calc _ ≤ ((a * n + b - 1 : ℕ) : ℝ) / b := h2
      _ ≤ ((a : ℝ) * n + b) / b := div_le_div_of_nonneg_right h3 hb'.le
      _ = _ := h4

/-- A number m ≥ 1 has at most log m + 1 bits. -/
theorem size_le_log {m : ℕ} (hm : 1 ≤ m) : (Nat.size m : ℝ) ≤ Real.logb 2 m + 1 := by
  have hs : 1 ≤ Nat.size m := Nat.size_pos.2 hm
  have h1 : 2 ^ (Nat.size m - 1) ≤ m := Nat.lt_size.1 (by omega)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h2 : ((Nat.size m - 1 : ℕ) : ℝ) ≤ Real.logb 2 m := by
    rw [Real.le_logb_iff_rpow_le one_lt_two hm', Real.rpow_natCast]
    exact_mod_cast h1
  have h3 : ((Nat.size m - 1 : ℕ) : ℝ) = (Nat.size m : ℝ) - 1 := by rw [Nat.cast_sub hs, Nat.cast_one]
  linarith

/-! ### The exponent -/

/-- The exponent at the index (ℓ, k), written out. -/
theorem needOf_eq (num : U × U → ℕ × ℕ) (C₀ l k lam B : ℕ) : needOf num C₀ ((unary l, unary k), unary lam, unary B) =
    ceilMul (num (unary l, unary k)).1 (num (unary l, unary k)).2 (k ^ 2 * lam) + C₀ * k ^ 2 * Nat.size (k * (lam + B + 1)) + 2 := by
  simp only [needOf, length_unary]

end QueryMachines.Bridge.Proof

namespace QueryMachines.Bridge

open Groundwork PaddedDescent.F Printed CliqueLevels Proof

/-- The number e′ lies in [e, 2e], is positive and at most 1, and is computed as the fraction
`cutFraction num`. -/
theorem cutNumberFacts : CutNumberFacts := by
  intro K e C₀ num hL hN
  refine ⟨?_, fun l => ?_⟩
  · have := hN.1
    unfold cutFraction; fun_prop
  · obtain ⟨h1, h2⟩ := hN.2 l
    have he := e_pos hL l
    have hb : (0 : ℝ) < (num (unary l, unary (K l))).2 := by exact_mod_cast den_pos hL hN l
    refine ⟨lt_min (he.trans_le h1) one_pos, le_min h1 (hL.e_le l), (min_le_left _ _).trans h2, min_le_right _ _, ?_⟩
    unfold cutFraction cutNumber
    dsimp only
    rw [Nat.cast_min, ← min_div_div_right hb.le, div_self hb.ne']

/-- A precision function for e is one for e′, with twice the constant. -/
theorem precisionCarriesOver : PrecisionCarriesOver := by
  rintro e e' slU C ⟨h1, h2, h3⟩ h
  refine ⟨h1, fun l => (h2 l).trans (h l).1, fun l => ?_⟩
  obtain ⟨g1, g2, g3⟩ := h l
  have he : 0 < e l := lt_of_lt_of_le (by positivity) (h2 l)
  have he' : 0 < e' l := he.trans_le g1
  have hh : 2 / e l ≤ (2 / e' l) ^ 2 := by
    rw [div_pow, div_le_div_iff₀ he (by positivity)]
    nlinarith
  calc (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ (2 / e l) ^ C := h3 l
    _ ≤ ((2 / e' l) ^ 2) ^ C := pow_le_pow_left₀ (by positivity) hh C
    _ = (2 / e' l) ^ (2 * C) := (pow_mul _ 2 C).symm

/-- 2^need is at least 4 times the printed bound for e′, C₀ and B + 1. -/
theorem needSuffices : NeedSuffices := by
  intro K e C₀ num hL hN l lam B _
  rw [needOf_eq]
  have h1 := le_ceilMul (a := (num (unary l, unary (K l))).1) (den_pos hL hN l) (K l ^ 2 * lam)
  generalize ceilMul (num (unary l, unary (K l))).1 (num (unary l, unary (K l))).2 (K l ^ 2 * lam) = c at h1 ⊢
  have h2 : (2 : ℝ) ^ (cutNumber K num l * (K l : ℝ) ^ 2 * lam) ≤ (2 : ℝ) ^ c := by
    rw [← Real.rpow_natCast (2 : ℝ) c]
    refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    unfold cutNumber
    push_cast at h1
    linarith
  have h3 : ((K l : ℝ) * ((lam : ℝ) + ((B + 1 : ℕ) : ℝ))) ^ (C₀ * K l ^ 2) ≤ (2 : ℝ) ^ (C₀ * K l ^ 2 * Nat.size (K l * (lam + B + 1))) := by
    have h4 : K l * (lam + B + 1) ≤ 2 ^ Nat.size (K l * (lam + B + 1)) := (Nat.lt_size_self _).le
    have h5 : (K l : ℝ) * ((lam : ℝ) + ((B + 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ Nat.size (K l * (lam + B + 1)) := by
      have : ((K l * (lam + B + 1) : ℕ) : ℝ) ≤ ((2 ^ Nat.size (K l * (lam + B + 1)) : ℕ) : ℝ) := Nat.cast_le.2 h4
      push_cast at this ⊢
      linarith
    calc _ ≤ ((2 : ℝ) ^ Nat.size (K l * (lam + B + 1))) ^ (C₀ * K l ^ 2) := pow_le_pow_left₀ (by positivity) h5 _
      _ = _ := by rw [← pow_mul, Nat.mul_comm]
  unfold bound
  calc 4 * ((2 : ℝ) ^ (cutNumber K num l * (K l : ℝ) ^ 2 * lam) * ((K l : ℝ) * ((lam : ℝ) + ((B + 1 : ℕ) : ℝ))) ^ (C₀ * K l ^ 2))
      ≤ 4 * ((2 : ℝ) ^ c * (2 : ℝ) ^ (C₀ * K l ^ 2 * Nat.size (K l * (lam + B + 1)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul h2 h3 (by positivity) (by positivity)) (by norm_num)
    _ = (2 : ℝ) ^ (c + C₀ * K l ^ 2 * Nat.size (K l * (lam + B + 1)) + 2) := by rw [pow_add, pow_add]; ring

/-- need ≤ e′K²λ + (2C₀ + 1)·K²·log(K(λ + B)). -/
theorem needIsSmall : NeedIsSmall := by
  intro K e C₀ num hL hN l lam B hlam hB
  rw [needOf_eq]
  push_cast
  have h1 := ceilMul_le (a := (num (unary l, unary (K l))).1) (den_pos hL hN l) (K l ^ 2 * lam)
  generalize ceilMul (num (unary l, unary (K l))).1 (num (unary l, unary (K l))).2 (K l ^ 2 * lam) = c at h1 ⊢
  have hK : (2 : ℝ) ≤ K l := by exact_mod_cast hL.K_two l
  have hl1 : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hx : (4 : ℝ) ≤ (K l : ℝ) * ((lam : ℝ) + B) := by nlinarith
  have hL2 : 2 ≤ Real.logb 2 ((K l : ℝ) * ((lam : ℝ) + B)) := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith)]
    have : (2 : ℝ) ^ (2 : ℝ) = 4 := by rw [show (2 : ℝ) ^ (2 : ℝ) = (2 : ℝ) ^ ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [this]; exact hx
  have hm : 1 ≤ K l * (lam + B + 1) := Nat.mul_pos (by have := hL.K_two l; omega) (by omega)
  have h2 := size_le_log hm
  have h3 : Real.logb 2 ((K l * (lam + B + 1) : ℕ) : ℝ) ≤ Real.logb 2 ((K l : ℝ) * ((lam : ℝ) + B)) + 1 := by
    have h4 : ((K l * (lam + B + 1) : ℕ) : ℝ) ≤ 2 * ((K l : ℝ) * ((lam : ℝ) + B)) := by push_cast; nlinarith
    have h5 : Real.logb 2 (2 * ((K l : ℝ) * ((lam : ℝ) + B))) = 1 + Real.logb 2 ((K l : ℝ) * ((lam : ℝ) + B)) := by
      rw [Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one one_lt_two]
    have h6 := Real.logb_le_logb_of_le one_lt_two (by exact_mod_cast hm) h4
    linarith
  generalize Real.logb 2 ((K l : ℝ) * ((lam : ℝ) + B)) = L at *
  generalize (Nat.size (K l * (lam + B + 1)) : ℝ) = s at *
  have hs : s ≤ L + 2 := by linarith
  unfold cutNumber
  push_cast at h1 ⊢
  have hC : (0 : ℝ) ≤ C₀ := Nat.cast_nonneg _
  have hP : (4 : ℝ) ≤ (K l : ℝ) ^ 2 := by nlinarith
  have hCP : 0 ≤ (C₀ : ℝ) * (K l : ℝ) ^ 2 := by positivity
  have g1 : (C₀ : ℝ) * (K l : ℝ) ^ 2 * s ≤ (C₀ : ℝ) * (K l : ℝ) ^ 2 * (2 * L) := mul_le_mul_of_nonneg_left (by linarith) hCP
  have g2 : (3 : ℝ) ≤ (K l : ℝ) ^ 2 * L := by nlinarith
  linarith

end QueryMachines.Bridge
