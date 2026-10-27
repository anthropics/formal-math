/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FixedWidthSteps.RouteDefs
public import GeneralPieces.Num.PartAUse
public import GeneralPieces.Num.Between
public import GeneralPieces.Num.Remarks

/-! # The sentences about numbers

Proofs of `ChainOfInequalities`, `RateOfThePairs`, `ConditionsHoldEventually`, `ReadAsThree`
(RouteDefs.lean) and of `FixedWidth.ProvisoHolds`, from part (a) of the theorem on the general
recursion (proof/rates/GeneralPieces/Num/PartA.lean, PartAUse.lean, Asymptotic.lean) and from the
remarks on the proof of part (c) (proof/rates/GeneralPieces/Num/Remarks.lean, Between.lean). -/

public section

namespace FixedWidthSteps

open Groundwork PaddedDescent.F Levels.Gen MainTheoremForms FixedWidth

/-- e_ℓ ≥ ½ρ^ℓ ≥ 2^{−ℓ−1} ≥ 1/log K_ℓ, and a number between 0.85ρ^ℓ and ρ^ℓ lies in [e_ℓ, 2e_ℓ]. -/
theorem chainOfInequalities : ChainOfInequalities := by
  intro ρ x₀ l hρ hρ1 hx
  have hA := GeneralPieces.PartA.thmRunningTime_a ρ x₀ hρ hρ1 hx
  have hlog : (2 : ℝ) ^ (l + 1) ≤ lg (K x₀ l) := GeneralPieces.PartAUse.two_pow_le_logK hA (by omega) l
  refine ⟨(hA.e_bounds l).1, ?_, one_div_le_one_div_of_le (by positivity) hlog, fun r h1 h2 => GeneralPieces.Asymptotic.between ρ x₀ l r hρ hx h1 h2⟩
  have h : (1 / 2 : ℝ) ^ l ≤ ρ ^ l := pow_le_pow_left₀ (by norm_num) hρ l
  have e : 1 / (2 : ℝ) ^ (l + 1) = 1 / 2 * (1 / 2) ^ l := by rw [pow_succ, one_div_pow]; field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

/-- e_ℓ ≤ (3x₀+6)/(log K_ℓ)^{α'}. -/
theorem rateOfThePairs : RateOfThePairs := by
  intro ρ x₀ l hρ hρ1 hx
  have hA := GeneralPieces.PartA.thmRunningTime_a ρ x₀ hρ hρ1 hx
  have hlog : (2 : ℝ) ^ (l + 1) ≤ Real.logb 2 (K x₀ l) := GeneralPieces.PartAUse.two_pow_le_logK hA (by omega) l
  have hL : 0 < Real.logb 2 (K x₀ l) := lt_of_lt_of_le (by positivity) hlog
  have hρ0 : 0 < ρ := by linarith
  have hα1 : Real.logb 2 (1 / ρ) ≤ 1 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_one, div_le_iff₀ hρ0]; linarith
  have ha : (1 : ℝ) ≤ 3 * x₀ + 6 := by have : (0 : ℝ) ≤ x₀ := Nat.cast_nonneg _; linarith
  have h0 : 0 ≤ ρ ^ l := by positivity
  have h1 : e ρ x₀ l ≤ ((3 * x₀ + 6) / Real.logb 2 (K x₀ l)) ^ Real.logb 2 (1 / ρ) := by
    have := (hA.e_bounds l).2; have := hA.rho_pow l; linarith
  have h2 : (3 * (x₀ : ℝ) + 6) ^ Real.logb 2 (1 / ρ) ≤ 3 * x₀ + 6 := by
    have := Real.rpow_le_rpow_of_exponent_le ha hα1
    rwa [Real.rpow_one] at this
  rw [Real.div_rpow (by linarith) hL.le] at h1
  have h3 : 0 < Real.logb 2 (K x₀ l) ^ Real.logb 2 (1 / ρ) := Real.rpow_pos_of_pos hL _
  show e ρ x₀ l ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.logb 2 (K x₀ l) ^ Real.logb 2 (1 / ρ)
  push_cast
  exact h1.trans (div_le_div_of_nonneg_right h2 h3.le)

/-- The conditions n ≥ K₀^17 and k ≤ (log n)^{1/4} hold for all but finitely many n when k is fixed. -/
theorem conditionsHoldEventually : ConditionsHoldEventually := by
  intro k K₀
  obtain ⟨n₀, h⟩ := GeneralPieces.Remarks.conditions_eventually k K₀
  refine ⟨n₀, fun n hn => ⟨(h n hn).1, ?_⟩⟩
  have hl : 0 ≤ Real.logb 2 n := by
    rcases Nat.eq_zero_or_pos n with rfl | hp
    · simp
    · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hp)
  calc (k : ℝ) ^ 4 ≤ (Real.logb 2 n ^ (1 / 4 : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) (h n hn).2 4
    _ = lg n := by rw [← Real.rpow_natCast, ← Real.rpow_mul hl]; norm_num; rfl

/-- A formula with k ≤ 2 is read as a 3-CNF. -/
theorem readAsThree : ReadAsThree := fun _ _ φ hk h => GeneralPieces.Remarks.read_as_three φ hk h

end FixedWidthSteps

namespace FixedWidth

open Groundwork PaddedDescent.F

/-- «… as is the case for ρ = 11/12 and for ρ = 1/√2.» The numbers are those of
proof/rates/GeneralPieces/Num/Between.lean: 11^ℓ/12^ℓ, and 2^{−ℓ/2} for even ℓ, (7/5)·2^{−(ℓ+1)/2}
for odd ℓ. They are computed from ℓ alone, in time polynomial in ℓ. -/
theorem provisoHolds : ProvisoHolds := by
  intro x₀
  refine ⟨⟨fun p => (11 ^ p.1.length, 12 ^ p.1.length), PolyT.comp (by fun_prop : PolyT fun u : U => (11 ^ u.length, 12 ^ u.length)) (PolyT.fst PolyT.id'), fun l => ?_⟩,
    ⟨fun p => (GeneralPieces.Between.num p.1.length, GeneralPieces.Between.den p.1.length), PolyT.comp GeneralPieces.Between.num_den_polyT (PolyT.fst PolyT.id'), fun l => ?_⟩⟩
  · dsimp only
    rw [List.length_replicate, GeneralPieces.Between.eleven_pow]
    have h : (0 : ℝ) ≤ (11 / 12) ^ l := by positivity
    exact ⟨by linarith, le_rfl⟩
  · dsimp only
    rw [List.length_replicate]
    exact GeneralPieces.Between.between_half l

end FixedWidth
