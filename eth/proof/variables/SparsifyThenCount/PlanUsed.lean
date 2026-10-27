/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsifyThenCount.PlanUsedDefs
import SparsifyThenCount.Main
import VariableBound.MainPrinted
import ClauseBound.Alg.Decode
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # The plan is used: proofs

* `stPlanUsed : StPlanUsed`. The plan on the code of (k, φ) depends only on k and n (`planD_enc`),
  so it is enough to look at the formula without clauses. For it the merged exponent `eBD` is `eD`,
  because the algorithm for the bound in m
  is taken only if there is a clause (`eBD_nil`). Without a plan `eD` is n. The clause `timeN` of
  `Alg`, at q = 1, then gives 2^n ≤ D·2^(D·k²·n·rn(n)). This is false as soon as D·k²·rn(n) ≤ 1/2
  and n ≥ 2(D + 1) (`not_le_bound`).
* `stRateZero : StRateZero`: log y/√y tends to 0, and y = log₂(n+4) tends to infinity. -/

public section

namespace SparsifyThenCount

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN UniformInK VariableBound VariableBound.Decide Filter

namespace PlanUsedL

section
variable {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (slU : U → U)

/-- On the code of (k, φ), k ≥ 1, φ a k-CNF on n variables, the plan is that for k and n: it does
not depend on φ. -/
theorem planD_enc {k n : ℕ} (φ : Sat3.CNF n) (hk : 1 ≤ k) (hφ : SatK.IsKCNF k φ) :
    planD S pick slU (SatM.enc k φ) = planAtD S k n (pick (root17 n)).2 (slU (pick (root17 n)).1).length := by
  obtain ⟨hdk, hdf⟩ := Decode.stDecM k n φ hk hφ.1
  have hkU : kU (SatM.enc k φ) = k := by rw [kU, hdk, List.length_replicate]
  have hnU : nU (SatM.enc k φ) = n := by rw [nU, hdf, List.length_replicate]
  rw [planD, idxU, precU, hkU, hnU]

/-- The formula without clauses is a k-CNF. -/
theorem isKCNF_nil (k n : ℕ) : SatK.IsKCNF k ([] : Sat3.CNF n) := ⟨fun _ h => absurd h List.not_mem_nil, List.nodup_nil⟩

/-- On the code of the formula without clauses the merged exponent is the exponent of the plan, or n
if there is none. -/
theorem eBD_nil {k : ℕ} (n : ℕ) (hk : 1 ≤ k) :
    eBD S pick slU (SatM.enc k ([] : Sat3.CNF n)) = (planAtD S k n (pick (root17 n)).2 (slU (pick (root17 n)).1).length).getD n := by
  obtain ⟨-, hdf⟩ := Decode.stDecM k n [] hk (isKCNF_nil k n).1
  have hnU : nU (SatM.enc k ([] : Sat3.CNF n)) = n := by rw [nU, hdf, List.length_replicate]
  have hu : useMD S pick slU (SatM.enc k ([] : Sat3.CNF n)) = false := by
    rw [useMD, hdf]
    simp [Decode.toN]
  rw [eBD, hu, cond_false, eD, planD_enc S pick slU [] hk (isKCNF_nil k n), hnU]

end

/-- 2^n is not within D·2^(D·k²·n·r), rounded down, if D·k²·r ≤ 1/2 and n ≥ 2(D + 1). -/
theorem not_le_bound {D k n : ℕ} {r : ℝ} (hr : (D : ℝ) * (k : ℝ) ^ 2 * r ≤ 1 / 2) (hn : 2 * (D + 1) ≤ n) :
    ¬ (2 ^ n ≤ ⌊(D : ℝ) * (2 : ℝ) ^ ((D : ℝ) * (k : ℝ) ^ 2 * n * r)⌋₊) := by
  intro h
  have h0 : (0 : ℝ) ≤ (D : ℝ) * (2 : ℝ) ^ ((D : ℝ) * (k : ℝ) ^ 2 * n * r) := by positivity
  have h1 : ((2 ^ n : ℕ) : ℝ) ≤ (D : ℝ) * (2 : ℝ) ^ ((D : ℝ) * (k : ℝ) ^ 2 * n * r) := (Nat.cast_le.2 h).trans (Nat.floor_le h0)
  have h2 : (D : ℝ) * (k : ℝ) ^ 2 * n * r ≤ (n : ℝ) / 2 := by
    have : (D : ℝ) * (k : ℝ) ^ 2 * n * r = (D : ℝ) * (k : ℝ) ^ 2 * r * n := by ring
    rw [this]
    have h3 := mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg n)
    linarith
  have h3 : (2 : ℝ) ^ ((D : ℝ) * (k : ℝ) ^ 2 * n * r) ≤ (2 : ℝ) ^ ((n : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
  have h4 : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ ((n : ℝ) / 2) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_add (by norm_num), add_halves, Real.rpow_natCast]
    push_cast
    rfl
  have h5 : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) / 2) := by positivity
  have h6 : (2 : ℝ) ^ ((n : ℝ) / 2) ≤ D := by
    have h7 : (2 : ℝ) ^ ((n : ℝ) / 2) * (2 : ℝ) ^ ((n : ℝ) / 2) ≤ (D : ℝ) * (2 : ℝ) ^ ((n : ℝ) / 2) := by
      rw [← h4]
      exact h1.trans (mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg D))
    exact le_of_mul_le_mul_right h7 h5
  have h8 : (2 : ℝ) ^ (((D + 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ ((n : ℝ) / 2) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : ((2 * (D + 1) : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at this ⊢
    linarith
  have h9 : ((D + 1 : ℕ) : ℝ) < (2 : ℝ) ^ (((D + 1 : ℕ) : ℝ)) := by
    rw [Real.rpow_natCast]
    exact_mod_cast Nat.lt_two_pow_self
  have h10 : ((D + 1 : ℕ) : ℝ) = (D : ℝ) + 1 := by push_cast; rfl
  linarith

end PlanUsedL

open PlanUsedL

/-- If some function A with the exponent function `VariableBound.eBD S pick slU` is an algorithm for
the rates rn and rm, and rn tends to 0, then for every width k ≥ 1 and all large n the plan exists
on the code of (k, φ), for every k-CNF φ on n
variables. -/
theorem stPlanUsed : StPlanUsed := by
  intro Idx _ S pick slU rn rm A h hr k hk
  obtain ⟨D, hD⟩ := h.timeN 1
  have hpos : (0 : ℝ) < 1 / (2 * ((D : ℝ) + 1) * (k : ℝ) ^ 2) := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hr.eventually (gt_mem_nhds hpos))
  refine ⟨max N (2 * (D + 1)), fun n hn φ hφ => ?_⟩
  rw [planD_enc S pick slU φ hk hφ]
  by_contra hne
  have hnone : planAtD S k n (pick (root17 n)).2 (slU (pick (root17 n)).1).length = none := by
    cases hp : planAtD S k n (pick (root17 n)).2 (slU (pick (root17 n)).1).length with
    | none => rfl
    | some v => rw [hp] at hne; exact absurd rfl hne
  have hn1 : 1 ≤ n := by have := (le_max_right N (2 * (D + 1))).trans hn; omega
  have ht := hD k n [] hk hn1 (isKCNF_nil k n)
  rw [eBD_nil S pick slU n hk, hnone, Option.getD_none, one_mul, pow_one] at ht
  have hk0 : (0 : ℝ) < (k : ℝ) ^ 2 := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  have hsmall : (D : ℝ) * (k : ℝ) ^ 2 * rn n ≤ 1 / 2 := by
    have h1 : rn n < 1 / (2 * ((D : ℝ) + 1) * (k : ℝ) ^ 2) := hN n ((le_max_left _ _).trans hn)
    have h2 : (D : ℝ) * (k : ℝ) ^ 2 * rn n ≤ (D : ℝ) * (k : ℝ) ^ 2 * (1 / (2 * ((D : ℝ) + 1) * (k : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left h1.le (by positivity)
    have h3 : (D : ℝ) * (k : ℝ) ^ 2 * (1 / (2 * ((D : ℝ) + 1) * (k : ℝ) ^ 2)) = (D : ℝ) / ((D : ℝ) + 1) * (1 / 2) := by
      field_simp
    have h4 : (D : ℝ) / ((D : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    rw [h3] at h2
    linarith
  refine not_le_bound hsmall ((le_max_right _ _).trans hn) (le_trans ?_ ht)
  omega

/-- The rate log₂ log₂(n+4)/√(log₂(n+4)) tends to 0. -/
theorem stRateZero : StRateZero := by
  have h1 : Tendsto (fun y : ℝ => Real.log y / y ^ (1 / 2 : ℝ)) atTop (nhds 0) := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have h2 : Tendsto (fun n : ℕ => Real.logb 2 ((n : ℝ) + 4)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp (tendsto_atTop_add_const_right _ 4 tendsto_natCast_atTop_atTop)
  have h3 := (h1.comp h2).const_mul (1 / Real.log 2)
  rw [mul_zero] at h3
  refine h3.congr fun n => ?_
  simp only [Function.comp, SatK.rN, pow_one]
  rw [← Real.log_div_log (b := 2) (x := Real.logb 2 ((n : ℝ) + 4))]
  ring

end SparsifyThenCount
