/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Part.Upper
public import ClauseBound.Part.Lower

/-! # The two bounds on the number of partitions in logarithms to base 2

With κ = π·√(2/3)/ln 2 there are constants B and C with κ·√E − B·log₂ E − C ≤ log₂ p(E) for E ≥ 1
and log₂ p(E) ≤ κ·√E + C for all E.
Both follow by taking logarithms in p(E) ≤ exp(π·√(2E/3)) and in p(E) ≥ H·exp(π·√(2E/3))/E^B. The
asymptotic formula of Hardy and Ramanujan would give B = 1. -/

public section

namespace ClauseBound.Part

open Finset Partitions

namespace Bounds

/-- log₂ e^x = x/ln 2. -/
theorem logb_exp (x : ℝ) : Real.logb 2 (Real.exp x) = x / Real.log 2 := by rw [Real.logb, Real.log_exp]

/-- κ·√E = π·√(2/3)·√E/ln 2. -/
theorem kappa_mul (x : ℝ) : kappa * x = cHR * x / Real.log 2 := by
  rw [kappa]
  ring

end Bounds

open Bounds

/-- There are B and C with κ·√E − B·log₂ E − C ≤ log₂ p(E) for E ≥ 1 and log₂ p(E) ≤ κ·√E + C for
all E. -/
theorem exists_bounds : ∃ B C : ℝ, Partitions.Bounds B C := by
  obtain ⟨H, B, hH, hlow⟩ := exists_le_p
  refine ⟨B, max 0 (-Real.logb 2 H), fun E hE => ?_, fun E => ?_⟩
  · have hE0 : (0 : ℝ) < E := by exact_mod_cast hE
    have hpos : 0 < H * Real.exp (cHR * Real.sqrt E) / (E : ℝ) ^ B := by positivity
    have h1 := Real.logb_le_logb_of_le one_lt_two hpos (hlow E hE)
    rw [Real.logb_div (by positivity) (by positivity), Real.logb_mul hH.ne' (Real.exp_pos _).ne', logb_exp, Real.logb_pow] at h1
    have h2 : -Real.logb 2 H ≤ max 0 (-Real.logb 2 H) := le_max_right _ _
    rw [kappa_mul]
    linarith
  · have hp : (0 : ℝ) < p E := by exact_mod_cast p_pos E
    have h1 := Real.logb_le_logb_of_le one_lt_two hp (p_le_exp E)
    rw [logb_exp] at h1
    have h2 : (0 : ℝ) ≤ max 0 (-Real.logb 2 H) := le_max_left _ _
    rw [kappa_mul]
    linarith

end ClauseBound.Part
