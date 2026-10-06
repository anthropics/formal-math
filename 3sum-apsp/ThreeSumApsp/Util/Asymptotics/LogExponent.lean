/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Powers of the logarithm as powers of n with an exponent that tends to 0

`(log n)^e = n^{e log log n / log n}` for `n ≥ 3`, and `log log n / log n` tends to 0.  So
`n^a (log n)^e ≤ n^{a + η(n)}` for all `n ≥ 1` (`rpow_mul_log_pow_le`), with one function
`η = logExponent e` that tends to 0 (`tendsto_logExponent`).
-/

@[expose] public section

namespace ThreeSumApsp

open Filter

/-- The exponent `e log log n / log n`, and 0 for `n < 3`. -/
noncomputable def logExponent (e n : ℕ) : ℝ :=
  if 3 ≤ n then (e : ℝ) * (Real.log (Real.log n) / Real.log n) else 0

/-- The exponent tends to 0. -/
theorem tendsto_logExponent (e : ℕ) : Tendsto (logExponent e) atTop (nhds 0) := by
  have hdiv : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => (e : ℝ) * (Real.log (Real.log n) / Real.log n)) atTop
      (nhds 0) := by
    have := (hdiv.comp hlog).const_mul (e : ℝ)
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  simp [logExponent, hn]

/-- `n^a (log n)^e ≤ n^{a + η(n)}` for all `n ≥ 1`, where `η(n) = logExponent e n` is the exponent
above, which tends to 0. -/
theorem rpow_mul_log_pow_le (a : ℝ) (e : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ a * Real.log n ^ e ≤ (n : ℝ) ^ (a + logExponent e n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases h3 : 3 ≤ n
  · have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast h3
    have hlog : 1 < Real.log n := by
      rw [Real.lt_log_iff_exp_lt hn0]
      have := Real.exp_one_lt_d9
      linarith
    have hlog0 : 0 < Real.log n := by linarith
    rw [Real.rpow_add hn0]
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (Real.rpow_nonneg hn0.le _)
    simp only [logExponent, h3, if_true]
    rw [Real.rpow_def_of_pos hn0, ← Real.rpow_natCast, Real.rpow_def_of_pos hlog0]
    congr 1
    field_simp
  · have hle : Real.log n ≤ 1 := by
      have hn2 : (n : ℝ) ≤ 2 := by exact_mod_cast (by omega : n ≤ 2)
      have hlog2 : Real.log n ≤ Real.log 2 := Real.log_le_log hn0 hn2
      have := Real.log_two_lt_d9
      linarith
    have hge : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    simp only [logExponent, h3, if_false, add_zero]
    calc (n : ℝ) ^ a * Real.log n ^ e ≤ (n : ℝ) ^ a * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hge hle) (Real.rpow_nonneg hn0.le _)
      _ = (n : ℝ) ^ a := mul_one _

end ThreeSumApsp
