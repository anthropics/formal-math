/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Asymptotics.Logarithms
public import ThreeSumApsp.Util.Asymptotics.PowPolylog

/-!
# `logU`, the paper's `log U`

`logU u` is `log u`, read as `log 2` for `u < 2`.

* It is positive and nondecreasing, and `log (cu) ≤ log c + log u` for `c ≥ 1`.
* `log (cU) = O(log U)` (`dominated_logU_mul`) and `log (c n^κ) = O(log n)`
  (`dominated_logU_mul_rpow`).
* Along bounds `u(n) ≤ c n^κ` it is `Õ(1)` (`isPowPolylog_logU_of_le`).
-/

public section

namespace ThreeSumApsp

/-- `logU u ≥ log 2`. -/
theorem log_two_le_logU (u : ℝ) : Real.log 2 ≤ logU u :=
  Real.log_le_log two_pos (le_max_right _ _)

/-- `logU u > 0`. -/
theorem logU_pos (u : ℝ) : 0 < logU u :=
  (Real.log_pos one_lt_two).trans_le (log_two_le_logU u)

/-- `1 + logU u ≥ 1`. -/
theorem one_le_one_add_logU (u : ℝ) : 1 ≤ 1 + logU u :=
  le_add_of_nonneg_right (logU_pos u).le

/-- `log u ≤ logU u` for `u > 0`. -/
theorem log_le_logU {u : ℝ} (hu : 0 < u) : Real.log u ≤ logU u :=
  Real.log_le_log hu (le_max_left _ _)

/-- `logU` is nondecreasing. -/
theorem logU_mono {u v : ℝ} (h : u ≤ v) : logU u ≤ logU v :=
  Real.log_le_log (lt_max_of_lt_right two_pos) (max_le_max_right _ h)

/-- `logU (c u) ≤ log c + logU u` for `c ≥ 1`. -/
theorem logU_mul_le {c : ℝ} (hc : 1 ≤ c) (u : ℝ) : logU (c * u) ≤ Real.log c + logU u := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hmax : (0 : ℝ) < max u 2 := lt_max_of_lt_right two_pos
  rw [logU, logU, ← Real.log_mul hc0.ne' hmax.ne']
  exact Real.log_le_log (lt_max_of_lt_right two_pos) (max_le
    (mul_le_mul_of_nonneg_left (le_max_left _ _) hc0.le)
    ((le_max_right u 2).trans (le_mul_of_one_le_left hmax.le hc)))

/-- `logU u ≤ logU (c u)` for `c ≥ 1`, also for negative `u`. -/
theorem logU_le_logU_mul {c : ℝ} (hc : 1 ≤ c) (u : ℝ) : logU u ≤ logU (c * u) := by
  rcases le_or_gt 0 u with hu | hu
  · exact logU_mono (le_mul_of_one_le_left hu hc)
  · have hcu : c * u < 0 := mul_neg_of_pos_of_neg (zero_lt_one.trans_le hc) hu
    rw [logU, logU, max_eq_right (by linarith), max_eq_right (by linarith)]

/-- `logU (n^κ) ≤ log 2 + κ log n` for `n ≥ 1` and `κ ≥ 0`. -/
theorem logU_rpow_le {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 ≤ κ) :
    logU ((n : ℝ) ^ κ) ≤ Real.log 2 + κ * Real.log n := by
  have hpow : 1 ≤ (n : ℝ) ^ κ := Real.one_le_rpow (Nat.one_le_cast.2 hn) hκ
  rw [← Real.log_rpow (Nat.cast_pos.2 hn), ← Real.log_mul two_ne_zero (by positivity)]
  exact Real.log_le_log (lt_max_of_lt_right two_pos) (max_le (by linarith) (by linarith))

/-! ## `logU` of a multiple -/

/-- `log (cU) = O(log U)` for a constant `c ≥ 1`. -/
theorem dominated_logU_mul {c : ℝ} (hc : 1 ≤ c) :
    Dominated (fun _ : ℝ => True) (fun U => logU (c * U)) logU := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  refine .of_le_const_mul (C := 1 + Real.log c / Real.log 2) (by positivity) fun U _ => ?_
  have hscale : Real.log c ≤ Real.log c / Real.log 2 * logU U := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left (log_two_le_logU U) hlogc
  linarith [logU_mul_le hc U, hscale]

/-- `log (c n^κ) = O(log n)` on `n ≥ 2`. -/
theorem dominated_logU_mul_rpow {c κ : ℝ} (hc : 1 ≤ c) (hκ : 0 ≤ κ) :
    Dominated (fun n : ℕ => 2 ≤ n) (fun n => logU (c * (n : ℝ) ^ κ)) fun n => Real.log n := by
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hlog : Dominated (fun n : ℕ => 2 ≤ n) (fun n => Real.log n + 1) fun n => Real.log n :=
    dominated_log_add_one_log.comp (fun n : ℕ => (n : ℝ)) fun _ h => by exact_mod_cast h
  refine (hlog.const_mul (c := Real.log c + 1 + κ) (by positivity)).mono_left fun n hn => ?_
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  -- `log (c n^κ) ≤ log c + log 2 + κ log n ≤ (log c + 1 + κ) (log n + 1)`
  nlinarith [logU_mul_le hc ((n : ℝ) ^ κ), logU_rpow_le (one_le_two.trans hn) hκ,
    Real.log_two_lt_one, mul_nonneg hlogc hlogn]

/-! ## `logU` along bounds that are polynomial in `n` -/

/-- `log u(n) = Õ(1)` for bounds `1 ≤ u(n) ≤ c n^κ` on the numbers. -/
theorem isPowPolylog_logU_of_le {mag : ℕ → ℝ} {c κ : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → 1 ≤ mag n ∧ mag n ≤ c * (n : ℝ) ^ κ) :
    IsPowPolylog (fun n => logU (mag n)) 0 := by
  refine (isPowPolylog_log_mul_rpow (2 * c) κ).mono_left_of_nonneg
    (.of_forall fun n => (logU_pos _).le) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  obtain ⟨hone, hle⟩ := h n hn
  refine Real.log_le_log (lt_max_of_lt_right two_pos) (max_le ?_ ?_) <;> rw [mul_assoc] <;> linarith

/-- `log (c n^κ) = Õ(1)`. -/
theorem isPowPolylog_logU_mul_rpow {c κ : ℝ} (hc : 1 ≤ c) (hκ : 0 ≤ κ) :
    IsPowPolylog (fun n : ℕ => logU (c * (n : ℝ) ^ κ)) 0 :=
  isPowPolylog_logU_of_le fun _ hn =>
    ⟨one_le_mul_of_one_le_of_one_le hc (Real.one_le_rpow (Nat.one_le_cast.2 hn) hκ), le_rfl⟩

end ThreeSumApsp
