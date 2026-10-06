/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec3.Corollary15_16
public import ThreeSumApsp.TimeClaims.Sec3.Definitions

/-!
# The arithmetic behind the running-time claims of Section 3

Elementary inequalities that the deductions between running-time claims use silently.

* `⌈n^{1/3}⌉ ≥ 1` and `(log s + 1)^e ≥ 1`.
* Thin instances, `n ≥ D^18` (Theorem 5, Corollaries 15, 16 and 26): the overheads `n D`, `n² / √D`
  and `1` are at most `n² / D^a`, and so at most the bounds `n² log² D / D^{1/18}` and
  `n² / D^{0.063}`.
* The pieces into which Corollary 15 splits `W` have at most `n² / √D` query pairs (`splitCap_le`).
-/

public section

namespace ThreeSumApsp

/-! ## Two quantities that are at least 1 -/

/-- `⌈n^{1/3}⌉ ≥ 1` for `n ≥ 1`. -/
theorem one_le_cbrtCeil {n : ℕ} (hn : 1 ≤ n) : 1 ≤ cbrtCeil n :=
  Nat.ceil_pos.2 (Real.rpow_pos_of_pos (Nat.cast_pos.2 hn) _)

/-- `(log s + 1)^e ≥ 1`. -/
theorem one_le_log_add_one_pow (s e : ℕ) : 1 ≤ (Real.log s + 1) ^ e :=
  one_le_pow₀ (le_add_of_nonneg_left (Real.log_natCast_nonneg s))

/-! ## Thin instances: `n ≥ D^18` -/

/-- `D^{1+a} ≤ n` for `a ≤ 17`. -/
theorem mul_rpow_le_of_pow_le {n D : ℕ} {a : ℝ} (hD : 1 ≤ D) (hDn : D ^ 18 ≤ n) (ha : a ≤ 17) :
    (D : ℝ) * (D : ℝ) ^ a ≤ n := by
  have hD1 : (1 : ℝ) ≤ D := Nat.one_le_cast.2 hD
  calc (D : ℝ) * (D : ℝ) ^ a = (D : ℝ) ^ (1 + a) := by
        rw [Real.rpow_add (zero_lt_one.trans_le hD1), Real.rpow_one]
    _ ≤ (D : ℝ) ^ ((18 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1 (by push_cast; linarith)
    _ = ((D ^ 18 : ℕ) : ℝ) := by rw [Real.rpow_natCast, Nat.cast_pow]
    _ ≤ n := Nat.cast_le.2 hDn

/-- Writing the matrices: `n D ≤ n² / D^a`. -/
theorem mul_le_sq_div_rpow {n D : ℕ} {a : ℝ} (hD : 1 ≤ D) (hDn : D ^ 18 ≤ n) (ha : a ≤ 17) :
    (n : ℝ) * (D : ℝ) ≤ (n : ℝ) ^ 2 / (D : ℝ) ^ a := by
  rw [le_div_iff₀ (Real.rpow_pos_of_pos (Nat.cast_pos.2 hD) a), mul_assoc, sq]
  exact mul_le_mul_of_nonneg_left (mul_rpow_le_of_pow_le hD hDn ha) n.cast_nonneg

/-- `1 ≤ n² / D^a`. -/
theorem one_le_sq_div_rpow {n D : ℕ} {a : ℝ} (hD : 1 ≤ D) (hDn : D ^ 18 ≤ n) (ha : a ≤ 17) :
    1 ≤ (n : ℝ) ^ 2 / (D : ℝ) ^ a :=
  (one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.2 ((Nat.one_le_pow _ _ hD).trans hDn))
    (Nat.one_le_cast.2 hD)).trans (mul_le_sq_div_rpow hD hDn ha)

/-- `n² / √D ≤ n² / D^a` for `a ≤ 1/2`. -/
theorem sq_div_sqrt_le_sq_div_rpow (n : ℕ) {D : ℕ} {a : ℝ} (hD : 1 ≤ D) (ha : a ≤ 1 / 2) :
    (n : ℝ) ^ 2 / Real.sqrt D ≤ (n : ℝ) ^ 2 / (D : ℝ) ^ a := by
  rw [Real.sqrt_eq_rpow]
  exact div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos (Nat.cast_pos.2 hD) a)
    (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hD) ha)

/-- `1 ≤ n² / √D`. -/
theorem one_le_sq_div_sqrt {n D : ℕ} (hD : 1 ≤ D) (hDn : D ^ 18 ≤ n) :
    1 ≤ (n : ℝ) ^ 2 / Real.sqrt D := by
  rw [Real.sqrt_eq_rpow]
  exact one_le_sq_div_rpow hD hDn (by norm_num)

/-- The factor `log² D` of Theorem 5 is at least 1: `n² / D^a ≤ n² log² D / D^a` for `D ≥ 3`. -/
theorem sq_div_rpow_le_sq_mul_log_sq_div (n : ℕ) {D : ℕ} (a : ℝ) (hD : 3 ≤ D) :
    (n : ℝ) ^ 2 / (D : ℝ) ^ a ≤ (n : ℝ) ^ 2 * Real.log D ^ 2 / (D : ℝ) ^ a :=
  div_le_div_of_nonneg_right
    (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (Real.one_le_log_natCast_of_three_le hD)))
    (Real.rpow_nonneg D.cast_nonneg a)

/-- Writing the matrices costs at most the bound of Theorem 5: `n D ≤ n² log² D / D^{1/18}`. -/
theorem mul_le_thinBound {n D : ℕ} (hD : 4 ≤ D) (hDn : D ^ 18 ≤ n) :
    (n : ℝ) * (D : ℝ) ≤ thinBound n D :=
  (mul_le_sq_div_rpow (by omega) hDn (by norm_num)).trans
    (sq_div_rpow_le_sq_mul_log_sq_div n _ (by omega))

/-- `1 ≤ n² log² D / D^{1/18}`. -/
theorem one_le_thinBound {n D : ℕ} (hD : 4 ≤ D) (hDn : D ^ 18 ≤ n) : 1 ≤ thinBound n D :=
  (one_le_sq_div_rpow (by omega) hDn (by norm_num)).trans
    (sq_div_rpow_le_sq_mul_log_sq_div n _ (by omega))

/-- Reading `n² / √D` answers costs at most the bound of Theorem 5:
`n² / √D ≤ n² log² D / D^{1/18}`. -/
theorem sq_div_sqrt_le_thinBound (n : ℕ) {D : ℕ} (hD : 4 ≤ D) :
    (n : ℝ) ^ 2 / Real.sqrt D ≤ thinBound n D :=
  (sq_div_sqrt_le_sq_div_rpow n (by omega) (by norm_num)).trans
    (sq_div_rpow_le_sq_mul_log_sq_div n _ (by omega))

/-! ## The pieces of Corollary 15 -/

/-- A piece has at most `n² / √D` query pairs. -/
theorem splitCap_le {n D : ℕ} (hD : 1 ≤ D) (hDn : D ^ 18 ≤ n) :
    (splitCap n D : ℝ) ≤ (n : ℝ) ^ 2 / Real.sqrt D := by
  rw [splitCap, Nat.cast_max, Nat.cast_one]
  exact max_le (one_le_sq_div_sqrt hD hDn) (Nat.floor_le (by positivity))

/-- `D^{1/18} ≤ √D log² D` for `D ≥ 3`. -/
theorem rpow_le_sqrt_mul_log_sq {D : ℕ} (hD : 3 ≤ D) :
    (D : ℝ) ^ (1 / 18 : ℝ) ≤ Real.sqrt D * Real.log D ^ 2 := by
  rw [Real.sqrt_eq_rpow]
  exact (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 (by omega)) (by norm_num)).trans
    (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (Real.one_le_log_natCast_of_three_le hD)))

/-- The overhead `w + 1` is at most the bound of the general case of Corollary 15:
`w + 1 ≤ (n² + w √D) log² D / D^{1/18}`. -/
theorem add_one_le_splitBound {n D : ℕ} (w : ℕ) (hD : 4 ≤ D) (hDn : D ^ 18 ≤ n) :
    (w : ℝ) + 1 ≤ splitBound n D w := by
  have hpos : 0 < (D : ℝ) ^ (1 / 18 : ℝ) := Real.rpow_pos_of_pos (Nat.cast_pos.2 (by omega)) _
  have hw : (w : ℝ) ≤ (w : ℝ) * Real.sqrt D * Real.log D ^ 2 / (D : ℝ) ^ (1 / 18 : ℝ) := by
    rw [le_div_iff₀ hpos, mul_assoc]
    exact mul_le_mul_of_nonneg_left (rpow_le_sqrt_mul_log_sq (by omega)) w.cast_nonneg
  rw [splitBound, add_mul, add_div, add_comm]
  exact add_le_add (one_le_thinBound hD hDn) hw

/-- The second term of the bound of Corollaries 16 and 26 is at most the bound. -/
theorem sq_div_rpow_le_wantedBound (n D w : ℕ) :
    (n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ) ≤ wantedBound n D w :=
  le_add_of_nonneg_left (by positivity)

/-- `1 ≤ w D^{0.437} + n² / D^{0.063}`. -/
theorem one_le_wantedBound {n D : ℕ} (hD : 1 ≤ D) (hDn : D ^ 18 ≤ n) (w : ℕ) :
    1 ≤ wantedBound n D w :=
  (one_le_sq_div_rpow hD hDn (by norm_num)).trans (sq_div_rpow_le_wantedBound n D w)

end ThreeSumApsp
