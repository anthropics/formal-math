/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log

/-!
# Ceilings of quotients and logarithms, floors and ceilings of roots

General facts about natural and real numbers. The quotient of two natural numbers, rounded up, is
Mathlib's `a ⌈/⌉ b`. It is computed by `Nat.ceilDiv_eq_add_pred_div : a ⌈/⌉ b = (a + b - 1) / b`.
It is the ceiling of the real quotient (`Nat.ceil_div_eq_ceilDiv`) and the least `k` with
`a ≤ k * b` (`Nat.ceilDiv_le_iff`, `Nat.lt_ceilDiv_iff`), so `a ≤ a ⌈/⌉ b * b < a + b`
(`Nat.le_ceilDiv_mul`, `Nat.ceilDiv_mul_lt`). The power of `b` with exponent `⌈log_b n⌉` is at most
`b * n` (`Nat.pow_clog_le_mul`). A natural number is compared with an `e`-th root by its `e`-th
power (`Real.natCast_le_rpow_inv_iff`, `Real.rpow_inv_le_natCast_iff`). `cbrtCeil n` is the cube
root of `n`, rounded up.
-/

public section

namespace Nat

/-! ## The ceiling of a quotient of natural numbers -/

/-- `a ⌈/⌉ b ≤ k` says that `k` pieces of size `b` cover `a`. Mathlib's `ceilDiv_le_iff_le_mul` has
`b * k` on the right. -/
theorem ceilDiv_le_iff {a b k : ℕ} (hb : 0 < b) : a ⌈/⌉ b ≤ k ↔ a ≤ k * b := by
  rw [ceilDiv_le_iff_le_mul hb, Nat.mul_comm]

/-- `i < a ⌈/⌉ b` says that `i` pieces of size `b` do not cover `a`. -/
theorem lt_ceilDiv_iff {a b i : ℕ} (hb : 0 < b) : i < a ⌈/⌉ b ↔ i * b < a := by
  rw [← Nat.not_le, ceilDiv_le_iff hb, Nat.not_le]

/-- `a ⌈/⌉ b` pieces of size `b` cover `a`. -/
theorem le_ceilDiv_mul {a b : ℕ} (hb : 0 < b) : a ≤ a ⌈/⌉ b * b :=
  (ceilDiv_le_iff hb).1 le_rfl

/-- `a ⌈/⌉ b` pieces of size `b` overshoot `a` by less than one piece. -/
theorem ceilDiv_mul_lt {a b : ℕ} (hb : 0 < b) : a ⌈/⌉ b * b < a + b := by
  have := Nat.div_mul_le_self (a + b - 1) b
  rw [Nat.ceilDiv_eq_add_pred_div]
  omega

/-- More to cover needs at least as many pieces. -/
theorem ceilDiv_le_ceilDiv_right {a a' : ℕ} (h : a ≤ a') (b : ℕ) : a ⌈/⌉ b ≤ a' ⌈/⌉ b :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h b) 1)

/-- The ceiling of the real quotient of two natural numbers, in natural numbers. -/
theorem ceil_div_eq_ceilDiv (a : ℕ) {b : ℕ} (hb : 0 < b) : ⌈(a : ℝ) / (b : ℝ)⌉₊ = a ⌈/⌉ b := by
  refine eq_of_forall_ge_iff fun k => ?_
  rw [Nat.ceil_le, div_le_iff₀ (Nat.cast_pos.2 hb), ceilDiv_le_iff hb]
  exact_mod_cast Iff.rfl

/-! ## The ceiling of a logarithm

`Real.natCeil_logb_natCast : ⌈Real.logb b n⌉₊ = Nat.clog b n` passes from real to natural numbers,
and `Nat.le_pow_clog : 1 < b → x ≤ b ^ Nat.clog b x` is the lower bound. -/

/-- Rounding `n ≥ 1` up to a power of `b` costs at most a factor `b`. -/
theorem pow_clog_le_mul {b n : ℕ} (hb : 1 < b) (hn : 1 ≤ n) : b ^ Nat.clog b n ≤ b * n := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn
  · simp [Nat.clog_one_right, hb.le]
  · have hpos : 0 < Nat.clog b n := Nat.clog_pos hb hn
    have hlt := Nat.pow_pred_clog_lt_self hb hn
    calc b ^ Nat.clog b n = b * b ^ (Nat.clog b n).pred := by
          rw [← Nat.pow_succ', Nat.succ_pred_eq_of_pos hpos]
      _ ≤ b * n := Nat.mul_le_mul_left b hlt.le

end Nat

namespace Real

/-! ## Roots

The `e`-th root of `t` is written `(t : ℝ) ^ ((e : ℝ)⁻¹)`. With these two lemmas,
`Nat.le_floor_iff` and `Nat.ceil_le`, its floor and its ceiling are described by powers of natural
numbers. -/

/-- `x` is at most the `e`-th root of `t` exactly if `x ^ e ≤ t`. -/
theorem natCast_le_rpow_inv_iff {e : ℕ} (he : e ≠ 0) (x t : ℕ) :
    (x : ℝ) ≤ (t : ℝ) ^ ((e : ℝ)⁻¹) ↔ x ^ e ≤ t := by
  rw [Real.le_rpow_inv_iff_of_pos x.cast_nonneg t.cast_nonneg
    (Nat.cast_pos.2 (Nat.pos_of_ne_zero he)), Real.rpow_natCast]
  exact_mod_cast Iff.rfl

/-- The `e`-th root of `t` is at most `x` exactly if `t ≤ x ^ e`. -/
theorem rpow_inv_le_natCast_iff {e : ℕ} (he : e ≠ 0) (x t : ℕ) :
    (t : ℝ) ^ ((e : ℝ)⁻¹) ≤ (x : ℝ) ↔ t ≤ x ^ e := by
  rw [Real.rpow_inv_le_iff_of_pos t.cast_nonneg x.cast_nonneg
    (Nat.cast_pos.2 (Nat.pos_of_ne_zero he)), Real.rpow_natCast]
  exact_mod_cast Iff.rfl

end Real

namespace ThreeSumApsp

/-- The cube root of `n`, rounded up: `⌈n^{1/3}⌉`. -/
@[expose] noncomputable def cbrtCeil (n : ℕ) : ℕ := ⌈(n : ℝ) ^ (1 / 3 : ℝ)⌉₊

end ThreeSumApsp
