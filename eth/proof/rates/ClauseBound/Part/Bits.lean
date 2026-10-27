/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.Tactic
public import PartitionStatement
public import ClauseBound.Part.Rec

/-! # The least h with p(h) ≥ 2^λ, and the label counts of the pieces made from partitions

For a length λ let h be the least integer ≥ 2 with p(h) ≥ 2^λ, where p counts partitions. In the
proof of Theorem B (Appendix B) the piece number s, |s| ≤ 2h, factors row-wise through R^row_s =
Σ_{i ≤ 2h} p(s + i) labels and
column-wise through R^col_s = Σ_{i ≤ 2h} p(2h − s − i) labels. The file defines h, R^row_s and
R^col_s and proves elementary facts about them and about partition numbers and logarithms:
p(E) ≥ (E + 1)/2, p(1) = 1, h ≥ 2, p(h) ≥ 2^λ, p(h − 1) < 2^λ, R^row_s ≥ 1 and R^col_s ≥ 1 for |s| ≤
2h, κ > 0, and bounds on log₂ and ⌈log₂⌉. -/

public section

namespace ClauseBound.Part.Bits

open Finset Partitions

/-- E(E + 1) ≤ 2·(1 + 2 + … + E). -/
theorem gauss (E : ℕ) : E * (E + 1) ≤ 2 * ∑ v ∈ Icc 1 E, v := by
  induction E with
  | zero => simp
  | succ E ih =>
    rw [sum_Icc_succ_top (by omega)]
    nlinarith

/-- p(E) ≥ (E + 1)/2, from the terms k = 1 of the recurrence. -/
theorem succ_le_two_mul_p (E : ℕ) : E + 1 ≤ 2 * p E := by
  rcases Nat.eq_zero_or_pos E with rfl | hE
  · rw [p_zero]
    norm_num
  have h1 : ∑ v ∈ Icc 1 E, v ≤ E * p E := by
    rw [mul_p_eq]
    refine sum_le_sum fun v hv => ?_
    have hv' := mem_Icc.1 hv
    have h1 : 1 ∈ Icc 1 (E / v) := mem_Icc.2 ⟨le_rfl, (Nat.le_div_iff_mul_le hv'.1).2 (by omega)⟩
    calc v ≤ v * p (E - 1 * v) := Nat.le_mul_of_pos_right _ (p_pos _)
      _ ≤ _ := single_le_sum (f := fun k => v * p (E - k * v)) (fun _ _ => Nat.zero_le _) h1
  have h2 := gauss E
  have h3 : E * (E + 1) ≤ E * (2 * p E) := by nlinarith
  exact Nat.le_of_mul_le_mul_left h3 hE

/-- p(1) = 1. -/
theorem p_one : p 1 = 1 := by
  have := mul_p_eq 1
  simpa [p_zero] using this

end ClauseBound.Part.Bits

namespace ClauseBound.Part

open Finset Partitions

/-- p(E) for an integer E; 0 for E < 0. -/
@[expose] def pz (E : ℤ) : ℕ := if 0 ≤ E then p E.toNat else 0

/-- Some h ≥ 2 has p(h) ≥ 2^λ. -/
theorem exists_h (lam : ℕ) : ∃ h : ℕ, 2 ≤ h ∧ 2 ^ lam ≤ p h := by
  refine ⟨2 ^ (lam + 1), ?_, ?_⟩
  · have := Nat.one_le_two_pow (n := lam)
    rw [pow_succ]
    omega
  · have h1 := Bits.succ_le_two_mul_p (2 ^ (lam + 1))
    have h2 : 2 ^ (lam + 1) = 2 * 2 ^ lam := pow_succ' 2 lam
    omega

open Classical in
/-- The least h ≥ 2 with p(h) ≥ 2^λ. -/
@[expose] noncomputable def hOf (lam : ℕ) : ℕ := Nat.find (exists_h lam)

/-- Σ_{i=0}^{2h} p(s + i). -/
@[expose] def Rrow (h : ℕ) (s : ℤ) : ℕ := ∑ i ∈ range (2 * h + 1), pz (s + i)

/-- Σ_{i=0}^{2h} p(2h − s − i). -/
@[expose] def Rcol (h : ℕ) (s : ℤ) : ℕ := ∑ i ∈ range (2 * h + 1), pz (2 * h - s - i)

/-- h ≥ 2. -/
theorem two_le_hOf (lam : ℕ) : 2 ≤ hOf lam := by
  unfold hOf
  exact And.left (Nat.find_spec (exists_h lam))

/-- p(h) ≥ 2^λ. -/
theorem two_pow_le_p_hOf (lam : ℕ) : 2 ^ lam ≤ p (hOf lam) := by
  unfold hOf
  exact And.right (Nat.find_spec (exists_h lam))

/-- R^row_s ≥ 1 for |s| ≤ 2h. -/
theorem one_le_Rrow {h : ℕ} {s : ℤ} (hs : |s| ≤ 2 * h) : 1 ≤ Rrow h s := by
  have h1 := abs_le.1 hs
  have h2 : 1 ≤ pz (s + ((2 * h : ℕ) : ℤ)) := by
    unfold pz
    rw [if_pos (by push_cast; omega)]
    exact p_pos _
  exact h2.trans (single_le_sum (f := fun i : ℕ => pz (s + i)) (fun _ _ => Nat.zero_le _) (mem_range.2 (Nat.lt_succ_self _)))

/-- R^col_s ≥ 1 for |s| ≤ 2h. -/
theorem one_le_Rcol {h : ℕ} {s : ℤ} (hs : |s| ≤ 2 * h) : 1 ≤ Rcol h s := by
  have h1 := abs_le.1 hs
  have h2 : 1 ≤ pz (2 * h - s - ((0 : ℕ) : ℤ)) := by
    unfold pz
    rw [if_pos (by push_cast; omega)]
    exact p_pos _
  exact h2.trans (single_le_sum (f := fun i : ℕ => pz (2 * h - s - i)) (fun _ _ => Nat.zero_le _) (mem_range.2 (Nat.succ_pos _)))

end ClauseBound.Part

namespace ClauseBound.Part.Bits

open Finset Partitions Real

/-- κ > 0. -/
theorem kappa_pos : 0 < kappa := by
  unfold kappa cHR
  have h1 := Real.pi_pos
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- p(h − 1) < 2^λ, because h is the least. -/
theorem p_pred_lt {lam : ℕ} (hl : 1 ≤ lam) : p (hOf lam - 1) < 2 ^ lam := by
  have h2 := two_le_hOf lam
  by_contra hn
  rcases Nat.lt_or_ge 2 (hOf lam) with h3 | h3
  · have h4 : hOf lam - 1 < hOf lam := by omega
    unfold hOf at h4 hn h3
    exact Nat.find_min _ h4 ⟨by omega, not_lt.1 hn⟩
  · rw [show hOf lam - 1 = 1 by omega, p_one] at hn
    exact hn (Nat.one_lt_two_pow (by omega))

/-- log₂ E ≤ 4·E^(1/4)/ln 2. -/
theorem logb_le_sqrt_sqrt {E : ℕ} (hE : 1 ≤ E) : logb 2 E ≤ 4 * √√(E : ℝ) / Real.log 2 := by
  have hE0 : (0 : ℝ) < E := by exact_mod_cast hE
  have hy : 0 < √√(E : ℝ) := Real.sqrt_pos.2 (Real.sqrt_pos.2 hE0)
  have h1 : (√√(E : ℝ)) ^ 4 = E := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hE0.le]
  have h2 : Real.log E = 4 * Real.log (√√(E : ℝ)) := by
    conv_lhs => rw [← h1]
    rw [Real.log_pow]
    norm_num
  have h3 := Real.log_le_sub_one_of_pos hy
  rw [Real.logb, h2]
  exact div_le_div_of_nonneg_right (by linarith) (Real.log_pos (by norm_num)).le

end ClauseBound.Part.Bits

namespace ClauseBound.Part

open Finset Partitions

end ClauseBound.Part

namespace ClauseBound.Part.Bits

open Finset Partitions Real

/-- If log₂ r ≤ y ≤ c then r ≤ 2^c. -/
theorem le_two_pow_of_logb_le {r c : ℕ} (hr : 1 ≤ r) {y : ℝ} (h1 : logb 2 r ≤ y) (h2 : y ≤ c) : r ≤ 2 ^ c := by
  have h3 : (r : ℝ) ≤ (2 : ℝ) ^ (c : ℝ) :=
    (Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hr)).1 (h1.trans h2)
  rw [Real.rpow_natCast] at h3
  exact_mod_cast h3

/-- If log₂ r ≤ y then ⌈log₂ r⌉ ≤ y + 1. -/
theorem clog_le {r : ℕ} (hr : 1 ≤ r) {y : ℝ} (hy : logb 2 r ≤ y) : (Nat.clog 2 r : ℝ) ≤ y + 1 := by
  have h0 : 0 ≤ y := (Real.logb_nonneg (by norm_num) (by exact_mod_cast hr)).trans hy
  have h1 : r ≤ 2 ^ ⌈y⌉₊ := le_two_pow_of_logb_le hr hy (Nat.le_ceil y)
  have h2 : (Nat.clog 2 r : ℝ) ≤ ⌈y⌉₊ := by exact_mod_cast Nat.clog_le_of_le_pow h1
  exact h2.trans (Nat.ceil_lt_add_one h0).le

/-- log₂(k·h + 1) ≤ 3 + log₂ h for k ≤ 4 and h ≥ 1. -/
theorem logb_succ_le {k h : ℕ} (hk : k ≤ 4) (hh : 1 ≤ h) : logb 2 ((k * h + 1 : ℕ) : ℝ) ≤ 3 + logb 2 h := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have h1 : ((k * h + 1 : ℕ) : ℝ) ≤ 2 ^ 3 * h := by
    have : k * h + 1 ≤ 2 ^ 3 * h := by nlinarith
    exact_mod_cast this
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h1
  rw [Real.logb_mul (by positivity) hh0.ne', Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h2
  simp only [Nat.cast_ofNat, mul_one] at h2
  exact h2

end ClauseBound.Part.Bits

namespace ClauseBound.Part

open Finset Partitions

end ClauseBound.Part
