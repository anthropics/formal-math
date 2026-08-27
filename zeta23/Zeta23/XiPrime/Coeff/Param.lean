/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Coeff/Param.lean — the complex parameter Λ⋆ = l/2 + it, |t| ≤ 1, versus l/2
([XF′ Remark 4.3] in the form the H3 assembly consumes).

For Λs : ℂ with Λs.re = l/2, |Λs.im| ≤ 1 and 2 ≤ l:
  l/2 ≤ ‖Λs‖,   l²/4 ≤ ‖Λs‖² ≤ l²/4 + 1,
  |Re(Λs⁻¹) − 2/l| ≤ 8/l³,   |‖Λs‖⁻² − 4/l²| ≤ 16/l⁴,   |‖Λs‖^{−2k} − (4/l²)^k| ≤ k·(4/l²)^{k+1}.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace Zeta23
namespace XiPrime

set_option linter.unusedSectionVars false

/-! Every lemma takes the same three hypotheses (hl) (hre) (him), used or not, so the consumer's call
shape is uniform. -/
section Param
variable {Λs : ℂ} {l : ℝ} (hl : 2 ≤ l) (hre : Λs.re = l / 2) (him : |Λs.im| ≤ 1)
include hl hre him

lemma norm_param_ge : l / 2 ≤ ‖Λs‖ := by
  have h := Complex.abs_re_le_norm Λs
  rw [hre, abs_of_nonneg (by linarith)] at h
  exact h

lemma normSq_param_eq : ‖Λs‖ ^ 2 = l ^ 2 / 4 + Λs.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, hre]; ring

lemma normSq_param_ge : l ^ 2 / 4 ≤ ‖Λs‖ ^ 2 := by
  rw [normSq_param_eq hl hre him]; nlinarith [sq_nonneg Λs.im]

lemma normSq_param_le : ‖Λs‖ ^ 2 ≤ l ^ 2 / 4 + 1 := by
  rw [normSq_param_eq hl hre him]
  have : Λs.im ^ 2 ≤ 1 := by
    have h := abs_le.mp him
    nlinarith
  linarith

lemma norm_param_pos : 0 < ‖Λs‖ := lt_of_lt_of_le (by linarith) (norm_param_ge hl hre him)

/-- |Re(Λs⁻¹) − 2/l| ≤ 8/l³  (indeed 0 ≤ 2/l − Re(Λs⁻¹) = 2t²/(l(l²/4+t²)) ≤ 8t²/l³). -/
lemma inv_re_param : |(Λs⁻¹).re - 2 / l| ≤ 8 / l ^ 3 := by
  have hl0 : 0 < l := by linarith
  have hns : Complex.normSq Λs = l ^ 2 / 4 + Λs.im ^ 2 := by
    rw [Complex.normSq_apply, hre]; ring
  have hA : 0 < l ^ 2 / 4 + Λs.im ^ 2 := by positivity
  rw [Complex.inv_re, hns, hre]
  have ht2 : Λs.im ^ 2 ≤ 1 := by have h := abs_le.mp him; nlinarith
  have ht0 : 0 ≤ Λs.im ^ 2 := sq_nonneg _
  -- the difference is 2t²/(l·A) with A = l²/4 + t²
  have hdiff : l / 2 / (l ^ 2 / 4 + Λs.im ^ 2) - 2 / l
      = -(2 * Λs.im ^ 2 / (l * (l ^ 2 / 4 + Λs.im ^ 2))) := by
    field_simp; ring
  rw [hdiff, abs_neg, abs_of_nonneg (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- 2 t² l³ ≤ 8 · l · A  ⟸  t² l² ≤ 4A = l² + 4t² and t² ≤ 1
  nlinarith [mul_nonneg (sub_nonneg.mpr ht2) (pow_nonneg hl0.le 3), mul_nonneg hl0.le ht0]

/-- |‖Λs‖⁻² − 4/l²| ≤ 16/l⁴  (indeed 0 ≤ 4/l² − ‖Λs‖⁻² = 4t²/(l²A) ≤ 16t²/l⁴). -/
lemma inv_normSq_param : |(‖Λs‖ ^ 2)⁻¹ - 4 / l ^ 2| ≤ 16 / l ^ 4 := by
  have hl0 : 0 < l := by linarith
  rw [normSq_param_eq hl hre him]
  have hA : 0 < l ^ 2 / 4 + Λs.im ^ 2 := by positivity
  have ht2 : Λs.im ^ 2 ≤ 1 := by have h := abs_le.mp him; nlinarith
  have ht0 : 0 ≤ Λs.im ^ 2 := sq_nonneg _
  have hdiff : (l ^ 2 / 4 + Λs.im ^ 2)⁻¹ - 4 / l ^ 2
      = -(4 * Λs.im ^ 2 / (l ^ 2 * (l ^ 2 / 4 + Λs.im ^ 2))) := by
    field_simp; ring
  rw [hdiff, abs_neg, abs_of_nonneg (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg ht0 (pow_nonneg hl0.le 4), pow_pos hl0 2, mul_nonneg ht0 (sq_nonneg (l^2))]

/-- 0 ≤ 4/l² − ‖Λs‖⁻²  (the sign: ‖Λs‖² ≥ l²/4). -/
lemma inv_normSq_param_le : (‖Λs‖ ^ 2)⁻¹ ≤ 4 / l ^ 2 := by
  have hl0 : 0 < l := by linarith
  have hb : 0 < l ^ 2 / 4 := by positivity
  calc (‖Λs‖ ^ 2)⁻¹ ≤ (l ^ 2 / 4)⁻¹ := by
        exact inv_anti₀ hb (normSq_param_ge hl hre him)
    _ = 4 / l ^ 2 := by rw [inv_div]

omit hl hre him in
/-- elementary: for 0 ≤ x ≤ y,  y·(y^k − x^k) ≤ k·(y − x)·y^k. -/
lemma mul_pow_sub_pow_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ∀ k : ℕ, y * (y ^ k - x ^ k) ≤ k * (y - x) * y ^ k
  | 0 => by simp
  | k + 1 => by
      have hy : 0 ≤ y := hx.trans hxy
      have ih := mul_pow_sub_pow_le hx hxy k
      have hxk : x ^ k ≤ y ^ k := pow_le_pow_left₀ hx hxy k
      have hyk : 0 ≤ y ^ k := pow_nonneg hy k
      have e1 : y * (y ^ (k + 1) - x ^ (k + 1)) = y * (y * (y ^ k - x ^ k)) + y * ((y - x) * x ^ k) := by
        ring
      have e2 : ((k + 1 : ℕ) : ℝ) * (y - x) * y ^ (k + 1) = y * (k * (y - x) * y ^ k) + (y - x) * y ^ k * y := by
        push_cast; ring
      rw [e1, e2]
      have h1 : y * (y * (y ^ k - x ^ k)) ≤ y * (k * (y - x) * y ^ k) := mul_le_mul_of_nonneg_left ih hy
      have h2 : y * ((y - x) * x ^ k) ≤ (y - x) * y ^ k * y := by
        have : (y - x) * x ^ k ≤ (y - x) * y ^ k := mul_le_mul_of_nonneg_left hxk (by linarith)
        nlinarith
      linarith

/-- |‖Λs‖^{−2k} − (4/l²)^k| ≤ k·(4/l²)^{k+1}. -/
lemma inv_normSq_pow_param (k : ℕ) :
    |((‖Λs‖ ^ 2)⁻¹) ^ k - (4 / l ^ 2) ^ k| ≤ k * (4 / l ^ 2) ^ (k + 1) := by
  have hl0 : 0 < l := by linarith
  set x := (‖Λs‖ ^ 2)⁻¹ with hx
  set y := 4 / l ^ 2 with hy
  have hx0 : 0 ≤ x := by positivity
  have hxy : x ≤ y := inv_normSq_param_le hl hre him
  have hy0 : 0 < y := by positivity
  have hyx : y - x ≤ y ^ 2 := by
    have h := inv_normSq_param hl hre him
    rw [abs_sub_comm] at h
    have h' := (abs_le.mp h).2
    have : (16 : ℝ) / l ^ 4 = y ^ 2 := by rw [hy]; field_simp; ring
    linarith [this]
  have hk := mul_pow_sub_pow_le hx0 hxy k
  rw [abs_sub_comm, abs_of_nonneg (by linarith [pow_le_pow_left₀ hx0 hxy k])]
  -- y^k − x^k ≤ k (y−x) y^k / y ≤ k y^{k+1}
  have hyk : 0 ≤ y ^ k := pow_nonneg hy0.le k
  have h1 : y * (y ^ k - x ^ k) ≤ y * (k * y ^ (k + 1)) := by
    calc y * (y ^ k - x ^ k) ≤ k * (y - x) * y ^ k := hk
      _ ≤ k * y ^ 2 * y ^ k := by
          have := mul_le_mul_of_nonneg_left hyx (by positivity : (0:ℝ) ≤ k * y ^ k)
          nlinarith
      _ = y * (k * y ^ (k + 1)) := by ring
  exact le_of_mul_le_mul_left h1 hy0

end Param

end XiPrime
end Zeta23
