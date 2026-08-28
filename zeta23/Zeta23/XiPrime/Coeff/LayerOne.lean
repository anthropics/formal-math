/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Coeff/LayerOne.lean — the ω = 1 (prime) layer of the diagonal law H3.

  sfPart Λs 1 y = Σ_{p ≤ e^y} ‖C(p;Λs)‖²/p = l²·(s²/2 − 4s³/3 + s⁴) + O(1+l),   s = y/l,
uniformly in 0 ≤ y ≤ l, for Re Λs = l/2, |Im Λs| ≤ 1, l ≥ 2.  Route: C(p;Λs) = −log p + Λs⁻¹(log p)²
(MainTerm's xiCoeff_prime), so ‖C(p)‖² = L² − 2·Re(Λs⁻¹)·L³ + ‖Λs‖⁻²·L⁴ (L = log p); the three prime sums
Σ(log p)^b/p = y^b/b + O((1+y)^{b−1}) (PrimeSums.prime_logpow_sum, b = 2,3,4); and the parameter
estimates Re(Λs⁻¹) = 2/l + O(l⁻³), ‖Λs‖⁻² = 4/l² + O(l⁻⁴) (Coeff/Param).
-/
import Zeta23.XiPrime.Coeff.DiagLaw

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Omega ArithmeticFunction.omega
open Finset Real

noncomputable section

namespace Zeta23
namespace XiPrime

/-- `‖−L + z·L²‖² = L² − 2·Re z·L³ + |z|²·L⁴` for real `L`. -/
lemma norm_sq_prime_term (L : ℝ) (z : ℂ) :
    ‖-(L : ℂ) + z * (L : ℂ) ^ 2‖ ^ 2 = L ^ 2 - 2 * z.re * L ^ 3 + (z.re ^ 2 + z.im ^ 2) * L ^ 4 := by
  have hL2 : ((L : ℂ)) ^ 2 = ((L ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hL2, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re, Complex.add_im,
    Complex.neg_im, Complex.ofReal_im, Complex.mul_im]
  ring

/-- `(Re Λ⁻¹)² + (Im Λ⁻¹)² = ‖Λ‖⁻²`. -/
lemma re_sq_add_im_sq_inv (Λs : ℂ) : (Λs⁻¹).re ^ 2 + (Λs⁻¹).im ^ 2 = (‖Λs‖ ^ 2)⁻¹ := by
  calc (Λs⁻¹).re ^ 2 + (Λs⁻¹).im ^ 2 = Complex.normSq (Λs⁻¹) := by
        rw [Complex.normSq_apply]; ring
    _ = ‖Λs⁻¹‖ ^ 2 := (Complex.sq_norm _).symm
    _ = (‖Λs‖ ^ 2)⁻¹ := by rw [norm_inv, inv_pow]

/-- the prime sums `S_b(y) := Σ_{p ≤ e^y, p prime} (log p)^b / p`. -/
def primeLogPowSum (b : ℕ) (y : ℝ) : ℝ :=
  ∑ p ∈ (Ioc 0 ⌊Real.exp y⌋₊).filter Nat.Prime, Real.log p ^ b / p

/-- the ω = 1 layer in terms of the three prime sums. -/
lemma sfPart_one_eq (Λs : ℂ) (y : ℝ) :
    sfPart Λs 1 y = primeLogPowSum 2 y - 2 * (Λs⁻¹).re * primeLogPowSum 3 y
      + (‖Λs‖ ^ 2)⁻¹ * primeLogPowSum 4 y := by
  unfold sfPart primeLogPowSum
  have hfilt : (Ioc 0 ⌊Real.exp y⌋₊).filter (fun N => Squarefree N ∧ ω N = 1)
      = (Ioc 0 ⌊Real.exp y⌋₊).filter Nat.Prime := by
    ext N
    simp only [Finset.mem_filter, squarefree_and_omega_one_iff]
  rw [hfilt, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpr : p.Prime := (Finset.mem_filter.1 hp).2
  rw [xiCoeff_prime hpr Λs, norm_sq_prime_term, re_sq_add_im_sq_inv]
  have hp0 : (0:ℝ) < p := by exact_mod_cast hpr.pos
  field_simp

set_option maxHeartbeats 800000 in
/-- **The ω = 1 layer of H3**: `sfPart Λs 1 y = l²(s²/2 − 4s³/3 + s⁴) + O(1+l)`, `s = y/l`, uniformly in
`0 ≤ y ≤ l`, for every `Λs` with `Re Λs = l/2`, `|Im Λs| ≤ 1`, `l ≥ 2`. -/
theorem sfPart_one_asymp :
    ∃ C : ℝ, ∀ (l : ℝ), 2 ≤ l → ∀ (Λs : ℂ), Λs.re = l / 2 → |Λs.im| ≤ 1 →
      ∀ y : ℝ, 0 ≤ y → y ≤ l →
        |sfPart Λs 1 y - l ^ 2 * ((y / l) ^ 2 / 2 - 4 * (y / l) ^ 3 / 3 + (y / l) ^ 4)|
          ≤ C * (1 + l) := by
  obtain ⟨C2, h2⟩ := prime_logpow_sum 2 le_rfl
  obtain ⟨C3, h3⟩ := prime_logpow_sum 3 (by norm_num)
  obtain ⟨C4, h4⟩ := prime_logpow_sum 4 (by norm_num)
  refine ⟨|C2| + 12 * |C3| + 6 + 9 * |C4| + 4, fun l hl Λs hre him y hy0 hyl => ?_⟩
  have hl0 : 0 < l := by linarith
  have hl1 : 1 + l ≤ 3 / 2 * l := by linarith
  have h1l : 0 ≤ 1 + l := by linarith
  have hy1 : 1 + y ≤ 1 + l := by linarith
  -- the three prime sums
  set S2 := primeLogPowSum 2 y with hS2
  set S3 := primeLogPowSum 3 y with hS3
  set S4 := primeLogPowSum 4 y with hS4
  have e2 : |S2 - y ^ 2 / 2| ≤ |C2| * (1 + l) := by
    have h := h2 y hy0
    simp only [Nat.cast_ofNat] at h
    rw [show (2:ℕ) - 1 = 1 from rfl, pow_one] at h
    calc |S2 - y ^ 2 / 2| ≤ C2 * (1 + y) := h
      _ ≤ |C2| * (1 + y) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ |C2| * (1 + l) := mul_le_mul_of_nonneg_left hy1 (abs_nonneg _)
  have e3 : |S3 - y ^ 3 / 3| ≤ |C3| * (1 + l) ^ 2 := by
    have h := h3 y hy0
    simp only [Nat.cast_ofNat] at h
    rw [show (3:ℕ) - 1 = 2 from rfl] at h
    calc |S3 - y ^ 3 / 3| ≤ C3 * (1 + y) ^ 2 := h
      _ ≤ |C3| * (1 + y) ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C3| * (1 + l) ^ 2 := by gcongr
  have e4 : |S4 - y ^ 4 / 4| ≤ |C4| * (1 + l) ^ 3 := by
    have h := h4 y hy0
    simp only [Nat.cast_ofNat] at h
    rw [show (4:ℕ) - 1 = 3 from rfl] at h
    calc |S4 - y ^ 4 / 4| ≤ C4 * (1 + y) ^ 3 := h
      _ ≤ |C4| * (1 + y) ^ 3 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C4| * (1 + l) ^ 3 := by gcongr
  -- the parameter
  set zr := (Λs⁻¹).re with hzr
  set w := (‖Λs‖ ^ 2)⁻¹ with hw
  have hz2 : |zr - 2 / l| ≤ 8 / l ^ 3 := inv_re_param hl hre him
  have hw2 : |w - 4 / l ^ 2| ≤ 16 / l ^ 4 := inv_normSq_param hl hre him
  have hwle : w ≤ 4 / l ^ 2 := inv_normSq_param_le hl hre him
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have h8 : 8 / l ^ 3 ≤ 2 / l := by
    rw [div_le_div_iff₀ (by positivity) hl0]
    have : 4 ≤ l ^ 2 := by nlinarith
    nlinarith
  have hzabs : |zr| ≤ 4 / l := by
    have h := abs_sub_abs_le_abs_sub zr (2 / l)
    rw [abs_of_pos (by positivity : (0:ℝ) < 2 / l)] at h
    have : |zr| ≤ 2 / l + 8 / l ^ 3 := by linarith
    calc |zr| ≤ 2 / l + 8 / l ^ 3 := this
      _ ≤ 2 / l + 2 / l := by linarith
      _ = 4 / l := by ring
  -- rewrite sfPart and the main term
  rw [sfPart_one_eq Λs y]
  have hmain : l ^ 2 * ((y / l) ^ 2 / 2 - 4 * (y / l) ^ 3 / 3 + (y / l) ^ 4)
      = y ^ 2 / 2 - 2 * (2 / l) * (y ^ 3 / 3) + (4 / l ^ 2) * (y ^ 4 / 4) := by
    field_simp
    ring
  rw [hmain]
  have hdec : S2 - 2 * zr * S3 + w * S4 - (y ^ 2 / 2 - 2 * (2 / l) * (y ^ 3 / 3) + 4 / l ^ 2 * (y ^ 4 / 4))
      = (S2 - y ^ 2 / 2) + (-(2 * zr) * (S3 - y ^ 3 / 3)) + (-(2 * (zr - 2 / l)) * (y ^ 3 / 3))
        + (w * (S4 - y ^ 4 / 4)) + ((w - 4 / l ^ 2) * (y ^ 4 / 4)) := by ring
  change |S2 - 2 * zr * S3 + w * S4 - (y ^ 2 / 2 - 2 * (2 / l) * (y ^ 3 / 3) + 4 / l ^ 2 * (y ^ 4 / 4))|
    ≤ (|C2| + 12 * |C3| + 6 + 9 * |C4| + 4) * (1 + l)
  rw [hdec]
  -- the five term bounds, each ≤ const · (1+l)
  have hy3 : y ^ 3 ≤ l ^ 3 := pow_le_pow_left₀ hy0 hyl 3
  have hy4 : y ^ 4 ≤ l ^ 4 := pow_le_pow_left₀ hy0 hyl 4
  have t2 : |-(2 * zr) * (S3 - y ^ 3 / 3)| ≤ 12 * |C3| * (1 + l) := by
    rw [abs_mul, abs_neg, abs_mul, abs_two]
    calc 2 * |zr| * |S3 - y ^ 3 / 3| ≤ 2 * (4 / l) * (|C3| * (1 + l) ^ 2) := by
          gcongr
      _ = 8 * |C3| * ((1 + l) / l) * (1 + l) := by field_simp; ring
      _ ≤ 8 * |C3| * (3 / 2) * (1 + l) := by
          have : (1 + l) / l ≤ 3 / 2 := by rw [div_le_iff₀ hl0]; linarith
          gcongr
      _ = 12 * |C3| * (1 + l) := by ring
  have t3 : |-(2 * (zr - 2 / l)) * (y ^ 3 / 3)| ≤ 6 * (1 + l) := by
    rw [abs_mul, abs_neg, abs_mul, abs_two, abs_of_nonneg (by positivity : (0:ℝ) ≤ y ^ 3 / 3)]
    calc 2 * |zr - 2 / l| * (y ^ 3 / 3) ≤ 2 * (8 / l ^ 3) * (l ^ 3 / 3) := by gcongr
      _ = 16 / 3 := by field_simp; ring
      _ ≤ 6 * (1 + l) := by linarith
  have t4 : |w * (S4 - y ^ 4 / 4)| ≤ 9 * |C4| * (1 + l) := by
    rw [abs_mul, abs_of_nonneg hw0]
    calc w * |S4 - y ^ 4 / 4| ≤ (4 / l ^ 2) * (|C4| * (1 + l) ^ 3) := by gcongr
      _ = 4 * |C4| * ((1 + l) ^ 2 / l ^ 2) * (1 + l) := by field_simp
      _ ≤ 4 * |C4| * (9 / 4) * (1 + l) := by
          have : (1 + l) ^ 2 / l ^ 2 ≤ 9 / 4 := by
            rw [div_le_iff₀ (by positivity)]; nlinarith
          gcongr
      _ = 9 * |C4| * (1 + l) := by ring
  have t5 : |(w - 4 / l ^ 2) * (y ^ 4 / 4)| ≤ 4 * (1 + l) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ y ^ 4 / 4)]
    calc |w - 4 / l ^ 2| * (y ^ 4 / 4) ≤ (16 / l ^ 4) * (l ^ 4 / 4) := by gcongr
      _ = 4 := by field_simp; ring
      _ ≤ 4 * (1 + l) := by linarith
  calc |(S2 - y ^ 2 / 2) + (-(2 * zr) * (S3 - y ^ 3 / 3)) + (-(2 * (zr - 2 / l)) * (y ^ 3 / 3))
        + (w * (S4 - y ^ 4 / 4)) + ((w - 4 / l ^ 2) * (y ^ 4 / 4))|
      ≤ |S2 - y ^ 2 / 2| + |-(2 * zr) * (S3 - y ^ 3 / 3)| + |-(2 * (zr - 2 / l)) * (y ^ 3 / 3)|
        + |w * (S4 - y ^ 4 / 4)| + |(w - 4 / l ^ 2) * (y ^ 4 / 4)| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact abs_add_le _ _
    _ ≤ |C2| * (1 + l) + 12 * |C3| * (1 + l) + 6 * (1 + l) + 9 * |C4| * (1 + l) + 4 * (1 + l) :=
        add_le_add (add_le_add (add_le_add (add_le_add e2 t2) t3) t4) t5
    _ = (|C2| + 12 * |C3| + 6 + 9 * |C4| + 4) * (1 + l) := by ring

end XiPrime
end Zeta23
