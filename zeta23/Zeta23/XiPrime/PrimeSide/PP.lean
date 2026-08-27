/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization; bracketed labels such as [prop:PP] refer to the paper.
-/
import Zeta23.XiPrime.Defs
import Zeta23.ThmE.PPChi

/-!
# [prop:PP] for a general-coefficient Dirichlet polynomial  (ξ′ prime side)

The ξ′ theorem's prime side ([XF′] Thm 8.1) is the paper's
§5 computation with the prime density P_X replaced by the Dirichlet polynomial with ARBITRARY complex
coefficients
    P_c(X; τ) = (1/π) Σ_{N ≤ X} (Re c_N cos(τ log N) + Im c_N sin(τ log N))/√N  = Zeta23.XiPrime.Pc X c τ
(Zeta23/XiPrime/Defs.lean).  This file evaluates the bilinear form 𝓜[P_c, P_c] = PrimeSide.Mform Φ T P_c P_c
(paper §5 "Evaluation of 𝓜": the 𝒟/𝒪₁/𝒪₂ split + Montgomery–Vaughan) ONCE for
general weights: writing c_N = ‖c_N‖ e^{i arg c_N},
    P_c(τ) = (1/π) Σ_N w_N cos(τ log N − arg c_N),   w_N := ‖c_N‖/√N,
a single family of phase-shifted cosines, so the phased kernels AminusPh/AplusPh of Zeta23/ThmE/PPChi.lean
(and everything kernel-side in Zeta23/PrimeSideB/PPKernel.lean, which is generic in the frequencies and
phases) apply verbatim.  The three estimates are proved for an ARBITRARY real weight w ≥ 0 with w 1 = 0
and arbitrary phases (section GeneralWeights), then specialised to w = ‖c‖/√· (section Results).

Main result (NON-asymptotic: one (p, F), no T₀, no coefficient hypothesis beyond c 1 = 0):

* prop_PP_c — the three-term form
    |𝓜[P_c,P_c] − (T/π) Σ_N ‖c_N‖²/N g(log N)|
        ≤ K₁(cϱ)·L·Σ‖c_N‖²/N  +  K₂·C·L·Σ‖c_N‖²  +  K₃·L·(Σ‖c_N‖/√N)²
  with K₁ = (8+8cϱ)/(2π²) (𝒟: ∫Φ²|x| ≤ (8+8cϱ)L), K₂ = 32π/(2π²) (𝒪₁: H-MV with Σ w_N²·2N = 2Σ‖c_N‖²,
  ∫Φ² ≤ 2πL), K₃ = (2π/log 2)/(2π²) (𝒪₂: |A⁺(y,y′)| ≤ 2∫Φ²/(y+y′), y, y′ ≥ log 2 — this is where
  c 1 = 0 is used: the frequency log 1 = 0 must carry zero weight);
* prop_PP_c' — the same with one constant KPP C cϱ, shaped exactly as the named input
  Zeta23.XiPrime.PPInput of Zeta23/XiPrime/PrimeSide/Concrete.lean, whose four sums
  Σ‖c‖²/N·g, Σ‖c‖²/N, Σ‖c‖², Σ‖c‖/√N are written here LITERALLY over Finset.Ioc 0 ⌊X⌋₊ (the bodies of
  sumW2g / sumSqDivW / sumSqW / S1), so that PPInput closes by defeq without this file importing the
  assembly.
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace XiPrime

open Zeta23.PrimeSide Zeta23.ThmE

/-! ## The magnitude/phase form of P_c -/

section PcForm

/-- Re c · cos θ + Im c · sin θ = ‖c‖ · cos(θ − arg c). -/
lemma re_mul_cos_add_im_mul_sin (z : ℂ) (θ : ℝ) :
    z.re * Real.cos θ + z.im * Real.sin θ = ‖z‖ * Real.cos (θ - z.arg) := by
  have h1 : ‖z‖ * Real.cos z.arg = z.re := by
    have := Complex.norm_mul_exp_arg_mul_I z
    have h := congrArg Complex.re this
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re] at h
    exact h
  have h2 : ‖z‖ * Real.sin z.arg = z.im := by
    have := Complex.norm_mul_exp_arg_mul_I z
    have h := congrArg Complex.im this
    rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im] at h
    exact h
  rw [Real.cos_sub, ← h1, ← h2]
  ring

/-- the general weight  w_N := ‖c_N‖/√N. -/
def wcoef (c : ℕ → ℂ) (n : ℕ) : ℝ := ‖c n‖ / Real.sqrt n

lemma wcoef_nonneg (c : ℕ → ℂ) (n : ℕ) : 0 ≤ wcoef c n :=
  div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

lemma wcoef_sq (c : ℕ → ℂ) (n : ℕ) : wcoef c n ^ 2 = ‖c n‖ ^ 2 / n := by
  unfold wcoef
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

lemma wcoef_sq_mul {c : ℕ → ℂ} {n : ℕ} (hn : 1 ≤ n) : wcoef c n ^ 2 * n = ‖c n‖ ^ 2 := by
  rw [wcoef_sq]
  have : (0:ℝ) < n := by exact_mod_cast hn
  field_simp

lemma wcoef_one {c : ℕ → ℂ} (hc1 : c 1 = 0) : wcoef c 1 = 0 := by
  simp [wcoef, hc1]

/-- The magnitude/phase form:  P_c(X; τ) = (1/π) Σ_N w_N · cos(τ·log N − arg c_N)
(mirror of ThmE.PXc_eq_sum; sign +1/π here). -/
lemma Pc_eq_sum (c : ℕ → ℂ) (X τ : ℝ) :
    Pc X c τ = (1 / π) * ∑ n ∈ primeRange X, wcoef c n * Real.cos (τ * Real.log n - (c n).arg) := by
  unfold Pc primeRange wcoef
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [re_mul_cos_add_im_mul_sin]
  ring

end PcForm

/-! ## [prop:PP] for a general real weight w and phases φ

Everything in this section is about the phased cosine polynomial  Q(τ) := Σ_{N≤X} w_N cos(τ log N − φ_N)
with ARBITRARY w, φ : ℕ → ℝ; the hypotheses 0 ≤ w, w 1 = 0 enter only the 𝒪₂ estimate. -/

section GeneralWeights
variable {Φ : ℝ → ℝ} {T : ℝ}

/-- Q(τ) := Σ_{N ∈ primeRange X} w_N cos(τ log N − φ_N). -/
def cosPolyPh (X : ℝ) (w φ : ℕ → ℝ) (τ : ℝ) : ℝ :=
  ∑ n ∈ primeRange X, w n * Real.cos (τ * Real.log n - φ n)

/-- **[eq:MPP] for Q** (mirror of Mform_PXc_PXc): bilinearity, the per-pair phased
decomposition Mform_cos_cos_ph, and the diagonal/off-diagonal split:
  𝓜[Q,Q] = ½ ( Σ_n w_n² A⁻(y_n,y_n) + Σ_{n≠m} w_n w_m A⁻_ph + Σ_{n,m} w_n w_m A⁺_ph ). -/
lemma Mform_cosPolyPh (hT : 0 ≤ T) (hΦ : Continuous Φ) (X : ℝ) (w φ : ℕ → ℝ) :
    Mform Φ T (cosPolyPh X w φ) (cosPolyPh X w φ)
      = (1 / 2) *
        ((∑ n ∈ primeRange X, w n ^ 2 * Aminus Φ T (Real.log n) (Real.log n))
          + (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
              (if n = m then (0:ℝ) else w n * w m
                * AminusPh Φ T (Real.log n) (Real.log m) (φ n) (φ m)))
          + ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
              w n * w m * AplusPh Φ T (Real.log n) (Real.log m) (φ n) (φ m)) := by
  have h1 : Mform Φ T (cosPolyPh X w φ) (cosPolyPh X w φ) =
      ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, w n * w m *
        Mform Φ T (fun τ => Real.cos (τ * Real.log n - φ n))
          (fun τ => Real.cos (τ * Real.log m - φ m)) := by
    unfold Mform
    have hpt : ∀ q : ℝ × ℝ, Φ (q.1 - q.2) ^ 2 * cosPolyPh X w φ q.1 * cosPolyPh X w φ q.2
        = ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
            w n * w m *
            (Φ (q.1 - q.2) ^ 2 * Real.cos (q.1 * Real.log n - φ n)
              * Real.cos (q.2 * Real.log m - φ m)) := by
      intro q
      unfold cosPolyPh
      rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    simp_rw [hpt]
    have hint : ∀ n m : ℕ, Integrable (fun q : ℝ × ℝ =>
        w n * w m *
        (Φ (q.1 - q.2) ^ 2 * Real.cos (q.1 * Real.log n - φ n)
          * Real.cos (q.2 * Real.log m - φ m)))
        (volume.restrict (Icc T (2 * T) ×ˢ Icc T (2 * T))) := fun n m =>
      (Mform_integrableOn hΦ (u := fun τ => Real.cos (τ * Real.log n - φ n))
        (v := fun τ => Real.cos (τ * Real.log m - φ m)) (by fun_prop) (by fun_prop)).const_mul _
    rw [integral_finset_sum _ (fun n _ => integrable_finset_sum _ (fun m _ => hint n m))]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_finset_sum _ (fun m _ => hint n m)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_const_mul]
  rw [h1]
  simp_rw [Mform_cos_cos_ph hT hΦ]
  have e : ∀ n m : ℕ, w n * w m *
      ((AminusPh Φ T (Real.log n) (Real.log m) (φ n) (φ m)
        + AplusPh Φ T (Real.log n) (Real.log m) (φ n) (φ m)) / 2)
      = (1 / 2) * (w n * w m * AminusPh Φ T (Real.log n) (Real.log m) (φ n) (φ m))
        + (1 / 2) * (w n * w m * AplusPh Φ T (Real.log n) (Real.log m) (φ n) (φ m)) := by
    intro n m; ring
  simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hA := sum_sum_eq_diag_add_offdiag (primeRange X)
    (fun n m => w n * w m * AminusPh Φ T (Real.log n) (Real.log m) (φ n) (φ m))
  have hdiag : ∑ n ∈ primeRange X, w n * w n * AminusPh Φ T (Real.log n) (Real.log n) (φ n) (φ n)
      = ∑ n ∈ primeRange X, w n ^ 2 * Aminus Φ T (Real.log n) (Real.log n) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [AminusPh_self]
    ring
  rw [hA, hdiag]
  ring

/-- **𝒟 for Q** (mirror of diag_estimate): with ∫Φ²cos(xy) = 2πg(y) [eq:Phi2FT],
  |½ Σ w_n² A⁻(y_n,y_n) − πT Σ w_n² g(y_n)| ≤ ½ (Σ w_n²) ∫Φ²|x|. -/
lemma diag_estimate_w (hT : 0 ≤ T) (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2)
    (hΦabs : Integrable fun x => Φ x ^ 2 * |x|) {g : ℝ → ℝ}
    (hFT : ∀ y, ∫ x, Φ x ^ 2 * Real.cos (x * y) = 2 * π * g y) (X : ℝ) (w : ℕ → ℝ) :
    |(1 / 2) * (∑ n ∈ primeRange X, w n ^ 2 * Aminus Φ T (Real.log n) (Real.log n))
        - π * T * ∑ n ∈ primeRange X, w n ^ 2 * g (Real.log n)|
      ≤ (1 / 2) * (∑ n ∈ primeRange X, w n ^ 2) * ∫ x, Φ x ^ 2 * |x| := by
  have e : (1 / 2) * (∑ n ∈ primeRange X, w n ^ 2 * Aminus Φ T (Real.log n) (Real.log n))
        - π * T * ∑ n ∈ primeRange X, w n ^ 2 * g (Real.log n)
      = (1 / 2) * ∑ n ∈ primeRange X, w n ^ 2 *
          (Aminus Φ T (Real.log n) (Real.log n) - T * ∫ x, Φ x ^ 2 * Real.cos (x * Real.log n)) := by
    simp_rw [hFT]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [e, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc |∑ n ∈ primeRange X, w n ^ 2 *
          (Aminus Φ T (Real.log n) (Real.log n) - T * ∫ x, Φ x ^ 2 * Real.cos (x * Real.log n))|
      ≤ ∑ n ∈ primeRange X, |w n ^ 2 *
          (Aminus Φ T (Real.log n) (Real.log n) - T * ∫ x, Φ x ^ 2 * Real.cos (x * Real.log n))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ primeRange X, w n ^ 2 * ∫ x, Φ x ^ 2 * |x| := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_left (abs_Aminus_diag_sub_le hT hΦ hΦ2 hΦabs _) (sq_nonneg _)
    _ = (∑ n ∈ primeRange X, w n ^ 2) * ∫ x, Φ x ^ 2 * |x| := by rw [Finset.sum_mul]

/-- for n ∈ primeRange X: either n = 1 (where the weight vanishes) or 2 ≤ n. -/
lemma w_eq_zero_or_two_le {w : ℕ → ℝ} (hw1 : w 1 = 0) {X : ℝ} {n : ℕ} (hn : n ∈ primeRange X) :
    w n = 0 ∨ 2 ≤ n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · left
    have : n = 1 := by have := one_le_of_mem_primeRange hn; omega
    subst this; exact hw1
  · exact Or.inr h

/-- **𝒪₂ for Q** (mirror of O2_estimate; "since y_n + y_m ≥ 2 log 2 the second inner
integral is O(1)"):  |Σ_{n,m} w_n w_m A⁺_ph| ≤ (∫Φ²/log 2)·(Σ w_n)², for w ≥ 0 with w 1 = 0. -/
lemma O2_estimate_w (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2) (X T : ℝ)
    {w : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n) (hw1 : w 1 = 0) (φ : ℕ → ℝ) :
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        w n * w m * AplusPh Φ T (Real.log n) (Real.log m) (φ n) (φ m)|
      ≤ (∫ x, Φ x ^ 2) / Real.log 2 * (∑ n ∈ primeRange X, w n) ^ 2 := by
  have hW : 0 ≤ ∫ x, Φ x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hper : ∀ n ∈ primeRange X, ∀ m ∈ primeRange X,
      |w n * w m * AplusPh Φ T (Real.log n) (Real.log m) (φ n) (φ m)|
        ≤ w n * w m * ((∫ x, Φ x ^ 2) / Real.log 2) := by
    intro n hn m hm
    rw [abs_mul, abs_mul, abs_of_nonneg (hw0 n), abs_of_nonneg (hw0 m)]
    rcases w_eq_zero_or_two_le hw1 hn with h0 | hn2
    · simp [h0]
    rcases w_eq_zero_or_two_le hw1 hm with h0 | hm2
    · simp [h0]
    have hyn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
    have hym : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast hm2)
    have hpos : 0 < Real.log n + Real.log m := by linarith
    have hA : |AplusPh Φ T (Real.log n) (Real.log m) (φ n) (φ m)|
        ≤ (∫ x, Φ x ^ 2) / Real.log 2 := by
      calc |AplusPh Φ T (Real.log n) (Real.log m) (φ n) (φ m)|
          ≤ 2 / (Real.log n + Real.log m) * ∫ x, Φ x ^ 2 := abs_AplusPh_le hΦ hΦ2 hpos _ _
        _ ≤ 2 / (2 * Real.log 2) * ∫ x, Φ x ^ 2 := by gcongr; linarith
        _ = (∫ x, Φ x ^ 2) / Real.log 2 := by field_simp
    exact mul_le_mul_of_nonneg_left hA (mul_nonneg (hw0 n) (hw0 m))
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun n _ => Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => hper n hn m hm) ?_
  refine le_of_eq ?_
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- H-MV size bookkeeping for a general weight (mirror of MV_size_le₂): if |M_n| ≤ W on the range then
  C·√(Σ (w_n M_n)²·2n)·√(Σ w_n²·2n) ≤ 2CW·Σ w_n² n   (both slot orders). -/
lemma MV_size_le_w {C : ℝ} (hC : 0 ≤ C) (X : ℝ) (w : ℕ → ℝ) {M : ℕ → ℝ} {W : ℝ} (hW : 0 ≤ W)
    (hM : ∀ n ∈ primeRange X, |M n| ≤ W) :
    C * Real.sqrt (∑ n ∈ primeRange X, (w n * M n) ^ 2 * (2 * n))
        * Real.sqrt (∑ n ∈ primeRange X, w n ^ 2 * (2 * n))
      ≤ 2 * C * W * ∑ n ∈ primeRange X, w n ^ 2 * n ∧
    C * Real.sqrt (∑ n ∈ primeRange X, w n ^ 2 * (2 * n))
        * Real.sqrt (∑ n ∈ primeRange X, (w n * M n) ^ 2 * (2 * n))
      ≤ 2 * C * W * ∑ n ∈ primeRange X, w n ^ 2 * n := by
  set S := ∑ n ∈ primeRange X, w n ^ 2 * n with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have h2S : ∑ n ∈ primeRange X, w n ^ 2 * (2 * n) = 2 * S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hMS : ∑ n ∈ primeRange X, (w n * M n) ^ 2 * (2 * n) ≤ W ^ 2 * (2 * S) := by
    rw [← h2S, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hM2 : M n ^ 2 ≤ W ^ 2 := by
      rw [← sq_abs (M n)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hM n hn) 2
    have hnn : 0 ≤ w n ^ 2 * (2 * n) := mul_nonneg (sq_nonneg _) (by positivity)
    calc (w n * M n) ^ 2 * (2 * n) = M n ^ 2 * (w n ^ 2 * (2 * n)) := by ring
      _ ≤ W ^ 2 * (w n ^ 2 * (2 * n)) := mul_le_mul_of_nonneg_right hM2 hnn
  have hs1 : Real.sqrt (∑ n ∈ primeRange X, w n ^ 2 * (2 * n)) = Real.sqrt (2 * S) := by rw [h2S]
  have hs2 : Real.sqrt (∑ n ∈ primeRange X, (w n * M n) ^ 2 * (2 * n)) ≤ W * Real.sqrt (2 * S) := by
    calc Real.sqrt (∑ n ∈ primeRange X, (w n * M n) ^ 2 * (2 * n))
        ≤ Real.sqrt (W ^ 2 * (2 * S)) := Real.sqrt_le_sqrt hMS
      _ = W * Real.sqrt (2 * S) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hW]
  have hsq : Real.sqrt (2 * S) * Real.sqrt (2 * S) = 2 * S := Real.mul_self_sqrt (by positivity)
  have h2Snn : 0 ≤ Real.sqrt (2 * S) := Real.sqrt_nonneg _
  constructor
  · rw [hs1]
    calc C * Real.sqrt (∑ n ∈ primeRange X, (w n * M n) ^ 2 * (2 * n)) * Real.sqrt (2 * S)
        ≤ C * (W * Real.sqrt (2 * S)) * Real.sqrt (2 * S) := by
          apply mul_le_mul_of_nonneg_right _ h2Snn
          exact mul_le_mul_of_nonneg_left hs2 hC
      _ = C * W * (Real.sqrt (2 * S) * Real.sqrt (2 * S)) := by ring
      _ = 2 * C * W * S := by rw [hsq]; ring
  · rw [hs1]
    calc C * Real.sqrt (2 * S) * Real.sqrt (∑ n ∈ primeRange X, (w n * M n) ^ 2 * (2 * n))
        ≤ C * Real.sqrt (2 * S) * (W * Real.sqrt (2 * S)) :=
          mul_le_mul_of_nonneg_left hs2 (mul_nonneg hC h2Snn)
      _ = C * W * (Real.sqrt (2 * S) * Real.sqrt (2 * S)) := by ring
      _ = 2 * C * W * S := by rw [hsq]; ring

/-- One H-MV application with a bounded multiplier M (|M_n| ≤ W := ∫Φ²) in either slot and either
trig function: the four shapes of off-diagonal sums met in 𝒪₁ are each ≤ 2CW·Σ w_n² n. -/
lemma MV_four {C : ℝ} (hMV : Zeta23.MVHilbert C) (hC : 0 ≤ C) (X cc : ℝ) (w φ : ℕ → ℝ)
    {M : ℕ → ℝ} {W : ℝ} (hW : 0 ≤ W) (hM : ∀ n ∈ primeRange X, |M n| ≤ W) :
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
        w n * M n * w m * Real.sin (cc * (Real.log n - Real.log m) - (φ n - φ m))
          / (Real.log n - Real.log m))| ≤ 2 * C * W * ∑ n ∈ primeRange X, w n ^ 2 * n ∧
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
        w n * M n * w m * Real.cos (cc * (Real.log n - Real.log m) - (φ n - φ m))
          / (Real.log n - Real.log m))| ≤ 2 * C * W * ∑ n ∈ primeRange X, w n ^ 2 * n ∧
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
        w n * (w m * M m) * Real.sin (cc * (Real.log n - Real.log m) - (φ n - φ m))
          / (Real.log n - Real.log m))| ≤ 2 * C * W * ∑ n ∈ primeRange X, w n ^ 2 * n ∧
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
        w n * (w m * M m) * Real.cos (cc * (Real.log n - Real.log m) - (φ n - φ m))
          / (Real.log n - Real.log m))| ≤ 2 * C * W * ∑ n ∈ primeRange X, w n ^ 2 * n := by
  have hL := MV_real_ph hMV X cc (fun k => w k * M k) (fun k => w k) φ
  have hR := MV_real_ph hMV X cc (fun k => w k) (fun k => w k * M k) φ
  have hsz := MV_size_le_w hC X w hW hM
  exact ⟨hL.2.trans hsz.1, hL.1.trans hsz.1, hR.2.trans hsz.2, hR.1.trans hsz.2⟩

/-- **𝒪₁ for Q** (mirror of O1_bound): the exact evaluation sub_mul_AminusPh_eq splits
Σ_{n≠m} w_n w_m A⁻_ph into eight off-diagonal trigonometric sums, each an H-MV sum with one bounded
multiplier (C^∓, S^∓, all ≤ ∫Φ² in modulus):  |Σ_{n≠m} w_n w_m A⁻_ph| ≤ 16·C·(∫Φ²)·Σ_n w_n² n. -/
theorem O1_bound_w {C : ℝ} (hMV : Zeta23.MVHilbert C) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2) (X : ℝ) (w φ : ℕ → ℝ) :
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        (if n = m then (0:ℝ) else w n * w m
          * AminusPh Φ T (Real.log n) (Real.log m) (φ n) (φ m))|
      ≤ 16 * C * (∫ x, Φ x ^ 2) * ∑ n ∈ primeRange X, w n ^ 2 * n := by
  set W : ℝ := ∫ x, Φ x ^ 2 with hW
  have hW0 : 0 ≤ W := MeasureTheory.integral_nonneg fun x => sq_nonneg _
  set S : ℝ := ∑ n ∈ primeRange X, w n ^ 2 * n with hSdef
  set S1 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    w n * Cm Φ T (Real.log n) * w m
      * Real.sin ((2 * T) * (Real.log n - Real.log m) - (φ n - φ m)) / (Real.log n - Real.log m)) with hS1
  set S2 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    w n * Sm Φ T (Real.log n) * w m
      * Real.cos ((2 * T) * (Real.log n - Real.log m) - (φ n - φ m)) / (Real.log n - Real.log m)) with hS2
  set S3 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    w n * (w m * Cm Φ T (Real.log m))
      * Real.sin (T * (Real.log n - Real.log m) - (φ n - φ m)) / (Real.log n - Real.log m)) with hS3
  set S4 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    w n * (w m * Sm Φ T (Real.log m))
      * Real.cos (T * (Real.log n - Real.log m) - (φ n - φ m)) / (Real.log n - Real.log m)) with hS4
  set S5 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    w n * (w m * Cp Φ T (Real.log m))
      * Real.sin ((2 * T) * (Real.log n - Real.log m) - (φ n - φ m)) / (Real.log n - Real.log m)) with hS5
  set S6 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    w n * (w m * Sp Φ T (Real.log m))
      * Real.cos ((2 * T) * (Real.log n - Real.log m) - (φ n - φ m)) / (Real.log n - Real.log m)) with hS6
  set S7 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    w n * Cp Φ T (Real.log n) * w m
      * Real.sin (T * (Real.log n - Real.log m) - (φ n - φ m)) / (Real.log n - Real.log m)) with hS7
  set S8 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    w n * Sp Φ T (Real.log n) * w m
      * Real.cos (T * (Real.log n - Real.log m) - (φ n - φ m)) / (Real.log n - Real.log m)) with hS8
  have hsplit : ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
      (if n = m then (0:ℝ) else w n * w m
        * AminusPh Φ T (Real.log n) (Real.log m) (φ n) (φ m))
      = S1 + S2 - S3 - S4 + S5 + S6 - S7 - S8 := by
    rw [hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => ?_
    by_cases hnm : n = m
    · simp [hnm]
    · simp only [if_neg hnm]
      have hθ : Real.log n - Real.log m ≠ 0 := by
        have hn1 := one_le_of_mem_primeRange hn
        have hm1 := one_le_of_mem_primeRange hm
        have hinj : Real.log n ≠ Real.log m := by
          rcases lt_or_gt_of_ne hnm with hlt | hgt
          · exact ne_of_lt (Real.log_lt_log (by exact_mod_cast hn1) (by exact_mod_cast hlt))
          · exact ne_of_gt (Real.log_lt_log (by exact_mod_cast hm1) (by exact_mod_cast hgt))
        exact sub_ne_zero.mpr hinj
      have hA := sub_mul_AminusPh_eq (Φ := Φ) hT hΦ hθ (φ n) (φ m)
      have hAm : AminusPh Φ T (Real.log n) (Real.log m) (φ n) (φ m)
          = ((Real.sin ((Real.log n - Real.log m) * (2 * T) - (φ n - φ m)) * Cm Φ T (Real.log n)
              + Real.cos ((Real.log n - Real.log m) * (2 * T) - (φ n - φ m)) * Sm Φ T (Real.log n)
              - (Real.sin ((Real.log n - Real.log m) * T - (φ n - φ m)) * Cm Φ T (Real.log m)
                + Real.cos ((Real.log n - Real.log m) * T - (φ n - φ m)) * Sm Φ T (Real.log m)))
            + (Real.sin ((Real.log n - Real.log m) * (2 * T) - (φ n - φ m)) * Cp Φ T (Real.log m)
              + Real.cos ((Real.log n - Real.log m) * (2 * T) - (φ n - φ m)) * Sp Φ T (Real.log m)
              - (Real.sin ((Real.log n - Real.log m) * T - (φ n - φ m)) * Cp Φ T (Real.log n)
                + Real.cos ((Real.log n - Real.log m) * T - (φ n - φ m)) * Sp Φ T (Real.log n))))
            / (Real.log n - Real.log m) := by
        rw [eq_div_iff hθ, mul_comm]
        exact hA
      rw [hAm, mul_comm ((2 : ℝ) * T) (Real.log n - Real.log m),
        mul_comm T (Real.log n - Real.log m)]
      field_simp
      ring
  have hw_Cm : ∀ n ∈ primeRange X, |Cm Φ T (Real.log n)| ≤ W := fun n _ => abs_Cm_le hT hΦ hΦ2 _
  have hw_Sm : ∀ n ∈ primeRange X, |Sm Φ T (Real.log n)| ≤ W := fun n _ => abs_Sm_le hT hΦ hΦ2 _
  have hw_Cp : ∀ n ∈ primeRange X, |Cp Φ T (Real.log n)| ≤ W := fun n _ => abs_Cp_le hT hΦ hΦ2 _
  have hw_Sp : ∀ n ∈ primeRange X, |Sp Φ T (Real.log n)| ≤ W := fun n _ => abs_Sp_le hT hΦ hΦ2 _
  have h2Cm := MV_four hMV hC X (2 * T) w φ hW0 hw_Cm
  have h2Sm := MV_four hMV hC X (2 * T) w φ hW0 hw_Sm
  have h2Cp := MV_four hMV hC X (2 * T) w φ hW0 hw_Cp
  have h2Sp := MV_four hMV hC X (2 * T) w φ hW0 hw_Sp
  have h1Cm := MV_four hMV hC X T w φ hW0 hw_Cm
  have h1Sm := MV_four hMV hC X T w φ hW0 hw_Sm
  have h1Cp := MV_four hMV hC X T w φ hW0 hw_Cp
  have h1Sp := MV_four hMV hC X T w φ hW0 hw_Sp
  have hb1 : |S1| ≤ 2 * C * W * S := h2Cm.1
  have hb2 : |S2| ≤ 2 * C * W * S := h2Sm.2.1
  have hb3 : |S3| ≤ 2 * C * W * S := h1Cm.2.2.1
  have hb4 : |S4| ≤ 2 * C * W * S := h1Sm.2.2.2
  have hb5 : |S5| ≤ 2 * C * W * S := h2Cp.2.2.1
  have hb6 : |S6| ≤ 2 * C * W * S := h2Sp.2.2.2
  have hb7 : |S7| ≤ 2 * C * W * S := h1Cp.1
  have hb8 : |S8| ≤ 2 * C * W * S := h1Sp.2.1
  rw [hsplit]
  have habs : |S1 + S2 - S3 - S4 + S5 + S6 - S7 - S8|
      ≤ |S1| + |S2| + |S3| + |S4| + |S5| + |S6| + |S7| + |S8| := by
    have t1 := abs_add_le S1 S2
    have t2 := abs_sub (S1 + S2) S3
    have t3 := abs_sub (S1 + S2 - S3) S4
    have t4 := abs_add_le (S1 + S2 - S3 - S4) S5
    have t5 := abs_add_le (S1 + S2 - S3 - S4 + S5) S6
    have t6 := abs_sub (S1 + S2 - S3 - S4 + S5 + S6) S7
    have t7 := abs_sub (S1 + S2 - S3 - S4 + S5 + S6 - S7) S8
    linarith
  calc |S1 + S2 - S3 - S4 + S5 + S6 - S7 - S8|
      ≤ |S1| + |S2| + |S3| + |S4| + |S5| + |S6| + |S7| + |S8| := habs
    _ ≤ 8 * (2 * C * W * S) := by linarith
    _ = 16 * C * W * S := by ring

end GeneralWeights

/-! ## Assembly: [prop:PP] for P_c -/

section Results
variable {C cϱ : ℝ} {p : Setting} {F : LocalFun}

/-- [eq:MPP] for P_c:  𝓜[P_c,P_c] = (1/2π²)·(𝒟-sum + 𝒪₁-sum + 𝒪₂-sum) with weights w_N = ‖c_N‖/√N and
phases arg c_N ((1/π)·(1/π) = 1/π², as (−1/π)² in the ζ case). -/
lemma Mform_Pc_Pc {Φ : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hΦ : Continuous Φ) (c : ℕ → ℂ) (X : ℝ) :
    Mform Φ T (Pc X c) (Pc X c)
      = (1 / (2 * π ^ 2)) *
        ((∑ n ∈ primeRange X, wcoef c n ^ 2 * Aminus Φ T (Real.log n) (Real.log n))
          + (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
              (if n = m then (0:ℝ) else wcoef c n * wcoef c m
                * AminusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg))
          + ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
              wcoef c n * wcoef c m
                * AplusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg) := by
  have hP : Pc X c = fun τ => (1 / π) * cosPolyPh X (wcoef c) (fun n => (c n).arg) τ := by
    funext τ
    rw [Pc_eq_sum]
    rfl
  rw [hP, Mform_const_mul_left, Mform_const_mul_right, Mform_cosPolyPh hT hΦ]
  ring

/-- the single constant of the PPInput-shaped form. -/
def KPP (C cϱ : ℝ) : ℝ := (1 / (2 * π ^ 2)) * ((8 + 8 * cϱ) + 32 * π * C + 2 * π / Real.log 2)

/-- **[prop:PP] for the general-coefficient Dirichlet polynomial P_c — three-term form.**
For ONE (p, F) under the window-generic taper hypotheses LocalHypsCore, T ≥ 1, an H-MV constant C ≥ 0,
and any c : ℕ → ℂ with c 1 = 0:
  |𝓜[P_c,P_c] − (T/π)·Σ_{N≤X} ‖c_N‖²/N·g(log N)|
      ≤ (8+8cϱ)/(2π²)·L·Σ‖c_N‖²/N  +  32π/(2π²)·C·L·Σ‖c_N‖²  +  (2π/log 2)/(2π²)·L·(Σ‖c_N‖/√N)²,
all sums over N ∈ Finset.Ioc 0 ⌊X⌋₊ (= PrimeSide.primeRange X). -/
theorem prop_PP_c (hMV : Zeta23.MVHilbert C) (hC : 0 ≤ C) (hF : LocalHypsCore cϱ p F)
    (hT : 1 ≤ p.T) (c : ℕ → ℂ) (hc1 : c 1 = 0) :
    |Mform F.Phi p.T (Pc p.X c) (Pc p.X c)
        - p.T / π * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, ‖c n‖ ^ 2 / n * F.g (Real.log n)|
      ≤ (1 / (2 * π ^ 2)) * (8 + 8 * cϱ) * p.L * (∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, ‖c n‖ ^ 2 / n)
        + (1 / (2 * π ^ 2)) * (32 * π) * C * p.L * (∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, ‖c n‖ ^ 2)
        + (1 / (2 * π ^ 2)) * (2 * π / Real.log 2) * p.L
            * (∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, ‖c n‖ / Real.sqrt n) ^ 2 := by
  -- all sums are over primeRange p.X (defeq); rename
  show |Mform F.Phi p.T (Pc p.X c) (Pc p.X c)
        - p.T / π * ∑ n ∈ primeRange p.X, ‖c n‖ ^ 2 / n * F.g (Real.log n)|
      ≤ (1 / (2 * π ^ 2)) * (8 + 8 * cϱ) * p.L * (∑ n ∈ primeRange p.X, ‖c n‖ ^ 2 / n)
        + (1 / (2 * π ^ 2)) * (32 * π) * C * p.L * (∑ n ∈ primeRange p.X, ‖c n‖ ^ 2)
        + (1 / (2 * π ^ 2)) * (2 * π / Real.log 2) * p.L
            * (∑ n ∈ primeRange p.X, ‖c n‖ / Real.sqrt n) ^ 2
  have hπ : (0:ℝ) < π := Real.pi_pos
  have hT0 : 0 ≤ p.T := by linarith
  have hL8 : 8 ≤ p.L := hF.eight_le_L
  have hL1 : 1 ≤ p.L := by linarith
  have hΦc : Continuous F.Phi := hF.Phi_contDiff.continuous
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcϱ : 4 ≤ cϱ := hF.four_le_cϱ
  set W := ∫ x, F.Phi x ^ 2 with hWdef
  have hW0 : 0 ≤ W := integral_nonneg fun x => sq_nonneg _
  have hWle : W ≤ 2 * π * p.L := hF.integral_Phi_sq_le
  set ΛΦ := ∫ x, F.Phi x ^ 2 * |x| with hΛΦdef
  have hΛΦ0 : 0 ≤ ΛΦ := integral_nonneg fun x => mul_nonneg (sq_nonneg _) (abs_nonneg _)
  have hΛΦle : ΛΦ ≤ (8 + 8 * cϱ) * p.L := by
    have h1 := hF.integral_Phi_sq_mul_abs_le
    have hw : 1 ≤ p.w := hF.one_le_w
    have hcL : 0 ≤ cϱ * p.L := mul_nonneg (by linarith) (by linarith)
    have harg : 0 < cϱ * p.L / (4 * p.w) := by positivity
    have hlog : Real.log (cϱ * p.L / (4 * p.w)) ≤ cϱ * p.L / (4 * p.w) := by
      linarith [Real.log_le_sub_one_of_pos harg]
    have hfrac : cϱ * p.L / (4 * p.w) ≤ cϱ * p.L := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hcL (by linarith : (0:ℝ) ≤ 4 * p.w - 1)]
    calc ΛΦ ≤ 8 + 8 * Real.log (cϱ * p.L / (4 * p.w)) := h1
      _ ≤ 8 + 8 * (cϱ * p.L) := by linarith
      _ ≤ 8 * p.L + 8 * (cϱ * p.L) := by linarith
      _ = (8 + 8 * cϱ) * p.L := by ring
  -- the three coefficient sums
  set A := ∑ n ∈ primeRange p.X, ‖c n‖ ^ 2 / n with hAdef
  set B := ∑ n ∈ primeRange p.X, ‖c n‖ ^ 2 with hBdef
  set S₁ := ∑ n ∈ primeRange p.X, ‖c n‖ / Real.sqrt n with hS₁def
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun n _ => sq_nonneg _
  -- the weight sums in terms of A, B, S₁
  have hwA : ∑ n ∈ primeRange p.X, wcoef c n ^ 2 = A := by
    rw [hAdef]
    exact Finset.sum_congr rfl fun n _ => wcoef_sq c n
  have hwB : ∑ n ∈ primeRange p.X, wcoef c n ^ 2 * n = B := by
    rw [hBdef]
    exact Finset.sum_congr rfl fun n hn => wcoef_sq_mul (one_le_of_mem_primeRange hn)
  have hwS : ∑ n ∈ primeRange p.X, wcoef c n = S₁ := by
    rw [hS₁def]
    rfl
  have hwg : ∑ n ∈ primeRange p.X, wcoef c n ^ 2 * F.g (Real.log n)
      = ∑ n ∈ primeRange p.X, ‖c n‖ ^ 2 / n * F.g (Real.log n) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [wcoef_sq]
  -- the three estimates
  have hD := diag_estimate_w hT0 hΦc hF.Phi_sq_integrable hF.Phi_sq_mul_abs_integrable
    hF.Phi_sq_fourier p.X (wcoef c)
  have hO1 := O1_bound_w hMV hC hT0 hΦc hF.Phi_sq_integrable p.X (wcoef c) (fun n => (c n).arg)
  have hO2 := O2_estimate_w hΦc hF.Phi_sq_integrable p.X p.T (wcoef_nonneg c) (wcoef_one hc1)
    (fun n => (c n).arg)
  rw [hwA] at hD
  rw [hwB] at hO1
  rw [hwS] at hO2
  rw [Mform_Pc_Pc hT0 hΦc, ← hwg]
  set D := ∑ n ∈ primeRange p.X, wcoef c n ^ 2 * Aminus F.Phi p.T (Real.log n) (Real.log n)
    with hDdef
  set O1 := ∑ n ∈ primeRange p.X, ∑ m ∈ primeRange p.X,
    (if n = m then (0:ℝ) else wcoef c n * wcoef c m
      * AminusPh F.Phi p.T (Real.log n) (Real.log m) (c n).arg (c m).arg) with hO1def
  set O2 := ∑ n ∈ primeRange p.X, ∑ m ∈ primeRange p.X,
    wcoef c n * wcoef c m
      * AplusPh F.Phi p.T (Real.log n) (Real.log m) (c n).arg (c m).arg with hO2def
  set G := ∑ n ∈ primeRange p.X, wcoef c n ^ 2 * F.g (Real.log n) with hGdef
  have hk : (0:ℝ) < 1 / (2 * π ^ 2) := by positivity
  -- 𝒟: rescale diag_estimate_w by 1/π²
  have bD : |1 / (2 * π ^ 2) * D - p.T / π * G| ≤ 1 / (2 * π ^ 2) * (8 + 8 * cϱ) * p.L * A := by
    have e : 1 / (2 * π ^ 2) * D - p.T / π * G = (1 / π ^ 2) * ((1 / 2) * D - π * p.T * G) := by
      field_simp
    rw [e, abs_mul, abs_of_pos (by positivity)]
    calc 1 / π ^ 2 * |1 / 2 * D - π * p.T * G|
        ≤ 1 / π ^ 2 * ((1 / 2) * A * ΛΦ) := mul_le_mul_of_nonneg_left hD (by positivity)
      _ ≤ 1 / π ^ 2 * ((1 / 2) * A * ((8 + 8 * cϱ) * p.L)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hΛΦle (by positivity)
      _ = 1 / (2 * π ^ 2) * (8 + 8 * cϱ) * p.L * A := by
          field_simp
  have bO1 : |1 / (2 * π ^ 2) * O1| ≤ 1 / (2 * π ^ 2) * (32 * π) * C * p.L * B := by
    rw [abs_mul, abs_of_pos hk]
    calc 1 / (2 * π ^ 2) * |O1|
        ≤ 1 / (2 * π ^ 2) * (16 * C * W * B) := mul_le_mul_of_nonneg_left hO1 hk.le
      _ ≤ 1 / (2 * π ^ 2) * (16 * C * (2 * π * p.L) * B) := by
          apply mul_le_mul_of_nonneg_left _ hk.le
          apply mul_le_mul_of_nonneg_right _ hB0
          exact mul_le_mul_of_nonneg_left hWle (by positivity)
      _ = 1 / (2 * π ^ 2) * (32 * π) * C * p.L * B := by ring
  have bO2 : |1 / (2 * π ^ 2) * O2| ≤ 1 / (2 * π ^ 2) * (2 * π / Real.log 2) * p.L * S₁ ^ 2 := by
    rw [abs_mul, abs_of_pos hk]
    calc 1 / (2 * π ^ 2) * |O2|
        ≤ 1 / (2 * π ^ 2) * (W / Real.log 2 * S₁ ^ 2) := mul_le_mul_of_nonneg_left hO2 hk.le
      _ ≤ 1 / (2 * π ^ 2) * ((2 * π * p.L) / Real.log 2 * S₁ ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hk.le
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact div_le_div_of_nonneg_right hWle hlog2.le
      _ = 1 / (2 * π ^ 2) * (2 * π / Real.log 2) * p.L * S₁ ^ 2 := by ring
  have split : 1 / (2 * π ^ 2) * (D + O1 + O2) - p.T / π * G
      = (1 / (2 * π ^ 2) * D - p.T / π * G) + 1 / (2 * π ^ 2) * O1 + 1 / (2 * π ^ 2) * O2 := by ring
  rw [split]
  calc |(1 / (2 * π ^ 2) * D - p.T / π * G) + 1 / (2 * π ^ 2) * O1 + 1 / (2 * π ^ 2) * O2|
      ≤ |1 / (2 * π ^ 2) * D - p.T / π * G| + |1 / (2 * π ^ 2) * O1| + |1 / (2 * π ^ 2) * O2| :=
        abs_add_three _ _ _
    _ ≤ 1 / (2 * π ^ 2) * (8 + 8 * cϱ) * p.L * A
        + 1 / (2 * π ^ 2) * (32 * π) * C * p.L * B
        + 1 / (2 * π ^ 2) * (2 * π / Real.log 2) * p.L * S₁ ^ 2 :=
        add_le_add (add_le_add bD bO1) bO2

/-- **[prop:PP] for P_c — PPInput-shaped form** (one constant KPP C cϱ; literally the body of
Zeta23.XiPrime.PPInput in Zeta23/XiPrime/PrimeSide/Concrete.lean with K := KPP C cϱ). -/
theorem prop_PP_c' (hMV : Zeta23.MVHilbert C) (hC : 0 ≤ C) (hF : LocalHypsCore cϱ p F)
    (hT : 1 ≤ p.T) (c : ℕ → ℂ) (hc1 : c 1 = 0) :
    |Mform F.Phi p.T (Pc p.X c) (Pc p.X c)
        - p.T / π * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, ‖c n‖ ^ 2 / n * F.g (Real.log n)|
      ≤ KPP C cϱ * p.L *
        ((∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, ‖c n‖ ^ 2 / n)
          + (∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, ‖c n‖ ^ 2)
          + (∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, ‖c n‖ / Real.sqrt n) ^ 2) := by
  have h := prop_PP_c hMV hC hF hT c hc1
  refine h.trans ?_
  set A := ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, ‖c n‖ ^ 2 / n
  set B := ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, ‖c n‖ ^ 2
  set S₁ := ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, ‖c n‖ / Real.sqrt n
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hS0 : 0 ≤ S₁ ^ 2 := sq_nonneg _
  have hL : 0 ≤ p.L := hF.L_pos.le
  have hcϱ : 4 ≤ cϱ := hF.four_le_cϱ
  have hπ : (0:ℝ) < π := Real.pi_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk : (0:ℝ) ≤ 1 / (2 * π ^ 2) := by positivity
  have h1 : (0:ℝ) ≤ 8 + 8 * cϱ := by linarith
  have h2 : (0:ℝ) ≤ 32 * π * C := by positivity
  have h3 : (0:ℝ) ≤ 2 * π / Real.log 2 := by positivity
  unfold KPP
  have eA : 1 / (2 * π ^ 2) * (8 + 8 * cϱ) * p.L * A
      ≤ 1 / (2 * π ^ 2) * ((8 + 8 * cϱ) + 32 * π * C + 2 * π / Real.log 2) * p.L * A := by
    apply mul_le_mul_of_nonneg_right _ hA0
    apply mul_le_mul_of_nonneg_right _ hL
    apply mul_le_mul_of_nonneg_left _ hk
    linarith
  have eB : 1 / (2 * π ^ 2) * (32 * π) * C * p.L * B
      ≤ 1 / (2 * π ^ 2) * ((8 + 8 * cϱ) + 32 * π * C + 2 * π / Real.log 2) * p.L * B := by
    rw [show 1 / (2 * π ^ 2) * (32 * π) * C = 1 / (2 * π ^ 2) * (32 * π * C) by ring]
    apply mul_le_mul_of_nonneg_right _ hB0
    apply mul_le_mul_of_nonneg_right _ hL
    apply mul_le_mul_of_nonneg_left _ hk
    linarith
  have eS : 1 / (2 * π ^ 2) * (2 * π / Real.log 2) * p.L * S₁ ^ 2
      ≤ 1 / (2 * π ^ 2) * ((8 + 8 * cϱ) + 32 * π * C + 2 * π / Real.log 2) * p.L * S₁ ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ hS0
    apply mul_le_mul_of_nonneg_right _ hL
    apply mul_le_mul_of_nonneg_left _ hk
    linarith
  calc 1 / (2 * π ^ 2) * (8 + 8 * cϱ) * p.L * A
        + 1 / (2 * π ^ 2) * (32 * π) * C * p.L * B
        + 1 / (2 * π ^ 2) * (2 * π / Real.log 2) * p.L * S₁ ^ 2
      ≤ 1 / (2 * π ^ 2) * ((8 + 8 * cϱ) + 32 * π * C + 2 * π / Real.log 2) * p.L * A
        + 1 / (2 * π ^ 2) * ((8 + 8 * cϱ) + 32 * π * C + 2 * π / Real.log 2) * p.L * B
        + 1 / (2 * π ^ 2) * ((8 + 8 * cϱ) + 32 * π * C + 2 * π / Real.log 2) * p.L * S₁ ^ 2 :=
        add_le_add (add_le_add eA eB) eS
    _ = 1 / (2 * π ^ 2) * ((8 + 8 * cϱ) + 32 * π * C + 2 * π / Real.log 2) * p.L
        * (A + B + S₁ ^ 2) := by ring

end Results

end XiPrime
end Zeta23

