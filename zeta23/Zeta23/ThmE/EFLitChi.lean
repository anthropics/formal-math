/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/EFLitChi.lean — the literature-form explicit formula for L(s,χ)
(primitive χ mod q > 1) and its bridge to ExplicitFormulaPaperChi.

The paper does not display the χ-EF ([thm:E] proof (i),
§8.2, says only "the derivation of Appendix A applies to [IK04, Theorem 5.12] for
L(s,χ)"); literatureRHSchi below is a transcription of IK04-Thm-5.12-for-L(s,χ), with
the χ/conj(χ) leg assignment forced by the paper's ν-side display P_{X,χ} (§8.2).

Conventions: h := paperFT k (h(z) = ∫k(u)e^{izu}du); κ = (1−χ(−1))/2; no pole terms (Λ(s,χ)
entire for primitive χ, q > 1); coefficients c n = (coeff χ) n (the character values ℕ → ℂ).
-/
import Zeta23.ThmE.PrimeSideChi
import Zeta23.ExplicitFormula
import Zeta23.ExplicitFormula.Bridge

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Real Set Complex
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace ThmE

open Zeta23.PrimeSide

/-- Right-hand side of the literature explicit formula for L(s,χ), primitive χ mod q > 1
(IK04 Thm 5.12 specialised; transcription — see file header):
  −Σ_{n≥1} (Λ(n)/√n)(c(n) k(log n) + conj(c(n)) k(−log n))
    + (1/2π)∫_ℝ h(r)·[Re ψ(1/4 + κ/2 + ir/2) + log(q/π)] dr. -/
def literatureRHSchi (κ q : ℕ) (c : ℕ → ℂ) (k : ℝ → ℂ) : ℂ :=
  - ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (c n * k (Real.log n) + (starRingEnd ℂ) (c n) * k (-Real.log n))
  + (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r
      * ((((Complex.digamma (1 / 4 + (κ : ℂ) / 2 + I * r / 2)).re + Real.log (q / π) : ℝ)) : ℂ)

/-- **H-EF(χ), literature form**: for every k ∈ C_c²(ℝ), the zero sum converges absolutely and
  Σ_ρ m_ρ h(γ_ρ) = literatureRHSchi. -/
def EF_lit_chi (κ q : ℕ) (c : ℕ → ℂ) (Z : ZeroConfig) : Prop :=
  ∀ k : ℝ → ℂ, ContDiff ℝ 2 k → HasCompactSupport k →
    Summable (fun ρ : Z.carrier => (Z.mult ρ : ℂ) * paperFT k (gammaOf ρ)) ∧
    ∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT k (gammaOf ρ) = literatureRHSchi κ q c k

/-- Twisted prime term (mirror of Zeta23.EF.prime_term): the c-twisted prime sum equals
∫ h·P_{X,χ} — transcription target: P_{X,χ} = −π⁻¹ Re Σ_{n≤X} Λ(n)χ(n)n^{−1/2−iτ} (§8.2);
Re-unfolding via PXc_eq_sum_cos_sin (Hypotheses.lean) assigns c(n) to the e^{−iτ log n} leg. -/
theorem integrable_paperFT_mul_sin {k : ℝ → ℂ}
    (hFk : Integrable (FourierTransform.fourier k)) (y : ℝ) :
    Integrable (fun r : ℝ => paperFT k r * (Real.sin (r * y) : ℂ)) := by
  refine (Zeta23.EF.integrable_paperFT_ofReal hFk).mul_bdd (c := 1) (by fun_prop) ?_
  filter_upwards with r
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_sin_le_one _

/-- Twisted inversion pairing: cc * k(y) + conj(cc) * k(-y) equals (1/pi) times the integral of
h(tau) * (Re cc * cos(tau y) + Im cc * sin(tau y)). -/
theorem ck_add_conj_k_neg {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (FourierTransform.fourier k)) (cc : ℂ) (y : ℝ) :
    cc * k y + (starRingEnd ℂ) cc * k (-y)
      = (1 / π : ℂ) * ∫ τ : ℝ, paperFT k τ
          * ((cc.re * Real.cos (τ * y) + cc.im * Real.sin (τ * y) : ℝ) : ℂ) := by
  rw [Zeta23.EF.paper_inversion hk hki hFk y, Zeta23.EF.paper_inversion hk hki hFk (-y),
    mul_left_comm cc, mul_left_comm ((starRingEnd ℂ) cc), ← mul_add,
    ← Zeta23.EF.cintegral_const_mul cc, ← Zeta23.EF.cintegral_const_mul ((starRingEnd ℂ) cc),
    ← integral_add ((Zeta23.EF.integrable_paperFT_mul_cexp hFk y).const_mul cc)
      ((Zeta23.EF.integrable_paperFT_mul_cexp hFk (-y)).const_mul _)]
  have hconj : (starRingEnd ℂ) cc = (cc.re : ℂ) - (cc.im : ℂ) * I := by
    apply Complex.ext <;> simp
  have hcc : cc = (cc.re : ℂ) + (cc.im : ℂ) * I := (Complex.re_add_im cc).symm
  have h2 : ∀ τ : ℝ, cc * (paperFT k τ * cexp (-I * τ * y))
      + (starRingEnd ℂ) cc * (paperFT k τ * cexp (-I * τ * ↑(-y)))
      = 2 * (paperFT k τ * ((cc.re * Real.cos (τ * y) + cc.im * Real.sin (τ * y) : ℝ) : ℂ)) := by
    intro τ
    have he1 : cexp (-I * τ * y) = Real.cos (τ * y) - Real.sin (τ * y) * I := by
      rw [show (-I * τ * y : ℂ) = ((-(τ * y) : ℝ) : ℂ) * I by push_cast; ring,
        Complex.exp_mul_I]
      push_cast
      simp
      ring
    have he2 : cexp (-I * τ * ((-y : ℝ) : ℂ)) = Real.cos (τ * y) + Real.sin (τ * y) * I := by
      rw [show (-I * τ * ((-y : ℝ) : ℂ) : ℂ) = (((τ * y) : ℝ) : ℂ) * I by push_cast; ring,
        Complex.exp_mul_I]
      push_cast
      ring
    rw [he1, he2]
    nth_rewrite 1 [hcc]
    rw [hconj]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  simp_rw [h2]
  rw [Zeta23.EF.cintegral_const_mul, ← mul_assoc]
  congr 1
  field_simp

/-- Support step, twisted: the summand vanishes for n outside (0, floor(e^L)]. -/
theorem prime_summand_chi_eq_zero {c : ℕ → ℂ} {k : ℝ → ℂ} {L : ℝ}
    (hks : tsupport k ⊆ Icc (-L) L)
    {n : ℕ} (hn : n ∉ Finset.Ioc 0 ⌊Real.exp L⌋₊) :
    ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (c n * k (Real.log n) + (starRingEnd ℂ) (c n) * k (-Real.log n)) = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · have hn' : ⌊Real.exp L⌋₊ < n := by
      simp only [Finset.mem_Ioc, not_and, not_le] at hn
      exact hn hpos
    have hX : Real.exp L < n := (Nat.floor_lt (Real.exp_pos L).le).mp hn'
    have hlog : L < Real.log n := by
      rw [← Real.log_exp L]
      exact Real.log_lt_log (Real.exp_pos L) hX
    have h1 : k (Real.log n) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have := (hks hmem).2
      linarith
    have h2 : k (-Real.log n) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have := (hks hmem).1
      linarith
    rw [h1, h2, mul_zero, mul_zero, add_zero, mul_zero]
theorem prime_term_chi {q : ℕ} {c : ℕ → ℂ} {k : ℝ → ℂ} {L : ℝ} (hk : Continuous k)
    (hks : tsupport k ⊆ Icc (-L) L) (hFk : Integrable (FourierTransform.fourier k)) :
    -(∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
        * (c n * k (Real.log n) + (starRingEnd ℂ) (c n) * k (-Real.log n)))
      = ∫ τ : ℝ, paperFT k τ * (PXc c (Real.exp L) τ : ℂ) := by
  have hki : Integrable k :=
    hk.integrable_of_hasCompactSupport (Zeta23.EF.hasCompactSupport_of_tsupport_subset hks)
  set S := Finset.Ioc 0 ⌊Real.exp L⌋₊ with hS
  rw [tsum_eq_sum (s := S) (fun n hn => prime_summand_chi_eq_zero hks hn)]
  have step1 : ∑ n ∈ S, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
        * (c n * k (Real.log n) + (starRingEnd ℂ) (c n) * k (-Real.log n))
      = ∑ n ∈ S, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
        * ((1 / π : ℂ) * ∫ τ : ℝ, paperFT k τ
            * (((c n).re * Real.cos (τ * Real.log n)
              + (c n).im * Real.sin (τ * Real.log n) : ℝ) : ℂ)) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ck_add_conj_k_neg hk hki hFk (c n) (Real.log n)]
  rw [step1]
  have hint : ∀ n : ℕ, Integrable (fun τ : ℝ => paperFT k τ
      * (((c n).re * Real.cos (τ * Real.log n)
        + (c n).im * Real.sin (τ * Real.log n) : ℝ) : ℂ)) := by
    intro n
    have h1 := (Zeta23.EF.integrable_paperFT_mul_cos hFk (Real.log n)).const_mul
      (((c n).re : ℂ))
    have h2 := (integrable_paperFT_mul_sin hFk (Real.log n)).const_mul (((c n).im : ℂ))
    refine (h1.add h2).congr (Filter.Eventually.of_forall fun τ => ?_)
    simp only [Pi.add_apply]
    push_cast [-Complex.ofReal_cos, -Complex.ofReal_sin]
    ring
  have step2 : (fun τ : ℝ => paperFT k τ * (PXc c (Real.exp L) τ : ℂ))
      = fun τ : ℝ => ∑ n ∈ S, (-(1 / π) * ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ))
          * (paperFT k τ * (((c n).re * Real.cos (τ * Real.log n)
            + (c n).im * Real.sin (τ * Real.log n) : ℝ) : ℂ)) := by
    ext τ
    rw [PXc_eq_sum_cos_sin, ← hS]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
    have hn0' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn0
    have hpow : ((n:ℝ) ^ (-(1/2 : ℝ)) : ℝ) = 1 / Real.sqrt n := by
      rw [Real.rpow_neg hn0'.le, Real.sqrt_eq_rpow]
      exact (one_div _).symm
    rw [hpow]
    push_cast
    ring
  rw [step2, integral_finsetSum _ (fun n _ => (hint n).const_mul _)]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Zeta23.EF.cintegral_const_mul]
  ring

/-- κ-shifted archimedean term (mirror of Zeta23.EF.gamma_term): pointwise-rearrangement of the
bracket into μ_χ (muq's definition is (1/2π)(log(q/π) + Re ψ(1/4+κ/2+iτ/2))). -/
theorem gamma_term_chi {κ q : ℕ} (_hq : 1 ≤ q) (k : ℝ → ℂ) :
    (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r
        * ((((Complex.digamma (1 / 4 + (κ : ℂ) / 2 + I * r / 2)).re + Real.log (q / π) : ℝ)) : ℂ)
      = ∫ τ : ℝ, paperFT k τ * (muq κ q τ : ℂ) := by
  rw [← Zeta23.EF.cintegral_const_mul]
  congr 1
  ext r
  simp only [muq]
  push_cast
  ring

/-- Integrability of h·P_{X,χ} (finite twisted cos/sin sum; no Chebyshev input needed). -/
theorem integrable_paperFT_mul_PXc {k : ℝ → ℂ} (c : ℕ → ℂ) (L : ℝ)
    (hFk : Integrable (FourierTransform.fourier k)) :
    Integrable (fun τ : ℝ => paperFT k τ * (PXc c (Real.exp L) τ : ℂ)) := by
  set S := Finset.Ioc 0 ⌊Real.exp L⌋₊ with hS
  have hint : ∀ n : ℕ, Integrable (fun τ : ℝ => paperFT k τ
      * (((c n).re * Real.cos (τ * Real.log n)
        + (c n).im * Real.sin (τ * Real.log n) : ℝ) : ℂ)) := by
    intro n
    have h1 := (Zeta23.EF.integrable_paperFT_mul_cos hFk (Real.log n)).const_mul
      (((c n).re : ℂ))
    have h2 := (integrable_paperFT_mul_sin hFk (Real.log n)).const_mul (((c n).im : ℂ))
    refine (h1.add h2).congr (Filter.Eventually.of_forall fun τ => ?_)
    simp only [Pi.add_apply]
    push_cast [-Complex.ofReal_cos, -Complex.ofReal_sin]
    ring
  have step2 : (fun τ : ℝ => paperFT k τ * (PXc c (Real.exp L) τ : ℂ))
      = fun τ : ℝ => ∑ n ∈ S, (-(1 / π) * ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ))
          * (paperFT k τ * (((c n).re * Real.cos (τ * Real.log n)
            + (c n).im * Real.sin (τ * Real.log n) : ℝ) : ℂ)) := by
    ext τ
    rw [PXc_eq_sum_cos_sin, ← hS]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
    have hn0' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn0
    have hpow : ((n:ℝ) ^ (-(1/2 : ℝ)) : ℝ) = 1 / Real.sqrt n := by
      rw [Real.rpow_neg hn0'.le, Real.sqrt_eq_rpow]
      exact (one_div _).symm
    rw [hpow]
    push_cast
    ring
  rw [step2]
  exact integrable_finsetSum _ (fun n _ => (hint n).const_mul _)

/-- Mirror of Zeta23.EF.literatureRHS_eq_integral_nu — NO pole term for q > 1. -/
theorem literatureRHSchi_eq_integral_nu {κ q : ℕ} {c : ℕ → ℂ} {k : ℝ → ℂ} {L : ℝ}
    (hq : 1 ≤ q) (_hL : 0 < L) (hk : Continuous k)
    (hks : tsupport k ⊆ Icc (-L) L) (hFk : Integrable (FourierTransform.fourier k))
    (hμ : Integrable (fun τ : ℝ => paperFT k τ * (muq κ q τ : ℂ))) :
    literatureRHSchi κ q c k = ∫ τ : ℝ, paperFT k τ * (nuXc κ q c (Real.exp L) τ : ℂ) := by
  have hP := integrable_paperFT_mul_PXc (k := k) c L hFk
  unfold literatureRHSchi
  rw [prime_term_chi (q := q) hk hks hFk, gamma_term_chi hq k, ← integral_add hP hμ]
  congr 1
  ext τ
  simp only [nuXc]
  push_cast
  ring


/-- From H-Gamma(chi): |mu_chi(tau)| <= K2 (1+|tau|)^(1/2) for all tau (continuity on [-1,1];
Stirling with log(q|tau|/2pi) and log x <= 2 x^(1/2) for |tau| >= 1). -/
theorem abs_muq_le_of_gammaFactsChi {κ q : ℕ} (hΓq : GammaFactsChi κ q) (hq : 1 ≤ q) :
    ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ τ : ℝ, |muq κ q τ| ≤ K₂ * (1 + |τ|) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC⟩ := hΓq.stirling
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hΓq.smooth.continuous.continuousOn (s := Icc (-1 : ℝ) 1))
  have hπ : 0 < 1 / (2 * π) := by positivity
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  set Lq : ℝ := |Real.log (2 * π / q)| with hLq
  set K₂ : ℝ := max M 0 + |C| + (1 / (2 * π)) * Lq + 1 / π with hK₂
  have hLq0 : 0 ≤ Lq := abs_nonneg _
  have hK₂nn : 0 ≤ K₂ := by
    have h1 : 0 ≤ max M 0 := le_max_right _ _
    have h2 : (0:ℝ) ≤ 1 / π := by positivity
    positivity
  refine ⟨K₂, hK₂nn, fun τ => ?_⟩
  have hb1 : 1 ≤ (1 + |τ|) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith [abs_nonneg τ]) (by norm_num)
  rcases le_or_gt |τ| 1 with hτ | hτ
  · have := hM τ (abs_le.mp hτ)
    rw [Real.norm_eq_abs] at this
    calc |muq κ q τ| ≤ max M 0 := this.trans (le_max_left _ _)
      _ ≤ K₂ * 1 := by
        rw [mul_one, hK₂]
        have : (0:ℝ) ≤ 1 / π := by positivity
        have : (0:ℝ) ≤ (1 / (2 * π)) * Lq := by positivity
        linarith [abs_nonneg C]
      _ ≤ K₂ * (1 + |τ|) ^ (1 / 2 : ℝ) := by gcongr
  · have hτ1 : 1 ≤ |τ| := hτ.le
    have hst := hC τ hτ1
    have hsq : 1 ≤ τ ^ 2 := by rw [← sq_abs]; nlinarith
    have hCτ : C / τ ^ 2 ≤ |C| := by
      calc C / τ ^ 2 ≤ |C| / τ ^ 2 := by gcongr; exact le_abs_self C
        _ ≤ |C| := div_le_self (abs_nonneg C) hsq
    have hlogsplit : (q : ℝ) * |τ| / (2 * π) = |τ| / (2 * π / q) := by
      field_simp
    have hlog : |Real.log ((q:ℝ) * |τ| / (2 * π))| ≤ Real.log |τ| + Lq := by
      rw [hlogsplit, Real.log_div (by positivity) (by positivity)]
      calc abs (Real.log |τ| - Real.log (2 * π / q))
          ≤ abs (Real.log |τ|) + Lq := abs_sub _ _
        _ = Real.log |τ| + Lq := by rw [abs_of_nonneg (Real.log_nonneg hτ1)]
    have hlog2 : Real.log |τ| ≤ 2 * (1 + |τ|) ^ (1 / 2 : ℝ) := by
      have := Real.log_le_rpow_div (abs_nonneg τ) (by norm_num : (0 : ℝ) < 1 / 2)
      have hmono : |τ| ^ (1 / 2 : ℝ) ≤ (1 + |τ|) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg τ) (by linarith) (by norm_num)
      calc Real.log |τ| ≤ |τ| ^ (1 / 2 : ℝ) / (1 / 2) := this
        _ = 2 * |τ| ^ (1 / 2 : ℝ) := by ring
        _ ≤ 2 * (1 + |τ|) ^ (1 / 2 : ℝ) := by gcongr
    have hmu : |muq κ q τ| ≤ |C| + (1 / (2 * π)) * (Real.log |τ| + Lq) := by
      have htri : |muq κ q τ| ≤ |muq κ q τ - 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))|
          + |1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))| := by
        have := abs_add_le (muq κ q τ - 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π)))
          (1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π)))
        rwa [sub_add_cancel] at this
      calc |muq κ q τ| ≤ C / τ ^ 2 + |1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))| := by
            linarith
        _ ≤ |C| + (1 / (2 * π)) * (Real.log |τ| + Lq) := by
            rw [abs_mul, abs_of_pos hπ]
            gcongr
    set b := (1 + |τ|) ^ (1 / 2 : ℝ) with hb
    calc |muq κ q τ| ≤ |C| + (1 / (2 * π)) * (Real.log |τ| + Lq) := hmu
      _ ≤ |C| + (1 / (2 * π)) * (2 * b + Lq) := by gcongr
      _ = (|C| + (1 / (2 * π)) * Lq) * 1 + (1 / π) * b := by ring
      _ ≤ (|C| + (1 / (2 * π)) * Lq) * b + (1 / π) * b := by
          gcongr
      _ = (|C| + (1 / (2 * π)) * Lq + 1 / π) * b := by ring
      _ ≤ K₂ * b := by
          gcongr
          rw [hK₂]
          linarith [le_max_right M 0]

/-- k in C_c^2 and H-Gamma(chi) imply h_k times mu_chi is integrable. -/
theorem integrable_paperFT_mul_muq {κ q : ℕ} {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (hΓq : GammaFactsChi κ q) (hq : 1 ≤ q) :
    Integrable (fun τ : ℝ => paperFT k τ * (muq κ q τ : ℂ)) := by
  obtain ⟨Lam, hLam⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  obtain ⟨K₂, hK₂, hmu⟩ := abs_muq_le_of_gammaFactsChi hΓq hq
  set K₁ : ℝ := (∫ u, ‖k u‖) + ∫ u, ‖deriv (deriv k) u‖ with hK₁
  have hK₁nn : 0 ≤ K₁ := by positivity
  have hmeas : AEStronglyMeasurable (fun τ : ℝ => paperFT k τ * (muq κ q τ : ℂ)) :=
    (Zeta23.EF.integrable_paperFT_ofReal (Zeta23.EF.integrable_fourier_of_contDiff_two hk hkc)).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp hΓq.smooth.continuous).aestronglyMeasurable
  have hdom : Integrable (fun τ : ℝ => 2 * K₁ * K₂ * (1 + ‖τ‖) ^ (-(3 / 2) : ℝ)) :=
    (integrable_one_add_norm (by rw [Module.finrank_self]; norm_num)).const_mul _
  refine hdom.mono' hmeas (Filter.Eventually.of_forall fun τ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hb : 0 < 1 + |τ| := by linarith [abs_nonneg τ]
  have h1 : ‖paperFT k τ‖ * (1 + τ ^ 2) ≤ K₁ := Zeta23.EF.norm_paperFT_mul_one_add_sq_le hk hLam τ
  have h2 : |muq κ q τ| ≤ K₂ * (1 + |τ|) ^ (1 / 2 : ℝ) := hmu τ
  have hsq : (1 + |τ|) ^ (2 : ℝ) ≤ 2 * (1 + τ ^ 2) := by
    rw [Real.rpow_two]
    nlinarith [sq_abs τ, sq_nonneg (1 - |τ|)]
  have key : (1 + |τ|) ^ (1 / 2 : ℝ) ≤ 2 * (1 + τ ^ 2) * (1 + |τ|) ^ (-(3 / 2) : ℝ) := by
    rw [show (1 / 2 : ℝ) = 2 + (-(3 / 2)) by norm_num, Real.rpow_add hb]
    exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hb.le _)
  calc ‖paperFT k τ‖ * |muq κ q τ|
      ≤ ‖paperFT k τ‖ * (K₂ * (1 + |τ|) ^ (1 / 2 : ℝ)) := by gcongr
    _ ≤ ‖paperFT k τ‖ * (K₂ * (2 * (1 + τ ^ 2) * (1 + |τ|) ^ (-(3 / 2) : ℝ))) := by gcongr
    _ = (‖paperFT k τ‖ * (1 + τ ^ 2)) * (2 * K₂ * (1 + |τ|) ^ (-(3 / 2) : ℝ)) := by ring
    _ ≤ K₁ * (2 * K₂ * (1 + |τ|) ^ (-(3 / 2) : ℝ)) := by
        gcongr
    _ = 2 * K₁ * K₂ * (1 + |τ|) ^ (-(3 / 2) : ℝ) := by ring
/-- **Bridge** (App-A-for-χ, mirror of Zeta23.EF.explicitFormulaPaper_of_lit): the literature form
plus the χ-Γ facts give the paper form H-EF(χ).  [Proof: transplant of the ζ-case chain with
ν_{X,χ} = μ_χ + P_{X,χ}; side-integrabilities via the Bridge.lean toolkit (norm_paperFT bounds,
abs_mu-type from GammaFactsChi.stirling) + PXc continuity/boundedness (PXc_abs_le).] -/
theorem explicitFormulaPaperChi_of_lit {κ q : ℕ} {c : ℕ → ℂ} {Z : ZeroConfig}
    (hEF : EF_lit_chi κ q c Z) (hΓq : GammaFactsChi κ q) (hq : 1 ≤ q)
    (_hc : CoeffOK q c) :
    ExplicitFormulaPaperChi κ q c Z := by
  intro L hL f g hf hg hfs hgs
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  have hgc : HasCompactSupport g :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport g) hgs
  have hkd : ContDiff ℝ 2 (Zeta23.EF.weilTest f g) := Zeta23.EF.weilTest_contDiff hf hg.continuous hfc
  have hk : Continuous (Zeta23.EF.weilTest f g) := hkd.continuous
  have hks : tsupport (Zeta23.EF.weilTest f g) ⊆ Icc (-L) L :=
    Zeta23.EF.tsupport_weilTest_subset hfs hgs
  have hkcs : HasCompactSupport (Zeta23.EF.weilTest f g) :=
    Zeta23.EF.weilTest_hasCompactSupport hfc hgc
  have hFk : Integrable (FourierTransform.fourier (Zeta23.EF.weilTest f g)) :=
    Zeta23.EF.integrable_fourier_of_contDiff_two hkd hkcs
  have hμ : Integrable (fun τ : ℝ => paperFT (Zeta23.EF.weilTest f g) τ * (muq κ q τ : ℂ)) :=
    integrable_paperFT_mul_muq hkd hkcs hΓq hq
  obtain ⟨hsum, heq⟩ := hEF (Zeta23.EF.weilTest f g) hkd hkcs
  have hfac : ∀ z : ℂ, paperFT (Zeta23.EF.weilTest f g) z
      = paperFT f z * (starRingEnd ℂ) (paperFT g ((starRingEnd ℂ) z)) :=
    Zeta23.EF.paperFT_weilTest hf.continuous hg.continuous hfc hgc
  have hterm : (fun ρ : Z.carrier => (Z.mult ρ : ℂ) * paperFT (Zeta23.EF.weilTest f g) (gammaOf ρ))
      = fun ρ : Z.carrier => Z.Wsummand f g ρ := by
    ext ρ
    simp only [ZeroConfig.Wsummand, hfac, mul_assoc]
  have hreal : (fun τ : ℝ => paperFT (Zeta23.EF.weilTest f g) τ * (nuXc κ q c (Real.exp L) τ : ℂ))
      = fun τ : ℝ => paperFT f τ * (starRingEnd ℂ) (paperFT g τ) * (nuXc κ q c (Real.exp L) τ : ℂ) := by
    ext τ
    rw [hfac, Complex.conj_ofReal]
  have hnuint : Integrable (fun τ : ℝ => paperFT (Zeta23.EF.weilTest f g) τ
      * (nuXc κ q c (Real.exp L) τ : ℂ)) := by
    refine ((hμ.add (integrable_paperFT_mul_PXc (k := Zeta23.EF.weilTest f g) c L hFk)).congr
      (Filter.Eventually.of_forall fun τ => ?_))
    simp only [Pi.add_apply, nuXc]
    push_cast
    ring
  refine ⟨hterm ▸ hsum, hreal ▸ hnuint, ?_⟩
  rw [literatureRHSchi_eq_integral_nu hq hL hk hks hFk hμ, hreal] at heq
  rw [← heq, ZeroConfig.W, ← hterm]

end ThmE
end Zeta23
