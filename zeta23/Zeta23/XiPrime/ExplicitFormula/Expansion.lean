/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ExplicitFormula/Expansion.lean — the logarithmic derivative of ξ′ on the line Re s = 5/4.
 [XF′ §2]:
 * E := ξ′/ξ = L − A  (Lfn + ζ′/ζ;  A = −ζ′/ζ = LSeries Λ,  B := −A′ = LSeries (Λ·log));
 * Lemma 2.1:  ξ″/ξ′ = E + E′/E,  E′ = L′ + B;
 * FREEZING in closed form: replacing L by a constant Λ⋆ and L′ by 0 in E′/E = (L′+B)/(L−A) gives
   B/(Λ⋆ − A) ( = Σ_j Λ⋆^{−(j+1)} B A^j = Σ_N C_J(N;Λ⋆) N^{−s}, see LSeries_xiCoeffJ ),
   with the EXACT identity  (L′+B)/(L−A) − B/(Λ⋆−A) = L′/(L−A) + B(Λ⋆−L)/((L−A)(Λ⋆−A))
   and hence  ‖·‖ ≤ ‖L′‖/(‖L‖−A₀) + B₀‖L−Λ⋆‖/((‖L‖−A₀)(‖Λ⋆‖−A₀))  (no series on this side);
 * line estimates at σ = 5/4:  ‖A‖ ≤ A₀, ‖B‖ ≤ B₀,  Re L(5/4+it) ≥ ½log|t| − C,
   ‖L′(5/4+it)‖ ≤ C/|t|,  ‖L(5/4+it) − L⋆(τ)‖ ≤ C(|t−τ|+1)/min(t,τ)  (Stirling: GammaFacts).
-/
import Zeta23.XiPrime.ExplicitFormula
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet

open scoped BigOperators ArithmeticFunction ComplexConjugate
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Zeta23
namespace XiPrime

/-! ## 1. E, A, B -/

/-- E := ξ′/ξ = L + ζ′/ζ (meaningful on Re s > 1, where ζ ≠ 0). -/
def Efn (s : ℂ) : ℂ := Lfn s + logDeriv riemannZeta s

/-- A := Σ Λ(n) n^{−s} = −ζ′/ζ. -/
def Afn (s : ℂ) : ℂ := LSeries (fun n => ((Λ n : ℝ) : ℂ)) s

/-- B := Σ Λ(n) log n · n^{−s} = −A′. -/
def Bfn (s : ℂ) : ℂ := LSeries (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) s

theorem one_lt_re_of {s : ℂ} (hs : 1 < s.re) : s ≠ 1 ∧ s ≠ 0 ∧ 0 < s.re ∧ riemannZeta s ≠ 0 :=
  ⟨fun h => by rw [h] at hs; simp at hs, fun h => by rw [h] at hs; simp at hs; linarith,
    by linarith, riemannZeta_ne_zero_of_one_lt_re hs⟩

theorem logDeriv_zeta_eq_neg_Afn {s : ℂ} (hs : 1 < s.re) : logDeriv riemannZeta s = -Afn s := by
  have h2 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  unfold Afn
  rw [logDeriv, Pi.div_apply, h2]
  ring

theorem Efn_eq (s : ℂ) (hs : 1 < s.re) : Efn s = Lfn s - Afn s := by
  rw [Efn, logDeriv_zeta_eq_neg_Afn hs]; ring

/-- the open half-plane Re s > 1. -/
theorem isOpen_one_lt_re : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re

/-- abscissa of absolute convergence of Λ is ≤ 1. -/
theorem abscissa_vonMangoldt_le_one :
    LSeries.abscissaOfAbsConv (fun n => ((Λ n : ℝ) : ℂ)) ≤ 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy)

/-- the B-coefficients are logMul of the A-coefficients. -/
theorem logMul_vonMangoldt :
    LSeries.logMul (fun n => ((Λ n : ℝ) : ℂ)) = fun n => ((Λ n * Real.log n : ℝ) : ℂ) := by
  funext n
  simp only [LSeries.logMul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Complex.ofReal_mul, Complex.ofReal_log (Nat.cast_nonneg n), Complex.ofReal_natCast]
    ring

theorem hasDerivAt_Afn {s : ℂ} (hs : 1 < s.re) : HasDerivAt Afn (-Bfn s) s := by
  have h : LSeries.abscissaOfAbsConv (fun n => ((Λ n : ℝ) : ℂ)) < s.re :=
    lt_of_le_of_lt abscissa_vonMangoldt_le_one (by exact_mod_cast hs)
  have := LSeries_hasDerivAt h
  rw [logMul_vonMangoldt] at this
  exact this

theorem differentiableAt_Afn {s : ℂ} (hs : 1 < s.re) : DifferentiableAt ℂ Afn s :=
  (hasDerivAt_Afn hs).differentiableAt

theorem deriv_Afn {s : ℂ} (hs : 1 < s.re) : deriv Afn s = -Bfn s := (hasDerivAt_Afn hs).deriv

/-- B is absolutely summable on Re s > 1. -/
theorem summable_Bfn {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) s := by
  have h : LSeries.abscissaOfAbsConv (fun n => ((Λ n : ℝ) : ℂ)) < s.re :=
    lt_of_le_of_lt abscissa_vonMangoldt_le_one (by exact_mod_cast hs)
  have := LSeriesSummable_logMul_of_lt_re h
  rwa [logMul_vonMangoldt] at this

/-- L is differentiable on Re s > 0 away from 0 and 1 (here: Re s > 1). -/
theorem differentiableAt_Lfn {s : ℂ} (hs : 1 < s.re) : DifferentiableAt ℂ Lfn s := by
  obtain ⟨hs1, hs0, hpos, -⟩ := one_lt_re_of hs
  unfold Lfn
  have hA := Zeta23.WeilEF.analyticAt_Gammaℝ hpos
  have hG : DifferentiableAt ℂ (logDeriv Complex.Gammaℝ) s := by
    have : logDeriv Complex.Gammaℝ = fun z => deriv Gammaℝ z / Gammaℝ z := by
      funext z; rw [logDeriv_apply]
    rw [this]
    exact hA.deriv.differentiableAt.div hA.differentiableAt (Gammaℝ_ne_zero_of_re_pos hpos)
  refine (hG.add ?_).add ?_
  · exact (differentiableAt_const _).div differentiableAt_id hs0
  · exact (differentiableAt_const _).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1)

/-- logDeriv ζ is differentiable on Re s > 1 with derivative B (= −A′). -/
theorem hasDerivAt_logDeriv_zeta {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (logDeriv riemannZeta) (Bfn s) s := by
  have hev : logDeriv riemannZeta =ᶠ[𝓝 s] fun z => -Afn z := by
    filter_upwards [isOpen_one_lt_re.mem_nhds hs] with z hz
    exact logDeriv_zeta_eq_neg_Afn hz
  have h := (hasDerivAt_Afn hs).neg
  simp only [neg_neg] at h
  exact h.congr_of_eventuallyEq hev

theorem differentiableAt_Efn {s : ℂ} (hs : 1 < s.re) : DifferentiableAt ℂ Efn s :=
  (differentiableAt_Lfn hs).add (hasDerivAt_logDeriv_zeta hs).differentiableAt

theorem deriv_Efn {s : ℂ} (hs : 1 < s.re) : deriv Efn s = deriv Lfn s + Bfn s := by
  have h : HasDerivAt Efn (deriv Lfn s + Bfn s) s :=
    (differentiableAt_Lfn hs).hasDerivAt.add (hasDerivAt_logDeriv_zeta hs)
  exact h.deriv

/-- ξ′ = ξ · E on Re s > 1 (Seam.xiDeriv_eq_xi_mul). -/
theorem xiDeriv_eq_xi_mul_Efn {s : ℂ} (hs : 1 < s.re) : xiDeriv s = xi s * Efn s := by
  obtain ⟨hs1, -, hpos, hζ⟩ := one_lt_re_of hs
  exact xiDeriv_eq_xi_mul hpos hs1 hζ

theorem xi_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : xi s ≠ 0 := by
  obtain ⟨hs1, -, hpos, hζ⟩ := one_lt_re_of hs
  exact xi_ne_zero_of_re_pos hpos hs1 hζ

/-- E(s) ≠ 0 wherever ξ′(s) ≠ 0 (Re s > 1). -/
theorem Efn_ne_zero {s : ℂ} (hs : 1 < s.re) (hne : xiDeriv s ≠ 0) : Efn s ≠ 0 := by
  intro h
  apply hne
  rw [xiDeriv_eq_xi_mul_Efn hs, h, mul_zero]

/-- **[XF′ Lemma 2.1]**  ξ″/ξ′ = E + E′/E on Re s > 1 wherever ξ′ ≠ 0. -/
theorem logDeriv_xiDeriv_eq_Efn {s : ℂ} (hs : 1 < s.re) (hne : xiDeriv s ≠ 0) :
    logDeriv xiDeriv s = Efn s + deriv Efn s / Efn s := by
  obtain ⟨hs1, -, hpos, hζ⟩ := one_lt_re_of hs
  have hev : xiDeriv =ᶠ[𝓝 s] fun z => xi z * Efn z := by
    filter_upwards [isOpen_one_lt_re.mem_nhds hs] with z hz
    exact xiDeriv_eq_xi_mul_Efn hz
  have hxi : xi s ≠ 0 := xi_ne_zero_of_one_lt_re hs
  have hE : Efn s ≠ 0 := Efn_ne_zero hs hne
  have e1 : logDeriv xiDeriv s = logDeriv (fun z => xi z * Efn z) s := by
    simp only [logDeriv_apply, hev.deriv_eq, hev.self_of_nhds]
  rw [e1, logDeriv_mul (f := xi) (g := Efn) s hxi hE (xi_differentiable s) (differentiableAt_Efn hs)]
  rw [logDeriv_xi_eq hpos hs1 hζ, logDeriv_apply]
  rfl

theorem logDeriv_xiDeriv_eq_E {s : ℂ} (hs : 1 < s.re) (hne : xiDeriv s ≠ 0) :
    logDeriv xiDeriv s = (Lfn s + logDeriv riemannZeta s)
      + deriv (fun w => Lfn w + logDeriv riemannZeta w) s / (Lfn s + logDeriv riemannZeta s) :=
  logDeriv_xiDeriv_eq_Efn hs hne

/-! ## 2. Freezing, in closed form (pure algebra) -/

/-- the exact freezing identity. -/
theorem freeze_identity {L L' A B Λs : ℂ} (hLA : L - A ≠ 0) (hΛA : Λs - A ≠ 0) :
    (L' + B) / (L - A) - B / (Λs - A) = L' / (L - A) + B * (Λs - L) / ((L - A) * (Λs - A)) := by
  field_simp
  ring

theorem norm_sub_ge_of_le {L A : ℂ} {A₀ : ℝ} (hA : ‖A‖ ≤ A₀) : ‖L‖ - A₀ ≤ ‖L - A‖ := by
  have := norm_sub_norm_le L A
  have h2 : ‖L‖ - ‖A‖ ≤ ‖L - A‖ := by
    have := abs_norm_sub_norm_le L A
    rw [abs_le] at this
    linarith [this.1, norm_sub_rev L A]
  linarith

/-- **the freezing bound**: for ‖A‖ ≤ A₀ < min(‖L‖, ‖Λ⋆‖) and ‖B‖ ≤ B₀,
‖(L′+B)/(L−A) − B/(Λ⋆−A)‖ ≤ ‖L′‖/(‖L‖−A₀) + B₀‖L−Λ⋆‖/((‖L‖−A₀)(‖Λ⋆‖−A₀)). -/
theorem freeze_bound {L L' A B Λs : ℂ} {A₀ B₀ : ℝ} (hA : ‖A‖ ≤ A₀) (hB : ‖B‖ ≤ B₀)
    (hL : A₀ < ‖L‖) (hΛ : A₀ < ‖Λs‖) :
    ‖(L' + B) / (L - A) - B / (Λs - A)‖
      ≤ ‖L'‖ / (‖L‖ - A₀) + B₀ * ‖L - Λs‖ / ((‖L‖ - A₀) * (‖Λs‖ - A₀)) := by
  have h1 : ‖L‖ - A₀ ≤ ‖L - A‖ := norm_sub_ge_of_le hA
  have h2 : ‖Λs‖ - A₀ ≤ ‖Λs - A‖ := norm_sub_ge_of_le hA
  have hp1 : 0 < ‖L‖ - A₀ := by linarith
  have hp2 : 0 < ‖Λs‖ - A₀ := by linarith
  have hLA : L - A ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hp1 h1)
  have hΛA : Λs - A ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hp2 h2)
  have hB0 : 0 ≤ B₀ := le_trans (norm_nonneg _) hB
  rw [freeze_identity hLA hΛA]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hp1 h1
  · rw [norm_div, norm_mul, norm_mul, norm_sub_rev Λs L]
    have hden : (‖L‖ - A₀) * (‖Λs‖ - A₀) ≤ ‖L - A‖ * ‖Λs - A‖ :=
      mul_le_mul h1 h2 hp2.le (norm_nonneg _)
    calc ‖B‖ * ‖L - Λs‖ / (‖L - A‖ * ‖Λs - A‖)
        ≤ B₀ * ‖L - Λs‖ / (‖L - A‖ * ‖Λs - A‖) := by
          gcongr
    _ ≤ B₀ * ‖L - Λs‖ / ((‖L‖ - A₀) * (‖Λs‖ - A₀)) := by
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden

/-- E′/E in the (L′+B)/(L−A) form, on Re s > 1. -/
theorem deriv_Efn_div_Efn_eq {s : ℂ} (hs : 1 < s.re) :
    deriv Efn s / Efn s = (deriv Lfn s + Bfn s) / (Lfn s - Afn s) := by
  rw [deriv_Efn hs, Efn_eq s hs]

/-! ## 3. Uniform bounds for A and B on the line Re s = 5/4 -/

theorem re_54 (t : ℝ) : (((5/4 : ℝ) : ℂ) + t * I).re = 5/4 := by simp
theorem one_lt_re_54 (t : ℝ) : 1 < (((5/4 : ℝ) : ℂ) + t * I).re := by rw [re_54]; norm_num

theorem norm_Afn_le : ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ t : ℝ, ‖Afn (((5/4 : ℝ) : ℂ) + t * I)‖ ≤ A₀ := by
  obtain ⟨M, hM0, hM⟩ := Zeta23.WeilEF.norm_logDeriv_zeta_le_of_one_lt_re (c := 5/4) (by norm_num)
  refine ⟨M, hM0, fun t => ?_⟩
  have h := hM t
  rw [logDeriv_zeta_eq_neg_Afn (one_lt_re_54 t), norm_neg] at h
  exact h

theorem norm_Bfn_le : ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ t : ℝ, ‖Bfn (((5/4 : ℝ) : ℂ) + t * I)‖ ≤ B₀ := by
  have hsum : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) (((5/4:ℝ):ℂ)) n‖) :=
    summable_norm_iff.mpr (summable_Bfn (s := ((5/4:ℝ):ℂ)) (by simp; norm_num))
  refine ⟨∑' n : ℕ, ‖LSeries.term (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) (((5/4:ℝ):ℂ)) n‖,
    tsum_nonneg fun _ => norm_nonneg _, fun t => ?_⟩
  have hnorm : ∀ n : ℕ, ‖LSeries.term (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) (((5/4:ℝ):ℂ) + t * I) n‖
      = ‖LSeries.term (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) (((5/4:ℝ):ℂ)) n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, re_54, Complex.ofReal_re]
  unfold Bfn LSeries
  calc ‖∑' n, LSeries.term (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) (((5/4:ℝ):ℂ) + t * I) n‖
      ≤ ∑' n, ‖LSeries.term (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) (((5/4:ℝ):ℂ) + t * I) n‖ :=
        norm_tsum_le_tsum_norm (by simp_rw [hnorm]; exact hsum)
    _ = _ := by simp_rw [hnorm]

/-! ## 4. L on the line Re s = 5/4 (Stirling via Zeta23.GammaFacts) -/

section line
open Real in
/-- the complex logarithm near the positive imaginary axis:
‖log(5/8 + i t/2) − (log(t/2) + iπ/2)‖ ≤ 4/t for t ≥ 2. -/
theorem norm_log_w_sub_le {t : ℝ} (ht : 2 ≤ t) :
    ‖Complex.log (((5/8:ℝ):ℂ) + ((t/2:ℝ):ℂ) * I)
        - (((Real.log (t/2) : ℝ) : ℂ) + ((Real.pi/2 : ℝ) : ℂ) * I)‖ ≤ 4 / t := by
  set w : ℂ := ((5/8:ℝ):ℂ) + ((t/2:ℝ):ℂ) * I with hw
  have hwre : w.re = 5/8 := by simp [hw]
  have hwim : w.im = t/2 := by simp [hw]
  have ht0 : 0 < t := by linarith
  have ht2 : 0 < t/2 := by linarith
  have hnorm_sq : ‖w‖ ^ 2 = (5/8)^2 + (t/2)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hwre, hwim]; ring
  have hnorm_ge : t/2 ≤ ‖w‖ := by
    have := Complex.abs_im_le_norm w
    rw [hwim, abs_of_pos ht2] at this
    exact this
  have hnorm_pos : 0 < ‖w‖ := lt_of_lt_of_le ht2 hnorm_ge
  have hnorm_le : ‖w‖ ≤ 5/8 + t/2 := by
    calc ‖w‖ ≤ ‖((5/8:ℝ):ℂ)‖ + ‖((t/2:ℝ):ℂ) * I‖ := norm_add_le _ _
      _ = 5/8 + t/2 := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 5/8),
            abs_of_pos ht2]
  -- the difference, componentwise
  have hre : (Complex.log w - (((Real.log (t/2) : ℝ) : ℂ) + ((Real.pi/2 : ℝ) : ℂ) * I)).re
      = Real.log ‖w‖ - Real.log (t/2) := by
    simp [Complex.log_re]
  have him : (Complex.log w - (((Real.log (t/2) : ℝ) : ℂ) + ((Real.pi/2 : ℝ) : ℂ) * I)).im
      = Complex.arg w - Real.pi/2 := by
    simp [Complex.log_im]
  -- real part: 0 ≤ log‖w‖ − log(t/2) ≤ 5/(4t)
  have hre_bd : |Real.log ‖w‖ - Real.log (t/2)| ≤ 5 / (4 * t) := by
    have h1 : 0 ≤ Real.log ‖w‖ - Real.log (t/2) := by
      have := Real.log_le_log ht2 hnorm_ge
      linarith
    rw [abs_of_nonneg h1, ← Real.log_div hnorm_pos.ne' ht2.ne']
    have h2 : Real.log (‖w‖ / (t/2)) ≤ ‖w‖ / (t/2) - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : ‖w‖ / (t/2) - 1 ≤ 5 / (4 * t) := by
      have : ‖w‖ / (t/2) ≤ (5/8 + t/2) / (t/2) := div_le_div_of_nonneg_right hnorm_le ht2.le
      have e : (5/8 + t/2) / (t/2) = 5 / (4 * t) + 1 := by field_simp; ring
      linarith
    exact h2.trans h3
  -- imaginary part: 0 ≤ π/2 − arg w ≤ 5/(2t)
  have him_bd : |Complex.arg w - Real.pi/2| ≤ 5 / (2 * t) := by
    have harg : Complex.arg w = Real.arcsin (w.im / ‖w‖) :=
      Complex.arg_of_re_nonneg (by rw [hwre]; norm_num)
    set u : ℝ := w.im / ‖w‖ with hu
    have hu0 : 0 ≤ u := by rw [hu, hwim]; positivity
    have hu1 : u ≤ 1 := by
      rw [hu, div_le_one hnorm_pos, hwim]; exact hnorm_ge
    set v : ℝ := Real.pi/2 - Real.arcsin u with hv
    have hv0 : 0 ≤ v := by
      have := Real.arcsin_le_pi_div_two u
      rw [hv]; linarith
    have hv1 : v ≤ Real.pi/2 := by
      have : 0 ≤ Real.arcsin u := Real.arcsin_nonneg.mpr hu0
      rw [hv]; linarith
    have hsinv : Real.sin v = Real.sqrt (1 - u ^ 2) := by
      rw [hv, ← Real.arccos_eq_pi_div_two_sub_arcsin, Real.sin_arccos]
    have hsqrt : Real.sqrt (1 - u ^ 2) = (5/8) / ‖w‖ := by
      have e : 1 - u ^ 2 = ((5/8) / ‖w‖) ^ 2 := by
        rw [hu, hwim, div_pow, div_pow]
        field_simp
        nlinarith [hnorm_sq]
      rw [e, Real.sqrt_sq (by positivity)]
    have hjordan : 2 / Real.pi * v ≤ Real.sin v := Real.mul_le_sin hv0 hv1
    have hvle : v ≤ Real.pi / 2 * ((5/8) / ‖w‖) := by
      rw [hsinv, hsqrt] at hjordan
      have hπ := Real.pi_pos
      have : v = Real.pi / 2 * (2 / Real.pi * v) := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hjordan (by positivity)
    have hfin : Real.pi / 2 * ((5/8) / ‖w‖) ≤ 5 / (2 * t) := by
      have hπ4 : Real.pi ≤ 4 := Real.pi_le_four
      have h1 : (5/8) / ‖w‖ ≤ (5/8) / (t/2) := div_le_div_of_nonneg_left (by norm_num) ht2 hnorm_ge
      calc Real.pi / 2 * ((5/8) / ‖w‖) ≤ 4 / 2 * ((5/8) / (t/2)) := by
            exact mul_le_mul (by linarith) h1 (by positivity) (by norm_num)
        _ = 5 / (2 * t) := by field_simp; ring
    rw [harg, show Real.arcsin u - Real.pi / 2 = -v by rw [hv]; ring, abs_neg, abs_of_nonneg hv0]
    exact hvle.trans hfin
  -- combine
  calc ‖Complex.log w - (((Real.log (t/2) : ℝ) : ℂ) + ((Real.pi/2 : ℝ) : ℂ) * I)‖
      ≤ |(Complex.log w - (((Real.log (t/2) : ℝ) : ℂ) + ((Real.pi/2 : ℝ) : ℂ) * I)).re|
        + |(Complex.log w - (((Real.log (t/2) : ℝ) : ℂ) + ((Real.pi/2 : ℝ) : ℂ) * I)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 5 / (4 * t) + 5 / (2 * t) := by rw [hre, him]; exact add_le_add hre_bd him_bd
    _ = 15 / (4 * t) := by field_simp; ring
    _ ≤ 4 / t := by
        rw [div_le_div_iff₀ (by positivity) ht0]
        nlinarith

theorem s54_eq (t : ℝ) : ((5/4:ℝ):ℂ) + t * I = ((5/4:ℝ):ℂ) + ((t:ℝ):ℂ) * I := rfl

theorem half_s54 (t : ℝ) : (((5/4:ℝ):ℂ) + t * I) / 2 = ((5/8:ℝ):ℂ) + ((t/2:ℝ):ℂ) * I := by
  push_cast; ring

theorem norm_s54_ge (t : ℝ) : |t| ≤ ‖((5/4:ℝ):ℂ) + t * I‖ := by
  have := Complex.abs_im_le_norm (((5/4:ℝ):ℂ) + t * I)
  simpa using this

theorem norm_s54_sub_one_ge (t : ℝ) : |t| ≤ ‖((5/4:ℝ):ℂ) + t * I - 1‖ := by
  have := Complex.abs_im_le_norm (((5/4:ℝ):ℂ) + t * I - 1)
  simpa using this

theorem norm_inv_le_of_le {z : ℂ} {a : ℝ} (ha : 0 < a) (h : a ≤ ‖z‖) : ‖z⁻¹‖ ≤ a⁻¹ := by
  rw [norm_inv]; exact inv_anti₀ ha h

/-- **one-point Stirling for L**: ‖L(5/4+it) − L⋆(t)‖ ≤ 8/t for t ≥ 2,
L⋆(t) = ½log(t/2π) + iπ/4 (Defs.Lstar). -/
theorem norm_Lfn_sub_Lstar_self_le {t : ℝ} (ht : 2 ≤ t) :
    ‖Lfn (((5/4:ℝ):ℂ) + t * I) - Lstar t‖ ≤ 8 / t := by
  have ht0 : 0 < t := by linarith
  set s : ℂ := ((5/4:ℝ):ℂ) + t * I with hs
  set w : ℂ := ((5/8:ℝ):ℂ) + ((t/2:ℝ):ℂ) * I with hw
  have hsw : s / 2 = w := half_s54 t
  have hspos : 0 < s.re := by rw [hs, re_54]; norm_num
  have hwre : 0 < w.re := by simp [hw]
  have hwim : 1/2 ≤ |w.im| := by
    simp only [hw, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_zero, mul_one, zero_add, add_zero]
    rw [abs_of_pos (by linarith)]; linarith
  have hwim' : w.im = t/2 := by simp [hw]
  -- Stirling for ψ(w)
  have hstir := Zeta23.StirlingVert.digamma_stirling hwre hwim
  have hstir' : ‖Complex.digamma w - Complex.log w + (1/2 : ℂ) / w‖ ≤ 6 / t := by
    refine hstir.trans ?_
    rw [hwim', div_le_div_iff₀ (by positivity) ht0]
    nlinarith
  have hlog := norm_log_w_sub_le ht
  -- elementary reciprocals
  have hs_inv : ‖s⁻¹‖ ≤ t⁻¹ := norm_inv_le_of_le ht0 (by
    have := norm_s54_ge t; rwa [abs_of_pos ht0] at this)
  have hs1_inv : ‖(s - 1)⁻¹‖ ≤ t⁻¹ := norm_inv_le_of_le ht0 (by
    have := norm_s54_sub_one_ge t; rwa [abs_of_pos ht0] at this)
  have hw_inv : ‖w⁻¹‖ ≤ (t/2)⁻¹ := norm_inv_le_of_le (by positivity) (by
    have := Complex.abs_im_le_norm w; rwa [hwim', abs_of_pos (by positivity)] at this)
  -- the algebraic decomposition
  have hL : Lfn s = -(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma w + 1 / s + 1 / (s - 1) := by
    rw [Lfn_eq_digamma hspos, hsw]
  have hLstar : Lstar t = ((Real.log (t / (2 * Real.pi)) / 2 : ℝ) : ℂ) + Complex.I * (Real.pi / 4 : ℝ) := rfl
  have hlogid : ((Real.log (t / (2 * Real.pi)) / 2 : ℝ) : ℂ) + Complex.I * (Real.pi / 4 : ℝ)
      = (1/2 : ℂ) * (((Real.log (t/2) : ℝ) : ℂ) + ((Real.pi/2 : ℝ) : ℂ) * I)
        - (Real.log Real.pi : ℂ) / 2 := by
    have e1 : Real.log (t / (2 * Real.pi)) = Real.log (t/2) - Real.log Real.pi := by
      rw [show t / (2 * Real.pi) = (t/2) / Real.pi by ring,
        Real.log_div (by positivity) Real.pi_pos.ne']
    rw [e1]
    push_cast
    ring
  have key : Lfn s - Lstar t
      = (1/2 : ℂ) * (Complex.digamma w - Complex.log w + (1/2 : ℂ) / w)
        + (1/2 : ℂ) * (Complex.log w - (((Real.log (t/2) : ℝ) : ℂ) + ((Real.pi/2 : ℝ) : ℂ) * I))
        + (-(1/4 : ℂ) * w⁻¹ + s⁻¹ + (s - 1)⁻¹) := by
    rw [hL, hLstar, hlogid]
    simp only [one_div]
    ring
  rw [key]
  have hI3 : ‖-(1/4 : ℂ) * w⁻¹ + s⁻¹ + (s - 1)⁻¹‖ ≤ (1/4) * (t/2)⁻¹ + t⁻¹ + t⁻¹ := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ hs_inv)) hs1_inv)
    rw [norm_mul, norm_neg]
    have : ‖(1/4 : ℂ)‖ = 1/4 := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left hw_inv (by norm_num)
  calc ‖(1/2 : ℂ) * (Complex.digamma w - Complex.log w + (1/2 : ℂ) / w)
        + (1/2 : ℂ) * (Complex.log w - (((Real.log (t/2) : ℝ) : ℂ) + ((Real.pi/2 : ℝ) : ℂ) * I))
        + (-(1/4 : ℂ) * w⁻¹ + s⁻¹ + (s - 1)⁻¹)‖
      ≤ ‖(1/2 : ℂ) * (Complex.digamma w - Complex.log w + (1/2 : ℂ) / w)‖
        + ‖(1/2 : ℂ) * (Complex.log w - (((Real.log (t/2) : ℝ) : ℂ) + ((Real.pi/2 : ℝ) : ℂ) * I))‖
        + ‖-(1/4 : ℂ) * w⁻¹ + s⁻¹ + (s - 1)⁻¹‖ := norm_add₃_le
    _ ≤ (1/2) * (6 / t) + (1/2) * (4 / t) + ((1/4) * (t/2)⁻¹ + t⁻¹ + t⁻¹) := by
        refine add_le_add (add_le_add ?_ ?_) hI3
        · rw [norm_mul, show ‖(1/2:ℂ)‖ = 1/2 by norm_num]
          exact mul_le_mul_of_nonneg_left hstir' (by norm_num)
        · rw [norm_mul, show ‖(1/2:ℂ)‖ = 1/2 by norm_num]
          exact mul_le_mul_of_nonneg_left hlog (by norm_num)
    _ = (15/2) / t := by field_simp; ring
    _ ≤ 8 / t := by rw [div_le_div_iff₀ ht0 ht0]; nlinarith

/-- ordered case of |log t − log τ| ≤ |t − τ| / min t τ. -/
theorem log_sub_log_le_of_le {t τ : ℝ} (hτ : 0 < τ) (h : τ ≤ t) :
    Real.log t - Real.log τ ≤ (t - τ) / τ := by
  have ht : 0 < t := lt_of_lt_of_le hτ h
  rw [← Real.log_div ht.ne' hτ.ne']
  have h1 := Real.log_le_sub_one_of_pos (show 0 < t/τ by positivity)
  have e : t / τ - 1 = (t - τ) / τ := by field_simp
  linarith

theorem abs_log_sub_log_le {t τ : ℝ} (ht : 0 < t) (hτ : 0 < τ) :
    |Real.log t - Real.log τ| ≤ |t - τ| / min t τ := by
  rcases le_total τ t with h | h
  · have hlog : Real.log τ ≤ Real.log t := Real.log_le_log hτ h
    rw [min_eq_right h, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact log_sub_log_le_of_le hτ h
  · have hlog : Real.log t ≤ Real.log τ := Real.log_le_log ht h
    rw [min_eq_left h, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), neg_sub, neg_sub]
    exact log_sub_log_le_of_le ht h

/-- ‖L⋆(t) − L⋆(τ)‖ = ½|log t − log τ| ≤ |t−τ|/(2 min t τ). -/
theorem norm_Lstar_sub_Lstar_le {t τ : ℝ} (ht : 0 < t) (hτ : 0 < τ) :
    ‖Lstar t - Lstar τ‖ ≤ |t - τ| / (2 * min t τ) := by
  have e : Lstar t - Lstar τ = (((Real.log t - Real.log τ) / 2 : ℝ) : ℂ) := by
    unfold Lstar
    have e1 : Real.log (t / (2 * Real.pi)) - Real.log (τ / (2 * Real.pi)) = Real.log t - Real.log τ := by
      rw [Real.log_div ht.ne' (by positivity), Real.log_div hτ.ne' (by positivity)]; ring
    have : (((Real.log (t / (2 * Real.pi)) / 2 : ℝ)) : ℂ) - ((Real.log (τ / (2 * Real.pi)) / 2 : ℝ) : ℂ)
        = (((Real.log t - Real.log τ) / 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sub]; congr 1; rw [← e1]; ring
    rw [← this]; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
  have := abs_log_sub_log_le ht hτ
  have hm : 0 < min t τ := lt_min ht hτ
  rw [div_le_div_iff₀ two_pos (by positivity)]
  calc |Real.log t - Real.log τ| * (2 * min t τ) = 2 * (|Real.log t - Real.log τ| * min t τ) := by ring
    _ ≤ 2 * |t - τ| := by
        have := (le_div_iff₀ hm).mp this
        linarith
    _ = |t - τ| * 2 := by ring

/-- **L against a frozen L⋆(τ)**: ‖L(5/4+it) − L⋆(τ)‖ ≤ (|t−τ| + 16)/(2 min t τ) for t, τ ≥ 2. -/
theorem norm_Lfn_sub_Lstar_le {t τ : ℝ} (ht : 2 ≤ t) (hτ : 2 ≤ τ) :
    ‖Lfn (((5/4:ℝ):ℂ) + t * I) - Lstar τ‖ ≤ (|t - τ| + 16) / (2 * min t τ) := by
  have ht0 : 0 < t := by linarith
  have hτ0 : 0 < τ := by linarith
  have hm : 0 < min t τ := lt_min ht0 hτ0
  have h1 := norm_Lfn_sub_Lstar_self_le ht
  have h2 := norm_Lstar_sub_Lstar_le ht0 hτ0
  calc ‖Lfn (((5/4:ℝ):ℂ) + t * I) - Lstar τ‖
      ≤ ‖Lfn (((5/4:ℝ):ℂ) + t * I) - Lstar t‖ + ‖Lstar t - Lstar τ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 8 / t + |t - τ| / (2 * min t τ) := add_le_add h1 h2
    _ ≤ 16 / (2 * min t τ) + |t - τ| / (2 * min t τ) := by
        have : 8 / t ≤ 16 / (2 * min t τ) := by
          rw [div_le_div_iff₀ ht0 (by positivity)]
          nlinarith [min_le_left t τ]
        linarith
    _ = (|t - τ| + 16) / (2 * min t τ) := by ring

/-- ‖L⋆(τ)‖ ≥ ½ log(τ/2π). -/
theorem norm_Lstar_ge (τ : ℝ) : Real.log (τ / (2 * Real.pi)) / 2 ≤ ‖Lstar τ‖ := by
  have := Complex.abs_re_le_norm (Lstar τ)
  have hre : (Lstar τ).re = Real.log (τ / (2 * Real.pi)) / 2 := by
    simp [Lstar]
  rw [hre] at this
  exact (le_abs_self _).trans this

/-- ‖L(5/4+it)‖ ≥ ½ log(t/2π) − 8/t for t ≥ 2. -/
theorem norm_Lfn_ge {t : ℝ} (ht : 2 ≤ t) :
    Real.log (t / (2 * Real.pi)) / 2 - 8 / t ≤ ‖Lfn (((5/4:ℝ):ℂ) + t * I)‖ := by
  have h1 := norm_Lfn_sub_Lstar_self_le ht
  have h2 := norm_Lstar_ge t
  have h3 := norm_sub_norm_le (Lstar t) (Lfn (((5/4:ℝ):ℂ) + t * I))
  rw [norm_sub_rev] at h3
  linarith

end line

/-! ## 5. L′ on the line, conjugation symmetry, and the uniform bound for E′/E -/

section deriv_conj

theorem norm_sub₃_le' {a b c : ℂ} : ‖a - b - c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  calc ‖a - b - c‖ ≤ ‖a - b‖ + ‖c‖ := norm_sub_le _ _
    _ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by linarith [norm_sub_le a b]

/-- the digamma form of L (the right side of Seam.Lfn_eq_digamma), for differentiation. -/
def LfnD (s : ℂ) : ℂ :=
  -(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (s / 2) + 1 / s + 1 / (s - 1)

theorem isOpen_re_pos : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re

theorem Lfn_eventuallyEq_LfnD {s : ℂ} (hs : 0 < s.re) : Lfn =ᶠ[𝓝 s] LfnD := by
  filter_upwards [isOpen_re_pos.mem_nhds hs] with z hz
  exact Lfn_eq_digamma hz

theorem mem_integerComplement_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    z ∈ Complex.integerComplement := by
  rintro ⟨n, rfl⟩
  simp at hz

theorem hasDerivAt_LfnD {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsi : (s / 2).im ≠ 0) :
    HasDerivAt LfnD
      ((1 / 4 : ℂ) * deriv Complex.digamma (s / 2) - (s ^ 2)⁻¹ - ((s - 1) ^ 2)⁻¹) s := by
  have hmem := mem_integerComplement_of_im_ne_zero hsi
  have hψ : HasDerivAt (fun z => Complex.digamma (z / 2)) (deriv Complex.digamma (s / 2) * (1 / 2)) s := by
    have h1 := (Zeta23.Stirling.differentiableAt_digamma hmem).hasDerivAt
    have h2 : HasDerivAt (fun z : ℂ => z / 2) (1 / 2) s := by
      simpa using (hasDerivAt_id s).div_const (2:ℂ)
    exact h1.comp s h2
  have hinv : HasDerivAt (fun z : ℂ => 1 / z) (-(s ^ 2)⁻¹) s := by
    simpa [one_div] using hasDerivAt_inv hs0
  have hinv1 : HasDerivAt (fun z : ℂ => 1 / (z - 1)) (-((s - 1) ^ 2)⁻¹) s := by
    have h := (hasDerivAt_inv (sub_ne_zero.mpr hs1)).comp s ((hasDerivAt_id s).sub_const 1)
    simpa [one_div, Function.comp_def] using h
  have := (((hasDerivAt_const s (-(Real.log Real.pi : ℂ) / 2)).add (hψ.const_mul (1/2 : ℂ))).add hinv).add hinv1
  exact this.congr_deriv (by ring)

theorem deriv_Lfn_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hsi : s.im ≠ 0) :
    deriv Lfn s = (1 / 4 : ℂ) * deriv Complex.digamma (s / 2) - (s ^ 2)⁻¹ - ((s - 1) ^ 2)⁻¹ := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have hsi' : (s / 2).im ≠ 0 := by
    rw [Complex.div_ofNat_im]; exact div_ne_zero hsi two_ne_zero
  rw [(Lfn_eventuallyEq_LfnD hs).deriv_eq]
  exact (hasDerivAt_LfnD hs0 hs1 hsi').deriv

/-- ‖ψ′(w)‖ ≤ 1/Im(w)² + 2/|Im w| for Re w > 0, |Im w| ≥ 1/2 (trigamma series + Zeta23.StirlingVert). -/
theorem norm_deriv_digamma_le {w : ℂ} (hw : 0 < w.re) (hwi : 1 / 2 ≤ |w.im|) :
    ‖deriv Complex.digamma w‖ ≤ 1 / w.im ^ 2 + 2 / |w.im| := by
  have hwi0 : w.im ≠ 0 := by
    intro h; rw [h, abs_zero] at hwi; norm_num at hwi
  have hmem := mem_integerComplement_of_im_ne_zero hwi0
  have hsum := Zeta23.Stirling.hasSum_trigamma hmem
  -- summability of the norms
  have hshift : ∀ n : ℕ, ‖1 / (w + ((n + 1 : ℕ) : ℂ)) ^ 2‖ = 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 := by
    intro n
    rw [norm_div, norm_one, norm_pow]
    congr 2
    push_cast; ring_nf
  have hs1 : Summable (fun n : ℕ => 1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := Zeta23.StirlingVert.summable_inv_norm_sq hw
  have hsn : Summable (fun n : ℕ => ‖1 / (w + (n : ℂ)) ^ 2‖) := by
    rw [← summable_nat_add_iff 1]
    exact hs1.congr fun n => (hshift n).symm
  rw [← hsum.tsum_eq]
  calc ‖∑' n : ℕ, 1 / (w + (n : ℂ)) ^ 2‖ ≤ ∑' n : ℕ, ‖1 / (w + (n : ℂ)) ^ 2‖ := norm_tsum_le_tsum_norm hsn
    _ = ‖1 / (w + ((0:ℕ) : ℂ)) ^ 2‖ + ∑' n : ℕ, ‖1 / (w + ((n + 1 : ℕ) : ℂ)) ^ 2‖ := hsn.tsum_eq_zero_add
    _ = 1 / ‖w‖ ^ 2 + ∑' n : ℕ, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 := by
        congr 1
        · simp [norm_pow]
        · exact tsum_congr hshift
    _ ≤ 1 / w.im ^ 2 + 2 / |w.im| := by
        refine add_le_add ?_ (Zeta23.StirlingVert.tsum_inv_norm_sq_le hw hwi)
        have h1 : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
        have h2 : w.im ^ 2 ≤ ‖w‖ ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        exact div_le_div_of_nonneg_left zero_le_one (by positivity) h2

/-- **L′ on the line**: ‖L′(5/4+it)‖ ≤ 3/|t| for |t| ≥ 2. -/
theorem norm_deriv_Lfn_le {t : ℝ} (ht : 2 ≤ |t|) :
    ‖deriv Lfn (((5/4:ℝ):ℂ) + t * I)‖ ≤ 3 / |t| := by
  set s : ℂ := ((5/4:ℝ):ℂ) + t * I with hs
  have ht0 : 0 < |t| := by linarith
  have htne : t ≠ 0 := abs_pos.mp ht0
  have hsre : s.re = 5/4 := re_54 t
  have hsim : s.im = t := by simp [hs]
  have hs1 : s ≠ 1 := fun h => by rw [h] at hsim; simp at hsim; exact htne hsim.symm
  rw [deriv_Lfn_eq (by rw [hsre]; norm_num) hs1 (by rwa [hsim])]
  have hw : 0 < (s/2).re := by rw [Complex.div_ofNat_re, hsre]; norm_num
  have hwim : (s/2).im = t/2 := by rw [Complex.div_ofNat_im, hsim]
  have hwi : 1/2 ≤ |(s/2).im| := by
    rw [hwim, abs_div, abs_two]; linarith
  have hψ := norm_deriv_digamma_le hw hwi
  rw [hwim, abs_div, abs_two] at hψ
  have hs_inv : ‖(s ^ 2)⁻¹‖ ≤ (|t| ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg t) (norm_s54_ge t) 2)
  have hs1_inv : ‖((s - 1) ^ 2)⁻¹‖ ≤ (|t| ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg t) (norm_s54_sub_one_ge t) 2)
  have htt : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  calc ‖(1 / 4 : ℂ) * deriv Complex.digamma (s / 2) - (s ^ 2)⁻¹ - ((s - 1) ^ 2)⁻¹‖
      ≤ ‖(1 / 4 : ℂ) * deriv Complex.digamma (s / 2)‖ + ‖(s ^ 2)⁻¹‖ + ‖((s - 1) ^ 2)⁻¹‖ := norm_sub₃_le'
    _ ≤ (1/4) * (1 / (t/2) ^ 2 + 2 / (|t| / 2)) + (|t| ^ 2)⁻¹ + (|t| ^ 2)⁻¹ := by
        refine add_le_add (add_le_add ?_ hs_inv) hs1_inv
        rw [norm_mul, show ‖(1/4:ℂ)‖ = 1/4 by norm_num]
        exact mul_le_mul_of_nonneg_left hψ (by norm_num)
    _ = 3 / |t| ^ 2 + 1 / |t| := by
        have e : (t / 2) ^ 2 = |t| ^ 2 / 4 := by rw [div_pow, htt]; norm_num
        rw [e]; field_simp; ring
    _ ≤ 3 / |t| := by
        rw [div_add_div _ _ (by positivity) ht0.ne', div_le_div_iff₀ (by positivity) ht0]
        nlinarith

end deriv_conj

/-! ## 6. Conjugation symmetry on the line -/

section symmetry

theorem logDeriv_xi_conj (s : ℂ) : logDeriv xi (conj s) = conj (logDeriv xi s) := by
  rw [logDeriv_apply, logDeriv_apply, show deriv xi = xiDeriv from rfl, xiDeriv_conj, xi_conj,
    map_div₀]

theorem Efn_eq_logDeriv_xi {s : ℂ} (hs : 1 < s.re) : Efn s = logDeriv xi s := by
  obtain ⟨hs1, -, hpos, hζ⟩ := one_lt_re_of hs
  exact (logDeriv_xi_eq hpos hs1 hζ).symm

theorem conj_re_gt {s : ℂ} (hs : 1 < s.re) : 1 < (conj s).re := by rwa [Complex.conj_re]

theorem Efn_conj {s : ℂ} (hs : 1 < s.re) : Efn (conj s) = conj (Efn s) := by
  rw [Efn_eq_logDeriv_xi hs, Efn_eq_logDeriv_xi (conj_re_gt hs), logDeriv_xi_conj]

/-- E′/E = ξ″/ξ′ − E (Lemma 2.1 rearranged). -/
theorem derivE_div_E_eq {s : ℂ} (hs : 1 < s.re) (hne : xiDeriv s ≠ 0) :
    deriv Efn s / Efn s = logDeriv xiDeriv s - Efn s := by
  rw [logDeriv_xiDeriv_eq_Efn hs hne]; ring

theorem xiDeriv_conj_ne_zero {s : ℂ} (hne : xiDeriv s ≠ 0) : xiDeriv (conj s) ≠ 0 := by
  rw [xiDeriv_conj]; exact (map_ne_zero _).mpr hne

theorem derivE_div_E_conj {s : ℂ} (hs : 1 < s.re) (hne : xiDeriv s ≠ 0) :
    deriv Efn (conj s) / Efn (conj s) = conj (deriv Efn s / Efn s) := by
  rw [derivE_div_E_eq (conj_re_gt hs) (xiDeriv_conj_ne_zero hne), derivE_div_E_eq hs hne,
    logDeriv_xiDeriv_conj, Efn_conj hs, map_sub]

/-- an L-series with REAL coefficients is conjugation-equivariant. -/
theorem LSeries_real_conj (a : ℕ → ℝ) (s : ℂ) :
    LSeries (fun n => ((a n : ℝ) : ℂ)) (conj s) = conj (LSeries (fun n => ((a n : ℝ) : ℂ)) s) := by
  unfold LSeries
  rw [Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀, Complex.conj_ofReal]
    congr 1
    have harg : ((n : ℂ)).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]; exact Ne.symm Real.pi_ne_zero
    have h := Complex.cpow_conj (n : ℂ) s harg
    rwa [Complex.conj_natCast] at h

theorem Afn_conj (s : ℂ) : Afn (conj s) = conj (Afn s) := LSeries_real_conj _ s
theorem Bfn_conj (s : ℂ) : Bfn (conj s) = conj (Bfn s) := LSeries_real_conj _ s

/-- the frozen object B/(Λ⋆ − A) is conjugation-equivariant in (Λ⋆, s). -/
theorem frozen_conj (Λs s : ℂ) :
    Bfn (conj s) / (conj Λs - Afn (conj s)) = conj (Bfn s / (Λs - Afn s)) := by
  rw [Bfn_conj, Afn_conj, map_div₀, map_sub]

theorem conj_s54 (t : ℝ) : conj (((5/4:ℝ):ℂ) + t * I) = ((5/4:ℝ):ℂ) + (-t:ℝ) * I := by
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

end symmetry

/-! ## G. The generic line layer: archimedean line data (c, Λ, Λ⋆)  [XF′ §2 / §9.1 in one statement]

Everything the explicit formulas need on a line Re s = c about E := Λ + ζ′/ζ (ξ′: Λ = L, E = ξ′/ξ; W: Λ = L₂,
E = E₂ = W/ζ) follows from five Stirling-type facts about Λ and the frozen-parameter map Λ⋆ = Lpar, packaged as
ArchLineData, plus the single per-object input  hE : ∀ t, E(c+it) ≠ 0.  Instances: §7 below (Λ = Lfn, Lpar = Lstar,
c = 5/4) and Hardy/EFExpansion.lean (Λ = L2, Lpar = L2star, 9/8 ≤ c ≤ 5/4). -/

section generic

theorem log_two_pi_le_two : Real.log (2 * Real.pi) ≤ 2 := by
  have h1 : 2 * Real.pi ≤ Real.exp 2 := by
    have := Real.pi_lt_d2; have := Real.exp_one_gt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  calc Real.log (2 * Real.pi) ≤ Real.log (Real.exp 2) := Real.log_le_log (by positivity) h1
    _ = 2 := Real.log_exp 2

theorem log_four_le_two : Real.log 4 ≤ 2 := by
  have h1 : (4:ℝ) ≤ Real.exp 2 := by
    have := Real.exp_one_gt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  calc Real.log 4 ≤ Real.log (Real.exp 2) := Real.log_le_log (by positivity) h1
    _ = 2 := Real.log_exp 2

/-- E_Λ := Λ + ζ′/ζ. (Efn = EofL Lfn and E2fn = EofL L2, by rfl.) -/
def EofL (Λf : ℂ → ℂ) (s : ℂ) : ℂ := Λf s + logDeriv riemannZeta s

/-- **archimedean line data** for (c, Λ, Λ⋆). -/
structure ArchLineData (c : ℝ) (Λf : ℂ → ℂ) (Lpar : ℝ → ℂ) : Prop where
  one_lt : 1 < c
  le : c ≤ 3 / 2
  analytic : ∀ t : ℝ, AnalyticAt ℂ Λf ((c:ℂ) + t * I)
  conj_symm : ∀ z : ℂ, 1 < z.re → z.im ≠ 0 → Λf (conj z) = conj (Λf z)
  two_pt : ∃ C : ℝ, ∀ t τ : ℝ, 2 ≤ t → 2 ≤ τ → ‖Λf ((c:ℂ) + t * I) - Lpar τ‖ ≤ C * (|t - τ| + 1) / min t τ
  deriv_le : ∃ C : ℝ, ∀ t : ℝ, 2 ≤ t → ‖deriv Λf ((c:ℂ) + t * I)‖ ≤ C / t
  lower : ∃ C : ℝ, ∀ t : ℝ, 2 ≤ t → Real.log t / 2 - C ≤ ‖Λf ((c:ℂ) + t * I)‖
  lower_par : ∃ C : ℝ, ∀ τ : ℝ, 2 ≤ τ → Real.log τ / 2 - C ≤ ‖Lpar τ‖
  upper : ∃ M : ℝ, ∀ t : ℝ, ‖Λf ((c:ℂ) + t * I)‖ ≤ M * Real.log (2 + |t|)

variable {c : ℝ} {Λf : ℂ → ℂ} {Lpar : ℝ → ℂ}

theorem re_lineC (c t : ℝ) : ((c:ℂ) + t * I).re = c := by simp
theorem im_lineC (c t : ℝ) : ((c:ℂ) + t * I).im = t := by simp
theorem continuous_lineC (c : ℝ) : Continuous (fun t : ℝ => (c:ℂ) + t * I) := by fun_prop
theorem conj_lineC' (c t : ℝ) : conj ((c:ℂ) + t * I) = (c:ℂ) + (-t:ℝ) * I := by
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring

/-- A is bounded on Re s = c > 1. -/
theorem norm_Afn_le_at (hc : 1 < c) : ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ t : ℝ, ‖Afn ((c:ℂ) + t * I)‖ ≤ A₀ := by
  obtain ⟨M, hM0, hM⟩ := Zeta23.WeilEF.norm_logDeriv_zeta_le_of_one_lt_re (c := c) hc
  refine ⟨M, hM0, fun t => ?_⟩
  have h := hM t
  rw [logDeriv_zeta_eq_neg_Afn (by rw [re_lineC]; exact hc), norm_neg] at h
  exact h

/-- B is bounded on Re s = c > 1. -/
theorem norm_Bfn_le_at (hc : 1 < c) : ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ t : ℝ, ‖Bfn ((c:ℂ) + t * I)‖ ≤ B₀ := by
  have hsum : Summable (fun n : ℕ => ‖LSeries.term (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) (c:ℂ) n‖) :=
    summable_norm_iff.mpr (summable_Bfn (s := (c:ℂ)) (by simpa using hc))
  refine ⟨∑' n : ℕ, ‖LSeries.term (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) (c:ℂ) n‖,
    tsum_nonneg fun _ => norm_nonneg _, fun t => ?_⟩
  have hnorm : ∀ n : ℕ, ‖LSeries.term (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) ((c:ℂ) + t * I) n‖
      = ‖LSeries.term (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) (c:ℂ) n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, re_lineC, Complex.ofReal_re]
  unfold Bfn LSeries
  calc ‖∑' n, LSeries.term (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) ((c:ℂ) + t * I) n‖
      ≤ ∑' n, ‖LSeries.term (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) ((c:ℂ) + t * I) n‖ :=
        norm_tsum_le_tsum_norm (by simp_rw [hnorm]; exact hsum)
    _ = _ := by simp_rw [hnorm]

theorem EofL_eq_sub {s : ℂ} (hs : 1 < s.re) : EofL Λf s = Λf s - Afn s := by
  rw [EofL, logDeriv_zeta_eq_neg_Afn hs]; ring

/-- ζ′/ζ is analytic on Re s > 1. -/
theorem analyticAt_logDeriv_zeta {s : ℂ} (hs : 1 < s.re) : AnalyticAt ℂ (logDeriv riemannZeta) s := by
  have hd : DifferentiableOn ℂ (logDeriv riemannZeta) {s : ℂ | 1 < s.re} :=
    fun z hz => (hasDerivAt_logDeriv_zeta hz).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (isOpen_one_lt_re.mem_nhds hs)

theorem ArchLineData.analyticAt_E (h : ArchLineData c Λf Lpar) (t : ℝ) :
    AnalyticAt ℂ (EofL Λf) ((c:ℂ) + t * I) := by
  have e : EofL Λf = fun z => Λf z + logDeriv riemannZeta z := rfl
  rw [e]
  exact (h.analytic t).add (analyticAt_logDeriv_zeta (by rw [re_lineC]; exact h.one_lt))

theorem ArchLineData.deriv_E (h : ArchLineData c Λf Lpar) (t : ℝ) :
    deriv (EofL Λf) ((c:ℂ) + t * I) = deriv Λf ((c:ℂ) + t * I) + Bfn ((c:ℂ) + t * I) := by
  have hd : HasDerivAt (EofL Λf) (deriv Λf ((c:ℂ) + t * I) + Bfn ((c:ℂ) + t * I)) ((c:ℂ) + t * I) :=
    (h.analytic t).differentiableAt.hasDerivAt.add (hasDerivAt_logDeriv_zeta (by rw [re_lineC]; exact h.one_lt))
  exact hd.deriv

theorem ArchLineData.derivE_div_E_eq (h : ArchLineData c Λf Lpar) (t : ℝ) :
    deriv (EofL Λf) ((c:ℂ) + t * I) / EofL Λf ((c:ℂ) + t * I)
      = (deriv Λf ((c:ℂ) + t * I) + Bfn ((c:ℂ) + t * I)) / (Λf ((c:ℂ) + t * I) - Afn ((c:ℂ) + t * I)) := by
  rw [h.deriv_E, EofL_eq_sub (by rw [re_lineC]; exact h.one_lt)]

/-- continuity along the line of E, E′, and of E′/E where E ≠ 0. -/
theorem ArchLineData.continuous_E_line (h : ArchLineData c Λf Lpar) :
    Continuous (fun t : ℝ => EofL Λf ((c:ℂ) + t * I)) :=
  continuous_iff_continuousAt.mpr fun t =>
    ((h.analyticAt_E t).continuousAt).comp_of_eq (continuous_lineC c).continuousAt rfl

theorem ArchLineData.continuous_derivE_line (h : ArchLineData c Λf Lpar) :
    Continuous (fun t : ℝ => deriv (EofL Λf) ((c:ℂ) + t * I)) :=
  continuous_iff_continuousAt.mpr fun t =>
    ((h.analyticAt_E t).deriv.continuousAt).comp_of_eq (continuous_lineC c).continuousAt rfl

theorem ArchLineData.continuous_derivE_div_E_line (h : ArchLineData c Λf Lpar)
    (hE : ∀ t : ℝ, EofL Λf ((c:ℂ) + t * I) ≠ 0) :
    Continuous (fun t : ℝ => deriv (EofL Λf) ((c:ℂ) + t * I) / EofL Λf ((c:ℂ) + t * I)) :=
  h.continuous_derivE_line.div h.continuous_E_line hE

/-- conjugation symmetry of E off the real axis on Re s > 1. -/
theorem ArchLineData.E_conj (h : ArchLineData c Λf Lpar) {z : ℂ} (hz : 1 < z.re) (hzi : z.im ≠ 0) :
    EofL Λf (conj z) = conj (EofL Λf z) := by
  rw [EofL, EofL, h.conj_symm z hz hzi, logDeriv_zeta_eq_neg_Afn hz, logDeriv_zeta_eq_neg_Afn (conj_re_gt hz),
    Afn_conj, map_add, map_neg]

/-- the derivative inherits the conjugation symmetry (E analytic on the open set {Re > 1, Im ≠ 0}). -/
theorem ArchLineData.derivE_conj (h : ArchLineData c Λf Lpar) {t : ℝ} (ht : t ≠ 0) :
    deriv (EofL Λf) (conj ((c:ℂ) + t * I)) = conj (deriv (EofL Λf) ((c:ℂ) + t * I)) := by
  set s : ℂ := (c:ℂ) + t * I with hs
  have hA := h.analyticAt_E t
  rw [← hs] at hA
  have h1 : HasDerivAt (fun z => conj (EofL Λf (conj z))) (conj (deriv (EofL Λf) s)) (conj s) :=
    hA.differentiableAt.hasDerivAt.conj_conj
  have hopen : IsOpen {z : ℂ | 1 < z.re ∧ z.im ≠ 0} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_ne_fun Complex.continuous_im continuous_const)
  have hmem : conj s ∈ {z : ℂ | 1 < z.re ∧ z.im ≠ 0} := by
    refine ⟨?_, ?_⟩
    · rw [Complex.conj_re, hs, re_lineC]; exact h.one_lt
    · rw [Complex.conj_im, hs, im_lineC]; exact neg_ne_zero.mpr ht
  have hev : (fun z => conj (EofL Λf (conj z))) =ᶠ[𝓝 (conj s)] EofL Λf := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    rw [h.E_conj hz.1 hz.2, Complex.conj_conj]
  exact (h1.congr_of_eventuallyEq hev.symm).deriv

theorem ArchLineData.derivE_div_E_conj (h : ArchLineData c Λf Lpar) {t : ℝ} (ht : t ≠ 0) :
    deriv (EofL Λf) ((c:ℂ) + (-t:ℝ) * I) / EofL Λf ((c:ℂ) + (-t:ℝ) * I)
      = conj (deriv (EofL Λf) ((c:ℂ) + t * I) / EofL Λf ((c:ℂ) + t * I)) := by
  rw [← conj_lineC', h.derivE_conj ht, h.E_conj (by rw [re_lineC]; exact h.one_lt) (by rw [im_lineC]; exact ht),
    map_div₀]

theorem ArchLineData.norm_Λ_neg (h : ArchLineData c Λf Lpar) (t : ℝ) (ht : t ≠ 0) :
    ‖Λf ((c:ℂ) + (-t:ℝ) * I)‖ = ‖Λf ((c:ℂ) + t * I)‖ := by
  rw [← conj_lineC', h.conj_symm _ (by rw [re_lineC]; exact h.one_lt) (by rw [im_lineC]; exact ht), Complex.norm_conj]

/-- **the uniform bound for E′/E on the line**, given E ≠ 0 there. -/
theorem ArchLineData.derivE_div_E_uniform (h : ArchLineData c Λf Lpar)
    (hE : ∀ t : ℝ, EofL Λf ((c:ℂ) + t * I) ≠ 0) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ t : ℝ, ‖deriv (EofL Λf) ((c:ℂ) + t * I) / EofL Λf ((c:ℂ) + t * I)‖ ≤ CE := by
  obtain ⟨A₀, hA0, hA⟩ := norm_Afn_le_at h.one_lt
  obtain ⟨B₀, hB0, hB⟩ := norm_Bfn_le_at h.one_lt
  obtain ⟨C₁, hlow⟩ := h.lower
  obtain ⟨C₂, hder⟩ := h.deriv_le
  -- large t
  set t₀ : ℝ := max 2 (Real.exp (2 * (A₀ + |C₁| + 1))) with ht₀
  have ht₀2 : 2 ≤ t₀ := le_max_left _ _
  have hC₂' : ∀ t : ℝ, 2 ≤ t → ‖deriv Λf ((c:ℂ) + t * I)‖ ≤ |C₂| / 2 := fun t ht =>
    (hder t ht).trans ((div_le_div_of_nonneg_right (le_abs_self C₂) (by linarith)).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) ht))
  have hlarge : ∀ t : ℝ, t₀ ≤ t →
      ‖deriv (EofL Λf) ((c:ℂ) + t * I) / EofL Λf ((c:ℂ) + t * I)‖ ≤ |C₂| / 2 + B₀ := by
    intro t ht
    have ht2 : 2 ≤ t := le_trans ht₀2 ht
    have ht0 : 0 < t := by linarith
    have hlog : 2 * (A₀ + |C₁| + 1) ≤ Real.log t := by
      have := Real.log_le_log (Real.exp_pos _) (le_trans (le_max_right _ _) ht)
      rwa [Real.log_exp] at this
    have hL : A₀ + 1 ≤ ‖Λf ((c:ℂ) + t * I)‖ := by
      have := hlow t ht2; have := le_abs_self C₁; linarith
    rw [h.derivE_div_E_eq, norm_div]
    have hden : 1 ≤ ‖Λf ((c:ℂ) + ↑t * I) - Afn ((c:ℂ) + ↑t * I)‖ := by
      have := norm_sub_ge_of_le (L := Λf ((c:ℂ) + ↑t * I)) (hA t); linarith
    have hnum : ‖deriv Λf ((c:ℂ) + ↑t * I) + Bfn ((c:ℂ) + ↑t * I)‖ ≤ |C₂| / 2 + B₀ :=
      (norm_add_le _ _).trans (add_le_add (hC₂' t ht2) (hB t))
    calc _ ≤ ‖deriv Λf ((c:ℂ) + ↑t * I) + Bfn ((c:ℂ) + ↑t * I)‖ / 1 :=
          div_le_div_of_nonneg_left (norm_nonneg _) one_pos hden
      _ ≤ |C₂| / 2 + B₀ := by rw [div_one]; exact hnum
  -- large negative t by conjugation
  have hneg : ∀ t : ℝ, t₀ ≤ -t →
      ‖deriv (EofL Λf) ((c:ℂ) + t * I) / EofL Λf ((c:ℂ) + t * I)‖ ≤ |C₂| / 2 + B₀ := by
    intro t ht
    have hh := hlarge (-t) ht
    have htne : -t ≠ 0 := by intro h0; rw [h0] at ht; linarith
    have := h.derivE_div_E_conj (t := -t) htne
    simp only [neg_neg] at this
    rw [show ((c:ℂ) + t * I) = ((c:ℂ) + ((t:ℝ):ℂ) * I) from rfl, this, Complex.norm_conj]
    exact hh
  -- compact middle
  have hcont := h.continuous_derivE_div_E_line hE
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -t₀) (b := t₀)).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max M (|C₂| / 2 + B₀), le_max_of_le_right (by positivity), fun t => ?_⟩
  rcases le_or_gt t₀ t with h1 | h1
  · exact (hlarge t h1).trans (le_max_right _ _)
  rcases le_or_gt t₀ (-t) with h2 | h2
  · exact (hneg t h2).trans (le_max_right _ _)
  · exact (hM t ⟨by linarith, h1.le⟩).trans (le_max_left _ _)

/-- **the freezing estimate on the line**: for T ≥ T₀, τ ≥ T, t ≥ T/4,
‖E′/E(c+it) − B(c+it)/(Λ⋆(τ) − A(c+it))‖ ≤ C (|t − τ| + 1)/(T log T). -/
theorem ArchLineData.freeze_on_line (h : ArchLineData c Λf Lpar) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ τ t : ℝ, T ≤ τ → T / 4 ≤ t →
      ‖deriv (EofL Λf) ((c:ℂ) + t * I) / EofL Λf ((c:ℂ) + t * I)
          - Bfn ((c:ℂ) + t * I) / (Lpar τ - Afn ((c:ℂ) + t * I))‖
        ≤ C * (|t - τ| + 1) / (T * Real.log T) := by
  obtain ⟨A₀, hA0, hA⟩ := norm_Afn_le_at h.one_lt
  obtain ⟨B₀, hB0, hB⟩ := norm_Bfn_le_at h.one_lt
  obtain ⟨C₁, hlow⟩ := h.lower
  obtain ⟨C₂, hder⟩ := h.deriv_le
  obtain ⟨C₃, htwo⟩ := h.two_pt
  obtain ⟨C₄, hlowp⟩ := h.lower_par
  set K : ℝ := A₀ + |C₁| + |C₄| + 2 with hK
  refine ⟨16 * |C₂| + 64 * B₀ * |C₃|, max 8 (Real.exp (4 * K)), by positivity, le_max_left _ _, ?_⟩
  intro T hT τ t hτ ht
  have hT8 : 8 ≤ T := le_trans (le_max_left _ _) hT
  have hT0 : 0 < T := by linarith
  have ht2 : 2 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hτ2 : 2 ≤ τ := by linarith
  have hlogT : 4 * K ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos _) (le_trans (le_max_right _ _) hT)
    rwa [Real.log_exp] at this
  have hKpos : 2 ≤ K := by rw [hK]; have := abs_nonneg C₁; have := abs_nonneg C₄; linarith
  have hlogT1 : 1 ≤ Real.log T := by nlinarith
  have hlogt : Real.log T - 2 ≤ Real.log t := by
    have : Real.log (T/4) ≤ Real.log t := Real.log_le_log (by positivity) ht
    rw [Real.log_div hT0.ne' (by norm_num)] at this
    linarith [log_four_le_two]
  have hlogτ : Real.log T ≤ Real.log τ := Real.log_le_log hT0 hτ
  set s : ℂ := (c:ℂ) + t * I with hs
  -- lower bounds ‖Λ‖ − A₀ ≥ ¼ log T, ‖Λ⋆‖ − A₀ ≥ ¼ log T
  have hL : Real.log T / 4 ≤ ‖Λf s‖ - A₀ := by
    have := hlow t ht2; rw [← hs] at this; have := le_abs_self C₁; have := abs_nonneg C₄; nlinarith
  have hΛ : Real.log T / 4 ≤ ‖Lpar τ‖ - A₀ := by
    have := hlowp τ hτ2; have := le_abs_self C₄; have := abs_nonneg C₁; nlinarith
  have hq : 0 < Real.log T / 4 := by positivity
  have hLpos : A₀ < ‖Λf s‖ := by linarith
  have hΛpos : A₀ < ‖Lpar τ‖ := by linarith
  rw [h.derivE_div_E_eq, ← hs]
  have hfb := freeze_bound (L' := deriv Λf s) (hA t) (hB t) hLpos hΛpos
  rw [← hs] at hfb
  refine hfb.trans ?_
  -- first term
  have h1 : ‖deriv Λf s‖ / (‖Λf s‖ - A₀) ≤ 16 * |C₂| / (T * Real.log T) := by
    have hd : ‖deriv Λf s‖ ≤ |C₂| / t :=
      (hder t ht2).trans (div_le_div_of_nonneg_right (le_abs_self C₂) ht0.le)
    calc ‖deriv Λf s‖ / (‖Λf s‖ - A₀) ≤ (|C₂| / t) / (Real.log T / 4) := div_le_div₀ (by positivity) hd hq hL
      _ = 4 * |C₂| / (t * Real.log T) := by field_simp
      _ ≤ 16 * |C₂| / (T * Real.log T) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have : 0 ≤ |C₂| * Real.log T := by positivity
          nlinarith
  -- second term
  have h2 : B₀ * ‖Λf s - Lpar τ‖ / ((‖Λf s‖ - A₀) * (‖Lpar τ‖ - A₀))
      ≤ 64 * B₀ * |C₃| * (|t - τ| + 1) / (T * Real.log T) := by
    have hd : ‖Λf s - Lpar τ‖ ≤ |C₃| * (|t - τ| + 1) / min t τ := by
      refine (htwo t τ ht2 hτ2).trans ?_
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
        (le_min ht0.le (by linarith))
    have hmin : T / 4 ≤ min t τ := le_min ht (by linarith)
    have hden : (Real.log T / 4) * (Real.log T / 4) ≤ (‖Λf s‖ - A₀) * (‖Lpar τ‖ - A₀) :=
      mul_le_mul hL hΛ hq.le (by linarith)
    calc B₀ * ‖Λf s - Lpar τ‖ / ((‖Λf s‖ - A₀) * (‖Lpar τ‖ - A₀))
        ≤ B₀ * (|C₃| * (|t - τ| + 1) / min t τ) / ((Real.log T / 4) * (Real.log T / 4)) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hd hB0) (by positivity) hden
      _ ≤ B₀ * (|C₃| * (|t - τ| + 1) / (T / 4)) / ((Real.log T / 4) * (Real.log T / 4)) := by gcongr
      _ = 64 * B₀ * |C₃| * (|t - τ| + 1) / (T * (Real.log T * Real.log T)) := by field_simp; ring
      _ ≤ 64 * B₀ * |C₃| * (|t - τ| + 1) / (T * Real.log T) := by
          refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
          have : Real.log T ≤ Real.log T * Real.log T := by nlinarith
          exact mul_le_mul_of_nonneg_left this hT0.le
  calc ‖deriv Λf s‖ / (‖Λf s‖ - A₀) + B₀ * ‖Λf s - Lpar τ‖ / ((‖Λf s‖ - A₀) * (‖Lpar τ‖ - A₀))
      ≤ 16 * |C₂| / (T * Real.log T) + 64 * B₀ * |C₃| * (|t - τ| + 1) / (T * Real.log T) := add_le_add h1 h2
    _ ≤ (16 * |C₂| + 64 * B₀ * |C₃|) * (|t - τ| + 1) / (T * Real.log T) := by
        rw [← add_div]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have : 0 ≤ 16 * |C₂| * |t - τ| := by positivity
        nlinarith

/-- the frozen object B/(Λ⋆(τ) − A(c+it)) is uniformly small on the line: ‖B/(Λ⋆(τ) − A(c+it))‖ ≤ 4B₀/log T. -/
theorem ArchLineData.frozen_uniform (h : ArchLineData c Λf Lpar) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ τ t : ℝ, T ≤ τ →
      ‖Bfn ((c:ℂ) + t * I) / (Lpar τ - Afn ((c:ℂ) + t * I))‖ ≤ C / Real.log T := by
  obtain ⟨A₀, hA0, hA⟩ := norm_Afn_le_at h.one_lt
  obtain ⟨B₀, hB0, hB⟩ := norm_Bfn_le_at h.one_lt
  obtain ⟨C₄, hlowp⟩ := h.lower_par
  set K : ℝ := A₀ + |C₄| + 2 with hK
  refine ⟨4 * B₀, max 8 (Real.exp (4 * K)), by positivity, le_max_left _ _, ?_⟩
  intro T hT τ t hτ
  have hT8 : 8 ≤ T := le_trans (le_max_left _ _) hT
  have hT0 : 0 < T := by linarith
  have hτ2 : 2 ≤ τ := by linarith
  have hlogT : 4 * K ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos _) (le_trans (le_max_right _ _) hT)
    rwa [Real.log_exp] at this
  have hlogτ : Real.log T ≤ Real.log τ := Real.log_le_log hT0 hτ
  have hKpos : 2 ≤ K := by rw [hK]; have := abs_nonneg C₄; linarith
  have hΛ : Real.log T / 4 ≤ ‖Lpar τ‖ - A₀ := by
    have := hlowp τ hτ2; have := le_abs_self C₄; nlinarith
  have hq : 0 < Real.log T / 4 := by nlinarith
  have hden : Real.log T / 4 ≤ ‖Lpar τ - Afn ((c:ℂ) + t * I)‖ := hΛ.trans (norm_sub_ge_of_le (hA t))
  rw [norm_div]
  calc ‖Bfn ((c:ℂ) + ↑t * I)‖ / ‖Lpar τ - Afn ((c:ℂ) + ↑t * I)‖
      ≤ B₀ / (Real.log T / 4) := div_le_div₀ hB0 (hB t) hq hden
    _ = 4 * B₀ / Real.log T := by field_simp

/-- ‖E(c+it)‖ ≤ M log(2+|t|). -/
theorem ArchLineData.norm_E_line (h : ArchLineData c Λf Lpar) :
    ∃ M : ℝ, ∀ t : ℝ, ‖EofL Λf ((c:ℂ) + t * I)‖ ≤ M * Real.log (2 + |t|) := by
  obtain ⟨A₀, hA0, hA⟩ := norm_Afn_le_at h.one_lt
  obtain ⟨M, hM⟩ := h.upper
  have hlog2 : (1:ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogpos : ∀ t : ℝ, Real.log 2 ≤ Real.log (2 + |t|) := fun t =>
    Real.log_le_log two_pos (by linarith [abs_nonneg t])
  refine ⟨M + 2 * A₀, fun t => ?_⟩
  rw [EofL_eq_sub (by rw [re_lineC]; exact h.one_lt)]
  calc ‖Λf ((c:ℂ) + t * I) - Afn ((c:ℂ) + t * I)‖
      ≤ ‖Λf ((c:ℂ) + t * I)‖ + ‖Afn ((c:ℂ) + t * I)‖ := norm_sub_le _ _
    _ ≤ M * Real.log (2 + |t|) + A₀ := add_le_add (hM t) (hA t)
    _ ≤ (M + 2 * A₀) * Real.log (2 + |t|) := by nlinarith [hlogpos t]

/-- ‖(E + E′/E)(c+it)‖ ≤ M log(2+|t|), given E ≠ 0 on the line. -/
theorem ArchLineData.norm_E_add_dE_line (h : ArchLineData c Λf Lpar)
    (hE : ∀ t : ℝ, EofL Λf ((c:ℂ) + t * I) ≠ 0) :
    ∃ M : ℝ, ∀ t : ℝ, ‖EofL Λf ((c:ℂ) + t * I) + deriv (EofL Λf) ((c:ℂ) + t * I) / EofL Λf ((c:ℂ) + t * I)‖
      ≤ M * Real.log (2 + |t|) := by
  obtain ⟨M, hM⟩ := h.norm_E_line
  obtain ⟨CE, hCE0, hCE⟩ := h.derivE_div_E_uniform hE
  have hlog2 : (1:ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogpos : ∀ t : ℝ, Real.log 2 ≤ Real.log (2 + |t|) := fun t =>
    Real.log_le_log two_pos (by linarith [abs_nonneg t])
  refine ⟨M + 2 * CE, fun t => ?_⟩
  calc _ ≤ ‖EofL Λf ((c:ℂ) + t * I)‖ + ‖deriv (EofL Λf) ((c:ℂ) + t * I) / EofL Λf ((c:ℂ) + t * I)‖ :=
        norm_add_le _ _
    _ ≤ M * Real.log (2 + |t|) + CE := add_le_add (hM t) (hCE t)
    _ ≤ (M + 2 * CE) * Real.log (2 + |t|) := by nlinarith [hlogpos t]

end generic

/-! ## 7. The ξ′ instance: (c, Λ, Λ⋆) = (5/4, L, L⋆); the uniform bound for E′/E under (F2) and the freezing estimate -/

section uniform

theorem differentiableOn_Efn : DifferentiableOn ℂ Efn {s : ℂ | 1 < s.re} :=
  fun _ hs => (differentiableAt_Efn hs).differentiableWithinAt

theorem analyticAt_Efn {s : ℂ} (hs : 1 < s.re) : AnalyticAt ℂ Efn s :=
  differentiableOn_Efn.analyticAt (isOpen_one_lt_re.mem_nhds hs)

theorem differentiableOn_Lfn : DifferentiableOn ℂ Lfn {s : ℂ | 1 < s.re} :=
  fun _ hs => (differentiableAt_Lfn hs).differentiableWithinAt

theorem analyticAt_Lfn_of_one_lt {s : ℂ} (hs : 1 < s.re) : AnalyticAt ℂ Lfn s :=
  differentiableOn_Lfn.analyticAt (isOpen_one_lt_re.mem_nhds hs)

theorem continuous_line_54 : Continuous (fun t : ℝ => ((5/4:ℝ):ℂ) + t * I) := by fun_prop

theorem xiDeriv_ne_zero_line (hF2 : XiDerivZerosInStrip) (t : ℝ) :
    xiDeriv (((5/4:ℝ):ℂ) + t * I) ≠ 0 := by
  intro h
  have := (hF2 _ h).2
  rw [re_54] at this
  norm_num at this

theorem norm_Lfn_ge' {t : ℝ} (ht : 2 ≤ t) : Real.log t / 2 - 5 ≤ ‖Lfn (((5/4:ℝ):ℂ) + t * I)‖ := by
  have h := norm_Lfn_ge ht
  have ht0 : 0 < t := by linarith
  rw [Real.log_div ht0.ne' (by positivity)] at h
  have : 8 / t ≤ 4 := by rw [div_le_iff₀ ht0]; linarith
  linarith [log_two_pi_le_two]

theorem norm_Lstar_ge' {τ : ℝ} (hτ : 0 < τ) : Real.log τ / 2 - 1 ≤ ‖Lstar τ‖ := by
  have h := norm_Lstar_ge τ
  rw [Real.log_div hτ.ne' (by positivity)] at h
  linarith [log_two_pi_le_two]

/-- L(conj z) = conj L(z) (everywhere; Γℝ and 1/s, 1/(s−1) are real on ℝ). -/
theorem Lfn_conj (z : ℂ) : Lfn (conj z) = conj (Lfn z) := by
  unfold Lfn
  rw [Zeta23.RvM.logDeriv_Gammaℝ_conj, map_add, map_add, map_div₀, map_div₀, map_one, map_sub, map_one]

theorem norm_Lstar_le {τ : ℝ} (hτ : 2 ≤ τ) : ‖Lstar τ‖ ≤ Real.log τ / 2 + 2 := by
  have hτ0 : 0 < τ := by linarith
  unfold Lstar
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < Real.pi / 4), Real.log_div hτ0.ne' (by positivity)]
  have hlogτ : 0 ≤ Real.log τ := Real.log_nonneg (by linarith)
  have h2π : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have : |(Real.log τ - Real.log (2 * Real.pi)) / 2| ≤ Real.log τ / 2 + 1 := by
    rw [abs_le]; constructor <;> linarith [log_two_pi_le_two]
  linarith [Real.pi_lt_d2]

/-- ‖L(5/4+it)‖ ≤ M log(2+|t|) for all t. -/
theorem norm_Lfn_line54 : ∃ M : ℝ, ∀ t : ℝ, ‖Lfn (((5/4:ℝ):ℂ) + t * I)‖ ≤ M * Real.log (2 + |t|) := by
  -- big positive t
  have hbig : ∀ t : ℝ, 2 ≤ t → ‖Lfn (((5/4:ℝ):ℂ) + t * I)‖ ≤ Real.log t / 2 + 6 := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have h1 := norm_Lfn_sub_Lstar_self_le ht
    have h2 := norm_Lstar_le ht
    have : 8 / t ≤ 4 := by rw [div_le_iff₀ ht0]; linarith
    calc ‖Lfn (((5/4:ℝ):ℂ) + t * I)‖ ≤ ‖Lfn (((5/4:ℝ):ℂ) + t * I) - Lstar t‖ + ‖Lstar t‖ := norm_le_norm_sub_add _ _
      _ ≤ 8 / t + (Real.log t / 2 + 2) := add_le_add h1 h2
      _ ≤ Real.log t / 2 + 6 := by linarith
  -- compact middle
  have hcont : Continuous (fun t : ℝ => Lfn (((5/4:ℝ):ℂ) + t * I)) :=
    continuous_iff_continuousAt.mpr fun t =>
      ((analyticAt_Lfn_of_one_lt (one_lt_re_54 t)).continuousAt).comp_of_eq continuous_line_54.continuousAt rfl
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := -(2:ℝ)) (b := 2)).exists_bound_of_continuousOn hcont.continuousOn
  have hM₀0 : 0 ≤ M₀ := le_trans (norm_nonneg _) (hM₀ 0 ⟨by norm_num, by norm_num⟩)
  have hlog2 : (1:ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogpos : ∀ t : ℝ, Real.log 2 ≤ Real.log (2 + |t|) := fun t =>
    Real.log_le_log two_pos (by linarith [abs_nonneg t])
  refine ⟨2 * M₀ + 13, fun t => ?_⟩
  have hlt : Real.log |t| ≤ Real.log (2 + |t|) := by
    rcases eq_or_ne t 0 with rfl | ht
    · simp; exact Real.log_nonneg (by norm_num)
    · exact Real.log_le_log (abs_pos.mpr ht) (by linarith)
  have hl0 : 1 / 2 ≤ Real.log (2 + |t|) := hlog2.trans (hlogpos t)
  have key : ∀ u : ℝ, 2 ≤ u → |t| = u → ‖Lfn (((5/4:ℝ):ℂ) + t * I)‖ ≤ Real.log u / 2 + 6 →
      ‖Lfn (((5/4:ℝ):ℂ) + t * I)‖ ≤ (2 * M₀ + 13) * Real.log (2 + |t|) := by
    intro u hu htu hb
    rw [← htu] at hb
    calc ‖Lfn (((5/4:ℝ):ℂ) + t * I)‖ ≤ Real.log |t| / 2 + 6 := hb
      _ ≤ Real.log (2 + |t|) / 2 + 12 * Real.log (2 + |t|) := by linarith
      _ ≤ (2 * M₀ + 13) * Real.log (2 + |t|) := by nlinarith
  rcases le_or_gt 2 t with h | h
  · exact key t h (abs_of_pos (by linarith)) (hbig t h)
  rcases le_or_gt 2 (-t) with h' | h'
  · have hb := hbig (-t) h'
    rw [show (((5/4:ℝ):ℂ) + ((-t:ℝ):ℂ) * I) = conj (((5/4:ℝ):ℂ) + t * I) by rw [conj_s54], Lfn_conj,
      Complex.norm_conj] at hb
    exact key (-t) h' (abs_of_neg (by linarith)) hb
  · have := hM₀ t ⟨by linarith, h.le⟩
    nlinarith

/-- **the archimedean line data for ξ′**: (c, Λ, Λ⋆) = (5/4, L, L⋆). -/
theorem archLineData_Lfn : ArchLineData (5/4) Lfn Lstar where
  one_lt := by norm_num
  le := by norm_num
  analytic := fun t => analyticAt_Lfn_of_one_lt (one_lt_re_54 t)
  conj_symm := fun z _ _ => Lfn_conj z
  two_pt := ⟨8, fun t τ ht hτ => by
    have h := norm_Lfn_sub_Lstar_le ht hτ
    refine h.trans ?_
    have hm : 0 < min t τ := lt_min (by linarith) (by linarith)
    rw [div_le_div_iff₀ (by positivity) hm]
    nlinarith [abs_nonneg (t - τ)]⟩
  deriv_le := ⟨3, fun t ht => by
    have h := norm_deriv_Lfn_le (t := t) (by rw [abs_of_pos (by linarith)]; exact ht)
    rwa [abs_of_pos (by linarith : (0:ℝ) < t)] at h⟩
  lower := ⟨5, fun t ht => norm_Lfn_ge' ht⟩
  lower_par := ⟨1, fun τ hτ => norm_Lstar_ge' (by linarith)⟩
  upper := norm_Lfn_line54

/-- continuity of t ↦ E′/E(5/4+it) given ξ′ ≠ 0 on the line. -/
theorem continuous_derivE_div_E_line (hne : ∀ t : ℝ, xiDeriv (((5/4:ℝ):ℂ) + t * I) ≠ 0) :
    Continuous (fun t : ℝ => deriv Efn (((5/4:ℝ):ℂ) + t * I) / Efn (((5/4:ℝ):ℂ) + t * I)) :=
  archLineData_Lfn.continuous_derivE_div_E_line fun t => Efn_ne_zero (one_lt_re_54 t) (hne t)

/-- **uniform bound for E′/E on Re s = 5/4 under (F2)** — instance of ArchLineData.derivE_div_E_uniform. -/
theorem derivE_div_E_uniform (hF2 : XiDerivZerosInStrip) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ t : ℝ,
      ‖deriv Efn (((5/4:ℝ):ℂ) + t * I) / Efn (((5/4:ℝ):ℂ) + t * I)‖ ≤ CE :=
  archLineData_Lfn.derivE_div_E_uniform fun t => Efn_ne_zero (one_lt_re_54 t) (xiDeriv_ne_zero_line hF2 t)

/-- **the freezing estimate on the line** [XF′ Lemma 2.4, at σ = 5/4] — instance of ArchLineData.freeze_on_line:
there are C, T₀ such that for T ≥ T₀, τ ≥ T and t ≥ T/4,
‖E′/E(5/4+it) − B(5/4+it)/(L⋆(τ) − A(5/4+it))‖ ≤ C (|t − τ| + 1)/(T log T). -/
theorem freeze_on_line :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ τ t : ℝ, T ≤ τ → T / 4 ≤ t →
      ‖deriv Efn (((5/4:ℝ):ℂ) + t * I) / Efn (((5/4:ℝ):ℂ) + t * I)
          - Bfn (((5/4:ℝ):ℂ) + t * I) / (Lstar τ - Afn (((5/4:ℝ):ℂ) + t * I))‖
        ≤ C * (|t - τ| + 1) / (T * Real.log T) :=
  archLineData_Lfn.freeze_on_line

/-- the frozen object is uniformly small on the line — instance of `ArchLineData.frozen_uniform`. -/
theorem frozen_uniform :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ τ t : ℝ, T ≤ τ →
      ‖Bfn (((5/4:ℝ):ℂ) + t * I) / (Lstar τ - Afn (((5/4:ℝ):ℂ) + t * I))‖ ≤ C / Real.log T :=
  archLineData_Lfn.frozen_uniform

end uniform


end XiPrime
end Zeta23
