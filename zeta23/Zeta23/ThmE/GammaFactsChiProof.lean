/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/GammaFactsChiProof.lean — H-Γ(χ) as a theorem.
The nine fields of `ThmE.GammaFactsChi κ q` for
  μ_χ(τ) := (1/2π)[log(q/π) + Re ψ(1/4 + κ/2 + iτ/2)],   κ ≤ 1, q ≥ 1,
proved from the abscissa-parametrized digamma toolkit (Zeta23/GammaFacts/Mu.lean:
re_digamma_vertical / re_digamma_mono at any a ∈ (0,1)), the complex Stirling theorem for ψ
(Zeta23/GammaFacts/StirlingVert.lean), the trigamma series (Zeta23/Analytic/Stirling.lean) and the
FTC computations of Zeta23/GammaFacts/IntMu.lean re-run with log(qτ/2π) in place of log(τ/2π).
Key remark: in the Stirling field the conductor constant cancels:
  μ_χ(τ) − (1/2π)log(q|τ|/2π) = (1/2π)[Re ψ(a + iτ/2) − log(|τ|/2)],  a := 1/4 + κ/2 ∈ {1/4, 3/4},
so the ζ proof applies verbatim at abscissa a.
-/
import Zeta23.ThmE.Hypotheses
import Zeta23.GammaFacts.Complete
import Zeta23.WeilEF.GammaRBracket
import Zeta23.ThmE.IntMuChi

noncomputable section

namespace Zeta23
namespace ThmE
namespace GammaChi

open Complex MeasureTheory intervalIntegral

variable {κ q : ℕ}

/-- the abscissa `a := 1/4 + κ/2`. -/
def absc (κ : ℕ) : ℝ := 1 / 4 + (κ : ℝ) / 2

theorem absc_pos (κ : ℕ) : 0 < absc κ := by unfold absc; positivity

theorem absc_lt_one (hκ : κ ≤ 1) : absc κ < 1 := by
  unfold absc
  have : (κ : ℝ) ≤ 1 := by exact_mod_cast hκ
  linarith

theorem quarter_le_absc (κ : ℕ) : 1 / 4 ≤ absc κ := by
  unfold absc; have : (0:ℝ) ≤ (κ : ℝ) / 2 := by positivity
  linarith

/-- `μ_χ(τ) = (1/2π)·Re ψ(a + i·τ/2) + (1/2π)·log(q/π)`. -/
theorem muq_eq (κ q : ℕ) (τ : ℝ) :
    muq κ q τ = (1 / (2 * Real.pi))
        * (Complex.digamma (((absc κ : ℝ) : ℂ) + Complex.I * ((τ / 2 : ℝ) : ℂ))).re
      + (1 / (2 * Real.pi)) * Real.log (q / Real.pi) := by
  unfold muq absc
  have e : (1 : ℂ) / 4 + (κ : ℂ) / 2 + Complex.I * τ / 2
      = (((1 / 4 + (κ : ℝ) / 2 : ℝ)) : ℂ) + Complex.I * ((τ / 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [e]; ring

theorem arg_mem (hκ : κ ≤ 1) (t : ℝ) :
    ((absc κ : ℝ) : ℂ) + Complex.I * (t : ℂ) ∈ Complex.integerComplement :=
  MuFields.abscissa_mem (absc_pos κ) (absc_lt_one hκ) t

/-! ### even -/

theorem muq_even (hκ : κ ≤ 1) (τ : ℝ) : muq κ q (-τ) = muq κ q τ := by
  rw [muq_eq, muq_eq]
  congr 2
  have hconj : ((absc κ : ℝ) : ℂ) + Complex.I * (((-τ) / 2 : ℝ) : ℂ)
      = starRingEnd ℂ (((absc κ : ℝ) : ℂ) + Complex.I * ((τ / 2 : ℝ) : ℂ)) := by
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  rw [hconj, Zeta23.WeilEF.digamma_conj (arg_mem hκ _), Complex.conj_re]

/-! ### monotone, minimum at 0 -/

theorem muq_monotoneOn (hκ : κ ≤ 1) : MonotoneOn (muq κ q) (Set.Ici (0 : ℝ)) := by
  intro t₁ h₁ t₂ h₂ h12
  rw [muq_eq, muq_eq]
  have hmono := MuFields.re_digamma_mono (a := absc κ) (absc_pos κ) (absc_lt_one hκ)
    (Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp h₁] : (0 : ℝ) ≤ t₁ / 2))
    (Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp h₂] : (0 : ℝ) ≤ t₂ / 2))
    (by linarith)
  have h2π : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  have := mul_le_mul_of_nonneg_left hmono h2π
  linarith

theorem muq_zero_le (hκ : κ ≤ 1) (τ : ℝ) : muq κ q 0 ≤ muq κ q τ := by
  rcases le_total 0 τ with h | h
  · exact muq_monotoneOn hκ (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h) h
  · rw [← muq_even hκ τ]
    exact muq_monotoneOn hκ (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (by linarith)) (by linarith)

/-! ### Stirling (the conductor constant cancels) -/

/-- Stirling for μ_χ with the explicit, conductor-free constant 20/(2π). -/
theorem muq_stirling_const (hκ : κ ≤ 1) (hq : 1 ≤ q) (τ : ℝ) (hτ : 1 ≤ |τ|) :
    |muq κ q τ - (1 / (2 * Real.pi)) * Real.log (q * |τ| / (2 * Real.pi))|
      ≤ (20 / (2 * Real.pi)) / τ ^ 2 := by
  have hπ := Real.pi_pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hq)
  have ht : 1 / 2 ≤ |τ / 2| := by rw [abs_div, abs_two]; linarith
  have ha1 : absc κ ≤ 1 := (absc_lt_one hκ).le
  have h := Zeta23.StirlingVert.re_digamma_stirling' (a := absc κ) (absc_pos κ) ha1 ht
  have hτ0 : 0 < |τ| := by linarith
  set D : ℝ := (Complex.digamma (((absc κ : ℝ) : ℂ) + Complex.I * ((τ / 2 : ℝ) : ℂ))).re
    - Real.log |τ / 2| with hD
  have hD5 : |D| ≤ 5 / (τ / 2) ^ 2 := h
  have hlogs : Real.log (q * |τ| / (2 * Real.pi))
      = Real.log |τ / 2| + Real.log (q / Real.pi) := by
    rw [abs_div, abs_two, show (q : ℝ) * |τ| / (2 * Real.pi) = (|τ| / 2) * (q / Real.pi) by field_simp,
      Real.log_mul (by positivity) (by positivity)]
  have key : muq κ q τ - (1 / (2 * Real.pi)) * Real.log (q * |τ| / (2 * Real.pi))
      = (1 / (2 * Real.pi)) * D := by
    rw [muq_eq, hlogs, hD]; ring
  rw [key, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * Real.pi))]
  calc 1 / (2 * Real.pi) * |D| ≤ 1 / (2 * Real.pi) * (5 / (τ / 2) ^ 2) := by gcongr
    _ = 20 / (2 * Real.pi) / τ ^ 2 := by field_simp; ring

theorem muq_stirling (hκ : κ ≤ 1) (hq : 1 ≤ q) : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
    |muq κ q τ - (1 / (2 * Real.pi)) * Real.log (q * |τ| / (2 * Real.pi))| ≤ C / τ ^ 2 :=
  ⟨20 / (2 * Real.pi), muq_stirling_const hκ hq⟩

/-! ### μ_χ(0) > −1 -/

theorem neg_one_lt_muq_zero (hκ : κ ≤ 1) (hq : 1 ≤ q) : (-1 : ℝ) < muq κ q 0 := by
  rw [muq_eq, show ((0 : ℝ) / 2 : ℝ) = (0 : ℝ) by norm_num]
  have ha0 := absc_pos κ
  have ha1 := absc_lt_one hκ
  have ha4 := quarter_le_absc κ
  rw [MuFields.re_digamma_vertical ha0 ha1 0]
  -- the series is termwise nonnegative
  have hS : (0 : ℝ) ≤ ∑' n : ℕ,
      (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + absc κ) / (((n : ℝ) + 1 + absc κ) ^ 2 + (0 : ℝ) ^ 2)) := by
    refine tsum_nonneg fun n => ?_
    have hna : (0 : ℝ) < (n : ℝ) + 1 + absc κ := by positivity
    have h1 : ((n : ℝ) + 1 + absc κ) / (((n : ℝ) + 1 + absc κ) ^ 2 + (0 : ℝ) ^ 2)
        = 1 / ((n : ℝ) + 1 + absc κ) := by
      rw [show ((n : ℝ) + 1 + absc κ) ^ 2 + (0 : ℝ) ^ 2 = ((n : ℝ) + 1 + absc κ) * ((n : ℝ) + 1 + absc κ) by ring,
        div_mul_eq_div_div, div_self hna.ne']
    rw [h1]
    have h2 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h3 : 1 / ((n : ℝ) + 1 + absc κ) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le h2 (by linarith)
    linarith
  -- 1/a ≤ 4
  have hinv : absc κ / (absc κ ^ 2 + (0:ℝ) ^ 2) ≤ 4 := by
    rw [show absc κ ^ 2 + (0:ℝ) ^ 2 = absc κ * absc κ by ring, div_mul_eq_div_div, div_self ha0.ne']
    rw [div_le_iff₀ ha0]; linarith
  -- log(q/π) ≥ −log π > −1.4
  have hγ : Real.eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
  have hπ3 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hπ4 : Real.pi < 4 := Real.pi_lt_four
  have hlogπ : Real.log Real.pi < 1.4 := by
    have h1 : Real.log Real.pi < Real.log 4 := Real.log_lt_log Real.pi_pos hπ4
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have h3 := Real.log_two_lt_d9
    nlinarith
  have hq0 : (0:ℝ) < q := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hq)
  have hlogq : -Real.log Real.pi ≤ Real.log (q / Real.pi) := by
    rw [Real.log_div hq0.ne' Real.pi_pos.ne']
    have : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
    linarith
  set S := ∑' n : ℕ,
      (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + absc κ) / (((n : ℝ) + 1 + absc κ) ^ 2 + (0 : ℝ) ^ 2))
  have h2π : 0 < 2 * Real.pi := by positivity
  -- μ(0) ≥ (−γ − 4 − log π)/(2π) > −1
  have hsum : -6.07 ≤ -Real.eulerMascheroniConstant - absc κ / (absc κ ^ 2 + (0:ℝ) ^ 2) + S
      + Real.log (q / Real.pi) := by linarith
  have : -1 < (1 / (2 * Real.pi)) * (-6.07) := by
    have h607 : (1 / (2 * Real.pi)) * 6.07 < 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one h2π]; nlinarith
    linarith
  calc (-1 : ℝ) < (1 / (2 * Real.pi)) * (-6.07) := this
    _ ≤ (1 / (2 * Real.pi)) * (-Real.eulerMascheroniConstant - absc κ / (absc κ ^ 2 + (0:ℝ) ^ 2) + S)
        + (1 / (2 * Real.pi)) * Real.log (q / Real.pi) := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-! ### smooth -/

private lemma gamma_ne_neg_nat {z : ℂ} (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -m := by
  intro m h
  rw [h] at hz
  simp only [Complex.neg_re, Complex.natCast_re] at hz
  exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg m))) hz

/-- ψ is analytic on the right half-plane. -/
theorem analyticAt_digamma' {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.digamma z := by
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hGamD : DifferentiableOn ℂ Complex.Gamma {w : ℂ | 0 < w.re} := fun w hw =>
    (Complex.differentiableAt_Gamma w (gamma_ne_neg_nat hw)).differentiableWithinAt
  have hGamA := hGamD.analyticOnNhd hU
  have h1 : AnalyticAt ℂ (deriv Complex.Gamma) z := (hGamA z hz).deriv
  have h2 : AnalyticAt ℂ Complex.Gamma z := hGamA z hz
  have h3 : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero (gamma_ne_neg_nat hz)
  have h4 := h1.div h2 h3
  exact h4.congr (by
    filter_upwards with w
    rw [Complex.digamma_def, logDeriv_apply]
    rfl)


set_option backward.isDefEq.respectTransparency false in
theorem muq_smooth (κ q : ℕ) : ContDiff ℝ ⊤ (muq κ q) := by
  have hfun : muq κ q = fun τ : ℝ => (1 / (2 * Real.pi))
        * (Complex.digamma (((absc κ : ℝ) : ℂ) + Complex.I * (τ : ℂ) / 2)).re
      + (1 / (2 * Real.pi)) * Real.log (q / Real.pi) := by
    funext τ; rw [muq_eq]; congr 3; push_cast; ring
  rw [hfun]
  have hc : ContDiff ℝ ⊤ (fun τ : ℝ => (((absc κ : ℝ) : ℂ) + Complex.I * (τ : ℂ) / 2 : ℂ)) := by
    have h1 : ContDiff ℝ ⊤ (fun τ : ℝ => (τ : ℂ)) := Complex.ofRealCLM.contDiff
    have h2 : ContDiff ℝ ⊤ (fun τ : ℝ => Complex.I * (τ : ℂ)) := contDiff_const.mul h1
    have h3 : ContDiff ℝ ⊤ (fun τ : ℝ => Complex.I * (τ : ℂ) / 2) := by
      simpa [div_eq_mul_inv] using h2.mul contDiff_const
    exact contDiff_const.add h3
  refine contDiff_iff_contDiffAt.mpr fun τ => ?_
  have hz : (0 : ℝ) < ((((absc κ : ℝ) : ℂ) + Complex.I * (τ : ℂ) / 2 : ℂ)).re := by
    simp; exact absc_pos κ
  have h4' : AnalyticAt ℝ Complex.digamma (((absc κ : ℝ) : ℂ) + Complex.I * (τ : ℂ) / 2) :=
    AnalyticAt.restrictScalars (analyticAt_digamma' hz)
  have h4 : ContDiffAt ℝ ⊤ Complex.digamma (((absc κ : ℝ) : ℂ) + Complex.I * (τ : ℂ) / 2) :=
    h4'.contDiffAt
  have h5 : ContDiffAt ℝ ⊤
      (fun τ : ℝ => Complex.digamma (((absc κ : ℝ) : ℂ) + Complex.I * (τ : ℂ) / 2)) τ :=
    h4.comp τ hc.contDiffAt
  have h6 : ContDiffAt ℝ ⊤
      (fun τ : ℝ => (Complex.digamma (((absc κ : ℝ) : ℂ) + Complex.I * (τ : ℂ) / 2)).re) τ :=
    (Complex.reCLM.contDiff.contDiffAt).comp τ h5
  have h7 := (contDiffAt_const (c := (1 / (2 * Real.pi) : ℝ))).mul h6
  exact h7.add contDiffAt_const

/-! ### μ_χ′ ≪ 1/|τ| (mirror of MuFields.mu_deriv_bound at abscissa a ≥ 1/4) -/

set_option backward.isDefEq.respectTransparency false in
theorem muq_deriv_bound_const (hκ : κ ≤ 1) (τ : ℝ) (hτ : 1 ≤ |τ|) :
    |deriv (muq κ q) τ| ≤ (24 / Real.pi) / |τ| := by
  have hτ0 : (0 : ℝ) < |τ| := by linarith
  set zA : ℂ := ((absc κ : ℝ) : ℂ) + (Complex.I / 2) * (τ : ℂ) with hzA
  have hzA_eq : zA = ((absc κ : ℝ) : ℂ) + Complex.I * ((τ / 2 : ℝ) : ℂ) := by
    rw [hzA]
    push_cast
    ring
  have hmem : zA ∈ Complex.integerComplement := by
    rw [hzA_eq]
    exact arg_mem hκ (τ / 2)
  have hψd : DifferentiableAt ℂ Complex.digamma zA :=
    Zeta23.Stirling.differentiableAt_digamma hmem
  -- chain rule: μ has derivative (1/2π)·Re(ψ′(zA)·(I/2)) at τ
  have hginner : HasDerivAt (fun x : ℝ => ((absc κ : ℝ) : ℂ) + (Complex.I / 2) * (x : ℂ))
      (Complex.I / 2) τ := by
    have h1 : HasDerivAt (fun x : ℝ => ((x : ℝ) : ℂ)) 1 τ := Complex.ofRealCLM.hasDerivAt
    have h2 := (h1.const_mul (Complex.I / 2)).const_add (((absc κ : ℝ) : ℂ))
    simpa using h2
  have hcompd : HasDerivAt
      (fun x : ℝ => Complex.digamma (((absc κ : ℝ) : ℂ) + (Complex.I / 2) * (x : ℂ)))
      ((Complex.I / 2) • deriv Complex.digamma zA) τ := by
    have h3 := HasDerivAt.scomp τ hψd.hasDerivAt hginner
    exact h3
  have hre : HasDerivAt
      (fun x : ℝ => (Complex.digamma (((absc κ : ℝ) : ℂ) + (Complex.I / 2) * (x : ℂ))).re)
      (((Complex.I / 2) • deriv Complex.digamma zA).re) τ :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt τ hcompd)
  have hmuD : HasDerivAt (muq κ q)
      (1 / (2 * Real.pi) * (((Complex.I / 2) • deriv Complex.digamma zA).re)) τ := by
    have h4 := (hre.const_mul (1 / (2 * Real.pi))).add_const ((1 / (2 * Real.pi)) * Real.log (q / Real.pi))
    have h5 : muq κ q = fun x : ℝ =>
        1 / (2 * Real.pi) * (Complex.digamma (((absc κ : ℝ) : ℂ) + (Complex.I / 2) * (x : ℂ))).re
          + (1 / (2 * Real.pi)) * Real.log (q / Real.pi) := by
      funext x
      rw [muq_eq]
      congr 3
      push_cast; ring
    rw [h5]
    exact h4
  rw [hmuD.deriv]
  -- bound the derivative value by the trigamma tail
  have htri := Zeta23.Stirling.hasSum_trigamma hmem
  have hnorm_term : ∀ n : ℕ, ‖(1 : ℂ) / (zA + n) ^ 2‖
      = (((absc κ : ℝ) + n) ^ 2 + (τ / 2) ^ 2)⁻¹ := by
    intro n
    have hre2 : (zA + n).re = (absc κ : ℝ) + n := by
      rw [hzA_eq]
      simp
    have him2 : (zA + n).im = τ / 2 := by
      rw [hzA_eq]
      simp
    rw [norm_div, norm_one, norm_pow, one_div]
    congr 1
    rw [show ‖zA + (n : ℂ)‖ ^ 2 = Complex.normSq (zA + n) from Complex.sq_norm _,
      Complex.normSq_apply, hre2, him2]
    ring
  -- comparison with the quarter line: (a+n)² ≥ (1/4+n)²
  have hcmp : ∀ n : ℕ, (((absc κ : ℝ) + n) ^ 2 + (τ / 2) ^ 2)⁻¹
      ≤ (((1 / 4 : ℝ) + n) ^ 2 + (τ / 2) ^ 2)⁻¹ := by
    intro n
    have ha := quarter_le_absc κ
    rw [← one_div, ← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hsummable_a : Summable (fun n : ℕ => (((absc κ : ℝ) + n) ^ 2 + (τ / 2) ^ 2)⁻¹) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hcmp (MuFields.summable_quarter_line (τ / 2))
  have hsummable_norm : Summable (fun n : ℕ => ‖(1 : ℂ) / (zA + n) ^ 2‖) := by
    refine hsummable_a.congr fun n => ?_
    exact (hnorm_term n).symm
  have hψ'bound : ‖deriv Complex.digamma zA‖ ≤ 24 / |τ| := by
    have h6 : deriv Complex.digamma zA = ∑' n : ℕ, (1 : ℂ) / (zA + n) ^ 2 := htri.tsum_eq.symm
    rw [h6]
    calc ‖∑' n : ℕ, (1 : ℂ) / (zA + n) ^ 2‖ ≤ ∑' n : ℕ, ‖(1 : ℂ) / (zA + n) ^ 2‖ :=
          norm_tsum_le_tsum_norm hsummable_norm
      _ = ∑' n : ℕ, (((absc κ : ℝ) + n) ^ 2 + (τ / 2) ^ 2)⁻¹ := by
          congr 1
          funext n
          exact hnorm_term n
      _ ≤ ∑' n : ℕ, (((1 / 4 : ℝ) + n) ^ 2 + (τ / 2) ^ 2)⁻¹ :=
          Summable.tsum_le_tsum hcmp hsummable_a (MuFields.summable_quarter_line (τ / 2))
      _ ≤ 12 / |τ / 2| := MuFields.trigamma_tail_le (by
          rw [abs_div]
          rw [show |(2 : ℝ)| = 2 by norm_num]
          linarith)
      _ = 24 / |τ| := by
          rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]
          field_simp
          norm_num
  -- |Re((I/2)•ψ′)| ≤ ‖ψ′‖/2
  have hval : |(((Complex.I / 2) • deriv Complex.digamma zA).re)|
      ≤ ‖deriv Complex.digamma zA‖ / 2 := by
    calc |(((Complex.I / 2) • deriv Complex.digamma zA).re)|
        ≤ ‖(Complex.I / 2) • deriv Complex.digamma zA‖ := Complex.abs_re_le_norm _
      _ = ‖Complex.I / 2‖ * ‖deriv Complex.digamma zA‖ := norm_smul _ _
      _ = ‖deriv Complex.digamma zA‖ / 2 := by
          rw [norm_div, Complex.norm_I]
          rw [show ‖(2 : ℂ)‖ = 2 from by
            rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos (by norm_num)]]
          ring
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  calc 1 / (2 * Real.pi) * |(((Complex.I / 2) • deriv Complex.digamma zA).re)|
      ≤ 1 / (2 * Real.pi) * (‖deriv Complex.digamma zA‖ / 2) := by
        gcongr
    _ ≤ 1 / (2 * Real.pi) * ((24 / |τ|) / 2) := by
        gcongr
    _ ≤ (24 / Real.pi) / |τ| := by
        rw [div_div, div_mul_eq_mul_div, one_mul]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        ring_nf
        have e1 : Real.pi * Real.pi⁻¹ = 1 := mul_inv_cancel₀ hπ.ne'
        have e2 : |τ| * |τ|⁻¹ = 1 := mul_inv_cancel₀ hτ0.ne'
        nlinarith [e1, e2]


theorem muq_deriv_bound (hκ : κ ≤ 1) : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| → |deriv (muq κ q) τ| ≤ C / |τ| :=
  ⟨24 / Real.pi, muq_deriv_bound_const hκ⟩

/-! ### The bundle -/

/-- H-Γ(χ) from the two integral fields (supplied by Zeta23/ThmE/IntMuChi.lean from
`muq_stirling` + continuity by the FTC computations with log(qτ/2π)). -/
theorem gammaFactsChi_of_int (hκ : κ ≤ 1) (hq : 1 ≤ q)
    (hint : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |(∫ τ in T..(2 * T), muq κ q τ) - T * ell1q q T / (2 * Real.pi)| ≤ C / T)
    (hint2 : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |(∫ τ in T..(2 * T), muq κ q τ ^ 2) - T * ell1q q T ^ 2 / (4 * Real.pi ^ 2)|
        ≤ C * (T * ell1q q T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2) :
    GammaFactsChi κ q :=
  ⟨muq_even hκ, muq_smooth κ q, muq_monotoneOn hκ, muq_zero_le hκ, neg_one_lt_muq_zero hκ hq,
    muq_stirling hκ hq, muq_deriv_bound hκ, hint, hint2⟩

/-- **H-Γ(χ), unconditionally** (parity κ ≤ 1, modulus q ≥ 1): all nine fields are theorems
(the two ∫ fields via Zeta23/ThmE/IntMuChi.lean). -/
theorem gammaFactsChi (hκ : κ ≤ 1) (hq : 1 ≤ q) : GammaFactsChi κ q :=
  gammaFactsChi_of_int hκ hq
    (IntMuChi.int_muq_of_stirling hq (muq_smooth κ q).continuous (muq_stirling hκ hq))
    (IntMuChi.int_muq_sq_of_stirling hq (muq_smooth κ q).continuous (muq_stirling hκ hq))

/-- **H-Γ(χ) with one constant for all parities κ ≤ 1 and all moduli q ≥ 1**
(`GammaFactsChiBounded`; consumed by the q-uniform RvM(χ)): every constant and threshold
above is conductor-free (the Stirling constant 20/2π, the derivative constant 24/π, and
int_muq_uniform / int_muq_sq_uniform whose constants are explicit in the Stirling constant). -/
theorem gammaFactsChi_uniform :
    ∃ C : ℝ, ∀ (κ q : ℕ), κ ≤ 1 → 1 ≤ q → GammaFactsChiBounded κ q C := by
  set Cs : ℝ := 20 / (2 * Real.pi) with hCs
  set T₂ : ℝ := max (2 * Real.pi * Real.exp 4) (32 * Real.pi ^ 2 * (Cs * (1 + Cs) + 1)) with hT₂
  set K₂ : ℝ := 8 * (1 + 2 * Real.log 2 ^ 2) + 1 + 4 * Real.pi * |Cs| with hK₂
  set C : ℝ := max (max (max Cs (24 / Real.pi)) (max 1 T₂)) K₂ with hC
  have hCs_le : Cs ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have h24_le : 24 / Real.pi ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have h1_le : (1:ℝ) ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hT₂_le : T₂ ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  have hK₂_le : K₂ ≤ C := le_max_right _ _
  refine ⟨C, fun κ q hκ hq => ?_⟩
  have hcont := (muq_smooth κ q).continuous
  have hst := muq_stirling_const (q := q) hκ hq
  refine ⟨muq_even hκ, muq_smooth κ q, muq_monotoneOn hκ, muq_zero_le hκ, neg_one_lt_muq_zero hκ hq,
    ?_, ?_, ?_, ?_⟩
  · intro τ hτ
    exact (hst τ hτ).trans (div_le_div_of_nonneg_right hCs_le (sq_nonneg _))
  · intro τ hτ
    exact (muq_deriv_bound_const hκ τ hτ).trans (div_le_div_of_nonneg_right h24_le (abs_nonneg _))
  · intro T hT
    have hT1 : (1:ℝ) ≤ T := h1_le.trans hT
    have hT0 : 0 < T := by linarith
    exact (IntMuChi.int_muq_uniform Cs κ q hq hcont hst T hT1).trans
      (div_le_div_of_nonneg_right hCs_le hT0.le)
  · intro T hT
    have hT' : T₂ ≤ T := hT₂_le.trans hT
    have hT0 : 0 ≤ T := le_trans (by linarith) hT
    have h := IntMuChi.int_muq_sq_uniform Cs κ q hq hcont hst T hT'
    refine h.trans ?_
    have hnn : 0 ≤ (T * ell1q q T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2 := by positivity
    have hk : K₂ * (T * ell1q q T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2
        = K₂ * ((T * ell1q q T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2) := by ring
    have hc : C * (T * ell1q q T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2
        = C * ((T * ell1q q T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2) := by ring
    rw [hk, hc]
    exact mul_le_mul_of_nonneg_right hK₂_le hnn

end GammaChi
end ThmE
end Zeta23
