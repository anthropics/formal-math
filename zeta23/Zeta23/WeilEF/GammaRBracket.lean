/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/GammaRBracket.lean — the critical-line Γℝ bracket; proves
`Zeta23.WeilEF.gammaR_bracket`:

  logDeriv Γℝ(1/2+it) + logDeriv Γℝ(1/2−it) = Re ψ(1/4 + it/2) − log π      (t ∈ ℝ),

from Γℝ(s) = π^{−s/2}Γ(s/2) (Mathlib `Complex.Gammaℝ`), logDeriv Γℝ(s) = −(log π)/2 + ψ(s/2)/2
for re s > 0, and the conjugation symmetry ψ(conj z) = conj ψ(z) (from the partial-fraction
series Zeta23.DigammaSeries.hasSum_digamma_series).
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Zeta23.GammaFacts.Series

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex

/-- conjugation symmetry of the digamma function off the poles. -/
theorem digamma_conj {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Complex.digamma (starRingEnd ℂ z) = starRingEnd ℂ (Complex.digamma z) := by
  have hz' : starRingEnd ℂ z ∈ Complex.integerComplement := by
    rintro ⟨k, hk⟩
    apply hz
    refine ⟨k, ?_⟩
    have := congrArg (starRingEnd ℂ) hk
    simpa using this
  have h1 := Zeta23.DigammaSeries.hasSum_digamma_series hz
  have h2 := Zeta23.DigammaSeries.hasSum_digamma_series hz'
  -- conj of the series for z is the series for conj z
  have h1c : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (starRingEnd ℂ z + n + 1))
      (starRingEnd ℂ (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z)) := by
    have := (Complex.hasSum_conj' ).mpr h1
    refine this.congr_fun fun n => ?_
    simp only [map_sub, map_div₀, map_one, map_add, map_natCast]
  have huniq := h2.unique h1c
  have e : starRingEnd ℂ (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z)
      = starRingEnd ℂ (Complex.digamma z) + (Real.eulerMascheroniConstant : ℂ)
        + 1 / starRingEnd ℂ z := by
    simp only [map_add, map_div₀, map_one, Complex.conj_ofReal]
  rw [e] at huniq
  linear_combination huniq

/-- `logDeriv Γℝ(s) = −(log π)/2 + ψ(s/2)/2` for `re s > 0`. -/
theorem logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s = -((Real.log Real.pi : ℝ) : ℂ) / 2 + (1 / 2) * Complex.digamma (s / 2) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hs2 : 0 < (s / 2).re := by simp; linarith
  have hGne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs2
  have hpow_ne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hπ]; exact Complex.exp_ne_zero _
  -- Γℝ as a product of two functions
  have hfun : Complex.Gammaℝ = fun s => (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s
      * (Complex.Gamma ∘ fun s : ℂ => s / 2) s := by
    funext s; rw [Complex.Gammaℝ_def]; rfl
  -- derivative of the power factor
  have hdpow : HasDerivAt (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2)) s := by
    have h := ((hasDerivAt_id s).neg.div_const 2).const_cpow (c := (Real.pi : ℂ)) (Or.inl hπ)
    convert h using 1
    · funext x; simp
    · simp
  have hdiff_pow : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s :=
    hdpow.differentiableAt
  have hΓdiff : DifferentiableAt ℂ Complex.Gamma (s / 2) := by
    apply Complex.differentiableAt_Gamma
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hhalf : DifferentiableAt ℂ (fun s : ℂ => s / 2) s := differentiableAt_id.div_const 2
  have hdiff_G : DifferentiableAt ℂ (Complex.Gamma ∘ fun s : ℂ => s / 2) s := hΓdiff.comp s hhalf
  rw [hfun, logDeriv_mul s hpow_ne (by exact hGne) hdiff_pow hdiff_G,
    logDeriv_comp (g := fun s : ℂ => s / 2) (x := s) hΓdiff hhalf, ← Complex.digamma_def]
  -- the power factor's logDeriv
  have h1 : logDeriv (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s = Complex.log Real.pi * (-1 / 2) := by
    rw [logDeriv_apply, hdpow.deriv]
    field_simp
  have h2 : deriv (fun s : ℂ => s / 2) s = 1 / 2 := by
    have : HasDerivAt (fun s : ℂ => s / 2) (1 / 2) s := by
      simpa using (hasDerivAt_id s).div_const 2
    exact this.deriv
  rw [h1, h2, (Complex.ofReal_log Real.pi_pos.le).symm]
  ring

/-- **The critical-line Γℝ bracket** is EF_lit's Γ-integrand: for real t,
logDeriv Γℝ(1/2+it) + logDeriv Γℝ(1/2−it) = Re ψ(1/4+it/2) − log π  (ψ = digamma;
Γℝ(s) = π^{−s/2}Γ(s/2), logDeriv Γℝ(s) = −(log π)/2 + ψ(s/2)/2, conj symmetry). -/
theorem gammaR_bracket (t : ℝ) :
    logDeriv Complex.Gammaℝ (1/2 + t * I) + logDeriv Complex.Gammaℝ (1/2 - t * I)
      = (((Complex.digamma (1/4 + t/2 * I)).re - Real.log Real.pi : ℝ) : ℂ) := by
  have hp : 0 < ((1:ℂ)/2 + t * I).re := by simp
  have hm : 0 < ((1:ℂ)/2 - t * I).re := by simp
  rw [logDeriv_Gammaℝ hp, logDeriv_Gammaℝ hm]
  set w : ℂ := 1/4 + t/2 * I with hw
  have e1 : ((1:ℂ)/2 + t * I) / 2 = w := by rw [hw]; ring
  have e2 : ((1:ℂ)/2 - t * I) / 2 = starRingEnd ℂ w := by
    have : starRingEnd ℂ w = 1/4 - t/2 * I := by
      rw [hw, show (1:ℂ)/4 + (t:ℂ)/2 * I = ((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ) * I by push_cast; ring]
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    rw [this]; ring
  have hwZ : w ∈ Complex.integerComplement := by
    rintro ⟨k, hk⟩
    have := congrArg Complex.re hk
    rw [hw] at this
    simp at this
    -- (k : ℝ) = 1/4 is impossible
    have h4 : (4 * k : ℤ) = (1 : ℤ) := by
      have : (4 : ℝ) * k = 1 := by rw [this]; norm_num
      exact_mod_cast this
    omega
  rw [e1, e2, digamma_conj hwZ]
  -- ψ(w)/2 + conj ψ(w)/2 = Re ψ(w)
  have hre : (1/2 : ℂ) * Complex.digamma w + (1/2 : ℂ) * starRingEnd ℂ (Complex.digamma w)
      = ((Complex.digamma w).re : ℂ) := by
    rw [← mul_add, Complex.add_conj]; push_cast; ring
  push_cast
  linear_combination hre

end WeilEF
end Zeta23
