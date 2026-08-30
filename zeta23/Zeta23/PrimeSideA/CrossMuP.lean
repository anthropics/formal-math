/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
Imported by PrimeSideA.lean.
-/
import Zeta23.PrimeSideA.Basic
import Zeta23.PrimeSideA.CrossMuPCore

/-!
# [prop:cross] (i):  `𝓜[μ, P_X] ≪ l √X`   (the paper §5.4)

Paper proof (§5.4): with `m(τ′) := ∫_I Φ(τ−τ′)² μ(τ) dτ`, "`m` is `C¹`, and differentiating
under the integral and integrating by parts in `τ`,
`m′(τ′) = μ(T)Φ(T−τ′)² − μ(2T)Φ(2T−τ′)² + ∫_I μ′(τ)Φ(τ−τ′)² dτ`, so that `∫_I|m′| ≪ lL`.
For `y ≥ log 2`, integrating by parts, `|∫_I m(τ′)cos(τ′y)dτ′| ≤ (2 sup|m| + ∫_I|m′|)/y ≪ lL/y`.
Therefore `|𝓜[μ,P_X]| = |π⁻¹ Σ_n a_n ∫_I m(τ′)cos(τ′y_n)dτ′| ≪ lL Σ_{n≤X} a_n/log n ≪ lL √X/L = l√X`
by (eq:cheb1)."

Formal route (same two integrations by parts, but ordered so that NO differentiation under the
integral sign is needed): Fubini with `τ` outer; IBP in `τ′` on `Φ(τ−τ′)²·cos(τ′y)` (the derivative
lands on `Φ²`, `Φ ∈ C¹`); Fubini swap; IBP in `τ` on `μ(τ)·(Φ²)′(τ−τ′)` (the derivative lands on
`μ`); then the sup bounds `|μ| ≤ l`, `|μ′| ≤ C/T` on `I` and `∫_S Φ(·−c)² ≤ ∫_ℝ Φ² = 2πbL` give
`|𝓜[μ, cos(·y)]| ≤ (4l + C)·2πbL/|y|`, and [eq:cheb1] (`cheb1c`: `Σ Λ(n)/(√n log n) ≪ √X/log X`, `log X = L`)
finishes.  Inputs: `LocalHyps` (Φ ∈ C¹, Φ even, ∫Φ² = 2πbL, b ≤ a ≤ 1, l ≥ 1), H-Γ (`smooth`,
`deriv_bound`, via `mu_abs_le_l`), H-cheb (`cheb1c`).
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace PrimeSide


/-! ## [prop:cross] (i) -/

section CrossMuP
variable (cϱ lam : ℝ)

/-- `𝓜[μ, P_X]` as the finite sum `−π⁻¹ Σ_n a_n 𝓜[μ, cos(· y_n)]` (§5.4, Fubini/linearity). -/
lemma Mform_mu_PX_eq {p : Setting} {F : LocalFun} (hΦ : Continuous F.Phi) (hμ : Continuous Zeta23.mu) :
    Mform F.Phi p.T Zeta23.mu (Zeta23.PX p.X)
      = ∑ n ∈ primeRange p.X, (-(1 / Real.pi) * acoef n)
          * Mform F.Phi p.T Zeta23.mu (fun t => Real.cos (t * ycoef n)) := by
  unfold Mform
  have h1 : (fun q : ℝ × ℝ => F.Phi (q.1 - q.2) ^ 2 * Zeta23.mu q.1 * Zeta23.PX p.X q.2)
      = fun q => ∑ n ∈ primeRange p.X, (-(1 / Real.pi) * acoef n)
          * (F.Phi (q.1 - q.2) ^ 2 * Zeta23.mu q.1 * Real.cos (q.2 * ycoef n)) := by
    funext q
    rw [PX_eq, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [h1, integral_finsetSum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul]
  · intro n _
    have hv : Continuous fun t : ℝ => Real.cos (t * ycoef n) := by fun_prop
    have := (Mform_integrableOn (T := p.T) hΦ hμ hv).const_mul (-(1 / Real.pi) * acoef n)
    simpa only using this

/-- **[prop:cross] (i)** (§5.4): `𝓜[μ,P_X] ≪ l√X`, stated in the `∃ C, EventuallyAtCore cϱ lam …`
form used by the results of `PrimeSideA.lean` (which imports this file). -/
theorem prop_cross_muP (hΓ : Zeta23.GammaFacts) (hcheb : Zeta23.ChebyshevMertens)
    (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |Mform F.Phi p.T Zeta23.mu (Zeta23.PX p.X)| ≤ C * (p.l * Real.sqrt p.X)) := by
  obtain ⟨T₁, hT₁⟩ := mu_abs_le_l hΓ
  obtain ⟨Cd, hCd⟩ := hΓ.deriv_bound
  obtain ⟨Cc, hCc⟩ := hcheb.cheb1c
  have hμ : ContDiff ℝ 1 Zeta23.mu := hΓ.smooth.of_le (by exact_mod_cast le_top)
  refine ⟨2 * (4 + |Cd|) * |Cc|, max T₁ (2 * π * Real.exp (|(2:ℝ)| / lam)), ?_⟩
  intro p F hplam hT hF
  have hT₁' : T₁ ≤ p.T := (le_max_left _ _).trans hT
  have hT2 : 2 * π * Real.exp (|(2:ℝ)| / p.lam) ≤ p.T := by rw [hplam]; exact (le_max_right _ _).trans hT
  have hlam0 : 0 < p.lam := hplam ▸ hlam.1
  have hT1 : 1 ≤ p.T := Setting.one_le_T (div_nonneg (abs_nonneg _) hlam0.le) hT2
  have hT0 : 0 ≤ p.T := by linarith
  have hl1 : 1 ≤ p.l := hF.one_le_l
  have hL := hF.L_pos
  have hX2 : 2 ≤ p.X := Setting.le_X_of_T hlam0 hT2
  have hlogX : Real.log p.X = p.L := by simp [Setting.X]
  -- sup bounds for μ, μ' on I
  have hB : ∀ τ ∈ Icc p.T (2 * p.T), |Zeta23.mu τ| ≤ p.l := hT₁ p hT₁'
  have hD : ∀ τ ∈ Icc p.T (2 * p.T), |deriv Zeta23.mu τ| ≤ |Cd| / p.T := by
    intro τ hτ
    have hτ1 : 1 ≤ |τ| := by rw [abs_of_nonneg (by linarith [hτ.1])]; linarith [hτ.1]
    refine (hCd τ hτ1).trans ?_
    rw [abs_of_nonneg (by linarith [hτ.1])]
    calc Cd / τ ≤ |Cd| / τ := div_le_div_of_nonneg_right (le_abs_self _) (by linarith [hτ.1])
      _ ≤ |Cd| / p.T := div_le_div_of_nonneg_left (abs_nonneg _) (by linarith) hτ.1
  -- the oscillatory bound at each frequency y_n, n ≥ 2
  set S : ℝ := ∫ x, F.Phi x ^ 2 with hSdef
  have hS : S ≤ 2 * π * p.L := hF.integral_Phi_sq_le
  have hS0 : 0 ≤ S := integral_nonneg fun x => sq_nonneg _
  set K : ℝ := (4 * p.l + |Cd| / p.T * p.T) * S with hKdef
  have hKeq : K = (4 * p.l + |Cd|) * S := by
    have hTne : p.T ≠ 0 := by linarith
    rw [hKdef, div_mul_cancel₀ _ hTne]
  have hK0 : 0 ≤ K := by rw [hKeq]; positivity
  have hosc : ∀ n ∈ primeRange p.X,
      |(-(1 / Real.pi) * acoef n) * Mform F.Phi p.T Zeta23.mu (fun t => Real.cos (t * ycoef n))|
        ≤ (1 / Real.pi) * K * (acoef n / ycoef n) := by
    intro n hn
    have ha0 : 0 ≤ acoef n := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · -- n = 1: a_1 = 0
      have hn1 : n = 1 := by
        have : 0 < n := (Finset.mem_Ioc.mp hn).1
        omega
      subst hn1
      simp [acoef]
    · have hy : 0 < ycoef n := Real.log_pos (by exact_mod_cast h2)
      have hM := abs_Mform_cos_le hT0 hF.Phi_contDiff hF.Phi_sq_integrable hμ hB hD hy.ne'
      rw [abs_of_pos hy] at hM
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi),
        abs_of_nonneg ha0]
      calc 1 / Real.pi * acoef n * |Mform F.Phi p.T Zeta23.mu fun t => Real.cos (t * ycoef n)|
          ≤ 1 / Real.pi * acoef n * (K / ycoef n) := by gcongr
        _ = 1 / Real.pi * K * (acoef n / ycoef n) := by ring
  -- sum over n
  rw [Mform_mu_PX_eq hF.Phi_contDiff.continuous hμ.continuous]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hosc).trans ?_)
  rw [← Finset.mul_sum]
  -- Σ a_n / y_n ≤ Cc √X / log X = Cc √X / L
  have hsum : ∑ n ∈ primeRange p.X, acoef n / ycoef n ≤ |Cc| * Real.sqrt p.X / p.L := by
    have h := hCc p.X hX2
    rw [hlogX] at h
    have e : ∑ n ∈ primeRange p.X, acoef n / ycoef n
        = ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Λ n : ℝ) / (Real.sqrt n * Real.log n) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [acoef, ycoef, div_div]
    rw [e]
    refine h.trans ?_
    gcongr; exact le_abs_self _
  have hsum0 : 0 ≤ ∑ n ∈ primeRange p.X, acoef n / ycoef n :=
    Finset.sum_nonneg fun n _ => div_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
      (Real.log_natCast_nonneg _)
  calc 1 / Real.pi * K * ∑ n ∈ primeRange p.X, acoef n / ycoef n
      ≤ 1 / Real.pi * ((4 * p.l + |Cd|) * (2 * π * p.L)) * (|Cc| * Real.sqrt p.X / p.L) := by
        rw [hKeq]; gcongr
    _ = 2 * (4 * p.l + |Cd|) * |Cc| * Real.sqrt p.X := by field_simp
    _ ≤ 2 * ((4 + |Cd|) * p.l) * |Cc| * Real.sqrt p.X := by
        gcongr
        nlinarith [abs_nonneg Cd]
    _ = 2 * (4 + |Cd|) * |Cc| * (p.l * Real.sqrt p.X) := by ring

end CrossMuP

end PrimeSide
end Zeta23
