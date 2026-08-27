/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/CrossMuPChi.lean — [prop:cross] (i) for L(s,χ):  `𝓜[μ_χ, P_{X,χ}] ≪_q l√X`
(statement in Zeta23/ThmE/PrimeSideChi.lean, which re-exports this proof).

Route = the ζ-proof of Zeta23/PrimeSideA/CrossMuP.lean (double IBP, no differentiation under the
integral), with two changes: the density μ_χ's bounds come from the H-Γ(χ) package
(`GammaFactsChi`: stirling for |μ_χ| ≤ C_q·l on I, deriv_bound for |μ_χ′| ≤ C/T), and the prime
sum has complex unimodular-or-smaller coefficients: `Re(c_n·n^{−iτ}) = ‖c_n‖·cos(τ·log n − arg c_n)`,
handled by the PHASE-SHIFTED oscillatory bound `abs_Mform_cos_phase_le` (CrossMuPCore) — the bounds
enter only through `‖c_n‖ ≤ 1`, exactly per [thm:E] proof (iii).
-/
import Zeta23.PrimeSideA.Basic
import Zeta23.PrimeSideA.CrossMuPCore
import Zeta23.ThmE.Hypotheses
import Zeta23.ThmE.PrimeSideChi

noncomputable section

open MeasureTheory Real Set Finset Complex
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace ThmE

open Zeta23.PrimeSide

/-! ## The Mform finite-sum split and the oscillatory bound -/

open Zeta23.PrimeSide in
/-- `𝓜[u, P_{X,c}]` as the finite phase-split sum (mirror of the ζ `Mform_mu_PX_eq`). -/
lemma Mform_mu_PXc_eq {Φ : ℝ → ℝ} (hΦ : Continuous Φ) {u : ℝ → ℝ} (hu : Continuous u)
    (c : ℕ → ℂ) (X T : ℝ) :
    Mform Φ T u (PXc c X)
      = ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (-(1 / Real.pi) * ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))))
          * ((c n).re * Mform Φ T u (fun t => Real.cos (t * Real.log n))
             + (c n).im * Mform Φ T u (fun t => Real.sin (t * Real.log n))) := by
  unfold Mform
  have h1 : (fun q : ℝ × ℝ => Φ (q.1 - q.2) ^ 2 * u q.1 * PXc c X q.2)
      = fun q => ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (-(1 / Real.pi) * ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))))
          * ((c n).re * (Φ (q.1 - q.2) ^ 2 * u q.1 * Real.cos (q.2 * Real.log n))
             + (c n).im * (Φ (q.1 - q.2) ^ 2 * u q.1 * Real.sin (q.2 * Real.log n))) := by
    funext q
    rw [PXc_eq_sum_cos_sin, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [h1, integral_finsetSum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul]
    congr 1
    have i1 := (Mform_integrableOn' (T := T) hΦ hu
      (show Continuous fun t : ℝ => Real.cos (t * Real.log n) by fun_prop)).const_mul ((c n).re)
    have i2 := (Mform_integrableOn' (T := T) hΦ hu
      (show Continuous fun t : ℝ => Real.sin (t * Real.log n) by fun_prop)).const_mul ((c n).im)
    beta_reduce at i1 i2
    rw [integral_add i1 i2, integral_const_mul, integral_const_mul]
  · intro n _
    have i1 := (Mform_integrableOn' (T := T) hΦ hu
      (show Continuous fun t : ℝ => Real.cos (t * Real.log n) by fun_prop)).const_mul ((c n).re)
    have i2 := (Mform_integrableOn' (T := T) hΦ hu
      (show Continuous fun t : ℝ => Real.sin (t * Real.log n) by fun_prop)).const_mul ((c n).im)
    beta_reduce at i1 i2
    exact (i1.add i2).const_mul _

/-! ## [prop:cross](i) for L(s,χ) — the proof -/

open Zeta23.PrimeSide in
/-- **[prop:cross](i) for L(s,χ)** (statement = `prop_cross_muP_chi` of PrimeSideChi.lean, plus
the mathematically-required `1 ≤ q`): `|𝓜[μ_χ, P_{X,χ}]| ≪_q l√X`.  Complex coefficients enter
only through `|re|, |im| ≤ ‖c n‖ ≤ 1` ([thm:E] (iii)); the sin-part uses the phase-shifted
oscillatory bound at `θ = −π/2`. -/
theorem prop_cross_muP_chi_proved {κ q : ℕ} {c : ℕ → ℂ} {cϱ lam : ℝ}
    (hΓq : GammaFactsChi κ q) (hcheb : ChebyshevMertens) (hc : CoeffOK q c) (hq : 1 ≤ q)
    (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |Mform F.Phi p.T (muq κ q) (PXc c p.X)| ≤ C * (Zeta23.l p.T * Real.sqrt p.X)) := by
  obtain ⟨Cμ, T₁, hCμ, hT₁⟩ := muq_abs_le κ q hΓq hq
  obtain ⟨Cd, hCd⟩ := hΓq.deriv_bound
  obtain ⟨Cc, hCc⟩ := hcheb.cheb1c
  have hμ : ContDiff ℝ 1 (muq κ q) := hΓq.smooth.of_le (by exact_mod_cast le_top)
  refine ⟨4 * (4 * Cμ + |Cd|) * |Cc|, max T₁ (2 * π * Real.exp (|(2:ℝ)| / lam)), ?_⟩
  intro p F hplam hT hF
  have hT₁' : T₁ ≤ p.T := (le_max_left _ _).trans hT
  have hT2 : 2 * π * Real.exp (|(2:ℝ)| / p.lam) ≤ p.T := by
    rw [hplam]; exact (le_max_right _ _).trans hT
  have hlam0 : 0 < p.lam := hplam ▸ hlam.1
  have hT1 : 1 ≤ p.T := Setting.one_le_T (div_nonneg (abs_nonneg _) hlam0.le) hT2
  have hT0 : 0 ≤ p.T := by linarith
  have hl1 : 1 ≤ p.l := hF.one_le_l
  have hL := hF.L_pos
  have hX2 : 2 ≤ p.X := Setting.le_X_of_T hlam0 hT2
  have hlogX : Real.log p.X = p.L := by simp [Setting.X]
  -- sup bounds for μ_χ, μ_χ' on I
  have hB : ∀ τ ∈ Set.Icc p.T (2 * p.T), |muq κ q τ| ≤ Cμ * p.l := hT₁ p hT₁'
  have hD : ∀ τ ∈ Set.Icc p.T (2 * p.T), |deriv (muq κ q) τ| ≤ |Cd| / p.T := by
    intro τ hτ
    have hτ1 : 1 ≤ |τ| := by rw [abs_of_nonneg (by linarith [hτ.1])]; linarith [hτ.1]
    refine (hCd τ hτ1).trans ?_
    rw [abs_of_nonneg (by linarith [hτ.1])]
    calc Cd / τ ≤ |Cd| / τ := div_le_div_of_nonneg_right (le_abs_self _) (by linarith [hτ.1])
      _ ≤ |Cd| / p.T := div_le_div_of_nonneg_left (abs_nonneg _) (by linarith) hτ.1
  set S : ℝ := ∫ x, F.Phi x ^ 2 with hSdef
  have hS : S ≤ 2 * π * p.L := hF.integral_Phi_sq_le
  have hS0 : 0 ≤ S := integral_nonneg fun x => sq_nonneg _
  set K : ℝ := (4 * (Cμ * p.l) + |Cd| / p.T * p.T) * S with hKdef
  have hKeq : K = (4 * Cμ * p.l + |Cd|) * S := by
    have hTne : p.T ≠ 0 := by linarith
    rw [hKdef, div_mul_cancel₀ _ hTne]
    ring
  have hK0 : 0 ≤ K := by rw [hKeq]; positivity
  -- per-n coefficient and frequency
  have hren : ∀ n : ℕ, 2 ≤ n → (0:ℝ) < Real.log n := fun n h2 =>
    Real.log_pos (by exact_mod_cast h2)
  have hosc : ∀ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
      |(-(1 / Real.pi) * ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))))
          * ((c n).re * Mform F.Phi p.T (muq κ q) (fun t => Real.cos (t * Real.log n))
             + (c n).im * Mform F.Phi p.T (muq κ q) (fun t => Real.sin (t * Real.log n)))|
        ≤ (1 / Real.pi) * (2 * K) * ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) / Real.log n) := by
    intro n hn
    have ha0 : (0:ℝ) ≤ (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn1 : n = 1 := by
        have : 0 < n := (Finset.mem_Ioc.mp hn).1
        omega
      subst hn1
      simp
    · have hy : 0 < Real.log n := hren n h2
      -- cos part
      have hMc := abs_Mform_cos_le hT0 hF.Phi_contDiff hF.Phi_sq_integrable hμ hB hD hy.ne'
      rw [abs_of_pos hy] at hMc
      -- sin part via the phase bound at θ = −π/2
      have hsin_eq : Mform F.Phi p.T (muq κ q) (fun t => Real.sin (t * Real.log n))
          = Mform F.Phi p.T (muq κ q) (fun t => Real.cos (t * Real.log n + -(π / 2))) := by
        unfold Mform
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only []
        rw [show z.2 * Real.log n + -(π / 2) = z.2 * Real.log n - π / 2 by ring,
          Real.cos_sub_pi_div_two]
      have hMs := abs_Mform_cos_phase_le hT0 hF.Phi_contDiff hF.Phi_sq_integrable hμ hB hD
        hy.ne' (-(π / 2))
      rw [abs_of_pos hy] at hMs
      rw [← hsin_eq] at hMs
      -- |re|, |im| ≤ ‖c n‖ ≤ 1
      have hre : |(c n).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (hc.norm_le n)
      have him : |(c n).im| ≤ 1 := (Complex.abs_im_le_norm _).trans (hc.norm_le n)
      have hKb : (4 * (Cμ * p.l) + |Cd| / p.T * p.T) * S / Real.log n = K / Real.log n := by
        rw [hKdef]
      rw [abs_mul]
      have h1 : |(c n).re * Mform F.Phi p.T (muq κ q) (fun t => Real.cos (t * Real.log n))
          + (c n).im * Mform F.Phi p.T (muq κ q) (fun t => Real.sin (t * Real.log n))|
          ≤ 2 * (K / Real.log n) := by
        calc |(c n).re * Mform F.Phi p.T (muq κ q) (fun t => Real.cos (t * Real.log n))
            + (c n).im * Mform F.Phi p.T (muq κ q) (fun t => Real.sin (t * Real.log n))|
            ≤ |(c n).re| * |Mform F.Phi p.T (muq κ q) (fun t => Real.cos (t * Real.log n))|
              + |(c n).im| * |Mform F.Phi p.T (muq κ q) (fun t => Real.sin (t * Real.log n))| := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_mul, abs_mul]
          _ ≤ 1 * (K / Real.log n) + 1 * (K / Real.log n) := by
              refine add_le_add (mul_le_mul hre (hMc.trans (le_of_eq hKb)) (abs_nonneg _)
                zero_le_one) (mul_le_mul him (hMs.trans (le_of_eq hKb)) (abs_nonneg _) zero_le_one)
          _ = 2 * (K / Real.log n) := by ring
      calc |(-(1 / Real.pi) * ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))))| * |_|
          ≤ (1 / Real.pi * ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)))) * (2 * (K / Real.log n)) := by
            rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi),
              abs_of_nonneg ha0]
            exact mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 1 / Real.pi * (2 * K) * ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) / Real.log n) := by
            field_simp
  -- sum over n
  rw [Mform_mu_PXc_eq hF.Phi_contDiff.continuous hμ.continuous]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hosc).trans ?_)
  rw [← Finset.mul_sum]
  have hsum : ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) / Real.log n
      ≤ |Cc| * Real.sqrt p.X / p.L := by
    have h := hCc p.X hX2
    rw [hlogX] at h
    have e : ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) / Real.log n
        = ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Λ n : ℝ) / (Real.sqrt n * Real.log n) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hn).1
      rcases eq_or_lt_of_le hn1 with h1 | h2
      · rw [← h1]
        simp
      · have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
        have hs : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn0
        have hlg : (0:ℝ) < Real.log n := Real.log_pos (by exact_mod_cast h2)
        rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow]
        field_simp
    rw [e]
    exact h.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self Cc) (Real.sqrt_nonneg _)) hL.le)
  have hsum0 : 0 ≤ ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) / Real.log n :=
    Finset.sum_nonneg fun n _ => div_nonneg
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (Real.log_natCast_nonneg _)
  calc 1 / Real.pi * (2 * K) * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
        (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) / Real.log n
      ≤ 1 / Real.pi * (2 * ((4 * Cμ * p.l + |Cd|) * (2 * π * p.L)))
          * (|Cc| * Real.sqrt p.X / p.L) := by
        rw [hKeq]
        gcongr
    _ = 4 * (4 * Cμ * p.l + |Cd|) * |Cc| * Real.sqrt p.X := by field_simp; ring
    _ ≤ 4 * ((4 * Cμ + |Cd|) * p.l) * |Cc| * Real.sqrt p.X := by
        gcongr
        nlinarith [abs_nonneg Cd, hCμ]
    _ = 4 * (4 * Cμ + |Cd|) * |Cc| * (Zeta23.l p.T * Real.sqrt p.X) := by ring

end ThmE
end Zeta23
