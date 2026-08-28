/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization.

Zeta23/XiPrime/PrimeSide/Cross.lean — generalised-coefficient prime side:
[prop:cross](i) for the density P_c with ARBITRARY complex coefficients:
    |𝓜[μ, P_c]| ≤ C · l · L · S₁(c),      S₁(c) = Σ_{N≤X} ‖c_N‖/√N,
for T ≥ T₀ (C, T₀ depend on H-Γ only), provided c 1 = 0.

Route = Zeta23/ThmE/CrossMuPChi.lean (double IBP, oscillatory bounds abs_Mform_cos_le /
abs_Mform_cos_phase_le of CrossMuPCore) with Λ(n)·χ(n) ↦ c_N/√N and the per-N saving 1/log N
replaced by 1/log 2 (N ≥ 2; the N = 1 term is killed by c 1 = 0).  The ζ/χ proofs use the finer
Σ Λ(n)/(√n log n) ≪ √X/log X to get l√X; here the coefficient side only has the crude
S₁ ≪ √X·l, and l·L·S₁ ≪ L·l²·√X is still o(T·L·l²) — [XF′] Remark 7.2.
-/
import Zeta23.XiPrime.PrimeSide.Density
import Zeta23.PrimeSideA.CrossMuPCore

noncomputable section

open Real Filter MeasureTheory Set Finset
open scoped BigOperators

namespace Zeta23
namespace XiPrime

open PrimeSide

/-- `𝓜[u, P_c]` as the finite cos/sin-split sum (mirror of ThmE.Mform_mu_PXc_eq). -/
lemma Mform_u_Pc_eq {Φ : ℝ → ℝ} (hΦ : Continuous Φ) {u : ℝ → ℝ} (hu : Continuous u)
    (c : ℕ → ℂ) (X T : ℝ) :
    Mform Φ T u (Pc X c)
      = ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ((1 / Real.pi) * (Real.sqrt n)⁻¹)
          * ((c n).re * Mform Φ T u (fun t => Real.cos (t * Real.log n))
             + (c n).im * Mform Φ T u (fun t => Real.sin (t * Real.log n))) := by
  unfold Mform
  have h1 : (fun q : ℝ × ℝ => Φ (q.1 - q.2) ^ 2 * u q.1 * Pc X c q.2)
      = fun q => ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ((1 / Real.pi) * (Real.sqrt n)⁻¹)
          * ((c n).re * (Φ (q.1 - q.2) ^ 2 * u q.1 * Real.cos (q.2 * Real.log n))
             + (c n).im * (Φ (q.1 - q.2) ^ 2 * u q.1 * Real.sin (q.2 * Real.log n))) := by
    funext q
    unfold Pc
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [div_eq_mul_inv]
    ring
  rw [h1, integral_finset_sum]
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

/-- **[prop:cross](i) for P_c** with arbitrary complex coefficients (`c 1 = 0`):
`|𝓜[μ, P_c]| ≤ C · l · L · S₁(c; X)` for `T ≥ T₀`, constants depending on H-Γ only. -/
theorem cross_muPc {cϱ lam : ℝ} (hΓ : Zeta23.GammaFacts) (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (c : ℕ → ℂ), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCore cϱ p F → c 1 = 0 →
      |Mform F.Phi p.T Zeta23.mu (Pc p.X c)| ≤ C * (p.l * p.L * S1 c p.X) := by
  obtain ⟨T₁, hT₁⟩ := mu_abs_le_l hΓ
  obtain ⟨Cd, hCd⟩ := hΓ.deriv_bound
  have hμ : ContDiff ℝ 1 Zeta23.mu := hΓ.smooth.of_le (by exact_mod_cast le_top)
  refine ⟨8 * (4 + |Cd|) / Real.log 2, max T₁ 1, fun p F c hplam hT hF hc1 => ?_⟩
  have hT₁' : T₁ ≤ p.T := (le_max_left _ _).trans hT
  have hT1 : 1 ≤ p.T := (le_max_right _ _).trans hT
  have hT0 : 0 ≤ p.T := by linarith
  have hl1 : 1 ≤ p.l := hF.one_le_l
  have hL := hF.L_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- sup bounds for μ, μ' on I
  have hB : ∀ τ ∈ Set.Icc p.T (2 * p.T), |Zeta23.mu τ| ≤ p.l := hT₁ p hT₁'
  have hD : ∀ τ ∈ Set.Icc p.T (2 * p.T), |deriv Zeta23.mu τ| ≤ |Cd| / p.T := by
    intro τ hτ
    have hτ1 : 1 ≤ |τ| := by rw [abs_of_nonneg (by linarith [hτ.1])]; linarith [hτ.1]
    refine (hCd τ hτ1).trans ?_
    rw [abs_of_nonneg (by linarith [hτ.1])]
    calc Cd / τ ≤ |Cd| / τ := div_le_div_of_nonneg_right (le_abs_self _) (by linarith [hτ.1])
      _ ≤ |Cd| / p.T := div_le_div_of_nonneg_left (abs_nonneg _) (by linarith) hτ.1
  set S : ℝ := ∫ x, F.Phi x ^ 2 with hSdef
  have hS : S ≤ 2 * π * p.L := hF.integral_Phi_sq_le
  have hS0 : 0 ≤ S := integral_nonneg fun x => sq_nonneg _
  set K : ℝ := (4 * p.l + |Cd| / p.T * p.T) * S with hKdef
  have hKeq : K = (4 * p.l + |Cd|) * S := by
    have hTne : p.T ≠ 0 := by linarith
    rw [hKdef, div_mul_cancel₀ _ hTne]
  have hK0 : 0 ≤ K := by rw [hKeq]; positivity
  -- per-n bound
  have hosc : ∀ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
      |((1 / Real.pi) * (Real.sqrt n)⁻¹)
          * ((c n).re * Mform F.Phi p.T Zeta23.mu (fun t => Real.cos (t * Real.log n))
             + (c n).im * Mform F.Phi p.T Zeta23.mu (fun t => Real.sin (t * Real.log n)))|
        ≤ (2 * K / (Real.pi * Real.log 2)) * (‖c n‖ / Real.sqrt n) := by
    intro n hn
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn1 : n = 1 := by
        have : 0 < n := (Finset.mem_Ioc.mp hn).1
        omega
      subst hn1
      simp [hc1]
    · have hy : 0 < Real.log n := Real.log_pos (by exact_mod_cast h2)
      have hylog2 : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast h2)
      have hMc := abs_Mform_cos_le hT0 hF.Phi_contDiff hF.Phi_sq_integrable hμ hB hD hy.ne'
      rw [abs_of_pos hy] at hMc
      have hsin_eq : Mform F.Phi p.T Zeta23.mu (fun t => Real.sin (t * Real.log n))
          = Mform F.Phi p.T Zeta23.mu (fun t => Real.cos (t * Real.log n + -(π / 2))) := by
        unfold Mform
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only []
        rw [show z.2 * Real.log n + -(π / 2) = z.2 * Real.log n - π / 2 by ring,
          Real.cos_sub_pi_div_two]
      have hMs := abs_Mform_cos_phase_le hT0 hF.Phi_contDiff hF.Phi_sq_integrable hμ hB hD
        hy.ne' (-(π / 2))
      rw [abs_of_pos hy, ← hsin_eq] at hMs
      have hre : |(c n).re| ≤ ‖c n‖ := Complex.abs_re_le_norm _
      have him : |(c n).im| ≤ ‖c n‖ := Complex.abs_im_le_norm _
      have hKn : (4 * p.l + |Cd| / p.T * p.T) * S / Real.log n ≤ K / Real.log 2 := by
        rw [← hKdef]
        exact div_le_div_of_nonneg_left hK0 hlog2 hylog2
      have h1 : |(c n).re * Mform F.Phi p.T Zeta23.mu (fun t => Real.cos (t * Real.log n))
          + (c n).im * Mform F.Phi p.T Zeta23.mu (fun t => Real.sin (t * Real.log n))|
          ≤ 2 * ‖c n‖ * (K / Real.log 2) := by
        calc |(c n).re * Mform F.Phi p.T Zeta23.mu (fun t => Real.cos (t * Real.log n))
            + (c n).im * Mform F.Phi p.T Zeta23.mu (fun t => Real.sin (t * Real.log n))|
            ≤ |(c n).re| * |Mform F.Phi p.T Zeta23.mu (fun t => Real.cos (t * Real.log n))|
              + |(c n).im| * |Mform F.Phi p.T Zeta23.mu (fun t => Real.sin (t * Real.log n))| := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_mul, abs_mul]
          _ ≤ ‖c n‖ * (K / Real.log 2) + ‖c n‖ * (K / Real.log 2) :=
              add_le_add (mul_le_mul hre (hMc.trans hKn) (abs_nonneg _) (norm_nonneg _))
                (mul_le_mul him (hMs.trans hKn) (abs_nonneg _) (norm_nonneg _))
          _ = 2 * ‖c n‖ * (K / Real.log 2) := by ring
      have hsq0 : 0 ≤ (Real.sqrt (n:ℝ))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 / Real.pi) * (Real.sqrt n)⁻¹)]
      calc (1 / Real.pi) * (Real.sqrt n)⁻¹ * |_| ≤ (1 / Real.pi) * (Real.sqrt n)⁻¹
            * (2 * ‖c n‖ * (K / Real.log 2)) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (2 * K / (Real.pi * Real.log 2)) * (‖c n‖ / Real.sqrt n) := by
            field_simp
  -- sum over n
  rw [Mform_u_Pc_eq hF.Phi_contDiff.continuous hμ.continuous]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hosc).trans ?_)
  rw [← Finset.mul_sum]
  change 2 * K / (π * Real.log 2) * S1 c p.X ≤ _
  have hS1 := S1_nonneg c p.X
  have hπ3 := Real.pi_gt_three
  calc 2 * K / (π * Real.log 2) * S1 c p.X
      ≤ 2 * ((4 * p.l + |Cd|) * (2 * π * p.L)) / (π * Real.log 2) * S1 c p.X := by
        rw [hKeq]; gcongr
    _ = 4 * (4 * p.l + |Cd|) / Real.log 2 * (p.L * S1 c p.X) := by
        field_simp <;> ring
    _ ≤ 4 * ((4 + |Cd|) * (2 * p.l)) / Real.log 2 * (p.L * S1 c p.X) := by
        gcongr
        nlinarith [abs_nonneg Cd]
    _ = 8 * (4 + |Cd|) / Real.log 2 * (p.l * p.L * S1 c p.X) := by
        field_simp
        ring

end XiPrime
end Zeta23
