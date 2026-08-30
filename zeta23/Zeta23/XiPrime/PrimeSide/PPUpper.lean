/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization.

Zeta23/XiPrime/PrimeSide/PPUpper.lean — the Frobenius UPPER bound for the P-part Gram
matrix of an arbitrary Dirichlet polynomial (consumed by Lemma 6.1, where it is applied to the
re-expansion coefficients e_r of [XF′] §6).

  Σ_{k,l<d} Q_{kl}(e)²  ≤  K·L²·( T·L·Σ‖e‖²/N + L·Σ‖e‖² + L·S₁(e)² + L·l·log l·(l + S₁(e))² ),
  Q_{kl}(e) := ∫ φ̂(τ−τ_k) φ̂(τ−τ_l) P_e(X;τ) dτ = GentryNu (Pc p.X e) p F k l,
for T ≥ T₀ under LocalHypsCore, e 1 = 0.  Route: [lem:ends] for the density ν = P_e alone
(lem_ends_nu with B = l + S₁/π) turns Σ Q² into L²·𝓜[P_e,P_e] + O(L³ l log l B²), and [prop:PP]
for P_e (PPInput) with g ≤ L bounds 𝓜[P_e,P_e].
-/
import Zeta23.XiPrime.PrimeSide.Concrete

noncomputable section

open Real Filter MeasureTheory Set
open scoped BigOperators

namespace Zeta23
namespace XiPrime

open PrimeSide

/-- NuBound for `P_e` (regime `l ≥ 0`). -/
lemma nuBound_Pc' {p : Setting} (hl : 0 ≤ p.l) (e : ℕ → ℂ) :
    NuBound p (p.l + (1 / π) * S1 e p.X) (Pc p.X e) := by
  intro τ
  have h1 := Pc_abs_le p.X e τ
  have h2 : 0 ≤ max (Real.log (|τ| / (4 * p.T))) 0 := le_max_right _ _
  linarith

/-- `Σ ‖e‖²/N · g(log N) ≤ L · Σ ‖e‖²/N` since `0 ≤ g ≤ A_φ ≤ L`. -/
lemma sumW2g_le {cϱ : ℝ} {p : Setting} {F : LocalFun} (hF : LocalHypsCore cϱ p F) (e : ℕ → ℂ) :
    sumW2g e p.X F.g ≤ p.L * sumSqDivW e p.X := by
  unfold sumW2g sumSqDivW
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  have hg : F.g (Real.log n) ≤ p.L := by
    refine (hF.g_le_Aphi _).trans ((hF.Aphi_le _).trans ?_)
    refine max_le ?_ hF.L_pos.le
    linarith [abs_nonneg (Real.log (n:ℝ))]
  have h0 : 0 ≤ ‖e n‖ ^ 2 / n := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  calc ‖e n‖ ^ 2 / n * F.g (Real.log n) ≤ ‖e n‖ ^ 2 / n * p.L :=
        mul_le_mul_of_nonneg_left hg h0
    _ = p.L * (‖e n‖ ^ 2 / n) := by ring

set_option maxHeartbeats 1600000 in
/-- **Frobenius upper bound for the P-part Gram matrix of an arbitrary Dirichlet polynomial.** -/
theorem frobSq_Ppart_le (hPP : PPInput) {C : ℝ} (hMV : Zeta23.MVHilbert C) (hC : 0 < C)
    (cϱ lam : ℝ) (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ K T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (e : ℕ → ℂ), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCore cϱ p F → e 1 = 0 →
      ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu (Pc p.X e) p F k l ^ 2
        ≤ K * p.L ^ 2 * (p.T * p.L * sumSqDivW e p.X + p.L * sumSqW e p.X
            + p.L * S1 e p.X ^ 2 + p.L * p.l * Real.log p.l * (p.l + S1 e p.X) ^ 2) := by
  obtain ⟨Kpp, hK⟩ := hPP C cϱ hMV hC
  obtain ⟨Ce, T₁, hCe⟩ := lem_ends_nu cϱ lam
  refine ⟨max (1 / π + max Kpp 0) (max Ce 0) + 1, max T₁ 1, fun p F e hplam hT hF he1 => ?_⟩
  have hT1 : 1 ≤ p.T := (le_max_right _ _).trans hT
  have hT₁ : T₁ ≤ p.T := (le_max_left _ _).trans hT
  have hL := hF.L_pos
  have hl1 := hF.one_le_l
  have hl0 : 0 ≤ p.l := by linarith
  have hS := S1_nonneg e p.X
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  -- ends for ν = P_e
  set B := p.l + (1 / π) * S1 e p.X with hB
  have hlB : p.l ≤ B := by
    have : 0 ≤ (1 / π) * S1 e p.X := by positivity
    rw [hB]; linarith
  have hends := hCe p F B (Pc p.X e) hplam hT₁ hF (Pc_continuous p.X e) (nuBound_Pc' hl0 e) hlB
  -- PP for P_e
  have hpp := hK p F e hF hT1 he1
  have hg := sumW2g_le hF e
  -- sizes
  have h1 : 0 ≤ sumSqDivW e p.X := sumSqDivW_nonneg _ _
  have h2 : 0 ≤ sumSqW e p.X := sumSqW_nonneg _ _
  have hlog : 0 ≤ Real.log p.l := Real.log_nonneg hl1
  -- the abstract inequality: L² · (M + E) with M ≤ (T/π) L S + Kpp L (...), |E| ≤ Ce L l log l B²
  have hB2 : B ^ 2 ≤ (p.l + S1 e p.X) ^ 2 := by
    apply pow_le_pow_left₀ (by rw [hB]; positivity)
    rw [hB]
    have : (1 / π) * S1 e p.X ≤ S1 e p.X := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hπ]; nlinarith
    linarith
  have key : (p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu (Pc p.X e) p F k l ^ 2
      ≤ (1 / π + max Kpp 0) * (p.T * p.L * sumSqDivW e p.X + p.L * sumSqW e p.X
          + p.L * S1 e p.X ^ 2) + max Ce 0 * (p.L * p.l * Real.log p.l * (p.l + S1 e p.X) ^ 2) := by
    have e1 := (abs_le.1 hends).2
    have e2 := (abs_le.1 hpp).2
    -- MtotalNu (Pc) p F = Mform F.Phi p.T Pc Pc
    have hM : MtotalNu (Pc p.X e) p F = Mform F.Phi p.T (Pc p.X e) (Pc p.X e) := rfl
    rw [hM] at e1
    have hx1 : 0 ≤ p.L * p.l * Real.log p.l * B ^ 2 := by positivity
    have hx2 : 0 ≤ p.L * (sumSqDivW e p.X + sumSqW e p.X + S1 e p.X ^ 2) := by positivity
    have hCe' : Ce * (p.L * p.l * Real.log p.l * B ^ 2)
        ≤ max Ce 0 * (p.L * p.l * Real.log p.l * (p.l + S1 e p.X) ^ 2) := by
      calc Ce * (p.L * p.l * Real.log p.l * B ^ 2) ≤ max Ce 0 * (p.L * p.l * Real.log p.l * B ^ 2) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hx1
        _ ≤ max Ce 0 * (p.L * p.l * Real.log p.l * (p.l + S1 e p.X) ^ 2) := by
            gcongr
    have hK' : Kpp * p.L * (sumSqDivW e p.X + sumSqW e p.X + S1 e p.X ^ 2)
        ≤ max Kpp 0 * (p.T * p.L * sumSqDivW e p.X + p.L * sumSqW e p.X + p.L * S1 e p.X ^ 2) := by
      calc Kpp * p.L * (sumSqDivW e p.X + sumSqW e p.X + S1 e p.X ^ 2)
          ≤ max Kpp 0 * (p.L * (sumSqDivW e p.X + sumSqW e p.X + S1 e p.X ^ 2)) := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hx2
        _ ≤ max Kpp 0 * (p.T * p.L * sumSqDivW e p.X + p.L * sumSqW e p.X + p.L * S1 e p.X ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
            nlinarith [mul_nonneg hL.le h1]
    have hmain : p.T / π * sumW2g e p.X F.g ≤ (1 / π) * (p.T * p.L * sumSqDivW e p.X) := by
      have : p.T / π * sumW2g e p.X F.g ≤ p.T / π * (p.L * sumSqDivW e p.X) :=
        mul_le_mul_of_nonneg_left hg (by positivity)
      refine this.trans (le_of_eq ?_); ring
    have hmain' : (1 / π) * (p.T * p.L * sumSqDivW e p.X)
        ≤ (1 / π) * (p.T * p.L * sumSqDivW e p.X + p.L * sumSqW e p.X + p.L * S1 e p.X ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg hL.le h2, mul_nonneg hL.le (sq_nonneg (S1 e p.X))]
    linarith [e1, e2, hmain, hmain', hK', hCe']
  have hfin : ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu (Pc p.X e) p F k l ^ 2
      = p.L ^ 2 * ((p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu (Pc p.X e) p F k l ^ 2) := by
    field_simp
  rw [hfin]
  have hbr : 0 ≤ p.T * p.L * sumSqDivW e p.X + p.L * sumSqW e p.X
      + p.L * S1 e p.X ^ 2 + p.L * p.l * Real.log p.l * (p.l + S1 e p.X) ^ 2 := by positivity
  have hm1 : 0 ≤ 1 / π + max Kpp 0 := by positivity
  have hm2 : 0 ≤ max Ce 0 := le_max_right _ _
  calc p.L ^ 2 * ((p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu (Pc p.X e) p F k l ^ 2)
      ≤ p.L ^ 2 * ((1 / π + max Kpp 0) * (p.T * p.L * sumSqDivW e p.X + p.L * sumSqW e p.X
          + p.L * S1 e p.X ^ 2) + max Ce 0 * (p.L * p.l * Real.log p.l * (p.l + S1 e p.X) ^ 2)) :=
        mul_le_mul_of_nonneg_left key (sq_nonneg _)
    _ ≤ (max (1 / π + max Kpp 0) (max Ce 0) + 1) * p.L ^ 2 * (p.T * p.L * sumSqDivW e p.X
          + p.L * sumSqW e p.X + p.L * S1 e p.X ^ 2
          + p.L * p.l * Real.log p.l * (p.l + S1 e p.X) ^ 2) := by
        have hA : 0 ≤ p.T * p.L * sumSqDivW e p.X + p.L * sumSqW e p.X + p.L * S1 e p.X ^ 2 := by
          positivity
        have hE : 0 ≤ p.L * p.l * Real.log p.l * (p.l + S1 e p.X) ^ 2 := by positivity
        have hmax1 : 1 / π + max Kpp 0 ≤ max (1 / π + max Kpp 0) (max Ce 0) + 1 := by
          linarith [le_max_left (1 / π + max Kpp 0) (max Ce 0)]
        have hmax2 : max Ce 0 ≤ max (1 / π + max Kpp 0) (max Ce 0) + 1 := by
          linarith [le_max_right (1 / π + max Kpp 0) (max Ce 0)]
        have hL2 : 0 ≤ p.L ^ 2 := sq_nonneg _
        nlinarith [mul_le_mul_of_nonneg_right hmax1 hA, mul_le_mul_of_nonneg_right hmax2 hE,
          mul_nonneg hL2 hA, mul_nonneg hL2 hE]

end XiPrime
end Zeta23
