/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ExplicitFormula/FamilyFacts.lean — per-height facts of a FamilyHyps height-family, packaged, and the
power/log absorption used in the final (EF4) bound.
-/
import Zeta23.XiPrime.ExplicitFormula
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Complex Set Filter Topology MeasureTheory

noncomputable section

namespace Zeta23
namespace XiPrime

/-- **Per-height facts of a FamilyHyps family.**  For T ≥ T₁: λ fixed in (0,1); L = λ·l(T) with
1 ≤ L ≤ log T (so 0 < L); X = e^L with X^{3/4} ≤ T^{3λ/4}; the window φ_T is C² as a complex-valued function
and supported in [−L/2, L/2]; and (the C) it is even, |φ| ≤ 1, ‖φ^{(j)}‖₁ ≤ C for j = 1,2,3. -/
theorem FamilyHyps.perT {Pf : ℝ → Params} (hPf : FamilyHyps Pf) :
    ∃ lam C T₁ : ℝ, 0 < lam ∧ lam < 1 ∧ 0 ≤ C ∧ 0 < T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
      (Pf T).lam = lam ∧
      1 ≤ (Pf T).L T ∧
      (Pf T).L T = lam * l T ∧
      (Pf T).X T = Real.exp ((Pf T).L T) ∧
      (Pf T).L T ≤ Real.log T ∧
      (Pf T).X T ^ (3 / 4 : ℝ) ≤ T ^ (3 * lam / 4) ∧
      ContDiff ℝ 2 (fun u : ℝ => (((Pf T).phi T u : ℝ) : ℂ)) ∧
      tsupport ((Pf T).phi T) ⊆ Icc (-((Pf T).L T / 2)) ((Pf T).L T / 2) ∧
      0 < (Pf T).L T ∧
      (∀ u : ℝ, (Pf T).phi T (-u) = (Pf T).phi T u) ∧
      (∀ u : ℝ, |(Pf T).phi T u| ≤ 1) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ 3 →
        Integrable (iteratedDeriv j ((Pf T).phi T)) ∧ ∫ u : ℝ, |iteratedDeriv j ((Pf T).phi T) u| ≤ C) := by
  obtain ⟨lam, hlam0, hlam1, hlam⟩ := hPf.lam_const
  obtain ⟨C, T₀, hwin⟩ := hPf.window
  -- C ≥ 0 is forced by the j = 1 bound at any admissible T
  have hC0 : 0 ≤ C := by
    have h := (hwin (max T₀ 0) (le_max_left _ _)).2.2.2.2 1 le_rfl (by norm_num)
    exact le_trans (integral_nonneg fun u => abs_nonneg _) h.2
  set T₁ : ℝ := max (max T₀ 1) (2 * Real.pi * Real.exp (1 / lam)) with hT₁
  have h2π : 0 < 2 * Real.pi := by positivity
  refine ⟨lam, C, T₁, hlam0, hlam1, hC0, ?_, fun T hT => ?_⟩
  · exact lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_max_left _ _))
  have hT₀ : T₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT1 : 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTpos : 0 < T := by linarith
  have hTe : 2 * Real.pi * Real.exp (1 / lam) ≤ T := le_trans (le_max_right _ _) hT
  obtain ⟨hcd, hsupp, heven, hle1, hderiv⟩ := hwin T hT₀
  have hLdef : (Pf T).L T = lam * l T := by rw [Params.L, hlam T]
  -- l T ≥ 1/lam
  have hl : 1 / lam ≤ l T := by
    rw [l, Real.le_log_iff_exp_le (by positivity), le_div_iff₀ h2π]
    linarith
  have hL1 : 1 ≤ (Pf T).L T := by
    rw [hLdef]
    have := mul_le_mul_of_nonneg_left hl hlam0.le
    rw [mul_one_div_cancel hlam0.ne'] at this
    exact this
  have hlT : l T ≤ Real.log T := by
    rw [l, Real.log_div hTpos.ne' h2π.ne']
    have : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    linarith
  have hl0 : 0 ≤ l T := le_trans (by positivity) hl
  have hLlog : (Pf T).L T ≤ Real.log T := by
    rw [hLdef]
    calc lam * l T ≤ 1 * l T := mul_le_mul_of_nonneg_right hlam1.le hl0
      _ = l T := one_mul _
      _ ≤ Real.log T := hlT
  have hX : (Pf T).X T = Real.exp ((Pf T).L T) := rfl
  have hX34 : (Pf T).X T ^ (3 / 4 : ℝ) ≤ T ^ (3 * lam / 4) := by
    rw [hX, ← Real.exp_mul, Real.rpow_def_of_pos hTpos]
    apply Real.exp_le_exp.mpr
    rw [hLdef]
    have := mul_le_mul_of_nonneg_left hlT hlam0.le
    nlinarith
  have hcd2 : ContDiff ℝ 2 (fun u : ℝ => (((Pf T).phi T u : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hcd.of_le (by norm_num))
  exact ⟨hlam T, hL1, hLdef, hX, hLlog, hX34, hcd2, hsupp, by linarith, heven, hle1, hderiv⟩

/-- log T ≤ (1/ε)·T^ε for T ≥ 0 (Mathlib's Real.log_le_rpow_div, repackaged). -/
lemma log_le_const_mul_rpow {ε : ℝ} (hε : 0 < ε) {T : ℝ} (hT : 0 ≤ T) :
    Real.log T ≤ (1 / ε) * T ^ ε := by
  have := Real.log_le_rpow_div hT hε
  rw [div_eq_mul_one_div, mul_comm] at this
  exact this

/-- **Power/log absorption.**  With δ := (1 − 3λ/4)/2 > 0 (λ < 1):
  T^{3λ/4}·log²T·A/(T·log T) ≤ C·T^{−δ}   and   T^{3λ/4}·log²T·A/T² ≤ C·T^{−δ}/T   for T ≥ 2. -/
theorem pow_log_absorb (lam : ℝ) (hlam : lam < 1) (hlam0 : 0 < lam) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C T₁ : ℝ, 0 < C ∧ ∀ T : ℝ, T₁ ≤ T →
      T ^ (3 * lam / 4) * Real.log T ^ 2 * A / (T * Real.log T)
          ≤ C * T ^ (-((1 - 3 * lam / 4) / 2)) ∧
      T ^ (3 * lam / 4) * Real.log T ^ 2 * A / T ^ 2
          ≤ C * T ^ (-((1 - 3 * lam / 4) / 2)) / T := by
  set δ : ℝ := (1 - 3 * lam / 4) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; nlinarith
  -- log T ≤ (1/δ) T^δ and log² T ≤ (2/δ)² T^δ
  refine ⟨A * (1 / δ) + A * (2 / δ) ^ 2 + 1, 2, by positivity, fun T hT => ?_⟩
  have hTpos : 0 < T := by linarith
  have hlog0 : 0 < Real.log T := Real.log_pos (by linarith)
  have hlog1 : Real.log T ≤ (1 / δ) * T ^ δ := log_le_const_mul_rpow hδ0 hTpos.le
  have hlog2 : Real.log T ^ 2 ≤ (2 / δ) ^ 2 * T ^ δ := by
    have h := log_le_const_mul_rpow (ε := δ / 2) (by positivity) hTpos.le
    have h' : Real.log T ^ 2 ≤ ((1 / (δ / 2)) * T ^ (δ / 2)) ^ 2 :=
      pow_le_pow_left₀ hlog0.le h 2
    calc Real.log T ^ 2 ≤ ((1 / (δ / 2)) * T ^ (δ / 2)) ^ 2 := h'
      _ = (2 / δ) ^ 2 * (T ^ (δ / 2)) ^ 2 := by rw [mul_pow]; congr 1; field_simp
      _ = (2 / δ) ^ 2 * T ^ δ := by
          rw [← Real.rpow_natCast (T ^ (δ / 2)) 2, ← Real.rpow_mul hTpos.le]
          push_cast
          ring_nf
  -- exponent bookkeeping: 3λ/4 = 1 − 2δ
  have hexp : 3 * lam / 4 = 1 - 2 * δ := by rw [hδ]; ring
  have hTδ : 0 < T ^ δ := Real.rpow_pos_of_pos hTpos _
  have hTnegδ : T ^ (-δ) = (T ^ δ)⁻¹ := Real.rpow_neg hTpos.le δ
  have hpow1 : T ^ (3 * lam / 4) = T * (T ^ δ)⁻¹ * (T ^ δ)⁻¹ := by
    rw [hexp, show (1 : ℝ) - 2 * δ = 1 + (-δ) + (-δ) by ring, Real.rpow_add hTpos,
      Real.rpow_add hTpos, Real.rpow_one, hTnegδ]
  constructor
  · -- T^{3λ/4} log²T A /(T log T) = A · (T^δ)⁻¹ (T^δ)⁻¹ · log T
    have e : T ^ (3 * lam / 4) * Real.log T ^ 2 * A / (T * Real.log T)
        = A * ((T ^ δ)⁻¹ * ((T ^ δ)⁻¹ * Real.log T)) := by
      rw [hpow1]
      field_simp
    rw [e, show -((1 - 3 * lam / 4) / 2) = -δ by rw [hδ], hTnegδ]
    have h1 : (T ^ δ)⁻¹ * Real.log T ≤ 1 / δ := by
      rw [inv_mul_le_iff₀ hTδ]
      linarith
    have h2 : (T ^ δ)⁻¹ * ((T ^ δ)⁻¹ * Real.log T) ≤ (T ^ δ)⁻¹ * (1 / δ) :=
      mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hTδ.le)
    calc A * ((T ^ δ)⁻¹ * ((T ^ δ)⁻¹ * Real.log T)) ≤ A * ((T ^ δ)⁻¹ * (1 / δ)) :=
          mul_le_mul_of_nonneg_left h2 hA
      _ = (A * (1 / δ)) * (T ^ δ)⁻¹ := by ring
      _ ≤ (A * (1 / δ) + A * (2 / δ) ^ 2 + 1) * (T ^ δ)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hTδ.le)
          nlinarith [sq_nonneg (2 / δ)]
  · -- T^{3λ/4} log²T A / T² = A · (T^δ)⁻¹ (T^δ)⁻¹ · log²T / T
    have e : T ^ (3 * lam / 4) * Real.log T ^ 2 * A / T ^ 2
        = A * ((T ^ δ)⁻¹ * ((T ^ δ)⁻¹ * Real.log T ^ 2)) / T := by
      rw [hpow1]
      field_simp
    rw [e, show -((1 - 3 * lam / 4) / 2) = -δ by rw [hδ], hTnegδ]
    apply div_le_div_of_nonneg_right _ hTpos.le
    have h1 : (T ^ δ)⁻¹ * Real.log T ^ 2 ≤ (2 / δ) ^ 2 := by
      rw [inv_mul_le_iff₀ hTδ]
      linarith
    have h2 : (T ^ δ)⁻¹ * ((T ^ δ)⁻¹ * Real.log T ^ 2) ≤ (T ^ δ)⁻¹ * (2 / δ) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hTδ.le)
    calc A * ((T ^ δ)⁻¹ * ((T ^ δ)⁻¹ * Real.log T ^ 2)) ≤ A * ((T ^ δ)⁻¹ * (2 / δ) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 hA
      _ = (A * (2 / δ) ^ 2) * (T ^ δ)⁻¹ := by ring
      _ ≤ (A * (1 / δ) + A * (2 / δ) ^ 2 + 1) * (T ^ δ)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hTδ.le)
          nlinarith [hδ0]

end XiPrime
end Zeta23
