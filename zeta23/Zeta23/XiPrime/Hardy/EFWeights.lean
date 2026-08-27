/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Hardy/EFWeights.lean — the pair-weight bounds at an ARBITRARY imaginary shift |Im z| ≤ 3/4
(namespace Zeta23.XiPrime.HW).  This file builds on the per-window layer `TestWeight.WindowAt` of
ExplicitFormula/TestWeight.lean (norm_phiHat_le / abs_re_mul_norm_phiHat_le at general z, paperFT_kfun, kfun regularity).

The W contour runs on Re s = c with c ∈ (1, 5/4], and the low-zero / pole terms need
the weight at points with |Re ρ − 1/2| ≤ 3/4 off the line; so the per-factor estimates
(‖φ̂(w)‖ ≤ (1+C)e^{|Im w|L/2}L/(1+(Re w)²), |Re w|‖φ̂(w)‖ ≤ 2C·e^{|Im w|L/2}/(1+(Re w)²)) are evaluated at any z with
|Im z| ≤ 3/4, using e^{|Im z|L/2} ≤ e^{3L/8} (L ≥ 1); the two exponential factors multiply to X^{3/4}.
  paperFT_kfun_bounds : ‖ĥ_{kfun}(z)‖ ≤ C·X^{3/4}·L²·K_{τ_k}(Re z)K_{τ_l}(Re z),
                        (|Re z−τ_k| + |Re z−τ_l|)·‖ĥ_{kfun}(z)‖ ≤ C·X^{3/4}·L·K_{τ_k}(Re z)K_{τ_l}(Re z);
  paperFT_comp_neg    : ĥ_{u ↦ k(−u)}(z) = ĥ_k(−z)   (re-export of TestWeight.paperFT_comp_neg);
  cauchyK_le_of_far   : K_a(x) ≤ 4/T² when |x − a| ≥ T/2;
  kfun_regular', kfun_facts : (W0) for kfun and for u ↦ kfun(−u), one threshold / one constant with the bounds.
-/
import Zeta23.XiPrime.ExplicitFormula.TestWeight
import Zeta23.XiPrime.ExplicitFormula.EntryError

open scoped ComplexConjugate
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Zeta23
namespace XiPrime
namespace HW

open Zeta23.WeilEF (Hfn)

/-! ## A. reflection of the paper Fourier transform -/

/-- ĥ_{u ↦ k(−u)}(z) = ĥ_k(−z). -/
theorem paperFT_comp_neg (k : ℝ → ℂ) (z : ℂ) : paperFT (fun u => k (-u)) z = paperFT k (-z) :=
  TestWeight.paperFT_comp_neg k z

/-! ## A'. the far Cauchy kernel (used by EFLowZeros and EFMain) -/

/-- if |x − a| ≥ T/2 > 0 then K_a(x) = (1 + (x−a)²)⁻¹ ≤ 4/T². -/
lemma cauchyK_le_of_far {a x T : ℝ} (hT : 0 < T) (h : T / 2 ≤ |x - a|) : cauchyK a x ≤ 4 / T ^ 2 := by
  unfold cauchyK
  have habs : (T / 2) ^ 2 ≤ (x - a) ^ 2 := by
    rw [← sq_abs (x - a)]
    exact pow_le_pow_left₀ (by linarith) h 2
  rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ## B. the factor and pair bounds at |Im| ≤ 3/4, from TestWeight.WindowAt -/

section Bounds
variable {P : Params} {T C : ℝ}

/-- factor bounds at w = z − a with |Im z| ≤ 3/4. -/
lemma factor_bounds_le (w : TestWeight.WindowAt P T C) (z : ℂ) (hz : |z.im| ≤ 3/4) (a : ℝ) :
    ‖P.phiHat T (z - a)‖
        ≤ (1 + C) * Real.exp (3/4 * (P.L T / 2)) * P.L T * (1 + (z.re - a) ^ 2)⁻¹ ∧
      |z.re - a| * ‖P.phiHat T (z - a)‖
        ≤ 2 * C * Real.exp (3/4 * (P.L T / 2)) * (1 + (z.re - a) ^ 2)⁻¹ := by
  have hL0 : 0 ≤ P.L T := le_trans zero_le_one w.one_le_L
  have hC0 : 0 ≤ C := w.C_nonneg
  have him : (z - a).im = z.im := by simp
  have hre : (z - a).re = z.re - a := by simp
  have hexp : Real.exp (|(z - a).im| * (P.L T / 2)) ≤ Real.exp (3/4 * (P.L T / 2)) := by
    rw [him]; exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hz (by linarith))
  have hK : 0 ≤ (1 + (z.re - a) ^ 2)⁻¹ := by positivity
  constructor
  · have h := w.norm_phiHat_le (z - a)
    rw [hre, div_eq_mul_inv] at h
    have h1 : 0 ≤ 1 + C := by linarith
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp h1) hL0) hK)
  · have h := w.abs_re_mul_norm_phiHat_le (z - a)
    rw [hre, div_eq_mul_inv] at h
    have h4 : 0 ≤ 2 * C := by positivity
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp h4) hK)

/-- pair bounds at |Im z| ≤ 3/4. -/
lemma pair_bounds_le (w : TestWeight.WindowAt P T C) (z : ℂ) (hz : |z.im| ≤ 3/4) (a b : ℝ) :
    ‖P.phiHat T (z - a) * P.phiHat T (z - b)‖
        ≤ (1 + C) ^ 2 * P.X T ^ (3/4 : ℝ) * P.L T ^ 2 * ((1 + (z.re - a) ^ 2)⁻¹ * (1 + (z.re - b) ^ 2)⁻¹) ∧
      (|z.re - a| + |z.re - b|) * ‖P.phiHat T (z - a) * P.phiHat T (z - b)‖
        ≤ 4 * C * (1 + C) * P.X T ^ (3/4 : ℝ) * P.L T * ((1 + (z.re - a) ^ 2)⁻¹ * (1 + (z.re - b) ^ 2)⁻¹) := by
  set L := P.L T with hLdef
  set E := Real.exp (3/4 * (L / 2)) with hEdef
  have hL1 : 1 ≤ L := w.one_le_L
  have hC0 : 0 ≤ C := w.C_nonneg
  have hE : 0 < E := Real.exp_pos _
  have hEX : E * E = P.X T ^ (3/4 : ℝ) := TestWeight.WindowAt.exp_mul_exp_eq_X_rpow P T
  obtain ⟨ha0, ha1⟩ := factor_bounds_le w z hz a
  obtain ⟨hb0, hb1⟩ := factor_bounds_le w z hz b
  set Ka := (1 + (z.re - a) ^ 2)⁻¹
  set Kb := (1 + (z.re - b) ^ 2)⁻¹
  have hKa : 0 ≤ Ka := by positivity
  have hKb : 0 ≤ Kb := by positivity
  set A := ‖P.phiHat T (z - a)‖
  set B := ‖P.phiHat T (z - b)‖
  have hB : 0 ≤ B := norm_nonneg _
  rw [norm_mul]
  constructor
  · calc A * B ≤ ((1 + C) * E * L * Ka) * ((1 + C) * E * L * Kb) := mul_le_mul ha0 hb0 hB (by positivity)
      _ = (1 + C) ^ 2 * (E * E) * L ^ 2 * (Ka * Kb) := by ring
      _ = (1 + C) ^ 2 * P.X T ^ (3/4 : ℝ) * L ^ 2 * (Ka * Kb) := by rw [hEX]
  · have h1 : |z.re - a| * (A * B) ≤ (2 * C * E * Ka) * ((1 + C) * E * L * Kb) := by
      calc |z.re - a| * (A * B) = (|z.re - a| * A) * B := by ring
        _ ≤ (2 * C * E * Ka) * ((1 + C) * E * L * Kb) := mul_le_mul ha1 hb0 hB (by positivity)
    have h2 : |z.re - b| * (A * B) ≤ ((1 + C) * E * L * Ka) * (2 * C * E * Kb) := by
      calc |z.re - b| * (A * B) = A * (|z.re - b| * B) := by ring
        _ ≤ ((1 + C) * E * L * Ka) * (2 * C * E * Kb) := mul_le_mul ha0 hb1 (by positivity) (by positivity)
    calc (|z.re - a| + |z.re - b|) * (A * B) = |z.re - a| * (A * B) + |z.re - b| * (A * B) := by ring
      _ ≤ (2 * C * E * Ka) * ((1 + C) * E * L * Kb) + ((1 + C) * E * L * Ka) * (2 * C * E * Kb) :=
          add_le_add h1 h2
      _ = 4 * C * (1 + C) * (E * E) * L * (Ka * Kb) := by ring
      _ = 4 * C * (1 + C) * P.X T ^ (3/4 : ℝ) * L * (Ka * Kb) := by rw [hEX]

end Bounds

/-! ## C. the consumer statements -/

/-- **the pair-weight bounds at any |Im z| ≤ 3/4.** -/
theorem paperFT_kfun_bounds {Pf : ℝ → Params} (hPf : FamilyHyps Pf) :
    ∃ C T₁ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₁ ≤ T → ∀ (k l : ℤ) (z : ℂ), |z.im| ≤ 3/4 →
      ‖paperFT (kfun (Pf T) T k l) z‖
          ≤ C * (Pf T).X T ^ (3/4 : ℝ) * (Pf T).L T ^ 2 *
            (cauchyK ((Pf T).tau T k) z.re * cauchyK ((Pf T).tau T l) z.re) ∧
      (|z.re - (Pf T).tau T k| + |z.re - (Pf T).tau T l|) * ‖paperFT (kfun (Pf T) T k l) z‖
          ≤ C * (Pf T).X T ^ (3/4 : ℝ) * (Pf T).L T *
            (cauchyK ((Pf T).tau T k) z.re * cauchyK ((Pf T).tau T l) z.re) := by
  obtain ⟨C, T₁, hC1, hW⟩ := hPf.windowAt
  have hC : 0 ≤ C := le_trans zero_le_one hC1
  refine ⟨4 * (1 + C) ^ 2, T₁, by positivity, fun T hT k l z hz => ?_⟩
  have w := hW T hT
  rw [w.paperFT_kfun k l z]
  obtain ⟨h1, h2⟩ := pair_bounds_le w z hz ((Pf T).tau T k) ((Pf T).tau T l)
  have hKK : 0 ≤ (Pf T).X T ^ (3/4 : ℝ) * (Pf T).L T ^ 2 *
      (cauchyK ((Pf T).tau T k) z.re * cauchyK ((Pf T).tau T l) z.re) := by
    have := cauchyK_nonneg ((Pf T).tau T k) z.re
    have := cauchyK_nonneg ((Pf T).tau T l) z.re
    have : 0 ≤ (Pf T).X T ^ (3/4 : ℝ) := Real.rpow_nonneg (Real.exp_pos _).le _
    positivity
  have hKK1 : 0 ≤ (Pf T).X T ^ (3/4 : ℝ) * (Pf T).L T *
      (cauchyK ((Pf T).tau T k) z.re * cauchyK ((Pf T).tau T l) z.re) := by
    have := cauchyK_nonneg ((Pf T).tau T k) z.re
    have := cauchyK_nonneg ((Pf T).tau T l) z.re
    have : 0 ≤ (Pf T).X T ^ (3/4 : ℝ) := Real.rpow_nonneg (Real.exp_pos _).le _
    have : 0 ≤ (Pf T).L T := le_trans zero_le_one w.one_le_L
    positivity
  have hc1 : (1 + C) ^ 2 ≤ 4 * (1 + C) ^ 2 := by nlinarith [sq_nonneg (1 + C)]
  have hc2 : 4 * C * (1 + C) ≤ 4 * (1 + C) ^ 2 := by nlinarith
  constructor
  · calc ‖(Pf T).phiHat T (z - (Pf T).tau T k) * (Pf T).phiHat T (z - (Pf T).tau T l)‖
        ≤ (1 + C) ^ 2 * ((Pf T).X T ^ (3/4 : ℝ) * (Pf T).L T ^ 2 *
            (cauchyK ((Pf T).tau T k) z.re * cauchyK ((Pf T).tau T l) z.re)) := by
          simpa only [cauchyK, mul_assoc] using h1
      _ ≤ 4 * (1 + C) ^ 2 * ((Pf T).X T ^ (3/4 : ℝ) * (Pf T).L T ^ 2 *
            (cauchyK ((Pf T).tau T k) z.re * cauchyK ((Pf T).tau T l) z.re)) :=
          mul_le_mul_of_nonneg_right hc1 hKK
      _ = _ := by ring
  · calc (|z.re - (Pf T).tau T k| + |z.re - (Pf T).tau T l|) *
          ‖(Pf T).phiHat T (z - (Pf T).tau T k) * (Pf T).phiHat T (z - (Pf T).tau T l)‖
        ≤ 4 * C * (1 + C) * ((Pf T).X T ^ (3/4 : ℝ) * (Pf T).L T *
            (cauchyK ((Pf T).tau T k) z.re * cauchyK ((Pf T).tau T l) z.re)) := by
          simpa only [cauchyK, mul_assoc] using h2
      _ ≤ 4 * (1 + C) ^ 2 * ((Pf T).X T ^ (3/4 : ℝ) * (Pf T).L T *
            (cauchyK ((Pf T).tau T k) z.re * cauchyK ((Pf T).tau T l) z.re)) :=
          mul_le_mul_of_nonneg_right hc2 hKK1
      _ = _ := by ring

/-- ĥ for the mirrored pair test function. -/
theorem paperFT_kfun_neg (P : Params) (T : ℝ) (k l : ℤ) (z : ℂ) :
    paperFT (fun u => kfun P T k l (-u)) z = paperFT (kfun P T k l) (-z) :=
  paperFT_comp_neg _ z

/-! ## D. (W0) for kfun and its mirror, same threshold as the bounds -/

/-- **(W0)** regularity and support of kfun and of u ↦ kfun(−u). -/
theorem kfun_regular' {Pf : ℝ → Params} (hPf : FamilyHyps Pf) :
    ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T → ∀ k l : ℤ,
      (ContDiff ℝ 2 (kfun (Pf T) T k l) ∧ HasCompactSupport (kfun (Pf T) T k l) ∧
        tsupport (kfun (Pf T) T k l) ⊆ Icc (-(Pf T).L T) ((Pf T).L T)) ∧
      (ContDiff ℝ 2 (fun u => kfun (Pf T) T k l (-u)) ∧ HasCompactSupport (fun u => kfun (Pf T) T k l (-u)) ∧
        tsupport (fun u => kfun (Pf T) T k l (-u)) ⊆ Icc (-(Pf T).L T) ((Pf T).L T)) ∧
      1 ≤ (Pf T).L T := by
  obtain ⟨C, T₁, _, hW⟩ := hPf.windowAt
  refine ⟨T₁, fun T hT k l => ?_⟩
  have w := hW T hT
  exact ⟨⟨w.kfun_contDiff k l, w.kfun_hasCompactSupport k l, w.kfun_tsupport k l⟩,
    ⟨w.kfun_neg_contDiff k l, w.kfun_neg_hasCompactSupport k l, w.kfun_neg_tsupport k l⟩, w.one_le_L⟩

/-- All weight facts under one threshold and one constant, in the form consumed by `Hardy/EFMain`. -/
theorem kfun_facts {Pf : ℝ → Params} (hPf : FamilyHyps Pf) :
    ∃ C T₁ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₁ ≤ T → ∀ k l : ℤ,
      (ContDiff ℝ 2 (kfun (Pf T) T k l) ∧ HasCompactSupport (kfun (Pf T) T k l) ∧
        tsupport (kfun (Pf T) T k l) ⊆ Icc (-(Pf T).L T) ((Pf T).L T)) ∧
      (ContDiff ℝ 2 (fun u => kfun (Pf T) T k l (-u)) ∧ HasCompactSupport (fun u => kfun (Pf T) T k l (-u)) ∧
        tsupport (fun u => kfun (Pf T) T k l (-u)) ⊆ Icc (-(Pf T).L T) ((Pf T).L T)) ∧
      1 ≤ (Pf T).L T ∧
      ∀ z : ℂ, |z.im| ≤ 3/4 →
        ‖paperFT (kfun (Pf T) T k l) z‖
            ≤ C * (Pf T).X T ^ (3/4 : ℝ) * (Pf T).L T ^ 2 *
              (cauchyK ((Pf T).tau T k) z.re * cauchyK ((Pf T).tau T l) z.re) ∧
        (|z.re - (Pf T).tau T k| + |z.re - (Pf T).tau T l|) * ‖paperFT (kfun (Pf T) T k l) z‖
            ≤ C * (Pf T).X T ^ (3/4 : ℝ) * (Pf T).L T *
              (cauchyK ((Pf T).tau T k) z.re * cauchyK ((Pf T).tau T l) z.re) := by
  obtain ⟨T₀, h0⟩ := kfun_regular' hPf
  obtain ⟨C, T₁, hC, h1⟩ := paperFT_kfun_bounds hPf
  refine ⟨C, max T₀ T₁, hC, fun T hT k l => ?_⟩
  obtain ⟨a, b, c⟩ := h0 T (le_trans (le_max_left _ _) hT) k l
  exact ⟨a, b, c, fun z hz => h1 T (le_trans (le_max_right _ _) hT) k l z hz⟩

end HW
end XiPrime
end Zeta23
