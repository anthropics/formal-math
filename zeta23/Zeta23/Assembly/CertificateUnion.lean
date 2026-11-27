/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.Assembly.Certificate
import Zeta23.Assembly.SeamUnion

/-!
# Asymptotic moment certificate for the simple-or-on-line union
-/

open Filter Asymptotics Topology Real RHLinalg

noncomputable section

namespace Zeta23.Assembly

/-- Fixed-height algebra for the union seam. -/
theorem union_lower_moment
    {lower N NII trGh frGh B κ R₁ R₂ : ℝ} (hB : 0 ≤ B)
    (h0 : 2 * ZeroSide.unionC * trGh - frGh - ZeroSide.unionQ * N -
        2 * ZeroSide.unionQ * NII -
        B * (2 * ZeroSide.unionC + 2 * Real.sqrt frGh + B)
      ≤ ZeroSide.unionQ * lower)
    (htr : N - R₁ ≤ trGh) (hfr : frGh ≤ κ * N + R₂) :
    (2 * ZeroSide.unionC - ZeroSide.unionQ - κ) * N -
        (2 * ZeroSide.unionC * R₁ + R₂ + 2 * ZeroSide.unionQ * NII +
          B * (2 * ZeroSide.unionC + 2 * Real.sqrt (κ * N + R₂) + B))
      ≤ ZeroSide.unionQ * lower := by
  have hsqrt : Real.sqrt frGh ≤ Real.sqrt (κ * N + R₂) := Real.sqrt_le_sqrt hfr
  have h2sqrt : 2 * Real.sqrt frGh ≤ 2 * Real.sqrt (κ * N + R₂) := by
    linarith
  have hBsqrt := mul_le_mul_of_nonneg_left h2sqrt hB
  have htrC : 2 * ZeroSide.unionC * (N - R₁) ≤
      2 * ZeroSide.unionC * trGh :=
    mul_le_mul_of_nonneg_left htr
      (mul_nonneg (by norm_num) ZeroSide.unionC_pos.le)
  nlinarith

/-- Moment cap `κ` implies union proportion
`1 - (κ - 1)/(3/2 + √2)`. -/
theorem union_count_certificate (Z : ZeroConfig) (P : Params) (κ : ℝ)
    (lower : ℝ → ℝ) (θ₀ : ℝ → ℝ)
    (h0 : ∀ᶠ T in atTop,
      2 * ZeroSide.unionC * rtrace (P.hat T (Z.Gz P T)) -
        frobSq (P.hat T (Z.Gz P T)) -
        ZeroSide.unionQ * (Z.N T (2 * T) : ℝ) -
        2 * ZeroSide.unionQ * (NII Z T : ℝ) -
        θ₀ T / (P.a T * P.L T) *
          (2 * ZeroSide.unionC +
            2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) +
            θ₀ T / (P.a T * P.L T))
      ≤ ZeroSide.unionQ * lower T)
    (hB0 : ∀ᶠ T in atTop, 0 ≤ θ₀ T / (P.a T * P.L T))
    (hBto : Tendsto (fun T => θ₀ T / (P.a T * P.L T)) atTop (𝓝 0))
    (hNII_o : (fun T => (NII Z T : ℝ)) =o[atTop]
      (fun T => (Z.N T (2 * T) : ℝ)))
    (hNtop : Tendsto (fun T => (Z.N T (2 * T) : ℝ)) atTop atTop)
    (htrace : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      (1 - δ) * (Z.N T (2 * T) : ℝ) ≤
        rtrace (P.hat T (Z.Gz P T)))
    (hfrob : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      frobSq (P.hat T (Z.Gz P T)) ≤
        (κ + δ) * (Z.N T (2 * T) : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - (κ - 1) / ZeroSide.unionQ - ε) *
          (Z.N T (2 * T) : ℝ) ≤ lower T := by
  intro ε hε
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set B : ℝ → ℝ := fun T => θ₀ T / (P.a T * P.L T) with hBdef
  set δ : ℝ := ε / 100 with hδdef
  have hδ : 0 < δ := by simp only [hδdef]; linarith
  have hκδ0 : 0 ≤ κ + δ := by
    by_contra hneg
    rw [not_le] at hneg
    obtain ⟨T, hfr, hN1⟩ := ((hfrob δ hδ).and (hNtop.eventually_ge_atTop 1)).exists
    have : frobSq (P.hat T (Z.Gz P T)) < 0 :=
      lt_of_le_of_lt hfr (mul_neg_of_neg_of_pos hneg (by
        simp only [hNdef] at hN1 ⊢
        linarith))
    exact absurd (frobSq_nonneg _) (not_le.mpr this)
  have hot := err_isLittleO (N := N) (R₁ := fun _ => 0) (R₂ := fun _ => 0)
    (NII := fun T => (NII Z T : ℝ)) (B := B) (cl := fun _ => κ + δ)
    (K := κ + δ) hNtop (isLittleO_zero _ _) (isLittleO_zero _ _) hNII_o hBto
    (Eventually.of_forall fun _ => ⟨hκδ0, le_rfl⟩)
  have htail : ∀ᶠ T in atTop,
      2 * ZeroSide.unionQ * (NII Z T : ℝ) +
        B T * (2 * ZeroSide.unionC +
          2 * Real.sqrt ((κ + δ) * N T) + B T)
      ≤ ε * N T := by
    filter_upwards [hot.def (half_pos hε), hB0, hNtop.eventually_ge_atTop 0] with
      T hsmall hBnonneg hNnonneg
    simp only [Real.norm_eq_abs, mul_zero, zero_add, add_zero,
      abs_of_nonneg hNnonneg] at hsmall
    have hsqrt : 0 ≤ Real.sqrt ((κ + δ) * N T) := Real.sqrt_nonneg _
    have hNII : 0 ≤ (NII Z T : ℝ) := Nat.cast_nonneg _
    have hbr : 2 * ZeroSide.unionC +
        2 * Real.sqrt ((κ + δ) * N T) + B T
      ≤ 2 * (4 + 2 * Real.sqrt ((κ + δ) * N T) + B T) := by
      nlinarith [ZeroSide.unionC_le_four]
    have hBbr := mul_le_mul_of_nonneg_left hbr hBnonneg
    have hNIIcmp : 2 * ZeroSide.unionQ * (NII Z T : ℝ)
        ≤ 2 * (3 * (NII Z T : ℝ)) := by
      have := mul_le_mul_of_nonneg_right ZeroSide.unionQ_le_three hNII
      nlinarith
    have hold : 3 * (NII Z T : ℝ) +
        B T * (4 + 2 * Real.sqrt ((κ + δ) * N T) + B T)
      ≤ ε / 2 * N T := (le_abs_self _).trans hsmall
    nlinarith
  have hc9 : 2 * ZeroSide.unionC + 1 ≤ 9 := by
    linarith [ZeroSide.unionC_le_four]
  have hmom : (2 * ZeroSide.unionC + 1) * δ ≤ ε := by
    have hmul := mul_le_mul_of_nonneg_right hc9 hε.le
    simp only [hδdef]
    nlinarith
  have hmain : ∀ᶠ T in atTop,
      (1 - (κ - 1) / ZeroSide.unionQ - ε) * N T ≤ lower T := by
    filter_upwards [h0, hB0, htrace δ hδ, hfrob δ hδ, htail,
      hNtop.eventually_ge_atTop 0] with T hseam hBnonneg htr hfr htailT hNnonneg
    have hlow := union_lower_moment (κ := κ) (R₁ := δ * N T)
      (R₂ := δ * N T) hBnonneg hseam
      (by simp only [hNdef] at htr ⊢; linarith)
      (by simp only [hNdef] at hfr ⊢; linarith)
    rw [show κ * N T + δ * N T = (κ + δ) * N T by ring] at hlow
    have hmomN := mul_le_mul_of_nonneg_right hmom hNnonneg
    have hεN : 0 ≤ ε * N T := mul_nonneg hε.le hNnonneg
    have htwo : 2 * (ε * N T) ≤ ZeroSide.unionQ * (ε * N T) :=
      mul_le_mul_of_nonneg_right ZeroSide.two_le_unionQ hεN
    have herr :
        2 * ZeroSide.unionC * (δ * N T) + δ * N T +
          2 * ZeroSide.unionQ * (NII Z T : ℝ) +
          B T * (2 * ZeroSide.unionC +
            2 * Real.sqrt ((κ + δ) * N T) + B T)
        ≤ ZeroSide.unionQ * (ε * N T) := by
      have hmomN' :
          2 * ZeroSide.unionC * (δ * N T) + δ * N T ≤ ε * N T := by
        nlinarith
      nlinarith
    have hratio : ZeroSide.unionQ *
        ((1 - (κ - 1) / ZeroSide.unionQ - ε) * N T) =
        (2 * ZeroSide.unionC - ZeroSide.unionQ - κ) * N T -
          ZeroSide.unionQ * (ε * N T) := by
      have hqne : ZeroSide.unionQ ≠ 0 := ZeroSide.unionQ_pos.ne'
      field_simp
      nlinarith [ZeroSide.two_unionC_eq_one_add_two_unionQ]
    have hscaled : ZeroSide.unionQ *
        ((1 - (κ - 1) / ZeroSide.unionQ - ε) * N T)
      ≤ ZeroSide.unionQ * lower T := by
      rw [hratio]
      linarith
    exact le_of_mul_le_mul_left hscaled ZeroSide.unionQ_pos
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hmain
  exact ⟨T₀, fun T hT => by simpa only [hNdef] using hT₀ T hT⟩

end Zeta23.Assembly
