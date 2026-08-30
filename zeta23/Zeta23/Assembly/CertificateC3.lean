/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Assembly/CertificateC3.lean — the count certificate for the rank–trace inequality with parameter
c = 3 (distinct zeros), following Assembly/Certificate.count_certificate with the c = 3 fixed-T algebra:
from the seam shape 6·tr Ĝ − ‖Ĝ‖² − 3N − 5NII − B(6 + 2√‖Ĝ‖² + B) ≤ 2·lower (the c = 3 seam
carries 5·NII: 3 from −3N(I′) and 2 from 2·#𝒵(I′) ≤ 2N_d + 2NII) and the moment
hypotheses tr Ĝ ≥ (1−δ)N, ‖Ĝ‖² ≤ (κ+δ)N (every δ > 0), eventually (3/2 − κ/2 − ε)·N ≤ lower.
-/
import Zeta23.Assembly.Certificate

open Filter Asymptotics Topology Real RHLinalg

noncomputable section

namespace Zeta23
namespace Assembly

/-- the c = 3 fixed-T algebra with the 5·NII window term. -/
theorem count_lower_moment_c3_five
    {lower N NII trGh frGh B κ R₁ R₂ : ℝ} (hB : 0 ≤ B)
    (h0 : 6 * trGh - frGh - 3 * N - 5 * NII - B * (6 + 2 * Real.sqrt frGh + B) ≤ 2 * lower)
    (htr : N - R₁ ≤ trGh) (hfr : frGh ≤ κ * N + R₂) :
    (3/2 - κ/2) * N - (3 * R₁ + R₂ / 2 + (5/2) * NII
        + (B/2) * (6 + 2 * Real.sqrt (κ * N + R₂) + B)) ≤ lower := by
  have h2 : Real.sqrt frGh ≤ Real.sqrt (κ * N + R₂) := Real.sqrt_le_sqrt hfr
  nlinarith [h0, htr, h2, hB, mul_le_mul_of_nonneg_left h2 hB]

/-- **the c = 3 count certificate.** -/
theorem count_certificate_c3 (Z : ZeroConfig) (P : Params) (κ : ℝ) (lower : ℝ → ℝ)
    (θ₀ : ℝ → ℝ)
    (h0 : ∀ᶠ T in atTop, 6 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T))
      - 3 * (Z.N T (2 * T) : ℝ) - 5 * (NII Z T : ℝ)
      - θ₀ T / (P.a T * P.L T)
          * (6 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ T / (P.a T * P.L T))
      ≤ 2 * lower T)
    (hB0 : ∀ᶠ T in atTop, 0 ≤ θ₀ T / (P.a T * P.L T))
    (hBto : Tendsto (fun T => θ₀ T / (P.a T * P.L T)) atTop (𝓝 0))
    (hNII_o : (fun T => (NII Z T : ℝ)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)))
    (hNtop : Tendsto (fun T => (Z.N T (2 * T) : ℝ)) atTop atTop)
    (htrace : ∀ δ > (0:ℝ), ∀ᶠ T in atTop,
      (1 - δ) * (Z.N T (2 * T) : ℝ) ≤ rtrace (P.hat T (Z.Gz P T)))
    (hfrob : ∀ δ > (0:ℝ), ∀ᶠ T in atTop,
      frobSq (P.hat T (Z.Gz P T)) ≤ (κ + δ) * (Z.N T (2 * T) : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3/2 - κ/2 - ε) * (Z.N T (2 * T) : ℝ) ≤ lower T := by
  intro ε hε
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set B : ℝ → ℝ := fun T => θ₀ T / (P.a T * P.L T) with hBdef
  set δ : ℝ := ε / 6 with hδdef
  have hδ : 0 < δ := by simp only [hδdef]; linarith
  have hκδ0 : 0 ≤ κ + δ := by
    by_contra h
    rw [not_le] at h
    obtain ⟨T, hT1, hT2⟩ := ((hfrob δ hδ).and (hNtop.eventually_ge_atTop 1)).exists
    have : frobSq (P.hat T (Z.Gz P T)) < 0 :=
      lt_of_le_of_lt hT1 (mul_neg_of_neg_of_pos h (by simp only [hNdef] at hT2 ⊢; linarith))
    exact absurd (frobSq_nonneg _) (not_le.mpr this)
  have hot := err_isLittleO (N := N) (R₁ := fun _ => 0) (R₂ := fun _ => 0)
    (NII := fun T => (NII Z T : ℝ)) (B := B) (cl := fun _ => κ + δ) (K := κ + δ)
    hNtop (isLittleO_zero _ _) (isLittleO_zero _ _) hNII_o hBto
    (Eventually.of_forall fun _ => ⟨hκδ0, le_rfl⟩)
  -- B ≤ δ/2 · N eventually (B → 0, N → ∞)
  have hBsmall : ∀ᶠ T in atTop, B T ≤ δ / 2 * N T := by
    have hB1 : ∀ᶠ T in atTop, B T ≤ 1 := by
      have := hBto.eventually (eventually_le_nhds (show (0:ℝ) < 1 by norm_num))
      exact this
    filter_upwards [hB1, hNtop.eventually_ge_atTop (2 / δ)] with T h1 h2
    have : 1 ≤ δ / 2 * N T := by
      rw [div_le_iff₀ hδ] at h2
      nlinarith
    linarith
  have hsmall : ∀ᶠ T in atTop,
      (5/2) * (NII Z T : ℝ) + (B T / 2) * (6 + 2 * Real.sqrt ((κ + δ) * N T) + B T)
        ≤ 2 * δ * N T := by
    filter_upwards [hot.def hδ, hNII_o.def hδ, hNtop.eventually_ge_atTop 0, hBsmall, hB0]
      with T h1 hnii hN0 hBs hB₀
    simp only [Real.norm_eq_abs, mul_zero, zero_add, add_zero, abs_of_nonneg hN0] at h1 hnii
    have h1' : 3 * (NII Z T : ℝ) + B T * (4 + 2 * Real.sqrt ((κ + δ) * N T) + B T) ≤ δ * N T :=
      (le_abs_self _).trans h1
    have hnii' : (NII Z T : ℝ) ≤ δ * N T := (le_abs_self _).trans hnii
    have hB₀' : 0 ≤ B T := hB₀
    -- (5/2)NII + (B/2)(6 + 2√ + B) = ½[3NII + B(4 + 2√ + B)] + NII + B
    nlinarith
  have hmain : ∀ᶠ T in atTop, (3/2 - κ/2 - ε) * N T ≤ lower T := by
    filter_upwards [h0, hB0, htrace δ hδ, hfrob δ hδ, hsmall,
      hNtop.eventually_ge_atTop 0] with T hA hB₀ htr hfr hsm hN0
    have hlow := count_lower_moment_c3_five (κ := κ) (R₁ := δ * N T) (R₂ := δ * N T) hB₀ hA
      (by simp only [hNdef] at htr ⊢; linarith) (by simp only [hNdef] at hfr ⊢; linarith)
    rw [show κ * N T + δ * N T = (κ + δ) * N T by ring] at hlow
    have hεδ : (3/2 - κ/2 - ε) * N T
        ≤ (3/2 - κ/2) * N T - (3 * (δ * N T) + δ * N T / 2 + 2 * δ * N T) := by
      simp only [hδdef]; nlinarith
    linarith [hsm, hlow, hεδ]
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hmain
  exact ⟨T₀, fun T hT => hT₀ T hT⟩

end Assembly
end Zeta23
