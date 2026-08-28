/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Assembly/Certificate.lean — the §6 certificate abstracted over the second moment: for any
zero configuration and window parameters, with the zero-side block/tail inputs as usual, if eventually
tr Ĝ ≥ (1−δ)N  and  ‖Ĝ‖_F² ≤ (κ+δ)N  (every δ > 0), then every count satisfying the fixed-T seam
inequality is eventually at least (2 − κ − ε)N(T,2T)  (every ε > 0).  At κ = 1/λ₁ + λ₁/3 this is the
paper's H(λ₁).  The arithmetic lives entirely in the two moment hypotheses; no prime side, no
zero-counting formula and no explicit formula is consumed here.
-/
import Zeta23.Assembly

open Filter Asymptotics Topology Real RHLinalg

noncomputable section

namespace Zeta23
namespace Assembly

/-- κ-version of `N0star_lower_H`: moments ⟹ fixed-T lower bound. -/
theorem N0star_lower_moment
    {N0star N NII trGh frGh B κ R₁ R₂ : ℝ} (hB : 0 ≤ B)
    (h0 : 4 * trGh - frGh - 2 * N - 3 * NII - B * (4 + 2 * Real.sqrt frGh + B) ≤ N0star)
    (htr : N - R₁ ≤ trGh) (hfr : frGh ≤ κ * N + R₂) :
    (2 - κ) * N - (4 * R₁ + R₂ + 3 * NII
        + B * (4 + 2 * Real.sqrt (κ * N + R₂) + B)) ≤ N0star := by
  have h2 : Real.sqrt frGh ≤ Real.sqrt (κ * N + R₂) := Real.sqrt_le_sqrt hfr
  nlinarith [h0, htr, h2, hB, mul_le_mul_of_nonneg_left h2 hB]

/-! ## Seam-agnostic count certificates (for the multiplicity-aware rank–trace variants:
the zero-side inequality arrives as the hypothesis h0, so the same algebra serves N₀* (seamA),
the c = 2 multiplicity-aware N₀ˢ seam, and — in halved form below — the c = 3 N_d seam). -/

/-- The moment certificate with the fixed-T seam inequality abstracted: any count `lower`
satisfying the seam shape eventually obeys the (2 − κ − ε) certificate. -/
theorem count_certificate (Z : ZeroConfig) (P : Params) (κ : ℝ) (lower : ℝ → ℝ)
    (θ₀ : ℝ → ℝ)
    (h0 : ∀ᶠ T in atTop, 4 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T))
      - 2 * (Z.N T (2 * T) : ℝ) - 3 * (NII Z T : ℝ)
      - θ₀ T / (P.a T * P.L T)
          * (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ T / (P.a T * P.L T))
      ≤ lower T)
    (hB0 : ∀ᶠ T in atTop, 0 ≤ θ₀ T / (P.a T * P.L T))
    (hBto : Tendsto (fun T => θ₀ T / (P.a T * P.L T)) atTop (𝓝 0))
    (hNII_o : (fun T => (NII Z T : ℝ)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)))
    (hNtop : Tendsto (fun T => (Z.N T (2 * T) : ℝ)) atTop atTop)
    (htrace : ∀ δ > (0:ℝ), ∀ᶠ T in atTop,
      (1 - δ) * (Z.N T (2 * T) : ℝ) ≤ rtrace (P.hat T (Z.Gz P T)))
    (hfrob : ∀ δ > (0:ℝ), ∀ᶠ T in atTop,
      frobSq (P.hat T (Z.Gz P T)) ≤ (κ + δ) * (Z.N T (2 * T) : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - κ - ε) * (Z.N T (2 * T) : ℝ) ≤ lower T := by
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
  have hsmall : ∀ᶠ T in atTop,
      3 * (NII Z T : ℝ) + B T * (4 + 2 * Real.sqrt ((κ + δ) * N T) + B T) ≤ δ * N T := by
    filter_upwards [hot.def hδ, hNtop.eventually_ge_atTop 0] with T h1 hN0
    simp only [Real.norm_eq_abs, mul_zero, zero_add, add_zero, abs_of_nonneg hN0] at h1
    exact (le_abs_self _).trans h1
  have hmain : ∀ᶠ T in atTop, (2 - κ - ε) * N T ≤ lower T := by
    filter_upwards [h0, hB0, htrace δ hδ, hfrob δ hδ, hsmall,
      hNtop.eventually_ge_atTop 0] with T hA hB₀ htr hfr hsm hN0
    have hlow := N0star_lower_moment (κ := κ) (R₁ := δ * N T) (R₂ := δ * N T) hB₀ hA
      (by simp only [hNdef] at htr ⊢; linarith) (by simp only [hNdef] at hfr ⊢; linarith)
    rw [show κ * N T + δ * N T = (κ + δ) * N T by ring] at hlow
    have hfin : (2 - κ - ε) * N T
        = (2 - κ) * N T - (4 * (δ * N T) + δ * N T + δ * N T) := by
      simp only [hδdef]; ring
    rw [hfin]
    linarith [hsm, hlow]
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hmain
  exact ⟨T₀, fun T hT => hT₀ T hT⟩

/-- the c = 3 fixed-T algebra: from `6·tr − frob − 3N − 3NII − B·(…) ≤ 2·lower` and the moment
bounds, `(3/2 − κ/2)·N − errors ≤ lower`. -/
theorem count_lower_moment_c3
    {lower N NII trGh frGh B κ R₁ R₂ : ℝ} (hB : 0 ≤ B)
    (h0 : 6 * trGh - frGh - 3 * N - 5 * NII - B * (6 + 2 * Real.sqrt frGh + B) ≤ 2 * lower)
    (htr : N - R₁ ≤ trGh) (hfr : frGh ≤ κ * N + R₂) :
    (3/2 - κ/2) * N - (3 * R₁ + R₂ / 2 + (5/2) * NII
        + (B/2) * (6 + 2 * Real.sqrt (κ * N + R₂) + B)) ≤ lower := by
  have h2 : Real.sqrt frGh ≤ Real.sqrt (κ * N + R₂) := Real.sqrt_le_sqrt hfr
  nlinarith [h0, htr, h2, hB, mul_le_mul_of_nonneg_left h2 hB]

end Assembly
end Zeta23
