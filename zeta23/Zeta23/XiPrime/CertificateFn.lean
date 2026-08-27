/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/CertificateFn.lean — the c = 2 and c = 3 count certificates over ABSTRACT REAL FUNCTIONS.

Zeta23.Assembly.count_certificate / count_certificate_c3 are stated for ONE parameter set P, with the
moments written as rtrace (P.hat T (Z.Gz P T)), frobSq (…) and the tail size as θ₀ T/(P.a T · P.L T).  Their
proofs never look inside those three real numbers (beyond frobSq ≥ 0).  For a HEIGHT FAMILY Pf : ℝ → Params
(the window at height T is (Pf T).phi T — the quartic window, Defs.Params.atV) we need the same algebra
with tr, fr, B, N, NII, lower arbitrary real functions of T; this file is that copy, proofs verbatim.
-/
import Zeta23.Assembly.CertificateC3

open Filter Asymptotics Topology Real

noncomputable section

namespace Zeta23
namespace XiPrime

open Assembly

/-- **c = 2 count certificate, function-abstract form.**  If eventually
4·tr − fr − 2N − 3NII − B(4 + 2√fr + B) ≤ lower, B ≥ 0, B → 0, NII = o(N), N → ∞, fr ≥ 0, and for every
δ > 0 eventually (1−δ)N ≤ tr and fr ≤ (κ+δ)N, then for every ε > 0 eventually (2 − κ − ε)N ≤ lower. -/
theorem count_certificate_fn (κ : ℝ) {N NII tr fr B lower : ℝ → ℝ}
    (hfr0 : ∀ᶠ T in atTop, 0 ≤ fr T)
    (h0 : ∀ᶠ T in atTop,
      4 * tr T - fr T - 2 * N T - 3 * NII T - B T * (4 + 2 * Real.sqrt (fr T) + B T) ≤ lower T)
    (hB0 : ∀ᶠ T in atTop, 0 ≤ B T)
    (hBto : Tendsto B atTop (𝓝 0))
    (hNII_o : NII =o[atTop] N)
    (hNtop : Tendsto N atTop atTop)
    (htrace : ∀ δ > (0:ℝ), ∀ᶠ T in atTop, (1 - δ) * N T ≤ tr T)
    (hfrob : ∀ δ > (0:ℝ), ∀ᶠ T in atTop, fr T ≤ (κ + δ) * N T) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - κ - ε) * N T ≤ lower T := by
  intro ε hε
  set δ : ℝ := ε / 6 with hδdef
  have hδ : 0 < δ := by simp only [hδdef]; linarith
  have hκδ0 : 0 ≤ κ + δ := by
    by_contra h
    rw [not_le] at h
    obtain ⟨T, hT1, hT2, hT3⟩ :=
      ((hfrob δ hδ).and ((hNtop.eventually_ge_atTop 1).and hfr0)).exists
    have : fr T < 0 := lt_of_le_of_lt hT1 (mul_neg_of_neg_of_pos h (by linarith))
    linarith
  have hot := err_isLittleO (N := N) (R₁ := fun _ => 0) (R₂ := fun _ => 0)
    (NII := NII) (B := B) (cl := fun _ => κ + δ) (K := κ + δ)
    hNtop (isLittleO_zero _ _) (isLittleO_zero _ _) hNII_o hBto
    (Eventually.of_forall fun _ => ⟨hκδ0, le_rfl⟩)
  have hsmall : ∀ᶠ T in atTop,
      3 * NII T + B T * (4 + 2 * Real.sqrt ((κ + δ) * N T) + B T) ≤ δ * N T := by
    filter_upwards [hot.def hδ, hNtop.eventually_ge_atTop 0] with T h1 hN0
    simp only [Real.norm_eq_abs, mul_zero, zero_add, add_zero, abs_of_nonneg hN0] at h1
    exact (le_abs_self _).trans h1
  have hmain : ∀ᶠ T in atTop, (2 - κ - ε) * N T ≤ lower T := by
    filter_upwards [h0, hB0, htrace δ hδ, hfrob δ hδ, hsmall,
      hNtop.eventually_ge_atTop 0] with T hA hB₀ htr hfr hsm hN0
    have hlow := N0star_lower_moment (κ := κ) (R₁ := δ * N T) (R₂ := δ * N T) hB₀ hA
      (by linarith) (by linarith)
    rw [show κ * N T + δ * N T = (κ + δ) * N T by ring] at hlow
    have hfin : (2 - κ - ε) * N T
        = (2 - κ) * N T - (4 * (δ * N T) + δ * N T + δ * N T) := by
      simp only [hδdef]; ring
    rw [hfin]
    linarith [hsm, hlow]
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hmain
  exact ⟨T₀, fun T hT => hT₀ T hT⟩

/-- **c = 3 count certificate, function-abstract form:** from
6·tr − fr − 3N − 5NII − B(6 + 2√fr + B) ≤ 2·lower and the moments, eventually (3/2 − κ/2 − ε)N ≤ lower. -/
theorem count_certificate_c3_fn (κ : ℝ) {N NII tr fr B lower : ℝ → ℝ}
    (hfr0 : ∀ᶠ T in atTop, 0 ≤ fr T)
    (h0 : ∀ᶠ T in atTop,
      6 * tr T - fr T - 3 * N T - 5 * NII T - B T * (6 + 2 * Real.sqrt (fr T) + B T) ≤ 2 * lower T)
    (hB0 : ∀ᶠ T in atTop, 0 ≤ B T)
    (hBto : Tendsto B atTop (𝓝 0))
    (hNII_o : NII =o[atTop] N)
    (hNtop : Tendsto N atTop atTop)
    (htrace : ∀ δ > (0:ℝ), ∀ᶠ T in atTop, (1 - δ) * N T ≤ tr T)
    (hfrob : ∀ δ > (0:ℝ), ∀ᶠ T in atTop, fr T ≤ (κ + δ) * N T) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 2 - κ / 2 - ε) * N T ≤ lower T := by
  intro ε hε
  set δ : ℝ := ε / 6 with hδdef
  have hδ : 0 < δ := by simp only [hδdef]; linarith
  have hκδ0 : 0 ≤ κ + δ := by
    by_contra h
    rw [not_le] at h
    obtain ⟨T, hT1, hT2, hT3⟩ :=
      ((hfrob δ hδ).and ((hNtop.eventually_ge_atTop 1).and hfr0)).exists
    have : fr T < 0 := lt_of_le_of_lt hT1 (mul_neg_of_neg_of_pos h (by linarith))
    linarith
  have hot := err_isLittleO (N := N) (R₁ := fun _ => 0) (R₂ := fun _ => 0)
    (NII := NII) (B := B) (cl := fun _ => κ + δ) (K := κ + δ)
    hNtop (isLittleO_zero _ _) (isLittleO_zero _ _) hNII_o hBto
    (Eventually.of_forall fun _ => ⟨hκδ0, le_rfl⟩)
  have hBsmall : ∀ᶠ T in atTop, B T ≤ δ / 2 * N T := by
    have hB1 : ∀ᶠ T in atTop, B T ≤ 1 :=
      hBto.eventually (eventually_le_nhds (show (0:ℝ) < 1 by norm_num))
    filter_upwards [hB1, hNtop.eventually_ge_atTop (2 / δ)] with T h1 h2
    have : 1 ≤ δ / 2 * N T := by
      rw [div_le_iff₀ hδ] at h2
      nlinarith
    linarith
  have hsmall : ∀ᶠ T in atTop,
      (5 / 2) * NII T + (B T / 2) * (6 + 2 * Real.sqrt ((κ + δ) * N T) + B T)
        ≤ 2 * δ * N T := by
    filter_upwards [hot.def hδ, hNII_o.def hδ, hNtop.eventually_ge_atTop 0, hBsmall, hB0]
      with T h1 hnii hN0 hBs hB₀
    simp only [Real.norm_eq_abs, mul_zero, zero_add, add_zero, abs_of_nonneg hN0] at h1 hnii
    have h1' : 3 * NII T + B T * (4 + 2 * Real.sqrt ((κ + δ) * N T) + B T) ≤ δ * N T :=
      (le_abs_self _).trans h1
    have hnii' : NII T ≤ δ * N T := (le_abs_self _).trans hnii
    have hB₀' : 0 ≤ B T := hB₀
    nlinarith
  have hmain : ∀ᶠ T in atTop, (3 / 2 - κ / 2 - ε) * N T ≤ lower T := by
    filter_upwards [h0, hB0, htrace δ hδ, hfrob δ hδ, hsmall,
      hNtop.eventually_ge_atTop 0] with T hA hB₀ htr hfr hsm hN0
    have hlow := count_lower_moment_c3_five (κ := κ) (R₁ := δ * N T) (R₂ := δ * N T) hB₀ hA
      (by linarith) (by linarith)
    rw [show κ * N T + δ * N T = (κ + δ) * N T by ring] at hlow
    have hεδ : (3 / 2 - κ / 2 - ε) * N T
        ≤ (3 / 2 - κ / 2) * N T - (3 * (δ * N T) + δ * N T / 2 + 2 * δ * N T) := by
      simp only [hδdef]; nlinarith
    linarith [hsm, hlow, hεδ]
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hmain
  exact ⟨T₀, fun T hT => hT₀ T hT⟩

end XiPrime
end Zeta23

end
