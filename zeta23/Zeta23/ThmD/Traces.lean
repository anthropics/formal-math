/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmD/Traces.lean — window-general traces assembly.
[eq:ratio-general]: the window-general [thm:traces] assembly.  Mirrors Zeta23/PrimeSideB.lean's
Data/Facts → TracesBounds pipeline with TWO changes (paper §7.1):
 * the [eq:gbounds] sandwich fields (sum_lower/sum_upper, forcing Σa_n²g ≈ L³/6 i.e. J = 1/3)
   are replaced by the moment field sumJ : Σ_{n≤X} a_n² g(y_n) = (L³/2)·J_T + O(L²)
   (discharged for the concrete window by ThmD/PP.lean sumA2g_close + Window.lean jD_close);
 * b is kept symbolic (no b_lower ≈ 1); only 1/2 ≤ b ≤ a ≤ 1 is carried (true for the
   Montgomery–Taylor window: b* = 1/2 + sin(2ϑ)/(4ϑ) > 1/2, minus O(w/L)).
Conclusion: TracesBoundsD (Zeta23/ThmD/AssemblyD.lean) with ratio constant
cRatio λ₁ a b J = λ₁a²/(b + λ₁²J).
-/
import Zeta23.PrimeSideB
import Zeta23.ThmD.AssemblyD
import Zeta23.ThmD.PP

noncomputable section

open Real Filter

namespace Zeta23
namespace ThmD

/-- the abstract data of the D-assembly: PrimeSideB's Data plus the window moment J_T
([eq:abJ]: J := (2/L³)∫_0^L g(y)·y dy). -/
structure DataD (P : Params) extends PrimeSide.Data P where
  /-- J := (2/L³) ∫_0^L g(y) y dy [eq:abJ]. -/
  JT : ℝ → ℝ

variable {P : Params} (D : DataD P)

/-- Hypotheses of the window-general [thm:traces] assembly (paper §7.1 "Propositions 5.1–5.5 hold
verbatim" + the partial-summation step).  All fields except ab_range and sumJ are verbatim copies
of Zeta23.PrimeSide.Facts (window-generic); see that structure for the paper labels. -/
structure FactsD : Prop where
  lam_pos : 0 < P.lam
  lam_le_one : P.lam ≤ 1
  one_le_w : 1 ≤ P.w
  /-- window-general [eq:abJ] ranges: 1/2 ≤ b ≤ a ≤ 1 and 0 ≤ J ≤ 1 eventually. -/
  ab_range : ∀ᶠ T in atTop,
    1 / 2 ≤ D.bT T ∧ D.bT T ≤ D.aT T ∧ D.aT T ≤ 1 ∧ 0 ≤ D.JT T ∧ D.JT T ≤ 1
  rvm : EvBound (fun T => D.Ncnt T - T * ell1 T / (2 * π)) l
  muints2 : EvBound (fun T => D.intMu2 T - T * ell1 T ^ 2 / (4 * π ^ 2))
      (fun T => T * ell1 T ^ 2 / (4 * π ^ 2) / l T ^ 2)
  prop_trace : EvBound (fun T => D.trG T - D.aT T * P.L T * D.Ncnt T)
      (fun T => P.L T * Real.sqrt (P.X T))
  lem_ends : EvBound (fun T => D.trG2 T - D.Mtot T)
      (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T))
  Msplit : ∀ᶠ T in atTop, D.Mtot T =
      D.Mmumu T + D.MPP T + 2 * D.MmuP T + 2 * D.MmuPi T + 2 * D.MPPi T + D.MPiPi T
  prop_mumu : EvBound (fun T => D.Mmumu T - 2 * π * D.bT T * P.L T * D.intMu2 T)
      (fun T => l T ^ 2 * Real.log (P.L T))
  prop_PP : EvBound (fun T => D.MPP T - T / π * D.sumL2g T) (fun T => P.L T ^ 2 * P.X T)
  /-- the §7.1 partial-summation step in place of the sandwich:
  Σ_{n≤X} a_n² g(y_n) = (L³/2)·J_T + O(L²). -/
  sumJ : EvBound (fun T => D.sumL2g T - P.L T ^ 3 / 2 * D.JT T) (fun T => P.L T ^ 2)
  cross_muP : EvBound D.MmuP (fun T => l T * Real.sqrt (P.X T))
  cross_muPi : EvBound D.MmuPi (fun T => l T * P.L T * Real.sqrt (P.X T))
  cross_PPi : EvBound D.MPPi (fun T => P.L T * P.X T)
  cross_PiPi : EvBound D.MPiPi (fun T => P.L T * P.X T / T)

/-- The pointwise inequality behind the D-version of [eq:tr2] ([eq:ratio-general] main term):
with the window moments b, J symbolic and the partial-summation input |S − L³J/2| ≤ Cs·L²
in place of the flat-top sandwich, |G2 − (TL/2π)(bℓ² + L²J)| ≤ C·E·(TL/2π)(bℓ² + L²J).
Simpler than PrimeSide.tr2_pointwise: no (b−1)-collapse is needed since b stays in the main term. -/
theorem tr2D_pointwise (T L ℓ lT X E S I2 b J G2 w CR Cμ Cs : ℝ)
    (hT : 1 ≤ T) (hL : 1 ≤ L) (hl : 1 ≤ lT) (hlog : 1 ≤ Real.log lT) (hX : 1 ≤ X)
    (hℓl : lT ≤ ℓ) (hLl : L ≤ lT) (hw : 1 ≤ w) (hL2w : 2 * w ≤ L)
    (hb : 1 / 2 ≤ b) (hb1 : b ≤ 1) (hJ0 : 0 ≤ J)
    (hE0 : 0 ≤ E) (hEw : w / L ≤ E) (hEmid : (lT ^ 2 + X) * Real.log lT / (T * lT) ≤ E)
    (hCR : 0 ≤ CR) (hCμ : 0 ≤ Cμ) (hCs : 0 ≤ Cs)
    (hR : |G2 - (2 * π * b * L * I2 + T / π * S)| ≤ CR * (L * lT * Real.log lT * (lT ^ 2 + X)))
    (hμ : |I2 - T * ℓ ^ 2 / (4 * π ^ 2)| ≤ Cμ * (T * ℓ ^ 2 / (4 * π ^ 2) / lT ^ 2))
    (hSJ : |S - L ^ 3 * J / 2| ≤ Cs * L ^ 2) :
    |G2 - T * L / (2 * π) * (b * ℓ ^ 2 + L ^ 2 * J)|
      ≤ (4 * π * CR + 2 * Cμ + 4 * Cs) * (E * (T * L / (2 * π) * (b * ℓ ^ 2 + L ^ 2 * J))) := by
  have hπ : 0 < π := Real.pi_pos
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < L := by linarith
  have hl0 : 0 < lT := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hℓ1 : 1 ≤ ℓ := le_trans hl hℓl
  have hlog0 : 0 ≤ Real.log lT := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hw0 : 0 ≤ w := by linarith
  have hb0 : 0 < b := by linarith
  set M₂ := T * L / (2 * π) * (b * ℓ ^ 2 + L ^ 2 * J) with hM₂def
  -- the ℓ²-piece lower bound: TLℓ²/(4π) ≤ M₂
  have hMa : T * L * ℓ ^ 2 / (4 * π) ≤ M₂ := by
    rw [hM₂def]
    have h1 : T * L * ℓ ^ 2 / (4 * π) = T * L / (2 * π) * (ℓ ^ 2 / 2) := by ring
    rw [h1]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [sq_nonneg ℓ, sq_nonneg L]
  have hM0 : 0 ≤ M₂ := le_trans (by positivity) hMa
  have hEM0 : 0 ≤ E * M₂ := mul_nonneg hE0 hM0
  have hE_L : 1 / L ≤ E := le_trans (by gcongr) hEw
  have hE_l2 : 1 / lT ^ 2 ≤ E := by
    refine le_trans ?_ hE_L
    rw [div_le_div_iff₀ (by positivity) hL0, one_mul, one_mul]
    calc L ≤ lT := hLl
      _ = lT * 1 := (mul_one _).symm
      _ ≤ lT * lT := by gcongr
      _ = lT ^ 2 := (sq lT).symm
  -- piece A: the lem_ends-type remainder
  have hA : L * lT * Real.log lT * (lT ^ 2 + X) ≤ 4 * π * (E * M₂) := by
    have h1 : (lT ^ 2 + X) * Real.log lT / (T * lT) * (T * L * ℓ ^ 2 / (4 * π)) ≤ E * M₂ :=
      mul_le_mul hEmid hMa (by positivity) hE0
    have h2 : 4 * π * ((lT ^ 2 + X) * Real.log lT / (T * lT) * (T * L * ℓ ^ 2 / (4 * π)))
        = L * Real.log lT * (lT ^ 2 + X) * ℓ ^ 2 / lT := by
      field_simp
    have h3 : L * lT * Real.log lT * (lT ^ 2 + X)
        ≤ L * Real.log lT * (lT ^ 2 + X) * ℓ ^ 2 / lT := by
      rw [le_div_iff₀ hl0]
      have hll : lT * lT ≤ ℓ ^ 2 := by
        rw [sq]
        exact mul_le_mul hℓl hℓl hl0.le hℓ0.le
      have h0 : 0 ≤ L * Real.log lT * (lT ^ 2 + X) := by positivity
      calc L * lT * Real.log lT * (lT ^ 2 + X) * lT
          = L * Real.log lT * (lT ^ 2 + X) * (lT * lT) := by ring
        _ ≤ L * Real.log lT * (lT ^ 2 + X) * ℓ ^ 2 := by gcongr
    calc L * lT * Real.log lT * (lT ^ 2 + X)
        ≤ L * Real.log lT * (lT ^ 2 + X) * ℓ ^ 2 / lT := h3
      _ = 4 * π * ((lT ^ 2 + X) * Real.log lT / (T * lT) * (T * L * ℓ ^ 2 / (4 * π))) := h2.symm
      _ ≤ 4 * π * (E * M₂) := by gcongr
  -- piece B1: the μ-moment remainder
  have hB1 : |2 * π * b * L * (I2 - T * ℓ ^ 2 / (4 * π ^ 2))| ≤ 2 * Cμ * (E * M₂) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * π * b * L)]
    calc 2 * π * b * L * |I2 - T * ℓ ^ 2 / (4 * π ^ 2)|
        ≤ 2 * π * 1 * L * (Cμ * (T * ℓ ^ 2 / (4 * π ^ 2) / lT ^ 2)) := by gcongr
      _ = 2 * Cμ * ((1 / lT ^ 2) * (T * L * ℓ ^ 2 / (4 * π))) := by
          field_simp
          try ring
      _ ≤ 2 * Cμ * ((1 / lT ^ 2) * M₂) := by
          have h0 : (0:ℝ) ≤ 1 / lT ^ 2 := by positivity
          gcongr
      _ ≤ 2 * Cμ * (E * M₂) := by gcongr
  -- piece B3: the partial-summation remainder
  have hB3 : |T / π * (S - L ^ 3 * J / 2)| ≤ 4 * Cs * (E * M₂) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ T / π)]
    calc T / π * |S - L ^ 3 * J / 2| ≤ T / π * (Cs * L ^ 2) := by gcongr
      _ = 4 * Cs * ((L / ℓ ^ 2) * (T * L * ℓ ^ 2 / (4 * π))) := by
          field_simp
          try ring
      _ ≤ 4 * Cs * ((1 / L) * M₂) := by
          have hLℓ2 : L / ℓ ^ 2 ≤ 1 / L := by
            rw [div_le_div_iff₀ (by positivity) hL0]
            have hLℓ : L ≤ ℓ := le_trans hLl hℓl
            nlinarith
          have h0 : (0:ℝ) ≤ L / ℓ ^ 2 := by positivity
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc L / ℓ ^ 2 * (T * L * ℓ ^ 2 / (4 * π)) ≤ 1 / L * (T * L * ℓ ^ 2 / (4 * π)) := by
                gcongr
            _ ≤ 1 / L * M₂ := by
                have : (0:ℝ) ≤ 1 / L := by positivity
                gcongr
      _ ≤ 4 * Cs * (E * M₂) := by gcongr
  -- assemble
  have hsplit : (2 * π * b * L * I2 + T / π * S) - M₂
      = 2 * π * b * L * (I2 - T * ℓ ^ 2 / (4 * π ^ 2)) + T / π * (S - L ^ 3 * J / 2) := by
    rw [hM₂def]
    field_simp
    ring
  calc |G2 - M₂|
      ≤ |G2 - (2 * π * b * L * I2 + T / π * S)|
        + |(2 * π * b * L * I2 + T / π * S) - M₂| := abs_sub_le _ _ _
    _ ≤ CR * (L * lT * Real.log lT * (lT ^ 2 + X))
        + (|2 * π * b * L * (I2 - T * ℓ ^ 2 / (4 * π ^ 2))| + |T / π * (S - L ^ 3 * J / 2)|) := by
        gcongr
        rw [hsplit]
        exact abs_add_le _ _
    _ ≤ CR * (4 * π * (E * M₂)) + (2 * Cμ * (E * M₂) + 4 * Cs * (E * M₂)) := by
        gcongr
    _ = (4 * π * CR + 2 * Cμ + 4 * Cs) * (E * M₂) := by ring

/-- from `f → 0`: eventually `C * f T ≤ 1/2` (used for the `Cᵢ·𝓔_T ≤ 1/2` side conditions of
`ratioD_pointwise`, here and in ThmDE.Traces). -/
theorem eventually_const_mul_le_half {f : ℝ → ℝ} (hf : Tendsto f atTop (nhds 0)) {C : ℝ}
    (hC : 0 < C) : ∀ᶠ T in atTop, C * f T ≤ 1 / 2 := by
  filter_upwards [hf.eventually (Iio_mem_nhds (show (0:ℝ) < 1 / (2 * C) by positivity))] with T hT
  rw [lt_div_iff₀ (by positivity)] at hT
  linarith

set_option maxHeartbeats 800000 in
/-- The pointwise inequality behind [eq:ratio-general], every quantity a real variable; the
identity cRatio(L/ℓ; a, b, J)·N · (TL/2π)(bℓ² + L²J) = (aL)²N · Tℓ/2π is where the
window-general constant is checked (mirrors PrimeSide.ratio_pointwise; a stays on tr G̃). -/
theorem ratioD_pointwise (T L ℓ lT E N G G2 A aa b J C₁ C₂ : ℝ)
    (hT : 1 ≤ T) (hL : 0 < L) (hℓ1 : 1 ≤ ℓ) (hℓl : lT ≤ ℓ) (hN0 : 0 < N) (hE0 : 0 ≤ E)
    (hET : 1 / T ≤ E) (hA : 0 ≤ A) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (ha : 1 / 2 ≤ aa) (hb : 1 / 2 ≤ b) (hJ0 : 0 ≤ J)
    (hs1 : C₁ * E ≤ 1 / 2) (hs2 : C₂ * E ≤ 1 / 2) (hTA : 2 * π * A ≤ T)
    (h1 : |G - aa * L * N| ≤ C₁ * (E * (aa * L * N)))
    (h2 : |G2 - T * L / (2 * π) * (b * ℓ ^ 2 + L ^ 2 * J)|
      ≤ C₂ * (E * (T * L / (2 * π) * (b * ℓ ^ 2 + L ^ 2 * J))))
    (hN : |N - T * ℓ / (2 * π)| ≤ A * lT) :
    |G ^ 2 / G2 - cRatio (L / ℓ) aa b J * N|
      ≤ 2 * (2 * π * A + 5 * C₁ + C₂) * (E * (cRatio (L / ℓ) aa b J * N)) := by
  have hπ : 0 < π := Real.pi_pos
  have hT0 : 0 < T := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have ha0 : 0 < aa := by linarith
  have hb0 : 0 < b := by linarith
  set M₂ := T * L / (2 * π) * (b * ℓ ^ 2 + L ^ 2 * J) with hM₂def
  have hden : 0 < b * ℓ ^ 2 + L ^ 2 * J := by
    have h1' : 0 < b * ℓ ^ 2 := by positivity
    nlinarith [mul_nonneg (sq_nonneg L) hJ0]
  have hM0 : 0 < M₂ := by
    rw [hM₂def]
    positivity
  set Φ₀ := cRatio (L / ℓ) aa b J * N with hΦ₀def
  have hdenR : 0 < b + (L / ℓ) ^ 2 * J := by
    have : 0 ≤ (L / ℓ) ^ 2 * J := by positivity
    linarith
  have hF0 : 0 < cRatio (L / ℓ) aa b J := by
    unfold cRatio
    apply div_pos (by positivity) hdenR
  have hΦ0 : 0 < Φ₀ := mul_pos hF0 hN0
  have key : Φ₀ * M₂ = (aa * L) ^ 2 * N * (T * ℓ / (2 * π)) := by
    rw [hΦ₀def, hM₂def]
    unfold cRatio
    field_simp
    try ring
  set α := G - aa * L * N with hαdef
  set bb := G2 - M₂ with hbbdef
  set δ := N - T * ℓ / (2 * π) with hδdef
  have hbb : |bb| ≤ C₂ * (E * M₂) := h2
  have hG2low : M₂ / 2 ≤ G2 := by
    have hx1 : -(C₂ * (E * M₂)) ≤ bb := (abs_le.mp hbb).1
    have hx2 : C₂ * (E * M₂) ≤ 1 / 2 * M₂ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hs2 hM0.le
    have hx3 : bb = G2 - M₂ := hbbdef
    linarith
  have hG2pos : 0 < G2 := lt_of_lt_of_le (by positivity) hG2low
  have hid : G ^ 2 - Φ₀ * G2 = (aa * L) ^ 2 * N * δ + 2 * (aa * L * N) * α + α ^ 2 - Φ₀ * bb := by
    have hG : G = aa * L * N + α := by rw [hαdef]; ring
    have hG2 : G2 = M₂ + bb := by rw [hbbdef]; ring
    rw [hG, hG2, hδdef]
    linear_combination (-1 : ℝ) * key
  have hLN0 : 0 ≤ aa * L * N := by positivity
  have hNup : N ≤ T * ℓ / (2 * π) + A * ℓ := by
    have := (abs_le.mp hN).2
    nlinarith
  have hLN2 : (aa * L * N) ^ 2 ≤ 2 * (Φ₀ * M₂) := by
    rw [key]
    have h' : (aa * L * N) ^ 2 = (aa * L) ^ 2 * N * N := by ring
    rw [h']
    have hc : (aa * L) ^ 2 * N * N ≤ (aa * L) ^ 2 * N * (T * ℓ / (2 * π) + A * ℓ) :=
      mul_le_mul_of_nonneg_left hNup (by positivity)
    have hd : (aa * L) ^ 2 * N * (A * ℓ) ≤ (aa * L) ^ 2 * N * (T * ℓ / (2 * π)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have t1 : |(aa * L) ^ 2 * N * δ| ≤ 2 * π * A * (E * (Φ₀ * M₂)) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (aa * L) ^ 2 * N)]
    calc (aa * L) ^ 2 * N * |δ| ≤ (aa * L) ^ 2 * N * (A * ℓ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hN.trans (mul_le_mul_of_nonneg_left hℓl hA)
      _ = 2 * π * A * ((1 / T) * ((aa * L) ^ 2 * N * (T * ℓ / (2 * π)))) := by
          field_simp
          try ring
      _ = 2 * π * A * ((1 / T) * (Φ₀ * M₂)) := by rw [key]
      _ ≤ 2 * π * A * (E * (Φ₀ * M₂)) := by
          have h0 : 0 ≤ Φ₀ * M₂ := by positivity
          gcongr
  have t2 : |2 * (aa * L * N) * α| ≤ 4 * C₁ * (E * (Φ₀ * M₂)) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (aa * L * N))]
    calc 2 * (aa * L * N) * |α| ≤ 2 * (aa * L * N) * (C₁ * (E * (aa * L * N))) := by gcongr
      _ = 2 * C₁ * E * (aa * L * N) ^ 2 := by ring
      _ ≤ 2 * C₁ * E * (2 * (Φ₀ * M₂)) := by gcongr
      _ = 4 * C₁ * (E * (Φ₀ * M₂)) := by ring
  have t3 : |α ^ 2| ≤ C₁ * (E * (Φ₀ * M₂)) := by
    rw [abs_pow]
    calc |α| ^ 2 ≤ (C₁ * (E * (aa * L * N))) ^ 2 := by gcongr
      _ = (C₁ * E) * (C₁ * E) * (aa * L * N) ^ 2 := by ring
      _ ≤ (C₁ * E) * (1 / 2) * (2 * (Φ₀ * M₂)) := by
          have h0 : 0 ≤ C₁ * E := by positivity
          gcongr
      _ = C₁ * (E * (Φ₀ * M₂)) := by ring
  have t4 : |Φ₀ * bb| ≤ C₂ * (E * (Φ₀ * M₂)) := by
    rw [abs_mul, abs_of_pos hΦ0]
    calc Φ₀ * |bb| ≤ Φ₀ * (C₂ * (E * M₂)) := by gcongr
      _ = C₂ * (E * (Φ₀ * M₂)) := by ring
  have hnum : |G ^ 2 - Φ₀ * G2| ≤ (2 * π * A + 5 * C₁ + C₂) * (E * (Φ₀ * M₂)) := by
    rw [hid]
    calc |(aa * L) ^ 2 * N * δ + 2 * (aa * L * N) * α + α ^ 2 - Φ₀ * bb|
        ≤ |(aa * L) ^ 2 * N * δ| + |2 * (aa * L * N) * α| + |α ^ 2| + |Φ₀ * bb| := by
          refine (abs_sub _ _).trans ?_
          linarith [abs_add_three ((aa * L) ^ 2 * N * δ) (2 * (aa * L * N) * α) (α ^ 2)]
      _ ≤ 2 * π * A * (E * (Φ₀ * M₂)) + 4 * C₁ * (E * (Φ₀ * M₂)) + C₁ * (E * (Φ₀ * M₂))
          + C₂ * (E * (Φ₀ * M₂)) := by gcongr
      _ = (2 * π * A + 5 * C₁ + C₂) * (E * (Φ₀ * M₂)) := by ring
  have hq : G ^ 2 / G2 - Φ₀ = (G ^ 2 - Φ₀ * G2) / G2 := by
    field_simp
  rw [hq, abs_div, abs_of_pos hG2pos, div_le_iff₀ hG2pos]
  calc |G ^ 2 - Φ₀ * G2| ≤ (2 * π * A + 5 * C₁ + C₂) * (E * (Φ₀ * M₂)) := hnum
    _ = 2 * (2 * π * A + 5 * C₁ + C₂) * (E * Φ₀) * (M₂ / 2) := by ring
    _ ≤ 2 * (2 * π * A + 5 * C₁ + C₂) * (E * Φ₀) * G2 := by
        have h0 : 0 ≤ 2 * (2 * π * A + 5 * C₁ + C₂) * (E * Φ₀) := by positivity
        gcongr

section assemblyD
variable {D} (h : FactsD D)
include h

private lemma NcntD_lower : ∀ᶠ T in Filter.atTop, T * l T / (4 * π) ≤ D.Ncnt T := by
  obtain ⟨A, hA, hN⟩ := h.rvm.eventually_le
  filter_upwards [hN, Filter.eventually_ge_atTop (4 * π * A), PaperParams.eventually_l_ge 0]
    with T hN hTA hl
  have hπ := Real.pi_pos
  have h1 : -(A * l T) ≤ D.Ncnt T - T * ell1 T / (2 * π) := (abs_le.mp hN).1
  have h2 : T * l T ≤ T * ell1 T :=
    mul_le_mul_of_nonneg_left (PaperParams.l_le_ell1 T) (by nlinarith)
  have h3 : T * l T / (2 * π) ≤ T * ell1 T / (2 * π) :=
    div_le_div_of_nonneg_right h2 (by positivity)
  have h4 : T * l T / (4 * π) = T * l T / (2 * π) - T * l T / (4 * π) := by ring
  have h5 : A * l T ≤ T * l T / (4 * π) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  linarith

private lemma T_le_NcntD : ∀ᶠ T in Filter.atTop, T ≤ 4 * π * D.Ncnt T := by
  filter_upwards [NcntD_lower h, PaperParams.eventually_l_ge 1, Filter.eventually_ge_atTop 0]
    with T hN hl hT
  have hπ := Real.pi_pos
  have : T * l T ≤ 4 * π * D.Ncnt T := by
    rw [div_le_iff₀ (by positivity)] at hN
    linarith
  nlinarith

private lemma NcntD_pos : ∀ᶠ T in Filter.atTop, 0 < D.Ncnt T := by
  filter_upwards [NcntD_lower h, PaperParams.eventually_l_ge 1, Filter.eventually_ge_atTop 1]
    with T hN hl hT
  have hπ := Real.pi_pos
  have h0 : (0:ℝ) < T * l T / (4 * π) := by positivity
  linarith

private lemma regimeD : ∀ᶠ T in Filter.atTop, 1 ≤ T ∧ 1 ≤ l T ∧ 1 ≤ Real.log (l T)
    ∧ 1 ≤ P.L T ∧ 1 ≤ P.X T ∧ P.L T ≤ l T ∧ P.X T ≤ T := by
  have hlam := h.lam_pos
  filter_upwards [Filter.eventually_ge_atTop 1, PaperParams.eventually_l_ge 1,
    PaperParams.eventually_log_l_ge 1, PaperParams.eventually_L_ge P hlam 1,
    PaperParams.eventually_one_le_X P hlam,
    PaperParams.eventually_X_le_T P hlam h.lam_le_one] with T h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, PaperParams.L_le_l P h.lam_le_one (by linarith), h6⟩

/-- the D-form of [eq:tr1]': tr G̃ = a L N (1 + O(𝓔)) — a STAYS (no collapse to 1). -/
private lemma tr1'D : EvBound (fun T => D.trG T - D.aT T * P.L T * D.Ncnt T)
    (fun T => P.calE T * (D.aT T * P.L T * D.Ncnt T)) := by
  obtain ⟨C₁, hC₁, h1⟩ := h.prop_trace.eventually_le
  have hlam := h.lam_pos
  have hw : 0 ≤ P.w := by linarith [h.one_le_w]
  refine EvBound.of_eventually_le (c := 8 * π * C₁) (by positivity) ?_
  filter_upwards [h1, h.ab_range, PaperParams.calE_ge_rpow hlam hw,
    PaperParams.calE_nonneg_eventually hlam hw, T_le_NcntD h, NcntD_pos h,
    Filter.eventually_ge_atTop 1, PaperParams.eventually_L_ge P hlam 1]
    with T h1 hab hEr hE0 hTN hN0 hT1 hL1
  obtain ⟨hb2, hba, ha1, hJ0, hJ1⟩ := hab
  have hT0 : 0 < T := by linarith
  have hL0 : 0 ≤ P.L T := by linarith
  have ha2 : 1 / 2 ≤ D.aT T := le_trans hb2 hba
  have hB : C₁ * (P.L T * Real.sqrt (P.X T))
      ≤ 8 * π * C₁ * (P.calE T * (D.aT T * P.L T * D.Ncnt T)) := by
    have hs : Real.sqrt (P.X T) ≤ T ^ (P.lam / 2 - 1) * T := by
      rw [PaperParams.rpow_half_sub_one_mul hT0]
      exact PaperParams.sqrt_X_le_rpow P hlam hT0
    have hs2 : T ^ (P.lam / 2 - 1) * T ≤ P.calE T * (4 * π * D.Ncnt T) :=
      mul_le_mul hEr hTN hT0.le hE0
    calc C₁ * (P.L T * Real.sqrt (P.X T))
        ≤ C₁ * (P.L T * (P.calE T * (4 * π * D.Ncnt T))) := by gcongr; exact hs.trans hs2
      _ = 4 * π * C₁ * (P.calE T * (P.L T * D.Ncnt T)) := by ring
      _ ≤ 4 * π * C₁ * (P.calE T * ((2 * D.aT T) * P.L T * D.Ncnt T)) := by
          have h2a : (1:ℝ) ≤ 2 * D.aT T := by linarith
          have hnn : 0 ≤ P.calE T := hE0
          have hLN : 0 ≤ P.L T * D.Ncnt T := mul_nonneg hL0 hN0.le
          calc 4 * π * C₁ * (P.calE T * (P.L T * D.Ncnt T))
              = 4 * π * C₁ * (P.calE T * (1 * P.L T * D.Ncnt T)) := by ring
            _ ≤ 4 * π * C₁ * (P.calE T * (2 * D.aT T * P.L T * D.Ncnt T)) := by
                gcongr
          
      _ = 8 * π * C₁ * (P.calE T * (D.aT T * P.L T * D.Ncnt T)) := by ring
  exact le_trans h1 hB

end assemblyD

section assemblyD2
variable {D} (h : FactsD D)
include h

/-- the D main term: (TL/2π)(b ℓ₁² + L² J) [eq:ratio-general]. -/
private def mainTr2D (P : Params) (D : DataD P) (T : ℝ) : ℝ :=
  T * P.L T / (2 * π) * (D.bT T * ell1 T ^ 2 + P.L T ^ 2 * D.JT T)

/-- the D-form of [eq:tr2], first form (verbatim mirror of PrimeSide.tr2_first over FactsD). -/
private lemma tr2_firstD : EvBound
    (fun T => D.trG2 T - (2 * π * D.bT T * P.L T * D.intMu2 T + T / π * D.sumL2g T))
    (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
  have e3 : EvBound (fun T => D.Mmumu T - 2 * π * D.bT T * P.L T * D.intMu2 T)
      (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
    refine h.prop_mumu.mono_right' one_pos ?_
    filter_upwards [regimeD h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩
    have hlogL : Real.log (P.L T) ≤ Real.log (l T) := Real.log_le_log (by linarith) hLl
    have hlogL0 : 0 ≤ Real.log (P.L T) := Real.log_nonneg hL
    calc l T ^ 2 * Real.log (P.L T) ≤ l T ^ 2 * Real.log (l T) := by gcongr
      _ = 1 * l T * Real.log (l T) * l T := by ring
      _ ≤ P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = 1 * (P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := (one_mul _).symm
  have e4 : EvBound (fun T => D.MPP T - T / π * D.sumL2g T)
      (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
    refine h.prop_PP.mono_right' one_pos ?_
    filter_upwards [regimeD h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩
    calc P.L T ^ 2 * P.X T = P.L T * P.L T * 1 * P.X T := by ring
      _ ≤ P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = 1 * (P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := (one_mul _).symm
  have hsqrtX : ∀ᶠ T in Filter.atTop, Real.sqrt (P.X T) ≤ P.X T := by
    filter_upwards [regimeD h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have e5 : EvBound D.MmuP (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
    refine h.cross_muP.mono_right' one_pos ?_
    filter_upwards [regimeD h, hsqrtX] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩ hs
    calc l T * Real.sqrt (P.X T) ≤ l T * P.X T := by gcongr
      _ = 1 * l T * 1 * (0 + P.X T) := by ring
      _ ≤ P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = 1 * (P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := (one_mul _).symm
  have e6 : EvBound D.MmuPi (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
    refine h.cross_muPi.mono_right' one_pos ?_
    filter_upwards [regimeD h, hsqrtX] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩ hs
    calc l T * P.L T * Real.sqrt (P.X T) ≤ l T * P.L T * P.X T := by gcongr
      _ = P.L T * l T * 1 * (0 + P.X T) := by ring
      _ ≤ P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = 1 * (P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := (one_mul _).symm
  have e7 : EvBound D.MPPi (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
    refine h.cross_PPi.mono_right' one_pos ?_
    filter_upwards [regimeD h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩
    calc P.L T * P.X T = P.L T * 1 * 1 * (0 + P.X T) := by ring
      _ ≤ P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = 1 * (P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := (one_mul _).symm
  have e8 : EvBound D.MPiPi (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
    refine h.cross_PiPi.mono_right' one_pos ?_
    filter_upwards [regimeD h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩
    calc P.L T * P.X T / T ≤ P.L T * P.X T := div_le_self (by nlinarith) hT
      _ = P.L T * 1 * 1 * (0 + P.X T) := by ring
      _ ≤ P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = 1 * (P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := (one_mul _).symm
  have S := h.lem_ends.add (e3.add (e4.add (((e5.const_mul 2).add (e6.const_mul 2)).add
    ((e7.const_mul 2).add e8))))
  refine S.congr_left ?_
  filter_upwards [h.Msplit] with T hM
  rw [hM]
  ring

/-- the D-form of [eq:tr2], second form: tr G̃² = (TL/2π)(bℓ₁² + L²J)(1 + O(𝓔_T)). -/
private lemma tr2D : EvBound (fun T => D.trG2 T - mainTr2D P D T)
    (fun T => P.calE T * mainTr2D P D T) := by
  have hlam := h.lam_pos
  have hw1 := h.one_le_w
  have hw : 0 ≤ P.w := by linarith
  obtain ⟨CR, hCR, hR⟩ := (tr2_firstD h).eventually_le
  obtain ⟨Cμ, hCμ, hμ⟩ := h.muints2.eventually_le
  obtain ⟨Cs, hCs, hsj⟩ := h.sumJ.eventually_le
  refine EvBound.of_eventually_le (c := 4 * π * CR + 2 * Cμ + 4 * Cs) (by positivity) ?_
  filter_upwards [hR, hμ, hsj, h.ab_range, regimeD h, PaperParams.calE_ge_w_div_L hlam hw,
    PaperParams.calE_ge_mid hlam hw, PaperParams.calE_nonneg_eventually hlam hw,
    PaperParams.eventually_L_ge P hlam (2 * P.w)]
    with T hR hμ hsj hab hreg hEw hEmid hE0 hL2w
  obtain ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩ := hreg
  obtain ⟨hb2, hba, ha1, hJ0, -⟩ := hab
  have hSJ : |D.sumL2g T - P.L T ^ 3 * D.JT T / 2| ≤ Cs * P.L T ^ 2 := by
    have e : P.L T ^ 3 * D.JT T / 2 = P.L T ^ 3 / 2 * D.JT T := by ring
    rw [e]
    exact hsj
  exact tr2D_pointwise T (P.L T) (ell1 T) (l T) (P.X T) (P.calE T) (D.sumL2g T) (D.intMu2 T)
    (D.bT T) (D.JT T) (D.trG2 T) P.w CR Cμ Cs hT hL hl hlog hX (PaperParams.l_le_ell1 T) hLl hw1 hL2w
    hb2 (hba.trans ha1) hJ0 hE0 hEw hEmid hCR.le hCμ.le hCs.le hR hμ hSJ

/-- the D-form of [eq:ratio]: (tr G̃)²/tr G̃² = cRatio(λ₁; a, b, J)·N·(1 + O(𝓔_T)). -/
private lemma ratioD : EvBound
    (fun T => D.trG T ^ 2 / D.trG2 T - cRatio (P.lam1 T) (D.aT T) (D.bT T) (D.JT T) * D.Ncnt T)
    (fun T => P.calE T * (cRatio (P.lam1 T) (D.aT T) (D.bT T) (D.JT T) * D.Ncnt T)) := by
  have hlam := h.lam_pos
  have hlam1 := h.lam_le_one
  have hw : 0 ≤ P.w := by linarith [h.one_le_w]
  obtain ⟨C₁, hC₁, h1⟩ := (tr1'D h).eventually_le
  obtain ⟨C₂, hC₂, h2⟩ := (tr2D h).eventually_le
  obtain ⟨A, hA, hN⟩ := h.rvm.eventually_le
  have hcal := PaperParams.calE_tendsto_zero hlam hlam1 hw
  have hs1 := eventually_const_mul_le_half hcal hC₁
  have hs2 := eventually_const_mul_le_half hcal hC₂
  refine EvBound.of_eventually_le (c := 2 * (2 * π * A + 5 * C₁ + C₂)) (by positivity) ?_
  filter_upwards [h1, h2, hN, hs1, hs2, regimeD h, h.ab_range, PaperParams.calE_ge_rpow hlam hw,
    PaperParams.calE_nonneg_eventually hlam hw, NcntD_pos h, Filter.eventually_ge_atTop (2 * π * A)]
    with T h1 h2 hN hs1 hs2 hreg hab hEr hE0 hN0 hTA
  obtain ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩ := hreg
  obtain ⟨hb2, hba, -, hJ0, -⟩ := hab
  have hET : 1 / T ≤ P.calE T := by
    refine le_trans ?_ hEr
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  exact ratioD_pointwise T (P.L T) (ell1 T) (l T) (P.calE T) (D.Ncnt T) (D.trG T) (D.trG2 T)
    A (D.aT T) (D.bT T) (D.JT T) C₁ C₂ hT (by linarith) (hl.trans (PaperParams.l_le_ell1 T)) (PaperParams.l_le_ell1 T)
    hN0 hE0 hET hA.le hC₁.le hC₂.le (le_trans hb2 hba) hb2 hJ0 hs1 hs2 hTA h1 h2 hN

end assemblyD2

/-- pointwise form of the hat-units Frobenius bound: the positive part of
G2/(aL)² − (1/cRatio)N is ≤ (4πA + 2C₂)·E·((1/cRatio)N). -/
theorem frhatD_pointwise (T L ℓ lT E N G2 A aa b J C₂ : ℝ)
    (hT : 1 ≤ T) (hL : 0 < L) (hℓ1 : 1 ≤ ℓ) (hℓl : lT ≤ ℓ) (hN0 : 0 < N) (hE0 : 0 ≤ E)
    (hET : 1 / T ≤ E) (hA : 0 ≤ A) (hC₂ : 0 ≤ C₂)
    (ha : 1 / 2 ≤ aa) (hb : 1 / 2 ≤ b) (hJ0 : 0 ≤ J)
    (hTA : 4 * π * A ≤ T)
    (h2 : |G2 - T * L / (2 * π) * (b * ℓ ^ 2 + L ^ 2 * J)|
      ≤ C₂ * (E * (T * L / (2 * π) * (b * ℓ ^ 2 + L ^ 2 * J))))
    (hN : |N - T * ℓ / (2 * π)| ≤ A * lT) :
    max (G2 / (aa * L) ^ 2 - (cRatio (L / ℓ) aa b J)⁻¹ * N) 0
      ≤ (4 * π * A + 2 * C₂) * (E * ((cRatio (L / ℓ) aa b J)⁻¹ * N)) := by
  have hπ : 0 < π := Real.pi_pos
  have hT0 : 0 < T := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have ha0 : 0 < aa := by linarith
  have hb0 : 0 < b := by linarith
  set M₂ := T * L / (2 * π) * (b * ℓ ^ 2 + L ^ 2 * J) with hM₂def
  have hdenR : 0 < b + (L / ℓ) ^ 2 * J := by
    have : 0 ≤ (L / ℓ) ^ 2 * J := by positivity
    linarith
  have hc0 : 0 < cRatio (L / ℓ) aa b J := by
    unfold cRatio
    apply div_pos (by positivity) hdenR
  have hcinv0 : 0 ≤ (cRatio (L / ℓ) aa b J)⁻¹ := (inv_pos.mpr hc0).le
  -- the N-free key identity
  have keyc : cRatio (L / ℓ) aa b J * M₂ = (aa * L) ^ 2 * (T * ℓ / (2 * π)) := by
    rw [hM₂def]
    unfold cRatio
    field_simp
    try ring
  have hM2aL : M₂ / (aa * L) ^ 2 = (cRatio (L / ℓ) aa b J)⁻¹ * (T * ℓ / (2 * π)) := by
    rw [eq_comm, inv_mul_eq_div, div_eq_div_iff hc0.ne' (by positivity : ((aa * L) ^ 2 : ℝ) ≠ 0)]
    linear_combination -keyc
  -- N vs Tℓ/2π
  have hNlow : T * ℓ / (4 * π) ≤ N := by
    have h1 := (abs_le.mp hN).1
    have hAl : A * lT ≤ T * ℓ / (4 * π) := by
      calc A * lT ≤ A * ℓ := by
            apply mul_le_mul_of_nonneg_left hℓl hA
        _ ≤ T / (4 * π) * ℓ := by
            apply mul_le_mul_of_nonneg_right _ hℓ0.le
            rw [le_div_iff₀ (by positivity)]
            linarith
        _ = T * ℓ / (4 * π) := by ring
    have he : T * ℓ / (4 * π) = T * ℓ / (2 * π) - T * ℓ / (4 * π) := by ring
    linarith
  have hTl2N : T * ℓ / (2 * π) ≤ 2 * N := by
    have he : T * ℓ / (2 * π) = 2 * (T * ℓ / (4 * π)) := by ring
    linarith
  have hAlEN : A * lT ≤ 4 * π * A * (E * N) := by
    calc A * lT ≤ A * ℓ := mul_le_mul_of_nonneg_left hℓl hA
      _ ≤ A * (4 * π * N / T) := by
          apply mul_le_mul_of_nonneg_left _ hA
          rw [le_div_iff₀ hT0]
          calc ℓ * T = 2 * π * (T * ℓ / (2 * π)) := by field_simp; try ring
            _ ≤ 2 * π * (2 * N) := by gcongr
            _ = 4 * π * N := by ring
      _ = 4 * π * A * ((1 / T) * N) := by field_simp; try ring
      _ ≤ 4 * π * A * (E * N) := by
          have h0 : 0 ≤ N := hN0.le
          gcongr
  -- the positive-part bound
  have hup : G2 / (aa * L) ^ 2 - (cRatio (L / ℓ) aa b J)⁻¹ * N
      ≤ (4 * π * A + 2 * C₂) * (E * ((cRatio (L / ℓ) aa b J)⁻¹ * N)) := by
    have hG2 : G2 ≤ M₂ + C₂ * (E * M₂) := by
      have := (abs_le.mp h2).2
      linarith
    have hM₂0 : 0 ≤ M₂ := by
      rw [hM₂def]
      have : 0 ≤ b * ℓ ^ 2 + L ^ 2 * J := by positivity
      positivity
    have step1 : G2 / (aa * L) ^ 2 ≤ (1 + C₂ * E) * (M₂ / (aa * L) ^ 2) := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (aa * L) ^ 2)]
      calc G2 ≤ M₂ + C₂ * (E * M₂) := hG2
        _ = (1 + C₂ * E) * M₂ := by ring
        _ = (1 + C₂ * E) * (M₂ / (aa * L) ^ 2) * (aa * L) ^ 2 := by
            field_simp
    rw [hM2aL] at step1
    have step2 : (1 + C₂ * E) * ((cRatio (L / ℓ) aa b J)⁻¹ * (T * ℓ / (2 * π)))
        - (cRatio (L / ℓ) aa b J)⁻¹ * N
        ≤ (cRatio (L / ℓ) aa b J)⁻¹ * (A * lT)
          + C₂ * E * ((cRatio (L / ℓ) aa b J)⁻¹ * (2 * N)) := by
      have hd : T * ℓ / (2 * π) - N ≤ A * lT := by
        have := (abs_le.mp hN).1
        linarith
      have e : (1 + C₂ * E) * ((cRatio (L / ℓ) aa b J)⁻¹ * (T * ℓ / (2 * π)))
          - (cRatio (L / ℓ) aa b J)⁻¹ * N
          = (cRatio (L / ℓ) aa b J)⁻¹ * (T * ℓ / (2 * π) - N)
            + C₂ * E * ((cRatio (L / ℓ) aa b J)⁻¹ * (T * ℓ / (2 * π))) := by
        ring
      rw [e]
      have t1' : (cRatio (L / ℓ) aa b J)⁻¹ * (T * ℓ / (2 * π) - N)
          ≤ (cRatio (L / ℓ) aa b J)⁻¹ * (A * lT) :=
        mul_le_mul_of_nonneg_left hd hcinv0
      have t2' : C₂ * E * ((cRatio (L / ℓ) aa b J)⁻¹ * (T * ℓ / (2 * π)))
          ≤ C₂ * E * ((cRatio (L / ℓ) aa b J)⁻¹ * (2 * N)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hTl2N hcinv0
      linarith
    have t3' : (cRatio (L / ℓ) aa b J)⁻¹ * (A * lT)
        ≤ 4 * π * A * (E * ((cRatio (L / ℓ) aa b J)⁻¹ * N)) := by
      calc (cRatio (L / ℓ) aa b J)⁻¹ * (A * lT)
          ≤ (cRatio (L / ℓ) aa b J)⁻¹ * (4 * π * A * (E * N)) :=
            mul_le_mul_of_nonneg_left hAlEN hcinv0
        _ = 4 * π * A * (E * ((cRatio (L / ℓ) aa b J)⁻¹ * N)) := by ring
    calc G2 / (aa * L) ^ 2 - (cRatio (L / ℓ) aa b J)⁻¹ * N
        ≤ (1 + C₂ * E) * ((cRatio (L / ℓ) aa b J)⁻¹ * (T * ℓ / (2 * π)))
          - (cRatio (L / ℓ) aa b J)⁻¹ * N := by linarith
      _ ≤ (cRatio (L / ℓ) aa b J)⁻¹ * (A * lT)
          + C₂ * E * ((cRatio (L / ℓ) aa b J)⁻¹ * (2 * N)) := step2
      _ ≤ 4 * π * A * (E * ((cRatio (L / ℓ) aa b J)⁻¹ * N))
          + 2 * C₂ * (E * ((cRatio (L / ℓ) aa b J)⁻¹ * N)) := by
          have e2 : C₂ * E * ((cRatio (L / ℓ) aa b J)⁻¹ * (2 * N))
              = 2 * C₂ * (E * ((cRatio (L / ℓ) aa b J)⁻¹ * N)) := by ring
          linarith [t3', e2.le, e2.ge]
      _ = (4 * π * A + 2 * C₂) * (E * ((cRatio (L / ℓ) aa b J)⁻¹ * N)) := by ring
  exact max_le hup (by positivity)

/-- the frhat field: the D-form hat-units second-moment upper bound. -/
private lemma frhatD {D : DataD P} (h : FactsD D) : EvBound
    (fun T => max (D.trG2 T / (D.aT T * P.L T) ^ 2
        - (cRatio (P.lam1 T) (D.aT T) (D.bT T) (D.JT T))⁻¹ * D.Ncnt T) 0)
    (fun T => P.calE T * ((cRatio (P.lam1 T) (D.aT T) (D.bT T) (D.JT T))⁻¹ * D.Ncnt T)) := by
  have hlam := h.lam_pos
  have hw : 0 ≤ P.w := by linarith [h.one_le_w]
  obtain ⟨C₂, hC₂, h2⟩ := (tr2D h).eventually_le
  obtain ⟨A, hA, hN⟩ := h.rvm.eventually_le
  refine EvBound.of_eventually_le (c := 4 * π * A + 2 * C₂) (by positivity) ?_
  filter_upwards [h2, hN, regimeD h, h.ab_range, PaperParams.calE_ge_rpow hlam hw,
    PaperParams.calE_nonneg_eventually hlam hw, NcntD_pos h,
    Filter.eventually_ge_atTop (4 * π * A)]
    with T h2 hN hreg hab hEr hE0 hN0 hTA
  obtain ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩ := hreg
  obtain ⟨hb2, hba, -, hJ0, -⟩ := hab
  have hET : 1 / T ≤ P.calE T := by
    refine le_trans ?_ hEr
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  refine le_trans (le_of_eq (abs_of_nonneg (le_max_right _ _))) ?_
  exact frhatD_pointwise T (P.L T) (ell1 T) (l T) (P.calE T) (D.Ncnt T) (D.trG2 T)
    A (D.aT T) (D.bT T) (D.JT T) C₂ hT (by linarith) (hl.trans (PaperParams.l_le_ell1 T))
    (PaperParams.l_le_ell1 T) hN0 hE0 hET hA.le hC₂.le (le_trans hb2 hba) hb2 hJ0 hTA h2 hN

/-- **[eq:ratio-general] assembly**: the D-interface traces bounds with ratio constant
cRatio λ₁ a b J. The body mirrors Zeta23.PrimeSide.tracesBounds_of_facts with b, J
symbolic. -/
theorem tracesBoundsD_of_factsD (h : FactsD D) :
    TracesBoundsD P D.aT D.bT D.JT D.trG D.trG2 D.Ncnt where
  tr1 := h.prop_trace
  ratio := ratioD h
  frhat := frhatD h

end ThmD
end Zeta23
