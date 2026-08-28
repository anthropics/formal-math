/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/FullLineChiAssembly.lean — the R → ∞ assembly of `full_line_identity_chi`
(two-character statement) from: rectangle_identity_chi (ContourChi; no pole terms),
good_heights_chi (FullLineChi), horizontal_vanish_chi (HorizontalChi),
verticals_eq_chi + zero_sum_limit_chi (FullLineChiFold), and the χ majorant pack
(FullLineChiProof).  Template: Zeta23/WeilEF/FullLineAssembly.lean.
-/
import Zeta23.ThmE.FullLineChiProof
import Zeta23.ThmE.FullLineChiFold
import Zeta23.ThmE.HorizontalChi
import Zeta23.WeilEF.FullLineAssembly

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Complex MeasureTheory Real Set Topology Filter DirichletCharacter
open scoped BigOperators

namespace Zeta23
namespace ThmE

open Zeta23.WeilEF

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-! ## Good heights, re-indexed (R_j ∈ [j+7, j+8]) -/

theorem exists_heights_chi (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∃ Cg : ℝ, 0 < Cg ∧ ∃ R : ℕ → ℝ, ∀ j : ℕ,
    (j : ℝ) + 7 ≤ R j ∧ R j ≤ (j : ℝ) + 8 ∧
    ∀ s : ℂ, (s.im = R j ∨ s.im = -R j) → 1 / 2 ≤ s.re → s.re ≤ 2 →
      χ.LFunction s ≠ 0 ∧ ‖logDeriv χ.LFunction s‖ ≤ Cg * (Real.log ((q:ℝ) * ((j : ℝ) + 10))) ^ 2 := by
  obtain ⟨C, hC, h⟩ := good_heights_chi hq hprim
  have hex : ∀ j : ℕ, ∃ R : ℝ, ((j + 7 : ℕ) : ℝ) ≤ R ∧ R ≤ ((j + 7 : ℕ) : ℝ) + 1 ∧
      ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 / 2 ≤ s.re → s.re ≤ 2 →
        χ.LFunction s ≠ 0 ∧
        ‖logDeriv χ.LFunction s‖ ≤ C * (Real.log ((q:ℝ) * (((j + 7 : ℕ) : ℝ) + 3))) ^ 2 :=
    fun j => h (j + 7) (by omega)
  refine ⟨C, hC, fun j => (hex j).choose, fun j => ?_⟩
  dsimp only
  obtain ⟨hs1, hs2, hs3⟩ := (hex j).choose_spec
  have e : ((j + 7 : ℕ) : ℝ) = (j : ℝ) + 7 := by push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · calc (j : ℝ) + 7 = ((j + 7 : ℕ) : ℝ) := e.symm
      _ ≤ _ := hs1
  · exact hs2.trans (by rw [e]; linarith)
  · intro s him h1 h2
    have e3 : Real.log ((q:ℝ) * (((j + 7 : ℕ) : ℝ) + 3)) = Real.log ((q:ℝ) * ((j : ℝ) + 10)) := by
      rw [e]; ring_nf
    obtain ⟨h3, h4⟩ := hs3 s him h1 h2
    exact ⟨h3, by rwa [e3] at h4⟩

/-! ## Λ(·,χ) ≠ 0 on the horizontal sides (left half by the functional equation + conjugation:
Λ_sym(s,χ) = W(χ)·conj Λ_sym(1 − conj s, χ), and 1 − conj s has re = 1 − re s > 1/2, SAME im) -/

theorem completedL_ne_zero_on_horizontals (hq : 1 < q) (hprim : χ.IsPrimitive)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) {R : ℝ}
    (hL : ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 / 2 ≤ s.re → s.re ≤ 2 → χ.LFunction s ≠ 0) :
    ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 - c ≤ s.re → s.re ≤ c → completedLFunction χ s ≠ 0 := by
  have hχ1 : χ ≠ 1 := ne_one_of_primitive hq hprim
  -- the right half: a zero of Λ with re > 0 is a nontrivial zero of L
  have aux : ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 / 2 ≤ s.re → s.re ≤ 2 →
      completedLSym χ s ≠ 0 := by
    intro s him h1 h2 h0
    have hnt := (completedLSym_eq_zero_iff hq hprim).mp h0
    exact hL s him h1 h2 hnt.1
  intro s him h1 h2 h0
  have h0' : completedLSym χ s = 0 := (completedLSym_eq_zero_iff' s).mpr h0
  rcases le_or_gt (1 / 2 : ℝ) s.re with hre | hre
  · exact aux s him hre (by linarith) h0'
  · -- Λ_sym χ s = Λ_sym χ (1 − (1 − s)) = W · Λ_sym χ⁻¹ (1 − s) = W · conj (Λ_sym χ (conj (1 − s)))
    have e1 : completedLSym χ s = rootNumber χ * completedLSym χ⁻¹ (1 - s) := by
      have := completedLSym_one_sub hprim (1 - s)
      rwa [sub_sub_cancel] at this
    rw [e1, completedLSym_inv_eq_conj hq hχ1, mul_eq_zero] at h0'
    rcases h0' with hW | hc
    · exact rootNumber_ne_zero hq hprim hW
    · rw [map_eq_zero] at hc
      apply aux ((starRingEnd ℂ) (1 - s)) ?_ ?_ ?_ hc
      · rcases him with h | h
        · left; simp [h]
        · right; simp [h]
      · simp; linarith
      · simp; linarith

/-! ## The full-line integrand is integrable -/

theorem integrable_FlineChi (hq : 1 < q) (hprim : χ.IsPrimitive) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) :
    Integrable (FlineChi χ k c) := by
  have hχ1 : χ ≠ 1 := ne_one_of_primitive hq hprim
  have hχ1' : χ⁻¹ ≠ 1 := fun h => hχ1 (inv_eq_one.mp h)
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hk hkc
  -- the two H factors
  set φ₁ : ℝ → ℂ := fun t => Hfn k ((c : ℂ) + t * I) with hφ₁
  set φ₂ : ℝ → ℂ := fun t => Hfn k (1 - c - t * I) with hφ₂
  have hφ₁c : Continuous φ₁ := continuous_Hfn_line hk hkc c
  have hφ₂c : Continuous φ₂ := by
    have h := continuous_Hfn_line hk hkc (1 - c)
    have : φ₂ = (fun t : ℝ => Hfn k (((1 - c : ℝ) : ℂ) + t * I)) ∘ fun t : ℝ => -t := by
      funext t; simp only [hφ₂, Function.comp_apply, one_sub_cast]
    rw [this]; exact h.comp continuous_neg
  have hφ₁b : ∀ t, ‖φ₁ t‖ ≤ C / (1 + t ^ 2) := fun t => hC c t (by linarith) (by linarith)
  have hφ₂b : ∀ t, ‖φ₂ t‖ ≤ C / (1 + t ^ 2) := by
    intro t
    have h2 := hC (1 - c) (-t) (by linarith) (by linarith)
    rw [← one_sub_cast, neg_sq] at h2
    exact h2
  -- four integrable pieces
  have hκ := parity_le_one' χ
  have hG₁ := integrable_mul_logDeriv_archChi_of_decay (q := q) (parity χ) hκ hφ₁c hC0 hφ₁b
    (by linarith : (1:ℝ)/2 ≤ c) hc2
  have hG₂ := integrable_mul_logDeriv_archChi_of_decay (q := q) (parity χ) hκ hφ₂c hC0 hφ₂b
    (by linarith : (1:ℝ)/2 ≤ c) hc2
  have hL₁ := integrable_mul_logDeriv_L_of_decay hχ1 hφ₁c hφ₁b hc1
  have hL₂ := integrable_mul_logDeriv_L_of_decay hχ1' hφ₂c hφ₂b hc1
  refine ((hG₁.add hL₁).add (hG₂.add hL₂)).congr (Eventually.of_forall fun t => ?_)
  have hre : 0 < ((c : ℂ) + t * I).re := by simp; linarith
  have hre1 : 1 ≤ ((c : ℂ) + t * I).re := by simp; linarith
  have hLne : χ.LFunction ((c : ℂ) + t * I) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hre1
  have hLne' : χ⁻¹.LFunction ((c : ℂ) + t * I) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχ1') hre1
  have e1 : logDeriv (completedLSym χ) ((c : ℂ) + t * I)
      = logDeriv (archChi q (parity χ)) ((c : ℂ) + t * I) + logDeriv χ.LFunction ((c : ℂ) + t * I) := by
    rw [← logDeriv_completedLSym_sub_L hq hχ1 hre hLne]; ring
  have e2 : logDeriv (completedLSym χ⁻¹) ((c : ℂ) + t * I)
      = logDeriv (archChi q (parity χ)) ((c : ℂ) + t * I) + logDeriv χ⁻¹.LFunction ((c : ℂ) + t * I) := by
    rw [← logDeriv_completedLSym_sub_L hq hχ1 hre hLne,
      ← logDeriv_completedLSym_sub_L_inv hq hχ1 hχ1' hre hLne hLne']; ring
  simp only [FlineChi, hφ₁, hφ₂, Pi.add_apply, e1, e2]
  ring

theorem tendsto_interval_FlineChi (hq : 1 < q) (hprim : χ.IsPrimitive) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2)
    {R : ℕ → ℝ} (hR : ∀ j : ℕ, (j : ℝ) ≤ R j) :
    Tendsto (fun j : ℕ => ∫ t in (-R j)..R j, FlineChi χ k c t) atTop
      (𝓝 (∫ t, FlineChi χ k c t)) := by
  have hRtop : Tendsto R atTop atTop := tendsto_atTop_mono hR tendsto_natCast_atTop_atTop
  exact intervalIntegral_tendsto_integral (integrable_FlineChi hq hprim hk hkc hc1 hc2)
    (tendsto_neg_atTop_atBot.comp hRtop) hRtop

/-! ## The assembly -/

/-- **Full-line identity for L(s,χ)** (two-character form). -/
theorem full_line_identity_chi' (hq : 1 < q) (hprim : χ.IsPrimitive)
    {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        (Hfn k ((c:ℝ) + t * I) * logDeriv (completedLSym χ) (((c:ℝ):ℂ) + t * I)
          + Hfn k (1 - c - t * I) * logDeriv (completedLSym χ⁻¹) (((c:ℝ):ℂ) + t * I))
      = ∑' ρ : (LZeros (LSeam_of hq hprim)).carrier,
          ((LZeros (LSeam_of hq hprim)).mult ρ : ℂ) * Hfn k ρ := by
  obtain ⟨Cg, hCg, R, hR⟩ := exists_heights_chi hq hprim
  set f : ℂ → ℂ := fun s => Hfn k s * logDeriv (completedLSym χ) s with hf
  -- the rectangle identity at every height R_j
  have hrect : ∀ j : ℕ, ∃ Z : Finset ℂ,
      ((Z : Set ℂ) = {ρ : ℂ | IsNontrivialZeroL χ ρ ∧ -R j < ρ.im ∧ ρ.im < R j}) ∧
      RectangleIntegral' f (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I)
        = ∑ ρ ∈ Z, (zeroMultL χ ρ : ℂ) * Hfn k ρ := by
    intro j
    obtain ⟨h1, h2, h3⟩ := hR j
    exact rectangle_identity_chi hq hprim hk hkc hc1 hc2 (R := R j) (by linarith)
      (completedL_ne_zero_on_horizontals hq hprim hc1 hc2
        (fun s him hr1 hr2 => (h3 s him hr1 hr2).1))
  choose Z hZ hE using hrect
  -- the three limits
  obtain ⟨hHtop, hHbot⟩ := horizontal_vanish_chi hq hprim hk hkc hc1 hc2 hCg hR
  have hZlim := zero_sum_limit_chi hq hprim hk hkc (R := R) (fun j => ⟨(hR j).1, (hR j).2.1⟩) hZ
  have hV := tendsto_interval_FlineChi hq hprim hk hkc hc1 hc2 (R := R)
    (fun j => by linarith [(hR j).1])
  -- decomposition of the normalized rectangle integral
  have hdec : ∀ j : ℕ, RectangleIntegral' f (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I)
      = (1 / (2 * Real.pi * I) : ℂ) * (HIntegral f (1 - c) c (-(R j)) - HIntegral f (1 - c) c (R j))
        + (1 / (2 * Real.pi) : ℂ) * ∫ t in (-R j)..R j, FlineChi χ k c t := by
    intro j
    obtain ⟨e1, e2, e3, e4⟩ := corner_re_im c (R j)
    rw [RectangleIntegral', RectangleIntegral, smul_eq_mul, e1, e2, e3, e4]
    have hv := verticals_eq_chi hq hprim hk hkc hc1 hc2 (R j)
    rw [hf]
    rw [show ∀ A B V₁ V₂ : ℂ, A - B + V₁ - V₂ = (A - B) + (V₁ - V₂) from fun _ _ _ _ => by ring, hv,
      smul_eq_mul, mul_add, inv_two_pi_I_mul_I]
  -- LHS → (1/2π) ∫ F
  have hL : Tendsto (fun j : ℕ => RectangleIntegral' f (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I))
      atTop (𝓝 ((1 / (2 * Real.pi) : ℂ) * ∫ t, FlineChi χ k c t)) := by
    have h := ((hHbot.sub hHtop).const_mul (1 / (2 * Real.pi * I) : ℂ)).add
      (hV.const_mul (1 / (2 * Real.pi) : ℂ))
    simp only [sub_zero, mul_zero, zero_add] at h
    refine h.congr fun j => ?_
    rw [hdec j]
  have hL' : Tendsto (fun j : ℕ => ∑ ρ ∈ Z j, (zeroMultL χ ρ : ℂ) * Hfn k ρ)
      atTop (𝓝 ((1 / (2 * Real.pi) : ℂ) * ∫ t, FlineChi χ k c t)) :=
    hL.congr fun j => hE j
  have := tendsto_nhds_unique hL' hZlim
  exact this

end ThmE
end Zeta23
