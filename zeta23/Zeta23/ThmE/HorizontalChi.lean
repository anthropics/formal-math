/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/HorizontalChi.lean — the horizontal sides of the explicit-formula rectangle for L(s,χ)
vanish along good heights.  The analogue for L(s,χ) of Zeta23/WeilEF/Horizontal.lean: ‖H‖ ≤ C_H/(1+R²) (norm_Hfn_le);
for re s ∈ [1/2, 3/2]: Λ'/Λ_sym = L'/L + (arch)' /arch (logDeriv_completedLSym_split, exists_parity,
norm_logDeriv_archChi_le); for re s < 1/2 reflect with logDeriv_completedLSym_one_sub_conj
(s ↦ 1 − conj s keeps the imaginary part); then length × sup and log²(q(j+10))/(1+(j+7)²) → 0.
-/
import Zeta23.ThmE.FullLineChiProof

noncomputable section

namespace Zeta23
namespace ThmE

open Complex Topology Filter Set MeasureTheory
open Zeta23.WeilEF

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **Horizontal sides vanish, χ-version** (used in `full_line_identity_chi`). -/
theorem horizontal_vanish_chi (hq : 1 < q) (hprim : χ.IsPrimitive) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) {Cg : ℝ} (hCg : 0 < Cg) {R : ℕ → ℝ}
    (hR : ∀ j : ℕ, (j : ℝ) + 7 ≤ R j ∧ R j ≤ (j : ℝ) + 8 ∧
      ∀ s : ℂ, (s.im = R j ∨ s.im = -R j) → 1/2 ≤ s.re → s.re ≤ 2 →
        χ.LFunction s ≠ 0 ∧ ‖logDeriv χ.LFunction s‖ ≤ Cg * (Real.log ((q:ℝ) * ((j : ℝ) + 10))) ^ 2) :
    Tendsto (fun j : ℕ => HIntegral (fun s => Hfn k s * logDeriv (completedLSym χ) s) (1 - c) c (R j))
      atTop (𝓝 0)
    ∧ Tendsto (fun j : ℕ => HIntegral (fun s => Hfn k s * logDeriv (completedLSym χ) s) (1 - c) c (-(R j)))
      atTop (𝓝 0) := by
  have hχ1 : χ ≠ 1 := ne_one_of_primitive hq hprim
  obtain ⟨CH, hCH0, hH⟩ := norm_Hfn_le hk hkc
  obtain ⟨κ, hκ1, hκdef⟩ := exists_parity' χ
  obtain ⟨Ca, hCa, harch⟩ := norm_logDeriv_archChi_le q κ hκ1
  have hq2 : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := by linarith
  set Lg : ℕ → ℝ := fun j => Real.log ((q:ℝ) * ((j : ℝ) + 10)) with hLgdef
  have hLg1 : ∀ j : ℕ, 1 ≤ Lg j := fun j => by
    rw [hLgdef, ← Real.log_exp 1]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    have := Real.exp_one_lt_d9
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have hLg_ge : ∀ j : ℕ, Real.log ((j:ℝ) + 10) ≤ Lg j := fun j => by
    show Real.log ((j:ℝ) + 10) ≤ Real.log ((q:ℝ) * ((j : ℝ) + 10))
    rw [Real.log_mul hq0.ne' (by positivity)]
    linarith [Real.log_nonneg (by linarith : (1:ℝ) ≤ q)]
  set K : ℝ := Ca + Cg with hKdef
  have hK0 : 0 < K := by positivity
  -- the arch factor is archChi q κ
  have harchfun : (fun z => (q : ℂ) ^ (z / 2) * DirichletCharacter.gammaFactor χ z) = archChi q κ := by
    funext z; rw [hκdef z]; rfl
  -- ‖Λ'/Λ_sym(s)‖ ≤ K log²(q(j+10)) on the good horizontals, re s ∈ [1/2, 3/2]
  have hright : ∀ (j : ℕ) (s : ℂ), (s.im = R j ∨ s.im = -R j) → 1/2 ≤ s.re → s.re ≤ 3/2 →
      ‖logDeriv (completedLSym χ) s‖ ≤ K * (Lg j) ^ 2 := by
    intro j s hsim hre1 hre2
    obtain ⟨hR1, hR2, hRs⟩ := hR j
    have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
    have hRj0 : 0 ≤ R j := by linarith
    obtain ⟨hL, hLL⟩ := hRs s hsim hre1 (by linarith)
    have hre0 : 0 < s.re := by linarith
    rw [logDeriv_completedLSym_split hq hχ1 hre0 hL, harchfun]
    have him8 : |s.im| ≤ (j : ℝ) + 8 := by
      rcases hsim with h | h
      · rw [h, abs_of_nonneg hRj0]; exact hR2
      · rw [h, abs_neg, abs_of_nonneg hRj0]; exact hR2
    have ha : ‖logDeriv (archChi q κ) s‖ ≤ Ca * Lg j := by
      have h := harch s.re s.im hre1 hre2
      rw [Complex.re_add_im] at h
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hCa.le)
      refine (Real.log_le_log (by positivity) (by linarith)).trans (hLg_ge j)
    have hLg2 : Lg j ≤ Lg j ^ 2 := by nlinarith [hLg1 j]
    calc ‖logDeriv χ.LFunction s + logDeriv (archChi q κ) s‖
        ≤ ‖logDeriv χ.LFunction s‖ + ‖logDeriv (archChi q κ) s‖ := norm_add_le _ _
      _ ≤ Cg * Lg j ^ 2 + Ca * Lg j ^ 2 := by
          have : Ca * Lg j ≤ Ca * Lg j ^ 2 := mul_le_mul_of_nonneg_left hLg2 hCa.le
          linarith
      _ = K * Lg j ^ 2 := by rw [hKdef]; ring
  -- the same bound on the whole horizontal segment x ∈ [1-c, c], by reflection for x < 1/2
  have hall : ∀ (j : ℕ) (x y : ℝ), (y = R j ∨ y = -R j) → 1 - c ≤ x → x ≤ c →
      ‖logDeriv (completedLSym χ) ((x : ℂ) + y * I)‖ ≤ K * (Lg j) ^ 2 := by
    intro j x y hy hx1 hx2
    rcases le_or_gt (1/2 : ℝ) x with hx | hx
    · exact hright j _ (by rcases hy with h | h <;> simp [h]) (by simpa using hx)
        (by simp; linarith)
    · -- reflect: s = 1 − conj s', s' := (1 − x) + y i (same imaginary part)
      set s' : ℂ := ((1 - x : ℝ) : ℂ) + y * I with hs'def
      have him' : s'.im = y := by simp [hs'def]
      have hre' : s'.re = 1 - x := by simp [hs'def]
      have e : ((x : ℂ) + y * I) = 1 - (starRingEnd ℂ) s' := by
        apply Complex.ext <;> simp [hs'def]
      rw [e, logDeriv_completedLSym_one_sub_conj hq hprim s', norm_neg, Complex.norm_conj]
      refine hright j s' ?_ (by rw [hre']; linarith) (by rw [hre']; linarith)
      rw [him']; exact hy
  -- integral bound along either horizontal
  have hint : ∀ (j : ℕ) (y : ℝ), (y = R j ∨ y = -R j) →
      ‖HIntegral (fun s => Hfn k s * logDeriv (completedLSym χ) s) (1 - c) c y‖
        ≤ CH / (1 + (R j) ^ 2) * (K * Lg j ^ 2) * |c - (1 - c)| := by
    intro j y hy
    unfold HIntegral
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hy2 : y ^ 2 = (R j) ^ 2 := by rcases hy with h | h <;> simp [h]
    dsimp only
    rw [norm_mul, ← hy2]
    exact mul_le_mul (hH x y (by linarith [hx.1]) (by linarith [hx.2]))
      (hall j x y hy hx.1.le hx.2) (norm_nonneg _) (by positivity)
  -- the majorant tends to 0
  set Lq : ℝ := Real.log q with hLq
  have hLq0 : 0 ≤ Lq := Real.log_nonneg (by linarith)
  set b : ℕ → ℝ := fun j => CH / (1 + (R j) ^ 2) * (K * Lg j ^ 2) * |c - (1 - c)| with hbdef
  have hLg_sq : ∀ j : ℕ, Lg j ^ 2 ≤ 2 * Lq ^ 2 + 8 * ((j : ℝ) + 10) := fun j => by
    have hy0 : (0 : ℝ) ≤ (j : ℝ) + 10 := by positivity
    have h := Real.log_le_rpow_div hy0 (by norm_num : (0:ℝ) < 1/2)
    have hsq : (((j : ℝ) + 10) ^ (1/2 : ℝ)) ^ 2 = (j : ℝ) + 10 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0]; norm_num
    have h0 : 0 ≤ Real.log ((j:ℝ) + 10) := Real.log_nonneg (by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)])
    have hl2 : Real.log ((j:ℝ) + 10) ^ 2 ≤ 4 * ((j : ℝ) + 10) := by
      calc Real.log ((j:ℝ) + 10) ^ 2 ≤ (((j : ℝ) + 10) ^ (1/2 : ℝ) / (1/2)) ^ 2 := pow_le_pow_left₀ h0 h 2
        _ = 4 * ((j : ℝ) + 10) := by rw [div_pow, hsq]; ring
    have hsplit : Lg j = Lq + Real.log ((j:ℝ) + 10) := by
      show Real.log ((q:ℝ) * ((j : ℝ) + 10)) = Real.log q + Real.log ((j:ℝ) + 10)
      exact Real.log_mul hq0.ne' (by positivity)
    rw [hsplit]
    nlinarith [sq_nonneg (Lq - Real.log ((j:ℝ) + 10))]
  have hb_le : ∀ j : ℕ, b j ≤ (CH * K * |c - (1 - c)| * (2 * Lq ^ 2 + 16)) / ((j : ℝ) + 7) := fun j => by
    obtain ⟨hR1, hR2, -⟩ := hR j
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h1 : Lg j ^ 2 / (1 + R j ^ 2) ≤ (2 * Lq ^ 2 + 16) / ((j : ℝ) + 7) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hR7 : ((j : ℝ) + 7) ^ 2 ≤ R j ^ 2 := pow_le_pow_left₀ (by positivity) hR1 2
      have hj7 : (j:ℝ) + 7 ≤ ((j : ℝ) + 7) ^ 2 := by nlinarith
      nlinarith [hLg_sq j, hR7, mul_le_mul_of_nonneg_right (hLg_sq j) (show (0:ℝ) ≤ (j:ℝ) + 7 by positivity),
        mul_nonneg hLq0 hLq0, sq_nonneg ((j:ℝ) + 7)]
    have e : b j = CH * K * |c - (1 - c)| * (Lg j ^ 2 / (1 + R j ^ 2)) := by
      rw [hbdef]; ring
    rw [e]
    calc CH * K * |c - (1 - c)| * (Lg j ^ 2 / (1 + R j ^ 2))
        ≤ CH * K * |c - (1 - c)| * ((2 * Lq ^ 2 + 16) / ((j : ℝ) + 7)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = CH * K * |c - (1 - c)| * (2 * Lq ^ 2 + 16) / ((j : ℝ) + 7) := by ring
  have hb0 : ∀ j, 0 ≤ b j := fun j => by rw [hbdef]; positivity
  have hb : Tendsto b atTop (𝓝 0) := by
    have hlim : Tendsto (fun j : ℕ => (CH * K * |c - (1 - c)| * (2 * Lq ^ 2 + 16)) / ((j : ℝ) + 7))
        atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    exact squeeze_zero hb0 hb_le hlim
  exact ⟨squeeze_zero_norm (fun j => hint j (R j) (Or.inl rfl)) hb,
    squeeze_zero_norm (fun j => hint j (-(R j)) (Or.inr rfl)) hb⟩

end ThmE
end Zeta23

end
