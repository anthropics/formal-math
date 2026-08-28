/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/Horizontal.lean — the horizontal sides of the explicit-formula rectangle vanish along
good heights (a sub-piece of `full_line_identity`).

For `s = x ± iR_j`, `x ∈ [1−c, c] ⊂ [−1/2, 3/2]`:  `‖H(s)‖ ≤ C_H/(1+R_j²)` (`norm_Hfn_le`), and
`‖Λ'/Λ(s)‖ ≤ K·log²(j+10)`: for `re s ≥ 1/2` split `Λ'/Λ = Γℝ'/Γℝ + ζ'/ζ` (`logDeriv_completedZeta`),
bound `ζ'/ζ` by the good-height hypothesis and `Γℝ'/Γℝ = −log π/2 + ψ(s/2)/2` by
`digamma_growth_strip`; for `re s < 1/2` reflect with `Λ'/Λ(s) = −Λ'/Λ(1−s)`
(`logDeriv_completedZeta_one_sub`), `1−s` lying on the opposite good horizontal.  Hence
`‖HIntegral‖ ≤ (2c−1)·C_H·K·log²(j+10)/(1+R_j²) → 0`.
-/
import Zeta23.WeilEF.FullLine

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Topology Filter Set MeasureTheory

/-- **Horizontal sides vanish** (interface for `full_line_identity`). -/
theorem horizontal_vanish {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) {Cg : ℝ} (hCg : 0 < Cg) {R : ℕ → ℝ}
    (hR : ∀ j : ℕ, (j : ℝ) + 7 ≤ R j ∧ R j ≤ (j : ℝ) + 8 ∧
      ∀ s : ℂ, (s.im = R j ∨ s.im = -R j) → 1/2 ≤ s.re → s.re ≤ 2 →
        riemannZeta s ≠ 0 ∧ ‖logDeriv riemannZeta s‖ ≤ Cg * (Real.log ((j : ℝ) + 10)) ^ 2) :
    Tendsto (fun j : ℕ => HIntegral (fun s => Hfn k s * logDeriv completedRiemannZeta s)
        (1 - c) c (R j)) atTop (𝓝 0)
    ∧ Tendsto (fun j : ℕ => HIntegral (fun s => Hfn k s * logDeriv completedRiemannZeta s)
        (1 - c) c (-(R j))) atTop (𝓝 0) := by
  obtain ⟨CH, hCH0, hH⟩ := norm_Hfn_le hk hkc
  obtain ⟨Cψ, hCψ, hψ⟩ := digamma_growth_strip
  set Lg : ℕ → ℝ := fun j => Real.log ((j : ℝ) + 10) with hLgdef
  have hLg1 : ∀ j : ℕ, 1 ≤ Lg j := fun j => by
    rw [hLgdef, ← Real.log_exp 1]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    have := Real.exp_one_lt_d9
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hlogπ : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  set K : ℝ := Real.log Real.pi / 2 + Cψ + Cg with hKdef
  have hK0 : 0 < K := by positivity
  -- ‖Λ'/Λ(s)‖ ≤ K log²(j+10) on the good horizontals, re s ∈ [1/2, 2]
  have hright : ∀ (j : ℕ) (s : ℂ), (s.im = R j ∨ s.im = -R j) → 1/2 ≤ s.re → s.re ≤ 2 →
      ‖logDeriv completedRiemannZeta s‖ ≤ K * (Lg j) ^ 2 := by
    intro j s hsim hre1 hre2
    obtain ⟨hR1, hR2, hRs⟩ := hR j
    have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
    have hRj0 : 0 ≤ R j := by linarith
    have him7 : 7 ≤ |s.im| := by
      rcases hsim with h | h
      · rw [h, abs_of_nonneg hRj0]; linarith
      · rw [h, abs_neg, abs_of_nonneg hRj0]; linarith
    have hs0 : s ≠ 0 := fun h => by rw [h] at him7; norm_num at him7
    have hs1 : s ≠ 1 := fun h => by rw [h] at him7; norm_num at him7
    obtain ⟨hζ, hLζ⟩ := hRs s hsim hre1 hre2
    have hre0 : 0 < s.re := by linarith
    rw [logDeriv_completedZeta s hs1 hζ hre0, logDeriv_Gammaℝ hre0]
    have hψs : ‖Complex.digamma (s / 2)‖ ≤ Cψ * Real.log (2 + |(s / 2).im|) :=
      hψ (s / 2) (by simp; linarith) (by simp; linarith)
    have hlog2 : Real.log (2 + |(s / 2).im|) ≤ Lg j := by
      have him8 : |s.im| ≤ (j : ℝ) + 8 := by
        rcases hsim with h | h
        · rw [h, abs_of_nonneg hRj0]; exact hR2
        · rw [h, abs_neg, abs_of_nonneg hRj0]; exact hR2
      have e : |(s / 2).im| = |s.im| / 2 := by simp [abs_div]
      rw [e, hLgdef]
      exact Real.log_le_log (by positivity) (by linarith)
    have hLg2 : Lg j ≤ Lg j ^ 2 := by nlinarith [hLg1 j]
    calc ‖-((Real.log Real.pi : ℝ) : ℂ) / 2 + 1 / 2 * Complex.digamma (s / 2) + logDeriv riemannZeta s‖
        ≤ ‖-((Real.log Real.pi : ℝ) : ℂ) / 2‖ + ‖(1 / 2 : ℂ) * Complex.digamma (s / 2)‖
          + ‖logDeriv riemannZeta s‖ := norm_add₃_le
      _ = Real.log Real.pi / 2 + 1 / 2 * ‖Complex.digamma (s / 2)‖ + ‖logDeriv riemannZeta s‖ := by
          rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogπ, norm_mul]
          norm_num
      _ ≤ Real.log Real.pi / 2 * Lg j ^ 2 + Cψ * Lg j ^ 2 + Cg * Lg j ^ 2 := by
          have h1 : Real.log Real.pi / 2 ≤ Real.log Real.pi / 2 * Lg j ^ 2 := by
            have : (1:ℝ) ≤ Lg j ^ 2 := by nlinarith [hLg1 j]
            nlinarith
          have h2 : 1 / 2 * ‖Complex.digamma (s / 2)‖ ≤ Cψ * Lg j ^ 2 := by
            have := hψs.trans (mul_le_mul_of_nonneg_left (hlog2.trans hLg2) hCψ.le)
            nlinarith [norm_nonneg (Complex.digamma (s / 2))]
          linarith
      _ = K * Lg j ^ 2 := by rw [hKdef]; ring
  -- the same bound on the whole horizontal segment x ∈ [1-c, c], by reflection for x < 1/2
  have hall : ∀ (j : ℕ) (x y : ℝ), (y = R j ∨ y = -R j) → 1 - c ≤ x → x ≤ c →
      ‖logDeriv completedRiemannZeta ((x : ℂ) + y * I)‖ ≤ K * (Lg j) ^ 2 := by
    intro j x y hy hx1 hx2
    rcases le_or_gt (1/2 : ℝ) x with hx | hx
    · exact hright j _ (by rcases hy with h | h <;> simp [h]) (by simpa using hx)
        (by simp; linarith)
    · -- reflect: s = 1 − s', s' := (1 − x) − y i on the opposite good horizontal
      set s' : ℂ := ((1 - x : ℝ) : ℂ) + (-y) * I with hs'def
      have him' : s'.im = -y := by simp [hs'def]
      have hre' : s'.re = 1 - x := by simp [hs'def]
      have hy0 : y ≠ 0 := by
        obtain ⟨hR1, -, -⟩ := hR j
        have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
        have hRpos : 0 < R j := by linarith
        rcases hy with h | h
        · rw [h]; exact hRpos.ne'
        · rw [h]; exact (neg_lt_zero.mpr hRpos).ne
      have hs'0 : s' ≠ 0 := fun h => hy0 (by
        have him0 := congrArg Complex.im h
        rw [him'] at him0; simpa using him0)
      have hs'1 : s' ≠ 1 := fun h => hy0 (by
        have him1 := congrArg Complex.im h
        rw [him'] at him1; simpa using him1)
      have e : ((x : ℂ) + y * I) = 1 - s' := by
        simp only [hs'def]; push_cast; ring
      rw [e, logDeriv_completedZeta_one_sub s' hs'0 hs'1, norm_neg]
      refine hright j s' ?_ (by rw [hre']; linarith) (by rw [hre']; linarith)
      rw [him']
      rcases hy with h | h
      · right; rw [h]
      · left; rw [h, neg_neg]
  -- integral bound along either horizontal
  have hint : ∀ (j : ℕ) (y : ℝ), (y = R j ∨ y = -R j) →
      ‖HIntegral (fun s => Hfn k s * logDeriv completedRiemannZeta s) (1 - c) c y‖
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
  set b : ℕ → ℝ := fun j => CH / (1 + (R j) ^ 2) * (K * Lg j ^ 2) * |c - (1 - c)| with hbdef
  have hLg_sq : ∀ j : ℕ, Lg j ^ 2 ≤ 4 * ((j : ℝ) + 10) := fun j => by
    have hy0 : (0 : ℝ) ≤ (j : ℝ) + 10 := by positivity
    have h := Real.log_le_rpow_div hy0 (by norm_num : (0:ℝ) < 1/2)
    have hsq : (((j : ℝ) + 10) ^ (1/2 : ℝ)) ^ 2 = (j : ℝ) + 10 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0]; norm_num
    have h0 : 0 ≤ Lg j := (zero_le_one.trans (hLg1 j))
    calc Lg j ^ 2 ≤ (((j : ℝ) + 10) ^ (1/2 : ℝ) / (1/2)) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = 4 * ((j : ℝ) + 10) := by rw [div_pow, hsq]; ring
  have hb_le : ∀ j : ℕ, b j ≤ (8 * CH * K * |c - (1 - c)|) / ((j : ℝ) + 7) := fun j => by
    obtain ⟨hR1, hR2, -⟩ := hR j
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h1 : Lg j ^ 2 / (1 + R j ^ 2) ≤ 8 / ((j : ℝ) + 7) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hR7 : ((j : ℝ) + 7) ^ 2 ≤ R j ^ 2 := pow_le_pow_left₀ (by positivity) hR1 2
      nlinarith [hLg_sq j, hR7, mul_le_mul_of_nonneg_right (hLg_sq j) (show (0:ℝ) ≤ (j:ℝ) + 7 by positivity),
        sq_nonneg ((j:ℝ) + 7)]
    have e : b j = CH * K * |c - (1 - c)| * (Lg j ^ 2 / (1 + R j ^ 2)) := by
      rw [hbdef]; ring
    rw [e]
    calc CH * K * |c - (1 - c)| * (Lg j ^ 2 / (1 + R j ^ 2))
        ≤ CH * K * |c - (1 - c)| * (8 / ((j : ℝ) + 7)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 8 * CH * K * |c - (1 - c)| / ((j : ℝ) + 7) := by ring
  have hb0 : ∀ j, 0 ≤ b j := fun j => by rw [hbdef]; positivity
  have hb : Tendsto b atTop (𝓝 0) := by
    have hlim : Tendsto (fun j : ℕ => (8 * CH * K * |c - (1 - c)|) / ((j : ℝ) + 7)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    exact squeeze_zero hb0 hb_le hlim
  exact ⟨squeeze_zero_norm (fun j => hint j (R j) (Or.inl rfl)) hb,
    squeeze_zero_norm (fun j => hint j (-(R j)) (Or.inr rfl)) hb⟩

end WeilEF
end Zeta23

end
