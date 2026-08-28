/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ExplicitFormula/FullLine.lean — (EF1) the R → ∞ limit, GENERIC in the function f.

For an ENTIRE f with: logDeriv f (1−s) = −logDeriv f s; all zeros in 1−c < Re s < c; good heights
R_j ∈ [j+j₀, j+j₀+1] with f ≠ 0 and ‖f′/f‖ ≤ C log²(j+j₀+3) on Im s = ±R_j, 1−c ≤ Re ≤ c; and a line
bound ‖f′/f(c+it)‖ ≤ M log(2+|t|), the rectangle identity (Contour.lean) passes to the limit:
    (1/2π) ∫ [H(c+it) + H(1−c−it)] · f′/f(c+it) dt = Σ'_ρ ord_ρ(f) · H(ρ)      (H = WeilEF.Hfn k),
the horizontal sides vanishing (‖H‖ ≤ C_H/(1+R²) on −1 ≤ Re ≤ 2, WeilEF.norm_Hfn_le), the left vertical
folding onto the right one by the symmetry, and the finite zero sums exhausting the (assumed absolutely
convergent) tsum.  Pattern: Zeta23/WeilEF/{FullLine,Horizontal,ZeroSumLimit,FullLineAssembly}.lean.
Instances (§ Instances): f = s(s−1) → rational_line;  f = ξ′ → (EF1) full_line_identity.
-/
import Zeta23.XiPrime.ExplicitFormula.Contour
import Zeta23.XiPrime.ZeroCount.GoodHeights
import Zeta23.XiPrime.ExplicitFormula.LineBound
import Zeta23.WeilEF.ZeroSummabilityGen

noncomputable section

namespace Zeta23
namespace XiPrime

open Complex Topology Filter Set MeasureTheory
open Zeta23.WeilEF (Hfn norm_Hfn_le continuous_Hfn_line one_sub_cast log_two_add_le)

/-! ## Generic majorants -/

section Generic

variable {f : ℂ → ℂ} {k : ℝ → ℂ} {c : ℝ}

/-- the full-line integrand  F_f(t) := [H(c+it) + H(1−c−it)] · f′/f(c+it). -/
def Fline (f : ℂ → ℂ) (k : ℝ → ℂ) (c : ℝ) (t : ℝ) : ℂ :=
  (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I)) * logDeriv f ((c : ℂ) + t * I)

/-- the two-sided weight t ↦ H(c+it) + H(1−c−it) is continuous. -/
theorem continuous_weight (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (c : ℝ) :
    Continuous (fun t : ℝ => Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I)) := by
  refine (continuous_Hfn_line hk hkc c).add ?_
  have h := continuous_Hfn_line hk hkc (1 - c)
  have : (fun t : ℝ => Hfn k (1 - c - t * I))
      = (fun t : ℝ => Hfn k (((1 - c : ℝ) : ℂ) + t * I)) ∘ fun t : ℝ => -t := by
    funext t; simp only [Function.comp_apply, one_sub_cast]
  rw [this]; exact h.comp continuous_neg

/-- the two-sided weight decays like 1/(1+t²) when −1 ≤ 1−c and c ≤ 2. -/
theorem norm_weight_le (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (hc0 : -1 ≤ c) (hc2 : c ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hk hkc
  refine ⟨2 * C, by positivity, fun t => ?_⟩
  have h1 := hC c t hc0 hc2
  have h2 := hC (1 - c) (-t) (by linarith) (by linarith)
  rw [← one_sub_cast, neg_sq] at h2
  calc ‖Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I)‖
      ≤ ‖Hfn k ((c : ℂ) + t * I)‖ + ‖Hfn k (1 - c - t * I)‖ := norm_add_le _ _
    _ ≤ C / (1 + t ^ 2) + C / (1 + t ^ 2) := add_le_add h1 h2
    _ = (2 * C) / (1 + t ^ 2) := by ring

/-- f′/f is continuous along a vertical line on which f (entire) does not vanish. -/
theorem continuous_logDeriv_line (hf : Differentiable ℂ f) (σ : ℝ)
    (hne : ∀ t : ℝ, f ((σ : ℂ) + t * I) ≠ 0) :
    Continuous (fun t : ℝ => logDeriv f ((σ : ℂ) + t * I)) := by
  have hline : Continuous (fun t : ℝ => ((σ : ℂ) + t * I)) := by fun_prop
  have hd : Differentiable ℂ (deriv f) := fun z => ((hf.analyticAt z).deriv).differentiableAt
  have h1 : Continuous (fun t : ℝ => deriv f ((σ : ℂ) + t * I)) := hd.continuous.comp hline
  have h2 : Continuous (fun t : ℝ => f ((σ : ℂ) + t * I)) := hf.continuous.comp hline
  simp_rw [logDeriv_apply]
  exact h1.div h2 hne

/-- generic: (continuous, ≤ C/(1+t²)) × (continuous, ≤ M log(2+|t|)) is integrable on ℝ. -/
theorem integrable_decay_mul_log {φ ψ : ℝ → ℂ} (hφc : Continuous φ) (hψc : Continuous ψ)
    {C : ℝ} (hC0 : 0 ≤ C) (hφ : ∀ t, ‖φ t‖ ≤ C / (1 + t ^ 2))
    {M : ℝ} (hM0 : 0 ≤ M) (hψ : ∀ t, ‖ψ t‖ ≤ M * Real.log (2 + |t|)) :
    Integrable (fun t => φ t * ψ t) := by
  set K : ℝ := C * (5 * M) with hK
  have hmaj : Integrable (fun t : ℝ => K * ((1 : ℝ) + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2)) :=
    (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (by rw [Module.finrank_self]; norm_num)).const_mul K
  refine Integrable.mono' hmaj (hφc.mul hψc).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  have hq : 0 < (1 + t ^ 2 : ℝ) := by positivity
  have hlog : Real.log (2 + |t|) ≤ 5 * (1 + t ^ 2) ^ (1 / 4 : ℝ) := by
    have := log_two_add_le (abs_nonneg t); rwa [sq_abs] at this
  have e : (1 + t ^ 2 : ℝ) ^ (-(3 / 2 : ℝ) / 2) = (1 + t ^ 2) ^ (1 / 4 : ℝ) / (1 + t ^ 2) := by
    rw [show (-(3 / 2 : ℝ) / 2) = (1 / 4 : ℝ) - 1 by norm_num, Real.rpow_sub hq, Real.rpow_one]
  rw [norm_mul, Real.norm_eq_abs, sq_abs, e]
  calc ‖φ t‖ * ‖ψ t‖ ≤ (C / (1 + t ^ 2)) * (M * (5 * (1 + t ^ 2) ^ (1 / 4 : ℝ))) :=
        mul_le_mul (hφ t) ((hψ t).trans (mul_le_mul_of_nonneg_left hlog hM0)) (norm_nonneg _)
          (by positivity)
    _ = K * ((1 + t ^ 2) ^ (1 / 4 : ℝ) / (1 + t ^ 2)) := by rw [hK]; ring

/-- points of the line Re s = c are not zeros of f. -/
theorem ne_zero_on_line {Zset : Set ℂ} (hZ : ∀ s, f s = 0 ↔ s ∈ Zset)
    (hstrip : ∀ ρ ∈ Zset, 1 - c < ρ.re ∧ ρ.re < c) (t : ℝ) : f ((c : ℂ) + t * I) ≠ 0 := by
  intro h0
  have h := (hstrip _ ((hZ _).mp h0)).2
  simp at h

/-- **Integrability of the full-line integrand** from the line bound. -/
theorem integrable_Fline_of (hf : Differentiable ℂ f) (hne : ∀ t : ℝ, f ((c : ℂ) + t * I) ≠ 0)
    (hline : ∃ M : ℝ, ∀ t : ℝ, ‖logDeriv f ((c : ℂ) + t * I)‖ ≤ M * Real.log (2 + |t|))
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (hc0 : -1 ≤ c) (hc2 : c ≤ 2) :
    Integrable (Fline f k c) := by
  obtain ⟨C, hC0, hC⟩ := norm_weight_le hk hkc hc0 hc2
  obtain ⟨M, hM⟩ := hline
  have hM' : ∀ t : ℝ, ‖logDeriv f ((c : ℂ) + t * I)‖ ≤ max M 0 * Real.log (2 + |t|) := fun t =>
    (hM t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.log_nonneg (by linarith [abs_nonneg t])))
  exact integrable_decay_mul_log (continuous_weight hk hkc c) (continuous_logDeriv_line hf c hne)
    hC0 hC (le_max_right _ _) hM'

/-- the truncated integrals of an integrable F converge to ∫ F along any R_j ≥ j. -/
theorem tendsto_intervalIntegral_of_integrable {F : ℝ → ℂ} (hF : Integrable F) {R : ℕ → ℝ}
    (hR : ∀ j : ℕ, (j : ℝ) ≤ R j) :
    Tendsto (fun j : ℕ => ∫ t in (-R j)..R j, F t) atTop (𝓝 (∫ t, F t)) := by
  have hRtop : Tendsto R atTop atTop := tendsto_atTop_mono hR tendsto_natCast_atTop_atTop
  exact intervalIntegral_tendsto_integral hF (tendsto_neg_atTop_atBot.comp hRtop) hRtop

/-! ## The vertical sides -/

/-- Folding the left vertical side onto the right one by  f′/f(1−s) = −f′/f(s):
V(c; −R, R) − V(1−c; −R, R) = I • ∫_{−R}^{R} F_f. -/
theorem verticals_eq_of (hf : Differentiable ℂ f) (hne : ∀ t : ℝ, f ((c : ℂ) + t * I) ≠ 0)
    (hsymm : ∀ s, logDeriv f (1 - s) = -logDeriv f s)
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (R : ℝ) :
    VIntegral (fun s => Hfn k s * logDeriv f s) c (-R) R
      - VIntegral (fun s => Hfn k s * logDeriv f s) (1 - c) (-R) R
      = I • ∫ t in (-R)..R, Fline f k c t := by
  set L := logDeriv f with hL
  have hLc : Continuous (fun t : ℝ => L ((c : ℂ) + t * I)) := continuous_logDeriv_line hf c hne
  have hHc := continuous_Hfn_line hk hkc c
  have hH2 : Continuous (fun t : ℝ => Hfn k (1 - c - t * I)) := by
    have h := continuous_Hfn_line hk hkc (1 - c)
    have : (fun t : ℝ => Hfn k (1 - c - t * I))
        = (fun t : ℝ => Hfn k (((1 - c : ℝ) : ℂ) + t * I)) ∘ fun t : ℝ => -t := by
      funext t; simp only [Function.comp_apply, one_sub_cast]
    rw [this]; exact h.comp continuous_neg
  have hleft : ∀ y : ℝ, Hfn k (((1 - c : ℝ) : ℂ) + y * I) * L (((1 - c : ℝ) : ℂ) + y * I)
      = -(Hfn k (1 - c - ((-y : ℝ) : ℂ) * I) * L ((c : ℂ) + ((-y : ℝ) : ℂ) * I)) := by
    intro y
    have hs : ((1 - c : ℝ) : ℂ) + y * I = 1 - ((c : ℂ) + ((-y : ℝ) : ℂ) * I) := by push_cast; ring
    rw [hs, hsymm]
    have : (1:ℂ) - ((c : ℂ) + ((-y:ℝ):ℂ) * I) = 1 - c - ((-y : ℝ) : ℂ) * I := by ring
    rw [this]; ring
  have hI1 : IntervalIntegrable (fun t : ℝ => Hfn k ((c : ℂ) + t * I) * L ((c : ℂ) + t * I))
      volume (-R) R := (hHc.mul hLc).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun t : ℝ => Hfn k (1 - c - t * I) * L ((c : ℂ) + t * I))
      volume (-R) R := (hH2.mul hLc).intervalIntegrable _ _
  have hfold : (∫ y in (-R)..R, Hfn k (((1 - c : ℝ) : ℂ) + y * I) * L (((1 - c : ℝ) : ℂ) + y * I))
      = -∫ t in (-R)..R, Hfn k (1 - c - t * I) * L ((c : ℂ) + t * I) := by
    simp_rw [hleft]
    rw [intervalIntegral.integral_neg]
    have h := intervalIntegral.integral_comp_neg (a := -R) (b := R)
      (fun t : ℝ => Hfn k (1 - c - t * I) * L ((c : ℂ) + t * I))
    simp only [neg_neg] at h
    rw [← h]
  dsimp only [VIntegral]
  rw [hfold, ← smul_sub, sub_neg_eq_add, ← intervalIntegral.integral_add hI1 hI2]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [Fline]
  ring

/-! ## Good heights, re-indexed -/

/-- from "∀ j ≥ j₀ ∃ R ∈ [j, j+1] …" to a height SEQUENCE R_j ∈ [j+j₀, j+j₀+1], j₀ ≥ 1, with the
log²-bound written in terms of j. -/
theorem exists_heights_of {a b : ℝ}
    (hGH : ∃ C : ℝ, 0 < C ∧ ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R : ℝ, (j : ℝ) ≤ R ∧ R ≤ (j : ℝ) + 1 ∧
      ∀ s : ℂ, (s.im = R ∨ s.im = -R) → a ≤ s.re → s.re ≤ b →
        f s ≠ 0 ∧ ‖logDeriv f s‖ ≤ C * (Real.log ((j : ℝ) + 3)) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ j₀ : ℕ, 1 ≤ j₀ ∧ ∃ R : ℕ → ℝ, ∀ j : ℕ,
      (j : ℝ) + j₀ ≤ R j ∧ R j ≤ (j : ℝ) + j₀ + 1 ∧
      ∀ s : ℂ, (s.im = R j ∨ s.im = -R j) → a ≤ s.re → s.re ≤ b →
        f s ≠ 0 ∧ ‖logDeriv f s‖ ≤ C * (Real.log ((j : ℝ) + j₀ + 3)) ^ 2 := by
  obtain ⟨C, hC, j₀, h⟩ := hGH
  have hex : ∀ j : ℕ, ∃ R : ℝ, ((j + (j₀ + 1) : ℕ) : ℝ) ≤ R ∧ R ≤ ((j + (j₀ + 1) : ℕ) : ℝ) + 1 ∧
      ∀ s : ℂ, (s.im = R ∨ s.im = -R) → a ≤ s.re → s.re ≤ b →
        f s ≠ 0 ∧ ‖logDeriv f s‖ ≤ C * (Real.log (((j + (j₀ + 1) : ℕ) : ℝ) + 3)) ^ 2 :=
    fun j => h (j + (j₀ + 1)) (by omega)
  refine ⟨C, hC, j₀ + 1, by omega, fun j => (hex j).choose, fun j => ?_⟩
  obtain ⟨hs1, hs2, hs3⟩ := (hex j).choose_spec
  have e : ((j + (j₀ + 1) : ℕ) : ℝ) = (j : ℝ) + ((j₀ + 1 : ℕ) : ℝ) := by push_cast; ring
  refine ⟨by rw [← e]; exact hs1, by rw [← e]; exact hs2, fun s him h1 h2 => ?_⟩
  rw [← e]
  exact hs3 s him h1 h2

/-! ## The horizontal sides -/

/-- **Horizontal sides vanish**: ‖H‖ ≤ C_H/(1+R_j²) on the segment and ‖f′/f‖ ≤ K log²(j+j₀+3) there,
R_j ≥ j + j₀ ≥ 1, so  ‖HIntegral‖ ≤ (2c−1)·C_H·K·log²/(1+R_j²) → 0. -/
theorem horizontal_vanish_of (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hc : 1 - c ≤ c) (hc2 : c ≤ 2) {K : ℝ} (hK : 0 ≤ K) {j₀ : ℕ} (hj₀ : 1 ≤ j₀) {R : ℕ → ℝ}
    (hR : ∀ j : ℕ, (j : ℝ) + j₀ ≤ R j ∧
      ∀ s : ℂ, (s.im = R j ∨ s.im = -R j) → 1 - c ≤ s.re → s.re ≤ c →
        ‖logDeriv f s‖ ≤ K * (Real.log ((j : ℝ) + j₀ + 3)) ^ 2) :
    Tendsto (fun j : ℕ => HIntegral (fun s => Hfn k s * logDeriv f s) (1 - c) c (R j))
        atTop (𝓝 0)
    ∧ Tendsto (fun j : ℕ => HIntegral (fun s => Hfn k s * logDeriv f s) (1 - c) c (-(R j)))
        atTop (𝓝 0) := by
  obtain ⟨CH, hCH0, hH⟩ := norm_Hfn_le hk hkc
  set n : ℕ → ℝ := fun j => (j : ℝ) + j₀ with hndef
  have hn1 : ∀ j, 1 ≤ n j := fun j => by
    have : (1 : ℝ) ≤ (j₀ : ℝ) := by exact_mod_cast hj₀
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    simp only [hndef]; linarith
  set Lg : ℕ → ℝ := fun j => Real.log (n j + 3) with hLgdef
  have hLg_eq : ∀ j : ℕ, Real.log ((j : ℝ) + j₀ + 3) = Lg j := fun j => by simp only [hLgdef, hndef]
  -- integral bound along either horizontal
  have hint : ∀ (j : ℕ) (y : ℝ), (y = R j ∨ y = -R j) →
      ‖HIntegral (fun s => Hfn k s * logDeriv f s) (1 - c) c y‖
        ≤ CH / (1 + (R j) ^ 2) * (K * Lg j ^ 2) * |c - (1 - c)| := by
    intro j y hy
    unfold HIntegral
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [Set.uIoc_of_le hc] at hx
    have hy2 : y ^ 2 = (R j) ^ 2 := by rcases hy with h | h <;> simp [h]
    dsimp only
    rw [norm_mul, ← hy2]
    refine mul_le_mul (hH x y (by linarith [hx.1]) (by linarith [hx.2])) ?_ (norm_nonneg _)
      (by positivity)
    rw [← hLg_eq]
    have hxre : ((x : ℂ) + y * I).re = x := by simp
    exact (hR j).2 ((x : ℂ) + y * I) (by rcases hy with h | h <;> simp [h]) (by rw [hxre]; exact hx.1.le)
      (by rw [hxre]; exact hx.2)
  -- the majorant tends to 0
  set b : ℕ → ℝ := fun j => CH / (1 + (R j) ^ 2) * (K * Lg j ^ 2) * |c - (1 - c)| with hbdef
  have hb0 : ∀ j, 0 ≤ b j := fun j => by rw [hbdef]; positivity
  have hb_le : ∀ j : ℕ, b j ≤ (CH * K * |c - (1 - c)|) * (Lg j ^ 2 / (1 * (n j + 3) + (-3))) := by
    intro j
    have hnR : n j ≤ R j := (hR j).1
    have hn0 : 0 < n j := by linarith [hn1 j]
    have hden : n j ≤ 1 + R j ^ 2 := by nlinarith [hnR, hn1 j]
    have e1 : (1 : ℝ) * (n j + 3) + (-3) = n j := by ring
    rw [e1]
    have h1 : Lg j ^ 2 / (1 + R j ^ 2) ≤ Lg j ^ 2 / n j :=
      div_le_div_of_nonneg_left (sq_nonneg _) hn0 hden
    have e : b j = CH * K * |c - (1 - c)| * (Lg j ^ 2 / (1 + R j ^ 2)) := by rw [hbdef]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hntop : Tendsto (fun j : ℕ => n j + 3) atTop atTop := by
    simp only [hndef]
    exact tendsto_atTop_add_const_right _ _
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hlim0 : Tendsto (fun j : ℕ => Lg j ^ 2 / (1 * (n j + 3) + (-3))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-3) 2 one_ne_zero).comp hntop
    exact h
  have hb : Tendsto b atTop (𝓝 0) := by
    have hlim := hlim0.const_mul (CH * K * |c - (1 - c)|)
    rw [mul_zero] at hlim
    exact squeeze_zero hb0 hb_le hlim
  exact ⟨squeeze_zero_norm (fun j => hint j (R j) (Or.inl rfl)) hb,
    squeeze_zero_norm (fun j => hint j (-(R j)) (Or.inr rfl)) hb⟩

/-! ## The zero side -/

/-- **Zero-sum limit**: finite sums over the windows {|Im ρ| < R_j} ∩ Zset (R increasing to ∞)
converge to the tsum of an absolutely convergent g over Zset. -/
theorem zero_sum_limit_of {Zset : Set ℂ} (g : ℂ → ℂ) (hsum : Summable (fun ρ : Zset => g ρ))
    {R : ℕ → ℝ} (hRmono : Monotone R) (hRge : ∀ j : ℕ, (j : ℝ) ≤ R j)
    {Z : ℕ → Finset ℂ}
    (hZ : ∀ j : ℕ, ((Z j : Set ℂ) = {ρ : ℂ | ρ ∈ Zset ∧ -R j < ρ.im ∧ ρ.im < R j})) :
    Tendsto (fun j : ℕ => ∑ ρ ∈ Z j, g ρ) atTop (𝓝 (∑' ρ : Zset, g ρ)) := by
  classical
  set G : Zset → ℂ := fun ρ => g ρ with hG
  have hmemZ : ∀ j ρ, ρ ∈ Z j ↔ ρ ∈ Zset ∧ -R j < ρ.im ∧ ρ.im < R j := by
    intro j ρ
    rw [← Finset.mem_coe, hZ j]
    rfl
  set s : ℕ → Finset Zset := fun j => (Z j).subtype (· ∈ Zset) with hsdef
  have hsum_eq : ∀ j, ∑ x ∈ s j, G x = ∑ ρ ∈ Z j, g ρ := by
    intro j
    have h1 := Finset.sum_subtype_eq_sum_filter (s := Z j) (p := (· ∈ Zset)) g
    have h2 : (Z j).filter (· ∈ Zset) = Z j := by
      apply Finset.filter_true_of_mem
      intro ρ hρ
      exact ((hmemZ j ρ).mp hρ).1
    rw [h2] at h1
    rw [← h1]
  have hmono : Monotone s := by
    intro i j hij x hx
    rw [Finset.mem_subtype, hmemZ] at hx ⊢
    obtain ⟨h1, h2, h3⟩ := hx
    have := hRmono hij
    exact ⟨h1, by linarith, by linarith⟩
  have hexh : ∀ B : Finset Zset, ∃ j, B ≤ s j := by
    intro B
    set M : ℝ := ∑ x ∈ B, |((x : ℂ)).im| with hM
    have hMle : ∀ x ∈ B, |((x : ℂ)).im| ≤ M := fun x hx =>
      Finset.single_le_sum (f := fun x : Zset => |((x : ℂ)).im|) (fun _ _ => abs_nonneg _) hx
    obtain ⟨j, hj⟩ := exists_nat_gt M
    refine ⟨j, fun x hx => ?_⟩
    rw [Finset.mem_subtype, hmemZ]
    have habs := abs_le.mp (hMle x hx)
    have hRj := hRge j
    exact ⟨x.2, by linarith [habs.1], by linarith [habs.2]⟩
  have hs_tend : Tendsto s atTop atTop := tendsto_atTop_atTop_of_monotone hmono hexh
  have hT : Tendsto (fun S : Finset Zset => ∑ x ∈ S, G x) atTop (𝓝 (∑' x, G x)) := by
    have hHas := hsum.hasSum
    simpa [HasSum] using hHas
  have := hT.comp hs_tend
  refine this.congr (fun j => ?_)
  simp only [Function.comp_apply, hsum_eq]

/-! ## Assembly -/

/-- **Generic full-line identity.**  f entire, logDeriv f (1−s) = −logDeriv f s, all zeros of f
(the set Zset) in the open strip 1−c < Re < c (1/2 < c ≤ 2), good heights with a log² bound for f′/f on
the horizontal segments, a log bound for f′/f on Re s = c, and absolute convergence of the zero sum.
Then  (1/2π) ∫ [H(c+it) + H(1−c−it)]·f′/f(c+it) dt = Σ'_{ρ ∈ Zset} ord_ρ(f)·H(ρ). -/
theorem full_line_identity_of (hf : Differentiable ℂ f) (hc : 1 / 2 < c) (hc2 : c ≤ 2)
    (hsymm : ∀ s, logDeriv f (1 - s) = -logDeriv f s)
    {Zset : Set ℂ} (hZ : ∀ s, f s = 0 ↔ s ∈ Zset) (hstrip : ∀ ρ ∈ Zset, 1 - c < ρ.re ∧ ρ.re < c)
    (hGH : ∃ C : ℝ, 0 < C ∧ ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R : ℝ, (j : ℝ) ≤ R ∧ R ≤ (j : ℝ) + 1 ∧
      ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 - c ≤ s.re → s.re ≤ c →
        f s ≠ 0 ∧ ‖logDeriv f s‖ ≤ C * (Real.log ((j : ℝ) + 3)) ^ 2)
    (hline : ∃ M : ℝ, ∀ t : ℝ, ‖logDeriv f ((c : ℂ) + t * I)‖ ≤ M * Real.log (2 + |t|))
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hsum : Summable (fun ρ : Zset => (analyticOrderNatAt f ρ : ℂ) * Hfn k ρ)) :
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I))
        * logDeriv f ((c : ℂ) + t * I))
      = ∑' ρ : Zset, (analyticOrderNatAt f ρ : ℂ) * Hfn k ρ := by
  have hcc : 1 - c < c := by linarith
  have hne : ∀ t : ℝ, f ((c : ℂ) + t * I) ≠ 0 := ne_zero_on_line hZ hstrip
  obtain ⟨Cg, hCg, j₀, hj₀, R, hR⟩ := exists_heights_of hGH
  have hRge : ∀ j : ℕ, (j : ℝ) ≤ R j := fun j => by
    have := (hR j).1; have : (0:ℝ) ≤ j₀ := Nat.cast_nonneg j₀; linarith
  have hR0 : ∀ j : ℕ, 0 ≤ R j := fun j => (Nat.cast_nonneg j).trans (hRge j)
  have hRmono : Monotone R := by
    intro i j hij
    rcases hij.eq_or_lt with h | h
    · rw [h]
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      linarith [(hR i).2.1, (hR j).1]
  set F : ℂ → ℂ := fun s => Hfn k s * logDeriv f s with hF
  -- the rectangle identity at every height R_j
  have hrect : ∀ j : ℕ, ∃ Z : Finset ℂ,
      ((Z : Set ℂ) = {ρ : ℂ | ρ ∈ Zset ∧ -R j < ρ.im ∧ ρ.im < R j}) ∧
      RectangleIntegral' F (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I)
        = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * Hfn k ρ := fun j =>
    rectangle_identity_of hf (differentiable_Hfn hk hkc) hcc hZ hstrip (hR0 j)
      (fun s him h1 h2 => ((hR j).2.2 s him h1 h2).1)
  choose Z hZc hE using hrect
  -- the three limits
  obtain ⟨hHtop, hHbot⟩ := horizontal_vanish_of (f := f) hk hkc hcc.le hc2 hCg.le hj₀ (R := R)
    (fun j => ⟨(hR j).1, fun s him h1 h2 => ((hR j).2.2 s him h1 h2).2⟩)
  have hZlim := zero_sum_limit_of (fun ρ => (analyticOrderNatAt f ρ : ℂ) * Hfn k ρ) hsum
    hRmono hRge hZc
  have hV := tendsto_intervalIntegral_of_integrable
    (integrable_Fline_of hf hne hline hk hkc (by linarith) hc2) hRge
  -- decomposition of the normalized rectangle integral
  have hdec : ∀ j : ℕ, RectangleIntegral' F (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I)
      = (1 / (2 * Real.pi * I) : ℂ) * (HIntegral F (1 - c) c (-(R j)) - HIntegral F (1 - c) c (R j))
        + (1 / (2 * Real.pi) : ℂ) * ∫ t in (-R j)..R j, Fline f k c t := by
    intro j
    obtain ⟨e1, e2, e3, e4⟩ := Zeta23.WeilEF.corner_re_im c (R j)
    rw [RectangleIntegral', RectangleIntegral, smul_eq_mul, e1, e2, e3, e4]
    have hv := verticals_eq_of hf hne hsymm hk hkc (R j)
    rw [hF]
    rw [show ∀ A B V₁ V₂ : ℂ, A - B + V₁ - V₂ = (A - B) + (V₁ - V₂) from fun _ _ _ _ => by ring, hv,
      smul_eq_mul, mul_add, Zeta23.WeilEF.inv_two_pi_I_mul_I]
  -- LHS → (1/2π) ∫ F
  have hL : Tendsto (fun j : ℕ => RectangleIntegral' F (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I))
      atTop (𝓝 ((1 / (2 * Real.pi) : ℂ) * ∫ t, Fline f k c t)) := by
    have h := ((hHbot.sub hHtop).const_mul (1 / (2 * Real.pi * I) : ℂ)).add
      (hV.const_mul (1 / (2 * Real.pi) : ℂ))
    simp only [sub_zero, mul_zero, zero_add] at h
    refine h.congr fun j => ?_
    rw [hdec j]
  have hL' : Tendsto (fun j : ℕ => ∑ ρ ∈ Z j, (analyticOrderNatAt f ρ : ℂ) * Hfn k ρ)
      atTop (𝓝 ((1 / (2 * Real.pi) : ℂ) * ∫ t, Fline f k c t)) :=
    hL.congr fun j => hE j
  have := tendsto_nhds_unique hL' hZlim
  exact this

end Generic

/-! ## Instances -/

section Rational

/-! ### f = s(s−1): the rational piece of (EF2)  (logDeriv = 1/s + 1/(s−1), zeros 0, 1, simple) -/

/-- the polynomial s(s−1). -/
def mulSubOne (s : ℂ) : ℂ := s * (s - 1)

theorem differentiable_mulSubOne : Differentiable ℂ mulSubOne := by
  unfold mulSubOne; fun_prop

theorem hasDerivAt_mulSubOne (s : ℂ) : HasDerivAt mulSubOne (2 * s - 1) s := by
  have h := (hasDerivAt_id s).fun_mul ((hasDerivAt_id s).sub_const 1)
  exact h.congr_deriv (by simp only [id]; ring)

theorem logDeriv_mulSubOne (s : ℂ) : logDeriv mulSubOne s = (2 * s - 1) / (s * (s - 1)) := by
  rw [logDeriv_apply, (hasDerivAt_mulSubOne s).deriv]
  rfl

theorem logDeriv_mulSubOne_one_sub (s : ℂ) : logDeriv mulSubOne (1 - s) = -logDeriv mulSubOne s := by
  rw [logDeriv_mulSubOne, logDeriv_mulSubOne, ← neg_div]
  have hden : (1 - s) * (1 - s - 1) = s * (s - 1) := by ring
  rw [hden]
  congr 1
  ring

theorem logDeriv_mulSubOne_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    logDeriv mulSubOne s = 1 / s + 1 / (s - 1) := by
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  rw [logDeriv_mulSubOne]
  field_simp
  ring

theorem mulSubOne_eq_zero_iff (s : ℂ) : mulSubOne s = 0 ↔ s ∈ ((({0, 1} : Finset ℂ)) : Set ℂ) := by
  simp [mulSubOne, sub_eq_zero]

theorem analyticOrderNatAt_mulSubOne_zero : analyticOrderNatAt mulSubOne 0 = 1 := by
  have h : analyticOrderAt mulSubOne 0 = (1 : ℕ) := by
    rw [AnalyticAt.analyticOrderAt_eq_natCast (differentiable_mulSubOne.analyticAt 0)]
    exact ⟨fun z => z - 1, by fun_prop, by simp, Eventually.of_forall fun z => by simp [mulSubOne]⟩
  simp [analyticOrderNatAt, h]

theorem analyticOrderNatAt_mulSubOne_one : analyticOrderNatAt mulSubOne 1 = 1 := by
  have h : analyticOrderAt mulSubOne 1 = (1 : ℕ) := by
    rw [AnalyticAt.analyticOrderAt_eq_natCast (differentiable_mulSubOne.analyticAt 1)]
    exact ⟨fun z => z, by fun_prop, by simp, Eventually.of_forall fun z => by simp [mulSubOne, mul_comm]⟩
  simp [analyticOrderNatAt, h]

/-- ‖1/s + 1/(s−1)‖ ≤ 2/|Im s| off the real axis. -/
theorem norm_logDeriv_mulSubOne_le {s : ℂ} (hs : s.im ≠ 0) :
    ‖logDeriv mulSubOne s‖ ≤ 2 / |s.im| := by
  have h0 : s ≠ 0 := fun h => hs (by simp [h])
  have h1 : s ≠ 1 := fun h => hs (by simp [h])
  have him0 : 0 < |s.im| := abs_pos.mpr hs
  have hn1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hn2 : |s.im| ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1); simpa using this
  rw [logDeriv_mulSubOne_eq h0 h1]
  calc ‖1 / s + 1 / (s - 1)‖ ≤ ‖1 / s‖ + ‖1 / (s - 1)‖ := norm_add_le _ _
    _ = 1 / ‖s‖ + 1 / ‖s - 1‖ := by simp
    _ ≤ 1 / |s.im| + 1 / |s.im| :=
        add_le_add (one_div_le_one_div_of_le him0 hn1) (one_div_le_one_div_of_le him0 hn2)
    _ = 2 / |s.im| := by ring

/-- good heights for s(s−1): R_j = j (j ≥ 2), ‖1/s + 1/(s−1)‖ ≤ 1 ≤ log²(j+3). -/
theorem mulSubOne_good_heights (a b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R : ℝ, (j : ℝ) ≤ R ∧ R ≤ (j : ℝ) + 1 ∧
      ∀ s : ℂ, (s.im = R ∨ s.im = -R) → a ≤ s.re → s.re ≤ b →
        mulSubOne s ≠ 0 ∧ ‖logDeriv mulSubOne s‖ ≤ C * (Real.log ((j : ℝ) + 3)) ^ 2 := by
  refine ⟨1, one_pos, 2, fun j hj => ⟨j, le_rfl, by linarith, fun s him _ _ => ?_⟩⟩
  have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have habs : |s.im| = j := by
    rcases him with h | h
    · rw [h, abs_of_nonneg (by linarith)]
    · rw [h, abs_neg, abs_of_nonneg (by linarith)]
  have hs : s.im ≠ 0 := by
    intro h; rw [h, abs_zero] at habs; linarith
  have hlog1 : 1 ≤ Real.log ((j : ℝ) + 3) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  constructor
  · intro h0
    rw [mulSubOne_eq_zero_iff] at h0
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at h0
    rcases h0 with h | h <;> (rw [h] at hs; simp at hs)
  · calc ‖logDeriv mulSubOne s‖ ≤ 2 / |s.im| := norm_logDeriv_mulSubOne_le hs
      _ ≤ 1 := by rw [habs, div_le_one (by linarith)]; exact hj2
      _ ≤ 1 * (Real.log ((j : ℝ) + 3)) ^ 2 := by nlinarith

/-- on Re s = c > 1:  logDeriv (s(s−1)) = 1/s + 1/(s−1), bounded by 1 + 1/(c−1). -/
theorem logDeriv_mulSubOne_line {c : ℝ} (hc1 : 1 < c) (t : ℝ) :
    logDeriv mulSubOne ((c : ℂ) + t * I) = 1 / ((c : ℂ) + t * I) + 1 / ((c : ℂ) + t * I - 1) :=
  logDeriv_mulSubOne_eq
    (fun h => by have := congrArg Complex.re h; simp at this; linarith)
    (fun h => by have := congrArg Complex.re h; simp at this; linarith)

theorem mulSubOne_line_bound {c : ℝ} (hc1 : 1 < c) :
    ∃ M : ℝ, ∀ t : ℝ, ‖logDeriv mulSubOne ((c : ℂ) + t * I)‖ ≤ M * Real.log (2 + |t|) := by
  set A : ℝ := 1 + 1 / (c - 1) with hA
  have hc0 : 0 < c - 1 := by linarith
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  refine ⟨2 * A, fun t => ?_⟩
  have hlog : 1 / 2 ≤ Real.log (2 + |t|) := by
    have h2 : Real.log 2 ≤ Real.log (2 + |t|) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
    linarith [Real.log_two_gt_d9]
  have hre1 : c ≤ ‖(c : ℂ) + t * I‖ := by
    have := Complex.abs_re_le_norm ((c : ℂ) + t * I)
    rw [abs_le] at this; simpa using this.2
  have hre2 : c - 1 ≤ ‖(c : ℂ) + t * I - 1‖ := by
    have := Complex.abs_re_le_norm ((c : ℂ) + t * I - 1)
    rw [abs_le] at this; simpa using this.2
  rw [logDeriv_mulSubOne_line hc1 t]
  calc ‖1 / ((c : ℂ) + t * I) + 1 / ((c : ℂ) + t * I - 1)‖
      ≤ ‖1 / ((c : ℂ) + t * I)‖ + ‖1 / ((c : ℂ) + t * I - 1)‖ := norm_add_le _ _
    _ = 1 / ‖(c : ℂ) + t * I‖ + 1 / ‖(c : ℂ) + t * I - 1‖ := by simp
    _ ≤ 1 / c + 1 / (c - 1) :=
        add_le_add (one_div_le_one_div_of_le (by linarith) hre1)
          (one_div_le_one_div_of_le (by linarith) hre2)
    _ ≤ A := by
        rw [hA]
        have : 1 / c ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        linarith
    _ = A * 1 := (mul_one A).symm
    _ ≤ A * (2 * Real.log (2 + |t|)) := mul_le_mul_of_nonneg_left (by linarith) hA0
    _ = 2 * A * Real.log (2 + |t|) := by ring

/-- The rational-line identity (cf. `rational_line`), as the f = s(s−1)
instance of full_line_identity_of:  (1/2π)∫[H(c+it)+H(1−c−it)]·(1/(c+it) + 1/(c+it−1)) dt = H(0) + H(1). -/
theorem rational_line_inst {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) :
    Integrable (fun t : ℝ => (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I))
        * (1 / ((c : ℂ) + t * I) + 1 / ((c : ℂ) + t * I - 1))) ∧
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I))
        * (1 / ((c : ℂ) + t * I) + 1 / ((c : ℂ) + t * I - 1)))
      = Hfn k 0 + Hfn k 1 := by
  have hstrip : ∀ ρ ∈ ((({0, 1} : Finset ℂ)) : Set ℂ), 1 - c < ρ.re ∧ ρ.re < c := by
    intro ρ hρ
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hρ
    rcases hρ with h | h <;> (rw [h]; simp; constructor <;> linarith)
  have hne : ∀ t : ℝ, mulSubOne ((c : ℂ) + t * I) ≠ 0 := ne_zero_on_line mulSubOne_eq_zero_iff hstrip
  have hint := integrable_Fline_of differentiable_mulSubOne hne (mulSubOne_line_bound hc1) hk hkc
    (by linarith) (by linarith)
  have hid := full_line_identity_of differentiable_mulSubOne (by linarith) (by linarith)
    logDeriv_mulSubOne_one_sub mulSubOne_eq_zero_iff hstrip (mulSubOne_good_heights (1 - c) c)
    (mulSubOne_line_bound hc1) hk hkc (Summable.of_finite)
  rw [Finset.tsum_subtype' ({0, 1} : Finset ℂ)
      (fun ρ => (analyticOrderNatAt mulSubOne ρ : ℂ) * Hfn k ρ),
    Finset.sum_pair zero_ne_one, analyticOrderNatAt_mulSubOne_zero,
    analyticOrderNatAt_mulSubOne_one, Nat.cast_one, one_mul, one_mul] at hid
  unfold Fline at hint
  simp_rw [logDeriv_mulSubOne_line hc1] at hint hid
  exact ⟨hint, hid⟩

end Rational

section XiDeriv

/-! ### f = ξ′: (EF1) [XF′ Prop. 4.1] -/

open Zeta23.WeilEF (EF_zero_sum_summable_gen)

/-- **(EF1) on a general line Re s = c ∈ (1, 3/2]**, conditional on (F2), with the line bound
‖ξ″/ξ′(c+it)‖ ≤ M log(2+|t|) as an explicit hypothesis (in tree only for c = 5/4:
LineBound.norm_logDeriv_xiDeriv_line).  Good heights: ZeroCount.xiDeriv_good_heights;
absolute convergence: WeilEF.EF_zero_sum_summable_gen plus the local zero count. -/
theorem full_line_identity_gen (hF2 : XiDerivZerosInStrip) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2)
    (hline : ∃ M : ℝ, ∀ t : ℝ, ‖logDeriv xiDeriv ((c : ℂ) + t * I)‖ ≤ M * Real.log (2 + |t|)) :
    Summable (fun ρ : {ρ : ℂ | IsXiDerivZero ρ} => (xiDerivMult (ρ : ℂ) : ℂ) * Hfn k ρ) ∧
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I))
        * logDeriv xiDeriv ((c : ℂ) + t * I))
      = ∑' ρ : {ρ : ℂ | IsXiDerivZero ρ}, (xiDerivMult (ρ : ℂ) : ℂ) * Hfn k ρ := by
  have hs : XiDerivSeam := xiDerivSeam_of_strip hF2
  obtain ⟨A₀, hA₀, hloc⟩ := (xiDeriv_riemannVonMangoldt hF2 hs).local_count
  have hsum : Summable (fun ρ : {ρ : ℂ | IsXiDerivZero ρ} => (xiDerivMult (ρ : ℂ) : ℂ) * Hfn k ρ) :=
    EF_zero_sum_summable_gen (xiDerivZeros hF2 hs) hA₀ hloc hk hkc
  refine ⟨hsum, ?_⟩
  have hstrip : ∀ ρ ∈ {ρ : ℂ | IsXiDerivZero ρ}, 1 - c < ρ.re ∧ ρ.re < c := fun ρ hρ => by
    have h := hF2 ρ hρ
    constructor <;> linarith [h.1, h.2]
  have hGH' : ∃ C : ℝ, 0 < C ∧ ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R : ℝ, (j : ℝ) ≤ R ∧ R ≤ (j : ℝ) + 1 ∧
      ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 - c ≤ s.re → s.re ≤ c →
        xiDeriv s ≠ 0 ∧ ‖logDeriv xiDeriv s‖ ≤ C * (Real.log ((j : ℝ) + 3)) ^ 2 := by
    obtain ⟨C, hC, j₀, h⟩ := ZeroCount.xiDeriv_good_heights hF2
    refine ⟨C, hC, j₀, fun j hj => ?_⟩
    obtain ⟨R, h1, h2, h3⟩ := h j hj
    exact ⟨R, h1, h2, fun s him hr1 hr2 => h3 s him (by linarith) (by linarith)⟩
  exact full_line_identity_of xiDeriv_differentiable (by linarith) (by linarith)
    logDeriv_xiDeriv_one_sub (Zset := {ρ : ℂ | IsXiDerivZero ρ}) (fun _ => Iff.rfl) hstrip hGH'
    hline hk hkc hsum

/-- **(EF1) The full-line identity for ξ″/ξ′** [XF′ Prop. 4.1] on the line Re s = 5/4,
conditional on (F2) only:  Σ'_{ξ′(ρ)=0} m_ρ H(ρ) converges absolutely and equals
(1/2π) ∫ [H(5/4+it) + H(−1/4−it)]·ξ″/ξ′(5/4+it) dt.  No pole terms: ξ′ is entire. -/
theorem full_line_identity (hF2 : XiDerivZerosInStrip) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) :
    Summable (fun ρ : {ρ : ℂ | IsXiDerivZero ρ} => (xiDerivMult (ρ : ℂ) : ℂ) * Hfn k ρ) ∧
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, (Hfn k (((5 / 4 : ℝ) : ℂ) + t * I)
        + Hfn k (1 - (5 / 4 : ℝ) - t * I)) * logDeriv xiDeriv (((5 / 4 : ℝ) : ℂ) + t * I))
      = ∑' ρ : {ρ : ℂ | IsXiDerivZero ρ}, (xiDerivMult (ρ : ℂ) : ℂ) * Hfn k ρ := by
  obtain ⟨C, _, hC⟩ := norm_logDeriv_xiDeriv_line hF2
  exact full_line_identity_gen hF2 hk hkc (by norm_num) (by norm_num) ⟨C, hC⟩

end XiDeriv

end XiPrime
end Zeta23
