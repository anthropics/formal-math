/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of the paper
"More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/
import Zeta23.PrimeSideTemp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Prime side, part B: [prop:PP] and the assembly of Theorem [thm:traces]

Paper §5 ("The prime side: magnitude"), subsections "Evaluation of 𝓜" and "Summary".

Contents
* §0 glue between the explicit-constant interface shape `EvBound` and Mathlib's `IsBigO`.
* §1 `Zeta23.PaperParams`: elementary facts about the scalar parameters `l, ℓ₁, L, X, λ₁, 𝓔_T`
  of `Defs.lean` (growth, positivity, `𝓔_T → 0`).  Pure real analysis, no hypotheses.
* §2 `Zeta23.PrimeSide.Facts` / `Zeta23.PrimeSide.tracesBounds_of_facts`: the proof of [thm:traces]
  ([eq:tr1], [eq:tr2], [eq:ratio], second forms) from the five sub-results of §5 + [eq:muints] (H-Γ)
  + [eq:RvM] (H-RvM) + [eq:abdef] (Taper), all taken as hypotheses on abstract real functions of `T`.
  This is where the paper's constants `ℓ₁² + L²/3` and `F(λ₁)` are checked.
* §3 [prop:PP]: `𝓜[P_X,P_X] = (T/π) Σ_{n≤X} Λ(n)²/n · g(log n) + O(L² X)` and the sandwich
  `(L−2w)³/6 + O(L²) ≤ Σ a_n² g(y_n) ≤ L³/6 + O(L²)` — over the concrete definitions of `Defs.lean`
  and `Mform`.
-/

noncomputable section

open Real Filter Asymptotics Topology

namespace Zeta23

/-! ## §0.  Explicit-constant ↔ `IsBigO` glue -/

namespace EvBound

lemma isBigO {f g : ℝ → ℝ} (h : EvBound f g) : f =O[atTop] g := by
  obtain ⟨C, hC, T₀, hT⟩ := h
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop T₀] with T hT'
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact (hT T hT').trans (mul_le_mul_of_nonneg_left (le_abs_self _) hC.le)

/-- From `IsBigO` back to the explicit form, when the majorant is eventually nonnegative. -/
lemma of_isBigO {f g : ℝ → ℝ} (h : f =O[atTop] g) (hg : ∀ᶠ T in atTop, 0 ≤ g T) :
    EvBound f g := by
  obtain ⟨C, hC, h⟩ := h.exists_pos
  rw [IsBigOWith] at h
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (h.and hg)
  refine ⟨C, hC, T₀, fun T hT => ?_⟩
  obtain ⟨h1, h2⟩ := hT₀ T hT
  simpa [Real.norm_eq_abs, abs_of_nonneg h2] using h1

lemma iff_isBigO {f g : ℝ → ℝ} (hg : ∀ᶠ T in atTop, 0 ≤ g T) :
    EvBound f g ↔ f =O[atTop] g := ⟨isBigO, fun h => of_isBigO h hg⟩

lemma mono_right {f g g' : ℝ → ℝ} (h : EvBound f g) (hgg' : ∀ᶠ T in atTop, g T ≤ g' T) :
    EvBound f g' := by
  obtain ⟨C, hC, T₀, hT⟩ := h
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hgg'
  refine ⟨C, hC, max T₀ T₁, fun T hT' => (hT T (le_of_max_le_left hT')).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (hT₁ T (le_of_max_le_right hT')) hC.le

/-- Weaken the majorant up to a constant: if `g ≤ c·g'` eventually then `EvBound f g → EvBound f g'`. -/
lemma mono_right' {f g g' : ℝ → ℝ} (h : EvBound f g) {c : ℝ} (hc : 0 < c)
    (hgg' : ∀ᶠ T in atTop, g T ≤ c * g' T) : EvBound f g' := by
  obtain ⟨C, hC, T₀, hT⟩ := h
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hgg'
  refine ⟨C * c, mul_pos hC hc, max T₀ T₁, fun T hT' => (hT T (le_of_max_le_left hT')).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hT₁ T (le_of_max_le_right hT')) hC.le

/-- An eventual pointwise bound with an explicit constant gives an `EvBound`. -/
lemma of_eventually_le {f g : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ T in atTop, |f T| ≤ c * g T) : EvBound f g := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp h
  exact ⟨c, hc, T₀, hT₀⟩

lemma eventually_le {f g : ℝ → ℝ} (h : EvBound f g) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T in atTop, |f T| ≤ C * g T := by
  obtain ⟨C, hC, T₀, hT⟩ := h
  exact ⟨C, hC, eventually_atTop.mpr ⟨T₀, hT⟩⟩

lemma add {f₁ f₂ g : ℝ → ℝ} (h₁ : EvBound f₁ g) (h₂ : EvBound f₂ g) :
    EvBound (fun T => f₁ T + f₂ T) g := by
  obtain ⟨C₁, hC₁, h₁⟩ := h₁.eventually_le
  obtain ⟨C₂, hC₂, h₂⟩ := h₂.eventually_le
  refine of_eventually_le (add_pos hC₁ hC₂) ?_
  filter_upwards [h₁, h₂] with T a b
  calc |f₁ T + f₂ T| ≤ |f₁ T| + |f₂ T| := abs_add_le _ _
    _ ≤ C₁ * g T + C₂ * g T := add_le_add a b
    _ = (C₁ + C₂) * g T := by ring

lemma sub {f₁ f₂ g : ℝ → ℝ} (h₁ : EvBound f₁ g) (h₂ : EvBound f₂ g) :
    EvBound (fun T => f₁ T - f₂ T) g := by
  obtain ⟨C₁, hC₁, h₁⟩ := h₁.eventually_le
  obtain ⟨C₂, hC₂, h₂⟩ := h₂.eventually_le
  refine of_eventually_le (add_pos hC₁ hC₂) ?_
  filter_upwards [h₁, h₂] with T a b
  calc |f₁ T - f₂ T| ≤ |f₁ T| + |f₂ T| := abs_sub _ _
    _ ≤ C₁ * g T + C₂ * g T := add_le_add a b
    _ = (C₁ + C₂) * g T := by ring

lemma const_mul {f g : ℝ → ℝ} (h : EvBound f g) (c : ℝ) :
    EvBound (fun T => c * f T) g := by
  obtain ⟨C, hC, h⟩ := h.eventually_le
  refine of_eventually_le (mul_pos (by positivity : (0:ℝ) < |c| + 1) hC) ?_
  filter_upwards [h, h.mono (fun T hT => (abs_nonneg _).trans hT)] with T a b
  rw [abs_mul, mul_assoc]
  calc |c| * |f T| ≤ |c| * (C * g T) := mul_le_mul_of_nonneg_left a (abs_nonneg c)
    _ ≤ (|c| + 1) * (C * g T) := by nlinarith

/-- Change `f` up to eventual pointwise domination. -/
lemma of_abs_le {f f' g : ℝ → ℝ} (h : EvBound f g) (h' : ∀ᶠ T in atTop, |f' T| ≤ |f T|) :
    EvBound f' g := by
  obtain ⟨C, hC, h⟩ := h.eventually_le
  refine of_eventually_le hC ?_
  filter_upwards [h, h'] with T a b using b.trans a

lemma congr_left {f f' g : ℝ → ℝ} (h : EvBound f g) (h' : ∀ᶠ T in atTop, f' T = f T) :
    EvBound f' g := h.of_abs_le (h'.mono fun T hT => by rw [hT])

/-- The majorant of an `EvBound` is eventually nonnegative. -/
lemma majorant_nonneg {f g : ℝ → ℝ} (h : EvBound f g) : ∀ᶠ T in atTop, 0 ≤ g T := by
  obtain ⟨C, hC, h⟩ := h.eventually_le
  filter_upwards [h] with T hT
  exact (mul_nonneg_iff_of_pos_left hC).mp ((abs_nonneg _).trans hT)

end EvBound

/-! ## §1.  The scalar parameters of `Defs.lean` -/

namespace PaperParams

lemma l_tendsto_atTop : Tendsto l atTop atTop := by
  unfold l
  exact Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))

lemma ell1_eq (T : ℝ) : ell1 T = l T + (2 * Real.log 2 - 1) := by unfold ell1; ring

/-- `2 log 2 − 1 > 0`, so `ℓ₁ > l`. -/
lemma two_log_two_sub_one_pos : 0 < 2 * Real.log 2 - 1 := by
  have := Real.log_two_gt_d9
  linarith

lemma l_lt_ell1 (T : ℝ) : l T < ell1 T := by
  rw [ell1_eq]; linarith [two_log_two_sub_one_pos]

lemma ell1_tendsto_atTop : Tendsto ell1 atTop atTop :=
  tendsto_atTop_mono (fun T => (l_lt_ell1 T).le) l_tendsto_atTop

variable (P : Params)

lemma X_pos (T : ℝ) : 0 < P.X T := Real.exp_pos _

/-- `X = (T/2π)^λ` for `T > 0`. -/
lemma X_eq_rpow {T : ℝ} (hT : 0 < T) : P.X T = (T / (2 * π)) ^ P.lam := by
  unfold Params.X Params.L l
  rw [Real.rpow_def_of_pos (div_pos hT (by positivity)), mul_comm]

lemma L_tendsto_atTop (hP : 0 < P.lam) : Tendsto P.L atTop atTop := by
  unfold Params.L
  exact l_tendsto_atTop.const_mul_atTop hP

lemma log_l_tendsto_atTop : Tendsto (fun T => Real.log (l T)) atTop atTop :=
  Real.tendsto_log_atTop.comp l_tendsto_atTop

lemma eventually_l_ge (c : ℝ) : ∀ᶠ T in atTop, c ≤ l T := l_tendsto_atTop.eventually_ge_atTop c

lemma eventually_log_l_ge (c : ℝ) : ∀ᶠ T in atTop, c ≤ Real.log (l T) :=
  log_l_tendsto_atTop.eventually_ge_atTop c

lemma eventually_L_ge (hlam : 0 < P.lam) (c : ℝ) : ∀ᶠ T in atTop, c ≤ P.L T :=
  (L_tendsto_atTop P hlam).eventually_ge_atTop c

lemma l_le_ell1 (T : ℝ) : l T ≤ ell1 T := (l_lt_ell1 T).le

lemma eventually_ell1_le_two_l : ∀ᶠ T in atTop, ell1 T ≤ 2 * l T := by
  filter_upwards [eventually_l_ge 1] with T h
  rw [ell1_eq]
  have := Real.log_two_lt_d9
  linarith

/-- `L ≤ l` when `λ ≤ 1` and `l ≥ 0`. -/
lemma L_le_l (hlam1 : P.lam ≤ 1) {T : ℝ} (hl : 0 ≤ l T) : P.L T ≤ l T := by
  unfold Params.L; nlinarith

/-- `√X = (T/2π)^{λ/2}`. -/
lemma sqrt_X_eq {T : ℝ} (hT : 0 < T) : Real.sqrt (P.X T) = (T / (2 * π)) ^ (P.lam / 2) := by
  rw [X_eq_rpow P hT, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  ring_nf

/-- `√X ≤ T^{λ/2}` for `T > 0` (as `T/2π ≤ T`). -/
lemma sqrt_X_le_rpow (hlam : 0 < P.lam) {T : ℝ} (hT : 0 < T) :
    Real.sqrt (P.X T) ≤ T ^ (P.lam / 2) := by
  rw [sqrt_X_eq P hT]
  apply Real.rpow_le_rpow (by positivity) _ (by linarith)
  rw [div_le_iff₀ (by positivity)]
  have := Real.pi_gt_three
  nlinarith

/-- `X ≤ T` eventually (`λ ≤ 1`). -/
lemma eventually_X_le_T (_hlam : 0 < P.lam) (hlam1 : P.lam ≤ 1) : ∀ᶠ T in atTop, P.X T ≤ T := by
  filter_upwards [eventually_ge_atTop (2 * π)] with T hT
  have hπ := Real.pi_gt_three
  have hT0 : 0 < T := by linarith
  rw [X_eq_rpow P hT0]
  have h1 : 1 ≤ T / (2 * π) := by rw [le_div_iff₀ (by positivity)]; linarith
  calc (T / (2 * π)) ^ P.lam ≤ (T / (2 * π)) ^ (1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 hlam1
    _ = T / (2 * π) := Real.rpow_one _
    _ ≤ T := by rw [div_le_iff₀ (by positivity)]; nlinarith

lemma eventually_one_le_X (hlam : 0 < P.lam) : ∀ᶠ T in atTop, 1 ≤ P.X T := by
  filter_upwards [eventually_L_ge P hlam 0] with T hL
  simpa [Params.X] using Real.one_le_exp hL

lemma rpow_half_sub_one_mul {T : ℝ} (hT : 0 < T) (s : ℝ) : T ^ (s - 1) * T = T ^ s := by
  rw [Real.rpow_sub_one hT.ne', div_mul_cancel₀ _ hT.ne']

variable {P}

/-- each of the three summands of `𝓔_T` is eventually nonnegative -/
lemma calE_summands_nonneg (hlam : 0 < P.lam) (hw : 0 ≤ P.w) :
    ∀ᶠ T in atTop, 0 ≤ P.w / P.L T ∧
      0 ≤ (l T ^ 2 + P.X T) * Real.log (l T) / (T * l T) ∧ 0 ≤ T ^ (P.lam / 2 - 1) := by
  filter_upwards [(L_tendsto_atTop P hlam).eventually_ge_atTop 0,
    l_tendsto_atTop.eventually_ge_atTop 1, eventually_ge_atTop (0:ℝ)] with T hL hl hT
  refine ⟨div_nonneg hw hL, div_nonneg (mul_nonneg (add_nonneg (sq_nonneg _) (X_pos P T).le)
    (Real.log_nonneg hl)) (mul_nonneg hT (by linarith)), Real.rpow_nonneg hT _⟩

/-- `𝓔_T ≥ w / L` for `T` large. -/
lemma calE_ge_w_div_L (hlam : 0 < P.lam) (hw : 0 ≤ P.w) :
    ∀ᶠ T in atTop, P.w / P.L T ≤ P.calE T := by
  filter_upwards [calE_summands_nonneg hlam hw] with T ⟨_, h2, h3⟩
  unfold Params.calE; linarith

/-- `𝓔_T ≥ T^{λ/2-1}` for `T` large. -/
lemma calE_ge_rpow (hlam : 0 < P.lam) (hw : 0 ≤ P.w) :
    ∀ᶠ T in atTop, T ^ (P.lam / 2 - 1) ≤ P.calE T := by
  filter_upwards [calE_summands_nonneg hlam hw] with T ⟨h1, h2, _⟩
  unfold Params.calE; linarith

/-- `𝓔_T ≥ (l²+X) log l /(T l)` for `T` large. -/
lemma calE_ge_mid (hlam : 0 < P.lam) (hw : 0 ≤ P.w) :
    ∀ᶠ T in atTop, (l T ^ 2 + P.X T) * Real.log (l T) / (T * l T) ≤ P.calE T := by
  filter_upwards [calE_summands_nonneg hlam hw] with T ⟨h1, _, h3⟩
  unfold Params.calE; linarith

lemma calE_nonneg_eventually (hlam : 0 < P.lam) (hw : 0 ≤ P.w) :
    ∀ᶠ T in atTop, 0 ≤ P.calE T := by
  filter_upwards [calE_summands_nonneg hlam hw] with T ⟨h1, h2, h3⟩
  unfold Params.calE; linarith

/-- `𝓔_T → 0` as `T → ∞`, for every fixed `0 < λ ≤ 1` and `w` (the paper [thm:traces]:
  "`𝓔_T ≪_λ w/L + T^{λ−1} log l` (λ<1), `𝓔_T ≪ w/L + log l / l` (λ=1)"; and `L = λ l → ∞`). -/
theorem calE_tendsto_zero (hlam : 0 < P.lam) (hlam1 : P.lam ≤ 1) (hw : 0 ≤ P.w) :
    Tendsto P.calE atTop (𝓝 0) := by
  -- w / L → 0
  have h1 : Tendsto (fun T => P.w / P.L T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (L_tendsto_atTop P hlam)
  -- T^{λ/2 - 1} → 0
  have h3 : Tendsto (fun T : ℝ => T ^ (P.lam / 2 - 1)) atTop (𝓝 0) := by
    have : P.lam / 2 - 1 = -(1 - P.lam / 2) := by ring
    rw [this]; exact tendsto_rpow_neg_atTop (by linarith)
  -- l² / T → 0
  have h2a : Tendsto (fun T => l T ^ 2 / T) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop (2 * π) 0 2 (by positivity)).comp
      (tendsto_id.atTop_div_const (show (0:ℝ) < 2 * π by positivity))
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    simp only [Function.comp, l, id, add_zero]
    rw [mul_div_cancel₀ _ (by positivity)]
  -- log l / l → 0
  have h2b : Tendsto (fun T => Real.log (l T) / l T) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp l_tendsto_atTop
    simpa [Function.comp_def] using this
  have hsum : Tendsto (fun T => P.w / P.L T + (l T ^ 2 / T + Real.log (l T) / l T)
      + T ^ (P.lam / 2 - 1)) atTop (𝓝 0) := by
    simpa using (h1.add (h2a.add h2b)).add h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (calE_nonneg_eventually hlam hw) ?_
  filter_upwards [eventually_l_ge 1, eventually_X_le_T P hlam hlam1, eventually_ge_atTop 1]
    with T hl hXT hT
  unfold Params.calE
  have hlog0 : 0 ≤ Real.log (l T) := Real.log_nonneg hl
  have hlogle : Real.log (l T) ≤ l T := Real.log_le_self (by linarith)
  have hX0 : 0 ≤ P.X T := (X_pos P T).le
  have hl0 : 0 < l T := by linarith only [hl]
  have hT0 : 0 < T := by linarith only [hT]
  have e1 : l T ^ 2 * Real.log (l T) / (T * l T) ≤ l T ^ 2 / T := by
    rw [div_le_div_iff₀ (by positivity) hT0]
    nlinarith only [hlogle, mul_nonneg (sq_nonneg (l T)) hT0.le]
  have e2 : P.X T * Real.log (l T) / (T * l T) ≤ Real.log (l T) / l T := by
    rw [div_le_div_iff₀ (by positivity) hl0]
    nlinarith only [hXT, mul_nonneg hlog0 hl0.le]
  have e3 : (l T ^ 2 + P.X T) * Real.log (l T) / (T * l T)
      = l T ^ 2 * Real.log (l T) / (T * l T) + P.X T * Real.log (l T) / (T * l T) := by ring
  linarith only [e1, e2, e3]

end PaperParams

/-! ## §2.  Assembly of Theorem [thm:traces] from the §5 sub-results

All quantities are real functions of `T` at fixed `P = (ϱ, λ, w)`.  The hypotheses below are exactly
the conclusions of [prop:trace], [lem:ends], [eq:Msplit], [prop:mumu], [prop:PP], [prop:cross]
(the paper §5), [eq:muints] (from H-Γ), [eq:RvM] (H-RvM) and [eq:abdef] (Taper), each in the
explicit-constant form `EvBound`. -/

namespace PrimeSide

open PaperParams

/-- The real-valued functions of `T` entering [thm:traces].  Docstrings give the paper object. -/
structure Data (P : Params) where
  /-- `a := L⁻¹ ∫ φ²` [eq:abdef] -/
  aT : ℝ → ℝ
  /-- `b := L⁻¹ ∫ φ⁴` [eq:abdef] -/
  bT : ℝ → ℝ
  /-- `tr G̃` (prime-side expression, [eq:Gdef] second form, divided by `L`) -/
  trG : ℝ → ℝ
  /-- `tr G̃² = Σ_{k,l<d} G̃_{kl}²` -/
  trG2 : ℝ → ℝ
  /-- `N(T,2T)` -/
  Ncnt : ℝ → ℝ
  /-- `𝓜 := ∬_{I×I} Φ(τ−τ')² ν_X(τ) ν_X(τ') dτ dτ'` [lem:ends] -/
  Mtot : ℝ → ℝ
  /-- `𝓜[μ,μ]` -/
  Mmumu : ℝ → ℝ
  /-- `𝓜[P_X,P_X]` -/
  MPP : ℝ → ℝ
  /-- `𝓜[μ,P_X]` -/
  MmuP : ℝ → ℝ
  /-- `𝓜[μ,Π_X]` -/
  MmuPi : ℝ → ℝ
  /-- `𝓜[P_X,Π_X]` -/
  MPPi : ℝ → ℝ
  /-- `𝓜[Π_X,Π_X]` -/
  MPiPi : ℝ → ℝ
  /-- `∫_T^{2T} μ(τ)² dτ` -/
  intMu2 : ℝ → ℝ
  /-- `Σ_{n ≤ X} Λ(n)²/n · g(log n) = Σ_n a_n² g(y_n)` -/
  sumL2g : ℝ → ℝ

variable {P : Params} (D : Data P)

/-- Hypotheses of the [thm:traces] assembly = conclusions of the §5 sub-results and of the
classical inputs, on the abstract data `D`.  Paper labels in each field's docstring. -/
structure Facts : Prop where
  lam_pos : 0 < P.lam
  lam_le_one : P.lam ≤ 1
  one_le_w : 1 ≤ P.w
  /-- [eq:abdef]: `1 − 2w/L ≤ b ≤ a ≤ 1` (for `T` large, so that `w ≤ L/8`). -/
  abdef : ∀ᶠ T in atTop, 1 - 2 * P.w / P.L T ≤ D.bT T ∧ D.bT T ≤ D.aT T ∧ D.aT T ≤ 1
  /-- [eq:RvM] (H-RvM): `N(T,2T) = T ℓ₁/2π + O(l)`. -/
  rvm : EvBound (fun T => D.Ncnt T - T * ell1 T / (2 * π)) l
  /-- [eq:muints], second formula (from H-Γ): `∫_T^{2T} μ² = (T ℓ₁²/4π²)(1 + O(l⁻²))`. -/
  muints2 : EvBound (fun T => D.intMu2 T - T * ell1 T ^ 2 / (4 * π ^ 2))
      (fun T => T * ell1 T ^ 2 / (4 * π ^ 2) / l T ^ 2)
  /-- [prop:trace]: `tr G̃ = a L N(T,2T) + O(L √X)`. -/
  prop_trace : EvBound (fun T => D.trG T - D.aT T * P.L T * D.Ncnt T)
      (fun T => P.L T * Real.sqrt (P.X T))
  /-- [lem:ends]: `tr G̃² = 𝓜 + O(L l log l (l² + X))`. -/
  lem_ends : EvBound (fun T => D.trG2 T - D.Mtot T)
      (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T))
  /-- [eq:Msplit]: bilinear expansion of `𝓜 = 𝓜[ν_X, ν_X]`, `ν_X = μ + Π_X + P_X`. -/
  Msplit : ∀ᶠ T in atTop, D.Mtot T =
      D.Mmumu T + D.MPP T + 2 * D.MmuP T + 2 * D.MmuPi T + 2 * D.MPPi T + D.MPiPi T
  /-- [prop:mumu], first form: `𝓜[μ,μ] = 2π b L ∫_T^{2T} μ² + O(l² log L)`. -/
  prop_mumu : EvBound (fun T => D.Mmumu T - 2 * π * D.bT T * P.L T * D.intMu2 T)
      (fun T => l T ^ 2 * Real.log (P.L T))
  /-- [prop:PP] (this file, §3), first form:
    `𝓜[P_X,P_X] = (T/π) Σ_{n≤X} Λ(n)²/n g(log n) + O(L² X)`. -/
  prop_PP : EvBound (fun T => D.MPP T - T / π * D.sumL2g T) (fun T => P.L T ^ 2 * P.X T)
  /-- [prop:PP] (this file, §3), sandwich lower half: `Σ a_n² g(y_n) ≥ (L−2w)³/6 − O(L²)`. -/
  sum_lower : EvBound (fun T => min (D.sumL2g T - (P.L T - 2 * P.w) ^ 3 / 6) 0)
      (fun T => P.L T ^ 2)
  /-- sandwich upper half: `Σ a_n² g(y_n) ≤ L³/6 + O(L²)`. -/
  sum_upper : EvBound (fun T => max (D.sumL2g T - P.L T ^ 3 / 6) 0) (fun T => P.L T ^ 2)
  /-- [prop:cross]: `𝓜[μ,P_X] ≪ l √X`. -/
  cross_muP : EvBound D.MmuP (fun T => l T * Real.sqrt (P.X T))
  /-- [prop:cross]: `𝓜[μ,Π_X] ≪ l L √X`. -/
  cross_muPi : EvBound D.MmuPi (fun T => l T * P.L T * Real.sqrt (P.X T))
  /-- [prop:cross]: `𝓜[P_X,Π_X] ≪ L X`. -/
  cross_PPi : EvBound D.MPPi (fun T => P.L T * P.X T)
  /-- [prop:cross]: `𝓜[Π_X,Π_X] ≪ L X / T`. -/
  cross_PiPi : EvBound D.MPiPi (fun T => P.L T * P.X T / T)

/-! ### The assembly -/

section assembly
variable {D} (h : Facts D)
include h

/-- [eq:tr1], first equality — this is [prop:trace] verbatim. -/
theorem tr1 : EvBound (fun T => D.trG T - D.aT T * P.L T * D.Ncnt T)
    (fun T => P.L T * Real.sqrt (P.X T)) := h.prop_trace

/-- From [eq:RvM]: eventually `T l /(4π) ≤ N(T,2T)` (and hence `N > 0`). -/
lemma Ncnt_lower : ∀ᶠ T in atTop, T * l T / (4 * π) ≤ D.Ncnt T := by
  obtain ⟨A, hA, hN⟩ := h.rvm.eventually_le
  filter_upwards [hN, eventually_ge_atTop (4 * π * A), eventually_l_ge 0] with T hN hTA hl
  have hπ := Real.pi_pos
  have h1 : -(A * l T) ≤ D.Ncnt T - T * ell1 T / (2 * π) := (abs_le.mp hN).1
  have h2 : T * l T ≤ T * ell1 T := mul_le_mul_of_nonneg_left (l_le_ell1 T) (by nlinarith)
  have h3 : T * l T / (2 * π) ≤ T * ell1 T / (2 * π) := div_le_div_of_nonneg_right h2 (by positivity)
  have h4 : T * l T / (4 * π) = T * l T / (2 * π) - T * l T / (4 * π) := by ring
  have h5 : A * l T ≤ T * l T / (4 * π) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  linarith

/-- eventually `T ≤ 4π N(T,2T)`. -/
lemma T_le_Ncnt : ∀ᶠ T in atTop, T ≤ 4 * π * D.Ncnt T := by
  filter_upwards [Ncnt_lower h, eventually_l_ge 1, eventually_ge_atTop 0] with T hN hl hT
  have hπ := Real.pi_pos
  have : T * l T ≤ 4 * π * D.Ncnt T := by rw [div_le_iff₀ (by positivity)] at hN; linarith
  nlinarith

lemma Ncnt_pos : ∀ᶠ T in atTop, 0 < D.Ncnt T := by
  filter_upwards [Ncnt_lower h, eventually_l_ge 1, eventually_ge_atTop 1] with T hN hl hT
  have hπ := Real.pi_pos
  exact lt_of_lt_of_le (by positivity) (le_trans (by gcongr : T * 1 / (4 * π) ≤ _) hN)
    |> fun h => by simpa using h

/-- [eq:tr1], second equality: `tr G̃ = L N(T,2T)(1 + O(𝓔_T))`.
  Paper: from `1 − 2w/L ≤ a ≤ 1`, `L N ≫ L T l` and `√X ≤ T^{λ/2}`. -/
theorem tr1' : EvBound (fun T => D.trG T - P.L T * D.Ncnt T)
    (fun T => P.calE T * (P.L T * D.Ncnt T)) := by
  obtain ⟨C₁, hC₁, h1⟩ := h.prop_trace.eventually_le
  have hlam := h.lam_pos
  have hw : 0 ≤ P.w := by linarith [h.one_le_w]
  refine EvBound.of_eventually_le (c := 4 * π * C₁ + 2) (by positivity) ?_
  filter_upwards [h1, h.abdef, calE_ge_w_div_L hlam hw, calE_ge_rpow hlam hw,
    calE_nonneg_eventually hlam hw, T_le_Ncnt h, Ncnt_pos h, eventually_ge_atTop 1,
    eventually_L_ge P hlam 1] with T h1 hab hEw hEr hE0 hTN hN0 hT1 hL1
  obtain ⟨hb1, hba, ha1⟩ := hab
  have hT0 : 0 < T := by linarith
  have hL0 : 0 ≤ P.L T := by linarith
  set N := D.Ncnt T
  set L := P.L T
  set E := P.calE T
  have hLN : 0 ≤ L * N := mul_nonneg hL0 hN0.le
  -- the taper discrepancy (1 - a) L N ≤ (2w/L) L N ≤ 2 E L N
  have hA : |D.aT T * L * N - L * N| ≤ 2 * E * (L * N) := by
    have : D.aT T * L * N - L * N = -((1 - D.aT T) * (L * N)) := by ring
    rw [this, abs_neg, abs_of_nonneg (mul_nonneg (by linarith) hLN)]
    have h2 : 1 - D.aT T ≤ 2 * E := by
      have : 2 * P.w / L = 2 * (P.w / L) := by ring
      linarith
    exact mul_le_mul_of_nonneg_right h2 hLN
  -- the √X term: C₁ L √X ≤ C₁ L T^{λ/2} = C₁ L T^{λ/2-1} T ≤ C₁ L E (4π N)
  have hB : C₁ * (L * Real.sqrt (P.X T)) ≤ 4 * π * C₁ * (E * (L * N)) := by
    have hs : Real.sqrt (P.X T) ≤ T ^ (P.lam / 2 - 1) * T := by
      rw [rpow_half_sub_one_mul hT0]; exact sqrt_X_le_rpow P hlam hT0
    have hs2 : T ^ (P.lam / 2 - 1) * T ≤ E * (4 * π * N) :=
      mul_le_mul hEr hTN hT0.le hE0
    calc C₁ * (L * Real.sqrt (P.X T)) ≤ C₁ * (L * (E * (4 * π * N))) := by
          gcongr; exact hs.trans hs2
      _ = 4 * π * C₁ * (E * (L * N)) := by ring
  calc |D.trG T - L * N|
      ≤ |D.trG T - D.aT T * L * N| + |D.aT T * L * N - L * N| := abs_sub_le _ _ _
    _ ≤ C₁ * (L * Real.sqrt (P.X T)) + 2 * E * (L * N) := add_le_add h1 hA
    _ ≤ 4 * π * C₁ * (E * (L * N)) + 2 * E * (L * N) := by linarith
    _ = (4 * π * C₁ + 2) * (E * (L * N)) := by ring

/-- The common regime `T ≥ 1, l ≥ 1, log l ≥ 1, L ≥ 1, X ≥ 1, L ≤ l, X ≤ T` (eventually). -/
lemma regime : ∀ᶠ T in atTop, 1 ≤ T ∧ 1 ≤ l T ∧ 1 ≤ Real.log (l T) ∧ 1 ≤ P.L T ∧ 1 ≤ P.X T ∧
    P.L T ≤ l T ∧ P.X T ≤ T := by
  have hlam := h.lam_pos
  filter_upwards [eventually_ge_atTop 1, eventually_l_ge 1, eventually_log_l_ge 1,
    eventually_L_ge P hlam 1, eventually_one_le_X P hlam, eventually_X_le_T P hlam h.lam_le_one]
    with T h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, L_le_l P h.lam_le_one (by linarith), h6⟩

/-- [eq:tr2], first form:
  `tr G̃² = 2π b L ∫_T^{2T} μ² + (T/π) Σ Λ(n)²/n g(log n) + O(L l log l (l²+X))`. -/
theorem tr2_first : EvBound
    (fun T => D.trG2 T - (2 * π * D.bT T * P.L T * D.intMu2 T + T / π * D.sumL2g T))
    (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
  -- every secondary error term is ≤ R := L l log l (l² + X) in the regime
  have e3 : EvBound (fun T => D.Mmumu T - 2 * π * D.bT T * P.L T * D.intMu2 T)
      (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
    refine h.prop_mumu.mono_right' one_pos ?_
    filter_upwards [regime h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩
    have hlogL : Real.log (P.L T) ≤ Real.log (l T) := Real.log_le_log (by linarith) hLl
    have hlogL0 : 0 ≤ Real.log (P.L T) := Real.log_nonneg hL
    calc l T ^ 2 * Real.log (P.L T) ≤ l T ^ 2 * Real.log (l T) := by gcongr
      _ = 1 * l T * Real.log (l T) * l T := by ring
      _ ≤ P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = _ := (one_mul _).symm
  have e4 : EvBound (fun T => D.MPP T - T / π * D.sumL2g T)
      (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
    refine h.prop_PP.mono_right' one_pos ?_
    filter_upwards [regime h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩
    calc P.L T ^ 2 * P.X T = P.L T * P.L T * 1 * P.X T := by ring
      _ ≤ P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = 1 * (P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := (one_mul _).symm
  have hsqrtX : ∀ᶠ T in atTop, Real.sqrt (P.X T) ≤ P.X T := by
    filter_upwards [regime h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have e5 : EvBound D.MmuP (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
    refine h.cross_muP.mono_right' one_pos ?_
    filter_upwards [regime h, hsqrtX] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩ hs
    calc l T * Real.sqrt (P.X T) ≤ l T * P.X T := by gcongr
      _ = 1 * l T * 1 * (0 + P.X T) := by ring
      _ ≤ P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = _ := (one_mul _).symm
  have e6 : EvBound D.MmuPi (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
    refine h.cross_muPi.mono_right' one_pos ?_
    filter_upwards [regime h, hsqrtX] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩ hs
    calc l T * P.L T * Real.sqrt (P.X T) ≤ l T * P.L T * P.X T := by gcongr
      _ = P.L T * l T * 1 * (0 + P.X T) := by ring
      _ ≤ P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = _ := (one_mul _).symm
  have e7 : EvBound D.MPPi (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
    refine h.cross_PPi.mono_right' one_pos ?_
    filter_upwards [regime h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩
    calc P.L T * P.X T = P.L T * 1 * 1 * (0 + P.X T) := by ring
      _ ≤ P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = _ := (one_mul _).symm
  have e8 : EvBound D.MPiPi (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
    refine h.cross_PiPi.mono_right' one_pos ?_
    filter_upwards [regime h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩
    calc P.L T * P.X T / T ≤ P.L T * P.X T := div_le_self (by nlinarith) hT
      _ = P.L T * 1 * 1 * (0 + P.X T) := by ring
      _ ≤ P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = _ := (one_mul _).symm
  have S := h.lem_ends.add (e3.add (e4.add (((e5.const_mul 2).add (e6.const_mul 2)).add
    ((e7.const_mul 2).add e8))))
  refine S.congr_left ?_
  filter_upwards [h.Msplit] with T hM
  rw [hM]; ring

omit h in
/-- The pointwise inequality behind [eq:tr2] (second form), with every quantity a real variable:
all analytic content is in the hypotheses, and the constants `ℓ₁² + L²/3` are checked here. -/
lemma tr2_pointwise (T L ℓ lT X E S I2 b G2 w CR Cμ Cu Cl : ℝ)
    (hT : 1 ≤ T) (hL : 1 ≤ L) (hl : 1 ≤ lT) (hlog : 1 ≤ Real.log lT) (hX : 1 ≤ X)
    (hℓl : lT ≤ ℓ) (hLl : L ≤ lT) (hw : 1 ≤ w) (hL2w : 2 * w ≤ L) (hb1 : 1 - 2 * w / L ≤ b) (hble1 : b ≤ 1)
    (hE0 : 0 ≤ E) (hEw : w / L ≤ E) (hEmid : (lT ^ 2 + X) * Real.log lT / (T * lT) ≤ E)
    (hCR : 0 ≤ CR) (hCμ : 0 ≤ Cμ) (hCu : 0 ≤ Cu) (hCl : 0 ≤ Cl)
    (hR : |G2 - (2 * π * b * L * I2 + T / π * S)| ≤ CR * (L * lT * Real.log lT * (lT ^ 2 + X)))
    (hμ : |I2 - T * ℓ ^ 2 / (4 * π ^ 2)| ≤ Cμ * (T * ℓ ^ 2 / (4 * π ^ 2) / lT ^ 2))
    (hSup : S - L ^ 3 / 6 ≤ Cu * L ^ 2) (hSlo : -(Cl * L ^ 2) ≤ S - (L - 2 * w) ^ 3 / 6) :
    |G2 - T * L / (2 * π) * (ℓ ^ 2 + L ^ 2 / 3)|
      ≤ (2 * π * CR + Cμ + 2 + 6 * (Cu + Cl + 2 * w)) * (E * (T * L / (2 * π) * (ℓ ^ 2 + L ^ 2 / 3))) := by
  have hπ : 0 < π := Real.pi_pos
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < L := by linarith
  have hl0 : 0 < lT := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hlog0 : 0 ≤ Real.log lT := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hw0 : 0 ≤ w := by linarith
  have hb0 : 0 ≤ b := by
    have : 2 * w / L ≤ 1 := by rw [div_le_one hL0]; linarith only [hL2w]
    linarith only [this, hb1]
  -- the main term and its two lower bounds
  set M₂ := T * L / (2 * π) * (ℓ ^ 2 + L ^ 2 / 3) with hM₂def
  have hM : M₂ = T * L * ℓ ^ 2 / (2 * π) + T * L ^ 3 / (6 * π) := by rw [hM₂def]; ring
  have hMa : T * L * ℓ ^ 2 / (2 * π) ≤ M₂ := by
    rw [hM]; linarith only [show 0 ≤ T * L ^ 3 / (6 * π) by positivity]
  have hMb : T * L ^ 3 / (6 * π) ≤ M₂ := by
    rw [hM]; linarith only [show 0 ≤ T * L * ℓ ^ 2 / (2 * π) by positivity]
  have hM0 : 0 ≤ M₂ := le_trans (by positivity) hMb
  have hEM0 : 0 ≤ E * M₂ := mul_nonneg hE0 hM0
  -- 1/L ≤ E and 1/l² ≤ E
  have hE_L : 1 / L ≤ E := le_trans (by gcongr) hEw
  have hE_l2 : 1 / lT ^ 2 ≤ E := by
    refine le_trans ?_ hE_L
    rw [div_le_div_iff₀ (by positivity) hL0, one_mul, one_mul]
    calc L ≤ lT := hLl
      _ = lT * 1 := (mul_one _).symm
      _ ≤ lT * lT := by gcongr
      _ = lT ^ 2 := (sq lT).symm
  -- Piece A: R ≤ 2π E M₂
  have hA : L * lT * Real.log lT * (lT ^ 2 + X) ≤ 2 * π * (E * M₂) := by
    have h1 : (lT ^ 2 + X) * Real.log lT / (T * lT) * (T * L * ℓ ^ 2 / (2 * π)) ≤ E * M₂ :=
      mul_le_mul hEmid hMa (by positivity) hE0
    have h2 : 2 * π * ((lT ^ 2 + X) * Real.log lT / (T * lT) * (T * L * ℓ ^ 2 / (2 * π)))
        = L * Real.log lT * (lT ^ 2 + X) * ℓ ^ 2 / lT := by
      field_simp
    have h3 : L * lT * Real.log lT * (lT ^ 2 + X) ≤ L * Real.log lT * (lT ^ 2 + X) * ℓ ^ 2 / lT := by
      rw [le_div_iff₀ hl0]
      have hll : lT * lT ≤ ℓ ^ 2 := by rw [sq]; exact mul_le_mul hℓl hℓl hl0.le hℓ0.le
      have h0 : 0 ≤ L * Real.log lT * (lT ^ 2 + X) := by positivity
      calc L * lT * Real.log lT * (lT ^ 2 + X) * lT = L * Real.log lT * (lT ^ 2 + X) * (lT * lT) := by
            ring
        _ ≤ L * Real.log lT * (lT ^ 2 + X) * ℓ ^ 2 := by gcongr
    calc L * lT * Real.log lT * (lT ^ 2 + X)
        ≤ L * Real.log lT * (lT ^ 2 + X) * ℓ ^ 2 / lT := h3
      _ = 2 * π * ((lT ^ 2 + X) * Real.log lT / (T * lT) * (T * L * ℓ ^ 2 / (2 * π))) := h2.symm
      _ ≤ 2 * π * (E * M₂) := by gcongr
  -- Piece B1: |2π b L (I2 − Tℓ²/(4π²))| ≤ Cμ E M₂
  have hB1 : |2 * π * b * L * (I2 - T * ℓ ^ 2 / (4 * π ^ 2))| ≤ Cμ * (E * M₂) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * π * b * L)]
    calc 2 * π * b * L * |I2 - T * ℓ ^ 2 / (4 * π ^ 2)|
        ≤ 2 * π * 1 * L * (Cμ * (T * ℓ ^ 2 / (4 * π ^ 2) / lT ^ 2)) := by gcongr
      _ = Cμ * ((1 / lT ^ 2) * (T * L * ℓ ^ 2 / (2 * π))) := by field_simp; ring
      _ ≤ Cμ * (E * M₂) := by gcongr
  -- Piece B2: |(b − 1) T L ℓ²/(2π)| ≤ 2 E M₂
  have hB2 : |(b - 1) * (T * L * ℓ ^ 2 / (2 * π))| ≤ 2 * (E * M₂) := by
    rw [abs_mul, abs_of_nonpos (by linarith only [hble1]), abs_of_nonneg (by positivity)]
    calc -(b - 1) * (T * L * ℓ ^ 2 / (2 * π)) ≤ (2 * w / L) * M₂ := by
          apply mul_le_mul (by linarith only [hb1]) hMa (by positivity) (by positivity)
      _ = 2 * ((w / L) * M₂) := by ring
      _ ≤ 2 * (E * M₂) := by gcongr
  -- Piece B3: |T/π (S − L³/6)| ≤ 6 (Cu + Cl + 2w) E M₂
  have hSlo' : -((Cl + 2 * w) * L ^ 2) ≤ S - L ^ 3 / 6 := by
    have h2 : -(2 * w * L ^ 2) ≤ (L - 2 * w) ^ 3 / 6 - L ^ 3 / 6 := by
      have e : (L - 2 * w) ^ 3 / 6 - L ^ 3 / 6 - (-(2 * w * L ^ 2))
          = w * (L ^ 2 - (4 / 3) * w ^ 2 + 2 * w * L) := by ring
      have hsq : (2 * w) * (2 * w) ≤ L * L := mul_le_mul hL2w hL2w (by linarith only [hw0]) hL0.le
      have : 0 ≤ w * (L ^ 2 - (4 / 3) * w ^ 2 + 2 * w * L) :=
        mul_nonneg hw0 (by linarith only [hsq, mul_nonneg hw0 hL0.le, sq_nonneg w])
      linarith only [e, this]
    linarith only [h2, hSlo]
  have hB3 : |T / π * (S - L ^ 3 / 6)| ≤ 6 * (Cu + Cl + 2 * w) * (E * M₂) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ T / π)]
    have hS : |S - L ^ 3 / 6| ≤ (Cu + Cl + 2 * w) * L ^ 2 := by
      rw [abs_le]
      constructor <;> linarith only [hSlo', hSup, mul_nonneg hCu (sq_nonneg L),
        mul_nonneg hCl (sq_nonneg L), mul_nonneg hw0 (sq_nonneg L)]
    calc T / π * |S - L ^ 3 / 6| ≤ T / π * ((Cu + Cl + 2 * w) * L ^ 2) := by gcongr
      _ = 6 * (Cu + Cl + 2 * w) * ((1 / L) * (T * L ^ 3 / (6 * π))) := by
          field_simp
      _ ≤ 6 * (Cu + Cl + 2 * w) * (E * M₂) := by gcongr
  -- assemble
  have hsplit : (2 * π * b * L * I2 + T / π * S) - M₂
      = 2 * π * b * L * (I2 - T * ℓ ^ 2 / (4 * π ^ 2)) + (b - 1) * (T * L * ℓ ^ 2 / (2 * π))
        + T / π * (S - L ^ 3 / 6) := by
    rw [hM]; field_simp; ring
  calc |G2 - M₂|
      ≤ |G2 - (2 * π * b * L * I2 + T / π * S)| + |(2 * π * b * L * I2 + T / π * S) - M₂| :=
        abs_sub_le _ _ _
    _ ≤ CR * (L * lT * Real.log lT * (lT ^ 2 + X))
        + (|2 * π * b * L * (I2 - T * ℓ ^ 2 / (4 * π ^ 2))| + |(b - 1) * (T * L * ℓ ^ 2 / (2 * π))|
          + |T / π * (S - L ^ 3 / 6)|) := by
        gcongr
        rw [hsplit]; exact abs_add_three _ _ _
    _ ≤ CR * (2 * π * (E * M₂)) + (Cμ * (E * M₂) + 2 * (E * M₂)
          + 6 * (Cu + Cl + 2 * w) * (E * M₂)) := by gcongr
    _ = (2 * π * CR + Cμ + 2 + 6 * (Cu + Cl + 2 * w)) * (E * M₂) := by ring

/-- [eq:tr2], second form: `tr G̃² = (T L/2π)(ℓ₁² + L²/3)(1 + O(𝓔_T))`. -/
theorem tr2 : EvBound (fun T => D.trG2 T - P.mainTr2 T) (fun T => P.calE T * P.mainTr2 T) := by
  have hlam := h.lam_pos
  have hw1 := h.one_le_w
  have hw : 0 ≤ P.w := by linarith
  obtain ⟨CR, hCR, hR⟩ := (tr2_first h).eventually_le
  obtain ⟨Cμ, hCμ, hμ⟩ := h.muints2.eventually_le
  obtain ⟨Cu, hCu, hu⟩ := h.sum_upper.eventually_le
  obtain ⟨Cl, hCl, hlo⟩ := h.sum_lower.eventually_le
  refine EvBound.of_eventually_le
    (c := 2 * π * CR + Cμ + 2 + 6 * (Cu + Cl + 2 * P.w)) (by positivity) ?_
  filter_upwards [hR, hμ, hu, hlo, h.abdef, regime h, calE_ge_w_div_L hlam hw,
    calE_ge_mid hlam hw, calE_nonneg_eventually hlam hw, eventually_L_ge P hlam (2 * P.w)]
    with T hR hμ hu hlo hab hreg hEw hEmid hE0 hL2w
  obtain ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩ := hreg
  obtain ⟨hb1, hba, ha1⟩ := hab
  have hSup : D.sumL2g T - P.L T ^ 3 / 6 ≤ Cu * P.L T ^ 2 := by
    rw [abs_of_nonneg (le_max_right _ _)] at hu
    exact (le_max_left _ _).trans hu
  have hSlo : -(Cl * P.L T ^ 2) ≤ D.sumL2g T - (P.L T - 2 * P.w) ^ 3 / 6 :=
    (abs_le.mp hlo).1.trans (min_le_left _ _)
  exact tr2_pointwise T (P.L T) (ell1 T) (l T) (P.X T) (P.calE T) (D.sumL2g T) (D.intMu2 T)
    (D.bT T) (D.trG2 T) P.w CR Cμ Cu Cl hT hL hl hlog hX (l_le_ell1 T) hLl hw1 hL2w hb1 (hba.trans ha1)
    hE0 hEw hEmid hCR.le hCμ.le hCu.le hCl.le hR hμ hSup hSlo

omit h in
/-- The pointwise inequality behind [eq:ratio], every quantity a real variable.  Here
`Φ₀ := F(L/ℓ)·N` and the identity `F(λ₁) N · (TL/2π)(ℓ² + L²/3) = L² N · Tℓ/2π` is where the
paper's `F(λ₁)`, `λ₁ = L/ℓ₁`, is checked. -/
lemma ratio_pointwise (T L ℓ lT E N G G2 A C₁ C₂ : ℝ)
    (hT : 1 ≤ T) (hL : 0 < L) (hℓ1 : 1 ≤ ℓ) (hℓl : lT ≤ ℓ) (hN0 : 0 < N) (hE0 : 0 ≤ E)
    (hET : 1 / T ≤ E) (hA : 0 ≤ A) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hs1 : C₁ * E ≤ 1 / 2) (hs2 : C₂ * E ≤ 1 / 2) (hTA : 2 * π * A ≤ T)
    (h1 : |G - L * N| ≤ C₁ * (E * (L * N)))
    (h2 : |G2 - T * L / (2 * π) * (ℓ ^ 2 + L ^ 2 / 3)| ≤ C₂ * (E * (T * L / (2 * π) * (ℓ ^ 2 + L ^ 2 / 3))))
    (hN : |N - T * ℓ / (2 * π)| ≤ A * lT) :
    |G ^ 2 / G2 - Ffun (L / ℓ) * N| ≤ 2 * (2 * π * A + 5 * C₁ + C₂) * (E * (Ffun (L / ℓ) * N)) := by
  have hπ : 0 < π := Real.pi_pos
  have hT0 : 0 < T := by linarith only [hT]
  have hℓ0 : 0 < ℓ := by linarith only [hℓ1]
  set M₂ := T * L / (2 * π) * (ℓ ^ 2 + L ^ 2 / 3) with hM₂def
  have hM0 : 0 < M₂ := by positivity
  set Φ₀ := Ffun (L / ℓ) * N with hΦ₀def
  have hF0 : 0 < Ffun (L / ℓ) := by unfold Ffun; positivity
  have hΦ0 : 0 < Φ₀ := mul_pos hF0 hN0
  have key : Φ₀ * M₂ = L ^ 2 * N * (T * ℓ / (2 * π)) := by
    simp only [hΦ₀def, hM₂def, Ffun]
    field_simp
  set a := G - L * N with hadef
  set bb := G2 - M₂ with hbbdef
  set δ := N - T * ℓ / (2 * π) with hδdef
  have hbb : |bb| ≤ C₂ * (E * M₂) := h2
  have hG2low : M₂ / 2 ≤ G2 := by
    have : -(C₂ * (E * M₂)) ≤ bb := (abs_le.mp hbb).1
    have : C₂ * (E * M₂) ≤ 1 / 2 * M₂ := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hs2 hM0.le
    linarith only [‹-(C₂ * (E * M₂)) ≤ bb›, this, hbbdef]
  have hG2pos : 0 < G2 := lt_of_lt_of_le (by positivity) hG2low
  -- the algebraic identity
  have hid : G ^ 2 - Φ₀ * G2 = L ^ 2 * N * δ + 2 * (L * N) * a + a ^ 2 - Φ₀ * bb := by
    have hG : G = L * N + a := by rw [hadef]; ring
    have hG2 : G2 = M₂ + bb := by rw [hbbdef]; ring
    rw [hG, hG2, hδdef]
    linear_combination (-1 : ℝ) * key
  -- (L N)² ≤ 2 Φ₀ M₂
  have hLN0 : 0 ≤ L * N := by positivity
  have hNup : N ≤ T * ℓ / (2 * π) + A * ℓ := by
    have := (abs_le.mp hN).2
    nlinarith only [this, hℓl, hA]
  have hLN2 : (L * N) ^ 2 ≤ 2 * (Φ₀ * M₂) := by
    rw [key]
    have h' : (L * N) ^ 2 = L ^ 2 * N * N := by ring
    rw [h']
    have hc : L ^ 2 * N * N ≤ L ^ 2 * N * (T * ℓ / (2 * π) + A * ℓ) :=
      mul_le_mul_of_nonneg_left hNup (by positivity)
    have hd : L ^ 2 * N * (A * ℓ) ≤ L ^ 2 * N * (T * ℓ / (2 * π)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [le_div_iff₀ (by positivity)]
      nlinarith only [hTA, hℓ0, hA]
    nlinarith only [hc, hd]
  -- the four bounds
  have t1 : |L ^ 2 * N * δ| ≤ 2 * π * A * (E * (Φ₀ * M₂)) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ L ^ 2 * N)]
    calc L ^ 2 * N * |δ| ≤ L ^ 2 * N * (A * ℓ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hN.trans (mul_le_mul_of_nonneg_left hℓl hA)
      _ = 2 * π * A * ((1 / T) * (Φ₀ * M₂)) := by rw [key]; field_simp
      _ ≤ 2 * π * A * (E * (Φ₀ * M₂)) := by gcongr
  have t2 : |2 * (L * N) * a| ≤ 4 * C₁ * (E * (Φ₀ * M₂)) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * (L * N))]
    calc 2 * (L * N) * |a| ≤ 2 * (L * N) * (C₁ * (E * (L * N))) := by gcongr
      _ = 2 * C₁ * E * (L * N) ^ 2 := by ring
      _ ≤ 2 * C₁ * E * (2 * (Φ₀ * M₂)) := by gcongr
      _ = 4 * C₁ * (E * (Φ₀ * M₂)) := by ring
  have t3 : |a ^ 2| ≤ C₁ * (E * (Φ₀ * M₂)) := by
    rw [abs_pow]
    calc |a| ^ 2 ≤ (C₁ * (E * (L * N))) ^ 2 := by gcongr
      _ = (C₁ * E) * (C₁ * E) * (L * N) ^ 2 := by ring
      _ ≤ (C₁ * E) * (1 / 2) * (2 * (Φ₀ * M₂)) := by gcongr
      _ = C₁ * (E * (Φ₀ * M₂)) := by ring
  have t4 : |Φ₀ * bb| ≤ C₂ * (E * (Φ₀ * M₂)) := by
    rw [abs_mul, abs_of_pos hΦ0]
    calc Φ₀ * |bb| ≤ Φ₀ * (C₂ * (E * M₂)) := by gcongr
      _ = C₂ * (E * (Φ₀ * M₂)) := by ring
  have hnum : |G ^ 2 - Φ₀ * G2| ≤ (2 * π * A + 5 * C₁ + C₂) * (E * (Φ₀ * M₂)) := by
    rw [hid]
    calc |L ^ 2 * N * δ + 2 * (L * N) * a + a ^ 2 - Φ₀ * bb|
        ≤ |L ^ 2 * N * δ| + |2 * (L * N) * a| + |a ^ 2| + |Φ₀ * bb| := by
          refine (abs_sub _ _).trans ?_
          linarith only [abs_add_three (L ^ 2 * N * δ) (2 * (L * N) * a) (a ^ 2)]
      _ ≤ 2 * π * A * (E * (Φ₀ * M₂)) + 4 * C₁ * (E * (Φ₀ * M₂)) + C₁ * (E * (Φ₀ * M₂))
          + C₂ * (E * (Φ₀ * M₂)) := by gcongr
      _ = (2 * π * A + 5 * C₁ + C₂) * (E * (Φ₀ * M₂)) := by ring
  -- divide by G2 ≥ M₂/2
  have hq : G ^ 2 / G2 - Φ₀ = (G ^ 2 - Φ₀ * G2) / G2 := by
    field_simp
  rw [hq, abs_div, abs_of_pos hG2pos, div_le_iff₀ hG2pos]
  calc |G ^ 2 - Φ₀ * G2| ≤ (2 * π * A + 5 * C₁ + C₂) * (E * (Φ₀ * M₂)) := hnum
    _ = 2 * (2 * π * A + 5 * C₁ + C₂) * (E * Φ₀) * (M₂ / 2) := by ring
    _ ≤ 2 * (2 * π * A + 5 * C₁ + C₂) * (E * Φ₀) * G2 := by gcongr

/-- [eq:ratio]: `(tr G̃)²/tr G̃² = F(λ₁) N(T,2T)(1 + O(𝓔_T))`, `λ₁ = L/ℓ₁`. -/
theorem ratio : EvBound (fun T => D.trG T ^ 2 / D.trG2 T - Ffun (P.lam1 T) * D.Ncnt T)
    (fun T => P.calE T * (Ffun (P.lam1 T) * D.Ncnt T)) := by
  have hlam := h.lam_pos
  have hlam1 := h.lam_le_one
  have hw : 0 ≤ P.w := by linarith [h.one_le_w]
  obtain ⟨C₁, hC₁, h1⟩ := (tr1' h).eventually_le
  obtain ⟨C₂, hC₂, h2⟩ := (tr2 h).eventually_le
  obtain ⟨A, hA, hN⟩ := h.rvm.eventually_le
  have hcal := calE_tendsto_zero hlam hlam1 hw
  have hs1 : ∀ᶠ T in atTop, C₁ * P.calE T ≤ 1 / 2 := by
    filter_upwards [hcal.eventually (Iio_mem_nhds (show (0:ℝ) < 1 / (2 * C₁) by positivity))]
      with T hT
    rw [lt_div_iff₀ (by positivity)] at hT
    linarith
  have hs2 : ∀ᶠ T in atTop, C₂ * P.calE T ≤ 1 / 2 := by
    filter_upwards [hcal.eventually (Iio_mem_nhds (show (0:ℝ) < 1 / (2 * C₂) by positivity))]
      with T hT
    rw [lt_div_iff₀ (by positivity)] at hT
    linarith
  refine EvBound.of_eventually_le (c := 2 * (2 * π * A + 5 * C₁ + C₂)) (by positivity) ?_
  filter_upwards [h1, h2, hN, hs1, hs2, regime h, calE_ge_rpow hlam hw,
    calE_nonneg_eventually hlam hw, Ncnt_pos h, eventually_ge_atTop (2 * π * A)]
    with T h1 h2 hN hs1 hs2 hreg hEr hE0 hN0 hTA
  obtain ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩ := hreg
  have hET : 1 / T ≤ P.calE T := by
    refine le_trans ?_ hEr
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  exact ratio_pointwise T (P.L T) (ell1 T) (l T) (P.calE T) (D.Ncnt T) (D.trG T) (D.trG2 T)
    A C₁ C₂ hT (by linarith) (hl.trans (l_le_ell1 T)) (l_le_ell1 T) hN0 hE0 hET hA.le hC₁.le
    hC₂.le hs1 hs2 hTA h1 h2 hN

/-- **Theorem [thm:traces]** (§5 of the paper, "Summary"), assembled: the content
`TracesBounds` holds for the data `D` under `Facts D`. -/
theorem tracesBounds_of_facts : TracesBounds P D.aT D.trG D.trG2 D.Ncnt where
  tr1 := tr1 h
  tr1' := tr1' h
  tr2 := tr2 h
  ratio := ratio h

end assembly

end PrimeSide

/-! ## §3.  [prop:PP]

Statement over `Mform` and `Defs.lean`'s `PX, PhiR, g`,
via the 𝒟 / 𝒪₁ / 𝒪₂ decomposition [eq:MPP]. -/

end Zeta23

end
