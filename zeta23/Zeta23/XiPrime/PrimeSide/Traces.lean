/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization.

Zeta23/XiPrime/PrimeSide/Traces.lean — ξ′ component, generalised-coefficient prime side: the output package
TracesBoundsXi and the ABSTRACT assembly FactsXi → TracesBoundsXi.

Mirror of Zeta23/ThmD/Traces.lean (DataD/FactsD → TracesBoundsD, the window-general [thm:traces])
with three changes, all forced by what XiPrime/Coeff.lean can deliver:
 * the §5 remainders carry the CRUDE coefficient majorants (Lemma 7.1(iii), Remark 7.2):
   prop_trace O(L√X·l), lem_ends O(L·l³·log l·(1+X)), prop_PP O(L·l²·X), cross_muP O(L·l²·√X),
   cross_PPi O(L·X·l) — each larger than the ζ shape by a power of l, each still o(main) at fixed
   λ < 1 because it sits behind X/T or √X/T;
 * the partial-summation field sumJ is in ε-form (the diagonal law Lemma 7.1(i) is
   "+ o(l²)"): Σ_N |c_N|²/N·g(log N) = (L³/2)·J_T + o(l²·L);
 * consequently the conclusions are Asymptotics.IsEquivalent statements (rate-free), proved with
   Mathlib's ~[atTop] algebra (mul/div/pow) instead of explicit-constant pointwise lemmas.
Everything here is about abstract real functions of T; no integrals, no coefficients.
-/
import Zeta23.ThmD.AssemblyD
import Zeta23.PrimeSideB
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

noncomputable section

open Real Filter Topology Asymptotics

namespace Zeta23
namespace XiPrime

open PaperParams PrimeSide

/-! ## The moment functional and the output package -/

/-- The window × density moment `J_T := (2/L³) · l · ∫_0^L D(y/l) g(y) dy`
(for `D(s) = s` this is ThmD's `J_T = (2/L³) ∫_0^L g(y) y dy` of [eq:abJ]; its T-limit for the window with
profile `v` is `jWin D λ v / λ`, XiPrime/Window.lean). -/
def JD (D g : ℝ → ℝ) (L l : ℝ) : ℝ := 2 / L ^ 3 * l * ∫ y in (0:ℝ)..L, (D (y / l) * g y)

/-- the second-trace main term `(TL/2π)(b ℓ₁² + L² J)` ([eq:ratio-general]; [XF′] Thm 8.1's `‖G̃‖²_F`). -/
def mainTr2Xi (P : Params) (bT JT : ℝ → ℝ) (T : ℝ) : ℝ :=
  T * P.L T / (2 * π) * (bT T * ell1 T ^ 2 + P.L T ^ 2 * JT T)

/-- **The ξ′ trace package** (mirror of `Zeta23.ThmD.TracesBoundsD` in rate-free form).  `aT, bT` are the
taper moments `L⁻¹∫φ², L⁻¹∫φ⁴`, `JT` the moment `JD D g_T (P.L T) (l T)`, `trG, trG2` the two prime-side
traces of `M̃ᵀ = Mᵀ/L`, and `Ncnt` any count with `Ncnt = T ℓ₁/2π + O(l)` (ξ′: N_{ξ′}(T,2T)). -/
structure TracesBoundsXi (P : Params) (aT bT JT trG trG2 Ncnt : ℝ → ℝ) : Prop where
  /-- [eq:tr1]': `tr G̃ ~ a L N` — [XF′] Thm 8.1 `tr Ĝ = N(1 + o(1))`. -/
  tr1' : trG ~[atTop] (fun T => aT T * P.L T * Ncnt T)
  /-- [eq:tr2]: `tr G̃² ~ (TL/2π)(b ℓ₁² + L² J_T)` — [XF′] Thm 8.1's `‖Ĝ‖²_F = (N/c)(1 + o(1))` before
  normalisation. -/
  tr2 : trG2 ~[atTop] mainTr2Xi P bT JT
  /-- [eq:ratio-general]: `(tr G̃)²/tr G̃² ~ cRatio(λ₁; a, b, J_T) · N`. -/
  ratio : (fun T => trG T ^ 2 / trG2 T)
    ~[atTop] (fun T => ThmD.cRatio (P.lam1 T) (aT T) (bT T) (JT T) * Ncnt T)
  /-- hat-units second moment: `tr G̃²/(aL)² ~ cRatio(λ₁; a, b, J_T)⁻¹ · N` (`= ‖M̂ᵀ‖²_F`). -/
  frhat : (fun T => trG2 T / (aT T * P.L T) ^ 2)
    ~[atTop] (fun T => (ThmD.cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹ * Ncnt T)

/-! ## Little-o glue -/

/-- domination by a vanishing multiple gives little-o: |g| ≤ E·h eventually with E → 0. -/
lemma isLittleO_of_le_mul {g h E : ℝ → ℝ} (hE : Tendsto E atTop (𝓝 0))
    (hle : ∀ᶠ T in atTop, |g T| ≤ E T * h T) : g =o[atTop] h := by
  have h1 : g =O[atTop] (fun T => E T * h T) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hle] with T hT
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
    exact hT.trans (le_abs_self _)
  have h2 : (fun T => E T * h T) =o[atTop] h := by
    have := ((isLittleO_one_iff ℝ).2 hE).mul_isBigO (isBigO_refl h atTop)
    exact this.congr_right fun T => by simp
  exact h1.trans_isLittleO h2

/-- an EvBound whose majorant is dominated by a vanishing multiple of h is little-o of h. -/
lemma evBound_isLittleO_of_le_mul {f g h E : ℝ → ℝ} (hf : EvBound f g)
    (hE : Tendsto E atTop (𝓝 0)) (hle : ∀ᶠ T in atTop, g T ≤ E T * h T) : f =o[atTop] h := by
  obtain ⟨C, hC, hfC⟩ := hf.eventually_le
  refine isLittleO_of_le_mul (E := fun T => C * E T) (by simpa using hE.const_mul C) ?_
  filter_upwards [hfC, hle] with T h1 h2
  calc |f T| ≤ C * g T := h1
    _ ≤ C * (E T * h T) := mul_le_mul_of_nonneg_left h2 hC.le
    _ = C * E T * h T := by ring

/-- two-sided δ-form of an asymptotic equivalence with an eventually nonnegative right side. -/
lemma eventually_abs_sub_le_of_isEquivalent {u v : ℝ → ℝ} (h : u ~[atTop] v)
    (hv : ∀ᶠ T in atTop, 0 ≤ v T) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T in atTop, |u T - v T| ≤ δ * v T := by
  have := h.isLittleO.def hδ
  filter_upwards [this, hv] with T h1 h2
  simpa [Real.norm_eq_abs, abs_of_nonneg h2] using h1

/-! ## The scalar rates -/

section Rates
variable (P : Params)

/-- `l² X / T → 0` for `0 < λ < 1` (the one place `λ < 1` strictly is used: `X = (T/2π)^λ`). -/
lemma tendsto_l_sq_mul_X_div (hlam0 : 0 < P.lam) (hlam1 : P.lam < 1) :
    Tendsto (fun T => l T ^ 2 * P.X T / T) atTop (𝓝 0) := by
  have hs : 0 < (1 - P.lam) / 2 := by linarith
  -- (log T)² ≤ T^{(1-λ)/2} eventually
  have hlog : ∀ᶠ T : ℝ in atTop, Real.log T ^ 2 ≤ T ^ ((1 - P.lam) / 2) := by
    have := (isLittleO_log_rpow_rpow_atTop 2 hs).bound (show (0:ℝ) < 1 by norm_num)
    filter_upwards [this, eventually_ge_atTop (1:ℝ)] with T hT hT1
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_two,
      abs_of_nonneg (sq_nonneg _), abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hT
    exact hT
  have hlim : Tendsto (fun T : ℝ => T ^ ((P.lam - 1) / 2)) atTop (𝓝 0) := by
    have : (P.lam - 1) / 2 = -((1 - P.lam) / 2) := by ring
    rw [this]; exact tendsto_rpow_neg_atTop hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    exact div_nonneg (mul_nonneg (sq_nonneg _) (X_pos P T).le) hT.le
  · filter_upwards [hlog, eventually_ge_atTop (2 * π), eventually_l_ge 0] with T hlogT hT hl0
    have hπ := Real.pi_gt_three
    have hT0 : 0 < T := by linarith
    have hl : l T ≤ Real.log T := by
      unfold l
      rw [Real.log_div hT0.ne' (by positivity)]
      have : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith)
      linarith
    have hX : P.X T ≤ T ^ P.lam := by
      rw [X_eq_rpow P hT0]
      exact Real.rpow_le_rpow (by positivity) (by rw [div_le_iff₀ (by positivity)]; nlinarith)
        hlam0.le
    have hX0 : 0 ≤ P.X T := (X_pos P T).le
    calc l T ^ 2 * P.X T / T ≤ Real.log T ^ 2 * T ^ P.lam / T := by
          gcongr
      _ ≤ T ^ ((1 - P.lam) / 2) * T ^ P.lam / T := by gcongr
      _ = T ^ ((P.lam - 1) / 2) := by
          rw [← Real.rpow_add hT0, div_eq_iff hT0.ne', ← Real.rpow_add_one hT0.ne']
          congr 1; ring

/-- `T^{λ/2 − 1} → 0` (λ < 2). -/
lemma tendsto_rpow_half_lam_sub_one (hlam : P.lam < 2) :
    Tendsto (fun T : ℝ => T ^ (P.lam / 2 - 1)) atTop (𝓝 0) := by
  have : P.lam / 2 - 1 = -(1 - P.lam / 2) := by ring
  rw [this]; exact tendsto_rpow_neg_atTop (by linarith)

/-- `1/l² → 0`. -/
lemma tendsto_inv_l_sq : Tendsto (fun T => (l T ^ 2)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero |>.comp l_tendsto_atTop)

/-- `1/T → 0` along atTop (named for uniformity). -/
lemma tendsto_inv_T : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero

end Rates

/-! ## Data and hypotheses of the abstract assembly -/

/-- the abstract real functions of T entering the ξ′ two-trace computation (mirror of
`PrimeSide.Data` + ThmD's `JT`; the pole weight `cΠ` is absorbed into the Π-cross data). -/
structure DataXi (P : Params) where
  /-- `a := L⁻¹ ∫ φ²` -/
  aT : ℝ → ℝ
  /-- `b := L⁻¹ ∫ φ⁴` -/
  bT : ℝ → ℝ
  /-- `J_T := (2/L³)·l·∫_0^L D(y/l) g(y) dy` -/
  JT : ℝ → ℝ
  /-- `tr M̃ᵀ` -/
  trG : ℝ → ℝ
  /-- `tr (M̃ᵀ)²` -/
  trG2 : ℝ → ℝ
  /-- the count `N` (any, with `N = Tℓ₁/2π + O(l)`) -/
  Ncnt : ℝ → ℝ
  /-- `𝓜 = 𝓜[ν, ν]` -/
  Mtot : ℝ → ℝ
  /-- `𝓜[μ, μ]` -/
  Mmumu : ℝ → ℝ
  /-- `𝓜[P_c, P_c]` -/
  MPP : ℝ → ℝ
  /-- `𝓜[μ, P_c]` -/
  MmuP : ℝ → ℝ
  /-- `cΠ·𝓜[μ, Π_X]` -/
  MmuPi : ℝ → ℝ
  /-- `cΠ·𝓜[P_c, Π_X]` -/
  MPPi : ℝ → ℝ
  /-- `cΠ²·𝓜[Π_X, Π_X]` -/
  MPiPi : ℝ → ℝ
  /-- `∫_T^{2T} μ²` -/
  intMu2 : ℝ → ℝ
  /-- the diagonal `Σ_{N≤X} |c_N|²/N · g(log N)` -/
  sumB2g : ℝ → ℝ

variable {P : Params} (D : DataXi P)

/-- the lem_ends-scale remainder `R_T := L·l³·log l·(1 + X)` that absorbs every first-form error. -/
def Rxi (P : Params) (T : ℝ) : ℝ := P.L T * l T ^ 3 * Real.log (l T) * (1 + P.X T)

/-- the comparison scale of the second trace: `M⋆ := T·L·l²` (`≤ 4π · mainTr2Xi`). -/
def Mstar (P : Params) (T : ℝ) : ℝ := T * P.L T * l T ^ 2

/-- **Hypotheses of the ξ′ two-trace assembly** = the §5 sub-results for the density
`ν = μ + cΠ·Π_X + P_c` with the crude coefficient majorants, + H-Γ's [eq:muints], + H-RvM-type count,
+ the window ranges.  Mirror of `ThmD.FactsD` (see the file header for the three changes). -/
structure FactsXi : Prop where
  lam_pos : 0 < P.lam
  lam_lt_one : P.lam < 1
  one_le_w : 1 ≤ P.w
  /-- window ranges [eq:abJ]: `1/2 ≤ b ≤ a ≤ 1`, `0 ≤ J_T` eventually. -/
  ab_range : ∀ᶠ T in atTop, 1 / 2 ≤ D.bT T ∧ D.bT T ≤ D.aT T ∧ D.aT T ≤ 1 ∧ 0 ≤ D.JT T
  /-- H-RvM-type: `N = T ℓ₁/2π + O(l)`. -/
  rvm : EvBound (fun T => D.Ncnt T - T * ell1 T / (2 * π)) l
  /-- [eq:muints]: `∫_T^{2T} μ² = (Tℓ₁²/4π²)(1 + O(l⁻²))`. -/
  muints2 : EvBound (fun T => D.intMu2 T - T * ell1 T ^ 2 / (4 * π ^ 2))
      (fun T => T * ell1 T ^ 2 / (4 * π ^ 2) / l T ^ 2)
  /-- [prop:trace] for ν: `tr G̃ = a L N + O(L √X · l)`. -/
  prop_trace : EvBound (fun T => D.trG T - D.aT T * P.L T * D.Ncnt T)
      (fun T => P.L T * Real.sqrt (P.X T) * l T)
  /-- [lem:ends] for ν (via lem_ends_nu with `B ≍ l(1+√X)`): `tr G̃² = 𝓜 + O(L l³ log l (1+X))`. -/
  lem_ends : EvBound (fun T => D.trG2 T - D.Mtot T) (Rxi P)
  /-- [eq:Msplit]: the bilinear expansion of `𝓜[ν,ν]`, `ν = μ + cΠ·Π_X + P_c`. -/
  Msplit : ∀ᶠ T in atTop, D.Mtot T =
      D.Mmumu T + D.MPP T + 2 * D.MmuP T + 2 * D.MmuPi T + 2 * D.MPPi T + D.MPiPi T
  /-- [prop:mumu] (coefficient-free, verbatim): `𝓜[μ,μ] = 2π b L ∫_T^{2T} μ² + O(l² log L)`. -/
  prop_mumu : EvBound (fun T => D.Mmumu T - 2 * π * D.bT T * P.L T * D.intMu2 T)
      (fun T => l T ^ 2 * Real.log (P.L T))
  /-- [prop:PP] for P_c: `𝓜[P_c,P_c] = (T/π) Σ |c_N|²/N g(log N) + O(L l² X)`. -/
  prop_PP : EvBound (fun T => D.MPP T - T / π * D.sumB2g T) (fun T => P.L T * l T ^ 2 * P.X T)
  /-- partial summation from the ε-form diagonal law: `Σ |c_N|²/N g(log N) = (L³/2) J_T + o(l² L)`. -/
  sumJ : ∀ ε : ℝ, 0 < ε → ∀ᶠ T in atTop,
      |D.sumB2g T - P.L T ^ 3 / 2 * D.JT T| ≤ ε * (l T ^ 2 * P.L T)
  /-- [prop:cross] for ν: `𝓜[μ,P_c] ≪ L l² √X`. -/
  cross_muP : EvBound D.MmuP (fun T => P.L T * l T ^ 2 * Real.sqrt (P.X T))
  /-- `cΠ·𝓜[μ,Π_X] ≪ l L √X` -/
  cross_muPi : EvBound D.MmuPi (fun T => l T * P.L T * Real.sqrt (P.X T))
  /-- `cΠ·𝓜[P_c,Π_X] ≪ L X l` -/
  cross_PPi : EvBound D.MPPi (fun T => P.L T * P.X T * l T)
  /-- `cΠ²·𝓜[Π_X,Π_X] ≪ L X / T` -/
  cross_PiPi : EvBound D.MPiPi (fun T => P.L T * P.X T / T)

/-! ## Two exact identities -/

/-- the exact identity behind [eq:ratio-general]:
`(aLN)²/M₂ = cRatio(L/ℓ; a,b,J)·N · (N / (Tℓ/2π))`, valid when `T, L, ℓ, b + λ₁²J` are nonzero. -/
private lemma ratio_identity (T L ℓ a b J N : ℝ) (hT : T ≠ 0) (hL : L ≠ 0) (hℓ : ℓ ≠ 0)
    (hden : b * ℓ ^ 2 + L ^ 2 * J ≠ 0) :
    (a * L * N) ^ 2 / (T * L / (2 * π) * (b * ℓ ^ 2 + L ^ 2 * J))
      = ThmD.cRatio (L / ℓ) a b J * N * (N / (T * ℓ / (2 * π))) := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_pos.ne'
  have hden' : b + (L / ℓ) ^ 2 * J ≠ 0 := by
    intro h0
    apply hden
    have : b * ℓ ^ 2 + L ^ 2 * J = (b + (L / ℓ) ^ 2 * J) * ℓ ^ 2 := by field_simp
    rw [this, h0, zero_mul]
  unfold ThmD.cRatio
  field_simp

/-- the exact identity behind the hat-units second moment:
`M₂/(aL)² = cRatio(L/ℓ; a,b,J)⁻¹ · (Tℓ/2π)`. -/
private lemma frhat_identity (T L ℓ a b J : ℝ) (hL : L ≠ 0) (hℓ : ℓ ≠ 0) (ha : a ≠ 0) :
    T * L / (2 * π) * (b * ℓ ^ 2 + L ^ 2 * J) / (a * L) ^ 2
      = (ThmD.cRatio (L / ℓ) a b J)⁻¹ * (T * ℓ / (2 * π)) := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_pos.ne'
  unfold ThmD.cRatio
  rw [inv_div]
  field_simp

/-! ## The assembly -/

section Assembly
variable {D} (h : FactsXi D)
include h

private lemma regime : ∀ᶠ T in atTop, 1 ≤ T ∧ 1 ≤ l T ∧ 1 ≤ Real.log (l T)
    ∧ 1 ≤ P.L T ∧ 1 ≤ P.X T ∧ P.L T ≤ l T ∧ P.X T ≤ T ∧ ell1 T ≤ 2 * l T := by
  have hlam := h.lam_pos
  filter_upwards [eventually_ge_atTop 1, eventually_l_ge 1, eventually_log_l_ge 1,
    eventually_L_ge P hlam 1, eventually_one_le_X P hlam,
    eventually_X_le_T P hlam h.lam_lt_one.le, eventually_ell1_le_two_l] with T h1 h2 h3 h4 h5 h6 h7
  exact ⟨h1, h2, h3, h4, h5, L_le_l P h.lam_lt_one.le (by linarith), h6, h7⟩

private lemma Ncnt_lower : ∀ᶠ T in atTop, T * l T / (4 * π) ≤ D.Ncnt T := by
  obtain ⟨A, hA, hN⟩ := h.rvm.eventually_le
  filter_upwards [hN, eventually_ge_atTop (4 * π * A), eventually_l_ge 0] with T hN hTA hl
  have hπ := Real.pi_pos
  have h1 : -(A * l T) ≤ D.Ncnt T - T * ell1 T / (2 * π) := (abs_le.mp hN).1
  have h2 : T * l T ≤ T * ell1 T := mul_le_mul_of_nonneg_left (l_le_ell1 T) (by nlinarith)
  have h3 : T * l T / (2 * π) ≤ T * ell1 T / (2 * π) :=
    div_le_div_of_nonneg_right h2 (by positivity)
  have h4 : T * l T / (4 * π) = T * l T / (2 * π) - T * l T / (4 * π) := by ring
  have h5 : A * l T ≤ T * l T / (4 * π) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  linarith

private lemma Ncnt_pos : ∀ᶠ T in atTop, 0 < D.Ncnt T := by
  filter_upwards [Ncnt_lower h, eventually_l_ge 1, eventually_ge_atTop 1] with T hN hl hT
  have hπ := Real.pi_pos
  have h0 : (0:ℝ) < T * l T / (4 * π) := by positivity
  linarith

/-- `N ~ T ℓ₁ / 2π`. -/
lemma isEquivalent_Ncnt : D.Ncnt ~[atTop] (fun T => T * ell1 T / (2 * π)) := by
  show (D.Ncnt - fun T => T * ell1 T / (2 * π)) =o[atTop] (fun T => T * ell1 T / (2 * π))
  refine evBound_isLittleO_of_le_mul (g := l) (E := fun T => 2 * π * T⁻¹) h.rvm
    (by simpa using tendsto_inv_T.const_mul (2 * π)) ?_
  filter_upwards [eventually_gt_atTop (0:ℝ), eventually_l_ge 0] with T hT hl
  have hπ := Real.pi_pos
  have : 2 * π * T⁻¹ * (T * ell1 T / (2 * π)) = ell1 T := by field_simp
  rw [this]
  exact l_le_ell1 T

/-- **[eq:tr1]'**: `tr G̃ ~ a L N`. -/
theorem tr1' : D.trG ~[atTop] (fun T => D.aT T * P.L T * D.Ncnt T) := by
  show (D.trG - fun T => D.aT T * P.L T * D.Ncnt T) =o[atTop] _
  have hlam := h.lam_pos
  refine evBound_isLittleO_of_le_mul (E := fun T => 8 * π * T ^ (P.lam / 2 - 1)) h.prop_trace
    (by simpa using (tendsto_rpow_half_lam_sub_one P (by linarith [h.lam_lt_one])).const_mul (8 * π)) ?_
  filter_upwards [regime h, Ncnt_lower h, h.ab_range] with T ⟨hT, hl, _u0, hL, _u1, _u2, _u3, _u4⟩ hN hab
  obtain ⟨hb2, hba, _u0, _u1⟩ := hab
  have hπ := Real.pi_pos
  have hT0 : 0 < T := by linarith
  have ha2 : 1 / 2 ≤ D.aT T := hb2.trans hba
  have hs : Real.sqrt (P.X T) ≤ T ^ (P.lam / 2 - 1) * T := by
    rw [rpow_half_sub_one_mul hT0]; exact sqrt_X_le_rpow P hlam hT0
  have hTl : T * l T ≤ 4 * π * D.Ncnt T := by
    rw [div_le_iff₀ (by positivity)] at hN; linarith
  calc P.L T * Real.sqrt (P.X T) * l T ≤ P.L T * (T ^ (P.lam / 2 - 1) * T) * l T := by gcongr
    _ = T ^ (P.lam / 2 - 1) * P.L T * (T * l T) := by ring
    _ ≤ T ^ (P.lam / 2 - 1) * P.L T * (4 * π * D.Ncnt T) := by gcongr
    _ = 8 * π * T ^ (P.lam / 2 - 1) * ((1 / 2) * P.L T * D.Ncnt T) := by ring
    _ ≤ 8 * π * T ^ (P.lam / 2 - 1) * (D.aT T * P.L T * D.Ncnt T) := by
        have : 0 ≤ D.Ncnt T := by
          have : (0:ℝ) ≤ T * l T / (4 * π) := by positivity
          linarith
        gcongr

/-- the first form of [eq:tr2]: all §5 remainders collected into `O(R_T)`. -/
private lemma tr2_first : EvBound
    (fun T => D.trG2 T - (2 * π * D.bT T * P.L T * D.intMu2 T + T / π * D.sumB2g T)) (Rxi P) := by
  -- each remainder is ≤ 1·R_T in the regime
  have dom : ∀ᶠ T in atTop,
      l T ^ 2 * Real.log (P.L T) ≤ 1 * Rxi P T ∧
      P.L T * l T ^ 2 * P.X T ≤ 1 * Rxi P T ∧
      P.L T * l T ^ 2 * Real.sqrt (P.X T) ≤ 1 * Rxi P T ∧
      l T * P.L T * Real.sqrt (P.X T) ≤ 1 * Rxi P T ∧
      P.L T * P.X T * l T ≤ 1 * Rxi P T ∧
      P.L T * P.X T / T ≤ 1 * Rxi P T := by
    filter_upwards [regime h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT, _u0⟩
    have hsX : Real.sqrt (P.X T) ≤ P.X T := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hlogL : Real.log (P.L T) ≤ Real.log (l T) := Real.log_le_log (by linarith) hLl
    have hR : Rxi P T = P.L T * l T ^ 3 * Real.log (l T) * (1 + P.X T) := rfl
    have hl2 : l T ^ 2 ≤ l T ^ 3 := by nlinarith
    have hl3 : l T ≤ l T ^ 3 := by nlinarith
    have h13 : (1:ℝ) ≤ l T ^ 3 := by nlinarith
    rw [one_mul, hR]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc l T ^ 2 * Real.log (P.L T) ≤ l T ^ 2 * Real.log (l T) := by
            gcongr
        _ = 1 * l T ^ 2 * Real.log (l T) * 1 := by ring
        _ ≤ P.L T * l T ^ 3 * Real.log (l T) * (1 + P.X T) := by gcongr <;> nlinarith
    · calc P.L T * l T ^ 2 * P.X T = P.L T * l T ^ 2 * 1 * P.X T := by ring
        _ ≤ P.L T * l T ^ 3 * Real.log (l T) * (1 + P.X T) := by gcongr <;> nlinarith
    · calc P.L T * l T ^ 2 * Real.sqrt (P.X T) ≤ P.L T * l T ^ 2 * P.X T := by gcongr
        _ = P.L T * l T ^ 2 * 1 * P.X T := by ring
        _ ≤ P.L T * l T ^ 3 * Real.log (l T) * (1 + P.X T) := by gcongr <;> nlinarith
    · calc l T * P.L T * Real.sqrt (P.X T) ≤ l T * P.L T * P.X T := by gcongr
        _ = P.L T * l T * 1 * P.X T := by ring
        _ ≤ P.L T * l T ^ 3 * Real.log (l T) * (1 + P.X T) := by gcongr <;> nlinarith
    · calc P.L T * P.X T * l T = P.L T * l T * 1 * P.X T := by ring
        _ ≤ P.L T * l T ^ 3 * Real.log (l T) * (1 + P.X T) := by gcongr <;> nlinarith
    · calc P.L T * P.X T / T ≤ P.L T * P.X T := div_le_self (by nlinarith) hT
        _ = P.L T * 1 * 1 * P.X T := by ring
        _ ≤ P.L T * l T ^ 3 * Real.log (l T) * (1 + P.X T) := by gcongr <;> nlinarith
  have e3 := h.prop_mumu.mono_right' one_pos (dom.mono fun T h => h.1)
  have e4 := h.prop_PP.mono_right' one_pos (dom.mono fun T h => h.2.1)
  have e5 := h.cross_muP.mono_right' one_pos (dom.mono fun T h => h.2.2.1)
  have e6 := h.cross_muPi.mono_right' one_pos (dom.mono fun T h => h.2.2.2.1)
  have e7 := h.cross_PPi.mono_right' one_pos (dom.mono fun T h => h.2.2.2.2.1)
  have e8 := h.cross_PiPi.mono_right' one_pos (dom.mono fun T h => h.2.2.2.2.2)
  have S := h.lem_ends.add (e3.add (e4.add (((e5.const_mul 2).add (e6.const_mul 2)).add
    ((e7.const_mul 2).add e8))))
  refine S.congr_left ?_
  filter_upwards [h.Msplit] with T hM
  rw [hM]; ring

/-- `M⋆ ≤ 4π · (TL/2π)(bℓ₁² + L²J)` and positivity of the main term, eventually. -/
private lemma Mstar_le : ∀ᶠ T in atTop,
    0 < Mstar P T ∧ Mstar P T ≤ 4 * π * mainTr2Xi P D.bT D.JT T := by
  filter_upwards [regime h, h.ab_range] with T ⟨hT, hl, _u0, hL, _u1, _u2, _u3, _u4⟩ ⟨hb2, _u5, _u6, hJ0⟩
  have hπ := Real.pi_pos
  have hℓ : l T ≤ ell1 T := l_le_ell1 T
  refine ⟨by unfold Mstar; positivity, ?_⟩
  unfold Mstar mainTr2Xi
  have h1 : 4 * π * (T * P.L T / (2 * π) * (D.bT T * ell1 T ^ 2 + P.L T ^ 2 * D.JT T))
      = 2 * T * P.L T * (D.bT T * ell1 T ^ 2 + P.L T ^ 2 * D.JT T) := by
    field_simp <;> ring
  rw [h1]
  have h2 : l T ^ 2 ≤ 2 * (D.bT T * ell1 T ^ 2 + P.L T ^ 2 * D.JT T) := by
    have : l T ^ 2 ≤ ell1 T ^ 2 := pow_le_pow_left₀ (by linarith) hℓ 2
    nlinarith [mul_nonneg (sq_nonneg (P.L T)) hJ0, sq_nonneg (ell1 T)]
  calc T * P.L T * l T ^ 2 ≤ T * P.L T * (2 * (D.bT T * ell1 T ^ 2 + P.L T ^ 2 * D.JT T)) := by
        gcongr
    _ = _ := by ring

/-- **[eq:tr2]**: `tr G̃² ~ (TL/2π)(b ℓ₁² + L² J_T)`. -/
theorem tr2 : D.trG2 ~[atTop] mainTr2Xi P D.bT D.JT := by
  have hlam := h.lam_pos
  -- (A) the collected §5 remainder is o(M⋆)
  have oA : (fun T => D.trG2 T - (2 * π * D.bT T * P.L T * D.intMu2 T + T / π * D.sumB2g T))
      =o[atTop] Mstar P := by
    refine evBound_isLittleO_of_le_mul (E := fun T => 2 * (l T ^ 2 * P.X T / T)) (tr2_first h)
      (by simpa using (tendsto_l_sq_mul_X_div P hlam h.lam_lt_one).const_mul 2) ?_
    filter_upwards [regime h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT, _u0⟩
    have hT0 : 0 < T := by linarith
    have hlogle : Real.log (l T) ≤ l T := Real.log_le_self (by linarith)
    unfold Rxi Mstar
    rw [show 2 * (l T ^ 2 * P.X T / T) * (T * P.L T * l T ^ 2)
        = P.L T * l T ^ 3 * l T * (2 * P.X T) by field_simp]
    gcongr <;> linarith
  -- (B) the μ-moment remainder is o(M⋆)
  have oB : (fun T => 2 * π * D.bT T * P.L T * (D.intMu2 T - T * ell1 T ^ 2 / (4 * π ^ 2)))
      =o[atTop] Mstar P := by
    obtain ⟨Cμ, hCμ, hμ⟩ := h.muints2.eventually_le
    refine isLittleO_of_le_mul (E := fun T => (2 * Cμ / π) * (l T ^ 2)⁻¹)
      (by simpa using tendsto_inv_l_sq.const_mul (2 * Cμ / π)) ?_
    filter_upwards [hμ, regime h, h.ab_range] with T hμ ⟨hT, hl, _u0, hL, _u1, _u2, _u3, hℓ2⟩
      ⟨hb2, hba, ha1, _u0⟩
    have hπ := Real.pi_pos
    have hb0 : 0 ≤ D.bT T := by linarith
    have hb1 : D.bT T ≤ 1 := hba.trans ha1
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * π * D.bT T * P.L T)]
    have hℓsq : ell1 T ^ 2 ≤ 4 * l T ^ 2 := by nlinarith [l_le_ell1 T]
    have hl0 : 0 < l T := by linarith
    calc 2 * π * D.bT T * P.L T * |D.intMu2 T - T * ell1 T ^ 2 / (4 * π ^ 2)|
        ≤ 2 * π * 1 * P.L T * (Cμ * (T * ell1 T ^ 2 / (4 * π ^ 2) / l T ^ 2)) := by gcongr
      _ = Cμ * T * P.L T * ell1 T ^ 2 / (2 * π * l T ^ 2) := by field_simp <;> ring
      _ ≤ Cμ * T * P.L T * (4 * l T ^ 2) / (2 * π * l T ^ 2) := by gcongr
      _ = (2 * Cμ / π) * (l T ^ 2)⁻¹ * Mstar P T := by unfold Mstar; field_simp <;> ring
  -- (C) the partial-summation remainder is o(M⋆), straight from the ε-form
  have oC : (fun T => T / π * (D.sumB2g T - P.L T ^ 3 / 2 * D.JT T)) =o[atTop] Mstar P := by
    rw [isLittleO_iff]
    intro c hc
    have hπ := Real.pi_pos
    filter_upwards [h.sumJ (c * π) (by positivity), eventually_gt_atTop (0:ℝ),
      Mstar_le h] with T hS hT ⟨hM0, _u0⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hM0, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ T / π)]
    calc T / π * |D.sumB2g T - P.L T ^ 3 / 2 * D.JT T| ≤ T / π * (c * π * (l T ^ 2 * P.L T)) := by
          gcongr
      _ = c * Mstar P T := by unfold Mstar; field_simp
  -- sum, and compare M⋆ with the main term
  have hsum := (oA.add oB).add oC
  have hbig : Mstar P =O[atTop] mainTr2Xi P D.bT D.JT := by
    refine IsBigO.of_bound (4 * π) ?_
    filter_upwards [Mstar_le h] with T ⟨h0, h1⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h0]
    exact h1.trans (by
      have : 0 ≤ 4 * π := by positivity
      nlinarith [le_abs_self (mainTr2Xi P D.bT D.JT T)])
  have key := hsum.trans_isBigO hbig
  show (D.trG2 - mainTr2Xi P D.bT D.JT) =o[atTop] mainTr2Xi P D.bT D.JT
  refine key.congr' (Eventually.of_forall fun T => ?_) EventuallyEq.rfl
  have hπ : (π : ℝ) ≠ 0 := Real.pi_pos.ne'
  simp only [Pi.sub_apply, mainTr2Xi]
  field_simp <;> ring

private lemma nonzeros : ∀ᶠ T in atTop, T ≠ 0 ∧ P.L T ≠ 0 ∧ ell1 T ≠ 0 ∧ D.aT T ≠ 0 ∧
    D.bT T * ell1 T ^ 2 + P.L T ^ 2 * D.JT T ≠ 0 ∧ T * ell1 T / (2 * π) ≠ 0 := by
  filter_upwards [regime h, h.ab_range] with T ⟨hT, hl, _u0, hL, _u1, _u2, _u3, _u4⟩ ⟨hb2, hba, _u5, hJ0⟩
  have hπ := Real.pi_pos
  have hℓ : 1 ≤ ell1 T := hl.trans (l_le_ell1 T)
  have hden : 0 < D.bT T * ell1 T ^ 2 + P.L T ^ 2 * D.JT T := by
    have : 0 < D.bT T * ell1 T ^ 2 := by positivity
    nlinarith [mul_nonneg (sq_nonneg (P.L T)) hJ0]
  exact ⟨by linarith, by linarith, by linarith, by linarith, hden.ne', by positivity⟩

/-- **[eq:ratio-general]**: `(tr G̃)²/tr G̃² ~ cRatio(λ₁; a, b, J_T) · N`. -/
theorem ratio : (fun T => D.trG T ^ 2 / D.trG2 T)
    ~[atTop] (fun T => ThmD.cRatio (P.lam1 T) (D.aT T) (D.bT T) (D.JT T) * D.Ncnt T) := by
  have h1 := tr1' h
  have h2 := tr2 h
  have hN := isEquivalent_Ncnt h
  -- trG²/trG2 ~ (aLN)²/M₂
  have hq : (fun T => D.trG T ^ 2 / D.trG2 T)
      ~[atTop] (fun T => (D.aT T * P.L T * D.Ncnt T) ^ 2 / mainTr2Xi P D.bT D.JT T) :=
    (h1.pow 2).div h2
  -- N/(Tℓ/2π) ~ 1
  have hone : (fun T => D.Ncnt T / (T * ell1 T / (2 * π))) ~[atTop] (fun _ => (1:ℝ)) := by
    refine (hN.div IsEquivalent.refl).congr_right ?_
    filter_upwards [nonzeros h] with T ⟨ _u0, _u1, _u2, _u3, _u4, h6⟩
    simp [div_self h6]
  have hmain : (fun T => ThmD.cRatio (P.lam1 T) (D.aT T) (D.bT T) (D.JT T) * D.Ncnt T
        * (D.Ncnt T / (T * ell1 T / (2 * π))))
      ~[atTop] (fun T => ThmD.cRatio (P.lam1 T) (D.aT T) (D.bT T) (D.JT T) * D.Ncnt T) := by
    exact ((IsEquivalent.refl
      (u := fun T => ThmD.cRatio (P.lam1 T) (D.aT T) (D.bT T) (D.JT T) * D.Ncnt T)
      (l := atTop)).mul hone).congr_left (Eventually.of_forall fun _ => rfl)
      |>.congr_right (Eventually.of_forall fun T => mul_one _)
  refine (hq.congr_right ?_).trans hmain
  filter_upwards [nonzeros h] with T ⟨hT, hL, hℓ, _u0, hden, _u1⟩
  simp only [mainTr2Xi, Params.lam1]
  exact ratio_identity T (P.L T) (ell1 T) (D.aT T) (D.bT T) (D.JT T) (D.Ncnt T) hT hL hℓ hden

/-- **hat-units second moment**: `tr G̃²/(aL)² ~ cRatio(λ₁; a, b, J_T)⁻¹ · N`. -/
theorem frhat : (fun T => D.trG2 T / (D.aT T * P.L T) ^ 2)
    ~[atTop] (fun T => (ThmD.cRatio (P.lam1 T) (D.aT T) (D.bT T) (D.JT T))⁻¹ * D.Ncnt T) := by
  have h2 := tr2 h
  have hN := isEquivalent_Ncnt h
  have hq : (fun T => D.trG2 T / (D.aT T * P.L T) ^ 2)
      ~[atTop] (fun T => mainTr2Xi P D.bT D.JT T / (D.aT T * P.L T) ^ 2) :=
    h2.div IsEquivalent.refl
  have hmain : (fun T => (ThmD.cRatio (P.lam1 T) (D.aT T) (D.bT T) (D.JT T))⁻¹
        * (T * ell1 T / (2 * π)))
      ~[atTop] (fun T => (ThmD.cRatio (P.lam1 T) (D.aT T) (D.bT T) (D.JT T))⁻¹ * D.Ncnt T) := by
    have := IsEquivalent.refl
      (u := fun T => (ThmD.cRatio (P.lam1 T) (D.aT T) (D.bT T) (D.JT T))⁻¹)
      (l := atTop) |>.mul hN.symm
    simpa [Pi.mul_def] using this
  refine (hq.congr_right ?_).trans hmain
  filter_upwards [nonzeros h] with T ⟨ _u0, hL, hℓ, ha, _u1, _u2⟩
  simp only [mainTr2Xi, Params.lam1]
  exact frhat_identity T (P.L T) (ell1 T) (D.aT T) (D.bT T) (D.JT T) hL hℓ ha

/-- **The ξ′ two-trace package, assembled** (statement declared in Interface.lean). -/
theorem tracesBoundsXi_of_factsXi : TracesBoundsXi P D.aT D.bT D.JT D.trG D.trG2 D.Ncnt where
  tr1' := tr1' h
  tr2 := tr2 h
  ratio := ratio h
  frhat := frhat h

end Assembly

/-! ## From the trace package to the δ-form hat-unit moments (the shape of `CoeffMoments`)

With `tr M̂ᵀ = tr G̃/(aL)` and `‖M̂ᵀ‖²_F = tr G̃²/(aL)²`, and the window limit `cRatio(λ₁; a_T, b_T, J_T) → c∞ > 0`
(XiPrime/Window.lean), the package gives: for every δ > 0, eventually
`(1−δ)N ≤ tr G̃/(aL) ≤ (1+δ)N` and `tr G̃²/(aL)² ≤ (c∞⁻¹ + δ) N`. -/

section Moments
variable {P : Params} {aT bT JT trG trG2 Ncnt : ℝ → ℝ}

theorem moments_trace (h : TracesBoundsXi P aT bT JT trG trG2 Ncnt)
    (hN0 : ∀ᶠ T in atTop, 0 ≤ Ncnt T) (haL : ∀ᶠ T in atTop, aT T * P.L T ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T in atTop, (1 - δ) * Ncnt T ≤ trG T / (aT T * P.L T) ∧
      trG T / (aT T * P.L T) ≤ (1 + δ) * Ncnt T := by
  have h1 : (fun T => trG T / (aT T * P.L T)) ~[atTop] Ncnt := by
    have := h.tr1'.div (IsEquivalent.refl (u := fun T => aT T * P.L T) (l := atTop))
    refine this.congr_right ?_
    filter_upwards [haL] with T hT
    simp only [Pi.div_apply]
    exact mul_div_cancel_left₀ _ hT
  filter_upwards [eventually_abs_sub_le_of_isEquivalent h1 hN0 hδ] with T hT
  constructor <;> nlinarith [(abs_le.mp hT).1, (abs_le.mp hT).2]

theorem moments_frob (h : TracesBoundsXi P aT bT JT trG trG2 Ncnt)
    (hN0 : ∀ᶠ T in atTop, 0 ≤ Ncnt T) {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => ThmD.cRatio (P.lam1 T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T in atTop, trG2 T / (aT T * P.L T) ^ 2 ≤ (c⁻¹ + δ) * Ncnt T := by
  -- cRatio⁻¹ · N ~ c⁻¹ · N
  have hinv : Tendsto (fun T => (ThmD.cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹) atTop
      (𝓝 c⁻¹) := hc.inv₀ hc0.ne'
  have hcc : (fun T => (ThmD.cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹)
      ~[atTop] (fun _ => c⁻¹) :=
    (isEquivalent_const_iff_tendsto (inv_ne_zero hc0.ne')).2 hinv
  have h1 : (fun T => trG2 T / (aT T * P.L T) ^ 2) ~[atTop] (fun T => c⁻¹ * Ncnt T) := by
    have := h.frhat.trans (hcc.mul (IsEquivalent.refl (u := Ncnt) (l := atTop)))
    simpa [Pi.mul_def] using this
  have hv : ∀ᶠ T in atTop, 0 ≤ c⁻¹ * Ncnt T :=
    hN0.mono fun T hT => mul_nonneg (inv_pos.2 hc0).le hT
  have hδ' : 0 < δ * c := by positivity
  filter_upwards [eventually_abs_sub_le_of_isEquivalent h1 hv hδ', hN0] with T hT hN
  have := (abs_le.mp hT).2
  have e : δ * c * (c⁻¹ * Ncnt T) = δ * Ncnt T := by field_simp
  nlinarith [e]

end Moments

end XiPrime
end Zeta23
