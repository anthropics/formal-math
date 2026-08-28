/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ExplicitFormula.lean  —  the explicit formula, normalisations (paper App. A [app:EF]).

The *normalisation chain*: the passage from a literature-verbatim explicit formula to the paper's
density ν_X = μ + Π_X + P_X [eq:mudef]–[eq:nudef], with every 2π and every sign:

  * `EF.literatureRHS` / `EF_lit` : the right-hand side of [eq:EFstd] (App. A, first display), i.e. the
    Weil explicit formula in the form the paper quotes from [IK04, Thm 5.12] / [Wei52] / [Bom00],
    for a single test function k ∈ C_c²(ℝ) with h(z) := ∫ k(u) e^{izu} du;
  * `EF.prop_EF_of_lit` : [eq:EFstd] for k := f ⋆ g̃  ⟹  [eq:EF]  W(f,g) = ∫ h_f(τ) conj(h_g(τ)) ν_X(τ) dτ,
    X = e^L, for f, g ∈ C_c²(ℝ) supported in [−L/2, L/2]  — exactly App. A's three identifications
    (Gamma term, prime term, pole term) plus h_{f⋆g̃}(z) = h_f(z)·conj(h_g(conj z)).

The truth of [eq:EFstd] itself (contour integration of
h((s-1/2)/i)·ξ'/ξ(s)) is the hypothesis `EF_lit`, stated for the zero configuration
abstractly.

CONVENTIONS (paper [Notation]).  Paper Fourier transform:
    f̂(τ) = h_f(τ) := ∫_ℝ f(u) e^{iτu} du,   inversion  f(u) = (1/2π) ∫_ℝ h_f(r) e^{-iru} dr.
Mathlib: 𝓕 f w = ∫ v, exp(-2πi v w) • f v.  Dictionary (proved below, `paperFT_ofReal_eq_fourier`):
    h_f(τ) = 𝓕 f (-τ/(2π)).
-/
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Zeta23.Defs

open MeasureTheory Complex Filter Set
open scoped Real FourierTransform Convolution ComplexConjugate ArithmeticFunction

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Zeta23
namespace EF

/-! ### App. A objects owned by this file -/

/-- App. A: `g̃(u) := conj (g(−u))`. -/
def tilde (g : ℝ → ℂ) : ℝ → ℂ := fun u => conj (g (-u))

/-- App. A: the Weil test function `k := f ⋆ g̃`, i.e. `k(x) = ∫ f(t) g̃(x − t) dt`
(Mathlib convolution w.r.t. Lebesgue measure and the ℝ-bilinear map `ContinuousLinearMap.mul ℝ ℂ`). -/
def weilTest (f g : ℝ → ℂ) : ℝ → ℂ := f ⋆[ContinuousLinearMap.mul ℝ ℂ] tilde g

end EF


namespace EF

/-! ## The literature form [eq:EFstd] -/

/-- The Gamma-factor bracket in [eq:EFstd]: `Re Γ'/Γ(1/4 + ir/2) − log π`
( = Γ_ℝ'/Γ_ℝ(1/2+ir) + Γ_ℝ'/Γ_ℝ(1/2−ir), Γ_ℝ(s) = π^{-s/2}Γ(s/2); equals 2π μ(r) by [eq:mudef]).
Γ'/Γ is spelled `Complex.digamma` (= logDeriv Gamma), identically to `Zeta23.mu` in Defs.lean. -/
def gammaBracket (r : ℝ) : ℝ := (Complex.digamma (1 / 4 + I * r / 2)).re - Real.log π

/-- Right-hand side of [eq:EFstd] (App. A, first display), VERBATIM:
`h(i/2) + h(−i/2) − Σ_{n≥1} Λ(n) n^{-1/2} (k(log n) + k(−log n)) + (1/2π) ∫_ℝ h(r) [Re Γ'/Γ(1/4 + ir/2) − log π] dr`
with `h := paperFT k`.  The n-sum is written over all `n : ℕ` (Λ(0) = Λ(1) = 0); for compactly supported k it
has finite support. -/
def literatureRHS (k : ℝ → ℂ) : ℂ :=
  paperFT k (I / 2) + paperFT k (-I / 2)
  - ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (k (Real.log n) + k (-Real.log n))
  + (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * (gammaBracket r : ℂ)

/-- **H-EF, literature form** ([eq:EFstd]; [IK04, Thm 5.12] specialised to ζ / [Wei52] / [Bom00]):
for every `k ∈ C_c²(ℝ)` with `h(z) := ∫ k(u)e^{izu}du`,
`Σ_ρ m_ρ h(γ_ρ) = literatureRHS k`, the zero sum converging absolutely (paper: "here absolutely
convergent since h(r) ≪_k (1+|r|)^{-2} on |Im r| ≤ 1/2").  It is a hypothesis
(structure field in Hypotheses.lean), never a Lean axiom. -/
def EF_lit (Z : ZeroConfig) : Prop :=
  ∀ k : ℝ → ℂ, ContDiff ℝ 2 k → HasCompactSupport k →
    Summable (fun ρ : Z.carrier => (Z.mult ρ : ℂ) * paperFT k (gammaOf ρ)) ∧
    ∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT k (gammaOf ρ) = literatureRHS k

/-- **H-EF, paper form** ([prop:EF], [eq:EF]): for `f, g ∈ C_c²(ℝ)` with supports in `[−L/2, L/2]`,
`W(f,g) = ∫_ℝ h_f(τ) conj(h_g(τ)) ν_X(τ) dτ`, `X = e^L`. -/
def EF_paper (Z : ZeroConfig) : Prop :=
  ∀ (L : ℝ) (f g : ℝ → ℂ), 0 < L → ContDiff ℝ 2 f → ContDiff ℝ 2 g →
    tsupport f ⊆ Icc (-(L / 2)) (L / 2) → tsupport g ⊆ Icc (-(L / 2)) (L / 2) →
    Z.W f g = ∫ τ : ℝ, paperFT f τ * conj (paperFT g τ) * (nuX (Real.exp L) τ : ℂ)

/-! ## ℂ-specialised integral helpers

(In this toolchain `rw [← integral_const_mul]` fails to key-match on ℂ-valued integrals because the
RCLike-generic lemma elaborates `Mul ℂ`/`NormedAddCommGroup ℂ` through a different instance path than
a goal written with `*`; restating the lemmas at ℂ (proved by `exact`) makes `rw` usable.) -/

theorem cintegral_const_mul (c : ℂ) (f : ℝ → ℂ) : ∫ x, c * f x = c * ∫ x, f x :=
  integral_const_mul c f

theorem cintegral_mul_const (c : ℂ) (f : ℝ → ℂ) : ∫ x, f x * c = (∫ x, f x) * c :=
  integral_mul_const c f

theorem cintegral_conj (f : ℝ → ℂ) : ∫ x, conj (f x) = conj (∫ x, f x) := integral_conj

/-! ## Dictionary with Mathlib's Fourier transform -/

/-- `h_k(τ) = 𝓕 k (−τ/(2π))` for real τ. -/
theorem paperFT_ofReal_eq_fourier (k : ℝ → ℂ) (τ : ℝ) :
    paperFT k τ = 𝓕 k (-τ / (2 * π)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold paperFT
  congr 1; ext u
  rw [smul_eq_mul, mul_comm (k u)]
  congr 1
  have : (-2 * π * u * (-τ / (2 * π))) = τ * u := by
    field_simp
  rw [this]
  push_cast
  ring_nf

/-- `h_k` is integrable on the real line when `𝓕 k` is (dictionary + linear substitution). -/
theorem integrable_paperFT_ofReal {k : ℝ → ℂ} (hFk : Integrable (𝓕 k)) :
    Integrable (fun τ : ℝ => paperFT k τ) := by
  have : (fun τ : ℝ => paperFT k τ) = fun τ => (𝓕 k) ((-(1 / (2 * π))) * τ) := by
    ext τ; rw [paperFT_ofReal_eq_fourier, show -(1 / (2 * π)) * τ = -τ / (2 * π) by ring]
  rw [this]
  exact hFk.comp_mul_left' (neg_ne_zero.mpr (by positivity))

/-- Paper inversion `k(u) = (1/2π) ∫ h(r) e^{−iru} dr` (App. A, "so that …"), from Mathlib's
`Continuous.fourierInv_fourier_eq` and the substitution `v = −r/(2π)`. -/
theorem paper_inversion {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (𝓕 k)) (u : ℝ) :
    k u = (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * cexp (-I * r * u) := by
  have hinv := congrFun (hk.fourierInv_fourier_eq hki hFk) u
  rw [← hinv, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  have key : (fun r : ℝ => paperFT k r * cexp (-I * r * u))
      = fun r => (fun v : ℝ => 𝓕 k v * cexp (2 * π * I * v * u)) ((-(1 / (2 * π))) * r) := by
    ext r
    rw [paperFT_ofReal_eq_fourier, show -(1 / (2 * π)) * r = -r / (2 * π) by ring]
    congr 1
    push_cast
    field_simp
  rw [key, Measure.integral_comp_mul_left (fun v : ℝ => 𝓕 k v * cexp (2 * π * I * v * u))]
  have habs : |(-(1 / (2 * π)) : ℝ)⁻¹| = 2 * π := by
    rw [inv_neg, abs_neg, one_div, inv_inv, abs_of_pos (by positivity)]
  rw [habs, Complex.real_smul, ← mul_assoc]
  have h2π : (1 / (2 * π) : ℂ) * ((2 * π : ℝ) : ℂ) = 1 := by
    push_cast; field_simp
  rw [h2π, one_mul]
  congr 1; ext v
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast; ring

/-! ## The test function k = f ⋆ g̃ -/

theorem continuous_tilde {g : ℝ → ℂ} (hg : Continuous g) : Continuous (tilde g) :=
  Complex.continuous_conj.comp (hg.comp continuous_neg)

theorem hasCompactSupport_tilde {g : ℝ → ℂ} (hgs : HasCompactSupport g) :
    HasCompactSupport (tilde g) :=
  (hgs.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (g := fun w : ℂ => conj w) (map_zero _)

theorem support_tilde_subset (g : ℝ → ℂ) : Function.support (tilde g) ⊆ -tsupport g := by
  intro u hu
  simp only [Function.mem_support, tilde, ne_eq, map_eq_zero] at hu
  exact subset_tsupport _ (by simpa [Function.mem_support] using hu)

theorem tsupport_tilde_subset {g : ℝ → ℂ} {L : ℝ} (hgs : tsupport g ⊆ Icc (-(L / 2)) (L / 2)) :
    tsupport (tilde g) ⊆ Icc (-(L / 2)) (L / 2) := by
  refine closure_minimal ((support_tilde_subset g).trans ?_) isClosed_Icc
  intro u hu
  have := hgs hu
  simp only [mem_Icc] at this ⊢
  constructor <;> linarith [this.1, this.2]

theorem paperFT_tilde (g : ℝ → ℂ) (z : ℂ) :
    paperFT (tilde g) z = conj (paperFT g (conj z)) := by
  unfold paperFT tilde
  rw [← cintegral_conj, ← integral_neg_eq_self]
  congr 1; ext u
  simp only [map_mul, ← Complex.exp_conj, conj_conj, Complex.conj_I, Complex.conj_ofReal,
    Complex.ofReal_neg, neg_neg]
  ring_nf

/-- App. A: `h_{f⋆g̃}(z) = h_f(z) · conj(h_g(conj z))` for all complex z. -/
theorem paperFT_weilTest {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) (z : ℂ) :
    paperFT (weilTest f g) z = paperFT f z * conj (paperFT g (conj z)) := by
  rw [← paperFT_tilde]
  have hgt : Continuous (tilde g) := continuous_tilde hg
  have hgts : HasCompactSupport (tilde g) := hasCompactSupport_tilde hgs
  -- the integrand on ℝ × ℝ : (x,t) ↦ f(t) g̃(x−t) e^{izx}, continuous with compact support
  have hFc : Continuous (Function.uncurry fun (x t : ℝ) => f t * tilde g (x - t) * cexp (I * z * x)) := by
    change Continuous fun p : ℝ × ℝ => f p.2 * tilde g (p.1 - p.2) * cexp (I * z * p.1)
    fun_prop
  have hFs : HasCompactSupport
      (Function.uncurry fun (x t : ℝ) => f t * tilde g (x - t) * cexp (I * z * x)) := by
    refine HasCompactSupport.intro ((hgts.isCompact.add hfs.isCompact).prod hfs.isCompact) ?_
    rintro ⟨x, t⟩ hxt
    change f t * tilde g (x - t) * cexp (I * z * x) = 0
    rw [mem_prod, not_and_or] at hxt
    rcases hxt with hx | ht
    · by_cases ht : t ∈ tsupport f
      · have hx' : x - t ∉ tsupport (tilde g) := fun h => hx ⟨x - t, h, t, ht, by ring⟩
        rw [image_eq_zero_of_notMem_tsupport hx']; simp
      · rw [image_eq_zero_of_notMem_tsupport ht]; simp
    · rw [image_eq_zero_of_notMem_tsupport ht]; simp
  have hFi : Integrable (Function.uncurry fun (x t : ℝ) => f t * tilde g (x - t) * cexp (I * z * x))
      (volume.prod volume) := hFc.integrable_of_hasCompactSupport hFs
  -- translation v = x − t in the inner integral
  have hshift : ∀ t : ℝ, ∫ x : ℝ, tilde g (x - t) * cexp (I * z * x)
      = cexp (I * z * t) * ∫ v : ℝ, tilde g v * cexp (I * z * v) := by
    intro t
    rw [← cintegral_const_mul,
      ← integral_sub_right_eq_self (fun v : ℝ => cexp (I * z * t) * (tilde g v * cexp (I * z * v))) t]
    congr 1; ext x
    simp only [Complex.ofReal_sub]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2; ring
  calc paperFT (weilTest f g) z
      = ∫ x : ℝ, (∫ t : ℝ, f t * tilde g (x - t)) * cexp (I * z * x) := by
        simp only [paperFT, weilTest, convolution_def, ContinuousLinearMap.mul_apply']
    _ = ∫ x : ℝ, ∫ t : ℝ, f t * tilde g (x - t) * cexp (I * z * x) := by
        congr 1; ext x; rw [← cintegral_mul_const]
    _ = ∫ t : ℝ, ∫ x : ℝ, f t * tilde g (x - t) * cexp (I * z * x) := integral_integral_swap hFi
    _ = ∫ t : ℝ, f t * cexp (I * z * t) * ∫ v : ℝ, tilde g v * cexp (I * z * v) := by
        congr 1; ext t
        rw [show (fun x : ℝ => f t * tilde g (x - t) * cexp (I * z * x))
            = fun x => f t * (tilde g (x - t) * cexp (I * z * x)) from funext fun _ => mul_assoc _ _ _,
          cintegral_const_mul, hshift t]
        ring
    _ = paperFT f z * paperFT (tilde g) z := by
        simp only [paperFT]; rw [← cintegral_mul_const]

theorem weilTest_contDiff {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : Continuous g)
    (hfs : HasCompactSupport f) :
    ContDiff ℝ 2 (weilTest f g) := by
  have := hfs.contDiff_convolution_left (n := 2) (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume)
    hf (continuous_tilde hg).locallyIntegrable
  simpa [weilTest] using this

theorem weilTest_hasCompactSupport {f g : ℝ → ℂ}
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    HasCompactSupport (weilTest f g) :=
  hfs.convolution _ (hasCompactSupport_tilde hgs)

/-- App. A: `supp k ⊆ [−L, L]` when `supp f, supp g ⊆ [−L/2, L/2]`. -/
theorem tsupport_weilTest_subset {f g : ℝ → ℂ} {L : ℝ}
    (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) (hgs : tsupport g ⊆ Icc (-(L / 2)) (L / 2)) :
    tsupport (weilTest f g) ⊆ Icc (-L) L := by
  refine closure_minimal ?_ isClosed_Icc
  refine (support_convolution_subset _).trans ?_
  rintro x ⟨a, ha, b, hb, rfl⟩
  have ha' := hfs (subset_tsupport _ ha)
  have hb' := tsupport_tilde_subset hgs (subset_tsupport _ hb)
  simp only [mem_Icc] at ha' hb' ⊢
  constructor <;> linarith [ha'.1, ha'.2, hb'.1, hb'.2]

/-! ## App. A: the three identifications -/

/-- *Gamma term*: `(1/2π) ∫ h(r)[Re Γ'/Γ(1/4+ir/2) − log π] dr = ∫ h μ` — definitional ([eq:mudef]). -/
theorem gamma_term (k : ℝ → ℂ) :
    (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * (gammaBracket r : ℂ)
      = ∫ τ : ℝ, paperFT k τ * (mu τ : ℂ) := by
  rw [← cintegral_const_mul]
  congr 1; ext r
  simp only [gammaBracket, mu]
  push_cast
  ring

/-- Compact support from a support bound. -/
theorem hasCompactSupport_of_tsupport_subset {k : ℝ → ℂ} {L : ℝ}
    (hks : tsupport k ⊆ Icc (-L) L) : HasCompactSupport k :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport k) hks

/-- `h(r) e^{-irw}` is integrable in r when h is. -/
theorem integrable_paperFT_mul_cexp {k : ℝ → ℂ} (hFk : Integrable (𝓕 k)) (w : ℝ) :
    Integrable (fun r : ℝ => paperFT k r * cexp (-I * r * w)) := by
  refine (integrable_paperFT_ofReal hFk).mul_bdd (c := 1) (by fun_prop) ?_
  filter_upwards with r
  rw [Complex.norm_exp]
  simp

/-- `h(r) cos(r y)` is integrable in r when h is. -/
theorem integrable_paperFT_mul_cos {k : ℝ → ℂ} (hFk : Integrable (𝓕 k)) (y : ℝ) :
    Integrable (fun r : ℝ => paperFT k r * (Real.cos (r * y) : ℂ)) := by
  refine (integrable_paperFT_ofReal hFk).mul_bdd (c := 1) (by fun_prop) ?_
  filter_upwards with r
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_cos_le_one _

/-- App. A, *prime term*, first step: `k(y) + k(−y) = (1/2π)∫ h(τ)(e^{−iτy}+e^{iτy})dτ = (1/π) ∫ h(τ) cos(τy) dτ`. -/
theorem k_add_k_neg {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (𝓕 k)) (y : ℝ) :
    k y + k (-y) = (1 / π : ℂ) * ∫ τ : ℝ, paperFT k τ * (Real.cos (τ * y) : ℂ) := by
  rw [paper_inversion hk hki hFk y, paper_inversion hk hki hFk (-y), ← mul_add,
    ← integral_add (integrable_paperFT_mul_cexp hFk y) (integrable_paperFT_mul_cexp hFk (-y))]
  have h2 : ∀ τ : ℝ, paperFT k τ * cexp (-I * τ * y) + paperFT k τ * cexp (-I * τ * ↑(-y))
      = 2 * (paperFT k τ * (Real.cos (τ * y) : ℂ)) := by
    intro τ
    rw [← mul_add, Complex.ofReal_cos, mul_left_comm, Complex.two_cos, add_comm]
    congr 2
    · congr 1; push_cast; ring
    · congr 1; push_cast; ring
  simp_rw [h2]
  rw [cintegral_const_mul, ← mul_assoc]
  congr 1
  field_simp

/-- App. A, *prime term*, support step: `k(±log n) = 0` for `n > X = e^L`; and the n = 0 term
vanishes since Λ(0) = 0.  Hence the n-sum in [eq:EFstd] is the finite sum over `0 < n ≤ ⌊X⌋`. -/
theorem prime_summand_eq_zero {k : ℝ → ℂ} {L : ℝ} (hks : tsupport k ⊆ Icc (-L) L)
    {n : ℕ} (hn : n ∉ Finset.Ioc 0 ⌊Real.exp L⌋₊) :
    ((Λ n / Real.sqrt n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · have hn' : ⌊Real.exp L⌋₊ < n := by
      simp only [Finset.mem_Ioc, not_and, not_le] at hn
      exact hn hpos
    have hX : Real.exp L < n := (Nat.floor_lt (Real.exp_pos L).le).mp hn'
    have hlog : L < Real.log n := by
      rw [← Real.log_exp L]
      exact Real.log_lt_log (Real.exp_pos L) hX
    have h1 : k (Real.log n) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem; have := (hks hmem).2; linarith
    have h2 : k (-Real.log n) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem; have := (hks hmem).1; linarith
    rw [h1, h2, add_zero, mul_zero]

/-- *Prime term*: for k continuous with `supp k ⊆ [−L, L]` and h integrable on ℝ,
`−Σ_{n≥1} Λ(n)n^{-1/2}(k(log n)+k(−log n)) = ∫ h P_X`, `X = e^L`
(uses inversion: `k(y)+k(−y) = (1/π)∫ h(τ)cos(τy)dτ`, and `k(±log n) = 0` for `n > X`). -/
theorem prime_term {k : ℝ → ℂ} {L : ℝ} (hk : Continuous k)
    (hks : tsupport k ⊆ Icc (-L) L) (hFk : Integrable (𝓕 k)) :
    -(∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)))
      = ∫ τ : ℝ, paperFT k τ * (PX (Real.exp L) τ : ℂ) := by
  have hki : Integrable k :=
    hk.integrable_of_hasCompactSupport (hasCompactSupport_of_tsupport_subset hks)
  set S := Finset.Ioc 0 ⌊Real.exp L⌋₊ with hS
  rw [tsum_eq_sum (s := S) (fun n hn => prime_summand_eq_zero hks hn)]
  -- rewrite each k(log n) + k(-log n) via inversion
  have step1 : ∑ n ∈ S, ((Λ n / Real.sqrt n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))
      = ∑ n ∈ S, ((Λ n / Real.sqrt n : ℝ) : ℂ) *
          ((1 / π : ℂ) * ∫ τ : ℝ, paperFT k τ * (Real.cos (τ * Real.log n) : ℂ)) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [k_add_k_neg hk hki hFk]
  rw [step1]
  -- right side: expand P_X and pull the finite sum and constants out of the integral
  have step2 : (fun τ : ℝ => paperFT k τ * (PX (Real.exp L) τ : ℂ))
      = fun τ : ℝ => ∑ n ∈ S, (-(1 / π) * ((Λ n / Real.sqrt n : ℝ) : ℂ)) *
          (paperFT k τ * (Real.cos (τ * Real.log n) : ℂ)) := by
    ext τ
    simp only [PX, ← hS]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [step2, integral_finsetSum _ (fun n _ => (integrable_paperFT_mul_cos hFk _).const_mul _)]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [cintegral_const_mul]
  ring

/-! ### Pole term: inversion + Fubini, and the two explicit integrals -/

theorem norm_cexp_neg_I_mul (τ u : ℝ) : ‖cexp (-I * τ * u)‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- Joint integrability of `(u,τ) ↦ h(τ) e^{−iτu} E(u)` for integrable h (on ℝ) and E. -/
theorem integrable_inversion_kernel {k : ℝ → ℂ} (hFk : Integrable (𝓕 k)) {E : ℝ → ℂ}
    (hE : Integrable E) :
    Integrable (Function.uncurry fun (u τ : ℝ) => paperFT k τ * cexp (-I * τ * u) * E u)
      (volume.prod volume) := by
  have hG : Integrable (fun p : ℝ × ℝ => E p.1 * paperFT k p.2) (volume.prod volume) :=
    hE.mul_prod (integrable_paperFT_ofReal hFk)
  refine hG.norm.mono' ?_ ?_
  · have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => paperFT k p.2) (volume.prod volume) :=
      (integrable_paperFT_ofReal hFk).aestronglyMeasurable.comp_snd
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => E p.1) (volume.prod volume) :=
      hE.aestronglyMeasurable.comp_fst
    have h3 : AEStronglyMeasurable (fun p : ℝ × ℝ => cexp (-I * p.2 * p.1)) (volume.prod volume) :=
      (by fun_prop : Continuous fun p : ℝ × ℝ => cexp (-I * p.2 * p.1)).aestronglyMeasurable
    exact (h1.mul h3).mul h2
  · filter_upwards with p
    simp only [Function.uncurry, norm_mul, norm_cexp_neg_I_mul, mul_one]
    exact le_of_eq (mul_comm _ _)

/-- App. A, "inserting `k(u) = (1/2π)∫ h(τ)e^{−iτu}dτ` and interchanging (all integrals absolutely
convergent)": for an integrable weight E,  `∫ k(u)E(u)du = (1/2π) ∫ h(τ) (∫ E(u)e^{−iτu}du) dτ`. -/
theorem integral_k_mul_weight {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (𝓕 k)) {E : ℝ → ℂ} (hE : Integrable E) :
    ∫ u : ℝ, k u * E u
      = (1 / (2 * π) : ℂ) * ∫ τ : ℝ, paperFT k τ * ∫ u : ℝ, E u * cexp (-I * τ * u) := by
  have hsub : (fun u : ℝ => k u * E u)
      = fun u : ℝ => (1 / (2 * π) : ℂ) * ∫ τ : ℝ, paperFT k τ * cexp (-I * τ * u) * E u := by
    ext u; rw [paper_inversion hk hki hFk u, mul_assoc, ← cintegral_mul_const]
  rw [hsub, cintegral_const_mul]
  congr 1
  rw [integral_integral_swap (integrable_inversion_kernel hFk hE)]
  congr 1; ext τ
  rw [← cintegral_const_mul]
  congr 1; ext u; ring

/-- The τ-integrand produced by `integral_k_mul_weight` is integrable (Fubini). -/
theorem integrable_paperFT_mul_weightFT {k : ℝ → ℂ} (hFk : Integrable (𝓕 k)) {E : ℝ → ℂ}
    (hE : Integrable E) :
    Integrable (fun τ : ℝ => paperFT k τ * ∫ u : ℝ, E u * cexp (-I * τ * u)) := by
  have := (integrable_inversion_kernel hFk hE).swap.integral_prod_left
  refine this.congr ?_
  filter_upwards with τ
  simp only [Function.comp, Function.uncurry, Prod.swap]
  rw [← cintegral_const_mul]
  congr 1; ext u; ring

theorem half_add_I_mul_ne_zero (τ : ℝ) : (1 / 2 : ℂ) + I * τ ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this

theorem half_sub_I_mul_ne_zero (τ : ℝ) : (1 / 2 : ℂ) - I * τ ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this

theorem neg_half_sub_I_mul_ne_zero (τ : ℝ) : (-(1 / 2) : ℂ) - I * τ ≠ 0 := by
  intro h; have := congrArg Complex.re h; norm_num at this

/-- Integrability of `u ↦ e^{−|u|/2} e^{−iτu}` on ℝ (two half-lines). -/
theorem integrable_exp_neg_abs_half_mul (τ : ℝ) :
    Integrable (fun u : ℝ => (Real.exp (-|u| / 2) : ℂ) * cexp (-I * τ * u)) := by
  have hIic : IntegrableOn (fun u : ℝ => cexp ((1 / 2 - I * τ) * u)) (Iic 0) :=
    integrableOn_exp_mul_complex_Iic (by simp) 0
  have hIoi : IntegrableOn (fun u : ℝ => cexp ((-(1 / 2) - I * τ) * u)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (by norm_num) 0
  have eIic : EqOn (fun u : ℝ => (Real.exp (-|u| / 2) : ℂ) * cexp (-I * τ * u))
      (fun u : ℝ => cexp ((1 / 2 - I * τ) * u)) (Iic 0) := by
    intro u hu
    simp only [mem_Iic] at hu
    simp only [abs_of_nonpos hu, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  have eIoi : EqOn (fun u : ℝ => (Real.exp (-|u| / 2) : ℂ) * cexp (-I * τ * u))
      (fun u : ℝ => cexp ((-(1 / 2) - I * τ) * u)) (Ioi 0) := by
    intro u hu
    simp only [mem_Ioi] at hu
    simp only [abs_of_pos hu, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  have := (hIic.congr_fun eIic.symm measurableSet_Iic).union
    (hIoi.congr_fun eIoi.symm measurableSet_Ioi)
  rwa [Iic_union_Ioi, integrableOn_univ] at this

theorem integrable_exp_neg_abs_half :
    Integrable (fun u : ℝ => (Real.exp (-|u| / 2) : ℂ)) := by
  simpa using integrable_exp_neg_abs_half_mul 0

/-- App. A: `∫_ℝ e^{−|u|/2} e^{−iτu} du = (1/4 + τ²)^{−1}`. -/
theorem integral_exp_neg_abs_half (τ : ℝ) :
    ∫ u : ℝ, (Real.exp (-|u| / 2) : ℂ) * cexp (-I * τ * u) = 1 / ((1 / 4 : ℂ) + τ ^ 2) := by
  have hIic : IntegrableOn (fun u : ℝ => cexp ((1 / 2 - I * τ) * u)) (Iic 0) :=
    integrableOn_exp_mul_complex_Iic (by simp) 0
  have hIoi : IntegrableOn (fun u : ℝ => cexp ((-(1 / 2) - I * τ) * u)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (by norm_num) 0
  have eIic : EqOn (fun u : ℝ => (Real.exp (-|u| / 2) : ℂ) * cexp (-I * τ * u))
      (fun u : ℝ => cexp ((1 / 2 - I * τ) * u)) (Iic 0) := by
    intro u hu
    simp only [mem_Iic] at hu
    simp only [abs_of_nonpos hu, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  have eIoi : EqOn (fun u : ℝ => (Real.exp (-|u| / 2) : ℂ) * cexp (-I * τ * u))
      (fun u : ℝ => cexp ((-(1 / 2) - I * τ) * u)) (Ioi 0) := by
    intro u hu
    simp only [mem_Ioi] at hu
    simp only [abs_of_pos hu, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) (hIic.congr_fun eIic.symm measurableSet_Iic)
    (hIoi.congr_fun eIoi.symm measurableSet_Ioi),
    setIntegral_congr_fun measurableSet_Iic eIic, setIntegral_congr_fun measurableSet_Ioi eIoi,
    integral_exp_mul_complex_Iic (by simp) 0, integral_exp_mul_complex_Ioi (by norm_num) 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have h1 := half_sub_I_mul_ne_zero τ
  have h2 := neg_half_sub_I_mul_ne_zero τ
  have h3 : (1 / 4 : ℂ) + τ ^ 2 ≠ 0 := by
    rw [show (1 / 4 : ℂ) + τ ^ 2 = ((1 / 4 + τ ^ 2 : ℝ) : ℂ) by push_cast; ring]
    exact_mod_cast (by positivity : (1 / 4 + τ ^ 2 : ℝ) ≠ 0)
  rw [div_add_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) h3]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The truncated growing weight `E_L(u) := 1_{[−L,L]}(u) e^{|u|/2}`. -/
def EL (L : ℝ) : ℝ → ℂ := (Icc (-L) L).indicator fun u => (Real.exp (|u| / 2) : ℂ)

theorem integrable_EL (L : ℝ) : Integrable (EL L) := by
  unfold EL
  refine IntegrableOn.integrable_indicator ?_ measurableSet_Icc
  exact (by fun_prop : Continuous fun u : ℝ => (Real.exp (|u| / 2) : ℂ)).continuousOn.integrableOn_compact
    isCompact_Icc

/-- `X^s = e^{Ls}` for `X = e^L`. -/
theorem exp_cpow (L : ℝ) (s : ℂ) : ((Real.exp L : ℝ) : ℂ) ^ s = cexp (L * s) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos L).ne'),
    ← Complex.ofReal_log (Real.exp_pos L).le, Real.log_exp]

/-- App. A: `∫_{−L}^{L} e^{|u|/2}e^{−iτu}du = 2Re∫_0^L e^{us̄}du = 2Re((X^s−1)/s)`, `s = 1/2+iτ`,
`X = e^L`. -/
theorem integral_EL_mul (τ : ℝ) {L : ℝ} (hL : 0 < L) :
    ∫ u : ℝ, EL L u * cexp (-I * τ * u)
      = ((2 * ((((Real.exp L : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + I * τ) - 1) / ((1 / 2 : ℂ) + I * τ)).re : ℝ) : ℂ) := by
  set s : ℂ := 1 / 2 + I * τ with hs
  have hs0 : s ≠ 0 := half_add_I_mul_ne_zero τ
  have hsc : conj s = 1 / 2 - I * τ := by
    rw [hs, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]
    ring
  have hsc0 : conj s ≠ 0 := by rw [hsc]; exact half_sub_I_mul_ne_zero τ
  -- to a set integral, then an interval integral, then split at 0
  have hind : (fun u : ℝ => EL L u * cexp (-I * τ * u))
      = (Icc (-L) L).indicator (fun u => (Real.exp (|u| / 2) : ℂ) * cexp (-I * τ * u)) := by
    ext u; simp only [EL, Set.indicator_mul_left]
  rw [hind, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -L ≤ L)]
  have hcont : Continuous fun u : ℝ => (Real.exp (|u| / 2) : ℂ) * cexp (-I * τ * u) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have e1 : EqOn (fun u : ℝ => (Real.exp (|u| / 2) : ℂ) * cexp (-I * τ * u))
      (fun u => cexp (-s * u)) (uIcc (-L) 0) := by
    intro u hu
    rw [uIcc_of_le (by linarith)] at hu
    simp only [abs_of_nonpos hu.2, Complex.ofReal_exp, ← Complex.exp_add, hs]
    congr 1; push_cast; ring
  have e2 : EqOn (fun u : ℝ => (Real.exp (|u| / 2) : ℂ) * cexp (-I * τ * u))
      (fun u => cexp (conj s * u)) (uIcc 0 L) := by
    intro u hu
    rw [uIcc_of_le hL.le] at hu
    simp only [abs_of_nonneg hu.1, Complex.ofReal_exp, ← Complex.exp_add, hsc]
    congr 1; push_cast; ring
  rw [intervalIntegral.integral_congr e1, intervalIntegral.integral_congr e2,
    integral_exp_mul_complex (neg_ne_zero.mpr hs0), integral_exp_mul_complex hsc0]
  -- evaluate: z + conj z with z = (X^s - 1)/s
  have hz : (cexp (-s * (0 : ℝ)) - cexp (-s * ((-L : ℝ) : ℂ))) / -s
      = (((Real.exp L : ℝ) : ℂ) ^ s - 1) / s := by
    rw [exp_cpow]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, Complex.ofReal_neg, mul_neg, neg_mul,
      neg_neg]
    rw [mul_comm s L]
    field_simp
    ring
  have hzc : (cexp (conj s * (L : ℝ)) - cexp (conj s * ((0 : ℝ) : ℂ))) / conj s
      = conj ((((Real.exp L : ℝ) : ℂ) ^ s - 1) / s) := by
    rw [exp_cpow, map_div₀, map_sub, map_one, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [mul_comm (conj s) L]
  rw [hz, hzc, Complex.add_conj]

/-- *Pole term*: for k continuous with `supp k ⊆ [−L, L]` and h integrable on ℝ,
`h(i/2) + h(−i/2) = ∫ h Π_X`, `X = e^L`
(uses `∫_ℝ e^{−|u|/2}e^{−iτu}du = (1/4+τ²)^{-1}` and `∫_{−L}^{L} e^{|u|/2}e^{−iτu}du = 2Re((X^s−1)/s)`). -/
theorem pole_term {k : ℝ → ℂ} {L : ℝ} (hL : 0 < L) (hk : Continuous k)
    (hks : tsupport k ⊆ Icc (-L) L) (hFk : Integrable (𝓕 k)) :
    paperFT k (I / 2) + paperFT k (-I / 2)
      = ∫ τ : ℝ, paperFT k τ * (PiX (Real.exp L) τ : ℂ) := by
  have hkc : HasCompactSupport k := hasCompactSupport_of_tsupport_subset hks
  have hki : Integrable k := hk.integrable_of_hasCompactSupport hkc
  have hA_int : Integrable (fun u : ℝ => k u * (Real.exp (-|u| / 2) : ℂ)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have hB_int : Integrable (fun u : ℝ => k u * (Real.exp (|u| / 2) : ℂ)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have hI1 : Integrable (fun u : ℝ => k u * cexp (I * (I / 2) * u)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have hI2 : Integrable (fun u : ℝ => k u * cexp (I * (-I / 2) * u)) :=
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  -- Step 1: h(i/2) + h(−i/2) = ∫ k(u)(e^{−u/2} + e^{u/2}) du = ∫ k e^{−|u|/2} + ∫ k e^{|u|/2}
  have step1 : paperFT k (I / 2) + paperFT k (-I / 2)
      = (∫ u : ℝ, k u * (Real.exp (-|u| / 2) : ℂ)) + ∫ u : ℝ, k u * (Real.exp (|u| / 2) : ℂ) := by
    rw [← integral_add hA_int hB_int]
    unfold paperFT
    rw [← integral_add hI1 hI2]
    congr 1; ext u
    rw [← mul_add, ← mul_add]
    congr 1
    have ha : I * (I / 2) * (u : ℂ) = ((-u / 2 : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [Complex.I_sq]; ring
    have hb : I * (-I / 2) * (u : ℂ) = ((u / 2 : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [ha, hb, ← Complex.ofReal_exp, ← Complex.ofReal_exp, ← Complex.ofReal_add,
      ← Complex.ofReal_add]
    congr 1
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu, neg_div]
    · rw [abs_of_nonpos hu, neg_neg, add_comm, neg_div]
  -- Step 2 (decaying half): ∫ k e^{−|u|/2} = (1/2π) ∫ h(τ) (1/4+τ²)^{-1} dτ
  have stepA : ∫ u : ℝ, k u * (Real.exp (-|u| / 2) : ℂ)
      = (1 / (2 * π) : ℂ) * ∫ τ : ℝ, paperFT k τ * (1 / ((1 / 4 : ℂ) + τ ^ 2)) := by
    rw [integral_k_mul_weight hk hki hFk integrable_exp_neg_abs_half]
    simp_rw [integral_exp_neg_abs_half]
  -- Step 2 (growing half, truncated by supp k ⊆ [−L,L]): ∫ k e^{|u|/2} = (1/2π) ∫ h(τ) 2Re((X^s−1)/s) dτ
  have hkEL : (fun u : ℝ => k u * (Real.exp (|u| / 2) : ℂ)) = fun u => k u * EL L u := by
    ext u
    by_cases hu : u ∈ Icc (-L) L
    · simp [EL, hu]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hu (hks h)), zero_mul, zero_mul]
  have stepB : ∫ u : ℝ, k u * (Real.exp (|u| / 2) : ℂ)
      = (1 / (2 * π) : ℂ) * ∫ τ : ℝ, paperFT k τ *
          ((2 * ((((Real.exp L : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + I * τ) - 1) / ((1 / 2 : ℂ) + I * τ)).re : ℝ) : ℂ) := by
    rw [hkEL, integral_k_mul_weight hk hki hFk (integrable_EL L)]
    simp_rw [integral_EL_mul _ hL]
  -- integrability of the two τ-integrands (from Fubini)
  have hintA : Integrable (fun τ : ℝ => paperFT k τ * (1 / ((1 / 4 : ℂ) + τ ^ 2))) := by
    have := integrable_paperFT_mul_weightFT hFk integrable_exp_neg_abs_half
    simp_rw [integral_exp_neg_abs_half] at this
    exact this
  have hintB : Integrable (fun τ : ℝ => paperFT k τ *
      ((2 * ((((Real.exp L : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + I * τ) - 1) / ((1 / 2 : ℂ) + I * τ)).re : ℝ) : ℂ)) := by
    have := integrable_paperFT_mul_weightFT hFk (integrable_EL L)
    simp_rw [integral_EL_mul _ hL] at this
    exact this
  -- assemble Π_X
  rw [step1, stepA, stepB, ← mul_add, ← integral_add hintA hintB, ← cintegral_const_mul]
  congr 1; ext τ
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h3 : (1 / 4 : ℂ) + τ ^ 2 ≠ 0 := by
    rw [show (1 / 4 : ℂ) + τ ^ 2 = ((1 / 4 + τ ^ 2 : ℝ) : ℂ) by push_cast; ring]
    exact_mod_cast (by positivity : (1 / 4 + τ ^ 2 : ℝ) ≠ 0)
  simp only [PiX]
  push_cast
  field_simp

/-! ### Integrability of the three densities against h (from the computations above) -/

theorem integrable_paperFT_mul_PiX {k : ℝ → ℂ} {L : ℝ} (hL : 0 < L) (hFk : Integrable (𝓕 k)) :
    Integrable (fun τ : ℝ => paperFT k τ * (PiX (Real.exp L) τ : ℂ)) := by
  have hintA : Integrable (fun τ : ℝ => paperFT k τ * (1 / ((1 / 4 : ℂ) + τ ^ 2))) := by
    have := integrable_paperFT_mul_weightFT hFk integrable_exp_neg_abs_half
    simp_rw [integral_exp_neg_abs_half] at this
    exact this
  have hintB : Integrable (fun τ : ℝ => paperFT k τ *
      ((2 * ((((Real.exp L : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + I * τ) - 1) / ((1 / 2 : ℂ) + I * τ)).re : ℝ) : ℂ)) := by
    have := integrable_paperFT_mul_weightFT hFk (integrable_EL L)
    simp_rw [integral_EL_mul _ hL] at this
    exact this
  refine ((hintA.add hintB).const_mul (1 / (2 * π) : ℂ)).congr ?_
  filter_upwards with τ
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h3 : (1 / 4 : ℂ) + τ ^ 2 ≠ 0 := by
    rw [show (1 / 4 : ℂ) + τ ^ 2 = ((1 / 4 + τ ^ 2 : ℝ) : ℂ) by push_cast; ring]
    exact_mod_cast (by positivity : (1 / 4 + τ ^ 2 : ℝ) ≠ 0)
  simp only [PiX, Pi.add_apply]
  push_cast
  field_simp

theorem paperFT_mul_PX_eq (k : ℝ → ℂ) (L : ℝ) :
    (fun τ : ℝ => paperFT k τ * (PX (Real.exp L) τ : ℂ))
      = fun τ : ℝ => ∑ n ∈ Finset.Ioc 0 ⌊Real.exp L⌋₊, (-(1 / π) * ((Λ n / Real.sqrt n : ℝ) : ℂ)) *
          (paperFT k τ * (Real.cos (τ * Real.log n) : ℂ)) := by
  ext τ
  simp only [PX]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

theorem integrable_paperFT_mul_PX {k : ℝ → ℂ} (L : ℝ) (hFk : Integrable (𝓕 k)) :
    Integrable (fun τ : ℝ => paperFT k τ * (PX (Real.exp L) τ : ℂ)) := by
  rw [paperFT_mul_PX_eq]
  exact integrable_finsetSum _ (fun n _ => (integrable_paperFT_mul_cos hFk _).const_mul _)

/-- `h·ν_X` is integrable, given that `h·μ` is (μ grows like log|τ|, so this last fact needs the
decay [eq:hfbound] of h and the Stirling bound [eq:mufacts]; it is supplied by the caller). -/
theorem integrable_paperFT_mul_nuX {k : ℝ → ℂ} {L : ℝ} (hL : 0 < L) (hFk : Integrable (𝓕 k))
    (hμ : Integrable (fun τ : ℝ => paperFT k τ * (mu τ : ℂ))) :
    Integrable (fun τ : ℝ => paperFT k τ * (nuX (Real.exp L) τ : ℂ)) := by
  refine ((hμ.add (integrable_paperFT_mul_PiX hL hFk)).add (integrable_paperFT_mul_PX L hFk)).congr ?_
  filter_upwards with τ
  simp only [nuX, Pi.add_apply]
  push_cast
  ring

/-! ## Adding up -/

/-- App. A, "Adding the three identifications gives (eq:EF)": the literature right-hand side equals
`∫ h ν_X`, `X = e^L`, for k ∈ C_c(ℝ) with `supp k ⊆ [−L, L]`, `𝓕 k` integrable and `h·μ` integrable. -/
theorem literatureRHS_eq_integral_nu {k : ℝ → ℂ} {L : ℝ} (hL : 0 < L) (hk : Continuous k)
    (hks : tsupport k ⊆ Icc (-L) L) (hFk : Integrable (𝓕 k))
    (hμ : Integrable (fun τ : ℝ => paperFT k τ * (mu τ : ℂ))) :
    literatureRHS k = ∫ τ : ℝ, paperFT k τ * (nuX (Real.exp L) τ : ℂ) := by
  have hPi := integrable_paperFT_mul_PiX hL hFk
  have hP := integrable_paperFT_mul_PX L hFk
  have hPiP : Integrable (fun τ : ℝ => paperFT k τ * (PiX (Real.exp L) τ : ℂ)
      + paperFT k τ * (PX (Real.exp L) τ : ℂ)) := hPi.add hP
  unfold literatureRHS
  rw [pole_term hL hk hks hFk, sub_eq_add_neg, prime_term hk hks hFk, gamma_term k,
    ← integral_add hPi hP, ← integral_add hPiP hμ]
  congr 1; ext τ
  simp only [nuX]
  push_cast
  ring

/-! ## [prop:EF] from the literature form -/

/-- **Main theorem.**  [eq:EFstd] (hypothesis `EF_lit`) ⟹ [eq:EF] for the pair (f,g):
`W(f,g) = ∫ h_f(τ) conj(h_g(τ)) ν_X(τ) dτ`, `X = e^L`.
Side hypotheses `hFk`, `hμ` are the two integrability facts App. A uses silently
("all integrals absolutely convergent") for k = f ⋆ g̃; both follow from [eq:hfbound] and [eq:mufacts]. -/
theorem prop_EF_of_lit (Z : ZeroConfig) (hEF : EF_lit Z) {L : ℝ} (hL : 0 < L) {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) (hgs : tsupport g ⊆ Icc (-(L / 2)) (L / 2))
    (hFk : Integrable (𝓕 (weilTest f g)))
    (hμ : Integrable (fun τ : ℝ => paperFT (weilTest f g) τ * (mu τ : ℂ))) :
    Summable (fun ρ : Z.carrier => Z.Wsummand f g ρ) ∧
    Integrable (fun τ : ℝ => paperFT f τ * conj (paperFT g τ) * (nuX (Real.exp L) τ : ℂ)) ∧
    Z.W f g = ∫ τ : ℝ, paperFT f τ * conj (paperFT g τ) * (nuX (Real.exp L) τ : ℂ) := by
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  have hgc : HasCompactSupport g :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport g) hgs
  have hkd : ContDiff ℝ 2 (weilTest f g) := weilTest_contDiff hf hg.continuous hfc
  have hk : Continuous (weilTest f g) := hkd.continuous
  have hks : tsupport (weilTest f g) ⊆ Icc (-L) L := tsupport_weilTest_subset hfs hgs
  obtain ⟨hsum, heq⟩ := hEF (weilTest f g) hkd (weilTest_hasCompactSupport hfc hgc)
  have hfac : ∀ z : ℂ, paperFT (weilTest f g) z = paperFT f z * conj (paperFT g (conj z)) :=
    paperFT_weilTest hf.continuous hg.continuous hfc hgc
  -- termwise: m_ρ h_k(γ_ρ) = m_ρ h_f(γ_ρ) conj(h_g(conj γ_ρ))
  have hterm : (fun ρ : Z.carrier => (Z.mult ρ : ℂ) * paperFT (weilTest f g) (gammaOf ρ))
      = fun ρ : Z.carrier => Z.Wsummand f g ρ := by
    ext ρ; simp only [ZeroConfig.Wsummand, hfac, mul_assoc]
  -- on the real line: h_k(τ) = h_f(τ) conj(h_g(τ))
  have hreal : (fun τ : ℝ => paperFT (weilTest f g) τ * (nuX (Real.exp L) τ : ℂ))
      = fun τ : ℝ => paperFT f τ * conj (paperFT g τ) * (nuX (Real.exp L) τ : ℂ) := by
    ext τ; rw [hfac, Complex.conj_ofReal]
  refine ⟨hterm ▸ hsum, hreal ▸ integrable_paperFT_mul_nuX hL hFk hμ, ?_⟩
  rw [literatureRHS_eq_integral_nu hL hk hks hFk hμ, hreal] at heq
  rw [← heq, ZeroConfig.W, ← hterm]

end EF
end Zeta23
