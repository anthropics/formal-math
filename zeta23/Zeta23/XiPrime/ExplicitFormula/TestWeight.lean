/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ExplicitFormula/TestWeight.lean — TEST-WEIGHT ESTIMATES for the ξ′ explicit formula.

Canonical text: [XF′] §3 (Lemma 3.1) and §4 (Thm 4.2 proof (b),(c)).
Consumer: EntryError.lean (the entry error 𝓔_{kl} of (EF4)).

WHAT IS HERE.  For a height family `Pf : ℝ → Params` with `hPf : FamilyHyps Pf` (ExplicitFormula.lean §7)
put P := Pf T, φ := P.phi T, L := P.L T, X := P.X T = e^L, τ_k := P.tau T k, and the Weil test function
    kfun P T k l := Zeta23.EF.weilTest (P.fk T k) (P.fk T l)      (k l : ℤ),
so that  paperFT (kfun P T k l) z = φ̂(z − τ_k) · φ̂(z − τ_l)  for ALL complex z (paperFT_kfun; this is
[XF′ Lemma 3.1] "Φ(s) = φ̂(t−ic−τ_k) φ̂(t−ic−τ_l)"), and H := Zeta23.WeilEF.Hfn (kfun …) is the weight of
the zero-side summand.  We prove, with constants depending only on hPf (never on T, k, l, t):
 (W5) the Cauchy-convolution lemma  ∫ dt/((1+(t−a)²)(1+(t−b)²)) ≤ 32π/(4+(a−b)²), its integrability, and
      the far-region bound  ∫_{|t−a| ≥ R} (same) ≤ π/R²;
 (W0) kfun ∈ C_c², tsupport ⊆ [−L, L] (also for u ↦ kfun(−u)); 0 < L, 1 ≤ L eventually;
 (W1) ‖H(5/4+it)‖ ≤ C X^{3/4} L² / ((1+(t−τ_k)²)(1+(t−τ_l)²));
 (W2) (|t−τ_k|+|t−τ_l|) ‖H(5/4+it)‖ ≤ C X^{3/4} L / ((1+(t−τ_k)²)(1+(t−τ_l)²))   (uses φ′, φ‴);
 (W3) the same two for the mirrored weight u ↦ kfun(−u), with τ ↦ −τ;
 (W4) on ℝ: paperFT kfun τ = φ̂_ℝ(τ−τ_k) φ̂_ℝ(τ−τ_l) (real), integrable, ∫‖·‖ ≤ C L²/(1+(τ_k−τ_l)²);
 (W6) ∫‖H‖ and ∫(1+|t−τ⋆|)‖H‖ ≤ C X^{3/4} L²/(1+(τ_k−τ_l)²), and the far-region bound
      ∫_{|t−τ⋆| ≥ 3τ⋆/4} ‖H‖ ≤ C X^{3/4} L²/T² when T ≤ τ_k, τ_l ≤ 2T (true for 0 ≤ k,l < d: tau_mem_Icc);
      same for the mirrored weight around −τ⋆.
ORGANISATION.  §A generic real analysis (W5).  §B paperFT helpers.  §C `WindowAt P T C`: the window
facts FamilyHyps gives at ONE good height (plus 1 ≤ L, 1 ≤ T), and `FamilyHyps.windowAt : ∃ C T₁, …`.
§D–§H: every estimate at a fixed height under `WindowAt`, with an EXPLICIT constant (a polynomial in C)
— these are the uniform statements; §I re-packages each in the "∃ C T₁, ∀ T ≥ T₁, ∀ k l" form.
A consumer needing ONE (C, T₁) for several items should use §C + the §D–§H lemmas directly.
The line is Re s = 5/4, written `(5/4 : ℂ) + t * I`.
-/
import Zeta23.XiPrime.ExplicitFormula
import Zeta23.Hypotheses.GzGp

open scoped BigOperators ComplexConjugate
open Complex MeasureTheory Set Filter Topology

noncomputable section

-- as in Zeta23/ExplicitFormula.lean and ~40 other files of the tree: lets `rw` match `deriv`/`∫` terms whose
-- (defeq) instance arguments were synthesized along different paths in different files.
set_option backward.isDefEq.respectTransparency false

namespace Zeta23
namespace XiPrime

open Zeta23.WeilEF (Hfn)

namespace TestWeight

/-! ## §A. Generic real analysis: the Cauchy convolution lemma (W5) -/

/-- the Cauchy kernel 1/(1+(t−a)²) is integrable. -/
theorem integrable_inv_one_add_sq_sub (a : ℝ) :
    Integrable (fun t : ℝ => 1 / (1 + (t - a) ^ 2)) := by
  have h := integrable_inv_one_add_sq.comp_sub_right a
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp [one_div]

theorem integral_inv_one_add_sq_sub (a : ℝ) : ∫ t : ℝ, 1 / (1 + (t - a) ^ 2) = Real.pi := by
  have h := integral_sub_right_eq_self (μ := (volume : Measure ℝ)) (fun u : ℝ => (1 + u ^ 2)⁻¹) a
  simp only [one_div]
  rw [h]
  exact integral_univ_inv_one_add_sq

/-- pointwise: 1/((1+(t−a)²)(1+(t−b)²)) ≤ 4/(4+(a−b)²) · (1/(1+(t−a)²) + 1/(1+(t−b)²)). -/
theorem cauchyConv_pointwise (a b t : ℝ) :
    1 / ((1 + (t - a) ^ 2) * (1 + (t - b) ^ 2))
      ≤ 4 / (4 + (a - b) ^ 2) * (1 / (1 + (t - a) ^ 2) + 1 / (1 + (t - b) ^ 2)) := by
  have hp : 0 < 1 + (t - a) ^ 2 := by positivity
  have hq : 0 < 1 + (t - b) ^ 2 := by positivity
  have hD : 0 < 4 + (a - b) ^ 2 := by positivity
  rw [div_add_div _ _ hp.ne' hq.ne', div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  have key : 4 + (a - b) ^ 2 ≤ 4 * ((1 + (t - b) ^ 2) + (1 + (t - a) ^ 2)) := by
    nlinarith [sq_nonneg ((t - a) + (t - b)), sq_nonneg (t - a), sq_nonneg (t - b)]
  calc 1 * ((4 + (a - b) ^ 2) * ((1 + (t - a) ^ 2) * (1 + (t - b) ^ 2)))
      = (4 + (a - b) ^ 2) * ((1 + (t - a) ^ 2) * (1 + (t - b) ^ 2)) := by ring
    _ ≤ 4 * ((1 + (t - b) ^ 2) + (1 + (t - a) ^ 2)) * ((1 + (t - a) ^ 2) * (1 + (t - b) ^ 2)) := by
        gcongr
    _ = 4 * (1 * (1 + (t - b) ^ 2) + (1 + (t - a) ^ 2) * 1) * ((1 + (t - a) ^ 2) * (1 + (t - b) ^ 2)) := by
        ring

/-- (W5a) integrability of the product of two Cauchy kernels. -/
theorem cauchyConv_integrable (a b : ℝ) :
    Integrable (fun t : ℝ => 1 / ((1 + (t - a) ^ 2) * (1 + (t - b) ^ 2))) := by
  refine (integrable_inv_one_add_sq_sub a).mono'
    (continuous_const.div (by fun_prop) fun t => by positivity).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  have hp : 0 < 1 + (t - a) ^ 2 := by positivity
  have hq : 1 ≤ 1 + (t - b) ^ 2 := by nlinarith [sq_nonneg (t - b)]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), one_div_le_one_div (by positivity) hp]
  nlinarith

/-- (W5b) ∫ dt/((1+(t−a)²)(1+(t−b)²)) ≤ 32π/(4+(a−b)²)  (we even get 8π). -/
theorem cauchyConv_integral_le (a b : ℝ) :
    ∫ t : ℝ, 1 / ((1 + (t - a) ^ 2) * (1 + (t - b) ^ 2)) ≤ 32 * Real.pi / (4 + (a - b) ^ 2) := by
  have hD : 0 < 4 + (a - b) ^ 2 := by positivity
  have hmaj : Integrable (fun t : ℝ =>
      4 / (4 + (a - b) ^ 2) * (1 / (1 + (t - a) ^ 2) + 1 / (1 + (t - b) ^ 2))) :=
    ((integrable_inv_one_add_sq_sub a).add (integrable_inv_one_add_sq_sub b)).const_mul _
  calc ∫ t : ℝ, 1 / ((1 + (t - a) ^ 2) * (1 + (t - b) ^ 2))
      ≤ ∫ t : ℝ, 4 / (4 + (a - b) ^ 2) * (1 / (1 + (t - a) ^ 2) + 1 / (1 + (t - b) ^ 2)) :=
        integral_mono_of_nonneg (Eventually.of_forall fun t => by positivity) hmaj
          (Eventually.of_forall fun t => cauchyConv_pointwise a b t)
    _ = 4 / (4 + (a - b) ^ 2) * (Real.pi + Real.pi) := by
        rw [integral_const_mul, integral_add (integrable_inv_one_add_sq_sub a)
          (integrable_inv_one_add_sq_sub b), integral_inv_one_add_sq_sub, integral_inv_one_add_sq_sub]
    _ = 8 * Real.pi / (4 + (a - b) ^ 2) := by ring
    _ ≤ 32 * Real.pi / (4 + (a - b) ^ 2) := by
        gcongr; linarith [Real.pi_pos]

/-- **(W5)** the Cauchy convolution lemma, packaged (integrability and bound together). -/
theorem cauchyConv (a b : ℝ) :
    Integrable (fun t : ℝ => 1 / ((1 + (t - a) ^ 2) * (1 + (t - b) ^ 2))) ∧
    ∫ t : ℝ, 1 / ((1 + (t - a) ^ 2) * (1 + (t - b) ^ 2)) ≤ 32 * Real.pi / (4 + (a - b) ^ 2) :=
  ⟨cauchyConv_integrable a b, cauchyConv_integral_le a b⟩

/-- the same bound with the friendlier denominator 1 + (a−b)². -/
theorem cauchyConv_integral_le' (a b : ℝ) :
    ∫ t : ℝ, 1 / ((1 + (t - a) ^ 2) * (1 + (t - b) ^ 2)) ≤ 32 * Real.pi / (1 + (a - b) ^ 2) := by
  refine (cauchyConv_integral_le a b).trans ?_
  gcongr
  norm_num

theorem measurableSet_far (a R : ℝ) : MeasurableSet {t : ℝ | R ≤ |t - a|} :=
  (isClosed_le continuous_const (by fun_prop)).measurableSet

/-- **(W5, far region)**: for R > 0,  ∫_{|t−a| ≥ R} dt/((1+(t−a)²)(1+(t−b)²)) ≤ π/R². -/
theorem cauchyConv_far (a b : ℝ) {R : ℝ} (hR : 0 < R) :
    ∫ t in {t : ℝ | R ≤ |t - a|}, 1 / ((1 + (t - a) ^ 2) * (1 + (t - b) ^ 2))
      ≤ Real.pi / R ^ 2 := by
  have hg : Integrable (fun t : ℝ => 1 / R ^ 2 * (1 / (1 + (t - b) ^ 2))) :=
    (integrable_inv_one_add_sq_sub b).const_mul _
  calc ∫ t in {t : ℝ | R ≤ |t - a|}, 1 / ((1 + (t - a) ^ 2) * (1 + (t - b) ^ 2))
      ≤ ∫ t in {t : ℝ | R ≤ |t - a|}, 1 / R ^ 2 * (1 / (1 + (t - b) ^ 2)) := by
        refine setIntegral_mono_on (cauchyConv_integrable a b).integrableOn hg.integrableOn
          (measurableSet_far a R) fun t ht => ?_
        have ht : R ≤ |t - a| := ht
        have hq : 0 < 1 + (t - b) ^ 2 := by positivity
        have hRa : R ^ 2 ≤ 1 + (t - a) ^ 2 := by
          rw [← sq_abs (t - a)]; nlinarith [abs_nonneg (t - a)]
        rw [one_div_mul_one_div, one_div_le_one_div (by positivity) (by positivity)]
        exact mul_le_mul_of_nonneg_right hRa hq.le
    _ ≤ ∫ t : ℝ, 1 / R ^ 2 * (1 / (1 + (t - b) ^ 2)) :=
        setIntegral_le_integral hg (Eventually.of_forall fun t => by positivity)
    _ = Real.pi / R ^ 2 := by
        rw [integral_const_mul, integral_inv_one_add_sq_sub]; ring

/-! ## §B. paperFT helpers -/

/-- [eq:hfbound], first order: supp f ⊆ [−Λ, Λ], f ∈ C_c¹ ⇒ ‖h_f(z)‖·‖z‖ ≤ e^{|Im z|Λ}‖f′‖₁.
(Same statement and proof as Zeta23.Taper.norm_paperFT_mul_le.) -/
theorem norm_paperFT_mul_le {f : ℝ → ℂ} {Λ : ℝ} (hf : ContDiff ℝ 1 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) (z : ℂ) :
    ‖paperFT f z‖ * ‖z‖ ≤ Real.exp (|z.im| * Λ) * ∫ u, ‖deriv f u‖ := by
  have hcs : HasCompactSupport f := hasCompactSupport_of_support_subset_abs hsupp
  have hts := tsupport_subset_of_support_subset_abs hsupp
  have hsupp1 : ∀ u, deriv f u ≠ 0 → |u| ≤ Λ := by
    intro u hu
    have : u ∈ tsupport f := support_deriv_subset (Function.mem_support.mpr hu)
    exact abs_le.mpr (hts this)
  have hint : Integrable (deriv f) :=
    (hf.continuous_deriv le_rfl).integrable_of_hasCompactSupport hcs.deriv
  have := norm_paperFT_le hint hsupp1 z
  rw [paperFT_deriv hf hcs, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul,
    mul_comm] at this
  exact this

/-- [eq:hfbound], third order: f ∈ C_c³ ⇒ ‖h_f(z)‖·‖z‖³ ≤ e^{|Im z|Λ}‖f‴‖₁ (three integrations by parts). -/
theorem norm_paperFT_mul_cube_le {f : ℝ → ℂ} {Λ : ℝ} (hf : ContDiff ℝ 3 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) (z : ℂ) :
    ‖paperFT f z‖ * ‖z‖ ^ 3 ≤ Real.exp (|z.im| * Λ) * ∫ u, ‖deriv (deriv (deriv f)) u‖ := by
  have hcs : HasCompactSupport f := hasCompactSupport_of_support_subset_abs hsupp
  have hts := tsupport_subset_of_support_subset_abs hsupp
  have hsupp1 : ∀ u, deriv f u ≠ 0 → |u| ≤ Λ := by
    intro u hu
    have : u ∈ tsupport f := support_deriv_subset (Function.mem_support.mpr hu)
    exact abs_le.mpr (hts this)
  have h1 : ContDiff ℝ 2 (deriv f) := hf.deriv'
  have := norm_paperFT_mul_sq_le h1 hsupp1 z
  rw [paperFT_deriv (hf.of_le (by norm_num)) hcs, norm_mul, norm_neg, norm_mul, Complex.norm_I,
    one_mul] at this
  calc ‖paperFT f z‖ * ‖z‖ ^ 3 = ‖z‖ * ‖paperFT f z‖ * ‖z‖ ^ 2 := by ring
    _ ≤ _ := this

/-- paperFT of u ↦ k(−u) is paperFT k reflected. -/
theorem paperFT_comp_neg (k : ℝ → ℂ) (z : ℂ) : paperFT (fun u => k (-u)) z = paperFT k (-z) := by
  rw [paperFT_def, paperFT_def]
  refine Eq.trans (integral_congr_ae (Eventually.of_forall fun u => ?_))
    (integral_neg_eq_self (fun v : ℝ => k v * cexp (I * (-z) * v)) volume)
  show k (-u) * cexp (I * z * u) = k (-u) * cexp (I * (-z) * ((-u : ℝ) : ℂ))
  push_cast
  ring_nf

/-- H(5/4 + it) = h_k(t − 3i/4). -/
theorem Hfn_five_four (k : ℝ → ℂ) (t : ℝ) :
    Hfn k ((5 / 4 : ℂ) + t * I) = paperFT k ((t : ℂ) - 3 / 4 * I) := by
  unfold Hfn
  congr 1
  rw [div_eq_iff Complex.I_ne_zero]
  linear_combination (3 / 4 : ℂ) * Complex.I_sq

/-- bridge for consumers who spell the line point with a real 5/4: `((5/4:ℝ):ℂ) + t*I`. -/
theorem Hfn_five_four_ofReal (k : ℝ → ℂ) (t : ℝ) :
    Hfn k (((5 / 4 : ℝ) : ℂ) + t * I) = Hfn k ((5 / 4 : ℂ) + t * I) := by
  push_cast; rfl

/-- the mirrored weight on the line: H_{k∘neg}(5/4 + it) = h_k(−t + 3i/4). -/
theorem Hfn_five_four_neg (k : ℝ → ℂ) (t : ℝ) :
    Hfn (fun u => k (-u)) ((5 / 4 : ℂ) + t * I) = paperFT k (-(t : ℂ) + 3 / 4 * I) := by
  rw [Hfn_five_four, paperFT_comp_neg]
  congr 1
  ring

theorem line_re (x : ℝ) : ((x : ℂ) - 3 / 4 * I).re = x := by simp
theorem line_im (x : ℝ) : |((x : ℂ) - 3 / 4 * I).im| = 3 / 4 := by norm_num [Complex.sub_im]
theorem mline_re (x : ℝ) : (-(x : ℂ) + 3 / 4 * I).re = -x := by simp
theorem mline_im (x : ℝ) : |(-(x : ℂ) + 3 / 4 * I).im| = 3 / 4 := by norm_num [Complex.add_im]

/-! ## §C. The window at one good height -/

/-- What `FamilyHyps` gives at ONE height T ≥ T₁ (plus 1 ≤ L, 1 ≤ T), with a single constant C ≥ 1
bounding ‖φ′‖₁, ‖φ″‖₁, ‖φ‴‖₁.  Every estimate of §§D–H is proved under this hypothesis with an explicit
constant; `FamilyHyps.windowAt` produces it eventually in T. -/
structure WindowAt (P : Params) (T : ℝ) (C : ℝ) : Prop where
  one_le_T : 1 ≤ T
  one_le_L : 1 ≤ P.L T
  one_le_C : 1 ≤ C
  contDiff : ContDiff ℝ 3 (P.phi T)
  tsupport_subset : tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2)
  abs_le_one : ∀ u, |P.phi T u| ≤ 1
  deriv_le : ∫ u, |deriv (P.phi T) u| ≤ C
  deriv2_le : ∫ u, |deriv (deriv (P.phi T)) u| ≤ C
  deriv3_le : ∫ u, |deriv (deriv (deriv (P.phi T))) u| ≤ C

/-- `FamilyHyps` ⇒ the window facts hold at every large height, with one constant. -/
theorem _root_.Zeta23.XiPrime.FamilyHyps.windowAt {Pf : ℝ → Params} (hPf : FamilyHyps Pf) :
    ∃ C T₁ : ℝ, 1 ≤ C ∧ ∀ T : ℝ, T₁ ≤ T → WindowAt (Pf T) T C := by
  obtain ⟨lam, hlam0, _, hlam⟩ := hPf.lam_const
  obtain ⟨C, T₀, hW⟩ := hPf.window
  refine ⟨max C 1, max T₀ (max 1 (2 * Real.pi * Real.exp (1 / lam))), le_max_right _ _,
    fun T hT => ?_⟩
  have hT₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hT1 : 1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hTe : 2 * Real.pi * Real.exp (1 / lam) ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  obtain ⟨hcd, hsupp, -, habs, hder⟩ := hW T hT₀
  have hL : 1 ≤ (Pf T).L T := by
    have h2π : 0 < 2 * Real.pi := by positivity
    have hlog : 1 / lam ≤ Real.log (T / (2 * Real.pi)) := by
      rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ h2π]
      calc Real.exp (1 / lam) * (2 * Real.pi) = 2 * Real.pi * Real.exp (1 / lam) := mul_comm _ _
        _ ≤ T := hTe
    show 1 ≤ (Pf T).lam * l T
    rw [hlam T, l]
    calc (1 : ℝ) = lam * (1 / lam) := by field_simp
      _ ≤ lam * Real.log (T / (2 * Real.pi)) := mul_le_mul_of_nonneg_left hlog hlam0.le
  have hd : ∀ j : ℕ, 1 ≤ j → j ≤ 3 → ∫ u, |iteratedDeriv j ((Pf T).phi T) u| ≤ max C 1 :=
    fun j h1 h3 => ((hder j h1 h3).2).trans (le_max_left _ _)
  refine ⟨hT1, hL, le_max_right _ _, hcd, hsupp, habs, ?_, ?_, ?_⟩
  · simpa only [iteratedDeriv_one] using hd 1 le_rfl (by norm_num)
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hd 2 (by norm_num) (by norm_num)
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hd 3 (by norm_num) le_rfl

namespace WindowAt

variable {P : Params} {T C : ℝ}

theorem L_pos (h : WindowAt P T C) : 0 < P.L T := lt_of_lt_of_le one_pos h.one_le_L
theorem T_pos (h : WindowAt P T C) : 0 < T := lt_of_lt_of_le one_pos h.one_le_T
theorem C_nonneg (h : WindowAt P T C) : 0 ≤ C := le_trans zero_le_one h.one_le_C
theorem X_pos (_h : WindowAt P T C) : 0 < P.X T := Real.exp_pos _

/-! ### §D. φ as a complex function, and the two per-factor bounds -/

theorem phiC_contDiff (h : WindowAt P T C) : ContDiff ℝ 3 (fun u => (P.phi T u : ℂ)) :=
  ofRealCLM.contDiff.comp h.contDiff

theorem phiC_supp (h : WindowAt P T C) : ∀ u, (P.phi T u : ℂ) ≠ 0 → |u| ≤ P.L T / 2 := by
  intro u hu
  have hu' : P.phi T u ≠ 0 := fun h0 => hu (by rw [h0, Complex.ofReal_zero])
  exact abs_le.mpr (h.tsupport_subset (subset_tsupport _ (Function.mem_support.mpr hu')))

theorem phiC_hasCompactSupport (h : WindowAt P T C) : HasCompactSupport (fun u => (P.phi T u : ℂ)) :=
  hasCompactSupport_of_support_subset_abs h.phiC_supp

theorem phiC_integrable (h : WindowAt P T C) : Integrable (fun u => (P.phi T u : ℂ)) :=
  h.phiC_contDiff.continuous.integrable_of_hasCompactSupport h.phiC_hasCompactSupport

theorem norm_phiC_le_indicator (h : WindowAt P T C) (u : ℝ) :
    ‖(P.phi T u : ℂ)‖ ≤ (Icc (-(P.L T / 2)) (P.L T / 2)).indicator (fun _ => (1 : ℝ)) u := by
  by_cases hu : u ∈ Icc (-(P.L T / 2)) (P.L T / 2)
  · rw [indicator_of_mem hu, Complex.norm_real, Real.norm_eq_abs]
    exact h.abs_le_one u
  · have h0 : (P.phi T u : ℂ) = 0 := by
      by_contra hne
      exact hu (abs_le.mp (h.phiC_supp u hne))
    rw [indicator_of_notMem hu, h0, norm_zero]

/-- ‖φ‖₁ ≤ L (|φ| ≤ 1 on its support [−L/2, L/2]). -/
theorem integral_norm_phiC_le (h : WindowAt P T C) : ∫ u, ‖(P.phi T u : ℂ)‖ ≤ P.L T := by
  have hL := h.L_pos
  have hint : Integrable ((Icc (-(P.L T / 2)) (P.L T / 2)).indicator fun _ : ℝ => (1 : ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (continuous_const.continuousOn.integrableOn_compact isCompact_Icc)
  calc ∫ u, ‖(P.phi T u : ℂ)‖
      ≤ ∫ u, (Icc (-(P.L T / 2)) (P.L T / 2)).indicator (fun _ => (1 : ℝ)) u :=
        integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _) hint
          (Eventually.of_forall h.norm_phiC_le_indicator)
    _ = P.L T := by
        rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
          smul_eq_mul, mul_one]
        ring

theorem deriv_phiC (h : WindowAt P T C) :
    deriv (fun u => (P.phi T u : ℂ)) = fun u => ((deriv (P.phi T) u : ℝ) : ℂ) := by
  funext u
  exact ((h.contDiff.differentiable (by norm_num) u).hasDerivAt.ofReal_comp).deriv

theorem deriv2_phiC (h : WindowAt P T C) :
    deriv (deriv (fun u => (P.phi T u : ℂ))) = fun u => ((deriv (deriv (P.phi T)) u : ℝ) : ℂ) := by
  rw [h.deriv_phiC]
  funext u
  have hd : Differentiable ℝ (deriv (P.phi T)) :=
    (h.contDiff.deriv' (n := 2)).differentiable (by norm_num)
  exact ((hd u).hasDerivAt.ofReal_comp).deriv

theorem deriv3_phiC (h : WindowAt P T C) :
    deriv (deriv (deriv (fun u => (P.phi T u : ℂ))))
      = fun u => ((deriv (deriv (deriv (P.phi T))) u : ℝ) : ℂ) := by
  rw [h.deriv2_phiC]
  funext u
  have hd : Differentiable ℝ (deriv (deriv (P.phi T))) :=
    ((h.contDiff.deriv' (n := 2)).deriv' (n := 1)).differentiable (by norm_num)
  exact ((hd u).hasDerivAt.ofReal_comp).deriv

theorem integral_norm_deriv_phiC_le (h : WindowAt P T C) :
    ∫ u, ‖deriv (fun u => (P.phi T u : ℂ)) u‖ ≤ C := by
  rw [h.deriv_phiC]; simp only [Complex.norm_real, Real.norm_eq_abs]; exact h.deriv_le

theorem integral_norm_deriv2_phiC_le (h : WindowAt P T C) :
    ∫ u, ‖deriv (deriv (fun u => (P.phi T u : ℂ))) u‖ ≤ C := by
  rw [h.deriv2_phiC]; simp only [Complex.norm_real, Real.norm_eq_abs]; exact h.deriv2_le

theorem integral_norm_deriv3_phiC_le (h : WindowAt P T C) :
    ∫ u, ‖deriv (deriv (deriv (fun u => (P.phi T u : ℂ)))) u‖ ≤ C := by
  rw [h.deriv3_phiC]; simp only [Complex.norm_real, Real.norm_eq_abs]; exact h.deriv3_le

theorem re_sq_le_norm_sq (z : ℂ) : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm z) 2

/-- **per-factor bound (size)**: ‖φ̂(z)‖ (1 + (Re z)²) ≤ (1+C) e^{|Im z| L/2} L
(zeroth-order [eq:hfbound] with ‖φ‖₁ ≤ L, plus second-order with ‖φ″‖₁ ≤ C and (Re z)² ≤ ‖z‖², L ≥ 1). -/
theorem phiHat_bound (h : WindowAt P T C) (z : ℂ) :
    ‖P.phiHat T z‖ * (1 + z.re ^ 2) ≤ (1 + C) * Real.exp (|z.im| * (P.L T / 2)) * P.L T := by
  have he := Real.exp_pos (|z.im| * (P.L T / 2))
  have hL := h.one_le_L
  have hC := h.C_nonneg
  have h0 : ‖P.phiHat T z‖ ≤ Real.exp (|z.im| * (P.L T / 2)) * P.L T :=
    (norm_paperFT_le h.phiC_integrable h.phiC_supp z).trans
      (mul_le_mul_of_nonneg_left h.integral_norm_phiC_le he.le)
  have h2 : ‖P.phiHat T z‖ * ‖z‖ ^ 2 ≤ Real.exp (|z.im| * (P.L T / 2)) * C :=
    (norm_paperFT_mul_sq_le (h.phiC_contDiff.of_le (by norm_num)) h.phiC_supp z).trans
      (mul_le_mul_of_nonneg_left h.integral_norm_deriv2_phiC_le he.le)
  have hn : 0 ≤ ‖P.phiHat T z‖ := norm_nonneg _
  calc ‖P.phiHat T z‖ * (1 + z.re ^ 2) = ‖P.phiHat T z‖ + ‖P.phiHat T z‖ * z.re ^ 2 := by ring
    _ ≤ Real.exp (|z.im| * (P.L T / 2)) * P.L T + Real.exp (|z.im| * (P.L T / 2)) * C :=
        add_le_add h0 ((mul_le_mul_of_nonneg_left (re_sq_le_norm_sq z) hn).trans h2)
    _ ≤ (1 + C) * Real.exp (|z.im| * (P.L T / 2)) * P.L T := by
        nlinarith [mul_nonneg (mul_nonneg hC he.le) (sub_nonneg.mpr hL)]

/-- **per-factor bound (first moment)**: ‖z‖ ‖φ̂(z)‖ (1 + (Re z)²) ≤ 2C e^{|Im z| L/2}
(first- and third-order [eq:hfbound]: ‖φ′‖₁, ‖φ‴‖₁ ≤ C). -/
theorem phiHat_moment_bound (h : WindowAt P T C) (z : ℂ) :
    ‖z‖ * ‖P.phiHat T z‖ * (1 + z.re ^ 2) ≤ 2 * C * Real.exp (|z.im| * (P.L T / 2)) := by
  have he := Real.exp_pos (|z.im| * (P.L T / 2))
  have h1 : ‖P.phiHat T z‖ * ‖z‖ ≤ Real.exp (|z.im| * (P.L T / 2)) * C :=
    (norm_paperFT_mul_le (h.phiC_contDiff.of_le (by norm_num)) h.phiC_supp z).trans
      (mul_le_mul_of_nonneg_left h.integral_norm_deriv_phiC_le he.le)
  have h3 : ‖P.phiHat T z‖ * ‖z‖ ^ 3 ≤ Real.exp (|z.im| * (P.L T / 2)) * C :=
    (norm_paperFT_mul_cube_le h.phiC_contDiff h.phiC_supp z).trans
      (mul_le_mul_of_nonneg_left h.integral_norm_deriv3_phiC_le he.le)
  have hre := re_sq_le_norm_sq z
  calc ‖z‖ * ‖P.phiHat T z‖ * (1 + z.re ^ 2)
      = ‖P.phiHat T z‖ * ‖z‖ + ‖P.phiHat T z‖ * ‖z‖ * z.re ^ 2 := by ring
    _ ≤ ‖P.phiHat T z‖ * ‖z‖ + ‖P.phiHat T z‖ * ‖z‖ * ‖z‖ ^ 2 := by gcongr
    _ = ‖P.phiHat T z‖ * ‖z‖ + ‖P.phiHat T z‖ * ‖z‖ ^ 3 := by ring
    _ ≤ Real.exp (|z.im| * (P.L T / 2)) * C + Real.exp (|z.im| * (P.L T / 2)) * C := add_le_add h1 h3
    _ = 2 * C * Real.exp (|z.im| * (P.L T / 2)) := by ring

theorem norm_phiHat_le (h : WindowAt P T C) (z : ℂ) :
    ‖P.phiHat T z‖ ≤ (1 + C) * Real.exp (|z.im| * (P.L T / 2)) * P.L T / (1 + z.re ^ 2) := by
  rw [le_div_iff₀ (by positivity)]; exact h.phiHat_bound z

theorem abs_re_mul_norm_phiHat_le (h : WindowAt P T C) (z : ℂ) :
    |z.re| * ‖P.phiHat T z‖ ≤ 2 * C * Real.exp (|z.im| * (P.L T / 2)) / (1 + z.re ^ 2) := by
  rw [le_div_iff₀ (by positivity)]
  calc |z.re| * ‖P.phiHat T z‖ * (1 + z.re ^ 2) ≤ ‖z‖ * ‖P.phiHat T z‖ * (1 + z.re ^ 2) := by
        gcongr; exact Complex.abs_re_le_norm z
    _ ≤ _ := h.phiHat_moment_bound z

/-- X^{3/8} · X^{3/8} = X^{3/4}, X = e^L. -/
theorem exp_mul_exp_eq_X_rpow (P : Params) (T : ℝ) :
    Real.exp (3 / 4 * (P.L T / 2)) * Real.exp (3 / 4 * (P.L T / 2)) = P.X T ^ (3 / 4 : ℝ) := by
  rw [← Real.exp_add, Params.X, ← Real.exp_mul]; congr 1; ring

/-- the factor on the line Im z = −3/4:  ‖φ̂(x − 3i/4)‖ ≤ (1+C) X^{3/8} L/(1+x²). -/
theorem factor_le (h : WindowAt P T C) (x : ℝ) :
    ‖P.phiHat T ((x : ℂ) - 3 / 4 * I)‖ ≤ (1 + C) * Real.exp (3 / 4 * (P.L T / 2)) * P.L T / (1 + x ^ 2) := by
  have := h.norm_phiHat_le ((x : ℂ) - 3 / 4 * I); rwa [line_re, line_im] at this

theorem factor_moment_le (h : WindowAt P T C) (x : ℝ) :
    |x| * ‖P.phiHat T ((x : ℂ) - 3 / 4 * I)‖ ≤ 2 * C * Real.exp (3 / 4 * (P.L T / 2)) / (1 + x ^ 2) := by
  have := h.abs_re_mul_norm_phiHat_le ((x : ℂ) - 3 / 4 * I); rwa [line_re, line_im] at this

/-- the factor on the mirrored line:  ‖φ̂(−x + 3i/4)‖ ≤ (1+C) X^{3/8} L/(1+x²). -/
theorem mfactor_le (h : WindowAt P T C) (x : ℝ) :
    ‖P.phiHat T (-(x : ℂ) + 3 / 4 * I)‖ ≤ (1 + C) * Real.exp (3 / 4 * (P.L T / 2)) * P.L T / (1 + x ^ 2) := by
  have := h.norm_phiHat_le (-(x : ℂ) + 3 / 4 * I); rwa [mline_re, mline_im, neg_sq] at this

theorem mfactor_moment_le (h : WindowAt P T C) (x : ℝ) :
    |x| * ‖P.phiHat T (-(x : ℂ) + 3 / 4 * I)‖ ≤ 2 * C * Real.exp (3 / 4 * (P.L T / 2)) / (1 + x ^ 2) := by
  have := h.abs_re_mul_norm_phiHat_le (-(x : ℂ) + 3 / 4 * I)
  rwa [mline_re, mline_im, neg_sq, abs_neg] at this

/-- the factor on the real line (no exponential): ‖φ̂(x)‖ ≤ (1+C) L/(1+x²). -/
theorem rfactor_le (h : WindowAt P T C) (x : ℝ) :
    ‖P.phiHat T x‖ ≤ (1 + C) * P.L T / (1 + x ^ 2) := by
  have := h.norm_phiHat_le (x : ℂ)
  simpa only [Complex.ofReal_re, Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, mul_one] using this

end WindowAt

end TestWeight

/-! ## §E. The Weil test function k = f_k ⋆ f̃_l and its transform -/


namespace TestWeight
namespace WindowAt

variable {P : Params} {T C : ℝ}

theorem fk_contDiff (h : WindowAt P T C) (k : ℤ) : ContDiff ℝ 2 (P.fk T k) :=
  GzGp.fk_contDiff P T (h.phiC_contDiff.of_le (by norm_num)) k

theorem fk_tsupport (h : WindowAt P T C) (k : ℤ) :
    tsupport (P.fk T k) ⊆ Icc (-(P.L T / 2)) (P.L T / 2) :=
  GzGp.fk_tsupport P T h.tsupport_subset k

theorem fk_hasCompactSupport (h : WindowAt P T C) (k : ℤ) : HasCompactSupport (P.fk T k) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (h.fk_tsupport k)

theorem fk_continuous (h : WindowAt P T C) (k : ℤ) : Continuous (P.fk T k) :=
  (h.fk_contDiff k).continuous

/-- (W0) k ∈ C². -/
theorem kfun_contDiff (h : WindowAt P T C) (k l : ℤ) : ContDiff ℝ 2 (kfun P T k l) :=
  EF.weilTest_contDiff (h.fk_contDiff k) (h.fk_continuous l) (h.fk_hasCompactSupport k)

/-- (W0) k has compact support. -/
theorem kfun_hasCompactSupport (h : WindowAt P T C) (k l : ℤ) : HasCompactSupport (kfun P T k l) :=
  EF.weilTest_hasCompactSupport (h.fk_hasCompactSupport k) (h.fk_hasCompactSupport l)

/-- (W0) tsupport k ⊆ [−L, L]. -/
theorem kfun_tsupport (h : WindowAt P T C) (k l : ℤ) :
    tsupport (kfun P T k l) ⊆ Icc (-P.L T) (P.L T) :=
  EF.tsupport_weilTest_subset (h.fk_tsupport k) (h.fk_tsupport l)

theorem kfun_continuous (h : WindowAt P T C) (k l : ℤ) : Continuous (kfun P T k l) :=
  (h.kfun_contDiff k l).continuous

theorem kfun_integrable (h : WindowAt P T C) (k l : ℤ) : Integrable (kfun P T k l) :=
  (h.kfun_continuous k l).integrable_of_hasCompactSupport (h.kfun_hasCompactSupport k l)

/-- (W0, mirrored) u ↦ k(−u) ∈ C². -/
theorem kfun_neg_contDiff (h : WindowAt P T C) (k l : ℤ) :
    ContDiff ℝ 2 (fun u => kfun P T k l (-u)) :=
  (h.kfun_contDiff k l).comp contDiff_neg

theorem kfun_neg_hasCompactSupport (h : WindowAt P T C) (k l : ℤ) :
    HasCompactSupport (fun u => kfun P T k l (-u)) :=
  (h.kfun_hasCompactSupport k l).comp_homeomorph (Homeomorph.neg ℝ)

theorem kfun_neg_tsupport (h : WindowAt P T C) (k l : ℤ) :
    tsupport (fun u => kfun P T k l (-u)) ⊆ Icc (-P.L T) (P.L T) := by
  refine closure_minimal ?_ isClosed_Icc
  intro u hu
  have hu' : -u ∈ tsupport (kfun P T k l) :=
    subset_tsupport _ (by simpa [Function.mem_support] using hu)
  have := h.kfun_tsupport k l hu'
  simp only [mem_Icc] at this ⊢
  constructor <;> linarith [this.1, this.2]

/-- **[XF′ Lemma 3.1]**  h_k(z) = φ̂(z − τ_k) · φ̂(z − τ_l)  for all complex z
(h_{f⋆g̃}(z) = h_f(z)·conj h_g(z̄), h_{f_k}(z) = φ̂(z − τ_k), and conj φ̂(z̄) = φ̂(z) as φ is real and even). -/
theorem paperFT_kfun (h : WindowAt P T C) (k l : ℤ) (z : ℂ) :
    paperFT (kfun P T k l) z = P.phiHat T (z - P.tau T k) * P.phiHat T (z - P.tau T l) := by
  unfold kfun
  rw [EF.paperFT_weilTest (h.fk_continuous k) (h.fk_continuous l) (h.fk_hasCompactSupport k)
      (h.fk_hasCompactSupport l),
    GzGp.paperFT_fk, GzGp.paperFT_fk, ← Complex.conj_ofReal (P.tau T l), ← map_sub,
    GzGp.phiHat_conj, Complex.conj_conj, Complex.conj_ofReal]

/-- the weight on the line Re s = 5/4:  H(5/4+it) = φ̂((t−τ_k) − 3i/4) · φ̂((t−τ_l) − 3i/4). -/
theorem Hfn_kfun (h : WindowAt P T C) (k l : ℤ) (t : ℝ) :
    Hfn (kfun P T k l) ((5 / 4 : ℂ) + t * I)
      = P.phiHat T (((t - P.tau T k : ℝ) : ℂ) - 3 / 4 * I)
        * P.phiHat T (((t - P.tau T l : ℝ) : ℂ) - 3 / 4 * I) := by
  rw [Hfn_five_four, h.paperFT_kfun]
  congr 2 <;> (push_cast; ring)

/-- the mirrored weight on the line:  H_{k∘neg}(5/4+it) = φ̂(−(t+τ_k) + 3i/4) · φ̂(−(t+τ_l) + 3i/4). -/
theorem Hfn_kfun_neg (h : WindowAt P T C) (k l : ℤ) (t : ℝ) :
    Hfn (fun u => kfun P T k l (-u)) ((5 / 4 : ℂ) + t * I)
      = P.phiHat T (-((t + P.tau T k : ℝ) : ℂ) + 3 / 4 * I)
        * P.phiHat T (-((t + P.tau T l : ℝ) : ℂ) + 3 / 4 * I) := by
  rw [Hfn_five_four_neg, h.paperFT_kfun]
  congr 2 <;> (push_cast; ring)

/-! ## §F. (W1)–(W3): pointwise bounds on the line Re s = 5/4 -/

/-- **(W1)** ‖H(5/4+it)‖ ≤ (1+C)² X^{3/4} L² / ((1+(t−τ_k)²)(1+(t−τ_l)²)). -/
theorem norm_Hfn_kfun_le (h : WindowAt P T C) (k l : ℤ) (t : ℝ) :
    ‖Hfn (kfun P T k l) ((5 / 4 : ℂ) + t * I)‖
      ≤ (1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2 /
          ((1 + (t - P.tau T k) ^ 2) * (1 + (t - P.tau T l) ^ 2)) := by
  have hC := h.C_nonneg
  have hL := h.L_pos
  rw [h.Hfn_kfun, norm_mul]
  calc ‖P.phiHat T (((t - P.tau T k : ℝ) : ℂ) - 3 / 4 * I)‖
        * ‖P.phiHat T (((t - P.tau T l : ℝ) : ℂ) - 3 / 4 * I)‖
      ≤ ((1 + C) * Real.exp (3 / 4 * (P.L T / 2)) * P.L T / (1 + (t - P.tau T k) ^ 2))
        * ((1 + C) * Real.exp (3 / 4 * (P.L T / 2)) * P.L T / (1 + (t - P.tau T l) ^ 2)) :=
        mul_le_mul (h.factor_le _) (h.factor_le _) (norm_nonneg _) (by positivity)
    _ = (1 + C) ^ 2 * (Real.exp (3 / 4 * (P.L T / 2)) * Real.exp (3 / 4 * (P.L T / 2))) * P.L T ^ 2 /
          ((1 + (t - P.tau T k) ^ 2) * (1 + (t - P.tau T l) ^ 2)) := by
        rw [div_mul_div_comm]; ring
    _ = _ := by rw [exp_mul_exp_eq_X_rpow]

/-- **(W2)** (|t−τ_k| + |t−τ_l|) ‖H(5/4+it)‖ ≤ 4C(1+C) X^{3/4} L / ((1+(t−τ_k)²)(1+(t−τ_l)²)). -/
theorem moment_norm_Hfn_kfun_le (h : WindowAt P T C) (k l : ℤ) (t : ℝ) :
    (|t - P.tau T k| + |t - P.tau T l|) * ‖Hfn (kfun P T k l) ((5 / 4 : ℂ) + t * I)‖
      ≤ 4 * C * (1 + C) * P.X T ^ (3 / 4 : ℝ) * P.L T /
          ((1 + (t - P.tau T k) ^ 2) * (1 + (t - P.tau T l) ^ 2)) := by
  have hC := h.C_nonneg
  have hL := h.L_pos
  rw [h.Hfn_kfun, norm_mul, ← exp_mul_exp_eq_X_rpow]
  set A := ‖P.phiHat T (((t - P.tau T k : ℝ) : ℂ) - 3 / 4 * I)‖
  set B := ‖P.phiHat T (((t - P.tau T l : ℝ) : ℂ) - 3 / 4 * I)‖
  set e := Real.exp (3 / 4 * (P.L T / 2))
  have hA := h.factor_le (t - P.tau T k)
  have hA' := h.factor_moment_le (t - P.tau T k)
  have hB := h.factor_le (t - P.tau T l)
  have hB' := h.factor_moment_le (t - P.tau T l)
  have hp : 0 < 1 + (t - P.tau T k) ^ 2 := by positivity
  have hq : 0 < 1 + (t - P.tau T l) ^ 2 := by positivity
  calc (|t - P.tau T k| + |t - P.tau T l|) * (A * B)
      = (|t - P.tau T k| * A) * B + A * (|t - P.tau T l| * B) := by ring
    _ ≤ (2 * C * e / (1 + (t - P.tau T k) ^ 2)) * ((1 + C) * e * P.L T / (1 + (t - P.tau T l) ^ 2))
        + ((1 + C) * e * P.L T / (1 + (t - P.tau T k) ^ 2)) * (2 * C * e / (1 + (t - P.tau T l) ^ 2)) :=
        add_le_add (mul_le_mul hA' hB (by positivity) (by positivity))
          (mul_le_mul hA hB' (by positivity) (by positivity))
    _ = 4 * C * (1 + C) * (e * e) * P.L T / ((1 + (t - P.tau T k) ^ 2) * (1 + (t - P.tau T l) ^ 2)) := by
        field_simp
        ring

/-- **(W3, size)** the mirrored weight: ‖H_{k∘neg}(5/4+it)‖ ≤ (1+C)² X^{3/4} L² / ((1+(t+τ_k)²)(1+(t+τ_l)²)). -/
theorem norm_Hfn_kfun_neg_le (h : WindowAt P T C) (k l : ℤ) (t : ℝ) :
    ‖Hfn (fun u => kfun P T k l (-u)) ((5 / 4 : ℂ) + t * I)‖
      ≤ (1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2 /
          ((1 + (t + P.tau T k) ^ 2) * (1 + (t + P.tau T l) ^ 2)) := by
  have hC := h.C_nonneg
  have hL := h.L_pos
  rw [h.Hfn_kfun_neg, norm_mul]
  calc ‖P.phiHat T (-((t + P.tau T k : ℝ) : ℂ) + 3 / 4 * I)‖
        * ‖P.phiHat T (-((t + P.tau T l : ℝ) : ℂ) + 3 / 4 * I)‖
      ≤ ((1 + C) * Real.exp (3 / 4 * (P.L T / 2)) * P.L T / (1 + (t + P.tau T k) ^ 2))
        * ((1 + C) * Real.exp (3 / 4 * (P.L T / 2)) * P.L T / (1 + (t + P.tau T l) ^ 2)) :=
        mul_le_mul (h.mfactor_le _) (h.mfactor_le _) (norm_nonneg _) (by positivity)
    _ = (1 + C) ^ 2 * (Real.exp (3 / 4 * (P.L T / 2)) * Real.exp (3 / 4 * (P.L T / 2))) * P.L T ^ 2 /
          ((1 + (t + P.tau T k) ^ 2) * (1 + (t + P.tau T l) ^ 2)) := by
        rw [div_mul_div_comm]; ring
    _ = _ := by rw [exp_mul_exp_eq_X_rpow]

/-- **(W3, first moment)** (|t+τ_k| + |t+τ_l|) ‖H_{k∘neg}(5/4+it)‖ ≤ 4C(1+C) X^{3/4} L / (…). -/
theorem moment_norm_Hfn_kfun_neg_le (h : WindowAt P T C) (k l : ℤ) (t : ℝ) :
    (|t + P.tau T k| + |t + P.tau T l|) * ‖Hfn (fun u => kfun P T k l (-u)) ((5 / 4 : ℂ) + t * I)‖
      ≤ 4 * C * (1 + C) * P.X T ^ (3 / 4 : ℝ) * P.L T /
          ((1 + (t + P.tau T k) ^ 2) * (1 + (t + P.tau T l) ^ 2)) := by
  have hC := h.C_nonneg
  have hL := h.L_pos
  rw [h.Hfn_kfun_neg, norm_mul, ← exp_mul_exp_eq_X_rpow]
  set A := ‖P.phiHat T (-((t + P.tau T k : ℝ) : ℂ) + 3 / 4 * I)‖
  set B := ‖P.phiHat T (-((t + P.tau T l : ℝ) : ℂ) + 3 / 4 * I)‖
  set e := Real.exp (3 / 4 * (P.L T / 2))
  have hA := h.mfactor_le (t + P.tau T k)
  have hA' := h.mfactor_moment_le (t + P.tau T k)
  have hB := h.mfactor_le (t + P.tau T l)
  have hB' := h.mfactor_moment_le (t + P.tau T l)
  have hp : 0 < 1 + (t + P.tau T k) ^ 2 := by positivity
  have hq : 0 < 1 + (t + P.tau T l) ^ 2 := by positivity
  calc (|t + P.tau T k| + |t + P.tau T l|) * (A * B)
      = (|t + P.tau T k| * A) * B + A * (|t + P.tau T l| * B) := by ring
    _ ≤ (2 * C * e / (1 + (t + P.tau T k) ^ 2)) * ((1 + C) * e * P.L T / (1 + (t + P.tau T l) ^ 2))
        + ((1 + C) * e * P.L T / (1 + (t + P.tau T k) ^ 2)) * (2 * C * e / (1 + (t + P.tau T l) ^ 2)) :=
        add_le_add (mul_le_mul hA' hB (by positivity) (by positivity))
          (mul_le_mul hA hB' (by positivity) (by positivity))
    _ = 4 * C * (1 + C) * (e * e) * P.L T / ((1 + (t + P.tau T k) ^ 2) * (1 + (t + P.tau T l) ^ 2)) := by
        field_simp
        ring

/-! ## §G. (W4): the transform on the real line -/

/-- **(W4)** on ℝ the transform is the real number φ̂_ℝ(τ−τ_k) φ̂_ℝ(τ−τ_l). -/
theorem paperFT_kfun_ofReal (h : WindowAt P T C) (k l : ℤ) (τ : ℝ) :
    paperFT (kfun P T k l) τ
      = ((P.phiHatR T (τ - P.tau T k) * P.phiHatR T (τ - P.tau T l) : ℝ) : ℂ) := by
  rw [h.paperFT_kfun, ← Complex.ofReal_sub, ← Complex.ofReal_sub, GzGp.phiHat_ofReal,
    GzGp.phiHat_ofReal, Complex.ofReal_mul]

theorem norm_paperFT_kfun_ofReal_le (h : WindowAt P T C) (k l : ℤ) (τ : ℝ) :
    ‖paperFT (kfun P T k l) τ‖
      ≤ (1 + C) ^ 2 * P.L T ^ 2 / ((1 + (τ - P.tau T k) ^ 2) * (1 + (τ - P.tau T l) ^ 2)) := by
  have hC := h.C_nonneg
  have hL := h.L_pos
  rw [h.paperFT_kfun, norm_mul, ← Complex.ofReal_sub, ← Complex.ofReal_sub]
  calc ‖P.phiHat T ((τ - P.tau T k : ℝ) : ℂ)‖ * ‖P.phiHat T ((τ - P.tau T l : ℝ) : ℂ)‖
      ≤ ((1 + C) * P.L T / (1 + (τ - P.tau T k) ^ 2)) * ((1 + C) * P.L T / (1 + (τ - P.tau T l) ^ 2)) :=
        mul_le_mul (h.rfactor_le _) (h.rfactor_le _) (norm_nonneg _) (by positivity)
    _ = _ := by rw [div_mul_div_comm]; ring

theorem continuous_paperFT_kfun_ofReal (h : WindowAt P T C) (k l : ℤ) :
    Continuous (fun τ : ℝ => paperFT (kfun P T k l) τ) :=
  (WeilEF.differentiable_paperFT (h.kfun_continuous k l) (h.kfun_hasCompactSupport k l)).continuous.comp
    Complex.continuous_ofReal

/-- **(W4)** h_k is integrable on ℝ. -/
theorem integrable_paperFT_kfun_ofReal (h : WindowAt P T C) (k l : ℤ) :
    Integrable (fun τ : ℝ => paperFT (kfun P T k l) τ) := by
  refine ((cauchyConv_integrable (P.tau T k) (P.tau T l)).const_mul ((1 + C) ^ 2 * P.L T ^ 2)).mono'
    (h.continuous_paperFT_kfun_ofReal k l).aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
  rw [mul_one_div]
  exact h.norm_paperFT_kfun_ofReal_le k l τ

/-- **(W4)** ∫‖h_k‖ ≤ 32π (1+C)² L² / (1 + (τ_k − τ_l)²). -/
theorem integral_norm_paperFT_kfun_ofReal_le (h : WindowAt P T C) (k l : ℤ) :
    ∫ τ : ℝ, ‖paperFT (kfun P T k l) τ‖
      ≤ 32 * Real.pi * (1 + C) ^ 2 * P.L T ^ 2 / (1 + (P.tau T k - P.tau T l) ^ 2) := by
  have hC := h.C_nonneg
  have hL := h.L_pos
  calc ∫ τ : ℝ, ‖paperFT (kfun P T k l) τ‖
      ≤ ∫ τ : ℝ, (1 + C) ^ 2 * P.L T ^ 2 * (1 / ((1 + (τ - P.tau T k) ^ 2) * (1 + (τ - P.tau T l) ^ 2))) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          ((cauchyConv_integrable _ _).const_mul _)
          (Eventually.of_forall fun τ => by
            beta_reduce; rw [mul_one_div]; exact h.norm_paperFT_kfun_ofReal_le k l τ)
    _ = (1 + C) ^ 2 * P.L T ^ 2 * ∫ τ : ℝ, 1 / ((1 + (τ - P.tau T k) ^ 2) * (1 + (τ - P.tau T l) ^ 2)) :=
        integral_const_mul _ _
    _ ≤ (1 + C) ^ 2 * P.L T ^ 2 * (32 * Real.pi / (1 + (P.tau T k - P.tau T l) ^ 2)) :=
        mul_le_mul_of_nonneg_left (cauchyConv_integral_le' _ _) (by positivity)
    _ = _ := by ring

/-! ## §H. (W6): integrated consequences on the line Re s = 5/4 -/

theorem continuous_Hfn_kfun (h : WindowAt P T C) (k l : ℤ) :
    Continuous (fun t : ℝ => Hfn (kfun P T k l) ((5 / 4 : ℂ) + t * I)) := by
  have hc := (WeilEF.differentiable_paperFT (h.kfun_continuous k l) (h.kfun_hasCompactSupport k l)).continuous
  unfold Hfn
  exact hc.comp (by fun_prop)

theorem continuous_Hfn_kfun_neg (h : WindowAt P T C) (k l : ℤ) :
    Continuous (fun t : ℝ => Hfn (fun u => kfun P T k l (-u)) ((5 / 4 : ℂ) + t * I)) := by
  have hc := (WeilEF.differentiable_paperFT ((h.kfun_neg_contDiff k l).continuous)
    (h.kfun_neg_hasCompactSupport k l)).continuous
  unfold Hfn
  exact hc.comp (by fun_prop)

/-- (W6) t ↦ H(5/4+it) is integrable. -/
theorem integrable_Hfn_kfun (h : WindowAt P T C) (k l : ℤ) :
    Integrable (fun t : ℝ => Hfn (kfun P T k l) ((5 / 4 : ℂ) + t * I)) := by
  refine ((cauchyConv_integrable (P.tau T k) (P.tau T l)).const_mul
      ((1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2)).mono'
    (h.continuous_Hfn_kfun k l).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [mul_one_div]
  exact h.norm_Hfn_kfun_le k l t

theorem integrable_Hfn_kfun_neg (h : WindowAt P T C) (k l : ℤ) :
    Integrable (fun t : ℝ => Hfn (fun u => kfun P T k l (-u)) ((5 / 4 : ℂ) + t * I)) := by
  refine ((cauchyConv_integrable (-P.tau T k) (-P.tau T l)).const_mul
      ((1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2)).mono'
    (h.continuous_Hfn_kfun_neg k l).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [mul_one_div, sub_neg_eq_add, sub_neg_eq_add]
  exact h.norm_Hfn_kfun_neg_le k l t

/-- **(W6a)** ∫‖H(5/4+it)‖dt ≤ 32π(1+C)² X^{3/4} L² / (1+(τ_k−τ_l)²). -/
theorem integral_norm_Hfn_kfun_le (h : WindowAt P T C) (k l : ℤ) :
    ∫ t : ℝ, ‖Hfn (kfun P T k l) ((5 / 4 : ℂ) + t * I)‖
      ≤ 32 * Real.pi * (1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2 / (1 + (P.tau T k - P.tau T l) ^ 2) := by
  have hC := h.C_nonneg
  have hL := h.L_pos
  have hX := h.X_pos
  calc ∫ t : ℝ, ‖Hfn (kfun P T k l) ((5 / 4 : ℂ) + t * I)‖
      ≤ ∫ t : ℝ, (1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2
          * (1 / ((1 + (t - P.tau T k) ^ 2) * (1 + (t - P.tau T l) ^ 2))) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          ((cauchyConv_integrable _ _).const_mul _)
          (Eventually.of_forall fun t => by beta_reduce; rw [mul_one_div]; exact h.norm_Hfn_kfun_le k l t)
    _ = (1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2
          * ∫ t : ℝ, 1 / ((1 + (t - P.tau T k) ^ 2) * (1 + (t - P.tau T l) ^ 2)) :=
        integral_const_mul _ _
    _ ≤ (1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2 * (32 * Real.pi / (1 + (P.tau T k - P.tau T l) ^ 2)) :=
        mul_le_mul_of_nonneg_left (cauchyConv_integral_le' _ _) (by positivity)
    _ = _ := by ring

/-- **(W6a, mirrored)** ∫‖H_{k∘neg}(5/4+it)‖dt ≤ 32π(1+C)² X^{3/4} L² / (1+(τ_k−τ_l)²). -/
theorem integral_norm_Hfn_kfun_neg_le (h : WindowAt P T C) (k l : ℤ) :
    ∫ t : ℝ, ‖Hfn (fun u => kfun P T k l (-u)) ((5 / 4 : ℂ) + t * I)‖
      ≤ 32 * Real.pi * (1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2 / (1 + (P.tau T k - P.tau T l) ^ 2) := by
  have hC := h.C_nonneg
  have hL := h.L_pos
  have hX := h.X_pos
  calc ∫ t : ℝ, ‖Hfn (fun u => kfun P T k l (-u)) ((5 / 4 : ℂ) + t * I)‖
      ≤ ∫ t : ℝ, (1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2
          * (1 / ((1 + (t - -P.tau T k) ^ 2) * (1 + (t - -P.tau T l) ^ 2))) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          ((cauchyConv_integrable _ _).const_mul _)
          (Eventually.of_forall fun t => by
            beta_reduce; rw [mul_one_div, sub_neg_eq_add, sub_neg_eq_add]; exact h.norm_Hfn_kfun_neg_le k l t)
    _ = (1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2
          * ∫ t : ℝ, 1 / ((1 + (t - -P.tau T k) ^ 2) * (1 + (t - -P.tau T l) ^ 2)) :=
        integral_const_mul _ _
    _ ≤ (1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2
          * (32 * Real.pi / (1 + (-P.tau T k - -P.tau T l) ^ 2)) :=
        mul_le_mul_of_nonneg_left (cauchyConv_integral_le' _ _) (by positivity)
    _ = _ := by ring

theorem abs_sub_tauStar_le (P : Params) (T : ℝ) (k l : ℤ) (t : ℝ) :
    |t - P.tauStar T k l| ≤ (|t - P.tau T k| + |t - P.tau T l|) / 2 := by
  have : t - P.tauStar T k l = ((t - P.tau T k) + (t - P.tau T l)) / 2 := by
    unfold Params.tauStar; ring
  rw [this, abs_div, abs_two]
  gcongr
  exact abs_add_le _ _

theorem abs_add_tauStar_le (P : Params) (T : ℝ) (k l : ℤ) (t : ℝ) :
    |t + P.tauStar T k l| ≤ (|t + P.tau T k| + |t + P.tau T l|) / 2 := by
  have : t + P.tauStar T k l = ((t + P.tau T k) + (t + P.tau T l)) / 2 := by
    unfold Params.tauStar; ring
  rw [this, abs_div, abs_two]
  gcongr
  exact abs_add_le _ _

/-- **(W6b, pointwise)** (1+|t−τ⋆|)‖H(5/4+it)‖ ≤ (1+C)(1+3C) X^{3/4} L² / ((1+(t−τ_k)²)(1+(t−τ_l)²)). -/
theorem weighted_norm_Hfn_kfun_le (h : WindowAt P T C) (k l : ℤ) (t : ℝ) :
    (1 + |t - P.tauStar T k l|) * ‖Hfn (kfun P T k l) ((5 / 4 : ℂ) + t * I)‖
      ≤ (1 + C) * (1 + 3 * C) * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2 /
          ((1 + (t - P.tau T k) ^ 2) * (1 + (t - P.tau T l) ^ 2)) := by
  have hC := h.C_nonneg
  have hL := h.one_le_L
  have hX := h.X_pos
  have hXr : 0 ≤ P.X T ^ (3 / 4 : ℝ) := Real.rpow_nonneg hX.le _
  have h1 := h.norm_Hfn_kfun_le k l t
  have h2 := h.moment_norm_Hfn_kfun_le k l t
  have hts := abs_sub_tauStar_le P T k l t
  set D := (1 + (t - P.tau T k) ^ 2) * (1 + (t - P.tau T l) ^ 2)
  have hD : 0 < D := by positivity
  set N := ‖Hfn (kfun P T k l) ((5 / 4 : ℂ) + t * I)‖
  have hN : 0 ≤ N := norm_nonneg _
  calc (1 + |t - P.tauStar T k l|) * N
      ≤ N + (1 / 2) * ((|t - P.tau T k| + |t - P.tau T l|) * N) := by nlinarith
    _ ≤ (1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2 / D
        + (1 / 2) * (4 * C * (1 + C) * P.X T ^ (3 / 4 : ℝ) * P.L T / D) := by gcongr
    _ = ((1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2 + 2 * C * (1 + C) * P.X T ^ (3 / 4 : ℝ) * P.L T) / D := by
        ring
    _ ≤ ((1 + C) * (1 + 3 * C) * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2) / D := by
        gcongr
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hC (by linarith : (0:ℝ) ≤ 1 + C)) hXr)
          (mul_nonneg (by linarith : (0:ℝ) ≤ P.L T) (sub_nonneg.mpr hL))]

/-- **(W6b, pointwise, mirrored)** (1+|t+τ⋆|)‖H_{k∘neg}(5/4+it)‖ ≤ (1+C)(1+3C) X^{3/4} L² / (…). -/
theorem weighted_norm_Hfn_kfun_neg_le (h : WindowAt P T C) (k l : ℤ) (t : ℝ) :
    (1 + |t + P.tauStar T k l|) * ‖Hfn (fun u => kfun P T k l (-u)) ((5 / 4 : ℂ) + t * I)‖
      ≤ (1 + C) * (1 + 3 * C) * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2 /
          ((1 + (t + P.tau T k) ^ 2) * (1 + (t + P.tau T l) ^ 2)) := by
  have hC := h.C_nonneg
  have hL := h.one_le_L
  have hX := h.X_pos
  have hXr : 0 ≤ P.X T ^ (3 / 4 : ℝ) := Real.rpow_nonneg hX.le _
  have h1 := h.norm_Hfn_kfun_neg_le k l t
  have h2 := h.moment_norm_Hfn_kfun_neg_le k l t
  have hts := abs_add_tauStar_le P T k l t
  set D := (1 + (t + P.tau T k) ^ 2) * (1 + (t + P.tau T l) ^ 2)
  have hD : 0 < D := by positivity
  set N := ‖Hfn (fun u => kfun P T k l (-u)) ((5 / 4 : ℂ) + t * I)‖
  have hN : 0 ≤ N := norm_nonneg _
  calc (1 + |t + P.tauStar T k l|) * N
      ≤ N + (1 / 2) * ((|t + P.tau T k| + |t + P.tau T l|) * N) := by nlinarith
    _ ≤ (1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2 / D
        + (1 / 2) * (4 * C * (1 + C) * P.X T ^ (3 / 4 : ℝ) * P.L T / D) := by gcongr
    _ = ((1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2 + 2 * C * (1 + C) * P.X T ^ (3 / 4 : ℝ) * P.L T) / D := by
        ring
    _ ≤ ((1 + C) * (1 + 3 * C) * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2) / D := by
        gcongr
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hC (by linarith : (0:ℝ) ≤ 1 + C)) hXr)
          (mul_nonneg (by linarith : (0:ℝ) ≤ P.L T) (sub_nonneg.mpr hL))]

theorem integrable_weighted_norm_Hfn_kfun (h : WindowAt P T C) (k l : ℤ) :
    Integrable (fun t : ℝ => (1 + |t - P.tauStar T k l|) * ‖Hfn (kfun P T k l) ((5 / 4 : ℂ) + t * I)‖) := by
  refine ((cauchyConv_integrable (P.tau T k) (P.tau T l)).const_mul
      ((1 + C) * (1 + 3 * C) * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2)).mono'
    (((continuous_const.add (by fun_prop)).mul (h.continuous_Hfn_kfun k l).norm).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_one_div]
  exact h.weighted_norm_Hfn_kfun_le k l t

theorem integrable_weighted_norm_Hfn_kfun_neg (h : WindowAt P T C) (k l : ℤ) :
    Integrable (fun t : ℝ =>
      (1 + |t + P.tauStar T k l|) * ‖Hfn (fun u => kfun P T k l (-u)) ((5 / 4 : ℂ) + t * I)‖) := by
  refine ((cauchyConv_integrable (-P.tau T k) (-P.tau T l)).const_mul
      ((1 + C) * (1 + 3 * C) * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2)).mono'
    (((continuous_const.add (by fun_prop)).mul (h.continuous_Hfn_kfun_neg k l).norm).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_one_div, sub_neg_eq_add, sub_neg_eq_add]
  exact h.weighted_norm_Hfn_kfun_neg_le k l t

/-- **(W6b)** ∫(1+|t−τ⋆|)‖H(5/4+it)‖dt ≤ 32π(1+C)(1+3C) X^{3/4} L² / (1+(τ_k−τ_l)²). -/
theorem integral_weighted_norm_Hfn_kfun_le (h : WindowAt P T C) (k l : ℤ) :
    ∫ t : ℝ, (1 + |t - P.tauStar T k l|) * ‖Hfn (kfun P T k l) ((5 / 4 : ℂ) + t * I)‖
      ≤ 32 * Real.pi * ((1 + C) * (1 + 3 * C)) * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2
          / (1 + (P.tau T k - P.tau T l) ^ 2) := by
  have hC := h.C_nonneg
  have hL := h.L_pos
  have hX := h.X_pos
  calc ∫ t : ℝ, (1 + |t - P.tauStar T k l|) * ‖Hfn (kfun P T k l) ((5 / 4 : ℂ) + t * I)‖
      ≤ ∫ t : ℝ, (1 + C) * (1 + 3 * C) * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2
          * (1 / ((1 + (t - P.tau T k) ^ 2) * (1 + (t - P.tau T l) ^ 2))) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity)
          ((cauchyConv_integrable _ _).const_mul _)
          (Eventually.of_forall fun t => by beta_reduce; rw [mul_one_div]; exact h.weighted_norm_Hfn_kfun_le k l t)
    _ = (1 + C) * (1 + 3 * C) * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2
          * ∫ t : ℝ, 1 / ((1 + (t - P.tau T k) ^ 2) * (1 + (t - P.tau T l) ^ 2)) :=
        integral_const_mul _ _
    _ ≤ (1 + C) * (1 + 3 * C) * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2
          * (32 * Real.pi / (1 + (P.tau T k - P.tau T l) ^ 2)) :=
        mul_le_mul_of_nonneg_left (cauchyConv_integral_le' _ _) (by positivity)
    _ = _ := by ring

/-- **(W6b, mirrored)** ∫(1+|t+τ⋆|)‖H_{k∘neg}(5/4+it)‖dt ≤ 32π(1+C)(1+3C) X^{3/4} L² / (1+(τ_k−τ_l)²). -/
theorem integral_weighted_norm_Hfn_kfun_neg_le (h : WindowAt P T C) (k l : ℤ) :
    ∫ t : ℝ, (1 + |t + P.tauStar T k l|) * ‖Hfn (fun u => kfun P T k l (-u)) ((5 / 4 : ℂ) + t * I)‖
      ≤ 32 * Real.pi * ((1 + C) * (1 + 3 * C)) * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2
          / (1 + (P.tau T k - P.tau T l) ^ 2) := by
  have hC := h.C_nonneg
  have hL := h.L_pos
  have hX := h.X_pos
  calc ∫ t : ℝ, (1 + |t + P.tauStar T k l|) * ‖Hfn (fun u => kfun P T k l (-u)) ((5 / 4 : ℂ) + t * I)‖
      ≤ ∫ t : ℝ, (1 + C) * (1 + 3 * C) * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2
          * (1 / ((1 + (t - -P.tau T k) ^ 2) * (1 + (t - -P.tau T l) ^ 2))) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity)
          ((cauchyConv_integrable _ _).const_mul _)
          (Eventually.of_forall fun t => by
            beta_reduce; rw [mul_one_div, sub_neg_eq_add, sub_neg_eq_add]
            exact h.weighted_norm_Hfn_kfun_neg_le k l t)
    _ = (1 + C) * (1 + 3 * C) * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2
          * ∫ t : ℝ, 1 / ((1 + (t - -P.tau T k) ^ 2) * (1 + (t - -P.tau T l) ^ 2)) :=
        integral_const_mul _ _
    _ ≤ (1 + C) * (1 + 3 * C) * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2
          * (32 * Real.pi / (1 + (-P.tau T k - -P.tau T l) ^ 2)) :=
        mul_le_mul_of_nonneg_left (cauchyConv_integral_le' _ _) (by positivity)
    _ = _ := by ring

/-! ### far region: |t − τ⋆| ≥ 3τ⋆/4  (τ⋆ = (τ_k+τ_l)/2, T ≤ τ_k, τ_l ≤ 2T) -/

/-- for 0 ≤ k < d:  T ≤ τ_k ≤ 2T  (τ_k = T + k·2π/L, d = ⌊LT/2π⌋). -/
theorem tau_mem_Icc (h : WindowAt P T C) (k : Fin (P.d T)) :
    T ≤ P.tau T (k : ℤ) ∧ P.tau T (k : ℤ) ≤ 2 * T := by
  have hL := h.L_pos
  have hT := h.T_pos
  have hh : 0 < P.hgrid T := by unfold Params.hgrid; positivity
  have hk0 : (0 : ℝ) ≤ ((k : ℤ) : ℝ) := by exact_mod_cast (Int.natCast_nonneg _)
  have hkd : ((k : ℤ) : ℝ) ≤ (P.d T : ℝ) := by
    have : ((k : ℕ) : ℝ) ≤ (P.d T : ℝ) := by exact_mod_cast k.2.le
    exact_mod_cast this
  have hd : (P.d T : ℝ) ≤ P.L T * T / (2 * Real.pi) := by
    unfold Params.d; exact Nat.floor_le (by positivity)
  constructor
  · show T ≤ T + ((k : ℤ) : ℝ) * P.hgrid T
    nlinarith
  · show T + ((k : ℤ) : ℝ) * P.hgrid T ≤ 2 * T
    have : ((k : ℤ) : ℝ) * P.hgrid T ≤ (P.L T * T / (2 * Real.pi)) * P.hgrid T :=
      mul_le_mul_of_nonneg_right (hkd.trans hd) hh.le
    have hgrid : (P.L T * T / (2 * Real.pi)) * P.hgrid T = T := by
      unfold Params.hgrid; field_simp
    linarith

theorem far_subset {τk τl T : ℝ} (hk1 : T ≤ τk) (hk2 : τk ≤ 2 * T) (hl1 : T ≤ τl) (hl2 : τl ≤ 2 * T) :
    {t : ℝ | 3 * ((τk + τl) / 2) / 4 ≤ |t - (τk + τl) / 2|} ⊆ {t : ℝ | T / 4 ≤ |t - τk|} := by
  intro t ht
  simp only [mem_setOf_eq] at ht ⊢
  have h1 : |t - (τk + τl) / 2| ≤ |t - τk| + |τk - (τk + τl) / 2| := abs_sub_le _ _ _
  have h2 : |τk - (τk + τl) / 2| ≤ T / 2 := by
    rw [abs_le]; constructor <;> linarith
  linarith

theorem far_subset_neg {τk τl T : ℝ} (hk1 : T ≤ τk) (hk2 : τk ≤ 2 * T) (hl1 : T ≤ τl) (hl2 : τl ≤ 2 * T) :
    {t : ℝ | 3 * ((τk + τl) / 2) / 4 ≤ |t + (τk + τl) / 2|} ⊆ {t : ℝ | T / 4 ≤ |t - -τk|} := by
  intro t ht
  simp only [mem_setOf_eq] at ht ⊢
  have h1 : |t - -((τk + τl) / 2)| ≤ |t - -τk| + |-τk - -((τk + τl) / 2)| := abs_sub_le _ _ _
  have h2 : |-τk - -((τk + τl) / 2)| ≤ T / 2 := by
    rw [abs_le]; constructor <;> linarith
  rw [sub_neg_eq_add] at h1
  linarith

/-- **(W6c)** far from the bump:  ∫_{|t−τ⋆| ≥ 3τ⋆/4} ‖H(5/4+it)‖ dt ≤ 16π (1+C)² X^{3/4} L² / T²,
for T ≤ τ_k, τ_l ≤ 2T (tau_mem_Icc). -/
theorem setIntegral_far_norm_Hfn_kfun_le (h : WindowAt P T C) {k l : ℤ}
    (hk1 : T ≤ P.tau T k) (hk2 : P.tau T k ≤ 2 * T) (hl1 : T ≤ P.tau T l) (hl2 : P.tau T l ≤ 2 * T) :
    ∫ t in {t : ℝ | 3 * P.tauStar T k l / 4 ≤ |t - P.tauStar T k l|},
        ‖Hfn (kfun P T k l) ((5 / 4 : ℂ) + t * I)‖
      ≤ 16 * Real.pi * (1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2 / T ^ 2 := by
  have hC := h.C_nonneg
  have hL := h.L_pos
  have hX := h.X_pos
  have hT := h.T_pos
  set K := (1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hsub := far_subset hk1 hk2 hl1 hl2
  have hg : Integrable (fun t : ℝ => K * (1 / ((1 + (t - P.tau T k) ^ 2) * (1 + (t - P.tau T l) ^ 2)))) :=
    (cauchyConv_integrable _ _).const_mul K
  calc ∫ t in {t : ℝ | 3 * P.tauStar T k l / 4 ≤ |t - P.tauStar T k l|},
          ‖Hfn (kfun P T k l) ((5 / 4 : ℂ) + t * I)‖
      ≤ ∫ t in {t : ℝ | 3 * P.tauStar T k l / 4 ≤ |t - P.tauStar T k l|},
          K * (1 / ((1 + (t - P.tau T k) ^ 2) * (1 + (t - P.tau T l) ^ 2))) :=
        setIntegral_mono_on (h.integrable_Hfn_kfun k l).norm.integrableOn hg.integrableOn
          (measurableSet_far _ _) (fun t _ => by rw [mul_one_div]; exact h.norm_Hfn_kfun_le k l t)
    _ ≤ ∫ t in {t : ℝ | T / 4 ≤ |t - P.tau T k|},
          K * (1 / ((1 + (t - P.tau T k) ^ 2) * (1 + (t - P.tau T l) ^ 2))) :=
        setIntegral_mono_set hg.integrableOn
          (Eventually.of_forall fun t => by simp only [Pi.zero_apply]; positivity)
          (HasSubset.Subset.eventuallyLE (by unfold Params.tauStar; exact hsub))
    _ = K * ∫ t in {t : ℝ | T / 4 ≤ |t - P.tau T k|},
          1 / ((1 + (t - P.tau T k) ^ 2) * (1 + (t - P.tau T l) ^ 2)) := integral_const_mul _ _
    _ ≤ K * (Real.pi / (T / 4) ^ 2) :=
        mul_le_mul_of_nonneg_left (cauchyConv_far _ _ (by positivity)) hK0
    _ = 16 * Real.pi * (1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2 / T ^ 2 := by
        rw [hK]; field_simp; ring

/-- **(W6c, mirrored)** ∫_{|t+τ⋆| ≥ 3τ⋆/4} ‖H_{k∘neg}(5/4+it)‖ dt ≤ 16π (1+C)² X^{3/4} L² / T². -/
theorem setIntegral_far_norm_Hfn_kfun_neg_le (h : WindowAt P T C) {k l : ℤ}
    (hk1 : T ≤ P.tau T k) (hk2 : P.tau T k ≤ 2 * T) (hl1 : T ≤ P.tau T l) (hl2 : P.tau T l ≤ 2 * T) :
    ∫ t in {t : ℝ | 3 * P.tauStar T k l / 4 ≤ |t + P.tauStar T k l|},
        ‖Hfn (fun u => kfun P T k l (-u)) ((5 / 4 : ℂ) + t * I)‖
      ≤ 16 * Real.pi * (1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2 / T ^ 2 := by
  have hC := h.C_nonneg
  have hL := h.L_pos
  have hX := h.X_pos
  have hT := h.T_pos
  set K := (1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hsub := far_subset_neg hk1 hk2 hl1 hl2
  have hg : Integrable (fun t : ℝ =>
      K * (1 / ((1 + (t - -P.tau T k) ^ 2) * (1 + (t - -P.tau T l) ^ 2)))) :=
    (cauchyConv_integrable _ _).const_mul K
  calc ∫ t in {t : ℝ | 3 * P.tauStar T k l / 4 ≤ |t + P.tauStar T k l|},
          ‖Hfn (fun u => kfun P T k l (-u)) ((5 / 4 : ℂ) + t * I)‖
      ≤ ∫ t in {t : ℝ | 3 * P.tauStar T k l / 4 ≤ |t + P.tauStar T k l|},
          K * (1 / ((1 + (t - -P.tau T k) ^ 2) * (1 + (t - -P.tau T l) ^ 2))) := by
        refine setIntegral_mono_on (h.integrable_Hfn_kfun_neg k l).norm.integrableOn hg.integrableOn
          ?_ (fun t _ => by
            rw [mul_one_div, sub_neg_eq_add, sub_neg_eq_add]; exact h.norm_Hfn_kfun_neg_le k l t)
        have := measurableSet_far (-P.tauStar T k l) (3 * P.tauStar T k l / 4)
        simp only [sub_neg_eq_add] at this
        exact this
    _ ≤ ∫ t in {t : ℝ | T / 4 ≤ |t - -P.tau T k|},
          K * (1 / ((1 + (t - -P.tau T k) ^ 2) * (1 + (t - -P.tau T l) ^ 2))) :=
        setIntegral_mono_set hg.integrableOn
          (Eventually.of_forall fun t => by simp only [Pi.zero_apply]; positivity)
          (HasSubset.Subset.eventuallyLE (by unfold Params.tauStar; exact hsub))
    _ = K * ∫ t in {t : ℝ | T / 4 ≤ |t - -P.tau T k|},
          1 / ((1 + (t - -P.tau T k) ^ 2) * (1 + (t - -P.tau T l) ^ 2)) := integral_const_mul _ _
    _ ≤ K * (Real.pi / (T / 4) ^ 2) :=
        mul_le_mul_of_nonneg_left (cauchyConv_far _ _ (by positivity)) hK0
    _ = 16 * Real.pi * (1 + C) ^ 2 * P.X T ^ (3 / 4 : ℝ) * P.L T ^ 2 / T ^ 2 := by
        rw [hK]; field_simp; ring

end WindowAt
end TestWeight

/-! ## §I. The "∃ C T₁, ∀ T ≥ T₁, ∀ k l" packaging (constants depend only on hPf)

Each item below is a one-line corollary of `FamilyHyps.windowAt` and the fixed-height lemma of §§E–H named
in its proof. -/

section Family

variable {Pf : ℝ → Params}

/-- **(W0)** regularity and support of the weight and its mirror; 0 < L, 1 ≤ L eventually. -/
theorem testWeight_regular (hPf : FamilyHyps Pf) :
    ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T → (0 < (Pf T).L T ∧ 1 ≤ (Pf T).L T) ∧ ∀ k l : ℤ,
      (ContDiff ℝ 2 (kfun (Pf T) T k l) ∧ HasCompactSupport (kfun (Pf T) T k l) ∧
        tsupport (kfun (Pf T) T k l) ⊆ Icc (-(Pf T).L T) ((Pf T).L T)) ∧
      (ContDiff ℝ 2 (fun u => kfun (Pf T) T k l (-u)) ∧
        HasCompactSupport (fun u => kfun (Pf T) T k l (-u)) ∧
        tsupport (fun u => kfun (Pf T) T k l (-u)) ⊆ Icc (-(Pf T).L T) ((Pf T).L T)) := by
  obtain ⟨C, T₁, -, hW⟩ := hPf.windowAt
  refine ⟨T₁, fun T hT => ?_⟩
  have h := hW T hT
  exact ⟨⟨h.L_pos, h.one_le_L⟩, fun k l =>
    ⟨⟨h.kfun_contDiff k l, h.kfun_hasCompactSupport k l, h.kfun_tsupport k l⟩,
     ⟨h.kfun_neg_contDiff k l, h.kfun_neg_hasCompactSupport k l, h.kfun_neg_tsupport k l⟩⟩⟩

/-- **[XF′ Lemma 3.1]** for the family: h_k(z) = φ̂(z−τ_k) φ̂(z−τ_l), all complex z, eventually in T. -/
theorem testWeight_paperFT (hPf : FamilyHyps Pf) :
    ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T → ∀ (k l : ℤ) (z : ℂ),
      paperFT (kfun (Pf T) T k l) z = (Pf T).phiHat T (z - (Pf T).tau T k) * (Pf T).phiHat T (z - (Pf T).tau T l) := by
  obtain ⟨C, T₁, -, hW⟩ := hPf.windowAt
  exact ⟨T₁, fun T hT k l z => (hW T hT).paperFT_kfun k l z⟩

/-- **(W1)** size on the line Re s = 5/4. -/
theorem testWeight_norm_le (hPf : FamilyHyps Pf) :
    ∃ C T₁ : ℝ, 0 < C ∧ ∀ T : ℝ, T₁ ≤ T → ∀ (k l : ℤ) (t : ℝ),
      ‖Hfn (kfun (Pf T) T k l) ((5 / 4 : ℂ) + t * I)‖
        ≤ C * (Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T ^ 2 /
            ((1 + (t - (Pf T).tau T k) ^ 2) * (1 + (t - (Pf T).tau T l) ^ 2)) := by
  obtain ⟨C, T₁, hC, hW⟩ := hPf.windowAt
  exact ⟨(1 + C) ^ 2, T₁, by positivity, fun T hT k l t => (hW T hT).norm_Hfn_kfun_le k l t⟩

/-- **(W2)** first moment on the line Re s = 5/4. -/
theorem testWeight_moment_norm_le (hPf : FamilyHyps Pf) :
    ∃ C T₁ : ℝ, 0 < C ∧ ∀ T : ℝ, T₁ ≤ T → ∀ (k l : ℤ) (t : ℝ),
      (|t - (Pf T).tau T k| + |t - (Pf T).tau T l|) * ‖Hfn (kfun (Pf T) T k l) ((5 / 4 : ℂ) + t * I)‖
        ≤ C * (Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T /
            ((1 + (t - (Pf T).tau T k) ^ 2) * (1 + (t - (Pf T).tau T l) ^ 2)) := by
  obtain ⟨C, T₁, hC, hW⟩ := hPf.windowAt
  exact ⟨4 * C * (1 + C), T₁, by positivity, fun T hT k l t => (hW T hT).moment_norm_Hfn_kfun_le k l t⟩

/-- **(W3)** the mirrored weight u ↦ k(−u): the same two bounds with τ ↦ −τ (written t + τ). -/
theorem testWeight_neg_norm_le (hPf : FamilyHyps Pf) :
    ∃ C T₁ : ℝ, 0 < C ∧ ∀ T : ℝ, T₁ ≤ T → ∀ (k l : ℤ) (t : ℝ),
      ‖Hfn (fun u => kfun (Pf T) T k l (-u)) ((5 / 4 : ℂ) + t * I)‖
          ≤ C * (Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T ^ 2 /
              ((1 + (t + (Pf T).tau T k) ^ 2) * (1 + (t + (Pf T).tau T l) ^ 2)) ∧
      (|t + (Pf T).tau T k| + |t + (Pf T).tau T l|)
          * ‖Hfn (fun u => kfun (Pf T) T k l (-u)) ((5 / 4 : ℂ) + t * I)‖
          ≤ C * (Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T /
              ((1 + (t + (Pf T).tau T k) ^ 2) * (1 + (t + (Pf T).tau T l) ^ 2)) := by
  obtain ⟨C, T₁, hC, hW⟩ := hPf.windowAt
  refine ⟨4 * (1 + C) ^ 2, T₁, by positivity, fun T hT k l t => ⟨?_, ?_⟩⟩
  · refine ((hW T hT).norm_Hfn_kfun_neg_le k l t).trans ?_
    have hXr : 0 ≤ (Pf T).X T ^ (3 / 4 : ℝ) := Real.rpow_nonneg (hW T hT).X_pos.le _
    have hL := (hW T hT).L_pos
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ hXr
    nlinarith [sq_nonneg (1 + C)]
  · refine ((hW T hT).moment_norm_Hfn_kfun_neg_le k l t).trans ?_
    have hXr : 0 ≤ (Pf T).X T ^ (3 / 4 : ℝ) := Real.rpow_nonneg (hW T hT).X_pos.le _
    have hL := (hW T hT).L_pos
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ hL.le
    apply mul_le_mul_of_nonneg_right _ hXr
    nlinarith [sq_nonneg (1 + C)]

/-- **(W4)** on the real line: real-valued product formula, integrable, ∫‖·‖ ≤ C L²/(1+(τ_k−τ_l)²). -/
theorem testWeight_real_line (hPf : FamilyHyps Pf) :
    ∃ C T₁ : ℝ, 0 < C ∧ ∀ T : ℝ, T₁ ≤ T → ∀ k l : ℤ,
      (∀ τ : ℝ, paperFT (kfun (Pf T) T k l) τ
          = (((Pf T).phiHatR T (τ - (Pf T).tau T k) * (Pf T).phiHatR T (τ - (Pf T).tau T l) : ℝ) : ℂ)) ∧
      Integrable (fun τ : ℝ => paperFT (kfun (Pf T) T k l) τ) ∧
      ∫ τ : ℝ, ‖paperFT (kfun (Pf T) T k l) τ‖
          ≤ C * (Pf T).L T ^ 2 / (1 + ((Pf T).tau T k - (Pf T).tau T l) ^ 2) := by
  obtain ⟨C, T₁, hC, hW⟩ := hPf.windowAt
  exact ⟨32 * Real.pi * (1 + C) ^ 2, T₁, by positivity, fun T hT k l =>
    ⟨(hW T hT).paperFT_kfun_ofReal k l, (hW T hT).integrable_paperFT_kfun_ofReal k l,
      (hW T hT).integral_norm_paperFT_kfun_ofReal_le k l⟩⟩

/-- **(W6)** for the family: integrability, ∫‖H‖, ∫(1+|t−τ⋆|)‖H‖ ≤ C X^{3/4}L²/(1+Δ²), and the far tail
≤ C X^{3/4} L²/T² (for T ≤ τ_k, τ_l ≤ 2T); plus the same four for the mirrored weight around −τ⋆. -/
theorem testWeight_integrals (hPf : FamilyHyps Pf) :
    ∃ C T₁ : ℝ, 0 < C ∧ ∀ T : ℝ, T₁ ≤ T → ∀ k l : ℤ,
      Integrable (fun t : ℝ => Hfn (kfun (Pf T) T k l) ((5 / 4 : ℂ) + t * I)) ∧
      Integrable (fun t : ℝ => Hfn (fun u => kfun (Pf T) T k l (-u)) ((5 / 4 : ℂ) + t * I)) ∧
      ∫ t : ℝ, ‖Hfn (kfun (Pf T) T k l) ((5 / 4 : ℂ) + t * I)‖
          ≤ C * (Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T ^ 2 / (1 + ((Pf T).tau T k - (Pf T).tau T l) ^ 2) ∧
      ∫ t : ℝ, ‖Hfn (fun u => kfun (Pf T) T k l (-u)) ((5 / 4 : ℂ) + t * I)‖
          ≤ C * (Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T ^ 2 / (1 + ((Pf T).tau T k - (Pf T).tau T l) ^ 2) ∧
      ∫ t : ℝ, (1 + |t - (Pf T).tauStar T k l|) * ‖Hfn (kfun (Pf T) T k l) ((5 / 4 : ℂ) + t * I)‖
          ≤ C * (Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T ^ 2 / (1 + ((Pf T).tau T k - (Pf T).tau T l) ^ 2) ∧
      ∫ t : ℝ, (1 + |t + (Pf T).tauStar T k l|)
            * ‖Hfn (fun u => kfun (Pf T) T k l (-u)) ((5 / 4 : ℂ) + t * I)‖
          ≤ C * (Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T ^ 2 / (1 + ((Pf T).tau T k - (Pf T).tau T l) ^ 2) ∧
      (T ≤ (Pf T).tau T k → (Pf T).tau T k ≤ 2 * T → T ≤ (Pf T).tau T l → (Pf T).tau T l ≤ 2 * T →
        ∫ t in {t : ℝ | 3 * (Pf T).tauStar T k l / 4 ≤ |t - (Pf T).tauStar T k l|},
            ‖Hfn (kfun (Pf T) T k l) ((5 / 4 : ℂ) + t * I)‖
          ≤ C * (Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T ^ 2 / T ^ 2 ∧
        ∫ t in {t : ℝ | 3 * (Pf T).tauStar T k l / 4 ≤ |t + (Pf T).tauStar T k l|},
            ‖Hfn (fun u => kfun (Pf T) T k l (-u)) ((5 / 4 : ℂ) + t * I)‖
          ≤ C * (Pf T).X T ^ (3 / 4 : ℝ) * (Pf T).L T ^ 2 / T ^ 2) := by
  obtain ⟨C, T₁, hC, hW⟩ := hPf.windowAt
  -- one constant dominating 32π(1+C)², 32π(1+C)(1+3C), 16π(1+C)²:
  refine ⟨32 * Real.pi * ((1 + C) * (1 + 3 * C)), T₁, by positivity, fun T hT k l => ?_⟩
  have h := hW T hT
  have hX := h.X_pos
  have hL := h.L_pos
  have hT0 := h.T_pos
  have hXr : 0 ≤ (Pf T).X T ^ (3 / 4 : ℝ) := Real.rpow_nonneg hX.le _
  have hcc : (1 + C) ^ 2 ≤ (1 + C) * (1 + 3 * C) := by nlinarith
  have hc1 : 32 * Real.pi * (1 + C) ^ 2 ≤ 32 * Real.pi * ((1 + C) * (1 + 3 * C)) :=
    mul_le_mul_of_nonneg_left hcc (by positivity)
  have hc2 : 16 * Real.pi * (1 + C) ^ 2 ≤ 32 * Real.pi * ((1 + C) * (1 + 3 * C)) := by
    nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg (1 + C))]
  refine ⟨h.integrable_Hfn_kfun k l, h.integrable_Hfn_kfun_neg k l, ?_, ?_,
    h.integral_weighted_norm_Hfn_kfun_le k l, h.integral_weighted_norm_Hfn_kfun_neg_le k l,
    fun hk1 hk2 hl1 hl2 => ⟨?_, ?_⟩⟩
  · exact (h.integral_norm_Hfn_kfun_le k l).trans (by gcongr)
  · exact (h.integral_norm_Hfn_kfun_neg_le k l).trans (by gcongr)
  · exact (h.setIntegral_far_norm_Hfn_kfun_le hk1 hk2 hl1 hl2).trans (by gcongr)
  · exact (h.setIntegral_far_norm_Hfn_kfun_neg_le hk1 hk2 hl1 hl2).trans (by gcongr)

/-- (W6, indices) for a Fin d index the hypothesis T ≤ τ_k ≤ 2T of the far-tail bound holds eventually. -/
theorem testWeight_tau_mem_Icc (hPf : FamilyHyps Pf) :
    ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T → ∀ k : Fin ((Pf T).d T),
      T ≤ (Pf T).tau T (k : ℤ) ∧ (Pf T).tau T (k : ℤ) ≤ 2 * T := by
  obtain ⟨C, T₁, -, hW⟩ := hPf.windowAt
  exact ⟨T₁, fun T hT k => (hW T hT).tau_mem_Icc k⟩

end Family

end XiPrime
end Zeta23
