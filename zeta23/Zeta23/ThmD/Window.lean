/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmD/Window.lean — [thm:D], the concrete window.  A summary of the statements
proved is given at the bottom of the file.

The concrete Montgomery–Taylor window of the [thm:D] proof (paper §7.1):
  φ_D(u) := √(cos(√2 λ u/L)) · φ_flat(u),   φ_flat = Zeta23.Taper.phi ϱ L w (the §2.2 ramp taper),
i.e. the paper's "cos(√2 u/l)^{1/2} ϱ(L/2−|u|)" at general 0 < λ ≤ 1 (we avoid the λ = 1
endpoint; the paper's display is the λ = 1 case with w = 1) and with the ramp width w kept
free as everywhere else in this project.

On the support [−L/2, L/2] the cosine argument is ≤ √2λ/2 = ϑ ≤ 1/√2 < π/2, so cos ≥ cos ϑ ≥ 3/4
> 0 there and √cos is smooth on a neighbourhood; off the support φ_flat kills everything
(and Real.sqrt of a negative is 0, so φ_D is total and 0 outside [−L/2, L/2] regardless).

WHY THESE STATEMENTS (paper §7.1, first paragraph): "Nothing in Sections 4–5 used that φ is
flat-topped, only: φ ∈ C_c² even, 0 ≤ φ ≤ 1, supp φ = [−L/2,L/2], φ nonincreasing in |u|
(so ‖φ'‖₁ ≤ 2, ‖(φ²)'‖₁ ≤ 2), and ‖φ''‖₁, ‖(φ²)''‖₁ ≪ 1" + the moments [eq:abJ] "differ from
those of v*_λ by O(1/L)".
-/
import Zeta23.Taper.Basic
import Zeta23.Taper.Norms
import Zeta23.Taper.Decay
import Zeta23.ThmD.Functional

noncomputable section

open Real Set MeasureTheory

namespace Zeta23
namespace ThmD

/-- the Montgomery–Taylor window: φ_D(u) := √(v*_λ(u/L)) · (ramp taper). -/
def phiD (ϱ : ℝ → ℝ) (lam L w : ℝ) (u : ℝ) : ℝ :=
  Real.sqrt (vStar lam (u / L)) * Taper.phi ϱ L w u

variable {ϱ : ℝ → ℝ} {lam L w : ℝ}

/-! ### pointwise / support facts (sentence 1 of §7.1) -/

theorem phiD_even (u : ℝ) : phiD ϱ lam L w (-u) = phiD ϱ lam L w u := by
  unfold phiD vStar
  rw [Taper.phi_even]
  norm_num [neg_div, mul_neg, Real.cos_neg]

theorem phiD_nonneg (hϱ : TaperProfile ϱ) (u : ℝ) : 0 ≤ phiD ϱ lam L w u :=
  mul_nonneg (Real.sqrt_nonneg _) (Taper.phi_nonneg hϱ u)

theorem phiD_le_one (hϱ : TaperProfile ϱ) (u : ℝ) : phiD ϱ lam L w u ≤ 1 := by
  unfold phiD
  calc Real.sqrt (vStar lam (u / L)) * Taper.phi ϱ L w u
      ≤ 1 * 1 := by
        refine mul_le_mul ?_ (Taper.phi_le_one hϱ u) (Taper.phi_nonneg hϱ u) zero_le_one
        rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
        exact Real.sqrt_le_sqrt (by unfold vStar; exact Real.cos_le_one _)
    _ = 1 := mul_one 1

theorem phiD_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : L / 2 ≤ |u|) :
    phiD ϱ lam L w u = 0 := by
  unfold phiD
  rw [Taper.phi_eq_zero hϱ hw hu, mul_zero]

/-- on the support, the cosine factor is bounded below: for |u| ≤ L/2 (0 < λ ≤ 1, L > 0),
cos(√2 λ u/L) ≥ 3/4. -/
theorem cos_factor_ge (h0 : 0 < lam) (h1 : lam ≤ 1) (hL : 0 < L) {u : ℝ}
    (hu : |u| ≤ L / 2) : 3 / 4 ≤ vStar lam (u / L) := by
  unfold vStar
  have h := Real.one_sub_sq_div_two_le_cos (x := Real.sqrt 2 * lam * (u / L))
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu2 : u ^ 2 ≤ (L / 2) ^ 2 := by
    rw [← sq_abs u]
    exact pow_le_pow_left₀ (abs_nonneg u) hu 2
  have hlam2 : lam ^ 2 ≤ 1 := pow_le_one₀ h0.le h1
  have hq0 : 0 ≤ u ^ 2 / L ^ 2 := by positivity
  have hq : u ^ 2 / L ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have harg : (Real.sqrt 2 * lam * (u / L)) ^ 2 ≤ 1 / 2 := by
    rw [mul_pow, mul_pow, div_pow, hsq]
    nlinarith [mul_nonneg (sub_nonneg.mpr hlam2) hq0]
  linarith

/-- φ_D ∈ C² (product of the C³ ramp with √cos, smooth near the support; glued with 0 off it). -/
theorem phiD_contDiff (hϱ : TaperProfile ϱ) (h0 : 0 < lam) (h1 : lam ≤ 1) (hw : 0 < w)
    (hwL : 2 * w ≤ L) : ContDiff ℝ 2 (phiD ϱ lam L w) := by
  have hL : 0 < L := by linarith
  rw [contDiff_iff_contDiffAt]
  intro u
  rcases lt_or_ge |u| (2 * L / 3) with hu | hu
  · -- near the support: √(cos) is smooth since cos ≥ some positive bound on a neighbourhood
    unfold phiD
    apply ContDiffAt.mul ?_
      (((Taper.phi_contDiff hϱ hw hwL).of_le (by norm_num)).contDiffAt)
    apply ContDiffAt.sqrt ?_ ?_
    · exact ((Real.contDiff_cos.comp (by fun_prop : ContDiff ℝ 2
        (fun u : ℝ => Real.sqrt 2 * lam * (u / L)))).contDiffAt)
    · -- cos(√2 λ u/L) ≠ 0 for |u| < 2L/3: the argument is < √2·(2/3) < π/2
      have hs32 : Real.sqrt 2 ≤ 3 / 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
      have harg : |Real.sqrt 2 * lam * (u / L)| < π / 2 := by
        rw [abs_mul, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt 2 * lam),
          abs_of_pos hL]
        have h1' : Real.sqrt 2 * lam ≤ 3 / 2 := by
          calc Real.sqrt 2 * lam ≤ (3/2) * 1 := by
                apply mul_le_mul hs32 h1 h0.le (by norm_num)
            _ = 3 / 2 := mul_one _
        have h2' : |u| / L < 2 / 3 := by
          rw [div_lt_iff₀ hL]
          linarith
        calc Real.sqrt 2 * lam * (|u| / L) ≤ (3/2) * (|u| / L) := by
              apply mul_le_mul_of_nonneg_right h1' (by positivity)
          _ < (3/2) * (2/3) := by
              apply mul_lt_mul_of_pos_left h2' (by norm_num)
          _ = 1 := by norm_num
          _ < π / 2 := by nlinarith [Real.pi_gt_three]
      apply ne_of_gt
      unfold vStar
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith [neg_abs_le (Real.sqrt 2 * lam * (u / L)), harg]
      · linarith [le_abs_self (Real.sqrt 2 * lam * (u / L))]
  · -- |u| ≥ 2L/3 > L/2: φ_D vanishes on a neighbourhood of u
    have hopen : IsOpen {v : ℝ | L / 2 < |v|} := by
      have : {v : ℝ | L / 2 < |v|} = (fun v : ℝ => |v|) ⁻¹' Set.Ioi (L / 2) := rfl
      rw [this]
      exact (continuous_abs).isOpen_preimage _ isOpen_Ioi
    have hmem : u ∈ {v : ℝ | L / 2 < |v|} := by
      simp only [Set.mem_setOf_eq]
      calc L / 2 < 2 * L / 3 := by linarith
        _ ≤ |u| := hu
    apply ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := 0))
    filter_upwards [hopen.mem_nhds hmem] with v hv
    exact phiD_eq_zero hϱ hw (le_of_lt hv)

/-- φ_D is nonincreasing in |u|: antitone on [0, ∞). -/
theorem phiD_antitoneOn (hϱ : TaperProfile ϱ) (h0 : 0 < lam) (h1 : lam ≤ 1) (hw : 0 < w)
    (hwL : 2 * w ≤ L) : AntitoneOn (phiD ϱ lam L w) (Set.Ici 0) := by
  have hL : 0 < L := by linarith
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  rcases le_or_gt (L / 2) y with hYL | hYL
  · rw [phiD_eq_zero hϱ hw (by rwa [abs_of_nonneg hy])]
    exact phiD_nonneg hϱ x
  · unfold phiD
    have hcosx : 0 ≤ vStar lam (x / L) := by
      have := cos_factor_ge (u := x) h0 h1 hL (by rw [abs_of_nonneg hx]; linarith)
      linarith
    have hdiv : x / L ≤ y / L := by gcongr
    have hargle : Real.sqrt 2 * lam * (x / L) ≤ Real.sqrt 2 * lam * (y / L) := by
      apply mul_le_mul_of_nonneg_left hdiv (by positivity)
    have hypi : Real.sqrt 2 * lam * (y / L) ≤ π := by
      have hs32 : Real.sqrt 2 ≤ 3 / 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
      have hyd : y / L ≤ 1 / 2 := by
        rw [div_le_iff₀ hL]
        linarith
      calc Real.sqrt 2 * lam * (y / L) ≤ (3 / 2) * 1 * (1 / 2) := by
            apply mul_le_mul (mul_le_mul hs32 h1 h0.le (by norm_num)) hyd (by positivity)
              (by norm_num)
        _ ≤ π := by nlinarith [Real.pi_gt_three]
    refine mul_le_mul ?_ ?_ (Taper.phi_nonneg hϱ y) (Real.sqrt_nonneg _)
    · apply Real.sqrt_le_sqrt
      unfold vStar
      exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hypi hargle
    · unfold Taper.phi
      apply hϱ.monotone
      rw [abs_of_nonneg hx, abs_of_nonneg hy]
      gcongr

/-! ### derivative norms (sentence 1 of §7.1, parenthetical + last clause) -/

/-- generic: an even C¹ function, nonincreasing on [0,∞), with values in [0,1] and support in
[−M, M], has total variation ∫|f'| ≤ 2 (= 2(f(0) − f(M))).  Used for φ_D and φ_D². -/
private theorem integral_abs_deriv_le_two {f : ℝ → ℝ} {M : ℝ} (hM : 0 < M)
    (hf : ContDiff ℝ 1 f) (heven : ∀ x, f (-x) = f x) (hanti : AntitoneOn f (Set.Ici 0))
    (h1 : ∀ x, f x ≤ 1) (hsupp : ∀ x, M ≤ |x| → f x = 0) :
    ∫ u, |deriv f u| ≤ 2 := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd' : Continuous (deriv f) := hf.continuous_deriv le_rfl
  -- deriv vanishes beyond the support
  have hderiv0 : ∀ x : ℝ, M < |x| → deriv f x = 0 := by
    intro x hx
    have hopen : IsOpen {v : ℝ | M < |v|} :=
      (continuous_abs).isOpen_preimage _ isOpen_Ioi
    have hEq : f =ᶠ[nhds x] (fun _ => (0:ℝ)) := by
      filter_upwards [hopen.mem_nhds hx] with v hv
      exact hsupp v (le_of_lt hv)
    rw [hEq.deriv_eq, deriv_const]
  -- |deriv f| is even
  have hodd : ∀ x : ℝ, |deriv f (-x)| = |deriv f x| := by
    intro x
    have hfe : (fun y : ℝ => f (-y)) = f := funext heven
    have h := deriv_comp_neg (f := f) (x := x)
    rw [hfe] at h
    have h' : deriv f (-x) = -deriv f x := by linarith
    rw [h', abs_neg]
  -- reduce to (0, ∞)
  have habs : (fun u : ℝ => |deriv f u|) = fun u => (fun t => |deriv f t|) |u| := by
    funext u
    show |deriv f u| = |deriv f (|u|)|
    rcases le_or_gt 0 u with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, hodd]
  have hhalf : ∫ u, |deriv f u| = 2 * ∫ u in Set.Ioi 0, |deriv f u| := by
    conv_lhs => rw [habs]
    exact integral_comp_abs (f := fun t => |deriv f t|)
  -- integrability
  have hcs : HasCompactSupport (deriv f) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -M) (b := M))
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hmem
    apply hx
    apply hderiv0
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
    rcases hmem with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hint : Integrable (fun u => |deriv f u|) :=
    (hd'.integrable_of_hasCompactSupport hcs).abs
  -- split (0, ∞) = (0, M] ∪ (M, ∞); the far part vanishes
  have hsplit : ∫ u in Set.Ioi 0, |deriv f u|
      = (∫ u in Set.Ioc 0 M, |deriv f u|) + ∫ u in Set.Ioi M, |deriv f u| := by
    rw [← MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      hint.integrableOn hint.integrableOn, Set.Ioc_union_Ioi_eq_Ioi hM.le]
  have hfar : ∫ u in Set.Ioi M, |deriv f u| = 0 := by
    apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    rw [hderiv0 x (by rw [abs_of_pos (lt_trans hM hx)]; exact hx), abs_zero]
  -- on (0, M]: |f'| = −f' (antitone), and FTC
  have hneg : ∀ x ∈ Set.Ioc 0 M, |deriv f x| = -deriv f x := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hle : deriv f x ≤ 0 := by
      have hmem : Set.Ici (0:ℝ) ∈ nhds x := Ici_mem_nhds hx0
      rw [← derivWithin_of_mem_nhds hmem]
      exact hanti.derivWithin_nonpos
    rw [abs_of_nonpos hle]
  have hFTC : ∫ u in (0:ℝ)..M, deriv f u = f M - f 0 :=
    intervalIntegral.integral_deriv_eq_sub (fun x _ => hd x)
      ((hd'.intervalIntegrable) 0 M)
  have hnear : ∫ u in Set.Ioc 0 M, |deriv f u| = f 0 - f M := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hneg]
    rw [← intervalIntegral.integral_of_le hM.le] at *
    rw [intervalIntegral.integral_neg, hFTC]
    ring
  have hfM : f M = 0 := hsupp M (by rw [abs_of_pos hM])
  have hf0 : f 0 ≤ 1 := h1 0
  rw [hhalf, hsplit, hfar, hnear, hfM]
  linarith

/-- ‖φ_D'‖₁ ≤ 2 (even, nonincreasing in |u|, 0 ≤ φ_D ≤ 1, compact support). -/
theorem integral_abs_deriv_phiD_le (hϱ : TaperProfile ϱ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hw : 0 < w) (hwL : 2 * w ≤ L) : ∫ u, |deriv (phiD ϱ lam L w) u| ≤ 2 := by
  have hL : 0 < L := by linarith
  exact integral_abs_deriv_le_two (by positivity : (0:ℝ) < L / 2)
    ((phiD_contDiff hϱ h0 h1 hw hwL).of_le (by norm_num)) phiD_even
    (phiD_antitoneOn hϱ h0 h1 hw hwL) (phiD_le_one hϱ)
    (fun x hx => phiD_eq_zero hϱ hw hx)

/-- ‖(φ_D²)'‖₁ ≤ 2 (same mechanism for φ_D²). -/
theorem integral_abs_deriv_phiD_sq_le (hϱ : TaperProfile ϱ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u, |deriv (fun u => phiD ϱ lam L w u ^ 2) u| ≤ 2 := by
  have hL : 0 < L := by linarith
  refine integral_abs_deriv_le_two (by positivity : (0:ℝ) < L / 2)
    (((phiD_contDiff hϱ h0 h1 hw hwL).pow 2).of_le (by norm_num)) ?_ ?_ ?_ ?_
  · intro x
    rw [phiD_even]
  · intro x hx y hy hxy
    exact pow_le_pow_left₀ (phiD_nonneg hϱ y)
      (phiD_antitoneOn hϱ h0 h1 hw hwL hx hy hxy) 2
  · intro x
    calc phiD ϱ lam L w x ^ 2 ≤ 1 ^ 2 :=
          pow_le_pow_left₀ (phiD_nonneg hϱ x) (phiD_le_one hϱ x) 2
      _ = 1 := one_pow 2
  · intro x hx
    rw [phiD_eq_zero hϱ hw hx, zero_pow two_ne_zero]

/-- ‖φ_D''‖₁ ≤ C(ϱ, λ)/w: explicit window-constant (the §7.1 "≪ 1" with w-dependence kept,
matching [eq:phinorms]'s shape; cDT plays the role of c_ϱ for this window). -/
def cDT (ϱ : ℝ → ℝ) (lam : ℝ) : ℝ :=
  64 * (Taper.cRho ϱ + 1) * (1 + lam ^ 2)

/-- φ_D² = (cosine factor) · φ², with no square root: (√v)² = v wherever φ ≠ 0 (there v ≥ 3/4),
and both sides vanish elsewhere. -/
theorem phiD_sq_eq (hϱ : TaperProfile ϱ) (h0 : 0 < lam) (h1 : lam ≤ 1) (hw : 0 < w)
    (hwL : 2 * w ≤ L) :
    (fun u => phiD ϱ lam L w u ^ 2)
      = fun u => vStar lam (u / L) * Taper.phi ϱ L w u ^ 2 := by
  have hL : 0 < L := by linarith
  funext u
  unfold phiD
  rcases le_or_gt (L / 2) |u| with hu | hu
  · rw [Taper.phi_eq_zero hϱ hw hu]
    ring
  · have hv : 0 ≤ vStar lam (u / L) := by
      have := cos_factor_ge h0 h1 hL hu.le
      linarith
  
    rw [mul_pow, Real.sq_sqrt hv]

private theorem hasDerivAt_cosFactor (u : ℝ) :
    HasDerivAt (fun u : ℝ => vStar lam (u / L))
      (-(Real.sqrt 2 * lam * (1 / L)) * Real.sin (Real.sqrt 2 * lam * (u / L))) u := by
  have hlin : HasDerivAt (fun u : ℝ => Real.sqrt 2 * lam * (u / L))
      (Real.sqrt 2 * lam * (1 / L)) u := by
    simpa using ((hasDerivAt_id u).div_const L).const_mul (Real.sqrt 2 * lam)
  have h := (Real.hasDerivAt_cos (Real.sqrt 2 * lam * (u / L))).comp u hlin
  unfold vStar
  exact h.congr_deriv (by ring)

private theorem hasDerivAt_cosFactor' (u : ℝ) :
    HasDerivAt (fun u : ℝ => -(Real.sqrt 2 * lam * (1 / L))
        * Real.sin (Real.sqrt 2 * lam * (u / L)))
      (-(Real.sqrt 2 * lam * (1 / L)) ^ 2 * Real.cos (Real.sqrt 2 * lam * (u / L))) u := by
  have hlin : HasDerivAt (fun u : ℝ => Real.sqrt 2 * lam * (u / L))
      (Real.sqrt 2 * lam * (1 / L)) u := by
    simpa using ((hasDerivAt_id u).div_const L).const_mul (Real.sqrt 2 * lam)
  have h := ((Real.hasDerivAt_sin (Real.sqrt 2 * lam * (u / L))).comp u hlin).const_mul
    (-(Real.sqrt 2 * lam * (1 / L)))
  exact h.congr_deriv (by ring)

/-- restriction of ∫|g| to the support interval (g vanishing outside). -/
private theorem integral_abs_eq_setIntegral {g : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h0 : ∀ x : ℝ, M < |x| → g x = 0) :
    ∫ u, |g u| = ∫ u in Set.Icc (-M) M, |g u| := by
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  have hMx : M < |x| := by
    rcases hx with h | h
    · rw [abs_of_neg (by linarith : x < 0)]
      linarith
    · rw [abs_of_pos (by linarith : 0 < x)]
      linarith
  rw [h0 x hMx, abs_zero]

/-- second derivatives vanish beyond the support. -/
private theorem deriv2_eq_zero_outside {f : ℝ → ℝ} {M : ℝ}
    (hsupp : ∀ x : ℝ, M ≤ |x| → f x = 0) {x : ℝ} (hx : M < |x|) :
    deriv (deriv f) x = 0 := by
  have hopen : IsOpen {v : ℝ | M < |v|} := (continuous_abs).isOpen_preimage _ isOpen_Ioi
  have h1 : deriv f =ᶠ[nhds x] (fun _ => (0:ℝ)) := by
    have hmem := hopen.mem_nhds hx
    filter_upwards [eventually_eventually_nhds.mpr hmem] with v hv
    have hEq : f =ᶠ[nhds v] (fun _ => (0:ℝ)) := by
      filter_upwards [hv] with t ht
      exact hsupp t (le_of_lt ht)
    rw [hEq.deriv_eq, deriv_const]
  rw [h1.deriv_eq, deriv_const]

theorem integral_abs_deriv2_phiD_sq_le (hϱ : TaperProfile ϱ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ u, |deriv (deriv (fun u => phiD ϱ lam L w u ^ 2)) u| ≤ cDT ϱ lam / w := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hs32 : Real.sqrt 2 ≤ 3 / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  set ω : ℝ := Real.sqrt 2 * lam * (1 / L) with hωdef
  have hω0 : 0 ≤ ω := by positivity
  have hωle : ω ≤ 2 / L := by
    rw [hωdef]
    rw [div_eq_mul_one_div 2 L]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith
  -- names for the factors
  set c : ℝ → ℝ := fun u => vStar lam (u / L) with hcdef
  set g : ℝ → ℝ := fun u => Taper.phi ϱ L w u ^ 2 with hgdef
  have hgC : ContDiff ℝ 3 g := (Taper.phi_contDiff hϱ hw0 hwL').pow 2
  have hgd : Differentiable ℝ g := hgC.differentiable (by norm_num)
  have hg1C : ContDiff ℝ 2 (deriv g) := hgC.deriv'
  have hg1d : Differentiable ℝ (deriv g) := hg1C.differentiable (by norm_num)
  have hg1 : ∀ u, HasDerivAt g (deriv g u) u := fun u => (hgd u).hasDerivAt
  have hg2 : ∀ u, HasDerivAt (deriv g) (deriv (deriv g) u) u := fun u => (hg1d u).hasDerivAt
  -- first derivative of F := c·g
  have hF1 : deriv (fun u => c u * g u) = fun u => (-ω * Real.sin (Real.sqrt 2 * lam * (u / L)))
      * g u + c u * deriv g u := by
    funext u
    exact ((hasDerivAt_cosFactor u).mul (hg1 u)).deriv
  -- second derivative
  have hF2 : ∀ u, deriv (deriv (fun u => c u * g u)) u
      = (-ω ^ 2 * Real.cos (Real.sqrt 2 * lam * (u / L))) * g u
        + 2 * ((-ω * Real.sin (Real.sqrt 2 * lam * (u / L))) * deriv g u)
        + c u * deriv (deriv g) u := by
    intro u
    rw [hF1]
    have hstep : HasDerivAt (fun u => (-ω * Real.sin (Real.sqrt 2 * lam * (u / L))) * g u
        + c u * deriv g u)
        ((-ω ^ 2 * Real.cos (Real.sqrt 2 * lam * (u / L))) * g u
          + (-ω * Real.sin (Real.sqrt 2 * lam * (u / L))) * deriv g u
          + ((-ω * Real.sin (Real.sqrt 2 * lam * (u / L))) * deriv g u
            + c u * deriv (deriv g) u)) u :=
      (((hasDerivAt_cosFactor' u).mul (hg1 u)).add ((hasDerivAt_cosFactor u).mul (hg2 u)))
    rw [hstep.deriv]
    ring
  -- rewrite the goal through φ_D² = c·g
  rw [show (fun u => phiD ϱ lam L w u ^ 2) = fun u => c u * g u from
    phiD_sq_eq hϱ h0 h1 hw0 hwL']
  -- support restriction
  have hsupp : ∀ x : ℝ, L / 2 ≤ |x| → c x * g x = 0 := by
    intro x hx
    rw [hgdef]
    simp only
    rw [Taper.phi_eq_zero hϱ hw0 hx]
    ring
  have hrestr : ∫ u, |deriv (deriv (fun u => c u * g u)) u|
      = ∫ u in Set.Icc (-(L/2)) (L/2), |deriv (deriv (fun u => c u * g u)) u| :=
    integral_abs_eq_setIntegral (by positivity) (fun x hx => deriv2_eq_zero_outside hsupp hx)
  rw [hrestr]
  -- pointwise bound and integration
  have hgle : ∀ u, g u ≤ 1 := by
    intro u
    rw [hgdef]
    simp only
    calc Taper.phi ϱ L w u ^ 2 ≤ 1 ^ 2 :=
          pow_le_pow_left₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) 2
      _ = 1 := one_pow 2
  have hg0 : ∀ u, 0 ≤ g u := fun u => sq_nonneg _
  have hcle : ∀ u, |c u| ≤ 1 := fun u => Real.abs_cos_le_one _
  have hpt : ∀ u, |deriv (deriv (fun u => c u * g u)) u|
      ≤ ω ^ 2 + 2 * ω * |deriv g u| + |deriv (deriv g) u| := by
    intro u
    rw [hF2 u]
    have e1 : |(-ω ^ 2 * Real.cos (Real.sqrt 2 * lam * (u / L))) * g u| ≤ ω ^ 2 := by
      rw [abs_mul, abs_mul, abs_neg, abs_pow, abs_of_nonneg hω0]
      calc ω ^ 2 * |Real.cos (Real.sqrt 2 * lam * (u / L))| * |g u|
          ≤ ω ^ 2 * 1 * 1 := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity))
              (by rw [abs_of_nonneg (hg0 u)]; exact hgle u) (abs_nonneg _) (by positivity)
        _ = ω ^ 2 := by ring
    have e2 : |2 * ((-ω * Real.sin (Real.sqrt 2 * lam * (u / L))) * deriv g u)|
        ≤ 2 * ω * |deriv g u| := by
      rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg hω0]
      rw [show |(2:ℝ)| = 2 from abs_of_pos two_pos]
      calc 2 * (ω * |Real.sin (Real.sqrt 2 * lam * (u / L))| * |deriv g u|)
          ≤ 2 * (ω * 1 * |deriv g u|) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hω0
        _ = 2 * ω * |deriv g u| := by ring
    have e3 : |c u * deriv (deriv g) u| ≤ |deriv (deriv g) u| := by
      rw [abs_mul]
      calc |c u| * |deriv (deriv g) u| ≤ 1 * |deriv (deriv g) u| :=
            mul_le_mul_of_nonneg_right (hcle u) (abs_nonneg _)
        _ = _ := one_mul _
    calc |(-ω ^ 2 * Real.cos (Real.sqrt 2 * lam * (u / L))) * g u
          + 2 * ((-ω * Real.sin (Real.sqrt 2 * lam * (u / L))) * deriv g u)
          + c u * deriv (deriv g) u|
        ≤ |(-ω ^ 2 * Real.cos (Real.sqrt 2 * lam * (u / L))) * g u
            + 2 * ((-ω * Real.sin (Real.sqrt 2 * lam * (u / L))) * deriv g u)|
          + |c u * deriv (deriv g) u| := abs_add_le _ _
      _ ≤ |(-ω ^ 2 * Real.cos (Real.sqrt 2 * lam * (u / L))) * g u|
          + |2 * ((-ω * Real.sin (Real.sqrt 2 * lam * (u / L))) * deriv g u)|
          + |c u * deriv (deriv g) u| := by
            linarith [abs_add_le ((-ω ^ 2 * Real.cos (Real.sqrt 2 * lam * (u / L))) * g u)
              (2 * ((-ω * Real.sin (Real.sqrt 2 * lam * (u / L))) * deriv g u))]
      _ ≤ _ := by linarith [e1, e2, e3]
  -- integrability of the majorant pieces (continuous with compact support / on compact)
  have hg1cont : Continuous (deriv g) := hg1C.continuous
  have hg2cont : Continuous (deriv (deriv g)) := hg1C.continuous_deriv (by norm_num)
  have iconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (ω ^ 2 : ℝ))
      (Set.Icc (-(L/2)) (L/2)) :=
    MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have iabs1 : MeasureTheory.IntegrableOn (fun u => 2 * ω * |deriv g u|)
      (Set.Icc (-(L/2)) (L/2)) :=
    ((hg1cont.abs.continuousOn).integrableOn_compact isCompact_Icc).const_mul _
  have iabs2 : MeasureTheory.IntegrableOn (fun u => |deriv (deriv g) u|)
      (Set.Icc (-(L/2)) (L/2)) :=
    (hg2cont.abs.continuousOn).integrableOn_compact isCompact_Icc
  have isum : MeasureTheory.IntegrableOn (fun u => ω ^ 2 + 2 * ω * |deriv g u|)
      (Set.Icc (-(L/2)) (L/2)) :=
    ((by fun_prop : Continuous fun u : ℝ => ω ^ 2 + 2 * ω * |deriv g u|)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hmajint : MeasureTheory.IntegrableOn
      (fun u => ω ^ 2 + 2 * ω * |deriv g u| + |deriv (deriv g) u|)
      (Set.Icc (-(L/2)) (L/2)) :=
    ((by fun_prop : Continuous fun u : ℝ =>
      ω ^ 2 + 2 * ω * |deriv g u| + |deriv (deriv g) u|)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hmono : ∫ u in Set.Icc (-(L/2)) (L/2), |deriv (deriv (fun u => c u * g u)) u|
      ≤ ∫ u in Set.Icc (-(L/2)) (L/2),
          (ω ^ 2 + 2 * ω * |deriv g u| + |deriv (deriv g) u|) := by
    apply MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) hmajint
      (MeasureTheory.ae_of_all _ fun u => hpt u)
  refine le_trans hmono ?_
  -- evaluate the majorant integral
  have hIg1 : Integrable (fun u => |deriv g u|) := by
    apply hg1cont.abs.integrable_of_hasCompactSupport
    apply HasCompactSupport.abs
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := -(L/2)) (b := L/2))
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hmem
    apply hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
    have : L / 2 < |x| := by
      rcases hmem with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    -- deriv g = 0 beyond the support of g
    have hopen : IsOpen {v : ℝ | L / 2 < |v|} := (continuous_abs).isOpen_preimage _ isOpen_Ioi
    have hEq : g =ᶠ[nhds x] (fun _ => (0:ℝ)) := by
      filter_upwards [hopen.mem_nhds this] with v hv
      rw [hgdef]
      simp only
      rw [Taper.phi_eq_zero hϱ hw0 (le_of_lt hv), zero_pow two_ne_zero]
    rw [hEq.deriv_eq, deriv_const]
  have hIg2 : Integrable (fun u => |deriv (deriv g) u|) := by
    apply hg2cont.abs.integrable_of_hasCompactSupport
    apply HasCompactSupport.abs
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := -(L/2)) (b := L/2))
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hmem
    apply hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
    have hgt : L / 2 < |x| := by
      rcases hmem with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    exact deriv2_eq_zero_outside (fun t ht => by
      rw [hgdef]; simp only; rw [Taper.phi_eq_zero hϱ hw0 ht, zero_pow two_ne_zero]) hgt
  have hsplit2 : ∫ u in Set.Icc (-(L/2)) (L/2),
      (ω ^ 2 + 2 * ω * |deriv g u| + |deriv (deriv g) u|)
      ≤ ω ^ 2 * L + 2 * ω * 2 + Taper.cRho ϱ / w := by
    have ea : ∫ u in Set.Icc (-(L/2)) (L/2), (ω ^ 2 + 2 * ω * |deriv g u|)
        = (∫ u in Set.Icc (-(L/2)) (L/2), (ω ^ 2 : ℝ))
          + ∫ u in Set.Icc (-(L/2)) (L/2), (2 * ω * |deriv g u|) :=
      MeasureTheory.integral_add iconst iabs1
    have eb : ∫ u in Set.Icc (-(L/2)) (L/2), (2 * ω * |deriv g u|)
        = 2 * ω * ∫ u in Set.Icc (-(L/2)) (L/2), |deriv g u| :=
      MeasureTheory.integral_const_mul _ _
    have e1 : ∫ u in Set.Icc (-(L/2)) (L/2), (ω ^ 2 + 2 * ω * |deriv g u|
        + |deriv (deriv g) u|)
        = (∫ u in Set.Icc (-(L/2)) (L/2), (ω ^ 2 : ℝ))
          + 2 * ω * (∫ u in Set.Icc (-(L/2)) (L/2), |deriv g u|)
          + ∫ u in Set.Icc (-(L/2)) (L/2), |deriv (deriv g) u| := by
      calc ∫ u in Set.Icc (-(L/2)) (L/2), (ω ^ 2 + 2 * ω * |deriv g u| + |deriv (deriv g) u|)
          = (∫ u in Set.Icc (-(L/2)) (L/2), (ω ^ 2 + 2 * ω * |deriv g u|))
            + ∫ u in Set.Icc (-(L/2)) (L/2), |deriv (deriv g) u| :=
            MeasureTheory.integral_add isum iabs2
        _ = _ := by rw [ea, eb]
    rw [e1]
    have c1 : ∫ u in Set.Icc (-(L/2)) (L/2), (ω ^ 2 : ℝ) ≤ ω ^ 2 * L := by
      rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
      nlinarith [sq_nonneg ω]
    have c2 : ∫ u in Set.Icc (-(L/2)) (L/2), |deriv g u| ≤ 2 := by
      refine le_trans (MeasureTheory.setIntegral_le_integral hIg1
        (MeasureTheory.ae_of_all _ fun u => abs_nonneg _)) ?_
      rw [hgdef]
      exact le_of_eq (Taper.integral_abs_deriv_phi_sq hϱ hw0 hwL')
    have c3 : ∫ u in Set.Icc (-(L/2)) (L/2), |deriv (deriv g) u| ≤ Taper.cRho ϱ / w := by
      refine le_trans (MeasureTheory.setIntegral_le_integral hIg2
        (MeasureTheory.ae_of_all _ fun u => abs_nonneg _)) ?_
      rw [hgdef]
      exact Taper.integral_abs_deriv2_phi_sq_le hϱ hw hwL'
    have hω0' : (0:ℝ) ≤ 2 * ω := by positivity
    nlinarith [mul_le_mul_of_nonneg_left c2 hω0']
  refine le_trans hsplit2 ?_
  -- final arithmetic: ω ≤ 2/L, L ≥ 8w, cRho ≥ 4
  have hcr := Taper.cRho_eq ϱ
  have hc4 : (0:ℝ) ≤ Taper.cRho ϱ := by
    have := Taper.four_le_cRho hϱ
    linarith
  have hωL : ω ^ 2 * L ≤ 4 / L := by
    calc ω ^ 2 * L ≤ (2/L) ^ 2 * L := by
          apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hω0 hωle 2) hL.le
      _ = 4 / L := by field_simp; ring
    
  have hLw : 1 / L ≤ 1 / (8 * w) := by
    apply one_div_le_one_div_of_le (by positivity) hwL
  have hfin : 4 / L + 2 * ω * 2 + Taper.cRho ϱ / w ≤ cDT ϱ lam / w := by
    have h4L : 4 / L ≤ 1 / w := by
      rw [div_le_div_iff₀ hL hw0]
      linarith
    have h2ω : 2 * ω * 2 ≤ 1 / w := by
      have h8 : 8 / L ≤ 1 / w := by
        rw [div_le_div_iff₀ hL hw0]
        linarith
      have h4ω : 2 * ω * 2 ≤ 8 / L := by
        have := hωle
        have e : (8:ℝ) / L = 4 * (2 / L) := by ring
        rw [e]
        linarith
      linarith
    have hcdt : (2 + Taper.cRho ϱ) / w ≤ cDT ϱ lam / w := by
      apply div_le_div_of_nonneg_right ?_ hw0.le
      unfold cDT
      nlinarith [hc4, sq_nonneg lam]
    have : 4 / L + 2 * ω * 2 + Taper.cRho ϱ / w ≤ (2 + Taper.cRho ϱ) / w := by
      have expand : (2 + Taper.cRho ϱ) / w = 1 / w + 1 / w + Taper.cRho ϱ / w := by
        field_simp
        ring
      rw [expand]
      linarith [h4L, h2ω]
    linarith [hcdt]
  linarith [hωL, hfin]

set_option maxHeartbeats 1000000 in
theorem integral_abs_deriv2_phiD_le (hϱ : TaperProfile ϱ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ u, |deriv (deriv (phiD ϱ lam L w)) u| ≤ cDT ϱ lam / w := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hs32 : Real.sqrt 2 ≤ 3 / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  set ω : ℝ := Real.sqrt 2 * lam * (1 / L) with hωdef
  have hω0 : 0 ≤ ω := by positivity
  have hωle : ω ≤ 2 / L := by
    rw [hωdef, div_eq_mul_one_div 2 L]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith
  set c : ℝ → ℝ := fun u => vStar lam (u / L) with hcdef
  set U : Set ℝ := {v : ℝ | |v| < 2 * L / 3} with hUdef
  have hUopen : IsOpen U := (continuous_abs).isOpen_preimage _ isOpen_Iio
  have hIccU : Set.Icc (-(L/2)) (L/2) ⊆ U := by
    intro x hx
    show |x| < 2 * L / 3
    have : |x| ≤ L / 2 := abs_le.mpr ⟨hx.1, hx.2⟩
    linarith
  have hUc : ∀ u ∈ U, 1 / 2 < c u := by
    intro u hu
    have hu' : |u| < 2 * L / 3 := hu
    have h1' : Real.sqrt 2 * lam ≤ 3 / 2 := by
      calc Real.sqrt 2 * lam ≤ (3/2) * 1 := mul_le_mul hs32 h1 h0.le (by norm_num)
        _ = 3 / 2 := mul_one _
    have h2' : |u| / L < 2 / 3 := by
      rw [div_lt_iff₀ hL]
      linarith
    have habs : |Real.sqrt 2 * lam * (u / L)| < 1 := by
      rw [abs_mul, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt 2 * lam),
        abs_of_pos hL]
      calc Real.sqrt 2 * lam * (|u| / L) ≤ (3/2) * (|u| / L) :=
            mul_le_mul_of_nonneg_right h1' (by positivity)
        _ < (3/2) * (2/3) := mul_lt_mul_of_pos_left h2' (by norm_num)
        _ = 1 := by norm_num
    have harg2 : (Real.sqrt 2 * lam * (u / L)) ^ 2 < 1 := by
      calc (Real.sqrt 2 * lam * (u / L)) ^ 2 = |Real.sqrt 2 * lam * (u / L)| ^ 2 :=
            (sq_abs _).symm
        _ < 1 ^ 2 := by
            apply pow_lt_pow_left₀ habs (abs_nonneg _) (by norm_num)
        _ = 1 := one_pow 2
    have := Real.one_sub_sq_div_two_le_cos (x := Real.sqrt 2 * lam * (u / L))
    rw [hcdef]
    simp only
    unfold vStar
    linarith
  have hUc0 : ∀ u ∈ U, c u ≠ 0 := fun u hu => by linarith [hUc u hu]
  have hsqrtc : ∀ u ∈ U, 1 / 2 ≤ Real.sqrt (c u) := by
    intro u hu
    rw [show (1:ℝ)/2 = Real.sqrt ((1/2)^2) from (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt
    nlinarith [hUc u hu]
  have hsqrtc1 : ∀ u : ℝ, Real.sqrt (c u) ≤ 1 := by
    intro u
    rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    apply Real.sqrt_le_sqrt
    rw [hcdef]
    simp only
    unfold vStar
    exact Real.cos_le_one _
  -- cosine-factor derivatives (global)
  have hc1 : ∀ u : ℝ, HasDerivAt c (-ω * Real.sin (Real.sqrt 2 * lam * (u / L))) u := by
    intro u
    have h := hasDerivAt_cosFactor (lam := lam) (L := L) u
    rw [hcdef]
    convert h using 1
  set c1 : ℝ → ℝ := fun u => -ω * Real.sin (Real.sqrt 2 * lam * (u / L)) with hc1def
  have hc2 : ∀ u : ℝ, HasDerivAt c1 (-ω ^ 2 * Real.cos (Real.sqrt 2 * lam * (u / L))) u := by
    intro u
    have h := hasDerivAt_cosFactor' (lam := lam) (L := L) u
    have e : c1 = fun u : ℝ => -(Real.sqrt 2 * lam * (1 / L))
        * Real.sin (Real.sqrt 2 * lam * (u / L)) := by
      rw [hc1def, hωdef]
    rw [e]
    convert h using 1
  have hc1abs : ∀ u : ℝ, |c1 u| ≤ ω := by
    intro u
    rw [hc1def]
    simp only
    rw [abs_mul, abs_neg, abs_of_nonneg hω0]
    calc ω * |Real.sin (Real.sqrt 2 * lam * (u / L))| ≤ ω * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hω0
      _ = ω := mul_one _
  have hc2abs : ∀ u : ℝ, |(-ω ^ 2 * Real.cos (Real.sqrt 2 * lam * (u / L)))| ≤ ω ^ 2 := by
    intro u
    rw [abs_mul, abs_neg, abs_pow, abs_of_nonneg hω0]
    calc ω ^ 2 * |Real.cos (Real.sqrt 2 * lam * (u / L))| ≤ ω ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)
      _ = ω ^ 2 := mul_one _
  -- √(cosine factor) and its derivatives on U
  set q : ℝ → ℝ := fun u => Real.sqrt (c u) with hqdef
  set q1 : ℝ → ℝ := fun u => c1 u / (2 * Real.sqrt (c u)) with hq1def
  have hq1 : ∀ u ∈ U, HasDerivAt q (q1 u) u := fun u hu => (hc1 u).sqrt (hUc0 u hu)
  have hq1abs : ∀ u ∈ U, |q1 u| ≤ ω := by
    intro u hu
    rw [hq1def]
    simp only
    rw [abs_div]
    have hden : (1:ℝ) ≤ |2 * Real.sqrt (c u)| := by
      rw [abs_of_pos (by nlinarith [hsqrtc u hu] : (0:ℝ) < 2 * Real.sqrt (c u))]
      nlinarith [hsqrtc u hu]
    calc |c1 u| / |2 * Real.sqrt (c u)| ≤ |c1 u| / 1 :=
          div_le_div_of_nonneg_left (abs_nonneg _) one_pos hden
      _ = |c1 u| := div_one _
      _ ≤ ω := hc1abs u
  set q2 : ℝ → ℝ := fun u => ((-ω ^ 2 * Real.cos (Real.sqrt 2 * lam * (u / L)))
      * (2 * Real.sqrt (c u)) - c1 u * (2 * q1 u)) / (2 * Real.sqrt (c u)) ^ 2 with hq2def
  have hq2 : ∀ u ∈ U, HasDerivAt q1 (q2 u) u := by
    intro u hu
    have hden : (2 : ℝ) * Real.sqrt (c u) ≠ 0 := by nlinarith [hsqrtc u hu]
    have h2q : HasDerivAt (fun y => 2 * Real.sqrt (c y)) (2 * q1 u) u := (hq1 u hu).const_mul 2
    exact (hc2 u).div h2q hden
  have hq2abs : ∀ u ∈ U, |q2 u| ≤ 4 * ω ^ 2 := by
    intro u hu
    rw [hq2def]
    simp only
    rw [abs_div]
    have hs05 := hsqrtc u hu
    have hs1 := hsqrtc1 u
    have hdenge : (1:ℝ) ≤ |(2 * Real.sqrt (c u)) ^ 2| := by
      rw [abs_of_pos (by nlinarith : (0:ℝ) < (2 * Real.sqrt (c u)) ^ 2)]
      nlinarith
    have hnum : |(-ω ^ 2 * Real.cos (Real.sqrt 2 * lam * (u / L))) * (2 * Real.sqrt (c u))
        - c1 u * (2 * q1 u)| ≤ 4 * ω ^ 2 := by
      have e1 : |(-ω ^ 2 * Real.cos (Real.sqrt 2 * lam * (u / L))) * (2 * Real.sqrt (c u))|
          ≤ 2 * ω ^ 2 := by
        rw [abs_mul]
        calc |(-ω ^ 2 * Real.cos (Real.sqrt 2 * lam * (u / L)))| * |2 * Real.sqrt (c u)|
            ≤ ω ^ 2 * 2 := by
              apply mul_le_mul (hc2abs u) ?_ (abs_nonneg _) (by positivity)
              rw [abs_of_pos (by nlinarith : (0:ℝ) < 2 * Real.sqrt (c u))]
              nlinarith
          _ = 2 * ω ^ 2 := by ring
      have e2 : |c1 u * (2 * q1 u)| ≤ 2 * ω ^ 2 := by
        rw [abs_mul]
        have h2q : |2 * q1 u| ≤ 2 * ω := by
          rw [abs_mul, show |(2:ℝ)| = 2 from abs_of_pos two_pos]
          exact mul_le_mul_of_nonneg_left (hq1abs u hu) (by norm_num)
        calc |c1 u| * |2 * q1 u| ≤ ω * (2 * ω) :=
              mul_le_mul (hc1abs u) h2q (abs_nonneg _) hω0
          _ = 2 * ω ^ 2 := by ring
      calc |(-ω ^ 2 * Real.cos (Real.sqrt 2 * lam * (u / L))) * (2 * Real.sqrt (c u))
          - c1 u * (2 * q1 u)|
          ≤ |(-ω ^ 2 * Real.cos (Real.sqrt 2 * lam * (u / L))) * (2 * Real.sqrt (c u))|
            + |c1 u * (2 * q1 u)| := abs_sub _ _
        _ ≤ 4 * ω ^ 2 := by linarith
    calc |(-ω ^ 2 * Real.cos (Real.sqrt 2 * lam * (u / L))) * (2 * Real.sqrt (c u))
        - c1 u * (2 * q1 u)| / |(2 * Real.sqrt (c u)) ^ 2|
        ≤ |(-ω ^ 2 * Real.cos (Real.sqrt 2 * lam * (u / L))) * (2 * Real.sqrt (c u))
            - c1 u * (2 * q1 u)| / 1 :=
          div_le_div_of_nonneg_left (abs_nonneg _) one_pos hdenge
      _ ≤ 4 * ω ^ 2 := by rw [div_one]; exact hnum
  -- φ and its derivatives
  set φf : ℝ → ℝ := Taper.phi ϱ L w with hφdef
  have hφC : ContDiff ℝ 3 φf := Taper.phi_contDiff hϱ hw0 hwL'
  have hφd : Differentiable ℝ φf := hφC.differentiable (by norm_num)
  have hφ1C : ContDiff ℝ 2 (deriv φf) := hφC.deriv'
  have hφ1d : Differentiable ℝ (deriv φf) := hφ1C.differentiable (by norm_num)
  have hφ1 : ∀ u, HasDerivAt φf (deriv φf u) u := fun u => (hφd u).hasDerivAt
  have hφ2 : ∀ u, HasDerivAt (deriv φf) (deriv (deriv φf) u) u := fun u => (hφ1d u).hasDerivAt
  have hφ1cont : Continuous (deriv φf) := hφ1C.continuous
  have hφ2cont : Continuous (deriv (deriv φf)) := hφ1C.continuous_deriv (by norm_num)
  -- first derivative of φ_D on U
  have hD1 : ∀ u ∈ U, HasDerivAt (phiD ϱ lam L w) (q1 u * φf u + q u * deriv φf u) u := by
    intro u hu
    have h := (hq1 u hu).mul (hφ1 u)
    exact h
  have hder1 : ∀ u ∈ U, deriv (phiD ϱ lam L w) u = q1 u * φf u + q u * deriv φf u :=
    fun u hu => (hD1 u hu).deriv
  -- second derivative on U
  have hdd : ∀ x ∈ U, deriv (deriv (phiD ϱ lam L w)) x
      = q2 x * φf x + 2 * (q1 x * deriv φf x) + q x * deriv (deriv φf) x := by
    intro x hx
    have hEq : deriv (phiD ϱ lam L w) =ᶠ[nhds x]
        (fun u => q1 u * φf u + q u * deriv φf u) := by
      filter_upwards [hUopen.mem_nhds hx] with v hv
      exact hder1 v hv
    rw [hEq.deriv_eq]
    have hstep : HasDerivAt (fun u => q1 u * φf u + q u * deriv φf u)
        (q2 x * φf x + q1 x * deriv φf x + (q1 x * deriv φf x + q x * deriv (deriv φf) x)) x :=
      ((hq2 x hx).mul (hφ1 x)).add ((hq1 x hx).mul (hφ2 x))
    rw [hstep.deriv]
    ring
  -- support restriction
  have hsuppD : ∀ x : ℝ, L / 2 ≤ |x| → phiD ϱ lam L w x = 0 := fun x hx =>
    phiD_eq_zero hϱ hw0 hx
  have hrestr : ∫ u, |deriv (deriv (phiD ϱ lam L w)) u|
      = ∫ u in Set.Icc (-(L/2)) (L/2), |deriv (deriv (phiD ϱ lam L w)) u| :=
    integral_abs_eq_setIntegral (by positivity)
      (fun x hx => deriv2_eq_zero_outside hsuppD hx)
  rw [hrestr]
  -- pointwise bound on the support interval
  have hpt : ∀ u ∈ Set.Icc (-(L/2)) (L/2), |deriv (deriv (phiD ϱ lam L w)) u|
      ≤ 4 * ω ^ 2 + 2 * ω * |deriv φf u| + |deriv (deriv φf) u| := by
    intro u hu
    have huU := hIccU hu
    rw [hdd u huU]
    have e1 : |q2 u * φf u| ≤ 4 * ω ^ 2 := by
      rw [abs_mul]
      calc |q2 u| * |φf u| ≤ (4 * ω ^ 2) * 1 := by
            apply mul_le_mul (hq2abs u huU) ?_ (abs_nonneg _) (by positivity)
            rw [hφdef, abs_of_nonneg (Taper.phi_nonneg hϱ u)]
            exact Taper.phi_le_one hϱ u
        _ = 4 * ω ^ 2 := mul_one _
    have e2 : |2 * (q1 u * deriv φf u)| ≤ 2 * ω * |deriv φf u| := by
      rw [abs_mul, abs_mul, show |(2:ℝ)| = 2 from abs_of_pos two_pos]
      calc 2 * (|q1 u| * |deriv φf u|) ≤ 2 * (ω * |deriv φf u|) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact mul_le_mul_of_nonneg_right (hq1abs u huU) (abs_nonneg _)
        _ = 2 * ω * |deriv φf u| := by ring
    have e3 : |q u * deriv (deriv φf) u| ≤ |deriv (deriv φf) u| := by
      rw [abs_mul]
      have : |q u| ≤ 1 := by
        rw [hqdef, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact hsqrtc1 u
      calc |q u| * |deriv (deriv φf) u| ≤ 1 * |deriv (deriv φf) u| :=
            mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ = _ := one_mul _
    calc |q2 u * φf u + 2 * (q1 u * deriv φf u) + q u * deriv (deriv φf) u|
        ≤ |q2 u * φf u + 2 * (q1 u * deriv φf u)| + |q u * deriv (deriv φf) u| := abs_add_le _ _
      _ ≤ |q2 u * φf u| + |2 * (q1 u * deriv φf u)| + |q u * deriv (deriv φf) u| := by
          linarith [abs_add_le (q2 u * φf u) (2 * (q1 u * deriv φf u))]
      _ ≤ _ := by linarith
  -- integrability and evaluation of the majorant
  have iconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (4 * ω ^ 2 : ℝ))
      (Set.Icc (-(L/2)) (L/2)) :=
    MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have iabs1 : MeasureTheory.IntegrableOn (fun u => 2 * ω * |deriv φf u|)
      (Set.Icc (-(L/2)) (L/2)) :=
    ((hφ1cont.abs.continuousOn).integrableOn_compact isCompact_Icc).const_mul _
  have iabs2 : MeasureTheory.IntegrableOn (fun u => |deriv (deriv φf) u|)
      (Set.Icc (-(L/2)) (L/2)) :=
    (hφ2cont.abs.continuousOn).integrableOn_compact isCompact_Icc
  have isum : MeasureTheory.IntegrableOn (fun u => 4 * ω ^ 2 + 2 * ω * |deriv φf u|)
      (Set.Icc (-(L/2)) (L/2)) :=
    ((by fun_prop : Continuous fun u : ℝ => 4 * ω ^ 2 + 2 * ω * |deriv φf u|)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hmajint : MeasureTheory.IntegrableOn
      (fun u => 4 * ω ^ 2 + 2 * ω * |deriv φf u| + |deriv (deriv φf) u|)
      (Set.Icc (-(L/2)) (L/2)) :=
    ((by fun_prop : Continuous fun u : ℝ =>
      4 * ω ^ 2 + 2 * ω * |deriv φf u| + |deriv (deriv φf) u|)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hIφD : MeasureTheory.IntegrableOn (fun u => |deriv (deriv (phiD ϱ lam L w)) u|)
      (Set.Icc (-(L/2)) (L/2)) := by
    have hd1C : ContDiff ℝ 1 (deriv (phiD ϱ lam L w)) :=
      (phiD_contDiff hϱ h0 h1 hw0 hwL').deriv'
    have hcont2 : Continuous (deriv (deriv (phiD ϱ lam L w))) :=
      hd1C.continuous_deriv (by norm_num)
    exact (hcont2.abs.continuousOn).integrableOn_compact isCompact_Icc
  have hmono : ∫ u in Set.Icc (-(L/2)) (L/2), |deriv (deriv (phiD ϱ lam L w)) u|
      ≤ ∫ u in Set.Icc (-(L/2)) (L/2),
          (4 * ω ^ 2 + 2 * ω * |deriv φf u| + |deriv (deriv φf) u|) :=
    MeasureTheory.setIntegral_mono_on hIφD hmajint measurableSet_Icc hpt
  refine le_trans hmono ?_
  -- integrals of |φ'| and |φ''| over ℝ (compact support)
  have hIg1 : Integrable (fun u => |deriv φf u|) := by
    apply hφ1cont.abs.integrable_of_hasCompactSupport
    apply HasCompactSupport.abs
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := -(L/2)) (b := L/2))
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hmem
    apply hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
    have hgt : L / 2 < |x| := by
      rcases hmem with h | h
      · rw [abs_of_neg (by linarith : x < 0)]; linarith
      · rw [abs_of_pos (by linarith : 0 < x)]; linarith
    have hopen : IsOpen {v : ℝ | L / 2 < |v|} := (continuous_abs).isOpen_preimage _ isOpen_Ioi
    have hEq : φf =ᶠ[nhds x] (fun _ => (0:ℝ)) := by
      filter_upwards [hopen.mem_nhds hgt] with v hv
      rw [hφdef]
      exact Taper.phi_eq_zero hϱ hw0 (le_of_lt hv)
    rw [hEq.deriv_eq, deriv_const]
  have hIg2 : Integrable (fun u => |deriv (deriv φf) u|) := by
    apply hφ2cont.abs.integrable_of_hasCompactSupport
    apply HasCompactSupport.abs
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := -(L/2)) (b := L/2))
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hmem
    apply hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
    have hgt : L / 2 < |x| := by
      rcases hmem with h | h
      · rw [abs_of_neg (by linarith : x < 0)]; linarith
      · rw [abs_of_pos (by linarith : 0 < x)]; linarith
    exact deriv2_eq_zero_outside (fun t ht => by
      rw [hφdef]; exact Taper.phi_eq_zero hϱ hw0 ht) hgt
  have hsplit2 : ∫ u in Set.Icc (-(L/2)) (L/2),
      (4 * ω ^ 2 + 2 * ω * |deriv φf u| + |deriv (deriv φf) u|)
      ≤ 4 * ω ^ 2 * L + 2 * ω * 2 + Taper.cRho ϱ / (2 * w) := by
    have ea : ∫ u in Set.Icc (-(L/2)) (L/2), (4 * ω ^ 2 + 2 * ω * |deriv φf u|)
        = (∫ u in Set.Icc (-(L/2)) (L/2), (4 * ω ^ 2 : ℝ))
          + ∫ u in Set.Icc (-(L/2)) (L/2), (2 * ω * |deriv φf u|) :=
      MeasureTheory.integral_add iconst iabs1
    have eb : ∫ u in Set.Icc (-(L/2)) (L/2), (2 * ω * |deriv φf u|)
        = 2 * ω * ∫ u in Set.Icc (-(L/2)) (L/2), |deriv φf u| :=
      MeasureTheory.integral_const_mul _ _
    have e1 : ∫ u in Set.Icc (-(L/2)) (L/2), (4 * ω ^ 2 + 2 * ω * |deriv φf u|
        + |deriv (deriv φf) u|)
        = (∫ u in Set.Icc (-(L/2)) (L/2), (4 * ω ^ 2 : ℝ))
          + 2 * ω * (∫ u in Set.Icc (-(L/2)) (L/2), |deriv φf u|)
          + ∫ u in Set.Icc (-(L/2)) (L/2), |deriv (deriv φf) u| := by
      calc ∫ u in Set.Icc (-(L/2)) (L/2),
            (4 * ω ^ 2 + 2 * ω * |deriv φf u| + |deriv (deriv φf) u|)
          = (∫ u in Set.Icc (-(L/2)) (L/2), (4 * ω ^ 2 + 2 * ω * |deriv φf u|))
            + ∫ u in Set.Icc (-(L/2)) (L/2), |deriv (deriv φf) u| :=
            MeasureTheory.integral_add isum iabs2
        _ = _ := by rw [ea, eb]
    rw [e1]
    have c1b : ∫ u in Set.Icc (-(L/2)) (L/2), (4 * ω ^ 2 : ℝ) ≤ 4 * ω ^ 2 * L := by
      rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
      nlinarith [sq_nonneg ω]
    have c2b : ∫ u in Set.Icc (-(L/2)) (L/2), |deriv φf u| ≤ 2 := by
      refine le_trans (MeasureTheory.setIntegral_le_integral hIg1
        (MeasureTheory.ae_of_all _ fun u => abs_nonneg _)) ?_
      rw [hφdef]
      exact le_of_eq (Taper.integral_abs_deriv_phi hϱ hw0 hwL')
    have c3b : ∫ u in Set.Icc (-(L/2)) (L/2), |deriv (deriv φf) u|
        ≤ Taper.cRho ϱ / (2 * w) := by
      refine le_trans (MeasureTheory.setIntegral_le_integral hIg2
        (MeasureTheory.ae_of_all _ fun u => abs_nonneg _)) ?_
      rw [hφdef]
      rw [Taper.integral_abs_deriv2_phi hϱ hw0 hwL']
      rw [div_le_div_iff₀ hw0 (by positivity)]
      have hcr := Taper.cRho_eq ϱ
      have hsup0 : 0 ≤ Taper.supDeriv ϱ := Real.iSup_nonneg fun x => abs_nonneg _
      nlinarith [mul_nonneg hsup0 hw0.le]
    have hω0' : (0:ℝ) ≤ 2 * ω := by positivity
    nlinarith [mul_le_mul_of_nonneg_left c2b hω0']
  refine le_trans hsplit2 ?_
  -- final arithmetic
  have hc4 : (0:ℝ) ≤ Taper.cRho ϱ := by linarith [Taper.four_le_cRho hϱ]
  have hωL : 4 * ω ^ 2 * L ≤ 16 / L := by
    calc 4 * ω ^ 2 * L ≤ 4 * (2/L) ^ 2 * L := by
          apply mul_le_mul_of_nonneg_right _ hL.le
          apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hω0 hωle 2) (by norm_num)
      _ = 16 / L := by field_simp; ring
  have h4L : 16 / L ≤ 2 / w := by
    rw [div_le_div_iff₀ hL hw0]
    linarith
  have h2ω : 2 * ω * 2 ≤ 1 / w := by
    have h8 : 8 / L ≤ 1 / w := by
      rw [div_le_div_iff₀ hL hw0]
      linarith
    have h4ω : 2 * ω * 2 ≤ 8 / L := by
      have e : (8:ℝ) / L = 4 * (2 / L) := by ring
      rw [e]
      linarith
    linarith
  have hcrw : Taper.cRho ϱ / (2 * w) ≤ Taper.cRho ϱ / w := by
    apply div_le_div_of_nonneg_left hc4 hw0
    linarith
  have hcdt : (3 + Taper.cRho ϱ) / w ≤ cDT ϱ lam / w := by
    apply div_le_div_of_nonneg_right ?_ hw0.le
    unfold cDT
    nlinarith [hc4, sq_nonneg lam]
  calc 4 * ω ^ 2 * L + 2 * ω * 2 + Taper.cRho ϱ / (2 * w)
      ≤ 2 / w + 1 / w + Taper.cRho ϱ / w := by linarith [hωL, h4L, h2ω, hcrw]
    _ = (3 + Taper.cRho ϱ) / w := by
        field_simp
        ring
    _ ≤ cDT ϱ lam / w := hcdt


/-! ### the moments [eq:abJ] vs their scale-free limits (last sentence of the [thm:D] proof:
"Its constants [eq:abJ] differ from those of v*_1 by O(1/L)") -/

/-- shared edge estimate for the moment comparisons: for |h| ≤ 1 and a plateau function
0 ≤ p ≤ 1 with p = 1 on [−L/2+w, L/2−w] and p = 0 off [−L/2, L/2],
|∫ h·p − ∫_{[−L/2,L/2]} h| ≤ 2w (the integrands differ only on the two ramps). -/
private theorem edge_estimate {h p : ℝ → ℝ} {L w : ℝ} (_hL : 0 < L) (hw0 : 0 < w)
    (hwL : 2 * w ≤ L) (hh : ∀ u, |h u| ≤ 1) (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
    (hpl : ∀ u : ℝ, |u| ≤ L/2 - w → p u = 1) (hsupp : ∀ u : ℝ, L/2 ≤ |u| → p u = 0)
    (hpc : Continuous p) (hhc : Continuous h) :
    |(∫ u, h u * p u) - ∫ u in Set.Icc (-(L/2)) (L/2), h u| ≤ 2 * w := by
  have hrestr : ∫ u, h u * p u = ∫ u in Set.Icc (-(L/2)) (L/2), h u * p u := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    have : L / 2 ≤ |x| := by
      rcases hx with hc | hc
      · rw [abs_of_neg (by linarith : x < 0)]; linarith
      · rw [abs_of_pos (by linarith : 0 < x)]; linarith
    rw [hsupp x this, mul_zero]
  have hIhp : MeasureTheory.IntegrableOn (fun u => h u * p u) (Set.Icc (-(L/2)) (L/2)) :=
    ((hhc.mul hpc).continuousOn).integrableOn_compact isCompact_Icc
  have hIh : MeasureTheory.IntegrableOn h (Set.Icc (-(L/2)) (L/2)) :=
    (hhc.continuousOn).integrableOn_compact isCompact_Icc
  have hsub : (∫ u, h u * p u) - ∫ u in Set.Icc (-(L/2)) (L/2), h u
      = ∫ u in Set.Icc (-(L/2)) (L/2), (h u * p u - h u) := by
    rw [hrestr, ← MeasureTheory.integral_sub hIhp hIh]
  rw [hsub]
  -- the two-ramp majorant
  set maj : ℝ → ℝ := fun u => (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
      + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u with hmaj
  have hImaj : Integrable maj := by
    apply Integrable.add
    · exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
        (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    · exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
        (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hind0 : ∀ (s : Set ℝ) (u : ℝ), 0 ≤ s.indicator (1 : ℝ → ℝ) u := fun s u =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) u
  have hptw : ∀ u ∈ Set.Icc (-(L/2)) (L/2), |h u * p u - h u| ≤ maj u := by
    intro u hu
    have hmaj0 : 0 ≤ maj u := by
      rw [hmaj]
      exact add_nonneg (hind0 _ u) (hind0 _ u)
    rcases le_or_gt |u| (L/2 - w) with hpl' | hedge
    · rw [hpl u hpl', mul_one, sub_self, abs_zero]
      exact hmaj0
    · have hbound : |h u * p u - h u| ≤ 1 := by
        have e : h u * p u - h u = h u * (p u - 1) := by ring
        rw [e, abs_mul]
        calc |h u| * |p u - 1| ≤ 1 * 1 := by
              apply mul_le_mul (hh u) ?_ (abs_nonneg _) zero_le_one
              rw [abs_le]
              exact ⟨by linarith [hp0 u], by linarith [hp1 u]⟩
          _ = 1 := mul_one 1
      have hone : (1:ℝ) ≤ maj u := by
        rw [hmaj]
        show (1:ℝ) ≤ (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
          + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u
        rcases le_or_gt u 0 with hneg | hpos
        · have hu1 : u ∈ Set.Icc (-(L/2)) (-(L/2) + w) := by
            refine ⟨hu.1, ?_⟩
            have habs : |u| = -u := abs_of_nonpos hneg
            rw [habs] at hedge
            linarith
          have := hind0 (Set.Icc (L/2 - w) (L/2)) u
          rw [Set.indicator_of_mem hu1, Pi.one_apply]
          linarith
        · have hu1 : u ∈ Set.Icc (L/2 - w) (L/2) := by
            refine ⟨?_, hu.2⟩
            have habs : |u| = u := abs_of_pos hpos
            rw [habs] at hedge
            linarith
          have := hind0 (Set.Icc (-(L/2)) (-(L/2) + w)) u
          rw [Set.indicator_of_mem hu1, Pi.one_apply]
          linarith
      linarith
  calc |∫ u in Set.Icc (-(L/2)) (L/2), (h u * p u - h u)|
      ≤ ∫ u in Set.Icc (-(L/2)) (L/2), |h u * p u - h u| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ u in Set.Icc (-(L/2)) (L/2), maj u := by
        apply MeasureTheory.setIntegral_mono_on
          (((hhc.mul hpc).sub hhc).abs.continuousOn.integrableOn_compact isCompact_Icc)
          hImaj.integrableOn measurableSet_Icc hptw
    _ ≤ ∫ u, maj u :=
        MeasureTheory.setIntegral_le_integral hImaj
          (MeasureTheory.ae_of_all _ fun u => by
            rw [hmaj]
            apply add_nonneg <;> exact Set.indicator_nonneg (fun _ _ => zero_le_one) u)
    _ = 2 * w := by
        rw [hmaj]
        rw [MeasureTheory.integral_add
          ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
            (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))
          ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
            (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))]
        rw [MeasureTheory.integral_indicator_one measurableSet_Icc,
          MeasureTheory.integral_indicator_one measurableSet_Icc,
          MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
          Real.volume_Icc, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
        ring

/-- substitution: ∫_{−L/2..L/2} v(u/L) du = L · ∫_{−1/2..1/2} v. -/
private theorem integral_scale {v : ℝ → ℝ} {L : ℝ} (hL : 0 < L) :
    ∫ u in (-(L/2))..(L/2), v (u / L) = L * ∫ s in (-(1:ℝ)/2)..(1/2), v s := by
  rw [intervalIntegral.integral_comp_div (f := v) hL.ne', smul_eq_mul,
    show -(L/2) / L = -(1:ℝ)/2 by field_simp; try ring,
    show L/2 / L = (1:ℝ)/2 by rw [div_div]; rw [div_eq_div_iff (by positivity) (by norm_num)]; ring]

/-- a_D := L⁻¹∫φ_D²;  |a_D − a*_λ| ≤ 4w/L. -/
theorem aD_close (hϱ : TaperProfile ϱ) (h0 : 0 < lam) (h1 : lam ≤ 1) (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L) :
    |L⁻¹ * (∫ u, phiD ϱ lam L w u ^ 2) - aStar lam| ≤ 4 * w / L := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  -- the scale-free mean as an integral over [−L/2, L/2]
  have hsub : aStar lam = L⁻¹ * ∫ u in Set.Icc (-(L/2)) (L/2), vStar lam (u / L) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2), integral_scale hL]
    unfold aStar
    field_simp
  -- the window integral via φ_D² = c·φ²
  have hwin : ∫ u, phiD ϱ lam L w u ^ 2 = ∫ u, vStar lam (u / L) * Taper.phi ϱ L w u ^ 2 := by
    rw [phiD_sq_eq hϱ h0 h1 hw0 hwL']
  rw [hwin, hsub]
  have hcore := edge_estimate (h := fun u => vStar lam (u / L))
    (p := fun u => Taper.phi ϱ L w u ^ 2) hL hw0 hwL'
    (fun u => by
      unfold vStar
      exact Real.abs_cos_le_one _)
    (fun u => sq_nonneg _)
    (fun u => by
      calc Taper.phi ϱ L w u ^ 2 ≤ 1 ^ 2 :=
            pow_le_pow_left₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) 2
        _ = 1 := one_pow 2)
    (fun u hu => by
      show Taper.phi ϱ L w u ^ 2 = 1
      rw [Taper.phi_eq_one hϱ hw0 hu, one_pow])
    (fun u hu => by
      show Taper.phi ϱ L w u ^ 2 = 0
      rw [Taper.phi_eq_zero hϱ hw0 hu, zero_pow two_ne_zero])
    ((Taper.phi_continuous hϱ hw0 hwL').pow 2)
    (by
      unfold vStar
      fun_prop)
  have e : L⁻¹ * (∫ u, vStar lam (u / L) * Taper.phi ϱ L w u ^ 2)
      - L⁻¹ * ∫ u in Set.Icc (-(L/2)) (L/2), vStar lam (u / L)
      = L⁻¹ * ((∫ u, vStar lam (u / L) * Taper.phi ϱ L w u ^ 2)
        - ∫ u in Set.Icc (-(L/2)) (L/2), vStar lam (u / L)) := by ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0:ℝ) < L⁻¹)]
  calc L⁻¹ * |(∫ u, vStar lam (u / L) * Taper.phi ϱ L w u ^ 2)
      - ∫ u in Set.Icc (-(L/2)) (L/2), vStar lam (u / L)|
      ≤ L⁻¹ * (2 * w) := mul_le_mul_of_nonneg_left hcore (by positivity)
    _ ≤ 4 * w / L := by
        rw [div_eq_mul_inv]
        nlinarith [hw0.le, inv_pos.mpr hL]

/-- b_D := L⁻¹∫φ_D⁴;  |b_D − b*_λ| ≤ 4w/L. -/
theorem bD_close (hϱ : TaperProfile ϱ) (h0 : 0 < lam) (h1 : lam ≤ 1) (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L) :
    |L⁻¹ * (∫ u, phiD ϱ lam L w u ^ 4) - bStar lam| ≤ 4 * w / L := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hsub : bStar lam = L⁻¹ * ∫ u in Set.Icc (-(L/2)) (L/2), vStar lam (u / L) ^ 2 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2),
      integral_scale (v := fun s => vStar lam s ^ 2) hL]
    unfold bStar
    field_simp
  have hwin : ∫ u, phiD ϱ lam L w u ^ 4
      = ∫ u, vStar lam (u / L) ^ 2 * Taper.phi ϱ L w u ^ 4 := by
    have e : (fun u => phiD ϱ lam L w u ^ 4)
        = fun u => vStar lam (u / L) ^ 2 * Taper.phi ϱ L w u ^ 4 := by
      have h2 := phiD_sq_eq hϱ h0 h1 hw0 hwL'
      funext u
      have := congrFun h2 u
      calc phiD ϱ lam L w u ^ 4 = (phiD ϱ lam L w u ^ 2) ^ 2 := by ring
        _ = (vStar lam (u / L) * Taper.phi ϱ L w u ^ 2) ^ 2 := by rw [this]
        _ = vStar lam (u / L) ^ 2 * Taper.phi ϱ L w u ^ 4 := by ring
    rw [e]
  rw [hwin, hsub]
  have hcore := edge_estimate (h := fun u => vStar lam (u / L) ^ 2)
    (p := fun u => Taper.phi ϱ L w u ^ 4) hL hw0 hwL'
    (fun u => by
      rw [abs_pow]
      calc |vStar lam (u / L)| ^ 2 ≤ 1 ^ 2 := by
            apply pow_le_pow_left₀ (abs_nonneg _) ?_ 2
            unfold vStar
            exact Real.abs_cos_le_one _
        _ = 1 := one_pow 2)
    (fun u => by positivity)
    (fun u => by
      calc Taper.phi ϱ L w u ^ 4 ≤ 1 ^ 4 :=
            pow_le_pow_left₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) 4
        _ = 1 := one_pow 4)
    (fun u hu => by
      show Taper.phi ϱ L w u ^ 4 = 1
      rw [Taper.phi_eq_one hϱ hw0 hu, one_pow])
    (fun u hu => by
      show Taper.phi ϱ L w u ^ 4 = 0
      rw [Taper.phi_eq_zero hϱ hw0 hu, zero_pow (by norm_num : (4:ℕ) ≠ 0)])
    ((Taper.phi_continuous hϱ hw0 hwL').pow 4)
    (by
      unfold vStar
      fun_prop)
  have e : L⁻¹ * (∫ u, vStar lam (u / L) ^ 2 * Taper.phi ϱ L w u ^ 4)
      - L⁻¹ * ∫ u in Set.Icc (-(L/2)) (L/2), vStar lam (u / L) ^ 2
      = L⁻¹ * ((∫ u, vStar lam (u / L) ^ 2 * Taper.phi ϱ L w u ^ 4)
        - ∫ u in Set.Icc (-(L/2)) (L/2), vStar lam (u / L) ^ 2) := by ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0:ℝ) < L⁻¹)]
  calc L⁻¹ * |(∫ u, vStar lam (u / L) ^ 2 * Taper.phi ϱ L w u ^ 4)
      - ∫ u in Set.Icc (-(L/2)) (L/2), vStar lam (u / L) ^ 2|
      ≤ L⁻¹ * (2 * w) := mul_le_mul_of_nonneg_left hcore (by positivity)
    _ ≤ 4 * w / L := by
        rw [div_eq_mul_inv]
        nlinarith [hw0.le, inv_pos.mpr hL]

section JMoment
/-! #### jD_close: the J-moment of the window vs J* (no Fubini — everything is one-variable:
the sharp-window autocorrelation has a trigonometric closed form (product-to-sum + explicit
antiderivatives), its y-moment evaluates to (L³/2)·(the closed form of J*) [jStar_closed], and
the ramp only moves the autocorrelation by 4w pointwise). -/

/-- the sharp-cutoff comparison autocorrelation, in closed form:
Cfun y := (L−y)/2 · cos(ω̃y) + sin(ω̃(L−y))/(2ω̃), ω̃ := √2λ/L. -/
def Cfun (lam L : ℝ) (y : ℝ) : ℝ :=
  (L - y) / 2 * Real.cos (Real.sqrt 2 * lam * (1 / L) * y)
    + Real.sin (Real.sqrt 2 * lam * (1 / L) * (L - y)) / (2 * (Real.sqrt 2 * lam * (1 / L)))

/-- product-to-sum evaluation: for 0 ≤ y ≤ L,
∫ u in −L/2..(L/2−y), v(u/L)·v((u+y)/L) du = Cfun y. -/
theorem integral_cos_overlap (h0 : 0 < lam) (hL : 0 < L) (y : ℝ) :
    ∫ u in (-(L/2))..(L/2 - y), vStar lam (u / L) * vStar lam ((u + y) / L)
      = Cfun lam L y := by
  have hωpos : (0:ℝ) < Real.sqrt 2 * lam * (1 / L) := by positivity
  set ω : ℝ := Real.sqrt 2 * lam * (1 / L) with hωdef
  have hH : ∀ u : ℝ, HasDerivAt (fun u => Real.cos (ω * y) * u / 2
      + Real.sin (ω * (2 * u + y)) / (4 * ω))
      (vStar lam (u / L) * vStar lam ((u + y) / L)) u := by
    intro u
    have hlin : HasDerivAt (fun u : ℝ => ω * (2 * u + y)) (ω * 2) u := by
      simpa using (((hasDerivAt_id u).const_mul (2:ℝ)).add_const y).const_mul ω
    have h1 : HasDerivAt (fun u : ℝ => Real.cos (ω * y) * u / 2)
        (Real.cos (ω * y) / 2) u := by
      simpa using ((hasDerivAt_id u).const_mul (Real.cos (ω * y))).div_const 2
    have h2 : HasDerivAt (fun u : ℝ => Real.sin (ω * (2 * u + y)) / (4 * ω))
        (Real.cos (ω * (2 * u + y)) * (ω * 2) / (4 * ω)) u :=
      ((Real.hasDerivAt_sin (ω * (2 * u + y))).comp u hlin).div_const (4 * ω)
    have h3 := h1.add h2
    refine h3.congr_deriv ?_
    unfold vStar
    have e1 : Real.sqrt 2 * lam * (u / L) = ω * u := by rw [hωdef]; ring
    have e2 : Real.sqrt 2 * lam * ((u + y) / L) = ω * (u + y) := by rw [hωdef]; ring
    rw [e1, e2]
    have hpts : Real.cos (ω * u) * Real.cos (ω * (u + y))
        = (Real.cos (ω * y) + Real.cos (ω * (2 * u + y))) / 2 := by
      have ha : ω * y = ω * (u + y) - ω * u := by ring
      have hb : ω * (2 * u + y) = ω * (u + y) + ω * u := by ring
      rw [ha, hb, Real.cos_sub, Real.cos_add]
      ring
    rw [hpts]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hH u)
    (Continuous.intervalIntegrable (by unfold vStar; fun_prop) _ _)]
  unfold Cfun
  rw [← hωdef]
  have e3 : ω * (2 * (L / 2 - y) + y) = ω * (L - y) := by ring
  have e6 : ω * (2 * -(L / 2) + y) = -(ω * (L - y)) := by ring
  rw [e3, e6, Real.sin_neg]
  field_simp
  ring

/-- the y-moment of the sharp autocorrelation, in closed form:
∫_0^L Cfun(y)·y dy = (L³/2)·(sin(2ϑ)/(8ϑ³) − cos(2ϑ)/(4ϑ²))  (explicit antiderivatives). -/
theorem integral_Cfun_moment (h0 : 0 < lam) (_h1 : lam ≤ 1) (hL : 0 < L) :
    ∫ y in (0:ℝ)..L, Cfun lam L y * y
      = L ^ 3 / 2 * (Real.sin (2 * theta lam) / (8 * theta lam ^ 3)
        - Real.cos (2 * theta lam) / (4 * theta lam ^ 2)) := by
  have hωpos : (0:ℝ) < Real.sqrt 2 * lam * (1 / L) := by positivity
  set ω : ℝ := Real.sqrt 2 * lam * (1 / L) with hωdef
  have hθ : 0 < theta lam := theta_pos h0
  have hωL : ω * L = 2 * theta lam := by
    rw [hωdef, show theta lam = lam / Real.sqrt 2 from rfl]
    have hs2 : (0:ℝ) < Real.sqrt 2 := by positivity
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp
    ring_nf
    try rw [hsq]
    try ring
  set H : ℝ → ℝ := fun y => (((L * y - y ^ 2) / ω + 2 / ω ^ 3) * Real.sin (ω * y)
      + ((L - 2 * y) / ω ^ 2) * Real.cos (ω * y)) / 2
    + ((y / ω) * Real.cos (ω * (L - y)) + Real.sin (ω * (L - y)) / ω ^ 2) / (2 * ω) with hHdef
  have hH : ∀ y : ℝ, HasDerivAt H (Cfun lam L y * y) y := by
    intro y
    have hlin1 : HasDerivAt (fun y : ℝ => ω * y) ω y := by
      simpa using (hasDerivAt_id y).const_mul ω
    have hlin2 : HasDerivAt (fun y : ℝ => ω * (L - y)) (ω * (-1)) y :=
      ((hasDerivAt_id y).const_sub L).const_mul ω
    have hsin1 : HasDerivAt (fun y : ℝ => Real.sin (ω * y)) (Real.cos (ω * y) * ω) y :=
      (Real.hasDerivAt_sin (ω * y)).comp y hlin1
    have hcos1 : HasDerivAt (fun y : ℝ => Real.cos (ω * y)) (-Real.sin (ω * y) * ω) y :=
      (Real.hasDerivAt_cos (ω * y)).comp y hlin1
    have hsin2 : HasDerivAt (fun y : ℝ => Real.sin (ω * (L - y)))
        (Real.cos (ω * (L - y)) * (ω * (-1))) y := by
      have := (Real.hasDerivAt_sin (ω * (L - y))).comp y hlin2
      simpa [Function.comp_def] using this
    have hcos2 : HasDerivAt (fun y : ℝ => Real.cos (ω * (L - y)))
        (-Real.sin (ω * (L - y)) * (ω * (-1))) y := by
      have := (Real.hasDerivAt_cos (ω * (L - y))).comp y hlin2
      simpa [Function.comp_def] using this
    have hq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * y) y := by
      simpa using hasDerivAt_pow 2 y
    have hp1 : HasDerivAt (fun y : ℝ => (L * y - y ^ 2) / ω + 2 / ω ^ 3)
        ((L * 1 - 2 * y) / ω) y :=
      ((((hasDerivAt_id y).const_mul L).sub hq).div_const ω).add_const (2 / ω ^ 3)
    have hp2 : HasDerivAt (fun y : ℝ => (L - 2 * y) / ω ^ 2) (-(2 * 1) / ω ^ 2) y := by
      have : HasDerivAt (fun y : ℝ => L - 2 * y) (-(2 * 1)) y := by
        simpa using ((hasDerivAt_id y).const_mul (2:ℝ)).const_sub L
      exact this.div_const (ω ^ 2)
    have hp3 : HasDerivAt (fun y : ℝ => y / ω) (1 / ω) y := by
      simpa using (hasDerivAt_id y).div_const ω
    have hA := ((hp1.mul hsin1).add (hp2.mul hcos1)).div_const 2
    have hB := (((hp3.mul hcos2).add (hsin2.div_const (ω ^ 2))).div_const (2 * ω))
    have htot := hA.add hB
    refine htot.congr_deriv ?_
    unfold Cfun
    rw [← hωdef]
    have hω0 : ω ≠ 0 := ne_of_gt hωpos
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hH y)
    (Continuous.intervalIntegrable (by
      unfold Cfun
      rw [← hωdef]
      fun_prop) _ _)]
  rw [hHdef]
  simp only
  rw [show ω * (0:ℝ) = 0 by ring, show ω * (L - L) = 0 by ring, show ω * (L - 0) = ω * L by ring,
    hωL, Real.sin_zero, Real.cos_zero]
  have hω0 : ω ≠ 0 := ne_of_gt hωpos
  have hωeq : ω = 2 * theta lam / L := by
    rw [eq_div_iff hL.ne']
    exact hωL
  rw [hωeq]
  field_simp
  ring

/-- the sharp window k := 1_{[−L/2,L/2]}·v(·/L). -/
def sharpW (lam L : ℝ) (u : ℝ) : ℝ :=
  (Set.Icc (-(L/2)) (L/2)).indicator (fun u => vStar lam (u / L)) u

/-- the sharp-window autocorrelation (full line) equals the overlap integral, i.e. Cfun. -/
theorem sharp_autocorr_eq (h0 : 0 < lam) (hL : 0 < L) {y : ℝ}
    (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    ∫ u, sharpW lam L u * sharpW lam L (u + y) = Cfun lam L y := by
  have hind : ∀ u : ℝ, sharpW lam L u * sharpW lam L (u + y)
      = (Set.Icc (-(L/2)) (L/2 - y)).indicator
          (fun u => vStar lam (u / L) * vStar lam ((u + y) / L)) u := by
    intro u
    unfold sharpW
    by_cases hu : u ∈ Set.Icc (-(L/2)) (L/2 - y)
    · have hu1 : u ∈ Set.Icc (-(L/2)) (L/2) := ⟨hu.1, by linarith [hu.2]⟩
      have hu2 : u + y ∈ Set.Icc (-(L/2)) (L/2) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
      rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu1, Set.indicator_of_mem hu2]
    · rw [Set.indicator_of_notMem hu]
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with hu | hu
      · rw [Set.indicator_of_notMem (s := Set.Icc (-(L/2)) (L/2)) (a := u)
          (by rw [Set.mem_Icc]; push Not; intro h; linarith), zero_mul]
      · rw [Set.indicator_of_notMem (s := Set.Icc (-(L/2)) (L/2)) (a := u + y)
          (by rw [Set.mem_Icc]; push Not; intro h; linarith), mul_zero]
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hind),
    MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2 - y)]
  exact integral_cos_overlap h0 hL y

/-- the window and the sharp cutoff differ by at most 2w in L¹. -/
theorem integral_abs_phiDsq_sub_sharp (hϱ : TaperProfile ϱ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u, |phiD ϱ lam L w u ^ 2 - sharpW lam L u| ≤ 2 * w := by
  have hL : 0 < L := by linarith
  have hsq := phiD_sq_eq hϱ h0 h1 hw hwL
  set maj : ℝ → ℝ := fun u => (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
      + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u with hmaj
  have hImaj : Integrable maj := by
    apply Integrable.add <;>
      exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
        (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hind0 : ∀ (s : Set ℝ) (u : ℝ), 0 ≤ s.indicator (1 : ℝ → ℝ) u := fun s u =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) u
  have hpt : ∀ u : ℝ, |phiD ϱ lam L w u ^ 2 - sharpW lam L u| ≤ maj u := by
    intro u
    have hmaj0 : 0 ≤ maj u := by
      rw [hmaj]
      exact add_nonneg (hind0 _ u) (hind0 _ u)
    have hval : phiD ϱ lam L w u ^ 2 = vStar lam (u / L) * Taper.phi ϱ L w u ^ 2 :=
      congrFun hsq u
    rcases le_or_gt |u| (L/2 - w) with hpl | hedge
    · -- plateau: φ = 1 and u ∈ Icc, so both sides are v(u/L)
      have huIcc : u ∈ Set.Icc (-(L/2)) (L/2) := by
        rw [abs_le] at hpl
        constructor <;> [linarith [hpl.1]; linarith [hpl.2]]
      rw [hval, Taper.phi_eq_one hϱ hw hpl, one_pow, mul_one]
      unfold sharpW
      rw [Set.indicator_of_mem huIcc, sub_self, abs_zero]
      exact hmaj0
    · rcases le_or_gt |u| (L/2) with hin | hout
      · -- edge: both sides in [−1, 1], difference ≤ 1, and maj = 1 there
        have hbound : |phiD ϱ lam L w u ^ 2 - sharpW lam L u| ≤ 1 := by
          have h1' : 0 ≤ phiD ϱ lam L w u ^ 2 := sq_nonneg _
          have h2' : phiD ϱ lam L w u ^ 2 ≤ 1 := by
            calc phiD ϱ lam L w u ^ 2 ≤ 1 ^ 2 :=
                  pow_le_pow_left₀ (phiD_nonneg hϱ u) (phiD_le_one hϱ u) 2
              _ = 1 := one_pow 2
          have h3' : 0 ≤ sharpW lam L u := by
            unfold sharpW
            apply Set.indicator_nonneg
            intro x hx
            have := cos_factor_ge (u := x) h0 h1 hL (abs_le.mpr ⟨hx.1, hx.2⟩)
            linarith
          have h4' : sharpW lam L u ≤ 1 := by
            unfold sharpW
            by_cases hm : u ∈ Set.Icc (-(L/2)) (L/2)
            · rw [Set.indicator_of_mem hm]
              unfold vStar
              exact Real.cos_le_one _
            · rw [Set.indicator_of_notMem hm]
              exact zero_le_one
          rw [abs_le]
          constructor <;> linarith
        have hone : (1:ℝ) ≤ maj u := by
          rw [hmaj]
          show (1:ℝ) ≤ (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
            + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u
          rcases le_or_gt u 0 with hneg | hpos
          · have hu1 : u ∈ Set.Icc (-(L/2)) (-(L/2) + w) := by
              refine ⟨?_, ?_⟩
              · have : |u| = -u := abs_of_nonpos hneg
                rw [this] at hin
                linarith
              · have : |u| = -u := abs_of_nonpos hneg
                rw [this] at hedge
                linarith
            have := hind0 (Set.Icc (L/2 - w) (L/2)) u
            rw [Set.indicator_of_mem hu1, Pi.one_apply]
            linarith
          · have hu1 : u ∈ Set.Icc (L/2 - w) (L/2) := by
              refine ⟨?_, ?_⟩
              · have : |u| = u := abs_of_pos hpos
                rw [this] at hedge
                linarith
              · have : |u| = u := abs_of_pos hpos
                rw [this] at hin
                linarith
            have := hind0 (Set.Icc (-(L/2)) (-(L/2) + w)) u
            rw [Set.indicator_of_mem hu1, Pi.one_apply]
            linarith
        linarith
      · -- outside: both vanish
        have h1' : phiD ϱ lam L w u = 0 := phiD_eq_zero hϱ hw (le_of_lt hout)
        have h2' : sharpW lam L u = 0 := by
          unfold sharpW
          apply Set.indicator_of_notMem
          intro hm
          have : |u| ≤ L / 2 := abs_le.mpr ⟨hm.1, hm.2⟩
          linarith
        rw [h1', h2']
        norm_num
        exact hmaj0
  -- integrate the pointwise bound
  calc ∫ u, |phiD ϱ lam L w u ^ 2 - sharpW lam L u|
      ≤ ∫ u, maj u := by
        apply MeasureTheory.integral_mono_of_nonneg
          (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) hImaj
          (MeasureTheory.ae_of_all _ hpt)
    _ = 2 * w := by
        rw [hmaj]
        rw [MeasureTheory.integral_add
          ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
            (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))
          ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
            (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))),
          MeasureTheory.integral_indicator_one measurableSet_Icc,
          MeasureTheory.integral_indicator_one measurableSet_Icc,
          MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
          Real.volume_Icc, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
        ring

/-- pointwise comparison of the window autocorrelation with the sharp one: ≤ 4w on [0, L]. -/
theorem autocorr_phiDsq_close (hϱ : TaperProfile ϱ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hw : 0 < w) (hwL : 2 * w ≤ L) {y : ℝ} (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    |Params.autocorr (fun u => phiD ϱ lam L w u ^ 2) y - Cfun lam L y| ≤ 4 * w := by
  have hL : 0 < L := by linarith
  set h : ℝ → ℝ := fun u => phiD ϱ lam L w u ^ 2 with hhdef
  set k : ℝ → ℝ := sharpW lam L with hkdef
  have hh_cont : Continuous h := ((phiD_contDiff hϱ h0 h1 hw hwL).pow 2).continuous
  have hh1 : ∀ u, |h u| ≤ 1 := by
    intro u
    rw [hhdef]
    simp only
    rw [abs_of_nonneg (sq_nonneg _)]
    calc phiD ϱ lam L w u ^ 2 ≤ 1 ^ 2 :=
          pow_le_pow_left₀ (phiD_nonneg hϱ u) (phiD_le_one hϱ u) 2
      _ = 1 := one_pow 2
  have hk_meas : Measurable k := by
    rw [hkdef]
    unfold sharpW
    exact Measurable.indicator (by unfold vStar; fun_prop) measurableSet_Icc
  have hk1 : ∀ u, |k u| ≤ 1 := by
    intro u
    rw [hkdef]
    unfold sharpW
    by_cases hm : u ∈ Set.Icc (-(L/2)) (L/2)
    · rw [Set.indicator_of_mem hm]
      unfold vStar
      exact Real.abs_cos_le_one _
    · rw [Set.indicator_of_notMem hm, abs_zero]
      exact zero_le_one
  have hcs : HasCompactSupport h := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := -(L/2)) (b := L/2))
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hmem
    apply hx
    rw [hhdef]
    simp only
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
    have : L / 2 ≤ |x| := by
      rcases hmem with hc | hc
      · rw [abs_of_neg (by linarith : x < 0)]; linarith
      · rw [abs_of_pos (by linarith : 0 < x)]; linarith
    rw [phiD_eq_zero hϱ hw this, zero_pow two_ne_zero]
  have hint_h : Integrable h := hh_cont.integrable_of_hasCompactSupport hcs
  have hint_k : Integrable k := by
    rw [hkdef]
    unfold sharpW
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
      (((by unfold vStar; fun_prop : Continuous fun u : ℝ => vStar lam (u / L)).continuousOn).integrableOn_compact
        isCompact_Icc)
  have hint_d : Integrable (fun u => h u - k u) := hint_h.sub hint_k
  have hint_hy : Integrable (fun u => h (u + y)) := hint_h.comp_add_right y
  have hint_ky : Integrable (fun u => k (u + y)) := hint_k.comp_add_right y
  have hint_dy : Integrable (fun u => h (u + y) - k (u + y)) := hint_hy.sub hint_ky
  have hmeas_hy : MeasureTheory.AEStronglyMeasurable (fun u => h (u + y)) MeasureTheory.volume :=
    hint_hy.aestronglyMeasurable
  -- products
  have hint_p1 : Integrable (fun u => (h u - k u) * h (u + y)) := by
    have := hint_d.bdd_mul (c := 1) hmeas_hy (MeasureTheory.ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hh1 (u + y))
    exact this.congr (MeasureTheory.ae_of_all _ fun u => by ring)
  have hint_p2 : Integrable (fun u => k u * (h (u + y) - k (u + y))) := by
    exact hint_dy.bdd_mul (c := 1) hk_meas.aestronglyMeasurable (MeasureTheory.ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hk1 u)
  have hint_hh : Integrable (fun u => h u * h (u + y)) := by
    have := hint_h.bdd_mul (c := 1) hmeas_hy (MeasureTheory.ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hh1 (u + y))
    exact this.congr (MeasureTheory.ae_of_all _ fun u => by ring)
  have hint_kk : Integrable (fun u => k u * k (u + y)) := by
    exact hint_ky.bdd_mul (c := 1) hk_meas.aestronglyMeasurable (MeasureTheory.ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hk1 u)
  -- decomposition
  have hCk : ∫ u, k u * k (u + y) = Cfun lam L y := sharp_autocorr_eq h0 hL hy0 hyL
  have hdecomp : Params.autocorr h y - Cfun lam L y
      = (∫ u, (h u - k u) * h (u + y)) + ∫ u, k u * (h (u + y) - k (u + y)) := by
    have e1 : Params.autocorr h y - Cfun lam L y
        = ∫ u, (h u * h (u + y) - k u * k (u + y)) := by
      rw [show Params.autocorr h y = ∫ u, h u * h (u + y) from rfl, ← hCk,
        MeasureTheory.integral_sub hint_hh hint_kk]
    rw [e1, ← MeasureTheory.integral_add hint_p1 hint_p2]
    apply MeasureTheory.integral_congr_ae
    apply MeasureTheory.ae_of_all
    intro u
    ring
  -- the L¹ bound, twice
  have hd2w := integral_abs_phiDsq_sub_sharp hϱ h0 h1 hw hwL
  have hint_dabs : Integrable (fun u => |h u - k u|) := hint_d.abs
  have hb1 : |∫ u, (h u - k u) * h (u + y)| ≤ 2 * w := by
    calc |∫ u, (h u - k u) * h (u + y)| ≤ ∫ u, |(h u - k u) * h (u + y)| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ u, |h u - k u| := by
          apply MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) hint_dabs
            (MeasureTheory.ae_of_all _ fun u => ?_)
          show |(h u - k u) * h (u + y)| ≤ |h u - k u|
          rw [abs_mul]
          calc |h u - k u| * |h (u + y)| ≤ |h u - k u| * 1 :=
                mul_le_mul_of_nonneg_left (hh1 (u + y)) (abs_nonneg _)
            _ = |h u - k u| := mul_one _
      _ ≤ 2 * w := hd2w
  have hb2 : |∫ u, k u * (h (u + y) - k (u + y))| ≤ 2 * w := by
    have htrans : ∫ u, |h (u + y) - k (u + y)| = ∫ u, |h u - k u| :=
      MeasureTheory.integral_add_right_eq_self (fun u => |h u - k u|) y
    calc |∫ u, k u * (h (u + y) - k (u + y))|
        ≤ ∫ u, |k u * (h (u + y) - k (u + y))| := MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ u, |h (u + y) - k (u + y)| := by
          apply MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) (hint_dy.abs)
            (MeasureTheory.ae_of_all _ fun u => ?_)
          show |k u * (h (u + y) - k (u + y))| ≤ |h (u + y) - k (u + y)|
          rw [abs_mul]
          calc |k u| * |h (u + y) - k (u + y)| ≤ 1 * |h (u + y) - k (u + y)| :=
                mul_le_mul_of_nonneg_right (hk1 u) (abs_nonneg _)
            _ = _ := one_mul _
      _ = ∫ u, |h u - k u| := htrans
      _ ≤ 2 * w := hd2w
  calc |Params.autocorr h y - Cfun lam L y|
      = |(∫ u, (h u - k u) * h (u + y)) + ∫ u, k u * (h (u + y) - k (u + y))| := by
        rw [hdecomp]
    _ ≤ |∫ u, (h u - k u) * h (u + y)| + |∫ u, k u * (h (u + y) - k (u + y))| := abs_add_le _ _
    _ ≤ 4 * w := by linarith

end JMoment

/-- J_D := (2/L³)∫_0^L g_D(y)·y dy, g_D = φ_D² ⋆ φ_D² [eq:abJ];  |J_D − J*_λ| ≤ 16w/L. -/
theorem jD_close (hϱ : TaperProfile ϱ) (h0 : 0 < lam) (h1 : lam ≤ 1) (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L) :
    |2 / L ^ 3 * (∫ y in (0:ℝ)..L, Params.autocorr (fun u => phiD ϱ lam L w u ^ 2) y * y)
      - jStar lam| ≤ 16 * w / L := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  set A : ℝ → ℝ := Params.autocorr (fun u => phiD ϱ lam L w u ^ 2) with hAdef
  have hAcont : Continuous A := by
    rw [hAdef]
    refine Taper.autocorr_continuous_of_support _ (M := L/2)
      ((phiD_contDiff hϱ h0 h1 hw0 hwL').pow 2).continuous ?_
    intro u hu
    show phiD ϱ lam L w u ^ 2 = 0
    rw [phiD_eq_zero hϱ hw0 hu, zero_pow two_ne_zero]
  have hCcont : Continuous (Cfun lam L) := by
    unfold Cfun
    fun_prop
  have hIA : IntervalIntegrable (fun y => A y * y) MeasureTheory.volume 0 L :=
    (hAcont.mul continuous_id).intervalIntegrable 0 L
  have hIC : IntervalIntegrable (fun y => Cfun lam L y * y) MeasureTheory.volume 0 L :=
    (hCcont.mul continuous_id).intervalIntegrable 0 L
  have hsplit : ∫ y in (0:ℝ)..L, A y * y
      = (∫ y in (0:ℝ)..L, (A y - Cfun lam L y) * y) + ∫ y in (0:ℝ)..L, Cfun lam L y * y := by
    have e1 : ∫ y in (0:ℝ)..L, (A y - Cfun lam L y) * y
        = ∫ y in (0:ℝ)..L, (A y * y - Cfun lam L y * y) :=
      intervalIntegral.integral_congr (fun y _ => by ring)
    rw [e1, intervalIntegral.integral_sub hIA hIC]
    ring
  have hcmp : |∫ y in (0:ℝ)..L, (A y - Cfun lam L y) * y| ≤ 4 * w * L * L := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (C := 4 * w * L)
      (f := fun y => (A y - Cfun lam L y) * y) (a := 0) (b := L) ?_
    · rw [Real.norm_eq_abs] at hb
      calc |∫ y in (0:ℝ)..L, (A y - Cfun lam L y) * y| ≤ 4 * w * L * |L - 0| := hb
        _ = 4 * w * L * L := by rw [sub_zero, abs_of_pos hL]
    · intro y hy
      rw [Set.uIoc_of_le hL.le] at hy
      rw [Real.norm_eq_abs]
      show |(A y - Cfun lam L y) * y| ≤ 4 * w * L
      rw [abs_mul]
      calc |A y - Cfun lam L y| * |y| ≤ (4 * w) * L := by
            apply mul_le_mul (autocorr_phiDsq_close hϱ h0 h1 hw0 hwL' hy.1.le hy.2) ?_
              (abs_nonneg _) (by positivity)
            rw [abs_of_pos hy.1]
            exact hy.2
        _ = 4 * w * L := rfl
  have hmain : 2 / L ^ 3 * ∫ y in (0:ℝ)..L, Cfun lam L y * y = jStar lam := by
    rw [integral_Cfun_moment h0 h1 hL, jStar_closed h0 h1]
    field_simp
    try ring
  have e : 2 / L ^ 3 * (∫ y in (0:ℝ)..L, A y * y) - jStar lam
      = 2 / L ^ 3 * (∫ y in (0:ℝ)..L, (A y - Cfun lam L y) * y) := by
    rw [hsplit, mul_add, hmain]
    try ring
  rw [← hAdef] at *
  rw [e, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / L ^ 3)]
  calc 2 / L ^ 3 * |∫ y in (0:ℝ)..L, (A y - Cfun lam L y) * y|
      ≤ 2 / L ^ 3 * (4 * w * L * L) := mul_le_mul_of_nonneg_left hcmp (by positivity)
    _ = 8 * w / L := by
        field_simp
        ring
    _ ≤ 16 * w / L := by
        apply div_le_div_of_nonneg_right ?_ hL.le
        linarith

section AutocorrC1
/-! #### C¹ facts for the autocorrelation (the g_D-side hypotheses of ThmD/PP.sumA2g_close):
for h C¹ with compact support and |h| ≤ 1, the autocorrelation is differentiable with
deriv = h ⋆ h' and |deriv| ≤ ∫|h'|.  Via Mathlib's convolution calculus. -/

open scoped Convolution

variable {h : ℝ → ℝ}

private theorem autocorr_eq_conv (heven : ∀ x : ℝ, h (-x) = h x) :
    Params.autocorr h = h ⋆[ContinuousLinearMap.mul ℝ ℝ] h := by
  funext y
  show ∫ u, h u * h (u + y) = ∫ t, h t * h (y - t)
  have e1 : ∫ u, h u * h (u + y) = ∫ t, h (t - y) * h t := by
    have := MeasureTheory.integral_add_right_eq_self (μ := MeasureTheory.volume)
      (fun t => h (t - y) * h t) y
    rw [← this]
    apply MeasureTheory.integral_congr_ae
    apply MeasureTheory.ae_of_all
    intro u
    simp only [add_sub_cancel_right]
  rw [e1]
  apply MeasureTheory.integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t
  show h (t - y) * h t = h t * h (y - t)
  have e2 : h (t - y) = h (y - t) := by
    rw [show t - y = -(y - t) by ring, heven]
  rw [e2, mul_comm]

theorem autocorr_deriv_facts (hC : ContDiff ℝ 1 h) (hcs : HasCompactSupport h)
    (heven : ∀ x : ℝ, h (-x) = h x) (hb : ∀ u : ℝ, |h u| ≤ 1)
    (hI : ∫ u, |deriv h u| ≤ 2) :
    Differentiable ℝ (Params.autocorr h) ∧ Continuous (deriv (Params.autocorr h))
      ∧ ∀ y : ℝ, |deriv (Params.autocorr h) y| ≤ 2 := by
  have hloc : MeasureTheory.LocallyIntegrable h MeasureTheory.volume :=
    (hC.continuous.integrable_of_hasCompactSupport hcs).locallyIntegrable
  have hD : ∀ y : ℝ, HasDerivAt (Params.autocorr h)
      ((h ⋆[ContinuousLinearMap.mul ℝ ℝ] deriv h) y) y := by
    intro y
    rw [autocorr_eq_conv heven]
    exact HasCompactSupport.hasDerivAt_convolution_right _ hloc hcs hC y
  have hdiff : Differentiable ℝ (Params.autocorr h) := fun y => (hD y).differentiableAt
  have hderiv_eq : deriv (Params.autocorr h) = h ⋆[ContinuousLinearMap.mul ℝ ℝ] deriv h :=
    funext fun y => (hD y).deriv
  have hcs' : HasCompactSupport (deriv h) := hcs.deriv
  have hcont' : Continuous (deriv h) := hC.continuous_deriv le_rfl
  refine ⟨hdiff, ?_, ?_⟩
  · rw [hderiv_eq]
    exact hcs'.continuous_convolution_right _ hloc hcont'
  · intro y
    rw [hderiv_eq]
    show |∫ t, h t * deriv h (y - t)| ≤ 2
    have hint' : MeasureTheory.Integrable (fun t => deriv h (y - t)) := by
      have h1 : MeasureTheory.Integrable (deriv h) :=
        hcont'.integrable_of_hasCompactSupport hcs'
      have h2 := h1.comp_sub_left y
      exact h2
    calc |∫ t, h t * deriv h (y - t)| ≤ ∫ t, |h t * deriv h (y - t)| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ t, |deriv h (y - t)| := by
          apply MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_of_all _ fun t => abs_nonneg _) hint'.abs
            (MeasureTheory.ae_of_all _ fun t => ?_)
          show |h t * deriv h (y - t)| ≤ |deriv h (y - t)|
          rw [abs_mul]
          calc |h t| * |deriv h (y - t)| ≤ 1 * |deriv h (y - t)| :=
                mul_le_mul_of_nonneg_right (hb t) (abs_nonneg _)
            _ = |deriv h (y - t)| := one_mul _
      _ = ∫ t, |deriv h t| := by
          have := MeasureTheory.integral_sub_left_eq_self (fun t => |deriv h t|)
            (μ := MeasureTheory.volume) y
          exact this
      _ ≤ 2 := hI

/-- the φ_D²-instance: g_D := autocorr(φ_D²) is C¹ with |g_D'| ≤ 2 (the paper's
"|g'| ≤ ‖(φ²)'‖₁ ≤ 2"), the exact hypotheses of ThmD/PP.sumA2g_close. -/
theorem gD_deriv_facts (hϱ : TaperProfile ϱ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Differentiable ℝ (Params.autocorr (fun u => phiD ϱ lam L w u ^ 2))
      ∧ Continuous (deriv (Params.autocorr (fun u => phiD ϱ lam L w u ^ 2)))
      ∧ ∀ y : ℝ, |deriv (Params.autocorr (fun u => phiD ϱ lam L w u ^ 2)) y| ≤ 2 := by
  have hL : 0 < L := by linarith
  apply autocorr_deriv_facts
  · exact ((phiD_contDiff hϱ h0 h1 hw hwL).pow 2).of_le (by norm_num)
  · apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := -(L/2)) (b := L/2))
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hmem
    apply hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
    have : L / 2 ≤ |x| := by
      rcases hmem with hc | hc
      · rw [abs_of_neg (by linarith : x < 0)]; linarith
      · rw [abs_of_pos (by linarith : 0 < x)]; linarith
    rw [phiD_eq_zero hϱ hw this, zero_pow two_ne_zero]
  · intro x
    rw [phiD_even]
  · intro u
    rw [abs_of_nonneg (sq_nonneg _)]
    calc phiD ϱ lam L w u ^ 2 ≤ 1 ^ 2 :=
          pow_le_pow_left₀ (phiD_nonneg hϱ u) (phiD_le_one hϱ u) 2
      _ = 1 := one_pow 2
  · exact integral_abs_deriv_phiD_sq_le hϱ h0 h1 hw hwL

end AutocorrC1

/-!
Summary of the statements proved in this file:
cos_factor_ge, phiD_contDiff, phiD_antitoneOn, integral_abs_deriv_phiD_le,
integral_abs_deriv_phiD_sq_le, integral_abs_deriv2_phiD_le, integral_abs_deriv2_phiD_sq_le,
aD_close, bD_close, jD_close (via the 1-D route: jStar_closed [Functional.lean] + the
sharp-window autocorrelation closed form integral_cos_overlap/sharp_autocorr_eq + the
y-moment closed form integral_Cfun_moment + the 4w ramp comparison
integral_abs_phiDsq_sub_sharp/autocorr_phiDsq_close — no Fubini anywhere).
-/

end ThmD
end Zeta23
