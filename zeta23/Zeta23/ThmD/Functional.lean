/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmD/Functional.lean — the scale-free variational objects of the paper §7.1 [subsec:MT]:
[eq:cv] the functional c_λ(v), [eq:vstar] the optimal profile v*_λ(s) = cos(√2 λ s) and the
closed-form constant c*_λ = √2 tan ϑ/(1 + ϑ tan ϑ), ϑ = λ/√2.
Pure one-variable calculus: no project imports; consumed by Zeta23/ThmD/Window.lean
(a/b/J of the concrete window) and Zeta23/ThmD/Assembly/Final (the constants of Theorem D).

Convention: we DEFINE cStar in the division-safe sin/cos form
  cStar λ := √2 sin ϑ / (cos ϑ + ϑ sin ϑ)
(the paper's √2 tan ϑ/(1+ϑ tan ϑ) after multiplying through by cos ϑ; equality recorded as
cStar_eq_tan_form).  For 0 ≤ ϑ ≤ 1/√2 < π/2 the denominator is ≥ cos(1/√2) ≥ 3/4 > 0
(cos x ≥ 1 − x²/2), so everything is well-behaved on λ ∈ [0,1].
-/
import Mathlib

noncomputable section

open Real intervalIntegral

namespace Zeta23
namespace ThmD

/-- ϑ := λ/√2  [eq:vstar]. -/
def theta (lam : ℝ) : ℝ := lam / Real.sqrt 2

/-- [eq:vstar]: the optimal window profile v*_λ(s) := cos(√2 λ s)  (scale-free; s ∈ [−1/2, 1/2]). -/
def vStar (lam : ℝ) (s : ℝ) : ℝ := Real.cos (Real.sqrt 2 * lam * s)

/-- [eq:vstar]: c*_λ := √2 tan ϑ / (1 + ϑ tan ϑ), written in the division-safe sin/cos form. -/
def cStar (lam : ℝ) : ℝ :=
  Real.sqrt 2 * Real.sin (theta lam) / (Real.cos (theta lam) + theta lam * Real.sin (theta lam))

/-- [eq:cv]: the scale-free functional
c_λ(v) = λ(∫v)² / (∫v² + λ² ∬|s−s'| v(s)v(s') ds ds'), integrals over [−1/2, 1/2]. -/
def cFun (lam : ℝ) (v : ℝ → ℝ) : ℝ :=
  lam * (∫ s in (-(1:ℝ)/2)..(1/2), v s) ^ 2 /
    ((∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2)
      + lam ^ 2 * ∫ s in (-(1:ℝ)/2)..(1/2), (∫ s' in (-(1:ℝ)/2)..(1/2), |s - s'| * v s * v s'))

/-- The three moments of v*_λ [eq:abJ] in scale-free form:
a* = ∫v*, b* = ∫v*², J* = ∬|s−s'|v*v*. -/
def aStar (lam : ℝ) : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2), vStar lam s
def bStar (lam : ℝ) : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2), vStar lam s ^ 2
def jStar (lam : ℝ) : ℝ :=
  ∫ s in (-(1:ℝ)/2)..(1/2), (∫ s' in (-(1:ℝ)/2)..(1/2), |s - s'| * vStar lam s * vStar lam s')

/-- The Theorem-D lower-bound constants: N₀* rate 2 − 1/c*, N₀ˢ rate 2c* − 1, N_d rate c*. -/
def HD (lam : ℝ) : ℝ := 2 - 1 / cStar lam

/-! ### Elementary range facts -/

theorem theta_nonneg {lam : ℝ} (h : 0 ≤ lam) : 0 ≤ theta lam := by
  unfold theta; positivity

theorem theta_pos {lam : ℝ} (h : 0 < lam) : 0 < theta lam := by
  unfold theta; positivity

theorem theta_le {lam : ℝ} (h : lam ≤ 1) (_h0 : 0 ≤ lam) : theta lam ≤ (Real.sqrt 2)⁻¹ := by
  unfold theta
  rw [div_le_iff₀ (by positivity), inv_mul_cancel₀ (by positivity)]
  exact h

theorem sqrt_two_inv_lt_one : (Real.sqrt 2)⁻¹ < 1 := by
  rw [inv_lt_one_iff₀]
  right
  nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]

/-- on [0, 1/√2] the denominator of cStar is ≥ 3/4  (cos x ≥ 1 − x²/2 and x sin x ≥ 0). -/
theorem theta_sq_le {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) : theta lam ^ 2 ≤ 1 / 2 := by
  have h := theta_le h1 h0
  have h2 : ((Real.sqrt 2)⁻¹) ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  calc theta lam ^ 2 ≤ ((Real.sqrt 2)⁻¹) ^ 2 := pow_le_pow_left₀ (theta_nonneg h0) h 2
    _ = 1 / 2 := h2

theorem theta_lt_pi_div_two {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    theta lam < π / 2 := by
  have h := theta_le h1 h0
  have := sqrt_two_inv_lt_one
  nlinarith [Real.pi_gt_three]

theorem sin_theta_nonneg {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    0 ≤ Real.sin (theta lam) := by
  apply Real.sin_nonneg_of_nonneg_of_le_pi (theta_nonneg h0)
  nlinarith [theta_lt_pi_div_two h0 h1, Real.pi_gt_three]

theorem sin_theta_pos {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    0 < Real.sin (theta lam) := by
  apply Real.sin_pos_of_pos_of_lt_pi (theta_pos h0)
  nlinarith [theta_lt_pi_div_two h0.le h1, Real.pi_gt_three]

theorem cos_theta_pos {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    0 < Real.cos (theta lam) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · nlinarith [theta_nonneg h0, Real.pi_gt_three]
  · exact theta_lt_pi_div_two h0 h1

theorem cStar_denom_ge {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    3 / 4 ≤ Real.cos (theta lam) + theta lam * Real.sin (theta lam) := by
  have h1' := Real.one_sub_sq_div_two_le_cos (x := theta lam)
  have h2 := theta_sq_le h0 h1
  have h3 := mul_nonneg (theta_nonneg h0) (sin_theta_nonneg h0 h1)
  linarith

theorem cStar_pos {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) : 0 < cStar lam := by
  unfold cStar
  have hn : 0 < Real.sqrt 2 * Real.sin (theta lam) := by
    have := sin_theta_pos h0 h1
    positivity
  have hd := cStar_denom_ge h0.le h1
  positivity

/-- Lipschitz bound on [0,1]: |c*_x − c*_y| ≤ 14|x − y| (the constant is crude). -/
theorem cStar_lipschitzOn {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |cStar x - cStar y| ≤ 14 * |x - y| := by
  have hs2 : (0:ℝ) < Real.sqrt 2 := by positivity
  have h12 : (1:ℝ) ≤ Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have h32 : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  set Nx := Real.sqrt 2 * Real.sin (theta x) with hNxd
  set Ny := Real.sqrt 2 * Real.sin (theta y) with hNyd
  set Dx := Real.cos (theta x) + theta x * Real.sin (theta x) with hDxd
  set Dy := Real.cos (theta y) + theta y * Real.sin (theta y) with hDyd
  have hDx0 : (3:ℝ)/4 ≤ Dx := cStar_denom_ge hx0 hx1
  have hDy0 : (3:ℝ)/4 ≤ Dy := cStar_denom_ge hy0 hy1
  have hθd : theta x - theta y = (x - y) / Real.sqrt 2 := by unfold theta; ring
  have hθabs : |theta x - theta y| ≤ |x - y| := by
    rw [hθd, abs_div, abs_of_pos hs2]
    exact div_le_self (abs_nonneg _) h12
  have hsinθ : |Real.sin (theta x) - Real.sin (theta y)| ≤ |x - y| / Real.sqrt 2 := by
    rw [← abs_of_pos hs2, ← abs_div, ← hθd]
    exact Real.abs_sin_sub_sin_le _ _
  have hsinθ' : |Real.sin (theta x) - Real.sin (theta y)| ≤ |x - y| :=
    le_trans (Real.abs_sin_sub_sin_le _ _) hθabs
  have hcosθ : |Real.cos (theta x) - Real.cos (theta y)| ≤ |x - y| :=
    le_trans (Real.abs_cos_sub_cos_le _ _) hθabs
  have hθyabs : |theta y| ≤ 1 := by
    rw [abs_of_nonneg (theta_nonneg hy0)]
    exact le_trans (theta_le hy1 hy0) (le_of_lt sqrt_two_inv_lt_one)
  -- |Nx − Ny| ≤ |x − y|·(3/2)  (crude: √2 ≤ 3/2, |sin difference| ≤ |x−y|)
  have hNd : |Nx - Ny| ≤ 3 / 2 * |x - y| := by
    rw [hNxd, hNyd, ← mul_sub, abs_mul, abs_of_pos hs2]
    exact mul_le_mul h32 hsinθ' (abs_nonneg _) (by norm_num)
  -- |Dx − Dy| ≤ 3|x − y|
  have hDd : |Dx - Dy| ≤ 3 * |x - y| := by
    have e : Dx - Dy = (Real.cos (theta x) - Real.cos (theta y))
        + ((theta x - theta y) * Real.sin (theta x)
          + theta y * (Real.sin (theta x) - Real.sin (theta y))) := by
      rw [hDxd, hDyd]; ring
    have h1 : |(theta x - theta y) * Real.sin (theta x)| ≤ |x - y| := by
      rw [abs_mul]
      calc |theta x - theta y| * |Real.sin (theta x)| ≤ |x - y| * 1 :=
            mul_le_mul hθabs (Real.abs_sin_le_one _) (abs_nonneg _) (abs_nonneg _)
        _ = |x - y| := mul_one _
    have h2 : |theta y * (Real.sin (theta x) - Real.sin (theta y))| ≤ |x - y| := by
      rw [abs_mul]
      calc |theta y| * |Real.sin (theta x) - Real.sin (theta y)| ≤ 1 * |x - y| :=
            mul_le_mul hθyabs hsinθ' (abs_nonneg _) zero_le_one
        _ = |x - y| := one_mul _
    calc |Dx - Dy| = |(Real.cos (theta x) - Real.cos (theta y))
        + ((theta x - theta y) * Real.sin (theta x)
          + theta y * (Real.sin (theta x) - Real.sin (theta y)))| := by rw [e]
      _ ≤ |Real.cos (theta x) - Real.cos (theta y)|
          + |(theta x - theta y) * Real.sin (theta x)
            + theta y * (Real.sin (theta x) - Real.sin (theta y))| := abs_add_le _ _
      _ ≤ |Real.cos (theta x) - Real.cos (theta y)|
          + (|(theta x - theta y) * Real.sin (theta x)|
            + |theta y * (Real.sin (theta x) - Real.sin (theta y))|) := by
          linarith [abs_add_le ((theta x - theta y) * Real.sin (theta x))
            (theta y * (Real.sin (theta x) - Real.sin (theta y)))]
      _ ≤ 3 * |x - y| := by linarith
  -- |Ny| ≤ 3/2, |Dy| ≤ 2
  have hNy : |Ny| ≤ 3 / 2 := by
    rw [hNyd, abs_mul, abs_of_pos hs2]
    calc Real.sqrt 2 * |Real.sin (theta y)| ≤ (3/2) * 1 :=
          mul_le_mul h32 (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num)
      _ = 3 / 2 := mul_one _
  have hDy2 : |Dy| ≤ 2 := by
    rw [hDyd]
    calc |Real.cos (theta y) + theta y * Real.sin (theta y)|
        ≤ |Real.cos (theta y)| + |theta y * Real.sin (theta y)| := abs_add_le _ _
      _ ≤ 1 + 1 * 1 := by
          refine add_le_add (Real.abs_cos_le_one _) ?_
          rw [abs_mul]
          exact mul_le_mul hθyabs (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one
      _ = 2 := by norm_num
  -- assemble
  have hDxne : Dx ≠ 0 := by linarith
  have hDyne : Dy ≠ 0 := by linarith
  have key : cStar x - cStar y = (Nx * Dy - Ny * Dx) / (Dx * Dy) := by
    unfold cStar
    rw [div_sub_div _ _ hDxne hDyne]
    ring
  rw [key, abs_div]
  have hnum : |Nx * Dy - Ny * Dx| ≤ 15 / 2 * |x - y| := by
    have e : Nx * Dy - Ny * Dx = (Nx - Ny) * Dy + Ny * (Dy - Dx) := by ring
    rw [e]
    calc |(Nx - Ny) * Dy + Ny * (Dy - Dx)|
        ≤ |(Nx - Ny) * Dy| + |Ny * (Dy - Dx)| := abs_add_le _ _
      _ = |Nx - Ny| * |Dy| + |Ny| * |Dy - Dx| := by rw [abs_mul, abs_mul]
      _ ≤ (3 / 2 * |x - y|) * 2 + (3 / 2) * (3 * |x - y|) := by
          refine add_le_add (mul_le_mul hNd hDy2 (abs_nonneg _) (by positivity)) ?_
          rw [abs_sub_comm]
          exact mul_le_mul hNy hDd (abs_nonneg _) (by norm_num)
      _ = 15 / 2 * |x - y| := by ring
  have hden : 9 / 16 ≤ |Dx * Dy| := by
    rw [abs_of_pos (by nlinarith : (0:ℝ) < Dx * Dy)]
    nlinarith
  calc |Nx * Dy - Ny * Dx| / |Dx * Dy| ≤ (15 / 2 * |x - y|) / (9 / 16) := by
        apply div_le_div₀ (by positivity) hnum (by norm_num) hden
    _ ≤ 14 * |x - y| := by rw [div_div_eq_mul_div]; nlinarith [abs_nonneg (x - y)]

/-- c*_λ is continuous on [0,1] (its denominator is ≥ 3/4 there); this is all the λ → 1⁻ passage needs. -/
theorem cStar_continuousOn : ContinuousOn cStar (Set.Icc 0 1) := by
  have hnum : Continuous fun lam : ℝ => Real.sqrt 2 * Real.sin (theta lam) := by unfold theta; fun_prop
  have hden : Continuous fun lam : ℝ => Real.cos (theta lam) + theta lam * Real.sin (theta lam) := by
    unfold theta; fun_prop
  refine (hnum.continuousOn.div hden.continuousOn fun lam hlam => ?_).congr fun lam _ => rfl
  have := cStar_denom_ge hlam.1 hlam.2
  linarith

/-- c* in the paper's tan form [eq:vstar] (cos ϑ ≠ 0 on the range). -/
theorem cStar_eq_tan_form {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    cStar lam = Real.sqrt 2 * Real.tan (theta lam)
      / (1 + theta lam * Real.tan (theta lam)) := by
  have hc := cos_theta_pos h0 h1
  have hd := cStar_denom_ge h0 h1
  have h3 : 0 ≤ theta lam * (Real.sin (theta lam) / Real.cos (theta lam)) := by
    have := sin_theta_nonneg h0 h1
    have := theta_nonneg h0
    positivity
  unfold cStar
  rw [Real.tan_eq_sin_div_cos, div_eq_div_iff (by linarith) (by linarith)]
  field_simp

/-! ### The moments of v*_λ (elementary trigonometric integrals) -/

/-- a* = √2 sin ϑ / λ  (= 2 sin(ω/2)/ω for ω = √2λ = 2ϑ). -/
theorem sqrt2_mul_half {lam : ℝ} : Real.sqrt 2 * lam * (1 / 2) = theta lam := by
  have hs2 : (0:ℝ) < Real.sqrt 2 := by positivity
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold theta
  rw [eq_div_iff hs2.ne']
  ring_nf
  rw [hsq]
  ring

theorem sqrt2_mul_neg_half {lam : ℝ} : Real.sqrt 2 * lam * (-(1:ℝ) / 2) = -theta lam := by
  have h := sqrt2_mul_half (lam := lam)
  ring_nf at h ⊢
  linarith

theorem aStar_eq {lam : ℝ} (h0 : 0 < lam) :
    aStar lam = Real.sqrt 2 * Real.sin (theta lam) / lam := by
  have hs2 : (0:ℝ) < Real.sqrt 2 := by positivity
  have hc : Real.sqrt 2 * lam ≠ 0 := by positivity
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold aStar vStar
  rw [intervalIntegral.integral_comp_mul_left Real.cos hc, integral_cos, smul_eq_mul,
    sqrt2_mul_half, sqrt2_mul_neg_half, Real.sin_neg]
  field_simp
  ring_nf
  try rw [hsq]
  try ring

/-- b* = 1/2 + sin(2ϑ)/(4ϑ). -/
theorem bStar_eq {lam : ℝ} (h0 : 0 < lam) :
    bStar lam = 1 / 2 + Real.sin (2 * theta lam) / (4 * theta lam) := by
  have hs2 : (0:ℝ) < Real.sqrt 2 := by positivity
  have hc : Real.sqrt 2 * lam ≠ 0 := by positivity
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hθ : 0 < theta lam := theta_pos h0
  unfold bStar vStar
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x ^ 2) hc, integral_cos_sq,
    smul_eq_mul, sqrt2_mul_half, sqrt2_mul_neg_half, Real.sin_neg, Real.cos_neg,
    Real.sin_two_mul]
  have h2θ : Real.sqrt 2 * lam = 2 * theta lam := by
    have := sqrt2_mul_half (lam := lam)
    linarith
  rw [h2θ]
  have hne : (2:ℝ) * theta lam ≠ 0 := by positivity
  field_simp
  ring

/-- antiderivative for the left piece: d/dx [(s−x)sin(ωx)/ω − cos(ωx)/ω²] = (s−x)cos(ωx). -/
private theorem hasDerivAt_left (ω s : ℝ) (hω : ω ≠ 0) (x : ℝ) :
    HasDerivAt (fun x => (s - x) * Real.sin (ω * x) / ω - Real.cos (ω * x) / ω ^ 2)
      ((s - x) * Real.cos (ω * x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => s - x) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub s
  have hlin : HasDerivAt (fun x : ℝ => ω * x) (ω * 1) x := (hasDerivAt_id x).const_mul ω
  have h2 : HasDerivAt (fun x : ℝ => Real.sin (ω * x)) (Real.cos (ω * x) * (ω * 1)) x :=
    (Real.hasDerivAt_sin (ω * x)).comp x hlin
  have h3 : HasDerivAt (fun x : ℝ => Real.cos (ω * x)) (-Real.sin (ω * x) * (ω * 1)) x :=
    (Real.hasDerivAt_cos (ω * x)).comp x hlin
  have h4 := ((h1.mul h2).div_const ω).sub (h3.div_const (ω ^ 2))
  exact h4.congr_deriv (by field_simp; ring)

/-- antiderivative for the right piece: d/dx [(x−s)sin(ωx)/ω + cos(ωx)/ω²] = (x−s)cos(ωx). -/
private theorem hasDerivAt_right (ω s : ℝ) (hω : ω ≠ 0) (x : ℝ) :
    HasDerivAt (fun x => (x - s) * Real.sin (ω * x) / ω + Real.cos (ω * x) / ω ^ 2)
      ((x - s) * Real.cos (ω * x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => x - s) 1 x := by
    simpa using (hasDerivAt_id x).sub_const s
  have hlin : HasDerivAt (fun x : ℝ => ω * x) (ω * 1) x := (hasDerivAt_id x).const_mul ω
  have h2 : HasDerivAt (fun x : ℝ => Real.sin (ω * x)) (Real.cos (ω * x) * (ω * 1)) x :=
    (Real.hasDerivAt_sin (ω * x)).comp x hlin
  have h3 : HasDerivAt (fun x : ℝ => Real.cos (ω * x)) (-Real.sin (ω * x) * (ω * 1)) x :=
    (Real.hasDerivAt_cos (ω * x)).comp x hlin
  have h4 := ((h1.mul h2).div_const ω).add (h3.div_const (ω ^ 2))
  exact h4.congr_deriv (by field_simp; ring)

/-- the inner kernel integral: for s ∈ [−1/2, 1/2],
∫ s' in −1/2..1/2, |s − s'| cos(√2 λ s') = a*/2 + cos ϑ/λ² − cos(√2 λ s)/λ². -/
private theorem kernel_eq {lam : ℝ} (h0 : 0 < lam) {s : ℝ} (hs1 : -(1:ℝ)/2 ≤ s)
    (hs2 : s ≤ 1/2) :
    ∫ s' in (-(1:ℝ)/2)..(1/2), |s - s'| * Real.cos (Real.sqrt 2 * lam * s')
      = aStar lam / 2 + Real.cos (theta lam) / lam ^ 2
        - Real.cos (Real.sqrt 2 * lam * s) / lam ^ 2 := by
  have hs2' : (0:ℝ) < Real.sqrt 2 := by positivity
  have hω : Real.sqrt 2 * lam ≠ 0 := by positivity
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set ω := Real.sqrt 2 * lam with hωdef
  have hcont : ∀ a b : ℝ, IntervalIntegrable
      (fun s' => |s - s'| * Real.cos (ω * s')) MeasureTheory.volume a b := fun a b =>
    (Continuous.intervalIntegrable (by fun_prop) a b)
  -- split at s
  have hsplit : ∫ s' in (-(1:ℝ)/2)..(1/2), |s - s'| * Real.cos (ω * s')
      = (∫ s' in (-(1:ℝ)/2)..s, |s - s'| * Real.cos (ω * s'))
        + ∫ s' in s..(1/2), |s - s'| * Real.cos (ω * s') :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont _ _) (hcont _ _)).symm
  -- left piece
  have hleft : ∫ s' in (-(1:ℝ)/2)..s, |s - s'| * Real.cos (ω * s')
      = (∫ s' in (-(1:ℝ)/2)..s, (s - s') * Real.cos (ω * s')) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hs1] at hx
    show |s - x| * Real.cos (ω * x) = (s - x) * Real.cos (ω * x)
    rw [abs_of_nonneg (by linarith [hx.2] : (0:ℝ) ≤ s - x)]
  have hleft2 : ∫ s' in (-(1:ℝ)/2)..s, (s - s') * Real.cos (ω * s')
      = ((s - s) * Real.sin (ω * s) / ω - Real.cos (ω * s) / ω ^ 2)
        - ((s - (-(1:ℝ)/2)) * Real.sin (ω * (-(1:ℝ)/2)) / ω
            - Real.cos (ω * (-(1:ℝ)/2)) / ω ^ 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_left ω s hω x) (Continuous.intervalIntegrable (by fun_prop) _ _)
  -- right piece
  have hright : ∫ s' in s..(1/2), |s - s'| * Real.cos (ω * s')
      = (∫ s' in s..(1/2), (s' - s) * Real.cos (ω * s')) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hs2] at hx
    show |s - x| * Real.cos (ω * x) = (x - s) * Real.cos (ω * x)
    rw [abs_of_nonpos (by linarith [hx.1] : s - x ≤ 0), neg_sub]
  have hright2 : ∫ s' in s..(1/2), (s' - s) * Real.cos (ω * s')
      = (((1:ℝ)/2 - s) * Real.sin (ω * (1/2)) / ω + Real.cos (ω * (1/2)) / ω ^ 2)
        - ((s - s) * Real.sin (ω * s) / ω + Real.cos (ω * s) / ω ^ 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_right ω s hω x) (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [hsplit, hleft, hleft2, hright, hright2, aStar_eq h0]
  rw [show ω * (1/2) = theta lam from sqrt2_mul_half, show ω * (-(1:ℝ)/2) = -theta lam
    from sqrt2_mul_neg_half, Real.sin_neg, Real.cos_neg]
  have hω2 : ω ^ 2 = 2 * lam ^ 2 := by rw [hωdef, mul_pow, hsq]
  rw [hω2]
  have h2θ : ω = 2 * theta lam := by
    have := sqrt2_mul_half (lam := lam)
    rw [hωdef]; linarith
  rw [h2θ]
  have hθ : 0 < theta lam := theta_pos h0
  field_simp
  ring_nf
  rw [show theta lam = lam / Real.sqrt 2 from rfl]
  field_simp
  ring_nf
  try rw [hsq]
  try ring

/-- The kernel identity behind J*: with β := a*/2 + cos ϑ/λ²,
∬|s−s'| v* v* = β a* − b*/λ². -/
theorem jStar_eq {lam : ℝ} (h0 : 0 < lam) (_h1 : lam ≤ 1) :
    jStar lam = (aStar lam / 2 + Real.cos (theta lam) / lam ^ 2) * aStar lam
      - bStar lam / lam ^ 2 := by
  have hω : Real.sqrt 2 * lam ≠ 0 := by positivity
  -- pull v(s) out of the inner integral and substitute the kernel closed form
  have hstep : ∀ s ∈ Set.uIcc (-(1:ℝ)/2) (1/2),
      (∫ s' in (-(1:ℝ)/2)..(1/2), |s - s'| * vStar lam s * vStar lam s')
        = vStar lam s * (aStar lam / 2 + Real.cos (theta lam) / lam ^ 2)
          - vStar lam s * Real.cos (Real.sqrt 2 * lam * s) / lam ^ 2 := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    have e1 : ∀ s' : ℝ, |s - s'| * vStar lam s * vStar lam s'
        = vStar lam s * (|s - s'| * Real.cos (Real.sqrt 2 * lam * s')) := by
      intro s'
      unfold vStar
      ring
    rw [intervalIntegral.integral_congr (fun s' _ => e1 s'),
      intervalIntegral.integral_const_mul, kernel_eq h0 hs.1 hs.2]
    ring
  unfold jStar
  rw [intervalIntegral.integral_congr hstep]
  have hii1 : IntervalIntegrable (fun s => vStar lam s *
      (aStar lam / 2 + Real.cos (theta lam) / lam ^ 2)) MeasureTheory.volume
      (-(1:ℝ)/2) (1/2) := by
    apply Continuous.intervalIntegrable
    unfold vStar
    fun_prop
  have hii2 : IntervalIntegrable (fun s => vStar lam s *
      Real.cos (Real.sqrt 2 * lam * s) / lam ^ 2) MeasureTheory.volume
      (-(1:ℝ)/2) (1/2) := by
    apply Continuous.intervalIntegrable
    unfold vStar
    fun_prop
  rw [intervalIntegral.integral_sub hii1 hii2, intervalIntegral.integral_mul_const]
  have e2 : ∀ s' : ℝ, vStar lam s' * Real.cos (Real.sqrt 2 * lam * s') / lam ^ 2
      = vStar lam s' ^ 2 * (lam ^ 2)⁻¹ := by
    intro s'
    unfold vStar
    ring
  rw [intervalIntegral.integral_congr (fun s' _ => e2 s'),
    intervalIntegral.integral_mul_const]
  unfold aStar bStar
  field_simp
  try ring

/-- [eq:vstar]: c_λ(v*_λ) = c*_λ  (the algebra b* + λ²J* = λ² β a* = ϑ sin ϑ·(√2 sin ϑ/λ·…),
collapsing to √2 sin ϑ/(cos ϑ + ϑ sin ϑ) after cancelling a*). -/
theorem cFun_vStar {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    cFun lam (vStar lam) = cStar lam := by
  have hθ := theta_pos h0
  have hs := sin_theta_pos h0 h1
  have hd := cStar_denom_ge h0.le h1
  have hdne : Real.cos (theta lam) + theta lam * Real.sin (theta lam) ≠ 0 := by linarith
  have hs2 : (0:ℝ) < Real.sqrt 2 := by positivity
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ha : aStar lam = Real.sqrt 2 * Real.sin (theta lam) / lam := aStar_eq h0
  have hD : bStar lam + lam ^ 2 * jStar lam
      = aStar lam * (Real.cos (theta lam) + theta lam * Real.sin (theta lam)) := by
    rw [jStar_eq h0 h1]
    rw [show theta lam = lam / Real.sqrt 2 from rfl] at *
    rw [ha]
    field_simp [h0.ne', hs2.ne']
    ring_nf
    try rw [hsq]
    try ring
  show lam * aStar lam ^ 2 / (bStar lam + lam ^ 2 * jStar lam) = cStar lam
  rw [hD, ha]
  unfold cStar
  field_simp [h0.ne', hs2.ne', hs.ne', hdne]
  try ring_nf
  try rw [hsq]
  try ring

/-! ### The λ = 1 values (the constants of Theorem D) -/

/-- HD 1 = 3/2 − (1/√2)·cot(1/√2)  (the paper's 2 − 1/c₁* = 3/2 − 2^{-1/2} cot 2^{-1/2}). -/
theorem theta_one : theta 1 = (Real.sqrt 2)⁻¹ := by
  unfold theta; rw [one_div]

theorem HD_one :
    HD 1 = 3 / 2 - (Real.sqrt 2)⁻¹ * (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹) := by
  have hs : 0 < Real.sin ((Real.sqrt 2)⁻¹) := by
    have := sin_theta_pos one_pos le_rfl
    rwa [theta_one] at this
  have hs2 : (0:ℝ) < Real.sqrt 2 := by positivity
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold HD cStar
  rw [theta_one, one_div_div]
  have hne : Real.sqrt 2 * Real.sin ((Real.sqrt 2)⁻¹) ≠ 0 := by positivity
  field_simp
  ring_nf
  rw [mul_inv_cancel₀ hs.ne', hsq]
  ring


/-- closed form of J* (used by Window.lean's jD_close):
J* = sin(2ϑ)/(8ϑ³) − cos(2ϑ)/(4ϑ²)  (pure algebra from jStar_eq + aStar_eq + bStar_eq,
using λ² = 2ϑ², sin 2ϑ = 2 sin ϑ cos ϑ, cos 2ϑ = 1 − 2 sin²ϑ). -/
theorem jStar_closed {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    jStar lam = Real.sin (2 * theta lam) / (8 * theta lam ^ 3)
      - Real.cos (2 * theta lam) / (4 * theta lam ^ 2) := by
  have hθ : 0 < theta lam := theta_pos h0
  have hs2 : (0:ℝ) < Real.sqrt 2 := by positivity
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hlam2 : lam ^ 2 = 2 * theta lam ^ 2 := by
    rw [show theta lam = lam / Real.sqrt 2 from rfl]
    field_simp
    ring_nf
    try rw [hsq]
    try ring
  rw [jStar_eq h0 h1, aStar_eq h0, bStar_eq h0, Real.sin_two_mul, Real.cos_two_mul']
  have ha : Real.sqrt 2 * Real.sin (theta lam) / lam = Real.sin (theta lam) / theta lam := by
    rw [show theta lam = lam / Real.sqrt 2 from rfl]
    field_simp
  rw [ha]
  field_simp
  linear_combination (16 * theta lam * lam ^ 2) * Real.sin_sq_add_cos_sq (theta lam)
    + (16 * theta lam - 16 * Real.sin (theta lam) * Real.cos (theta lam)) * hlam2

end ThmD
end Zeta23
