/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of the paper
"More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/
import Zeta23.PrimeSideB.PPKernel
import Zeta23.PrimeSideB.PP
import Zeta23.ThmE.Hypotheses
import Zeta23.ThmE.PrimeSideChi

/-!
# [prop:PP] for L(s,chi)

[thm:E] proof (iii) (§8.2): "the coefficients a_n acquire unimodular factors chi(n)n^{i.}, which
leave the diagonal D unchanged (|chi(n)|^2 = 1) and enter Lemma lem:MV and all other bounds only
through |a_n|".  This file proves that sentence for [prop:PP]:

* prop_PP_chi:  |M[P_{X,c}, P_{X,c}] − (T/pi)·sumA2gCoprime| ≤ C·L²X, over EventuallyAtCore
  (window-generic: no flat-top plateau fact used); hypotheses H-cheb + H-MV + CoeffUnimodular
  (unimodularity used EXACTLY once: the diagonal main term a_n²·normSq(c n)).
* sumA2gCoprime_upper (over EventuallyAtCore) and sumA2gCoprime_lower (over the FULL EventuallyAt:
  the lower g-sandwich needs LocalHyps.g_lower, which LocalHypsCore deliberately lacks — the
  Montgomery–Taylor window case supplies its own analogue), from H-cheb-coprime.

Route (magnitude/phase): write c n = r_n·exp(i·phi_n),
r_n := norm (c n), phi_n := arg (c n), so P_{X,c}(tau) = −(1/pi)·Sum_n a_n·r_n·cos(tau·log n − phi_n)
— ONE family of phase-shifted cosines.  The PPKernel pair decomposition generalizes by a single
phase parameter (Jker already carries an arbitrary constant): AminusPh/AplusPh below.  On the
diagonal the phase difference vanishes and AminusPh = Aminus, giving the zeta diagonal with weight
r_n²; the off-diagonal [lem:MV] application takes x_n with norm x_n ≤ a_n ("only through |a_n|");
the O2 bound is phase-free.
-/

noncomputable section

open MeasureTheory Real Set Finset ComplexConjugate
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace ThmE

open Zeta23.PrimeSide

variable {cϱ lam : ℝ} {q : ℕ} {c : ℕ → ℂ}

/-- Sum_{n ≤ X, (n,q)=1} Lambda(n)²/n · g(log n) — the [prop:PP] main-term sum for L(s,chi)
(index set = ChebyshevMertensCoprime's). -/
def sumA2gCoprime (q : ℕ) (X : ℝ) (g : ℝ → ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => Nat.Coprime n q),
    (Λ n : ℝ) ^ 2 / n * g (Real.log n)

/-- The weighted diagonal sum equals the coprime sum, for unimodular coefficients. -/
lemma sum_w_eq_sumA2gCoprime (hc : CoeffUnimodular q c) (X : ℝ) (g : ℝ → ℝ) :
    ∑ n ∈ primeRange X, acoef n ^ 2 * ‖c n‖ ^ 2 * g (Real.log n) = sumA2gCoprime q X g := by
  unfold sumA2gCoprime
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
  by_cases hcop : Nat.Coprime n q
  · rw [if_pos hcop, hc.norm_eq n hn0 hcop, acoef_sq]
    ring
  · rw [if_neg hcop, hc.toCoeffOK.vanish n hcop]
    simp

section PhaseKernel
variable {Φ : ℝ → ℝ} {T : ℝ}

/-- A⁻ with phases. -/
def AminusPh (Φ : ℝ → ℝ) (T y y' φ φ' : ℝ) : ℝ :=
  ∫ x in Icc (-T) T,
    Φ x ^ 2 * Jker (y - y') (x * y - (φ - φ')) (max (T - x) T) (min (2 * T - x) (2 * T))

/-- A⁺ with phases. -/
def AplusPh (Φ : ℝ → ℝ) (T y y' φ φ' : ℝ) : ℝ :=
  ∫ x in Icc (-T) T,
    Φ x ^ 2 * Jker (y + y') (x * y - (φ + φ')) (max (T - x) T) (min (2 * T - x) (2 * T))

/-- Equal phases: AminusPh = Aminus (the diagonal case). -/
lemma AminusPh_self (y y' φ : ℝ) : AminusPh Φ T y y' φ φ = Aminus Φ T y y' := by
  unfold AminusPh Aminus JmK
  simp only [sub_self, sub_zero]

/-- Continuity of the phased Jker integrand in x (mirror of continuous_Jker_offset). -/
lemma continuous_Jker_offset_ph (θ y ψ T : ℝ) :
    Continuous (fun x : ℝ =>
      Jker θ (x * y - ψ) (max (T - x) T) (min (2 * T - x) (2 * T))) := by
  by_cases hθ : θ = 0
  · simp only [Jker, hθ, if_true]; fun_prop
  · simp only [Jker, hθ, if_false]; fun_prop

/-- Product-to-sum with phases on the sheared window (mirror of inner_cos_cos). -/
lemma inner_cos_cos_ph (hT : 0 ≤ T) {x : ℝ} (hx : |x| ≤ T) (y y' φ φ' : ℝ) :
    ∫ τ' in Ix T x, Real.cos ((x + τ') * y - φ) * Real.cos (τ' * y' - φ')
      = (Jker (y - y') (x * y - (φ - φ')) (max (T - x) T) (min (2 * T - x) (2 * T))
          + Jker (y + y') (x * y - (φ + φ')) (max (T - x) T) (min (2 * T - x) (2 * T))) / 2 := by
  have hle := Ix_le hT hx
  unfold Ix
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
    ← intervalIntegral_cos_linear_eq_Jker, ← intervalIntegral_cos_linear_eq_Jker,
    ← intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro t _
  simp only
  rw [cos_mul_cos_eq]
  congr 2 <;> (congr 1; ring)

end PhaseKernel


section PhasePair
variable {Φ : ℝ → ℝ} {T : ℝ}

/-- [eq:MPP] per pair with phases: for T ≥ 0,
M[cos(·y − φ), cos(·y' − φ')] = ½ A⁻_ph + ½ A⁺_ph. -/
lemma Mform_cos_cos_ph (hT : 0 ≤ T) (hΦ : Continuous Φ) (y y' φ φ' : ℝ) :
    Mform Φ T (fun τ => Real.cos (τ * y - φ)) (fun τ => Real.cos (τ * y' - φ'))
      = (AminusPh Φ T y y' φ φ' + AplusPh Φ T y y' φ φ') / 2 := by
  unfold Mform AminusPh AplusPh
  have h1 : (fun q : ℝ × ℝ => Φ (q.1 - q.2) ^ 2 * Real.cos (q.1 * y - φ) * Real.cos (q.2 * y' - φ'))
      = fun q => Φ (q.1 - q.2) ^ 2 *
          (fun q : ℝ × ℝ => Real.cos (q.1 * y - φ) * Real.cos (q.2 * y' - φ')) q := by
    funext q; ring
  rw [h1, sqIntegral_shear hΦ (by fun_prop)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-T) T) ?zero]
  case zero =>
    intro x hx
    rw [Ix_eq_empty hT (not_mem_Icc_neg hx)]; simp
  have h2 : ∀ x ∈ Icc (-T) T,
      Φ x ^ 2 * ∫ τ' in Ix T x, Real.cos ((x + τ') * y - φ) * Real.cos (τ' * y' - φ')
        = (Φ x ^ 2 * Jker (y - y') (x * y - (φ - φ')) (max (T - x) T) (min (2 * T - x) (2 * T))
            + Φ x ^ 2 * Jker (y + y') (x * y - (φ + φ')) (max (T - x) T) (min (2 * T - x) (2 * T))) / 2 := by
    intro x hx
    rw [inner_cos_cos_ph hT (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩)]
    ring
  rw [setIntegral_congr_fun measurableSet_Icc h2, integral_div, integral_add]
  · exact ((hΦ.pow 2).mul (continuous_Jker_offset_ph _ _ _ _)).integrableOn_Icc
  · exact ((hΦ.pow 2).mul (continuous_Jker_offset_ph _ _ _ _)).integrableOn_Icc

/-- O₂-type bound, phase-free (mirror of abs_Aplus_le): for 0 < y + y',
|A⁺_ph(y,y',φ,φ')| ≤ (2/(y+y'))·∫Φ². -/
lemma abs_AplusPh_le (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2) {y y' : ℝ}
    (hyy : 0 < y + y') (φ φ' : ℝ) :
    |AplusPh Φ T y y' φ φ'| ≤ 2 / (y + y') * ∫ x, Φ x ^ 2 := by
  unfold AplusPh
  have hne : y + y' ≠ 0 := hyy.ne'
  have hint : IntegrableOn (fun x => Φ x ^ 2 *
      Jker (y + y') (x * y - (φ + φ')) (max (T - x) T) (min (2 * T - x) (2 * T))) (Icc (-T) T) :=
    ((hΦ.pow 2).mul (continuous_Jker_offset_ph _ _ _ _)).integrableOn_Icc
  calc |∫ x in Icc (-T) T, Φ x ^ 2 *
          Jker (y + y') (x * y - (φ + φ')) (max (T - x) T) (min (2 * T - x) (2 * T))|
      ≤ ∫ x in Icc (-T) T, |Φ x ^ 2 *
          Jker (y + y') (x * y - (φ + φ')) (max (T - x) T) (min (2 * T - x) (2 * T))| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x in Icc (-T) T, Φ x ^ 2 * (2 / (y + y')) := by
        apply setIntegral_mono_on hint.abs (hΦ2.integrableOn.mul_const _) measurableSet_Icc
        intro x _
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        have h := abs_Jker_le hne (x * y - (φ + φ')) (max (T - x) T) (min (2 * T - x) (2 * T))
        rwa [abs_of_pos hyy] at h
    _ = 2 / (y + y') * ∫ x in Icc (-T) T, Φ x ^ 2 := by rw [integral_mul_const]; ring
    _ ≤ 2 / (y + y') * ∫ x, Φ x ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact setIntegral_le_integral hΦ2 (Filter.Eventually.of_forall fun x => sq_nonneg _)

end PhasePair

section PhaseO1
variable {Φ : ℝ → ℝ} {T : ℝ}

/-- O₁-type exact evaluation with phases (mirror of sub_mul_Aminus_eq): for θ := y − y' ≠ 0, T ≥ 0,
ψ := φ − φ':
θ·A⁻_ph(y,y',φ,φ') = [sin(θ2T−ψ)C⁻(y) + cos(θ2T−ψ)S⁻(y) − (sin(θT−ψ)C⁻(y') + cos(θT−ψ)S⁻(y'))]
                   + [sin(θ2T−ψ)C⁺(y') + cos(θ2T−ψ)S⁺(y') − (sin(θT−ψ)C⁺(y) + cos(θT−ψ)S⁺(y))]. -/
lemma sub_mul_AminusPh_eq (hT : 0 ≤ T) (hΦ : Continuous Φ) {y y' : ℝ} (hθ : y - y' ≠ 0)
    (φ φ' : ℝ) :
    (y - y') * AminusPh Φ T y y' φ φ'
      = (Real.sin ((y - y') * (2 * T) - (φ - φ')) * Cm Φ T y
          + Real.cos ((y - y') * (2 * T) - (φ - φ')) * Sm Φ T y
          - (Real.sin ((y - y') * T - (φ - φ')) * Cm Φ T y'
            + Real.cos ((y - y') * T - (φ - φ')) * Sm Φ T y'))
        + (Real.sin ((y - y') * (2 * T) - (φ - φ')) * Cp Φ T y'
          + Real.cos ((y - y') * (2 * T) - (φ - φ')) * Sp Φ T y'
          - (Real.sin ((y - y') * T - (φ - φ')) * Cp Φ T y
            + Real.cos ((y - y') * T - (φ - φ')) * Sp Φ T y)) := by
  unfold AminusPh Cm Sm Cp Sp
  have hcont : Continuous fun x => Φ x ^ 2 * ((y - y') *
      Jker (y - y') (x * y - (φ - φ')) (max (T - x) T) (min (2 * T - x) (2 * T))) := by
    have := continuous_Jker_offset_ph (y - y') y (φ - φ') T; fun_prop
  rw [← integral_const_mul]
  have e1 : ∀ x, (y - y') * (Φ x ^ 2 *
      Jker (y - y') (x * y - (φ - φ')) (max (T - x) T) (min (2 * T - x) (2 * T)))
      = Φ x ^ 2 * ((y - y') *
          Jker (y - y') (x * y - (φ - φ')) (max (T - x) T) (min (2 * T - x) (2 * T))) := by
    intro x; ring
  simp_rw [e1]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -T ≤ T),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hL : ∫ x in (-T)..0, Φ x ^ 2 * ((y - y') *
      Jker (y - y') (x * y - (φ - φ')) (max (T - x) T) (min (2 * T - x) (2 * T)))
      = ∫ x in (-T)..0, Φ x ^ 2 * (Real.sin (((y - y') * (2 * T) - (φ - φ')) + x * y)
          - Real.sin (((y - y') * T - (φ - φ')) + x * y')) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith : -T ≤ 0)] at hx
    simp only
    congr 1
    rw [max_eq_left (by linarith [hx.2]), min_eq_right (by linarith [hx.2]), Jker_of_ne hθ,
      mul_div_cancel₀ _ hθ]
    congr 1
    · rw [show (y - y') * (2 * T) + (x * y - (φ - φ')) = ((y - y') * (2 * T) - (φ - φ')) + x * y by ring]
    · rw [show (y - y') * (T - x) + (x * y - (φ - φ')) = ((y - y') * T - (φ - φ')) + x * y' by ring]
  have hR : ∫ x in (0:ℝ)..T, Φ x ^ 2 * ((y - y') *
      Jker (y - y') (x * y - (φ - φ')) (max (T - x) T) (min (2 * T - x) (2 * T)))
      = ∫ x in (0:ℝ)..T, Φ x ^ 2 * (Real.sin (((y - y') * (2 * T) - (φ - φ')) + x * y')
          - Real.sin (((y - y') * T - (φ - φ')) + x * y)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hT] at hx
    simp only
    congr 1
    rw [max_eq_right (by linarith [hx.1]), min_eq_left (by linarith [hx.1]), Jker_of_ne hθ,
      mul_div_cancel₀ _ hθ]
    congr 1
    · rw [show (y - y') * (2 * T - x) + (x * y - (φ - φ')) = ((y - y') * (2 * T) - (φ - φ')) + x * y' by ring]
    · rw [show (y - y') * T + (x * y - (φ - φ')) = ((y - y') * T - (φ - φ')) + x * y by ring]
  rw [hL, hR, integral_sq_mul_sin_sub_sin hΦ, integral_sq_mul_sin_sub_sin hΦ]

end PhaseO1

/-! ## The magnitude/phase form of P_{X,c} -/

section PXcForm

/-- n^(−1/2 − iτ) = (√n)⁻¹·e^{−i·τ·log n} for n ≥ 1. -/
lemma cpow_neg_half_sub_I_mul {n : ℕ} (hn : 1 ≤ n) (τ : ℝ) :
    (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * τ)
      = (((Real.sqrt n)⁻¹ : ℝ) : ℂ) * Complex.exp ((-(τ * Real.log n) : ℝ) * Complex.I) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [show ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) by push_cast; rfl]
    exact (Complex.ofReal_log hn0.le).symm
  rw [Complex.cpow_def_of_ne_zero hnC, hlog]
  have harg : ((Real.log n : ℝ) : ℂ) * (-(1 / 2 : ℂ) - Complex.I * τ)
      = ((-(Real.log n / 2) : ℝ) : ℂ) + ((-(τ * Real.log n) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_exp]
  congr 1
  rw [Real.exp_neg]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0]
  congr 1
  ring

/-- The magnitude/phase form:  P_{X,c}(τ) = −(1/π) Σ_n a_n·‖c n‖·cos(τ·log n − arg(c n)). -/
lemma PXc_eq_sum (c : ℕ → ℂ) (X τ : ℝ) :
    PXc c X τ = -(1 / π) * ∑ n ∈ primeRange X,
      acoef n * ‖c n‖ * Real.cos (τ * Real.log n - (c n).arg) := by
  unfold PXc
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := one_le_of_mem_primeRange hn
  rw [cpow_neg_half_sub_I_mul hn1]
  have hsplit : ((Λ n : ℝ) : ℂ) * c n * ((((Real.sqrt n)⁻¹ : ℝ) : ℂ)
        * Complex.exp ((-(τ * Real.log n) : ℝ) * Complex.I))
      = (((Λ n : ℝ) * (Real.sqrt n)⁻¹ : ℝ) : ℂ)
        * (c n * Complex.exp ((-(τ * Real.log n) : ℝ) * Complex.I)) := by
    push_cast
    ring
  rw [hsplit, Complex.re_ofReal_mul]
  have hc : c n * Complex.exp ((-(τ * Real.log n) : ℝ) * Complex.I)
      = ((‖c n‖ : ℝ) : ℂ) * Complex.exp ((((c n).arg - τ * Real.log n : ℝ)) * Complex.I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (c n)]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hc, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hcos : Real.cos ((c n).arg - τ * Real.log n) = Real.cos (τ * Real.log n - (c n).arg) := by
    rw [← Real.cos_neg]
    congr 1
    ring
  rw [hcos]
  unfold acoef
  rw [div_eq_mul_inv]
  ring

end PXcForm

/-! ## H-MV with phases -/

section MVPh
variable {C : ℝ}

/-- Mirror of MV_real with a per-index phase: for real weights u, v and phases φv,
both trig sums Σ_{n≠m} u_n v_m·trig(cc(y_n−y_m) − (φv_n − φv_m))/(y_n−y_m) obey the H-MV bound. -/
lemma MV_real_ph (hMV : Zeta23.MVHilbert C) (X cc : ℝ) (u v φv : ℕ → ℝ) :
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
        u n * v m * Real.cos (cc * (Real.log n - Real.log m) - (φv n - φv m))
          / (Real.log n - Real.log m))|
      ≤ C * Real.sqrt (∑ n ∈ primeRange X, u n ^ 2 * (2 * n))
          * Real.sqrt (∑ n ∈ primeRange X, v n ^ 2 * (2 * n)) ∧
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
        u n * v m * Real.sin (cc * (Real.log n - Real.log m) - (φv n - φv m))
          / (Real.log n - Real.log m))|
      ≤ C * Real.sqrt (∑ n ∈ primeRange X, u n ^ 2 * (2 * n))
          * Real.sqrt (∑ n ∈ primeRange X, v n ^ 2 * (2 * n)) := by
  set x : ℕ → ℂ := fun n => (u n : ℂ)
    * Complex.exp ((cc * Real.log n - φv n : ℝ) * Complex.I) with hx
  set z : ℕ → ℂ := fun n => (v n : ℂ)
    * Complex.exp ((cc * Real.log n - φv n : ℝ) * Complex.I) with hz
  have key := MV_primeRange hMV X x z
  have hnx : ∀ n, ‖x n‖ ^ 2 = u n ^ 2 := by
    intro n
    simp only [hx, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have hnz : ∀ n, ‖z n‖ ^ 2 = v n ^ 2 := by
    intro n
    simp only [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  simp_rw [hnx, hnz] at key
  have hprod : ∀ n m, x n * conj (z m)
      = ((u n * v m : ℝ) : ℂ)
        * Complex.exp ((cc * (Real.log n - Real.log m) - (φv n - φv m) : ℝ) * Complex.I) := by
    intro n m
    have harg : ((cc * Real.log n - φv n : ℝ) : ℂ) * Complex.I
        + ((cc * Real.log m - φv m : ℝ) : ℂ) * (starRingEnd ℂ) Complex.I
        = ((cc * (Real.log n - Real.log m) - (φv n - φv m) : ℝ) : ℂ) * Complex.I := by
      rw [Complex.conj_I]; push_cast; ring
    simp only [hx, hz, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    rw [mul_mul_mul_comm, ← Complex.exp_add, harg]
    push_cast; ring
  have hre : (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        (if n = m then (0:ℂ) else x n * conj (z m) / ((Real.log n - Real.log m : ℝ) : ℂ))).re
      = ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
        u n * v m * Real.cos (cc * (Real.log n - Real.log m) - (φv n - φv m))
          / (Real.log n - Real.log m)) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with h
    · simp
    · rw [hprod, Complex.div_ofReal_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have him : (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        (if n = m then (0:ℂ) else x n * conj (z m) / ((Real.log n - Real.log m : ℝ) : ℂ))).im
      = ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
        u n * v m * Real.sin (cc * (Real.log n - Real.log m) - (φv n - φv m))
          / (Real.log n - Real.log m)) := by
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with h
    · simp
    · rw [hprod, Complex.div_ofReal_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  constructor
  · rw [← hre]; exact (Complex.abs_re_le_norm _).trans key
  · rw [← him]; exact (Complex.abs_im_le_norm _).trans key

/-- Size bound with weights on BOTH slots: |w₁| ≤ 1, |w₂| ≤ W ⟹ the MV bound ≤ 2CW·ΣΛ²,
in both slot orders. -/
lemma MV_size_le₂ (hC : 0 ≤ C) (X : ℝ) {w₁ w₂ : ℕ → ℝ} {W : ℝ} (hW : 0 ≤ W)
    (hw₁ : ∀ n ∈ primeRange X, |w₁ n| ≤ 1) (hw₂ : ∀ n ∈ primeRange X, |w₂ n| ≤ W) :
    C * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₁ n) ^ 2 * (2 * n))
        * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₂ n) ^ 2 * (2 * n))
      ≤ 2 * C * W * ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 ∧
    C * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₂ n) ^ 2 * (2 * n))
        * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₁ n) ^ 2 * (2 * n))
      ≤ 2 * C * W * ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 := by
  set Λ2 := ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 with hΛ2
  have hΛ2nn : 0 ≤ Λ2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hbd : ∀ (w : ℕ → ℝ) (B : ℝ), 0 ≤ B → (∀ n ∈ primeRange X, |w n| ≤ B) →
      ∑ n ∈ primeRange X, (acoef n * w n) ^ 2 * (2 * n) ≤ B ^ 2 * (2 * Λ2) := by
    intro w B hB hw
    rw [hΛ2, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [mul_pow, mul_comm (acoef n ^ 2), mul_assoc,
      acoef_sq_mul_two_mul (one_le_of_mem_primeRange hn)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (sq_abs (w n)).symm ▸ pow_le_pow_left₀ (abs_nonneg _) (hw n hn) 2
  have h1 := hbd w₁ 1 zero_le_one hw₁
  have h2 := hbd w₂ W hW hw₂
  have hs1 : Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₁ n) ^ 2 * (2 * n))
      ≤ Real.sqrt (2 * Λ2) := by
    refine (Real.sqrt_le_sqrt h1).trans ?_
    rw [one_pow, one_mul]
  have hs2 : Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₂ n) ^ 2 * (2 * n))
      ≤ W * Real.sqrt (2 * Λ2) := by
    calc Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₂ n) ^ 2 * (2 * n))
        ≤ Real.sqrt (W ^ 2 * (2 * Λ2)) := Real.sqrt_le_sqrt h2
      _ = W * Real.sqrt (2 * Λ2) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hW]
  have hsq : Real.sqrt (2 * Λ2) * Real.sqrt (2 * Λ2) = 2 * Λ2 :=
    Real.mul_self_sqrt (by positivity)
  constructor
  · calc C * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₁ n) ^ 2 * (2 * n))
          * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₂ n) ^ 2 * (2 * n))
        ≤ C * Real.sqrt (2 * Λ2) * (W * Real.sqrt (2 * Λ2)) := by
          refine mul_le_mul ?_ hs2 (Real.sqrt_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hs1 hC
      _ = C * W * (Real.sqrt (2 * Λ2) * Real.sqrt (2 * Λ2)) := by ring
      _ = 2 * C * W * Λ2 := by rw [hsq]; ring
  · calc C * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₂ n) ^ 2 * (2 * n))
          * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₁ n) ^ 2 * (2 * n))
        ≤ C * (W * Real.sqrt (2 * Λ2)) * Real.sqrt (2 * Λ2) := by
          refine mul_le_mul ?_ hs1 (Real.sqrt_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hs2 hC
      _ = C * W * (Real.sqrt (2 * Λ2) * Real.sqrt (2 * Λ2)) := by ring
      _ = 2 * C * W * Λ2 := by rw [hsq]; ring

end MVPh

/-! ## The decomposition 𝓜[P_{X,c}, P_{X,c}] = 𝒟 + 𝒪₁ + 𝒪₂, weighted and phased -/

section Decomp
variable {Φ : ℝ → ℝ} {T : ℝ}

/-- [eq:MPP] for P_{X,c} (mirror of Mform_PX_PX): with weights a_k‖c k‖ and phases arg(c k). -/
lemma Mform_PXc_PXc (hT : 0 ≤ T) (hΦ : Continuous Φ) (c : ℕ → ℂ) (X : ℝ) :
    Mform Φ T (PXc c X) (PXc c X)
      = (1 / (2 * π ^ 2)) *
        ((∑ n ∈ primeRange X, (acoef n * ‖c n‖) ^ 2 * Aminus Φ T (Real.log n) (Real.log n))
          + (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
              (if n = m then (0:ℝ) else (acoef n * ‖c n‖) * (acoef m * ‖c m‖)
                * AminusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg))
          + ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
              (acoef n * ‖c n‖) * (acoef m * ‖c m‖)
                * AplusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg) := by
  have h1 : Mform Φ T (PXc c X) (PXc c X) = (1 / π ^ 2) *
      ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (acoef n * ‖c n‖) * (acoef m * ‖c m‖) *
        Mform Φ T (fun τ => Real.cos (τ * Real.log n - (c n).arg))
          (fun τ => Real.cos (τ * Real.log m - (c m).arg)) := by
    unfold Mform
    have hpt : ∀ q : ℝ × ℝ, Φ (q.1 - q.2) ^ 2 * PXc c X q.1 * PXc c X q.2
        = (1 / π ^ 2) * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
            (acoef n * ‖c n‖) * (acoef m * ‖c m‖) *
            (Φ (q.1 - q.2) ^ 2 * Real.cos (q.1 * Real.log n - (c n).arg)
              * Real.cos (q.2 * Real.log m - (c m).arg)) := by
      intro q
      rw [PXc_eq_sum, PXc_eq_sum]
      rw [show ∀ A B : ℝ, Φ (q.1 - q.2) ^ 2 * (-(1 / π) * A) * (-(1 / π) * B)
          = (1 / π ^ 2) * (Φ (q.1 - q.2) ^ 2 * (A * B)) from fun A B => by ring,
        Finset.sum_mul_sum, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    simp_rw [hpt]
    rw [integral_const_mul]
    congr 1
    have hint : ∀ n m : ℕ, Integrable (fun q : ℝ × ℝ =>
        (acoef n * ‖c n‖) * (acoef m * ‖c m‖) *
        (Φ (q.1 - q.2) ^ 2 * Real.cos (q.1 * Real.log n - (c n).arg)
          * Real.cos (q.2 * Real.log m - (c m).arg)))
        (volume.restrict (Icc T (2 * T) ×ˢ Icc T (2 * T))) := fun n m =>
      (Mform_integrableOn hΦ (u := fun τ => Real.cos (τ * Real.log n - (c n).arg))
        (v := fun τ => Real.cos (τ * Real.log m - (c m).arg)) (by fun_prop) (by fun_prop)).const_mul _
    rw [integral_finsetSum _ (fun n _ => integrable_finsetSum _ (fun m _ => hint n m))]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_finsetSum _ (fun m _ => hint n m)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_const_mul]
  have h2 : ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (acoef n * ‖c n‖) * (acoef m * ‖c m‖) *
        Mform Φ T (fun τ => Real.cos (τ * Real.log n - (c n).arg))
          (fun τ => Real.cos (τ * Real.log m - (c m).arg))
      = (1 / 2) * ((∑ n ∈ primeRange X, (acoef n * ‖c n‖) ^ 2 * Aminus Φ T (Real.log n) (Real.log n))
          + (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
              (if n = m then (0:ℝ) else (acoef n * ‖c n‖) * (acoef m * ‖c m‖)
                * AminusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg))
          + ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
              (acoef n * ‖c n‖) * (acoef m * ‖c m‖)
                * AplusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg) := by
    simp_rw [Mform_cos_cos_ph hT hΦ]
    have e : ∀ n m : ℕ, (acoef n * ‖c n‖) * (acoef m * ‖c m‖) *
        ((AminusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg
          + AplusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg) / 2)
        = (1 / 2) * ((acoef n * ‖c n‖) * (acoef m * ‖c m‖)
            * AminusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg)
          + (1 / 2) * ((acoef n * ‖c n‖) * (acoef m * ‖c m‖)
            * AplusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg) := by
      intro n m; ring
    simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hA := sum_sum_eq_diag_add_offdiag (primeRange X)
      (fun n m => (acoef n * ‖c n‖) * (acoef m * ‖c m‖)
        * AminusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg)
    have hdiag : ∑ n ∈ primeRange X, (acoef n * ‖c n‖) * (acoef n * ‖c n‖)
        * AminusPh Φ T (Real.log n) (Real.log n) (c n).arg (c n).arg
        = ∑ n ∈ primeRange X, (acoef n * ‖c n‖) ^ 2 * Aminus Φ T (Real.log n) (Real.log n) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [AminusPh_self]
      ring
    rw [hA, hdiag]
    ring
  rw [h1, h2]
  ring

end Decomp

/-! ## The three estimates, weighted and phased -/

section Estimates
variable {Φ : ℝ → ℝ} {T : ℝ}

/-- 𝒟 for P_{X,c} (mirror of diag_estimate; weight ‖c n‖² ≤ 1 rides along). -/
lemma diag_estimate_chi (hT : 0 ≤ T) (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2)
    (hΦabs : Integrable fun x => Φ x ^ 2 * |x|) {g : ℝ → ℝ}
    (hFT : ∀ y, ∫ x, Φ x ^ 2 * Real.cos (x * y) = 2 * π * g y) (hc1 : ∀ n, ‖c n‖ ≤ 1) (X : ℝ) :
    |(1 / (2 * π ^ 2)) * (∑ n ∈ primeRange X, (acoef n * ‖c n‖) ^ 2 * Aminus Φ T (Real.log n) (Real.log n))
        - T / π * ∑ n ∈ primeRange X, acoef n ^ 2 * ‖c n‖ ^ 2 * g (Real.log n)|
      ≤ (1 / (2 * π ^ 2)) * (∑ n ∈ primeRange X, acoef n ^ 2) * ∫ x, Φ x ^ 2 * |x| := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  have e : (1 / (2 * π ^ 2)) * (∑ n ∈ primeRange X, (acoef n * ‖c n‖) ^ 2 * Aminus Φ T (Real.log n) (Real.log n))
        - T / π * ∑ n ∈ primeRange X, acoef n ^ 2 * ‖c n‖ ^ 2 * g (Real.log n)
      = (1 / (2 * π ^ 2)) * ∑ n ∈ primeRange X, (acoef n * ‖c n‖) ^ 2 *
          (Aminus Φ T (Real.log n) (Real.log n) - T * ∫ x, Φ x ^ 2 * Real.cos (x * Real.log n)) := by
    simp_rw [hFT]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_pow]
    field_simp
  rw [e, abs_mul, abs_of_pos (by positivity), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc |∑ n ∈ primeRange X, (acoef n * ‖c n‖) ^ 2 *
          (Aminus Φ T (Real.log n) (Real.log n) - T * ∫ x, Φ x ^ 2 * Real.cos (x * Real.log n))|
      ≤ ∑ n ∈ primeRange X, |(acoef n * ‖c n‖) ^ 2 *
          (Aminus Φ T (Real.log n) (Real.log n) - T * ∫ x, Φ x ^ 2 * Real.cos (x * Real.log n))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ primeRange X, acoef n ^ 2 * ∫ x, Φ x ^ 2 * |x| := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        calc (acoef n * ‖c n‖) ^ 2 *
              |Aminus Φ T (Real.log n) (Real.log n) - T * ∫ x, Φ x ^ 2 * Real.cos (x * Real.log n)|
            ≤ acoef n ^ 2 * |Aminus Φ T (Real.log n) (Real.log n)
                - T * ∫ x, Φ x ^ 2 * Real.cos (x * Real.log n)| := by
              apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
              rw [mul_pow]
              calc acoef n ^ 2 * ‖c n‖ ^ 2 ≤ acoef n ^ 2 * 1 ^ 2 := by
                    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
                    exact pow_le_pow_left₀ (norm_nonneg _) (hc1 n) 2
                _ = acoef n ^ 2 := by ring
          _ ≤ acoef n ^ 2 * ∫ x, Φ x ^ 2 * |x| :=
              mul_le_mul_of_nonneg_left (abs_Aminus_diag_sub_le hT hΦ hΦ2 hΦabs _) (sq_nonneg _)
    _ = (∑ n ∈ primeRange X, acoef n ^ 2) * ∫ x, Φ x ^ 2 * |x| := by rw [Finset.sum_mul]

/-- 𝒪₂ for P_{X,c} (mirror of O2_estimate; weights ≤ 1, phase-free bound). -/
lemma O2_estimate_chi (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2)
    (hc1 : ∀ n, ‖c n‖ ≤ 1) (X T : ℝ) :
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (acoef n * ‖c n‖) * (acoef m * ‖c m‖)
        * AplusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg|
      ≤ (∫ x, Φ x ^ 2) / Real.log 2 * (∑ n ∈ primeRange X, acoef n) ^ 2 := by
  have hW : 0 ≤ ∫ x, Φ x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hper : ∀ n ∈ primeRange X, ∀ m ∈ primeRange X,
      |(acoef n * ‖c n‖) * (acoef m * ‖c m‖)
          * AplusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg|
        ≤ acoef n * acoef m * ((∫ x, Φ x ^ 2) / Real.log 2) := by
    intro n hn m hm
    rw [abs_mul, abs_mul, abs_of_nonneg (mul_nonneg (acoef_nonneg n) (norm_nonneg _)),
      abs_of_nonneg (mul_nonneg (acoef_nonneg m) (norm_nonneg _))]
    rcases acoef_eq_zero_or_two_le hn with h0 | hn2
    · simp [h0]
    rcases acoef_eq_zero_or_two_le hm with h0 | hm2
    · simp [h0]
    have hwn : acoef n * ‖c n‖ ≤ acoef n := by
      calc acoef n * ‖c n‖ ≤ acoef n * 1 := mul_le_mul_of_nonneg_left (hc1 n) (acoef_nonneg n)
        _ = acoef n := mul_one _
    have hwm : acoef m * ‖c m‖ ≤ acoef m := by
      calc acoef m * ‖c m‖ ≤ acoef m * 1 := mul_le_mul_of_nonneg_left (hc1 m) (acoef_nonneg m)
        _ = acoef m := mul_one _
    have hyn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
    have hym : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast hm2)
    have hpos : 0 < Real.log n + Real.log m := by linarith
    have hA : |AplusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg|
        ≤ (∫ x, Φ x ^ 2) / Real.log 2 := by
      calc |AplusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg|
          ≤ 2 / (Real.log n + Real.log m) * ∫ x, Φ x ^ 2 := abs_AplusPh_le hΦ hΦ2 hpos _ _
        _ ≤ 2 / (2 * Real.log 2) * ∫ x, Φ x ^ 2 := by gcongr; linarith
        _ = (∫ x, Φ x ^ 2) / Real.log 2 := by field_simp
    exact mul_le_mul (mul_le_mul hwn hwm (mul_nonneg (acoef_nonneg m) (norm_nonneg _))
      (acoef_nonneg n)) hA (abs_nonneg _) (mul_nonneg (acoef_nonneg n) (acoef_nonneg m))
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun n _ => Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => hper n hn m hm) ?_
  refine le_of_eq ?_
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

end Estimates

/-! ## 𝒪₁ for P_{X,c} -/

section O1Chi
variable {Φ : ℝ → ℝ} {T : ℝ}

/-- 𝒪₁ for P_{X,c} (mirror of O1_bound; weights a_k‖c k‖ ≤ a_k, phases arg(c k) ride into
MV_real_ph): |Σ_{n≠m} w_n w_m A⁻_ph| ≤ 16·C·(∫Φ²)·ΣΛ². -/
theorem O1_bound_chi {C : ℝ} (hMV : Zeta23.MVHilbert C) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2) (hc1 : ∀ n, ‖c n‖ ≤ 1) (X : ℝ) :
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        (if n = m then (0:ℝ) else (acoef n * ‖c n‖) * (acoef m * ‖c m‖)
          * AminusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg)|
      ≤ 16 * C * (∫ x, Φ x ^ 2) * ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 := by
  set W : ℝ := ∫ x, Φ x ^ 2 with hW
  have hW0 : 0 ≤ W := MeasureTheory.integral_nonneg fun x => sq_nonneg _
  set Λ2 : ℝ := ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 with hΛ2
  have hΛ2nn : 0 ≤ Λ2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  set S1 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    acoef n * (‖c n‖ * Cm Φ T (Real.log n)) * (acoef m * ‖c m‖)
      * Real.sin ((2 * T) * (Real.log n - Real.log m) - ((c n).arg - (c m).arg)) / (Real.log n - Real.log m)) with hS1
  set S2 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    acoef n * (‖c n‖ * Sm Φ T (Real.log n)) * (acoef m * ‖c m‖)
      * Real.cos ((2 * T) * (Real.log n - Real.log m) - ((c n).arg - (c m).arg)) / (Real.log n - Real.log m)) with hS2
  set S3 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    acoef n * ‖c n‖ * (acoef m * (‖c m‖ * Cm Φ T (Real.log m)))
      * Real.sin (T * (Real.log n - Real.log m) - ((c n).arg - (c m).arg)) / (Real.log n - Real.log m)) with hS3
  set S4 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    acoef n * ‖c n‖ * (acoef m * (‖c m‖ * Sm Φ T (Real.log m)))
      * Real.cos (T * (Real.log n - Real.log m) - ((c n).arg - (c m).arg)) / (Real.log n - Real.log m)) with hS4
  set S5 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    acoef n * ‖c n‖ * (acoef m * (‖c m‖ * Cp Φ T (Real.log m)))
      * Real.sin ((2 * T) * (Real.log n - Real.log m) - ((c n).arg - (c m).arg)) / (Real.log n - Real.log m)) with hS5
  set S6 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    acoef n * ‖c n‖ * (acoef m * (‖c m‖ * Sp Φ T (Real.log m)))
      * Real.cos ((2 * T) * (Real.log n - Real.log m) - ((c n).arg - (c m).arg)) / (Real.log n - Real.log m)) with hS6
  set S7 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    acoef n * (‖c n‖ * Cp Φ T (Real.log n)) * (acoef m * ‖c m‖)
      * Real.sin (T * (Real.log n - Real.log m) - ((c n).arg - (c m).arg)) / (Real.log n - Real.log m)) with hS7
  set S8 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    acoef n * (‖c n‖ * Sp Φ T (Real.log n)) * (acoef m * ‖c m‖)
      * Real.cos (T * (Real.log n - Real.log m) - ((c n).arg - (c m).arg)) / (Real.log n - Real.log m)) with hS8
  have hsplit : ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
      (if n = m then (0:ℝ) else (acoef n * ‖c n‖) * (acoef m * ‖c m‖)
        * AminusPh Φ T (Real.log n) (Real.log m) ((c n).arg) ((c m).arg))
      = S1 + S2 - S3 - S4 + S5 + S6 - S7 - S8 := by
    rw [hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => ?_
    by_cases hnm : n = m
    · simp [hnm]
    · simp only [if_neg hnm]
      have hθ : Real.log n - Real.log m ≠ 0 := by
        have hn1 := one_le_of_mem_primeRange hn
        have hm1 := one_le_of_mem_primeRange hm
        have hinj : Real.log n ≠ Real.log m := by
          rcases lt_or_gt_of_ne hnm with hlt | hgt
          · exact ne_of_lt (Real.log_lt_log (by exact_mod_cast hn1) (by exact_mod_cast hlt))
          · exact ne_of_gt (Real.log_lt_log (by exact_mod_cast hm1) (by exact_mod_cast hgt))
        exact sub_ne_zero.mpr hinj
      have hA := sub_mul_AminusPh_eq (Φ := Φ) hT hΦ hθ ((c n).arg) ((c m).arg)
      have hAm : AminusPh Φ T (Real.log n) (Real.log m) ((c n).arg) ((c m).arg)
          = ((Real.sin ((Real.log n - Real.log m) * (2 * T) - ((c n).arg - (c m).arg)) * Cm Φ T (Real.log n)
              + Real.cos ((Real.log n - Real.log m) * (2 * T) - ((c n).arg - (c m).arg)) * Sm Φ T (Real.log n)
              - (Real.sin ((Real.log n - Real.log m) * T - ((c n).arg - (c m).arg)) * Cm Φ T (Real.log m)
                + Real.cos ((Real.log n - Real.log m) * T - ((c n).arg - (c m).arg)) * Sm Φ T (Real.log m)))
            + (Real.sin ((Real.log n - Real.log m) * (2 * T) - ((c n).arg - (c m).arg)) * Cp Φ T (Real.log m)
              + Real.cos ((Real.log n - Real.log m) * (2 * T) - ((c n).arg - (c m).arg)) * Sp Φ T (Real.log m)
              - (Real.sin ((Real.log n - Real.log m) * T - ((c n).arg - (c m).arg)) * Cp Φ T (Real.log n)
                + Real.cos ((Real.log n - Real.log m) * T - ((c n).arg - (c m).arg)) * Sp Φ T (Real.log n))))
            / (Real.log n - Real.log m) := by
        rw [eq_div_iff hθ, mul_comm]
        exact hA
      rw [hAm, mul_comm ((2 : ℝ) * T) (Real.log n - Real.log m),
        mul_comm T (Real.log n - Real.log m)]
      field_simp
      ring
  have hb : ∀ (M : ℕ → ℝ), (∀ n ∈ primeRange X, |M n| ≤ W) →
      (∀ n ∈ primeRange X, |‖c n‖ * M n| ≤ W) := by
    intro M hM n hn
    rw [abs_mul, abs_of_nonneg (norm_nonneg _)]
    calc ‖c n‖ * |M n| ≤ 1 * W := by
          apply mul_le_mul (hc1 n) (hM n hn) (abs_nonneg _) zero_le_one
      _ = W := one_mul _
  have hc1' : ∀ n ∈ primeRange X, |(‖c n‖ : ℝ)| ≤ 1 := by
    intro n _
    rw [abs_of_nonneg (norm_nonneg _)]
    exact hc1 n
  have hw_Cm : ∀ n ∈ primeRange X, |Cm Φ T (Real.log n)| ≤ W := fun n _ => abs_Cm_le hT hΦ hΦ2 _
  have hw_Sm : ∀ n ∈ primeRange X, |Sm Φ T (Real.log n)| ≤ W := fun n _ => abs_Sm_le hT hΦ hΦ2 _
  have hw_Cp : ∀ n ∈ primeRange X, |Cp Φ T (Real.log n)| ≤ W := fun n _ => abs_Cp_le hT hΦ hΦ2 _
  have hw_Sp : ∀ n ∈ primeRange X, |Sp Φ T (Real.log n)| ≤ W := fun n _ => abs_Sp_le hT hΦ hΦ2 _
  have hb1 : |S1| ≤ 2 * C * W * Λ2 := by
    rw [hS1]
    have h := (MV_real_ph hMV X (2 * T) (fun k => acoef k * (‖c k‖ * Cm Φ T (Real.log k))) (fun k => acoef k * ‖c k‖) (fun k => (c k).arg)).2
    have hsz := (MV_size_le₂ hC X hW0 hc1' (hb _ hw_Cm)).2
    have hfin := h.trans hsz
    rw [← hΛ2] at hfin
    exact hfin
  have hb2 : |S2| ≤ 2 * C * W * Λ2 := by
    rw [hS2]
    have h := (MV_real_ph hMV X (2 * T) (fun k => acoef k * (‖c k‖ * Sm Φ T (Real.log k))) (fun k => acoef k * ‖c k‖) (fun k => (c k).arg)).1
    have hsz := (MV_size_le₂ hC X hW0 hc1' (hb _ hw_Sm)).2
    have hfin := h.trans hsz
    rw [← hΛ2] at hfin
    exact hfin
  have hb3 : |S3| ≤ 2 * C * W * Λ2 := by
    rw [hS3]
    have h := (MV_real_ph hMV X (T) (fun k => acoef k * ‖c k‖) (fun k => acoef k * (‖c k‖ * Cm Φ T (Real.log k))) (fun k => (c k).arg)).2
    have hsz := (MV_size_le₂ hC X hW0 hc1' (hb _ hw_Cm)).1
    have hfin := h.trans hsz
    rw [← hΛ2] at hfin
    exact hfin
  have hb4 : |S4| ≤ 2 * C * W * Λ2 := by
    rw [hS4]
    have h := (MV_real_ph hMV X (T) (fun k => acoef k * ‖c k‖) (fun k => acoef k * (‖c k‖ * Sm Φ T (Real.log k))) (fun k => (c k).arg)).1
    have hsz := (MV_size_le₂ hC X hW0 hc1' (hb _ hw_Sm)).1
    have hfin := h.trans hsz
    rw [← hΛ2] at hfin
    exact hfin
  have hb5 : |S5| ≤ 2 * C * W * Λ2 := by
    rw [hS5]
    have h := (MV_real_ph hMV X (2 * T) (fun k => acoef k * ‖c k‖) (fun k => acoef k * (‖c k‖ * Cp Φ T (Real.log k))) (fun k => (c k).arg)).2
    have hsz := (MV_size_le₂ hC X hW0 hc1' (hb _ hw_Cp)).1
    have hfin := h.trans hsz
    rw [← hΛ2] at hfin
    exact hfin
  have hb6 : |S6| ≤ 2 * C * W * Λ2 := by
    rw [hS6]
    have h := (MV_real_ph hMV X (2 * T) (fun k => acoef k * ‖c k‖) (fun k => acoef k * (‖c k‖ * Sp Φ T (Real.log k))) (fun k => (c k).arg)).1
    have hsz := (MV_size_le₂ hC X hW0 hc1' (hb _ hw_Sp)).1
    have hfin := h.trans hsz
    rw [← hΛ2] at hfin
    exact hfin
  have hb7 : |S7| ≤ 2 * C * W * Λ2 := by
    rw [hS7]
    have h := (MV_real_ph hMV X (T) (fun k => acoef k * (‖c k‖ * Cp Φ T (Real.log k))) (fun k => acoef k * ‖c k‖) (fun k => (c k).arg)).2
    have hsz := (MV_size_le₂ hC X hW0 hc1' (hb _ hw_Cp)).2
    have hfin := h.trans hsz
    rw [← hΛ2] at hfin
    exact hfin
  have hb8 : |S8| ≤ 2 * C * W * Λ2 := by
    rw [hS8]
    have h := (MV_real_ph hMV X (T) (fun k => acoef k * (‖c k‖ * Sp Φ T (Real.log k))) (fun k => acoef k * ‖c k‖) (fun k => (c k).arg)).1
    have hsz := (MV_size_le₂ hC X hW0 hc1' (hb _ hw_Sp)).2
    have hfin := h.trans hsz
    rw [← hΛ2] at hfin
    exact hfin
  rw [hsplit]
  have habs : |S1 + S2 - S3 - S4 + S5 + S6 - S7 - S8|
      ≤ |S1| + |S2| + |S3| + |S4| + |S5| + |S6| + |S7| + |S8| := by
    have t1 := abs_add_le S1 S2
    have t2 := abs_sub (S1 + S2) S3
    have t3 := abs_sub (S1 + S2 - S3) S4
    have t4 := abs_add_le (S1 + S2 - S3 - S4) S5
    have t5 := abs_add_le (S1 + S2 - S3 - S4 + S5) S6
    have t6 := abs_sub (S1 + S2 - S3 - S4 + S5 + S6) S7
    have t7 := abs_sub (S1 + S2 - S3 - S4 + S5 + S6 - S7) S8
    linarith
  calc |S1 + S2 - S3 - S4 + S5 + S6 - S7 - S8|
      ≤ |S1| + |S2| + |S3| + |S4| + |S5| + |S6| + |S7| + |S8| := habs
    _ ≤ 8 * (2 * C * W * Λ2) := by linarith
    _ = 16 * C * W * Λ2 := by ring

end O1Chi

/-! ## The coprime g-sandwich (§5.4 with [eq:cheb2] restricted to (n,q)=1) -/

section SandwichChi
variable {p : Setting} {F : LocalFun}

/-- Upper half, over the window-generic Core layer (uses only g ≤ A_φ ≤ (L−|y|)₊). -/
theorem sumA2gCoprime_upper (hchebq : ChebyshevMertensCoprime q) (_hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      sumA2gCoprime q p.X F.g ≤ p.L ^ 3 / 6 + C * p.L ^ 2) := by
  obtain ⟨C, hC⟩ := hchebq.cheb2b
  refine ⟨C, 0, fun p F _ _ hF => ?_⟩
  have hX1 : (1:ℝ) ≤ p.X := by linarith [hF.two_le_X]
  have h1 : sumA2gCoprime q p.X F.g
      ≤ ∑ n ∈ (Finset.Ioc 0 ⌊p.X⌋₊).filter (fun n => Nat.Coprime n q),
          (Λ n : ℝ) ^ 2 / n * (p.L - Real.log n) := by
    unfold sumA2gCoprime
    refine Finset.sum_le_sum fun n hn => ?_
    have hn' : n ∈ primeRange p.X := (Finset.mem_filter.mp hn).1
    refine mul_le_mul_of_nonneg_left ?_ (a2_nonneg n)
    calc F.g (Real.log n) ≤ F.Aphi (Real.log n) := hF.g_le_Aphi _
      _ ≤ max (p.L - |Real.log n|) 0 := hF.Aphi_le _
      _ = p.L - Real.log n := by
          rw [abs_of_nonneg (log_nonneg_of_mem_primeRange hn'), max_eq_left]
          have := log_le_of_mem_primeRange hX1 hn'
          rw [p.log_X] at this; linarith
  have h2 := hC p.X hF.two_le_X
  rw [p.log_X] at h2
  have h3 := (abs_le.mp h2).2
  linarith

/-- Lower half, over the FULL taper layer (needs the flat-top bound g_lower, absent from Core). -/
theorem sumA2gCoprime_lower (hchebq : ChebyshevMertensCoprime q) (_hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAt cϱ lam (fun p F =>
      (p.L - 2 * p.w) ^ 3 / 6 - C * p.L ^ 2 ≤ sumA2gCoprime q p.X F.g) := by
  obtain ⟨C, hC⟩ := hchebq.cheb2b
  refine ⟨max C 0, 0, fun p F _ _ hF => ?_⟩
  set L' := p.L - 2 * p.w with hL'
  set x' := Real.exp L' with hx'
  have hL'pos : 6 ≤ L' := by have := hF.w_le; have := hF.eight_le_L; rw [hL']; linarith
  have hL'le : L' ≤ p.L := by rw [hL']; linarith [hF.one_le_w]
  have hx'2 : 2 ≤ x' := by linarith [Real.add_one_le_exp L']
  have hx'X : x' ≤ p.X := Real.exp_le_exp.mpr hL'le
  have hlogx' : Real.log x' = L' := Real.log_exp _
  have hsub : (Finset.Ioc 0 ⌊x'⌋₊).filter (fun n => Nat.Coprime n q)
      ⊆ (Finset.Ioc 0 ⌊p.X⌋₊).filter (fun n => Nat.Coprime n q) :=
    Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right (Nat.floor_le_floor hx'X))
  have h1 : ∑ n ∈ (Finset.Ioc 0 ⌊x'⌋₊).filter (fun n => Nat.Coprime n q),
      (Λ n : ℝ) ^ 2 / n * (Real.log x' - Real.log n) ≤ sumA2gCoprime q p.X F.g := by
    unfold sumA2gCoprime
    calc ∑ n ∈ (Finset.Ioc 0 ⌊x'⌋₊).filter (fun n => Nat.Coprime n q),
          (Λ n : ℝ) ^ 2 / n * (Real.log x' - Real.log n)
        ≤ ∑ n ∈ (Finset.Ioc 0 ⌊x'⌋₊).filter (fun n => Nat.Coprime n q),
            (Λ n : ℝ) ^ 2 / n * F.g (Real.log n) := by
          refine Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left ?_ (a2_nonneg n)
          have hn' : n ∈ primeRange x' := (Finset.mem_filter.mp hn).1
          calc Real.log x' - Real.log n ≤ max (p.L - 2 * p.w - |Real.log n|) 0 := by
                rw [hlogx', abs_of_nonneg (log_nonneg_of_mem_primeRange hn'), hL']
                exact le_max_left _ _
            _ ≤ F.g (Real.log n) := hF.g_lower _
      _ ≤ ∑ n ∈ (Finset.Ioc 0 ⌊p.X⌋₊).filter (fun n => Nat.Coprime n q),
            (Λ n : ℝ) ^ 2 / n * F.g (Real.log n) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro n _ _
          have : 0 ≤ F.g (Real.log n) := le_trans (le_max_right _ _) (hF.g_lower _)
          exact mul_nonneg (a2_nonneg n) this
  have h2 := hC x' hx'2
  rw [hlogx'] at h2
  have h3 := (abs_le.mp h2).1
  have hCmax : C * L' ^ 2 ≤ max C 0 * p.L ^ 2 := by
    calc C * L' ^ 2 ≤ max C 0 * L' ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
      _ ≤ max C 0 * p.L ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
          exact pow_le_pow_left₀ (by linarith) hL'le 2
  rw [hlogx'] at h1
  linarith

end SandwichChi

/-! ## Assembly: [prop:PP] for L(s,chi) -/

section Results

/-- **prop_PP_chi, q-uniform form** (hybrid range, [rem:otherL](i)): the same constant and
threshold for every modulus and unimodular coefficient sequence — the ∃ C T₀ sit outside (q, c).
(The constant does not depend on (q, c); unimodularity enters only through the norm bound and the
diagonal identity.  `prop_PP_chi` below is the (q, c)-specialisation of this theorem.) -/
theorem prop_PP_chi_uniform (hcheb : Zeta23.ChebyshevMertens) (hMV : ∃ C : ℝ, 0 < C ∧ Zeta23.MVHilbert C)
    (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C T₀ : ℝ, ∀ (q : ℕ) (c : ℕ → ℂ), CoeffUnimodular q c →
      ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₀ ≤ p.T → LocalHypsCore cϱ p F →
      |Mform F.Phi p.T (PXc c p.X) (PXc c p.X) - p.T / π * sumA2gCoprime q p.X F.g|
        ≤ C * (p.L ^ 2 * p.X) := by
  obtain ⟨CMV, hCMV, hMV⟩ := hMV
  obtain ⟨x₀, h1b⟩ := hcheb.cheb1b
  obtain ⟨C1d, h1d⟩ := hcheb.cheb1d
  obtain ⟨C2a, h2a⟩ := hcheb.cheb2a
  refine ⟨(1 / (2 * π ^ 2)) * ((1 / 2 + |C2a|) * (8 + 8 * |cϱ|) + 16 * CMV * (2 * π) * |C1d|
      + 2 * π / Real.log 2 * 9),
    max (2 * π * Real.exp (|x₀| / lam)) 1, fun q c hc p F hplam hT hF => ?_⟩
  have hc1 : ∀ n, ‖c n‖ ≤ 1 := hc.toCoeffOK.norm_le
  have hT1 : 1 ≤ p.T := le_trans (le_max_right _ _) hT
  have hT0 : 0 ≤ p.T := by linarith
  have hX0 : x₀ ≤ p.X := Setting.le_X_of_T (hplam ▸ hlam.1)
    (by rw [hplam]; exact (le_max_left _ _).trans hT)
  have hX2 : 2 ≤ p.X := hF.two_le_X
  have hL8 : 8 ≤ p.L := hF.eight_le_L
  have hL1 : 1 ≤ p.L := by linarith
  have hLX : p.L ≤ p.X := hF.L_le_X
  have hlogX : Real.log p.X = p.L := p.log_X
  have hΦc : Continuous F.Phi := hF.Phi_contDiff.continuous
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set W := ∫ x, F.Phi x ^ 2 with hWdef
  have hW0 : 0 ≤ W := integral_nonneg fun x => sq_nonneg _
  have hWle : W ≤ 2 * π * p.L := hF.integral_Phi_sq_le
  set ΛΦ := ∫ x, F.Phi x ^ 2 * |x| with hΛΦdef
  have hΛΦ0 : 0 ≤ ΛΦ := integral_nonneg fun x => mul_nonneg (sq_nonneg _) (abs_nonneg _)
  have hΛΦle : ΛΦ ≤ (8 + 8 * |cϱ|) * p.L := by
    have h1 := hF.integral_Phi_sq_mul_abs_le
    have hcϱ : 4 ≤ cϱ := hF.four_le_cϱ
    have hw : 1 ≤ p.w := hF.one_le_w
    have harg : 0 < cϱ * p.L / (4 * p.w) := by positivity
    have hlog : Real.log (cϱ * p.L / (4 * p.w)) ≤ cϱ * p.L / (4 * p.w) := by
      linarith [Real.log_le_sub_one_of_pos harg]
    have hfrac : cϱ * p.L / (4 * p.w) ≤ |cϱ| * p.L := by
      rw [div_le_iff₀ (by positivity), abs_of_nonneg (by linarith)]
      have hcL : 0 ≤ cϱ * p.L := mul_nonneg (by linarith) (by linarith)
      nlinarith [mul_nonneg hcL (by linarith : (0:ℝ) ≤ 4 * p.w - 1)]
    calc ΛΦ ≤ 8 + 8 * Real.log (cϱ * p.L / (4 * p.w)) := h1
      _ ≤ 8 + 8 * (|cϱ| * p.L) := by linarith
      _ ≤ 8 * p.L + 8 * (|cϱ| * p.L) := by linarith
      _ = (8 + 8 * |cϱ|) * p.L := by ring
  have hsuma : ∑ n ∈ primeRange p.X, acoef n ≤ 3 * Real.sqrt p.X := h1b p.X hX0
  have hsuma0 : 0 ≤ ∑ n ∈ primeRange p.X, acoef n := Finset.sum_nonneg fun n _ => acoef_nonneg n
  have hsumΛ2 : ∑ n ∈ primeRange p.X, (Λ n : ℝ) ^ 2 ≤ |C1d| * p.X * p.L := by
    have h := h1d p.X hX2
    rw [hlogX] at h
    refine h.trans ?_
    have hXL : 0 ≤ p.X * p.L := mul_nonneg (by linarith) (by linarith)
    calc C1d * p.X * p.L = C1d * (p.X * p.L) := by ring
      _ ≤ |C1d| * (p.X * p.L) := mul_le_mul_of_nonneg_right (le_abs_self _) hXL
      _ = |C1d| * p.X * p.L := by ring
  have hsuma2 : ∑ n ∈ primeRange p.X, acoef n ^ 2 ≤ (1 / 2 + |C2a|) * p.L ^ 2 := by
    have h := h2a p.X hX2
    rw [hlogX] at h
    simp_rw [acoef_sq]
    have h3 := (abs_le.mp h).2
    unfold primeRange
    calc ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Λ n : ℝ) ^ 2 / n ≤ p.L ^ 2 / 2 + C2a * p.L := by linarith
      _ ≤ p.L ^ 2 / 2 + |C2a| * p.L ^ 2 := by
          have h4 : C2a * p.L ≤ |C2a| * p.L := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
          have h5 : |C2a| * p.L ≤ |C2a| * p.L ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); nlinarith
          linarith
      _ = (1 / 2 + |C2a|) * p.L ^ 2 := by ring
  have hD := diag_estimate_chi hT0 hΦc hF.Phi_sq_integrable hF.Phi_sq_mul_abs_integrable
    hF.Phi_sq_fourier hc1 p.X
  have hO1 := O1_bound_chi (c := c) hMV hCMV.le hT0 hΦc hF.Phi_sq_integrable hc1 p.X
  have hO2 := O2_estimate_chi (c := c) hΦc hF.Phi_sq_integrable hc1 p.X p.T
  rw [Mform_PXc_PXc hT0 hΦc, ← sum_w_eq_sumA2gCoprime hc p.X F.g]
  set D := ∑ n ∈ primeRange p.X, (acoef n * ‖c n‖) ^ 2 * Aminus F.Phi p.T (Real.log n) (Real.log n)
  set O1 := ∑ n ∈ primeRange p.X, ∑ m ∈ primeRange p.X,
    (if n = m then (0:ℝ) else (acoef n * ‖c n‖) * (acoef m * ‖c m‖)
      * AminusPh F.Phi p.T (Real.log n) (Real.log m) (c n).arg (c m).arg)
  set O2 := ∑ n ∈ primeRange p.X, ∑ m ∈ primeRange p.X,
    (acoef n * ‖c n‖) * (acoef m * ‖c m‖)
      * AplusPh F.Phi p.T (Real.log n) (Real.log m) (c n).arg (c m).arg
  have hk : (0:ℝ) < 1 / (2 * π ^ 2) := by positivity
  have bD : |1 / (2 * π ^ 2) * D - p.T / π * ∑ n ∈ primeRange p.X, acoef n ^ 2 * ‖c n‖ ^ 2 * F.g (Real.log n)|
      ≤ 1 / (2 * π ^ 2) * ((1 / 2 + |C2a|) * (8 + 8 * |cϱ|)) * (p.L ^ 2 * p.X) := by
    refine hD.trans ?_
    rw [mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hk.le
    calc (∑ n ∈ primeRange p.X, acoef n ^ 2) * ΛΦ
        ≤ ((1 / 2 + |C2a|) * p.L ^ 2) * ((8 + 8 * |cϱ|) * p.L) := by
          apply mul_le_mul hsuma2 hΛΦle hΛΦ0 (by positivity)
      _ ≤ ((1 / 2 + |C2a|) * p.L ^ 2) * ((8 + 8 * |cϱ|) * p.X) := by gcongr
      _ = (1 / 2 + |C2a|) * (8 + 8 * |cϱ|) * (p.L ^ 2 * p.X) := by ring
  have bO1 : |1 / (2 * π ^ 2) * O1|
      ≤ 1 / (2 * π ^ 2) * (16 * CMV * (2 * π) * |C1d|) * (p.L ^ 2 * p.X) := by
    rw [abs_mul, abs_of_pos hk, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hk.le
    calc |O1| ≤ 16 * CMV * W * ∑ n ∈ primeRange p.X, (Λ n : ℝ) ^ 2 := hO1
      _ ≤ 16 * CMV * (2 * π * p.L) * (|C1d| * p.X * p.L) := by
          apply mul_le_mul _ hsumΛ2 (Finset.sum_nonneg fun n _ => sq_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hWle (by positivity)
      _ = 16 * CMV * (2 * π) * |C1d| * (p.L ^ 2 * p.X) := by ring
  have bO2 : |1 / (2 * π ^ 2) * O2| ≤ 1 / (2 * π ^ 2) * (2 * π / Real.log 2 * 9) * (p.L ^ 2 * p.X) := by
    rw [abs_mul, abs_of_pos hk, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hk.le
    calc |O2| ≤ W / Real.log 2 * (∑ n ∈ primeRange p.X, acoef n) ^ 2 := hO2
      _ ≤ (2 * π * p.L) / Real.log 2 * (3 * Real.sqrt p.X) ^ 2 := by
          apply mul_le_mul _ _ (sq_nonneg _) (by positivity)
          · exact div_le_div_of_nonneg_right hWle hlog2.le
          · exact pow_le_pow_left₀ hsuma0 hsuma 2
      _ = 2 * π / Real.log 2 * 9 * (p.L * p.X) := by
          rw [mul_pow, Real.sq_sqrt (by linarith)]; ring
      _ ≤ 2 * π / Real.log 2 * 9 * (p.L ^ 2 * p.X) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hLL : p.L ≤ p.L ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right hLL (by linarith)
  have split : 1 / (2 * π ^ 2) * (D + O1 + O2)
        - p.T / π * ∑ n ∈ primeRange p.X, acoef n ^ 2 * ‖c n‖ ^ 2 * F.g (Real.log n)
      = (1 / (2 * π ^ 2) * D - p.T / π * ∑ n ∈ primeRange p.X, acoef n ^ 2 * ‖c n‖ ^ 2 * F.g (Real.log n))
        + 1 / (2 * π ^ 2) * O1 + 1 / (2 * π ^ 2) * O2 := by ring
  rw [split]
  calc |(1 / (2 * π ^ 2) * D - p.T / π * ∑ n ∈ primeRange p.X, acoef n ^ 2 * ‖c n‖ ^ 2 * F.g (Real.log n))
        + 1 / (2 * π ^ 2) * O1 + 1 / (2 * π ^ 2) * O2|
      ≤ |1 / (2 * π ^ 2) * D - p.T / π * ∑ n ∈ primeRange p.X, acoef n ^ 2 * ‖c n‖ ^ 2 * F.g (Real.log n)|
        + |1 / (2 * π ^ 2) * O1| + |1 / (2 * π ^ 2) * O2| := abs_add_three _ _ _
    _ ≤ 1 / (2 * π ^ 2) * ((1 / 2 + |C2a|) * (8 + 8 * |cϱ|)) * (p.L ^ 2 * p.X)
        + 1 / (2 * π ^ 2) * (16 * CMV * (2 * π) * |C1d|) * (p.L ^ 2 * p.X)
        + 1 / (2 * π ^ 2) * (2 * π / Real.log 2 * 9) * (p.L ^ 2 * p.X) :=
        add_le_add (add_le_add bD bO1) bO2
    _ = (1 / (2 * π ^ 2)) * ((1 / 2 + |C2a|) * (8 + 8 * |cϱ|) + 16 * CMV * (2 * π) * |C1d|
      + 2 * π / Real.log 2 * 9) * (p.L ^ 2 * p.X) := by ring


/-- **[prop:PP] for L(s,chi)** ([thm:E] (iii)): under H-cheb + H-MV + CoeffUnimodular,
|𝓜[P_{X,c},P_{X,c}] − (T/π)·Σ_{n≤X,(n,q)=1}Λ(n)²/n·g(log n)| ≤ C·L²X for T ≥ T₀, over the
window-generic Core taper layer.
Proof: the q-uniform form `prop_PP_chi_uniform` above, specialised to (q, c) — the constant and
threshold do not depend on them. -/
theorem prop_PP_chi (hcheb : Zeta23.ChebyshevMertens) (hMV : ∃ C : ℝ, 0 < C ∧ Zeta23.MVHilbert C)
    (hc : CoeffUnimodular q c) (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |Mform F.Phi p.T (PXc c p.X) (PXc c p.X) - p.T / π * sumA2gCoprime q p.X F.g|
        ≤ C * (p.L ^ 2 * p.X)) := by
  obtain ⟨C, T₀, h⟩ := prop_PP_chi_uniform (cϱ := cϱ) hcheb hMV hlam
  exact ⟨C, T₀, fun p F hplam hT hF => h q c hc p F hplam hT hF⟩

end Results

end ThmE
end Zeta23
