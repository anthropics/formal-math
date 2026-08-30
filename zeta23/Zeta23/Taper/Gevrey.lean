/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Taper/Gevrey.lean — Gevrey-class taper profiles (items P1–P4 below).

PURPOSE.  The family / q-aspect version of the theorem (paper rem:otherL (iii): "requires a different (Gevrey-class)
taper in prop:tail") needs a profile ϱ with sup|ϱ^{(k)}| ≤ B·A^k·k^{sk} (all k ≥ 1) for some s > 1.  We fix s = 2 and the
explicit profile built from Mathlib's Real.expNegInvGlue g(x) = exp(−1/x) (x>0), 0 (x≤0):
   θ(x) := g(x)·g(1−x)   (a bump on (0,1)),      ϱ₂(x) := (∫_0^x θ) / (∫_0^1 θ).
CONTENTS (all tools exist in Mathlib):
 (P1) gevrey_expNegInvGlue : ∀ k ≥ 1, ∀ x, |iteratedDeriv k expNegInvGlue x| ≤ (18/e)^k · k^(2k).
      Route: for x > 0, expNegInvGlue =ᶠ[𝓝 x] (fun t => (G t).re) with G z := Complex.exp (−1/z) holomorphic on ℂ∖{0};
      real/complex iterated derivatives agree (induction with HasDerivAt.real_of_complex + EventuallyEq.iteratedDeriv_eq);
      Cauchy's estimate Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le on the circle |z − x| = x/2, where
      Re(1/z) = Re z/|z|² ≥ 2/(9x) so ‖G z‖ ≤ exp(−2/(9x)); then k!·(x/2)^{−k}·exp(−2/(9x)) ≤ k!·(9k/e)^k ≤ (9/e)^k k^{2k}·(k!/k^k)
      (sup_t t^k e^{−2t/9} = (9k/(2e))^k).  For x < 0 all derivatives vanish (eventually 0); x = 0 by continuity of
      iteratedDeriv k (expNegInvGlue is C^∞: Real.expNegInvGlue.contDiff).
 (P2) gevrey_mul : Leibniz (norm_iteratedFDeriv_mul_le / iteratedDeriv version): (G_s) for f,h with (A,B) ⇒ (G_s) for f·h
      with (2A, B²), using j^{sj}(k−j)^{s(k−j)} ≤ k^{sk} and Σ_j C(k,j) = 2^k.
 (P3) theta, rhoTwo : definitions; rhoTwo is a TaperProfile (monotone: θ ≥ 0; = 0 / = 1 outside (0,1); C^∞, indeed C³ as
      TaperProfile wants) and iteratedDeriv (k+1) rhoTwo = iteratedDeriv k θ / ∫θ.
 (P4) gevreyProfile_rhoTwo : GevreyProfile 2 (36/e) (2·e^8) rhoTwo   (∫_0^1 θ ≥ e^{−8}/2 since θ ≥ e^{−8} on [1/4,3/4]).
Downstream: a Gevrey tail lemma gives TailInputs with
θ₀ = η/L once (wD₀/A)^{1/2} ≥ c₁^{−1}[L/2 + log d + …]; nothing else in §2.2/§4 changes (c_ϱ finite).
-/
import Zeta23.Defs
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

namespace Zeta23
namespace Taper

open Real Complex Filter Topology Set Metric MeasureTheory intervalIntegral

/-- Gevrey-s derivative bounds in the (weaker-than-usual) form
sup|ϱ^{(k)}| ≤ B·A^k·k^{sk} for all k ≥ 1, on top of the paper's TaperProfile and C^∞. -/
structure GevreyProfile (s A B : ℝ) (ϱ : ℝ → ℝ) : Prop where
  taper : TaperProfile ϱ
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ϱ
  one_lt : 1 < s
  A_pos : 0 < A
  B_pos : 0 < B
  bound : ∀ k : ℕ, 1 ≤ k → ∀ x : ℝ, |iteratedDeriv k ϱ x| ≤ B * A ^ k * (k : ℝ) ^ (s * k)

/-- the bump θ(x) = g(x) g(1−x), g = expNegInvGlue. -/
def theta (x : ℝ) : ℝ := expNegInvGlue x * expNegInvGlue (1 - x)

/-- its primitive Θ(x) = ∫_0^x θ. -/
def Theta (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, theta t

/-- the Gevrey-2 profile ϱ₂ = normalized primitive of θ. -/
def rhoTwo (x : ℝ) : ℝ := (∫ t in (0:ℝ)..x, theta t) / ∫ t in (0:ℝ)..1, theta t

/-! ### (P1) Gevrey-2 bounds for exp(−1/x) via Cauchy's estimate -/

namespace Gevrey2

/-- holomorphic extension of exp(−1/x). -/
def G (z : ℂ) : ℂ := Complex.exp (-z⁻¹)

lemma G_differentiableOn : DifferentiableOn ℂ G {z : ℂ | z ≠ 0} := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  unfold G
  exact ((differentiableAt_inv_iff.mpr hz).neg).cexp

lemma G_analyticOnNhd : AnalyticOnNhd ℂ G {z : ℂ | z ≠ 0} :=
  G_differentiableOn.analyticOnNhd isOpen_ne

lemma Gn_hasDerivAt (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (iteratedDeriv n G) (iteratedDeriv (n + 1) G z) z := by
  have h := (G_analyticOnNhd.iterated_deriv n) z hz
  rw [iteratedDeriv_succ, iteratedDeriv_eq_iterate]
  exact h.differentiableAt.hasDerivAt

/-- real restriction. -/
def gR (t : ℝ) : ℝ := (G t).re

lemma gR_iteratedDeriv (n : ℕ) : ∀ t : ℝ, 0 < t → iteratedDeriv n gR t = (iteratedDeriv n G t).re := by
  induction n with
  | zero => intro t _; simp [gR]
  | succ n ih =>
    intro t ht
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv n gR =ᶠ[𝓝 t] fun u : ℝ => (iteratedDeriv n G (u : ℂ)).re := by
      filter_upwards [Ioi_mem_nhds ht] with u hu
      exact ih u hu
    rw [hev.deriv_eq]
    have hz : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    exact ((Gn_hasDerivAt n hz).real_of_complex).deriv

lemma expNegInvGlue_eventuallyEq_gR {x : ℝ} (hx : 0 < x) : expNegInvGlue =ᶠ[𝓝 x] gR := by
  filter_upwards [Ioi_mem_nhds hx] with t ht
  have ht' : ¬ t ≤ 0 := not_le.mpr ht
  simp only [expNegInvGlue, ht', if_false, gR, G]
  rw [show -(t : ℂ)⁻¹ = ((-t⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.exp_ofReal_re]

/-- Cauchy's estimate for G on the circle |z − x| = x/2. -/
lemma norm_iteratedDeriv_G_le (k : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedDeriv k G (x : ℂ)‖ ≤ k.factorial * Real.exp (-(2 / (9 * x))) / (x / 2) ^ k := by
  have hr : (0 : ℝ) < x / 2 := by positivity
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr
  · -- DiffContOnCl on the disc: G is differentiable on the closed disc (which misses 0)
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    refine G_differentiableOn.mono fun z hz h0 => ?_
    rw [mem_closedBall, h0, dist_comm, dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx] at hz
    linarith
  · intro z hz
    rw [mem_sphere, dist_eq_norm] at hz
    have hre : x / 2 ≤ z.re := by
      have := Complex.abs_re_le_norm (z - x)
      simp at this; rw [hz] at this; rw [abs_le] at this; linarith
    have hnorm : ‖z‖ ≤ 3 * x / 2 := by
      calc ‖z‖ = ‖(z - x) + x‖ := by ring_nf
        _ ≤ ‖z - x‖ + ‖(x : ℂ)‖ := norm_add_le _ _
        _ = 3 * x / 2 := by rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]; ring
    have hz0 : z ≠ 0 := fun h => by rw [h] at hre; simp at hre; linarith
    have hns : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
    unfold G
    rw [Complex.norm_exp, neg_re, Complex.inv_re]
    apply Real.exp_le_exp.mpr
    -- −(re/normSq) ≤ −2/(9x)  ⟸  2/(9x) ≤ re/normSq
    have hns' : Complex.normSq z ≤ (3 * x / 2) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    rw [neg_le_neg_iff, div_le_div_iff₀ (by positivity) hns]
    nlinarith

/-- elementary: u^k e^{−u} ≤ (k/e)^k for u ≥ 0, k ≥ 1. -/
lemma pow_mul_exp_neg_le (k : ℕ) (hk : 1 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    u ^ k * Real.exp (-u) ≤ ((k : ℝ) / Real.exp 1) ^ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : u / k ≤ Real.exp (u / k - 1) := by
    have := Real.add_one_le_exp (u / k - 1); linarith
  have h2 : (u / k) ^ k ≤ Real.exp (u / k - 1) ^ k := pow_le_pow_left₀ (by positivity) h1 k
  rw [← Real.exp_nat_mul, show (k : ℝ) * (u / k - 1) = u - k by field_simp] at h2
  rw [div_pow, div_le_iff₀ (by positivity)] at h2
  rw [div_pow, le_div_iff₀ (by positivity), Real.exp_one_pow]
  calc u ^ k * Real.exp (-u) * Real.exp k
      ≤ (Real.exp (u - k) * (k : ℝ) ^ k) * Real.exp (-u) * Real.exp k := by gcongr
    _ = (k : ℝ) ^ k * (Real.exp (u - k) * Real.exp (-u) * Real.exp k) := by ring
    _ = (k : ℝ) ^ k := by
        rw [← Real.exp_add, ← Real.exp_add, show u - k + -u + k = 0 by ring, Real.exp_zero, mul_one]

/-- the numeric step: k!·e^{−2/(9x)}·(x/2)^{−k} ≤ (18/e)^k k^{2k}. -/
lemma cauchy_bound_le (k : ℕ) (hk : 1 ≤ k) {x : ℝ} (hx : 0 < x) :
    k.factorial * Real.exp (-(2 / (9 * x))) / (x / 2) ^ k ≤ (18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k) := by
  set u : ℝ := 2 / (9 * x) with hu
  have hu0 : 0 ≤ u := by positivity
  have hxu : (x / 2)⁻¹ = 9 * u := by rw [hu]; field_simp
  have hkey := pow_mul_exp_neg_le k hk hu0
  have hfac : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
  rw [div_eq_mul_inv, ← inv_pow, hxu, mul_pow]
  -- k! * e^{-u} * (9^k u^k) ≤ k^k * 9^k (k/e)^k ≤ (18/e)^k k^{2k}
  have h9 : (0:ℝ) ≤ 9 ^ k := by positivity
  calc (k.factorial : ℝ) * Real.exp (-u) * ((9:ℝ) ^ k * u ^ k)
      = (k.factorial : ℝ) * (9:ℝ) ^ k * (u ^ k * Real.exp (-u)) := by ring
    _ ≤ (k : ℝ) ^ k * (9:ℝ) ^ k * (((k : ℝ) / Real.exp 1) ^ k) := by
        gcongr
    _ = (9 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k) := by rw [div_pow, div_pow, pow_mul]; ring
    _ ≤ (18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k) := by
        gcongr; norm_num

end Gevrey2

open Gevrey2 in
/-- **(P1)** Gevrey-2 bound for exp(−1/x): |g^{(k)}(x)| ≤ (18/e)^k k^{2k} for all k ≥ 1 and all real x
(Cauchy's estimate for G(z) = exp(−1/z) on the circle |z − x| = x/2, where ‖G‖ ≤ exp(−2/(9x))). -/
theorem gevrey_expNegInvGlue (k : ℕ) (hk : 1 ≤ k) (x : ℝ) :
    |iteratedDeriv k expNegInvGlue x| ≤ (18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * (k : ℝ)) := by
  have hrpow : (k : ℝ) ^ (2 * (k : ℝ)) = (k : ℝ) ^ (2 * k) := by
    rw [show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [hrpow]
  set C : ℝ := (18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k) with hC
  have hC0 : 0 ≤ C := by positivity
  -- x > 0
  have hpos : ∀ x : ℝ, 0 < x → |iteratedDeriv k expNegInvGlue x| ≤ C := by
    intro x hx
    rw [(expNegInvGlue_eventuallyEq_gR hx).iteratedDeriv_eq, gR_iteratedDeriv k x hx]
    exact (Complex.abs_re_le_norm _).trans ((norm_iteratedDeriv_G_le k hx).trans (cauchy_bound_le k hk hx))
  -- x < 0
  have hneg : ∀ x : ℝ, x < 0 → |iteratedDeriv k expNegInvGlue x| ≤ C := by
    intro x hx
    have hev : expNegInvGlue =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with t ht
      exact expNegInvGlue.zero_of_nonpos ht.le
    rw [hev.iteratedDeriv_eq, iteratedDeriv_const]
    simp [hC0, Nat.one_le_iff_ne_zero.mp hk]
  -- x = 0 by closedness + density
  have hcont : Continuous (iteratedDeriv k expNegInvGlue) :=
    expNegInvGlue.contDiff.continuous_iteratedDeriv k (by exact_mod_cast le_top)
  have hclosed : IsClosed {x : ℝ | |iteratedDeriv k expNegInvGlue x| ≤ C} :=
    isClosed_le (continuous_abs.comp hcont) continuous_const
  have hsub : ({0}ᶜ : Set ℝ) ⊆ {x : ℝ | |iteratedDeriv k expNegInvGlue x| ≤ C} := by
    intro x hx
    rcases lt_or_gt_of_ne hx with h | h
    · exact hneg x h
    · exact hpos x h
  have : x ∈ closure ({0}ᶜ : Set ℝ) := by rw [closure_compl_singleton]; trivial
  exact hclosed.closure_subset_iff.mpr hsub this


/-! ### bounds for g and g(1−·) with the convention gb 0 = 1 -/

def gb (k : ℕ) : ℝ := (18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k)

lemma gb_zero : gb 0 = 1 := by simp [gb]

lemma expNegInvGlue_le_one (x : ℝ) : expNegInvGlue x ≤ 1 := by
  unfold expNegInvGlue
  split_ifs with h
  · norm_num
  · apply Real.exp_le_one_iff.mpr
    have : 0 < x := not_le.mp h
    have := inv_pos.mpr this
    linarith

lemma abs_iteratedDeriv_g_le (k : ℕ) (x : ℝ) : |iteratedDeriv k expNegInvGlue x| ≤ gb k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [iteratedDeriv_zero, gb_zero, abs_of_nonneg (expNegInvGlue.nonneg x)]
    exact expNegInvGlue_le_one x
  · have h := gevrey_expNegInvGlue k hk x
    rw [show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast] at h
    exact h

lemma abs_iteratedDeriv_gflip_le (k : ℕ) (x : ℝ) :
    |iteratedDeriv k (fun t => expNegInvGlue (1 - t)) x| ≤ gb k := by
  rw [iteratedDeriv_comp_const_sub]
  simp only [smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact abs_iteratedDeriv_g_le k (1 - x)

lemma gb_mul_gb_le {k i : ℕ} (hi : i ≤ k) : gb i * gb (k - i) ≤ (18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k) := by
  unfold gb
  have h18 : (0:ℝ) ≤ 18 / Real.exp 1 := by positivity
  have hik : (i : ℝ) ≤ k := by exact_mod_cast hi
  have hki : ((k - i : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k i
  calc (18 / Real.exp 1) ^ i * (i : ℝ) ^ (2 * i) * ((18 / Real.exp 1) ^ (k - i) * ((k - i : ℕ) : ℝ) ^ (2 * (k - i)))
      = (18 / Real.exp 1) ^ (i + (k - i)) * ((i : ℝ) ^ (2 * i) * ((k - i : ℕ) : ℝ) ^ (2 * (k - i))) := by
        rw [pow_add]; ring
    _ ≤ (18 / Real.exp 1) ^ k * ((k : ℝ) ^ (2 * i) * (k : ℝ) ^ (2 * (k - i))) := by
        rw [Nat.add_sub_cancel' hi]
        gcongr
    _ = (18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k) := by
        rw [← pow_add]; congr 2; omega

/-! ### θ -/

lemma theta_contDiff {n : ℕ∞} : ContDiff ℝ n theta :=
  expNegInvGlue.contDiff.mul (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

lemma theta_continuous : Continuous theta := (theta_contDiff (n := 0)).continuous

lemma theta_nonneg (x : ℝ) : 0 ≤ theta x := mul_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)

lemma theta_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : theta x = 0 := by
  simp [theta, expNegInvGlue.zero_of_nonpos hx]

lemma theta_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) : theta x = 0 := by
  simp [theta, expNegInvGlue.zero_of_nonpos (show 1 - x ≤ 0 by linarith)]

lemma theta_pos {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : 0 < theta x :=
  mul_pos (expNegInvGlue.pos_of_pos h0) (expNegInvGlue.pos_of_pos (by linarith))

/-- Leibniz ⇒ |θ^{(k)}| ≤ (36/e)^k k^{2k}. -/
lemma abs_iteratedDeriv_theta_le (k : ℕ) (x : ℝ) :
    |iteratedDeriv k theta x| ≤ (36 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k) := by
  have hf : ContDiff ℝ k expNegInvGlue := expNegInvGlue.contDiff
  have hg : ContDiff ℝ k (fun t => expNegInvGlue (1 - t)) :=
    expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)
  have h := norm_iteratedFDeriv_mul_le hf hg x (n := k) le_rfl
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at h
  change |iteratedDeriv k theta x| ≤ _ at h
  refine h.trans ?_
  calc ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * |iteratedDeriv i expNegInvGlue x|
        * |iteratedDeriv (k - i) (fun t => expNegInvGlue (1 - t)) x|
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ((18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        calc |iteratedDeriv i expNegInvGlue x| * |iteratedDeriv (k - i) (fun t => expNegInvGlue (1 - t)) x|
            ≤ gb i * gb (k - i) := mul_le_mul (abs_iteratedDeriv_g_le i x) (abs_iteratedDeriv_gflip_le _ x)
                (abs_nonneg _) (by unfold gb; positivity)
          _ ≤ _ := gb_mul_gb_le hik
    _ = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) * ((18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k)) := by
        rw [Finset.sum_mul]
    _ = (2:ℝ) ^ k * ((18 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k)) := by
        congr 1; exact_mod_cast Nat.sum_range_choose k
    _ = (36 / Real.exp 1) ^ k * (k : ℝ) ^ (2 * k) := by
        rw [← mul_assoc, ← mul_pow]; congr 2; ring

/-! ### Θ = primitive of θ -/

lemma Theta_hasDerivAt (x : ℝ) : HasDerivAt Theta (theta x) x :=
  integral_hasDerivAt_right (theta_continuous.intervalIntegrable _ _)
    (theta_continuous.stronglyMeasurableAtFilter _ _) theta_continuous.continuousAt

lemma Theta_deriv : deriv Theta = theta := funext fun x => (Theta_hasDerivAt x).deriv

lemma Theta_differentiable : Differentiable ℝ Theta := fun x => (Theta_hasDerivAt x).differentiableAt

lemma Theta_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Theta := by
  rw [contDiff_infty_iff_deriv, Theta_deriv]
  exact ⟨Theta_differentiable, theta_contDiff⟩

lemma iteratedDeriv_succ_Theta (k : ℕ) : iteratedDeriv (k + 1) Theta = iteratedDeriv k theta := by
  rw [iteratedDeriv_succ', Theta_deriv]

lemma Theta_of_nonpos {x : ℝ} (hx : x ≤ 0) : Theta x = 0 := by
  unfold Theta
  rw [integral_symm, neg_eq_zero]
  rw [show (∫ t in x..0, theta t) = ∫ t in x..0, (0:ℝ) from
    integral_congr fun t ht => theta_eq_zero_of_nonpos (by rw [uIcc_of_le hx] at ht; exact ht.2)]
  simp

lemma Theta_of_one_le {x : ℝ} (hx : 1 ≤ x) : Theta x = Theta 1 := by
  unfold Theta
  rw [← integral_add_adjacent_intervals (b := 1) (theta_continuous.intervalIntegrable _ _)
    (theta_continuous.intervalIntegrable _ _)]
  rw [show (∫ t in (1:ℝ)..x, theta t) = ∫ t in (1:ℝ)..x, (0:ℝ) from
    integral_congr fun t ht => theta_eq_zero_of_one_le (by rw [uIcc_of_le hx] at ht; exact ht.1)]
  simp

lemma Theta_one_pos : 0 < Theta 1 :=
  intervalIntegral_pos_of_pos_on (theta_continuous.intervalIntegrable _ _) (fun x hx => theta_pos hx.1 hx.2)
    zero_lt_one

/-- ∫_0^1 θ ≥ e^{−8}/2 (θ ≥ e^{−8} on [1/4, 3/4]). -/
lemma Theta_one_ge : Real.exp (-8) / 2 ≤ Theta 1 := by
  have hc := theta_continuous
  have hlow : ∀ x ∈ Icc (1/4 : ℝ) (3/4), Real.exp (-8) ≤ theta x := by
    intro x hx
    have h1 : Real.exp (-4) ≤ expNegInvGlue x := by
      have hx0 : 0 < x := by linarith [hx.1]
      simp only [expNegInvGlue, not_le.mpr hx0, if_false]
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff, inv_le_comm₀ hx0 (by norm_num)]; linarith [hx.1]
    have h2 : Real.exp (-4) ≤ expNegInvGlue (1 - x) := by
      have hx0 : 0 < 1 - x := by linarith [hx.2]
      simp only [expNegInvGlue, not_le.mpr hx0, if_false]
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff, inv_le_comm₀ hx0 (by norm_num)]; linarith [hx.2]
    calc Real.exp (-8) = Real.exp (-4) * Real.exp (-4) := by rw [← Real.exp_add]; norm_num
      _ ≤ theta x := mul_le_mul h1 h2 (Real.exp_pos _).le (expNegInvGlue.nonneg _)
  unfold Theta
  rw [← integral_add_adjacent_intervals (b := 1/4) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    ← integral_add_adjacent_intervals (a := 1/4) (b := 3/4) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have i1 : 0 ≤ ∫ t in (0:ℝ)..(1/4), theta t := integral_nonneg (by norm_num) fun t _ => theta_nonneg t
  have i3 : 0 ≤ ∫ t in (3/4:ℝ)..1, theta t := integral_nonneg (by norm_num) fun t _ => theta_nonneg t
  have i2 : Real.exp (-8) / 2 ≤ ∫ t in (1/4:ℝ)..(3/4), theta t := by
    have := integral_mono_on (a := (1/4:ℝ)) (b := 3/4) (μ := volume) (by norm_num)
      _root_.intervalIntegrable_const (hc.intervalIntegrable _ _) hlow
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  linarith

/-! ### ϱ₂ -/

lemma rhoTwo_eq (x : ℝ) : rhoTwo x = (Theta 1)⁻¹ * Theta x := by
  unfold rhoTwo Theta; rw [div_eq_inv_mul]

lemma rhoTwo_eq_fun : rhoTwo = fun x => (Theta 1)⁻¹ * Theta x := funext rhoTwo_eq

lemma rhoTwo_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) rhoTwo := by
  rw [rhoTwo_eq_fun]; exact contDiff_const.mul Theta_contDiff

lemma rhoTwo_taper : TaperProfile rhoTwo where
  contDiff := by
    rw [rhoTwo_eq_fun]
    exact contDiff_const.mul (Theta_contDiff.of_le (WithTop.coe_le_coe.mpr le_top))
  monotone := by
    rw [rhoTwo_eq_fun]
    refine (monotone_of_deriv_nonneg Theta_differentiable fun x => ?_).const_mul (inv_nonneg.mpr Theta_one_pos.le)
    rw [Theta_deriv]; exact theta_nonneg x
  eq_zero x hx := by rw [rhoTwo_eq, Theta_of_nonpos hx, mul_zero]
  eq_one x hx := by rw [rhoTwo_eq, Theta_of_one_le hx, inv_mul_cancel₀ Theta_one_pos.ne']

lemma iteratedDeriv_rhoTwo (k : ℕ) (x : ℝ) :
    iteratedDeriv (k + 1) rhoTwo x = (Theta 1)⁻¹ * iteratedDeriv k theta x := by
  rw [rhoTwo_eq_fun, iteratedDeriv_const_mul_field, iteratedDeriv_succ_Theta]

/-- **(P4)** ϱ₂ is a Gevrey-2 taper profile with explicit constants (A, B) = (36/e, 2e^8):
the input needed by the family/q-aspect tail lemma. -/
theorem gevreyProfile_rhoTwo : GevreyProfile 2 (36 / Real.exp 1) (2 * Real.exp 8) rhoTwo where
  taper := rhoTwo_taper
  smooth := rhoTwo_contDiff
  one_lt := by norm_num
  A_pos := by positivity
  B_pos := by positivity
  bound k hk x := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [iteratedDeriv_rhoTwo, abs_mul, abs_inv, abs_of_pos Theta_one_pos]
    have hZ : (Theta 1)⁻¹ ≤ 2 * Real.exp 8 := by
      rw [inv_le_comm₀ Theta_one_pos (by positivity)]
      have := Theta_one_ge
      rw [show (2 * Real.exp 8)⁻¹ = Real.exp (-8) / 2 by rw [Real.exp_neg]; field_simp]
      exact this
    have hθ := abs_iteratedDeriv_theta_le j x
    have hA : (1:ℝ) ≤ 36 / Real.exp 1 := by
      rw [le_div_iff₀ (Real.exp_pos 1)]; have := Real.exp_one_lt_d9; linarith
    -- (36/e)^j j^{2j} ≤ (36/e)^{j+1} (j+1)^{2(j+1)}  and rpow form
    have hrpow : ((j + 1 : ℕ) : ℝ) ^ ((2:ℝ) * ((j + 1 : ℕ) : ℝ)) = ((j + 1 : ℕ) : ℝ) ^ (2 * (j + 1)) := by
      rw [show (2:ℝ) * ((j+1 : ℕ) : ℝ) = ((2 * (j+1) : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [hrpow]
    have hmono : (36 / Real.exp 1) ^ j * (j : ℝ) ^ (2 * j) ≤ (36 / Real.exp 1) ^ (j + 1) * ((j + 1 : ℕ) : ℝ) ^ (2 * (j + 1)) := by
      have h1 : (36 / Real.exp 1) ^ j ≤ (36 / Real.exp 1) ^ (j + 1) := pow_le_pow_right₀ hA (Nat.le_succ j)
      have h2 : (j : ℝ) ^ (2 * j) ≤ ((j + 1 : ℕ) : ℝ) ^ (2 * (j + 1)) := by
        calc (j : ℝ) ^ (2 * j) ≤ ((j + 1 : ℕ) : ℝ) ^ (2 * j) :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) (by push_cast; linarith) _
          _ ≤ ((j + 1 : ℕ) : ℝ) ^ (2 * (j + 1)) :=
              pow_le_pow_right₀ (by push_cast; linarith) (by omega)
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    calc (Theta 1)⁻¹ * |iteratedDeriv j theta x| ≤ (2 * Real.exp 8) * ((36 / Real.exp 1) ^ j * (j : ℝ) ^ (2 * j)) :=
          mul_le_mul hZ hθ (abs_nonneg _) (by positivity)
      _ ≤ (2 * Real.exp 8) * ((36 / Real.exp 1) ^ (j + 1) * ((j + 1 : ℕ) : ℝ) ^ (2 * (j + 1))) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = 2 * Real.exp 8 * (36 / Real.exp 1) ^ (j + 1) * ((j + 1 : ℕ) : ℝ) ^ (2 * (j + 1)) := by ring


end Taper
end Zeta23
