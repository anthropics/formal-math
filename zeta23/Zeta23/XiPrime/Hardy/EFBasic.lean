/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Hardy/EFBasic.lean — basic objects of the W explicit formula [XF′ §9.0–9.1].
 * analyticity of Γℝ, χ = chiFE, L₂, W at the REAL points of the strip away from the poles (Hardy/Basic.lean
   has everything off the real axis);
 * E₂ := L₂ + ζ′/ζ ( = W/ζ where ζ ≠ 0 ) and F_𝒵 := L₂ + W′/W;  [XF′ (Z1)]  F_𝒵 = E₂ + E₂′/E₂ on 1 < Re s < 3/2
   wherever W ≠ 0;  E₂ = L₂ − A, E₂′ = L₂′ + B;
 * [XF′ (Z2)]  F_𝒵(1−s) = −F_𝒵(s),  E₂(s̄) = conj E₂(s),  F_𝒵(s̄) = conj F_𝒵(s)  (off ℝ);
 * the low zeros of W in a compact box of the half-plane Re s > 1 are finitely many, hence a line Re s = c,
   c ∈ [9/8, 5/4], carrying no zero of W of height < t₀ exists  (the "choice of c" of Hardy/EFMain).
-/
import Zeta23.XiPrime.Hardy.TwoLine
import Zeta23.XiPrime.ExplicitFormula.Expansion

open scoped BigOperators ArithmeticFunction ComplexConjugate
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Zeta23
namespace XiPrime

open Hardy

/-! ## 1. Analyticity at real points away from the poles -/

/-- Γℝ is differentiable at s unless s/2 is a non-positive integer. -/
lemma differentiableAt_Gammaℝ_of_ne {s : ℂ} (hs : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) :
    DifferentiableAt ℂ Gammaℝ s := by
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := by
    refine DifferentiableAt.const_cpow ?_ (Or.inl (by exact_mod_cast Real.pi_ne_zero))
    exact (differentiableAt_id.neg).div_const 2
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    (Complex.differentiableAt_Gamma _ hs).comp s (differentiableAt_id.div_const 2)
  have : Gammaℝ = fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) := funext Gammaℝ_def
  rw [this]; exact h1.mul h2

/-- points of the vertical strip 1 < Re s < 3/2: no pole of Γℝ(s), Γℝ(1−s) and s ≠ 0, 1. -/
def GoodStrip : Set ℂ := {s : ℂ | 1 < s.re ∧ s.re < 3 / 2}

lemma isOpen_goodStrip : IsOpen GoodStrip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)

lemma goodStrip_half_ne {s : ℂ} (hs : s ∈ GoodStrip) (m : ℕ) : s / 2 ≠ -(m : ℂ) := by
  intro h
  have := congrArg Complex.re h
  simp at this
  have h1 := hs.1
  have : (0:ℝ) ≤ m := Nat.cast_nonneg m
  linarith

lemma goodStrip_one_sub_half_ne {s : ℂ} (hs : s ∈ GoodStrip) (m : ℕ) : (1 - s) / 2 ≠ -(m : ℂ) := by
  intro h
  have := congrArg Complex.re h
  simp at this
  obtain ⟨h1, h2⟩ := hs
  -- (1 - re s)/2 ∈ (−1/4, 0): equals −m only if m = 0… but then re s = 1, excluded; or m ≥ 1 ⇒ re s ≥ 3.
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp at this; linarith
  · have : (1:ℝ) ≤ m := by exact_mod_cast hm
    linarith

lemma goodStrip_ne_zero {s : ℂ} (hs : s ∈ GoodStrip) : s ≠ 0 := fun h => by
  have := hs.1; rw [h] at this; simp at this; linarith
lemma goodStrip_ne_one {s : ℂ} (hs : s ∈ GoodStrip) : s ≠ 1 := fun h => by
  have := hs.1; rw [h] at this; simp at this

lemma Gammaℝ_ne_zero_of_ne {s : ℂ} (hs : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) : Gammaℝ s ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff, not_exists]
  intro n h
  apply hs n
  rw [h]; ring

lemma analyticAt_Gammaℝ_goodStrip {s : ℂ} (hs : s ∈ GoodStrip) : AnalyticAt ℂ Gammaℝ s := by
  refine Complex.analyticAt_iff_eventually_differentiableAt.mpr ?_
  filter_upwards [isOpen_goodStrip.mem_nhds hs] with z hz
  exact differentiableAt_Gammaℝ_of_ne (goodStrip_half_ne hz)

lemma analyticAt_Gammaℝ_one_sub_goodStrip {s : ℂ} (hs : s ∈ GoodStrip) :
    AnalyticAt ℂ (fun z => Gammaℝ (1 - z)) s := by
  have h : AnalyticAt ℂ Gammaℝ (1 - s) := by
    refine Complex.analyticAt_iff_eventually_differentiableAt.mpr ?_
    have hopen : IsOpen ((fun z : ℂ => 1 - z) ⁻¹' GoodStrip) := isOpen_goodStrip.preimage (by fun_prop)
    have hmem : (1 - s) ∈ (fun z : ℂ => 1 - z) ⁻¹' GoodStrip := by simpa using hs
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have := goodStrip_one_sub_half_ne hz
    refine differentiableAt_Gammaℝ_of_ne fun m => ?_
    have h := this m
    simpa using h
  exact h.comp (analyticAt_const.sub analyticAt_id)

lemma chiFE_analyticAt_goodStrip {s : ℂ} (hs : s ∈ GoodStrip) : AnalyticAt ℂ chiFE s := by
  have : chiFE = fun z => Gammaℝ (1 - z) / Gammaℝ z := funext chiFE_def
  rw [this]
  exact (analyticAt_Gammaℝ_one_sub_goodStrip hs).div (analyticAt_Gammaℝ_goodStrip hs)
    (Gammaℝ_ne_zero_of_ne (goodStrip_half_ne hs))

lemma chiFE_ne_zero_goodStrip {s : ℂ} (hs : s ∈ GoodStrip) : chiFE s ≠ 0 :=
  div_ne_zero (Gammaℝ_ne_zero_of_ne (goodStrip_one_sub_half_ne hs)) (Gammaℝ_ne_zero_of_ne (goodStrip_half_ne hs))

lemma L2_analyticAt_goodStrip {s : ℂ} (hs : s ∈ GoodStrip) : AnalyticAt ℂ L2 s := by
  have e : L2 = fun z => -(1/2) * (deriv chiFE z / chiFE z) := by
    funext z; rw [L2, logDeriv_apply]
  rw [e]
  exact analyticAt_const.mul ((chiFE_analyticAt_goodStrip hs).deriv.div (chiFE_analyticAt_goodStrip hs)
    (chiFE_ne_zero_goodStrip hs))

lemma hardyW_analyticAt_goodStrip {s : ℂ} (hs : s ∈ GoodStrip) : AnalyticAt ℂ hardyW s := by
  have e : hardyW = fun z => deriv riemannZeta z + L2 z * riemannZeta z := funext fun z => rfl
  rw [e]
  exact (analyticAt_deriv_riemannZeta (goodStrip_ne_one hs)).add
    ((L2_analyticAt_goodStrip hs).mul (Hardy.analyticAt_riemannZeta (goodStrip_ne_one hs)))

/-! ## 2. E₂ and F_𝒵 -/

/-- E₂ := L₂ + ζ′/ζ  (= W/ζ wherever ζ ≠ 0; = L₂ − A on Re s > 1). -/
def E2fn (s : ℂ) : ℂ := L2 s + logDeriv riemannZeta s

/-- F_𝒵 := L₂ + W′/W  [XF′ §9.0]. -/
def FZfn (s : ℂ) : ℂ := L2 s + logDeriv hardyW s

theorem hardyW_eq_zeta_mul_E2fn {s : ℂ} (hζ : riemannZeta s ≠ 0) : hardyW s = riemannZeta s * E2fn s := by
  rw [E2fn, hardyW_eq_zeta_mul hζ]; ring

theorem E2fn_eq_L2_sub_Afn {s : ℂ} (hs : 1 < s.re) : E2fn s = L2 s - Afn s := by
  rw [E2fn, logDeriv_zeta_eq_neg_Afn hs]; ring

theorem E2fn_eq_Efn_add {s : ℂ} : E2fn s = Efn s + (L2 s - Lfn s) := by
  rw [E2fn, Efn]; ring

theorem analyticAt_E2fn {s : ℂ} (hs : s ∈ GoodStrip) : AnalyticAt ℂ E2fn s := by
  have e : E2fn = fun z => L2 z + logDeriv riemannZeta z := rfl
  have h1 : AnalyticAt ℂ (logDeriv riemannZeta) s := by
    have : logDeriv riemannZeta = fun z => deriv riemannZeta z / riemannZeta z := by
      funext z; rw [logDeriv_apply]
    rw [this]
    exact (analyticAt_deriv_riemannZeta (goodStrip_ne_one hs)).div
      (Hardy.analyticAt_riemannZeta (goodStrip_ne_one hs)) (riemannZeta_ne_zero_of_one_lt_re hs.1)
  rw [e]; exact (L2_analyticAt_goodStrip hs).add h1

theorem differentiableAt_E2fn {s : ℂ} (hs : s ∈ GoodStrip) : DifferentiableAt ℂ E2fn s :=
  (analyticAt_E2fn hs).differentiableAt

theorem differentiableAt_L2 {s : ℂ} (hs : s ∈ GoodStrip) : DifferentiableAt ℂ L2 s :=
  (L2_analyticAt_goodStrip hs).differentiableAt

theorem deriv_E2fn {s : ℂ} (hs : s ∈ GoodStrip) : deriv E2fn s = deriv L2 s + Bfn s := by
  have h : HasDerivAt E2fn (deriv L2 s + Bfn s) s :=
    (differentiableAt_L2 hs).hasDerivAt.add (hasDerivAt_logDeriv_zeta hs.1)
  exact h.deriv

theorem E2fn_ne_zero {s : ℂ} (hs : 1 < s.re) (hW : hardyW s ≠ 0) : E2fn s ≠ 0 := by
  intro h; apply hW
  rw [hardyW_eq_zeta_mul_E2fn (riemannZeta_ne_zero_of_one_lt_re hs), h, mul_zero]

/-- **[XF′ (Z1)]**  F_𝒵 = E₂ + E₂′/E₂ on 1 < Re s < 3/2 wherever W ≠ 0. -/
theorem FZfn_eq {s : ℂ} (hs : s ∈ GoodStrip) (hW : hardyW s ≠ 0) :
    FZfn s = E2fn s + deriv E2fn s / E2fn s := by
  have hev : hardyW =ᶠ[𝓝 s] fun z => riemannZeta z * E2fn z := by
    filter_upwards [isOpen_goodStrip.mem_nhds hs] with z hz
    exact hardyW_eq_zeta_mul_E2fn (riemannZeta_ne_zero_of_one_lt_re hz.1)
  have hζ := riemannZeta_ne_zero_of_one_lt_re hs.1
  have hE : E2fn s ≠ 0 := E2fn_ne_zero hs.1 hW
  have e1 : logDeriv hardyW s = logDeriv (fun z => riemannZeta z * E2fn z) s := by
    simp only [logDeriv_apply, hev.deriv_eq, hev.self_of_nhds]
  rw [FZfn, e1, logDeriv_mul (f := riemannZeta) (g := E2fn) s hζ hE
    (differentiableAt_riemannZeta (goodStrip_ne_one hs)) (differentiableAt_E2fn hs), logDeriv_apply (f := E2fn)]
  rw [E2fn]; ring

/-- E₂′/E₂ = F_𝒵 − E₂. -/
theorem derivE2_div_E2_eq {s : ℂ} (hs : s ∈ GoodStrip) (hW : hardyW s ≠ 0) :
    deriv E2fn s / E2fn s = FZfn s - E2fn s := by
  rw [FZfn_eq hs hW]; ring

/-! ## 3. Symmetries (off the real axis) -/

theorem logDeriv_riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    logDeriv riemannZeta (conj s) = conj (logDeriv riemannZeta s) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_riemannZeta_conj hs, Zeta23.riemannZeta_conj hs, map_div₀]

theorem E2fn_conj {s : ℂ} (hs : s.im ≠ 0) : E2fn (conj s) = conj (E2fn s) := by
  rw [E2fn, E2fn, L2_conj hs, logDeriv_riemannZeta_conj (ne_one_of_im_ne_zero hs), map_add]

theorem logDeriv_hardyW_conj {s : ℂ} (hs : s.im ≠ 0) :
    logDeriv hardyW (conj s) = conj (logDeriv hardyW s) := by
  have hs' : (conj s).im ≠ 0 := by simpa using hs
  rw [logDeriv_apply, logDeriv_apply, hardyW_conj hs]
  rw [deriv_conj_of_symm (hardyW_differentiableAt hs) ?_, map_div₀]
  filter_upwards [isOpen_im_ne_zero.mem_nhds hs'] with z hz
  exact hardyW_conj hz

theorem FZfn_conj {s : ℂ} (hs : s.im ≠ 0) : FZfn (conj s) = conj (FZfn s) := by
  rw [FZfn, FZfn, L2_conj hs, logDeriv_hardyW_conj hs, map_add]

/-- W′/W(1−s) = −W′/W(s) − 2L₂(s)  [XF′ (Z2)], wherever W(s) ≠ 0, off ℝ. -/
theorem logDeriv_hardyW_one_sub {s : ℂ} (hs : s.im ≠ 0) (hW : hardyW s ≠ 0) :
    logDeriv hardyW (1 - s) = -logDeriv hardyW s - 2 * L2 s := by
  have hs' := im_one_sub_ne_zero hs
  have hev : (fun z => hardyW (1 - z)) =ᶠ[𝓝 s] fun z => -(hardyW z / chiFE z) := by
    filter_upwards [isOpen_im_ne_zero.mem_nhds hs] with z hz
    rw [hardyW_eq_neg_chiFE_mul hz]
    field_simp [chiFE_ne_zero hz]
  have hχ := chiFE_ne_zero hs
  have hdW := hardyW_differentiableAt hs
  have hdχ := (chiFE_analyticAt hs).differentiableAt
  have hd1 : deriv (fun z => hardyW (1 - z)) s = -deriv hardyW (1 - s) := by
    have h1 : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
      simpa using (hasDerivAt_const s (1:ℂ)).fun_sub (hasDerivAt_id s)
    have h := (hardyW_differentiableAt hs').hasDerivAt.comp s h1
    rw [show (hardyW ∘ HSub.hSub 1) = (fun z => hardyW (1 - z)) from rfl] at h
    rw [h.deriv]; ring
  have hd2 : deriv (fun z => hardyW (1 - z)) s = deriv (fun z => -(hardyW z / chiFE z)) s := hev.deriv_eq
  have hd3 : deriv (fun z => -(hardyW z / chiFE z)) s
      = -((deriv hardyW s * chiFE s - hardyW s * deriv chiFE s) / chiFE s ^ 2) := by
    have h := ((hdW.hasDerivAt).div (hdχ.hasDerivAt) hχ).neg
    exact h.deriv
  have hval : hardyW (1 - s) = -(hardyW s / chiFE s) := hev.self_of_nhds
  have hderiv : deriv hardyW (1 - s) = (deriv hardyW s * chiFE s - hardyW s * deriv chiFE s) / chiFE s ^ 2 := by
    have : deriv hardyW (1 - s) = -deriv (fun z => hardyW (1 - z)) s := by rw [hd1]; ring
    rw [this, hd2, hd3]; ring
  rw [logDeriv_apply, logDeriv_apply, hval, hderiv, deriv_chiFE hs]
  field_simp
  ring

/-- **[XF′ (Z2)]**  F_𝒵(1−s) = −F_𝒵(s), off ℝ, wherever W(s) ≠ 0. -/
theorem FZfn_one_sub {s : ℂ} (hs : s.im ≠ 0) (hW : hardyW s ≠ 0) : FZfn (1 - s) = -FZfn s := by
  rw [FZfn, FZfn, L2_one_sub hs, logDeriv_hardyW_one_sub hs hW]; ring

/-! ## 4. Finitely many low zeros to the right of Re s = 1; a zero-free line -/

/-- the compact box [9/8, 5/4] × [−t₀, t₀] carries finitely many zeros of W. -/
theorem finite_lowZeros_right (t₀ : ℝ) :
    ({s : ℂ | 9/8 ≤ s.re ∧ s.re ≤ 5/4 ∧ |s.im| ≤ t₀} ∩ hardyW ⁻¹' {0}).Finite := by
  -- W is analytic on a neighbourhood of the box and not identically zero there (W = ζ·E₂ with
  -- Re E₂(5/4 + it) ≠ 0 for large t); isolated zeros + compactness.
  obtain ⟨t₁, ht₁, hlow⟩ := hardyW_two_line_lower
  -- We embed the box in the bigger rectangle [9/8, 2] × [−R, R], on which W is analytic
  -- (W has no poles on 1 < Re s < 3), and use the nonvanishing point 2 + i t₁ from the two-line bound.
  set R : ℝ := max (max t₀ 0) t₁ with hR
  have hsub : {s : ℂ | 9/8 ≤ s.re ∧ s.re ≤ 5/4 ∧ |s.im| ≤ t₀} ∩ hardyW ⁻¹' {0}
      ⊆ Rectangle (((9/8:ℝ):ℂ) - R * I) ((2:ℂ) + R * I) ∩ hardyW ⁻¹' {0} := by
    intro s ⟨⟨h1, h2, h3⟩, h0⟩
    refine ⟨?_, h0⟩
    rw [mem_Rect (by simp; norm_num) (by simp; exact le_trans (by positivity) (le_max_of_le_left (le_max_right _ _)))]
    simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_re,
      re_ofNat, add_zero, sub_im, mul_im, zero_sub, add_im, im_ofNat, zero_add, sub_zero]
    refine ⟨h1, by linarith, ?_, ?_⟩
    · have := (abs_le.mp h3).1; have : t₀ ≤ R := le_trans (le_max_left _ _) (le_max_left _ _); linarith
    · have := (abs_le.mp h3).2; have : t₀ ≤ R := le_trans (le_max_left _ _) (le_max_left _ _); linarith
  refine Set.Finite.subset ?_ hsub
  -- analyticity on the closed rectangle [9/8, 2] × [−R, R]: 1 < Re < 3 avoids every pole
  have hanal : AnalyticOnNhd ℂ hardyW (Rectangle (((9/8:ℝ):ℂ) - R * I) ((2:ℂ) + R * I)) := by
    intro s hs
    have hR0 : 0 ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
    rw [mem_Rect (by simp; norm_num) (by simp; linarith)] at hs
    simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_re,
      re_ofNat, add_zero, sub_im, mul_im, zero_sub, add_im, im_ofNat, zero_add, sub_zero] at hs
    obtain ⟨h1, h2, -, -⟩ := hs
    -- points with 1 < Re < 3: Γℝ(s), Γℝ(1−s) analytic, s ≠ 1
    have hne1 : s ≠ 1 := fun h => by rw [h] at h1; simp at h1; linarith
    have hA : ∀ m : ℕ, s / 2 ≠ -(m:ℂ) := by
      intro m h; have := congrArg Complex.re h; simp at this
      have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith
    have hB : ∀ m : ℕ, (1 - s) / 2 ≠ -(m:ℂ) := by
      intro m h; have := congrArg Complex.re h; simp at this
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp at this; linarith
      · rcases Nat.lt_or_ge m 2 with hm2 | hm2
        · interval_cases m <;> simp at this <;> linarith
        · have : (2:ℝ) ≤ m := by exact_mod_cast hm2
          linarith
    -- assemble: chiFE analytic & ≠ 0 at s
    have hG : AnalyticAt ℂ Gammaℝ s := by
      refine Complex.analyticAt_iff_eventually_differentiableAt.mpr ?_
      have hopen : IsOpen {z : ℂ | 1 < z.re ∧ z.re < 3} :=
        (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
      filter_upwards [hopen.mem_nhds (show s ∈ {z : ℂ | 1 < z.re ∧ z.re < 3} from ⟨by linarith, by linarith⟩)] with z hz
      refine differentiableAt_Gammaℝ_of_ne fun m h => ?_
      have := congrArg Complex.re h; simp at this
      have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith [hz.1]
    have hG1 : AnalyticAt ℂ (fun z => Gammaℝ (1 - z)) s := by
      have h : AnalyticAt ℂ Gammaℝ (1 - s) := by
        refine Complex.analyticAt_iff_eventually_differentiableAt.mpr ?_
        have hopen : IsOpen {z : ℂ | -2 < z.re ∧ z.re < 0} :=
          (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
        have hmem : (1 - s) ∈ {z : ℂ | -2 < z.re ∧ z.re < 0} := by
          simp only [mem_setOf_eq, sub_re, one_re]; constructor <;> linarith
        filter_upwards [hopen.mem_nhds hmem] with z hz
        refine differentiableAt_Gammaℝ_of_ne fun m h => ?_
        have := congrArg Complex.re h; simp at this
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp at this; linarith [hz.2]
        · have : (1:ℝ) ≤ m := by exact_mod_cast hm
          linarith [hz.1]
      exact h.comp (analyticAt_const.sub analyticAt_id)
    have hχ : AnalyticAt ℂ chiFE s := by
      have : chiFE = fun z => Gammaℝ (1 - z) / Gammaℝ z := funext chiFE_def
      rw [this]; exact hG1.div hG (Gammaℝ_ne_zero_of_ne hA)
    have hχ0 : chiFE s ≠ 0 := div_ne_zero (Gammaℝ_ne_zero_of_ne hB) (Gammaℝ_ne_zero_of_ne hA)
    have hL2 : AnalyticAt ℂ L2 s := by
      have e : L2 = fun z => -(1/2) * (deriv chiFE z / chiFE z) := by funext z; rw [L2, logDeriv_apply]
      rw [e]; exact analyticAt_const.mul (hχ.deriv.div hχ hχ0)
    have e : hardyW = fun z => deriv riemannZeta z + L2 z * riemannZeta z := funext fun z => rfl
    rw [e]
    exact (analyticAt_deriv_riemannZeta hne1).add (hL2.mul (Hardy.analyticAt_riemannZeta hne1))
  -- the nonvanishing point 2 + i t₁ lies in the rectangle
  have hx : (2:ℂ) + t₁ * I ∈ Rectangle (((9/8:ℝ):ℂ) - R * I) ((2:ℂ) + R * I) := by
    have hR0 : t₁ ≤ R := le_max_right _ _
    rw [mem_Rect (by simp; norm_num) (by simp; linarith)]
    simp; constructor <;> [norm_num; constructor <;> linarith]
  have hWx : hardyW ((2:ℂ) + t₁ * I) ≠ 0 := by
    have := (hlow t₁ (by rw [abs_of_pos (by linarith)])).2
    intro h; rw [h, norm_zero] at this; linarith
  exact Zeta23.Analytic.finite_zeros_rectangle hanal hx hWx

/-- **choice of the line**: some c ∈ [9/8, 5/4] such that W has no zero of height < t₀ on Re s = c. -/
theorem exists_zeroFree_line (t₀ : ℝ) :
    ∃ c : ℝ, 9/8 ≤ c ∧ c ≤ 5/4 ∧ ∀ s : ℂ, s.re = c → |s.im| < t₀ → hardyW s ≠ 0 := by
  have hfin := finite_lowZeros_right t₀
  set bad : Finset ℝ := (hfin.image Complex.re).toFinset with hbad
  obtain ⟨c, hc, hcb⟩ := (Icc_infinite (show (9/8:ℝ) < 5/4 by norm_num)).exists_notMem_finset bad
  refine ⟨c, hc.1, hc.2, fun s hsre hsim h0 => hcb ?_⟩
  rw [hbad, Set.Finite.mem_toFinset]
  exact ⟨s, ⟨⟨by rw [hsre]; exact hc.1, by rw [hsre]; exact hc.2, hsim.le⟩, h0⟩, hsre⟩

/-- … and then also none on Re s = 1 − c (off ℝ by W(1−s) = 0 ↔ W(s) = 0; at the real point via
the reflection identity extended to the real point by continuity). -/
theorem hardyW_ne_zero_reflect_line {c t₀ : ℝ}
    (h : ∀ s : ℂ, s.re = c → |s.im| < t₀ → hardyW s ≠ 0) :
    ∀ s : ℂ, s.re = 1 - c → |s.im| < t₀ → s.im ≠ 0 → hardyW s ≠ 0 := by
  intro s hsre hsim him h0
  have h1 : hardyW (1 - s) = 0 := (hardyW_one_sub_eq_zero_iff him).mpr h0
  exact h (1 - s) (by simp [hsre]) (by simpa using hsim) h1

end XiPrime
end Zeta23
