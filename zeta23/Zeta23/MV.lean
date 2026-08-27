/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/MV.lean — the Montgomery–Vaughan weighted Hilbert inequality: literature (diagonal, y = x)
form ⇒ the bilinear (x, z) form H-MV of Zeta23/Hypotheses.lean.

Purpose (trust reduction): Zeta23.MVHilbert C — what [prop:PP]/[prop:cross] consume —
is the BILINEAR inequality |Σ_{r≠s} x_r z̄_s/(λ_r−λ_s)| ≤ C (Σ|x_r|²/δ_r)^{1/2} (Σ|z_r|²/δ_r)^{1/2}.
The published theorem is the case z = x.  The paper, [lem:MV] and its proof,
verbatim: "Lemma (Montgomery–Vaughan). Let λ_1,…,λ_R be distinct real numbers and
δ_r := min_{s≠r}|λ_r−λ_s|. Then for all complex x_r, z_r,
  |Σ_{r≠s} x_r z̄_s/(λ_r−λ_s)| ≤ (3π/2)(Σ_r |x_r|²/δ_r)^{1/2}(Σ_r |z_r|²/δ_r)^{1/2}.
Proof. For z = x this is the weighted ("generalised") Hilbert inequality of Montgomery and Vaughan
[MV74, Theorem 2]; see also [Mon94, Chapter 7]. Any absolute constant in place of 3π/2 would
suffice below. In general, let H be the Hermitian matrix with entries i/(λ_r−λ_s) off the
diagonal and 0 on it, and Δ := diag(δ_r^{1/2}). The case z = x says |y*(ΔHΔ)y| ≤ (3π/2)‖y‖₂² for
all y, i.e. ‖ΔHΔ‖ ≤ 3π/2 since ΔHΔ is Hermitian; hence
|x*Hz| = |(Δ⁻¹x)*(ΔHΔ)(Δ⁻¹z)| ≤ (3π/2)‖Δ⁻¹x‖₂‖Δ⁻¹z‖₂."

Literature statement transcribed (H. L. Montgomery and R. C. Vaughan, "Hilbert's inequality",
J. London Math. Soc. (2) 8 (1974), 73–82, Theorem 2 = the "generalised" weighted form, their
(1.8)): if λ_1,…,λ_R are distinct reals, δ_r := min_{s≠r}|λ_r − λ_s|, then for all complex x_r,
  |Σ_{r≠s} x_r x̄_s / (λ_r − λ_s)| ≤ (3π/2) Σ_r |x_r|²/δ_r.
(The constant 3π/2 was later improved — Preissmann 1984 — but the paper says any absolute
constant suffices, and the headline result only needs ∃ C, so C is kept abstract: MVDiag C.)
As in Zeta23.MVHilbert we allow any admissible δ (δ_r > 0, δ_r ≤ |λ_r − λ_s| for s ≠ r); the right
side is antitone in δ, so this is equivalent to the min-gap δ of the literature.

We derive the bilinear form with constant 2C (not C) by POLARIZATION of the sesquilinear form plus
the scaling x ↦ t x, z ↦ z/t — an elementary route that avoids operator norms; the factor 2 is
immaterial (∃ C).  Result: Zeta23.MVHilbert_of_diag : 0 ≤ C → MVDiag C → MVHilbert (2 * C), and
Zeta23.exists_MVHilbert_of_diag for the ∃-forms used by PaperInputs.MV.
-/
import Zeta23.Hypotheses
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Zeta23

/-- **MV74 Theorem 2 (weighted Hilbert inequality), literature = diagonal form**, with an
abstract absolute constant C (MV74: C = 3π/2): for distinct real frequencies λ_r and admissible
gaps δ_r (0 < δ_r ≤ |λ_r − λ_s| for all s ≠ r), and all complex x_r,
  |Σ_{r≠s} x_r x̄_s/(λ_r − λ_s)| ≤ C · Σ_r |x_r|²/δ_r.
Same binder shape as Zeta23.MVHilbert with z := x. -/
def MVDiag (C : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (freq δ : ι → ℝ) (x : ι → ℂ),
    Function.Injective freq → (∀ r, 0 < δ r) → (∀ r s, r ≠ s → δ r ≤ |freq r - freq s|) →
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else x r * conj (x s) / ((freq r - freq s : ℝ) : ℂ)‖
      ≤ C * ∑ r, ‖x r‖ ^ 2 / δ r

namespace MV

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The sesquilinear form B(x,z) := Σ_{r≠s} x_r z̄_s/(λ_r−λ_s), written with a coefficient
c_{rs} (0 on the diagonal) so that (bi)linearity is by ring. -/
def coef (freq : ι → ℝ) (r s : ι) : ℂ :=
  if r = s then 0 else (((freq r - freq s : ℝ) : ℂ))⁻¹

def B (freq : ι → ℝ) (x z : ι → ℂ) : ℂ := ∑ r, ∑ s, x r * conj (z s) * coef freq r s

/-- the weighted ℓ² quantity Σ |x_r|²/δ_r. -/
def N2 (δ : ι → ℝ) (x : ι → ℂ) : ℝ := ∑ r, ‖x r‖ ^ 2 / δ r

lemma sum_eq_B (freq : ι → ℝ) (x z : ι → ℂ) :
    (∑ r, ∑ s, if r = s then (0 : ℂ) else x r * conj (z s) / ((freq r - freq s : ℝ) : ℂ))
      = B freq x z := by
  unfold B coef
  refine sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
  split_ifs <;> simp [div_eq_mul_inv]

/-- Polarization, termwise (sesquilinear, two index slots):
4 a b̄' = (a+b)(a'+b')^* − (a−b)(a'−b')^* + i(a+ib)(a'+ib')^* − i(a−ib)(a'−ib')^*. -/
lemma polar_term (a b a' b' : ℂ) :
    a * conj b' = (1 / 4 : ℂ) * ((a + b) * conj (a' + b') - (a - b) * conj (a' - b')
      + I * ((a + I * b) * conj (a' + I * b')) - I * ((a - I * b) * conj (a' - I * b'))) := by
  simp only [map_add, map_sub, map_mul, Complex.conj_I]
  have hI : I * I = -1 := Complex.I_mul_I
  linear_combination ((1/2 : ℂ) * a * conj b' - (1/2 : ℂ) * b * conj a') * hI

/-- Polarization of B. -/
lemma B_polar (freq : ι → ℝ) (x z : ι → ℂ) :
    B freq x z = (1 / 4 : ℂ) * (B freq (x + z) (x + z) - B freq (x - z) (x - z)
      + I * B freq (x + I • z) (x + I • z) - I * B freq (x - I • z) (x - I • z)) := by
  unfold B
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sum, ← sum_sub_distrib,
    ← sum_add_distrib]
  refine sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
  rw [polar_term (x r) (z r) (x s) (z s)]
  ring

omit [DecidableEq ι] in
/-- The weighted norms of the four polarization vectors add up to 4(N2 x + N2 z)
(parallelogram law in ℂ, termwise). -/
lemma N2_polar (δ : ι → ℝ) (x z : ι → ℂ) :
    N2 δ (x + z) + N2 δ (x - z) + N2 δ (x + I • z) + N2 δ (x - I • z)
      = 4 * (N2 δ x + N2 δ z) := by
  unfold N2
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun r _ => ?_
  have h1 := parallelogram_law_with_norm ℝ (x r) (z r)
  have h2 := parallelogram_law_with_norm ℝ (x r) (I * z r)
  have hI : ‖I * z r‖ = ‖z r‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  rw [hI] at h2
  have key : ‖x r + z r‖ ^ 2 + ‖x r - z r‖ ^ 2 + ‖x r + I * z r‖ ^ 2 + ‖x r - I * z r‖ ^ 2
      = 4 * (‖x r‖ ^ 2 + ‖z r‖ ^ 2) := by
    simp only [sq]; linarith [h1, h2]
  rw [show (4:ℝ) * (‖x r‖ ^ 2 / δ r + ‖z r‖ ^ 2 / δ r) = (4 * (‖x r‖ ^ 2 + ‖z r‖ ^ 2)) / δ r by
    ring, ← key]
  ring

omit [DecidableEq ι] in
lemma N2_nonneg {δ : ι → ℝ} (hδ : ∀ r, 0 < δ r) (x : ι → ℂ) : 0 ≤ N2 δ x :=
  sum_nonneg fun r _ => div_nonneg (sq_nonneg _) (hδ r).le

omit [DecidableEq ι] in
lemma eq_zero_of_N2_eq_zero {δ : ι → ℝ} (hδ : ∀ r, 0 < δ r) {x : ι → ℂ} (h : N2 δ x = 0) :
    x = 0 := by
  unfold N2 at h
  have := (sum_eq_zero_iff_of_nonneg (fun r _ => div_nonneg (sq_nonneg _) (hδ r).le)).mp h
  funext r
  have hr := this r (mem_univ r)
  rw [div_eq_zero_iff] at hr
  rcases hr with hr | hr
  · exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hr)
  · exact absurd hr (hδ r).ne'

lemma B_zero_left (freq : ι → ℝ) (z : ι → ℂ) : B freq 0 z = 0 := by simp [B]
lemma B_zero_right (freq : ι → ℝ) (x : ι → ℂ) : B freq x 0 = 0 := by simp [B]

/-- Scaling invariance: B(t x, t⁻¹ z) = B(x, z) for real t ≠ 0. -/
lemma B_scale (freq : ι → ℝ) (x z : ι → ℂ) {t : ℝ} (ht : t ≠ 0) :
    B freq ((t : ℂ) • x) ((t⁻¹ : ℝ) • z) = B freq x z := by
  unfold B
  refine sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul, map_mul, Complex.conj_ofReal]
  have : (t : ℂ) * ((t⁻¹ : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ht)]
  linear_combination (x r * conj (z s) * coef freq r s) * this

omit [DecidableEq ι] in
lemma N2_scale (δ : ι → ℝ) (x : ι → ℂ) (t : ℝ) :
    N2 δ ((t : ℂ) • x) = t ^ 2 * N2 δ x := by
  unfold N2
  rw [mul_sum]
  refine sum_congr rfl fun r _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]
  ring

omit [DecidableEq ι] in
lemma N2_real_smul (δ : ι → ℝ) (x : ι → ℂ) (t : ℝ) :
    N2 δ (t • x) = t ^ 2 * N2 δ x := by
  have : (t • x) = ((t : ℂ) • x) := by funext r; simp [Complex.real_smul]
  rw [this, N2_scale]

/-- Step 1: from the diagonal bound, |B(x,z)| ≤ C (N2 x + N2 z). -/
lemma norm_B_le_add {C : ℝ} (_hC : 0 ≤ C) {freq δ : ι → ℝ}
    (hdiag : ∀ y : ι → ℂ, ‖B freq y y‖ ≤ C * N2 δ y) (x z : ι → ℂ) :
    ‖B freq x z‖ ≤ C * (N2 δ x + N2 δ z) := by
  rw [B_polar]
  have h4 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
  calc ‖(1 / 4 : ℂ) * (B freq (x + z) (x + z) - B freq (x - z) (x - z)
        + I * B freq (x + I • z) (x + I • z) - I * B freq (x - I • z) (x - I • z))‖
      ≤ (1 / 4) * (‖B freq (x + z) (x + z)‖ + ‖B freq (x - z) (x - z)‖
        + ‖B freq (x + I • z) (x + I • z)‖ + ‖B freq (x - I • z) (x - I • z)‖) := by
        rw [norm_mul, h4]
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        · refine (norm_add_le _ _).trans ?_
          gcongr
          · exact norm_sub_le _ _
          · rw [norm_mul, Complex.norm_I, one_mul]
        · rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ (1 / 4) * (C * N2 δ (x + z) + C * N2 δ (x - z) + C * N2 δ (x + I • z)
        + C * N2 δ (x - I • z)) := by gcongr <;> exact hdiag _
    _ = C * (N2 δ x + N2 δ z) := by
        have := N2_polar δ x z
        linear_combination (C / 4) * this

/-- Step 2: scaling + AM–GM turn C(N2 x + N2 z) into 2C √(N2 x) √(N2 z). -/
lemma norm_B_le_sqrt {C : ℝ} (hC : 0 ≤ C) {freq δ : ι → ℝ} (hδ : ∀ r, 0 < δ r)
    (hdiag : ∀ y : ι → ℂ, ‖B freq y y‖ ≤ C * N2 δ y) (x z : ι → ℂ) :
    ‖B freq x z‖ ≤ 2 * C * Real.sqrt (N2 δ x) * Real.sqrt (N2 δ z) := by
  set u := Real.sqrt (N2 δ x) with hu
  set v := Real.sqrt (N2 δ z) with hv
  have hNx := N2_nonneg hδ x
  have hNz := N2_nonneg hδ z
  by_cases hx0 : N2 δ x = 0
  · rw [eq_zero_of_N2_eq_zero hδ hx0, B_zero_left, norm_zero]; positivity
  by_cases hz0 : N2 δ z = 0
  · rw [eq_zero_of_N2_eq_zero hδ hz0, B_zero_right, norm_zero]; positivity
  have hu0 : 0 < u := Real.sqrt_pos.mpr (lt_of_le_of_ne hNx (Ne.symm hx0))
  have hv0 : 0 < v := Real.sqrt_pos.mpr (lt_of_le_of_ne hNz (Ne.symm hz0))
  have hu2 : u ^ 2 = N2 δ x := Real.sq_sqrt hNx
  have hv2 : v ^ 2 = N2 δ z := Real.sq_sqrt hNz
  -- t with t² = v/u
  set t := Real.sqrt (v / u) with htdef
  have ht2 : t ^ 2 = v / u := Real.sq_sqrt (by positivity)
  have ht0 : 0 < t := Real.sqrt_pos.mpr (by positivity)
  have hscale := B_scale freq x z ht0.ne'
  rw [← hscale]
  refine (norm_B_le_add hC hdiag _ _).trans ?_
  rw [N2_scale, N2_real_smul, inv_pow, ht2, ← hu2, ← hv2]
  have : v / u * u ^ 2 + (v / u)⁻¹ * v ^ 2 = 2 * (u * v) := by
    field_simp
    ring
  rw [this]
  exact le_of_eq (by ring)

end MV

/-- **Bilinear Montgomery–Vaughan from the literature form**: MVDiag C ⇒ MVHilbert (2C)
(the paper's [lem:MV] "In general …" step, here via polarization + scaling instead of the
operator norm of ΔHΔ; constant 2C instead of C, immaterial for ∃C). -/
theorem MVHilbert_of_diag {C : ℝ} (hC : 0 ≤ C) (h : MVDiag C) : MVHilbert (2 * C) := by
  intro ι _ _ freq δ x z hinj hδ hsep
  rw [MV.sum_eq_B]
  have hdiag : ∀ y : ι → ℂ, ‖MV.B freq y y‖ ≤ C * MV.N2 δ y := by
    intro y
    have := h ι freq δ y hinj hδ hsep
    rw [MV.sum_eq_B] at this
    exact this
  exact MV.norm_B_le_sqrt hC hδ hdiag x z

/-- ∃-form, matching PaperInputs.MV's shape: (∃ C > 0, MVDiag C) → (∃ C > 0, MVHilbert C). -/
theorem exists_MVHilbert_of_diag (h : ∃ C : ℝ, 0 < C ∧ MVDiag C) :
    ∃ C : ℝ, 0 < C ∧ MVHilbert C := by
  obtain ⟨C, hC, hd⟩ := h
  exact ⟨2 * C, by positivity, MVHilbert_of_diag hC.le hd⟩

end Zeta23
