/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib

/-!
# MV step 0 — spacing lemmas for admissible weights

For an injective `freq : ι → ℝ` on a finite index type with ADMISSIBLE weights `δ`
(`0 < δ r` and `δ r ≤ |freq r − freq s|` for all `s ≠ r` — the shape of Zeta23.MVHilbert),
the open intervals `I_t = (freq t − δ t/2, freq t + δ t/2)` are pairwise disjoint, giving
by comparison with `∫ |u − freq s|^{−σ} du`:

* `spacing_sq`   (σ = 2):  Σ_{t≠s} δ t/(freq s − freq t)²  ≤  9/δ s
* `spacing_four` (σ = 4):  Σ_{t≠s} δ t/(freq s − freq t)⁴  ≤  27/(δ s)³
* `two_point`:  Σ_{k≠ℓ,m} δ k/((freq k − freq ℓ)²(freq k − freq m)²)
                  ≤ 36(δ ℓ + δ m)/(δ ℓ · δ m · (freq ℓ − freq m)²)

These replace [Preissmann 1984, Lemmes 1 & 6] (cited without proof in arXiv:2203.14950)
with elementary arguments at worse constants — sufficient for the ∃C form.
-/

noncomputable section
open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace MV

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Admissibility of weights (matches Zeta23.MVHilbert's hypotheses). -/
structure Adm (freq δ : ι → ℝ) : Prop where
  inj : Function.Injective freq
  pos : ∀ r, 0 < δ r
  le : ∀ r s, r ≠ s → δ r ≤ |freq r - freq s|

namespace Adm

variable {freq δ : ι → ℝ} (h : Adm freq δ)

/-- The interval `I_t`. -/
def itv (t : ι) : Set ℝ := Set.Ioo (freq t - δ t / 2) (freq t + δ t / 2)

omit [Fintype ι] [DecidableEq ι] in
/-- Centers are far apart: `(δ t + δ t')/2 ≤ |freq t − freq t'|` for `t ≠ t'`. -/
lemma centers_far (h : Adm freq δ) {t t' : ι} (htt : t ≠ t') :
    (δ t + δ t') / 2 ≤ |freq t - freq t'| := by
  have h1 := h.le t t' htt
  have h2 := h.le t' t htt.symm
  rw [abs_sub_comm] at h2
  rcases le_total (δ t) (δ t') with hd | hd <;> linarith

/-- The intervals are pairwise disjoint. -/
lemma itv_disjoint (h : Adm freq δ) :
    Set.univ.PairwiseDisjoint (fun t : ι => Adm.itv (freq := freq) (δ := δ) t) := by
  intro t _ t' _ htt
  have hfar := h.centers_far htt
  rw [Function.onFun, Set.disjoint_left]
  intro u hu hu'
  simp only [Adm.itv, Set.mem_Ioo] at hu hu'
  rcases abs_cases (freq t - freq t') with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hfar <;>
    linarith [hu.1, hu.2, hu'.1, hu'.2]

omit [Fintype ι] [DecidableEq ι] in
/-- For `u ∈ I_t`, `t ≠ s`: `|freq s − u| ≤ (3/2)|freq s − freq t|` and `δ s/2 ≤ |u − freq s|`. -/
lemma abs_le_of_mem_itv (h : Adm freq δ) {s t : ι} (hts : t ≠ s) {u : ℝ}
    (hu : u ∈ Adm.itv (freq := freq) (δ := δ) t) :
    |freq s - u| ≤ 3 / 2 * |freq s - freq t| ∧ δ s / 2 ≤ |u - freq s| := by
  simp only [Adm.itv, Set.mem_Ioo] at hu
  have hut : |u - freq t| ≤ δ t / 2 := by rw [abs_le]; constructor <;> linarith
  have hst : δ t ≤ |freq s - freq t| := by rw [abs_sub_comm]; exact h.le t s hts
  have hss : δ s ≤ |freq s - freq t| := h.le s t (Ne.symm hts)
  constructor
  · calc |freq s - u| = |(freq s - freq t) + (freq t - u)| := by ring_nf
      _ ≤ |freq s - freq t| + |freq t - u| := abs_add_le _ _
      _ = |freq s - freq t| + |u - freq t| := by rw [abs_sub_comm (freq t) u]
      _ ≤ |freq s - freq t| + δ t / 2 := by linarith
      _ ≤ 3 / 2 * |freq s - freq t| := by linarith
  · have key : |freq s - freq t| ≤ |freq s - u| + |u - freq t| := by
      calc |freq s - freq t| = |(freq s - u) + (u - freq t)| := by ring_nf
        _ ≤ |freq s - u| + |u - freq t| := abs_add_le _ _
    rw [abs_sub_comm u (freq s)]
    linarith

/-- Closed-form tail integrals: `∫_{Icc a b} (u−c)⁻² du = (a−c)⁻¹ − (b−c)⁻¹` for `c ∉ [a,b]`. -/
lemma integral_inv_sq_Icc {a b c : ℝ} (hab : a ≤ b) (hc : c < a ∨ b < c) :
    ∫ u in Set.Icc a b, ((u - c) ^ 2)⁻¹ = (a - c)⁻¹ - (b - c)⁻¹ := by
  have h0 : (0:ℝ) ∉ Set.uIcc (a - c) (b - c) := by
    rw [Set.mem_uIcc]
    rcases hc with hc | hc
    · push Not; constructor <;> intro <;> nlinarith
    · push Not; constructor <;> intro <;> nlinarith
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have e1 : ∀ u : ℝ, ((u - c) ^ 2)⁻¹ = (u - c) ^ (-2 : ℤ) := by
    intro u; rw [zpow_neg]; norm_cast
  simp_rw [e1]
  rw [intervalIntegral.integral_comp_sub_right (fun x => x ^ (-2:ℤ)) c,
    integral_zpow (Or.inr ⟨by norm_num, h0⟩)]
  norm_num [zpow_neg]
  ring

/-- `∫_{Icc a b} (u−c)⁻⁴ du = ((a−c)⁻³ − (b−c)⁻³)/3` for `c ∉ [a,b]`. -/
lemma integral_inv_four_Icc {a b c : ℝ} (hab : a ≤ b) (hc : c < a ∨ b < c) :
    ∫ u in Set.Icc a b, ((u - c) ^ 4)⁻¹ = ((a - c) ^ (3:ℕ))⁻¹ / 3 - ((b - c) ^ (3:ℕ))⁻¹ / 3 := by
  have h0 : (0:ℝ) ∉ Set.uIcc (a - c) (b - c) := by
    rw [Set.mem_uIcc]
    rcases hc with hc | hc
    · push Not; constructor <;> intro <;> nlinarith
    · push Not; constructor <;> intro <;> nlinarith
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have e1 : ∀ u : ℝ, ((u - c) ^ 4)⁻¹ = (u - c) ^ (-4 : ℤ) := by
    intro u; rw [zpow_neg]; norm_cast
  simp_rw [e1]
  rw [intervalIntegral.integral_comp_sub_right (fun x => x ^ (-4:ℤ)) c,
    integral_zpow (Or.inr ⟨by norm_num, h0⟩)]
  norm_num [zpow_neg]
  norm_cast
  push_cast
  set A := ((b - c) ^ (3:ℕ))⁻¹
  set B := ((a - c) ^ (3:ℕ))⁻¹
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- Closed-interval version of the membership bounds (for use on closures `J t`). -/
lemma abs_bounds_closed (h : Adm freq δ) {s t : ι} (hts : t ≠ s) {u : ℝ}
    (hut : |u - freq t| ≤ δ t / 2) :
    |freq s - u| ≤ 3 / 2 * |freq s - freq t| ∧ δ s / 2 ≤ |u - freq s| := by
  have hst : δ t ≤ |freq s - freq t| := by rw [abs_sub_comm]; exact h.le t s hts
  have hss : δ s ≤ |freq s - freq t| := h.le s t (Ne.symm hts)
  constructor
  · calc |freq s - u| = |(freq s - freq t) + (freq t - u)| := by ring_nf
      _ ≤ |freq s - freq t| + |freq t - u| := abs_add_le _ _
      _ = |freq s - freq t| + |u - freq t| := by rw [abs_sub_comm (freq t) u]
      _ ≤ |freq s - freq t| + δ t / 2 := by linarith
      _ ≤ 3 / 2 * |freq s - freq t| := by linarith
  · have key : |freq s - freq t| ≤ |freq s - u| + |u - freq t| := by
      calc |freq s - freq t| = |(freq s - u) + (u - freq t)| := by ring_nf
        _ ≤ |freq s - u| + |u - freq t| := abs_add_le _ _
    rw [abs_sub_comm u (freq s)]
    linarith

section MainSpacing
variable (h : Adm freq δ) (s : ι)

/-- The two-sided tail window around `freq s`, radius `R`. -/
private def window (freq δ : ι → ℝ) (s : ι) (R : ℝ) : Set ℝ :=
  Set.Icc (freq s - R) (freq s - δ s / 2) ∪ Set.Icc (freq s + δ s / 2) (freq s + R)

private lemma mem_window (h : Adm freq δ) {s t : ι} (hts : t ≠ s) {R : ℝ}
    (hR : 3 / 2 * |freq s - freq t| ≤ R) {u : ℝ}
    (hu : u ∈ Adm.itv (freq := freq) (δ := δ) t) : u ∈ window freq δ s R := by
  have hb := h.abs_le_of_mem_itv hts hu
  have h1 : |u - freq s| ≤ R := by
    rw [abs_sub_comm]; exact hb.1.trans hR
  rcases le_total u (freq s) with hle | hle
  · left
    rw [abs_of_nonpos (by linarith : u - freq s ≤ 0)] at h1
    rw [abs_of_nonpos (by linarith : u - freq s ≤ 0)] at hb
    exact ⟨by linarith, by linarith [hb.2]⟩
  · right
    rw [abs_of_nonneg (by linarith : 0 ≤ u - freq s)] at h1
    rw [abs_of_nonneg (by linarith : 0 ≤ u - freq s)] at hb
    exact ⟨by linarith [hb.2], by linarith⟩

omit [Fintype ι] [DecidableEq ι] in
private lemma window_integrable {s : ι} {R : ℝ} (hδs : 0 < δ s) {k : ℕ} (_hk : k ≠ 0) :
    MeasureTheory.IntegrableOn (fun u => ((u - freq s) ^ k)⁻¹) (window freq δ s R) := by
  have hcompact : IsCompact (window freq δ s R) := (isCompact_Icc).union isCompact_Icc
  refine ContinuousOn.integrableOn_compact hcompact ?_
  have hne : ∀ u ∈ window freq δ s R, (u - freq s) ^ k ≠ 0 := by
    intro u hu
    apply pow_ne_zero
    rcases hu with hu | hu
    · simp only [Set.mem_Icc] at hu; intro hh; nlinarith [hu.2]
    · simp only [Set.mem_Icc] at hu; intro hh; nlinarith [hu.1]
  exact ((continuous_sub_right (freq s)).pow k).continuousOn.inv₀ hne

/-- **Spacing lemma, σ = 2**: `Σ_{t≠s} δ t/(freq s − freq t)² ≤ 9/δ s`. -/
theorem spacing_sq (h : Adm freq δ) (s : ι) :
    ∑ t ∈ Finset.univ.erase s, δ t / (freq s - freq t) ^ 2 ≤ 9 / δ s := by
  classical
  have hδs := h.pos s
  rcases Finset.eq_empty_or_nonempty (Finset.univ.erase s) with he | hne
  · rw [he, Finset.sum_empty]; positivity
  obtain ⟨t₀, ht₀⟩ := hne
  set g : ℝ → ℝ := fun u => ((u - freq s) ^ 2)⁻¹ with hg
  set M : ℝ := Finset.univ.sup' ⟨s, Finset.mem_univ s⟩ (fun t => |freq s - freq t|) with hM
  set R : ℝ := 3 / 2 * M + 1 with hR
  have hMle : ∀ t : ι, |freq s - freq t| ≤ M := fun t =>
    Finset.le_sup' (fun r => |freq s - freq r|) (Finset.mem_univ t)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hMle s)
  have hδM : δ s ≤ M := (h.le s t₀ (Finset.ne_of_mem_erase ht₀).symm).trans (hMle t₀)
  have hRδ : δ s / 2 ≤ R := by linarith
  -- integrability on the window
  have hintW : MeasureTheory.IntegrableOn g (window freq δ s R) :=
    window_integrable (freq := freq) (δ := δ) hδs two_ne_zero
  -- each interval sits in the window
  have hsub : ∀ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t ⊆ window freq δ s R := by
    intro t ht u hu
    exact mem_window h (Finset.ne_of_mem_erase ht) (by linarith [hMle t]) hu
  -- per-term comparison
  have hper : ∀ t ∈ Finset.univ.erase s, δ t / (freq s - freq t) ^ 2
      ≤ 9 / 4 * ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u := by
    intro t ht
    have hts : t ≠ s := Finset.ne_of_mem_erase ht
    have hfst : (freq s - freq t) ≠ 0 := sub_ne_zero.2 fun hh => hts (h.inj hh.symm)
    have hpos2 : 0 < (freq s - freq t) ^ 2 := pow_two_pos_of_ne_zero hfst
    have hδt := h.pos t
    have hlow : ∀ u ∈ Adm.itv (freq := freq) (δ := δ) t,
        (9 / 4 * (freq s - freq t) ^ 2)⁻¹ ≤ g u := by
      intro u hu
      have hb := h.abs_le_of_mem_itv hts hu
      have hu0 : 0 < |u - freq s| := lt_of_lt_of_le (by linarith) hb.2
      have hsq : (u - freq s) ^ 2 ≤ 9 / 4 * (freq s - freq t) ^ 2 := by
        have h1 : |u - freq s| ≤ 3 / 2 * |freq s - freq t| := by
          rw [abs_sub_comm]; exact hb.1
        calc (u - freq s) ^ 2 = |u - freq s| ^ 2 := (sq_abs _).symm
          _ ≤ (3 / 2 * |freq s - freq t|) ^ 2 := by gcongr
          _ = 9 / 4 * |freq s - freq t| ^ 2 := by ring
          _ = 9 / 4 * (freq s - freq t) ^ 2 := by rw [sq_abs]
      have hupos : 0 < (u - freq s) ^ 2 := pow_two_pos_of_ne_zero (abs_pos.1 hu0)
      show _ ≤ ((u - freq s) ^ 2)⁻¹
      exact (inv_le_inv₀ (by positivity) hupos).2 hsq
    have hintT : MeasureTheory.IntegrableOn g (Adm.itv (freq := freq) (δ := δ) t) :=
      hintW.mono_set (hsub t ht)
    have h1 : ∫ _u in Adm.itv (freq := freq) (δ := δ) t, (9 / 4 * (freq s - freq t) ^ 2)⁻¹
        ≤ ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u := by
      apply MeasureTheory.setIntegral_mono_on
      · exact MeasureTheory.integrableOn_const (by simp [Adm.itv])
      · exact hintT
      · exact measurableSet_Ioo
      · exact hlow
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at h1
    have hvol : (volume (Adm.itv (freq := freq) (δ := δ) t)).toReal = δ t := by
      rw [Adm.itv, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [MeasureTheory.measureReal_def, hvol] at h1
    calc δ t / (freq s - freq t) ^ 2
        = 9 / 4 * (δ t * (9 / 4 * (freq s - freq t) ^ 2)⁻¹) := by
          field_simp
      _ ≤ 9 / 4 * ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u := by
          gcongr
  -- sum the comparisons, merge the disjoint intervals, pass to the window
  have hdisj : (↑(Finset.univ.erase s) : Set ι).PairwiseDisjoint
      (fun t => Adm.itv (freq := freq) (δ := δ) t) :=
    (h.itv_disjoint).subset (Set.subset_univ _)
  have hsum : ∑ t ∈ Finset.univ.erase s, ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u
      = ∫ u in ⋃ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t, g u := by
    rw [MeasureTheory.integral_biUnion_finset]
    · exact fun t _ => measurableSet_Ioo
    · exact hdisj
    · exact fun t ht => hintW.mono_set (hsub t ht)
  have hUsub : (⋃ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t)
      ⊆ window freq δ s R := by
    simp only [Set.iUnion_subset_iff]
    exact fun t ht => hsub t ht
  have hUmono : ∫ u in ⋃ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t, g u
      ≤ ∫ u in window freq δ s R, g u := by
    apply MeasureTheory.setIntegral_mono_set hintW
    · exact Filter.Eventually.of_forall fun u => by positivity
    · exact Filter.Eventually.of_forall hUsub
  -- evaluate the window integral
  have hwindow : ∫ u in window freq δ s R, g u ≤ 4 / δ s := by
    have hd : Disjoint (Set.Icc (freq s - R) (freq s - δ s / 2))
        (Set.Icc (freq s + δ s / 2) (freq s + R)) := by
      rw [Set.disjoint_left]
      intro u hu hu'
      simp only [Set.mem_Icc] at hu hu'
      linarith [hu.2, hu'.1]
    have hil : MeasureTheory.IntegrableOn g (Set.Icc (freq s - R) (freq s - δ s / 2)) :=
      hintW.mono_set Set.subset_union_left
    have hir : MeasureTheory.IntegrableOn g (Set.Icc (freq s + δ s / 2) (freq s + R)) :=
      hintW.mono_set Set.subset_union_right
    rw [window, MeasureTheory.setIntegral_union hd measurableSet_Icc hil hir]
    have hleft : ∫ u in Set.Icc (freq s - R) (freq s - δ s / 2), g u
        = (- R)⁻¹ + (δ s / 2)⁻¹ := by
      rw [hg]
      rw [integral_inv_sq_Icc (by linarith) (Or.inr (by linarith))]
      have e1 : freq s - R - freq s = -R := by ring
      have e2 : freq s - δ s / 2 - freq s = -(δ s / 2) := by ring
      rw [e1, e2]
      rw [inv_neg]
      ring
    have hright : ∫ u in Set.Icc (freq s + δ s / 2) (freq s + R), g u
        = (δ s / 2)⁻¹ - R⁻¹ := by
      rw [hg]
      rw [integral_inv_sq_Icc (by linarith) (Or.inl (by linarith))]
      have e1 : freq s + δ s / 2 - freq s = δ s / 2 := by ring
      have e2 : freq s + R - freq s = R := by ring
      rw [e1, e2]
    rw [hleft, hright]
    have hR0 : 0 < R := by linarith
    have : (δ s / 2)⁻¹ = 2 / δ s := by field_simp
    rw [this, inv_neg]
    have hRi : 0 < R⁻¹ := by positivity
    have h4 : 4 / δ s = 2 / δ s + 2 / δ s := by ring
    linarith
  -- assemble
  calc ∑ t ∈ Finset.univ.erase s, δ t / (freq s - freq t) ^ 2
      ≤ ∑ t ∈ Finset.univ.erase s, 9 / 4 * ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u :=
        Finset.sum_le_sum hper
    _ = 9 / 4 * ∑ t ∈ Finset.univ.erase s, ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u := by
        rw [Finset.mul_sum]
    _ = 9 / 4 * ∫ u in ⋃ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t, g u := by
        rw [hsum]
    _ ≤ 9 / 4 * (4 / δ s) := by
        have := hUmono.trans hwindow
        gcongr
    _ = 9 / δ s := by field_simp

end MainSpacing


/-- **Spacing lemma, σ = 4**: `Σ_{t≠s} δ t/(freq s − freq t)⁴ ≤ 27/(δ s)³`. -/
theorem spacing_four (h : Adm freq δ) (s : ι) :
    ∑ t ∈ Finset.univ.erase s, δ t / (freq s - freq t) ^ 4 ≤ 27 / δ s ^ 3 := by
  classical
  have hδs := h.pos s
  rcases Finset.eq_empty_or_nonempty (Finset.univ.erase s) with he | hne
  · rw [he, Finset.sum_empty]; positivity
  obtain ⟨t₀, ht₀⟩ := hne
  set g : ℝ → ℝ := fun u => ((u - freq s) ^ 4)⁻¹ with hg
  set M : ℝ := Finset.univ.sup' ⟨s, Finset.mem_univ s⟩ (fun t => |freq s - freq t|) with hM
  set R : ℝ := 3 / 2 * M + 1 with hR
  have hMle : ∀ t : ι, |freq s - freq t| ≤ M := fun t =>
    Finset.le_sup' (fun r => |freq s - freq r|) (Finset.mem_univ t)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hMle s)
  have hδM : δ s ≤ M := (h.le s t₀ (Finset.ne_of_mem_erase ht₀).symm).trans (hMle t₀)
  have hRδ : δ s / 2 ≤ R := by linarith
  have hintW : MeasureTheory.IntegrableOn g (window freq δ s R) :=
    window_integrable (freq := freq) (δ := δ) hδs four_ne_zero
  have hsub : ∀ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t ⊆ window freq δ s R := by
    intro t ht u hu
    exact mem_window h (Finset.ne_of_mem_erase ht) (by linarith [hMle t]) hu
  have hper : ∀ t ∈ Finset.univ.erase s, δ t / (freq s - freq t) ^ 4
      ≤ 81 / 16 * ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u := by
    intro t ht
    have hts : t ≠ s := Finset.ne_of_mem_erase ht
    have hfst : (freq s - freq t) ≠ 0 := sub_ne_zero.2 fun hh => hts (h.inj hh.symm)
    have hpos4 : 0 < (freq s - freq t) ^ 4 := by positivity
    have hδt := h.pos t
    have hlow : ∀ u ∈ Adm.itv (freq := freq) (δ := δ) t,
        (81 / 16 * (freq s - freq t) ^ 4)⁻¹ ≤ g u := by
      intro u hu
      have hb := h.abs_le_of_mem_itv hts hu
      have hu0 : 0 < |u - freq s| := lt_of_lt_of_le (by linarith) hb.2
      have hsq : (u - freq s) ^ 4 ≤ 81 / 16 * (freq s - freq t) ^ 4 := by
        have h1 : |u - freq s| ≤ 3 / 2 * |freq s - freq t| := by
          rw [abs_sub_comm]; exact hb.1
        calc (u - freq s) ^ 4 = |u - freq s| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
          _ ≤ (3 / 2 * |freq s - freq t|) ^ 4 := by gcongr
          _ = 81 / 16 * |freq s - freq t| ^ 4 := by ring
          _ = 81 / 16 * (freq s - freq t) ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
      have hupos : 0 < (u - freq s) ^ 4 := by
        have := abs_pos.1 hu0; positivity
      show _ ≤ ((u - freq s) ^ 4)⁻¹
      exact (inv_le_inv₀ (by positivity) hupos).2 hsq
    have hintT : MeasureTheory.IntegrableOn g (Adm.itv (freq := freq) (δ := δ) t) :=
      hintW.mono_set (hsub t ht)
    have h1 : ∫ _u in Adm.itv (freq := freq) (δ := δ) t, (81 / 16 * (freq s - freq t) ^ 4)⁻¹
        ≤ ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u := by
      apply MeasureTheory.setIntegral_mono_on
      · exact MeasureTheory.integrableOn_const (by simp [Adm.itv])
      · exact hintT
      · exact measurableSet_Ioo
      · exact hlow
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at h1
    have hvol : (volume (Adm.itv (freq := freq) (δ := δ) t)).toReal = δ t := by
      rw [Adm.itv, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [MeasureTheory.measureReal_def, hvol] at h1
    calc δ t / (freq s - freq t) ^ 4
        = 81 / 16 * (δ t * (81 / 16 * (freq s - freq t) ^ 4)⁻¹) := by
          field_simp
      _ ≤ 81 / 16 * ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u := by
          gcongr
  have hdisj : (↑(Finset.univ.erase s) : Set ι).PairwiseDisjoint
      (fun t => Adm.itv (freq := freq) (δ := δ) t) :=
    (h.itv_disjoint).subset (Set.subset_univ _)
  have hsum : ∑ t ∈ Finset.univ.erase s, ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u
      = ∫ u in ⋃ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t, g u := by
    rw [MeasureTheory.integral_biUnion_finset]
    · exact fun t _ => measurableSet_Ioo
    · exact hdisj
    · exact fun t ht => hintW.mono_set (hsub t ht)
  have hUsub : (⋃ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t)
      ⊆ window freq δ s R := by
    simp only [Set.iUnion_subset_iff]
    exact fun t ht => hsub t ht
  have hUmono : ∫ u in ⋃ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t, g u
      ≤ ∫ u in window freq δ s R, g u := by
    apply MeasureTheory.setIntegral_mono_set hintW
    · exact Filter.Eventually.of_forall fun u => by positivity
    · exact Filter.Eventually.of_forall hUsub
  have hwindow : ∫ u in window freq δ s R, g u ≤ 16 / (3 * δ s ^ 3) := by
    have hd : Disjoint (Set.Icc (freq s - R) (freq s - δ s / 2))
        (Set.Icc (freq s + δ s / 2) (freq s + R)) := by
      rw [Set.disjoint_left]
      intro u hu hu'
      simp only [Set.mem_Icc] at hu hu'
      linarith [hu.2, hu'.1]
    have hil : MeasureTheory.IntegrableOn g (Set.Icc (freq s - R) (freq s - δ s / 2)) :=
      hintW.mono_set Set.subset_union_left
    have hir : MeasureTheory.IntegrableOn g (Set.Icc (freq s + δ s / 2) (freq s + R)) :=
      hintW.mono_set Set.subset_union_right
    rw [window, MeasureTheory.setIntegral_union hd measurableSet_Icc hil hir]
    have hleft : ∫ u in Set.Icc (freq s - R) (freq s - δ s / 2), g u
        = -((R ^ (3:ℕ))⁻¹ / 3) + ((δ s / 2) ^ (3:ℕ))⁻¹ / 3 := by
      rw [hg, integral_inv_four_Icc (by linarith) (Or.inr (by linarith))]
      have e1 : freq s - R - freq s = -R := by ring
      have e2 : freq s - δ s / 2 - freq s = -(δ s / 2) := by ring
      rw [e1, e2]
      have e3 : (-R) ^ (3:ℕ) = -(R ^ (3:ℕ)) := by ring
      have e4 : (-(δ s / 2)) ^ (3:ℕ) = -((δ s / 2) ^ (3:ℕ)) := by ring
      rw [e3, e4, inv_neg, inv_neg]
      ring
    have hright : ∫ u in Set.Icc (freq s + δ s / 2) (freq s + R), g u
        = ((δ s / 2) ^ (3:ℕ))⁻¹ / 3 - (R ^ (3:ℕ))⁻¹ / 3 := by
      rw [hg, integral_inv_four_Icc (by linarith) (Or.inl (by linarith))]
      have e1 : freq s + δ s / 2 - freq s = δ s / 2 := by ring
      have e2 : freq s + R - freq s = R := by ring
      rw [e1, e2]
    rw [hleft, hright]
    have hR0 : 0 < R := by linarith
    have hRi : 0 < (R ^ (3:ℕ))⁻¹ := by positivity
    have hhalf : ((δ s / 2) ^ (3:ℕ))⁻¹ = 8 / δ s ^ 3 := by
      rw [div_pow]
      norm_num
    have h16 : 16 / (3 * δ s ^ 3) = 8 / δ s ^ 3 / 3 + 8 / δ s ^ 3 / 3 := by ring
    rw [hhalf]
    linarith
  calc ∑ t ∈ Finset.univ.erase s, δ t / (freq s - freq t) ^ 4
      ≤ ∑ t ∈ Finset.univ.erase s, 81 / 16 * ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u :=
        Finset.sum_le_sum hper
    _ = 81 / 16 * ∑ t ∈ Finset.univ.erase s, ∫ u in Adm.itv (freq := freq) (δ := δ) t, g u := by
        rw [Finset.mul_sum]
    _ = 81 / 16 * ∫ u in ⋃ t ∈ Finset.univ.erase s, Adm.itv (freq := freq) (δ := δ) t, g u := by
        rw [hsum]
    _ ≤ 81 / 16 * (16 / (3 * δ s ^ 3)) := by
        have := hUmono.trans hwindow
        gcongr
    _ = 27 / δ s ^ 3 := by field_simp; ring

/-- **Two-point lemma** (replaces Preissmann Lemme 6 at constant 36). -/
theorem two_point (h : Adm freq δ) {l m : ι} (hlm : l ≠ m) :
    ∑ k ∈ (Finset.univ.erase l).erase m,
        δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
      ≤ 36 * (δ l + δ m) / (δ l * δ m * (freq l - freq m) ^ 2) := by
  classical
  have hδl := h.pos l
  have hδm := h.pos m
  have hflm : (freq l - freq m) ≠ 0 := sub_ne_zero.2 fun hh => hlm (h.inj hh)
  have hC : 0 < (freq l - freq m) ^ 2 := pow_two_pos_of_ne_zero hflm
  have esq : ∀ x y : ℝ, (x - y) ^ 2 = (y - x) ^ 2 := fun x y => by ring
  have hsplit : ∀ k ∈ (Finset.univ.erase l).erase m,
      δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
        ≤ δ k / (freq l - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2)
          + δ k / (freq m - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2) := by
    intro k hk
    have hkm : k ≠ m := Finset.ne_of_mem_erase hk
    have hkl : k ≠ l := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    have hkl' : (freq k - freq l) ≠ 0 := sub_ne_zero.2 fun hh => hkl (h.inj hh)
    have hkm' : (freq k - freq m) ≠ 0 := sub_ne_zero.2 fun hh => hkm (h.inj hh)
    have hA : 0 < (freq k - freq l) ^ 2 := pow_two_pos_of_ne_zero hkl'
    have hB : 0 < (freq k - freq m) ^ 2 := pow_two_pos_of_ne_zero hkm'
    have hδk := h.pos k
    have htri : |freq l - freq m| ≤ |freq k - freq l| + |freq k - freq m| := by
      calc |freq l - freq m| = |(freq l - freq k) + (freq k - freq m)| := by ring_nf
        _ ≤ |freq l - freq k| + |freq k - freq m| := abs_add_le _ _
        _ = |freq k - freq l| + |freq k - freq m| := by rw [abs_sub_comm (freq l) (freq k)]
    have habs : 0 ≤ |freq l - freq m| := abs_nonneg _
    rcases le_total (|freq l - freq m| / 2) (|freq k - freq m|) with hP | hP
    · -- k far from m: keep the l-factor, crush the m-factor
      have hBC : (freq l - freq m) ^ 2 / 4 ≤ (freq k - freq m) ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hP 2
        rw [div_pow, sq_abs, sq_abs] at this
        linarith
      have key : δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
          ≤ δ k / (freq l - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2) := by
        have h1 : (1:ℝ) / (freq k - freq m) ^ 2 ≤ 4 / (freq l - freq m) ^ 2 := by
          rw [div_le_div_iff₀ hB hC]
          linarith
        have e : δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
            = (δ k / (freq l - freq k) ^ 2) * (1 / (freq k - freq m) ^ 2) := by
          rw [esq (freq k) (freq l), div_mul_eq_div_div, div_eq_mul_one_div]
        rw [e]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have hnn2 : 0 ≤ δ k / (freq m - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2) := by positivity
      linarith
    · -- k far from l
      have hAC : (freq l - freq m) ^ 2 / 4 ≤ (freq k - freq l) ^ 2 := by
        have h2 : |freq l - freq m| / 2 ≤ |freq k - freq l| := by linarith
        have := pow_le_pow_left₀ (by positivity) h2 2
        rw [div_pow, sq_abs, sq_abs] at this
        linarith
      have key : δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
          ≤ δ k / (freq m - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2) := by
        have h1 : (1:ℝ) / (freq k - freq l) ^ 2 ≤ 4 / (freq l - freq m) ^ 2 := by
          rw [div_le_div_iff₀ hA hC]
          linarith
        have e : δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
            = (δ k / (freq m - freq k) ^ 2) * (1 / (freq k - freq l) ^ 2) := by
          rw [mul_comm ((freq k - freq l) ^ 2) ((freq k - freq m) ^ 2),
            esq (freq k) (freq m), div_mul_eq_div_div, div_eq_mul_one_div]
        rw [e]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have hnn2 : 0 ≤ δ k / (freq l - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2) := by positivity
      linarith
  calc ∑ k ∈ (Finset.univ.erase l).erase m,
        δ k / ((freq k - freq l) ^ 2 * (freq k - freq m) ^ 2)
      ≤ ∑ k ∈ (Finset.univ.erase l).erase m,
          (δ k / (freq l - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2)
            + δ k / (freq m - freq k) ^ 2 * (4 / (freq l - freq m) ^ 2)) :=
        Finset.sum_le_sum hsplit
    _ = (∑ k ∈ (Finset.univ.erase l).erase m, δ k / (freq l - freq k) ^ 2)
          * (4 / (freq l - freq m) ^ 2)
        + (∑ k ∈ (Finset.univ.erase l).erase m, δ k / (freq m - freq k) ^ 2)
          * (4 / (freq l - freq m) ^ 2) := by
        rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    _ ≤ (9 / δ l) * (4 / (freq l - freq m) ^ 2) + (9 / δ m) * (4 / (freq l - freq m) ^ 2) := by
        have hsl : ∑ k ∈ (Finset.univ.erase l).erase m, δ k / (freq l - freq k) ^ 2
            ≤ 9 / δ l := by
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
            (fun k hk => Finset.mem_of_mem_erase hk) ?_) (h.spacing_sq l)
          exact fun k _ _ => div_nonneg (h.pos k).le (sq_nonneg _)
        have hsm : ∑ k ∈ (Finset.univ.erase l).erase m, δ k / (freq m - freq k) ^ 2
            ≤ 9 / δ m := by
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
            (fun k hk => Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hk, Finset.mem_univ k⟩) ?_)
            (h.spacing_sq m)
          exact fun k _ _ => div_nonneg (h.pos k).le (sq_nonneg _)
        gcongr
    _ = 36 * (δ l + δ m) / (δ l * δ m * (freq l - freq m) ^ 2) := by
        field_simp
        ring


end Adm
end MV
end Zeta23
