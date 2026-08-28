/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/FamilyHyps.lean — the explicit formula's window-regularity class FamilyHyps (ExplicitFormula.lean §7)
for GENERAL taper families (discharges the last binder of the _flat_std and _quartic ξ′ headlines).

  theorem familyHyps_flat {P : Params} (hP : P.Valid) (hlam : P.lam < 1) : FamilyHyps (fun _ => P)
  (familyHyps_atV for φ_v = √(v(u/L))·φ is in Zeta23/XiPrime/FamilyHypsV.lean, importing §1 below.)

FamilyHyps asks, from some T₀ on: φ_T is C³, tsupport φ_T ⊆ [−L/2, L/2], even, |φ_T| ≤ 1, and ‖φ_T^{(j)}‖_{L¹} ≤ C
for j = 1,2,3 with C independent of T.  For the ramp taper φ(u) = ϱ((L/2−|u|)/w) with a C³ profile ϱ (ϱ ≡ 0 on
(−∞,0], ≡ 1 on [1,∞)) the derivatives φ^{(j)}, 1 ≤ j ≤ 3, live on the two ramps of width w and are bounded by
B·w^{−j}, B := a bound for |ϱ′|,|ϱ″|,|ϱ‴| (continuous, supported in [0,1]), so ‖φ^{(j)}‖₁ ≤ 2B·w^{1−j} ≤ 2B: this is
the Zeta23/Taper/GevreyRamps.lean argument (product form φ = f₊·f₋, mixed Leibniz terms vanish) run at
regularity C³ instead of C^∞ — §1–§2 below.  For φ_v = √(v(u/L))·φ (§3) the factor g(u) = h(u/L), h := √v, is C³ on
a neighbourhood |u| < L(½+η) of the support (v > 0 on [−½,½] ⇒ on [−½−2η, ½+2η]) with |g^{(i)}| ≤ H·L^{−i}, so
Leibniz gives ‖φ_v^{(j)}‖₁ ≤ H·(L·L^{−j} + 2^j·2B) ≤ H(1 + 16B) uniformly in T (L ≥ 1).
-/
import Zeta23.XiPrime.ExplicitFormula
import Zeta23.XiPrime.Assembly
import Zeta23.XiPrime.QuarticWindow.Params
import Zeta23.Taper.GevreyRamps
import Zeta23.Taper.Params

noncomputable section

open Filter Set MeasureTheory Topology

namespace Zeta23
namespace XiPrime
namespace FamilyHypsC3

/-! ## §1. C³ ramp calculus for a TaperProfile -/

section Ramps
variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-- for 1 ≤ i ≤ 3 the i-th derivative of a C³ profile vanishes off (0,1). -/
lemma iteratedDeriv_eq_zero (hϱ : TaperProfile ϱ) {i : ℕ} (hi : 1 ≤ i) (hi3 : i ≤ 3)
    {x : ℝ} (hx : x ∉ Set.Ioo (0:ℝ) 1) : iteratedDeriv i ϱ x = 0 := by
  have hi0 : i ≠ 0 := by omega
  have hcont : Continuous (iteratedDeriv i ϱ) :=
    hϱ.contDiff.continuous_iteratedDeriv i (by exact_mod_cast hi3)
  have hcl : IsClosed {y : ℝ | iteratedDeriv i ϱ y = 0} := isClosed_eq hcont continuous_const
  have h1 : Set.Iio (0:ℝ) ⊆ {y | iteratedDeriv i ϱ y = 0} := by
    intro y hy
    have hev : ϱ =ᶠ[𝓝 y] (fun _ => (0:ℝ)) :=
      Filter.eventually_of_mem (Iio_mem_nhds hy) (fun z hz => hϱ.eq_zero z (le_of_lt hz))
    show iteratedDeriv i ϱ y = 0
    rw [hev.iteratedDeriv_eq i, iteratedDeriv_const, if_neg hi0]
  have h2 : Set.Ioi (1:ℝ) ⊆ {y | iteratedDeriv i ϱ y = 0} := by
    intro y hy
    have hev : ϱ =ᶠ[𝓝 y] (fun _ => (1:ℝ)) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hy) (fun z hz => hϱ.eq_one z (le_of_lt hz))
    show iteratedDeriv i ϱ y = 0
    rw [hev.iteratedDeriv_eq i, iteratedDeriv_const, if_neg hi0]
  have h1' : Set.Iic (0:ℝ) ⊆ {y | iteratedDeriv i ϱ y = 0} := by
    rw [← closure_Iio]; exact hcl.closure_subset_iff.mpr h1
  have h2' : Set.Ici (1:ℝ) ⊆ {y | iteratedDeriv i ϱ y = 0} := by
    rw [← closure_Ioi]; exact hcl.closure_subset_iff.mpr h2
  simp only [Set.mem_Ioo, not_and_or, not_lt] at hx
  rcases hx with hx | hx
  · exact h1' hx
  · exact h2' hx

/-- a uniform bound for |ϱ^{(i)}|, 1 ≤ i ≤ 3. -/
lemma exists_deriv_bound (hϱ : TaperProfile ϱ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i : ℕ, 1 ≤ i → i ≤ 3 → ∀ x : ℝ, |iteratedDeriv i ϱ x| ≤ B := by
  have hb : ∀ i : ℕ, i ≤ 3 → ∃ C : ℝ, ∀ x ∈ Set.Icc (0:ℝ) 1, ‖iteratedDeriv i ϱ x‖ ≤ C := fun i hi =>
    isCompact_Icc.exists_bound_of_continuousOn
      ((hϱ.contDiff.continuous_iteratedDeriv i (by exact_mod_cast hi)).continuousOn)
  obtain ⟨C1, hC1⟩ := hb 1 (by norm_num)
  obtain ⟨C2, hC2⟩ := hb 2 (by norm_num)
  obtain ⟨C3, hC3⟩ := hb 3 le_rfl
  refine ⟨max (max (max C1 C2) C3) 0, le_max_right _ _, fun i hi hi3 x => ?_⟩
  by_cases hx : x ∈ Set.Ioo (0:ℝ) 1
  · have hx' : x ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hx
    interval_cases i
    · exact (hC1 x hx').trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _))
    · exact (hC2 x hx').trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _))
    · exact (hC3 x hx').trans (le_trans (le_max_right _ _) (le_max_left _ _))
  · rw [iteratedDeriv_eq_zero hϱ hi hi3 hx, abs_zero]; exact le_max_right _ _

open Taper in
lemma iteratedDeriv_fP (hϱ : TaperProfile ϱ) {i : ℕ} (hi3 : i ≤ 3) (u : ℝ) :
    iteratedDeriv i (fP ϱ L w) u = (-1 : ℝ) ^ i * ((w⁻¹) ^ i * iteratedDeriv i ϱ ((L / 2 - u) / w)) := by
  have hg := iteratedDeriv_comp_const_mul (n := i) (hϱ.contDiff.of_le (by exact_mod_cast hi3)) w⁻¹
  rw [fP_eq]
  refine (congrFun (iteratedDeriv_comp_const_sub i (fun x => ϱ (w⁻¹ * x)) (L / 2)) u).trans ?_
  simp only [smul_eq_mul, hg, div_eq_inv_mul]

open Taper in
lemma iteratedDeriv_fM (hϱ : TaperProfile ϱ) {i : ℕ} (hi3 : i ≤ 3) (u : ℝ) :
    iteratedDeriv i (fM ϱ L w) u = (w⁻¹) ^ i * iteratedDeriv i ϱ ((L / 2 + u) / w) := by
  have hg := iteratedDeriv_comp_const_mul (n := i) (hϱ.contDiff.of_le (by exact_mod_cast hi3)) w⁻¹
  rw [fM_eq]
  refine (congrFun (iteratedDeriv_comp_add_const i (fun x => ϱ (w⁻¹ * x)) (L / 2)) u).trans ?_
  simp only [hg, div_eq_inv_mul, add_comm u]

open Taper in
/-- ramp majorants. -/
lemma abs_iteratedDeriv_fP_le (hϱ : TaperProfile ϱ) {B : ℝ}
    (hB : ∀ i : ℕ, 1 ≤ i → i ≤ 3 → ∀ x : ℝ, |iteratedDeriv i ϱ x| ≤ B) (hw : 0 < w) {k : ℕ}
    (hk : 1 ≤ k) (hk3 : k ≤ 3) (u : ℝ) : |iteratedDeriv k (fP ϱ L w) u|
      ≤ (Set.Ioo (L / 2 - w) (L / 2)).indicator (fun _ => (w⁻¹) ^ k * B) u := by
  rw [iteratedDeriv_fP hϱ hk3, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_mul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (w⁻¹) ^ k)]
  by_cases hu : u ∈ Set.Ioo (L / 2 - w) (L / 2)
  · rw [Set.indicator_of_mem hu]
    exact mul_le_mul_of_nonneg_left (hB k hk hk3 _) (by positivity)
  · rw [Set.indicator_of_notMem hu]
    have hx : (L / 2 - u) / w ∉ Set.Ioo (0:ℝ) 1 := by
      intro h
      apply hu
      simp only [Set.mem_Ioo, div_pos_iff_of_pos_right hw, div_lt_one hw] at h
      constructor <;> linarith [h.1, h.2]
    rw [iteratedDeriv_eq_zero hϱ hk hk3 hx, abs_zero, mul_zero]

open Taper in
lemma abs_iteratedDeriv_fM_le (hϱ : TaperProfile ϱ) {B : ℝ}
    (hB : ∀ i : ℕ, 1 ≤ i → i ≤ 3 → ∀ x : ℝ, |iteratedDeriv i ϱ x| ≤ B) (hw : 0 < w) {k : ℕ}
    (hk : 1 ≤ k) (hk3 : k ≤ 3) (u : ℝ) : |iteratedDeriv k (fM ϱ L w) u|
      ≤ (Set.Ioo (-(L / 2)) (w - L / 2)).indicator (fun _ => (w⁻¹) ^ k * B) u := by
  rw [iteratedDeriv_fM hϱ hk3, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (w⁻¹) ^ k)]
  by_cases hu : u ∈ Set.Ioo (-(L / 2)) (w - L / 2)
  · rw [Set.indicator_of_mem hu]
    exact mul_le_mul_of_nonneg_left (hB k hk hk3 _) (by positivity)
  · rw [Set.indicator_of_notMem hu]
    have hx : (L / 2 + u) / w ∉ Set.Ioo (0:ℝ) 1 := by
      intro h
      apply hu
      simp only [Set.mem_Ioo, div_pos_iff_of_pos_right hw, div_lt_one hw] at h
      constructor <;> linarith [h.1, h.2]
    rw [iteratedDeriv_eq_zero hϱ hk hk3 hx, abs_zero, mul_zero]

open Taper in
/-- mixed Leibniz terms vanish (open ramps disjoint when 2w ≤ L). -/
lemma iteratedDeriv_fP_mul_fM_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L)
    {i j : ℕ} (hi : 1 ≤ i) (hi3 : i ≤ 3) (hj : 1 ≤ j) (hj3 : j ≤ 3) (u : ℝ) :
    iteratedDeriv i (fP ϱ L w) u * iteratedDeriv j (fM ϱ L w) u = 0 := by
  by_cases hu : u ∈ Set.Ioo (L / 2 - w) (L / 2)
  · have hu' : (L / 2 + u) / w ∉ Set.Ioo (0:ℝ) 1 := by
      have h1 : 1 ≤ (L / 2 + u) / w := by rw [le_div_iff₀ hw]; linarith [hu.1]
      simp only [Set.mem_Ioo, not_and_or, not_lt]
      exact Or.inr h1
    rw [iteratedDeriv_fM hϱ hj3, iteratedDeriv_eq_zero hϱ hj hj3 hu']; ring
  · have hu' : (L / 2 - u) / w ∉ Set.Ioo (0:ℝ) 1 := by
      intro h
      apply hu
      simp only [Set.mem_Ioo, div_pos_iff_of_pos_right hw, div_lt_one hw] at h
      constructor <;> linarith [h.1, h.2]
    rw [iteratedDeriv_fP hϱ hi3, iteratedDeriv_eq_zero hϱ hi hi3 hu']; ring

open Taper in
lemma fP_contDiffAt (hϱ : TaperProfile ϱ) (u : ℝ) : ContDiffAt ℝ 3 (fP ϱ L w) u :=
  (hϱ.contDiff.comp (by fun_prop : ContDiff ℝ 3 fun u : ℝ => (L / 2 - u) / w)).contDiffAt

open Taper in
lemma fM_contDiffAt (hϱ : TaperProfile ϱ) (u : ℝ) : ContDiffAt ℝ 3 (fM ϱ L w) u :=
  (hϱ.contDiff.comp (by fun_prop : ContDiff ℝ 3 fun u : ℝ => (L / 2 + u) / w)).contDiffAt

open Taper in
/-- |φ^{(k)}| ≤ |f₊^{(k)}| + |f₋^{(k)}|, 1 ≤ k ≤ 3. -/
lemma abs_iteratedDeriv_phi_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L)
    {k : ℕ} (hk : 1 ≤ k) (hk3 : k ≤ 3) (u : ℝ) :
    |iteratedDeriv k (phi ϱ L w) u|
      ≤ |iteratedDeriv k (fP ϱ L w) u| + |iteratedDeriv k (fM ϱ L w) u| := by
  have hprod : phi ϱ L w = fP ϱ L w * fM ϱ L w := by
    funext u; exact phi_eq_mul hϱ hw hwL u
  have hPk : ContDiffAt ℝ k (fP ϱ L w) u := (fP_contDiffAt hϱ u).of_le (by exact_mod_cast hk3)
  have hMk : ContDiffAt ℝ k (fM ϱ L w) u := (fM_contDiffAt hϱ u).of_le (by exact_mod_cast hk3)
  rw [hprod, iteratedDeriv_mul hPk hMk]
  have hk0 : (0:ℕ) ≠ k := by omega
  rw [Finset.sum_eq_add 0 k hk0]
  · simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero, Nat.sub_zero,
      Nat.choose_self, Nat.sub_self]
    have h0 : |fP ϱ L w u| ≤ 1 := by
      unfold fP; rw [abs_of_nonneg (hϱ.nonneg _)]; exact hϱ.le_one _
    have h1 : |fM ϱ L w u| ≤ 1 := by
      unfold fM; rw [abs_of_nonneg (hϱ.nonneg _)]; exact hϱ.le_one _
    calc |fP ϱ L w u * iteratedDeriv k (fM ϱ L w) u + iteratedDeriv k (fP ϱ L w) u * fM ϱ L w u|
        ≤ |fP ϱ L w u * iteratedDeriv k (fM ϱ L w) u| + |iteratedDeriv k (fP ϱ L w) u * fM ϱ L w u| :=
          abs_add_le _ _
      _ = |fP ϱ L w u| * |iteratedDeriv k (fM ϱ L w) u| + |iteratedDeriv k (fP ϱ L w) u| * |fM ϱ L w u| := by
          rw [abs_mul, abs_mul]
      _ ≤ 1 * |iteratedDeriv k (fM ϱ L w) u| + |iteratedDeriv k (fP ϱ L w) u| * 1 := by
          gcongr
      _ = _ := by ring
  · intro c hc hne
    have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hne.1
    have hcr := Finset.mem_range.mp hc
    have hc2 : 1 ≤ k - c := by omega
    rw [mul_assoc, iteratedDeriv_fP_mul_fM_eq_zero hϱ hw hwL hc1 (by omega) hc2 (by omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

open Taper in
/-- pointwise ramp majorant for φ^{(k)}. -/
lemma abs_iteratedDeriv_phi_le_indicator (hϱ : TaperProfile ϱ) {B : ℝ}
    (hB : ∀ i : ℕ, 1 ≤ i → i ≤ 3 → ∀ x : ℝ, |iteratedDeriv i ϱ x| ≤ B) (hw : 0 < w) (hwL : 2 * w ≤ L)
    {k : ℕ} (hk : 1 ≤ k) (hk3 : k ≤ 3) (u : ℝ) :
    |iteratedDeriv k (phi ϱ L w) u|
      ≤ (Set.Ioo (L / 2 - w) (L / 2)).indicator (fun _ => (w⁻¹) ^ k * B) u
        + (Set.Ioo (-(L / 2)) (w - L / 2)).indicator (fun _ => (w⁻¹) ^ k * B) u :=
  (abs_iteratedDeriv_phi_le hϱ hw hwL hk hk3 u).trans
    (add_le_add (abs_iteratedDeriv_fP_le hϱ hB hw hk hk3 u) (abs_iteratedDeriv_fM_le hϱ hB hw hk hk3 u))

lemma integral_indicator_Ioo_const {a b M : ℝ} (hab : a ≤ b) :
    ∫ u, (Set.Ioo a b).indicator (fun _ => M) u = M * (b - a) := by
  rw [integral_indicator_const _ measurableSet_Ioo, measureReal_def, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_comm]

open Taper in
/-- **‖φ^{(k)}‖_{L¹} ≤ 2B·w^{1−k}** for 1 ≤ k ≤ 3 (2w ≤ L). -/
theorem integral_abs_iteratedDeriv_phi_le (hϱ : TaperProfile ϱ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ i : ℕ, 1 ≤ i → i ≤ 3 → ∀ x : ℝ, |iteratedDeriv i ϱ x| ≤ B) (hw : 0 < w)
    (hwL : 2 * w ≤ L) {k : ℕ} (hk : 1 ≤ k) (hk3 : k ≤ 3) :
    ∫ u, |iteratedDeriv k (phi ϱ L w) u| ≤ 2 * ((w⁻¹) ^ k * B) * w := by
  set M : ℝ := (w⁻¹) ^ k * B with hM
  have hM0 : 0 ≤ M := by positivity
  set Rp := Set.Ioo (L / 2 - w) (L / 2)
  set Rm := Set.Ioo (-(L / 2)) (w - L / 2)
  have hIp : Integrable (Rp.indicator fun _ => M) :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const (by simp))
  have hIm : Integrable (Rm.indicator fun _ => M) :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const (by simp))
  calc ∫ u, |iteratedDeriv k (phi ϱ L w) u|
      ≤ ∫ u, (Rp.indicator (fun _ => M) u + Rm.indicator (fun _ => M) u) :=
        integral_mono_of_nonneg (Eventually.of_forall fun u => abs_nonneg _) (hIp.add hIm)
          (Eventually.of_forall fun u => abs_iteratedDeriv_phi_le_indicator hϱ hB hw hwL hk hk3 u)
    _ = M * w + M * w := by
        rw [integral_add hIp hIm, integral_indicator_Ioo_const (by linarith),
          integral_indicator_Ioo_const (by linarith)]
        ring
    _ = 2 * M * w := by ring

end Ramps

/-! ## §2. FamilyHyps for the flat family of ANY valid parameter set -/

/-- derivatives of every order of a compactly supported function are compactly supported. -/
lemma hasCompactSupport_iteratedDeriv' {f : ℝ → ℝ} (hf : HasCompactSupport f) (k : ℕ) :
    HasCompactSupport (iteratedDeriv k f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih => simpa [iteratedDeriv_succ] using ih.deriv

end FamilyHypsC3

open FamilyHypsC3 in
/-- **FamilyHyps for the flat family** T ↦ P, for every valid P with λ < 1 (any C³ taper profile, any w ≥ 1). -/
theorem familyHyps_flat {P : Params} (hP : P.Valid) (hlam : P.lam < 1) : FamilyHyps (fun _ => P) := by
  obtain ⟨B, hB0, hB⟩ := exists_deriv_bound hP.taper
  have hw1 : 1 ≤ P.w := hP.one_le_w
  have hw : 0 < P.w := by linarith
  refine ⟨⟨P.lam, hP.lam_pos, hlam, fun _ => rfl⟩, ?_⟩
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp
    ((Assembly.tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop (8 * P.w))
  refine ⟨2 * B, T₀, fun T hT => ?_⟩
  have h8 : 8 * P.w ≤ P.L T := hT₀ T hT
  have hwL : 2 * P.w ≤ P.L T := by linarith
  have hcd : ContDiff ℝ 3 (P.phi T) := Params.phi_contDiff hP h8
  refine ⟨hcd, closure_minimal (Params.phi_support_subset hP) isClosed_Icc,
    fun u => Params.phi_even' u,
    fun u => abs_le.mpr ⟨by linarith [Params.phi_nonneg hP (T := T) u], Params.phi_le_one hP u⟩,
    fun j hj1 hj3 => ⟨?_, ?_⟩⟩
  · exact ((hcd.continuous_iteratedDeriv j (by exact_mod_cast hj3)).integrable_of_hasCompactSupport
      (hasCompactSupport_iteratedDeriv' (Params.phi_hasCompactSupport hP) j))
  · have hb := integral_abs_iteratedDeriv_phi_le (L := P.L T) (w := P.w) hP.taper hB0 hB hw hwL hj1 hj3
    refine hb.trans ?_
    -- 2·(w⁻¹)^j·B·w ≤ 2B  (w ≥ 1, j ≥ 1)
    have hwj : (P.w⁻¹) ^ j * P.w ≤ 1 := by
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [pow_succ, mul_assoc, inv_mul_cancel₀ hw.ne', mul_one]
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hw1)
    nlinarith

end XiPrime
end Zeta23
