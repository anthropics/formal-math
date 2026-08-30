/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Taper/GevreyRamps.lean — Gevrey ramp lemma:
for a Gevrey-s profile ϱ (`Taper.GevreyProfile s A B ϱ`), the concrete taper
φ(u) = ϱ((L/2 − |u|)/w) is C^∞ and ‖φ^{(k)}‖_{L¹} ≤ 2B·w·(A/w)^k·k^{sk} for every k ≥ 1.
Route: the product form φ = f₊·f₋ with f_±(u) = ϱ((L/2 ∓ u)/w) (Taper.phi_eq_mul, needs 2w ≤ L);
ϱ^{(i)} (i ≥ 1) vanishes off (0,1) (closure argument at the two endpoints), so in the Leibniz
expansion only i = 0 and i = k survive and |φ^{(k)}| ≤ |f₊^{(k)}| + |f₋^{(k)}|; each is
w^{−k}|ϱ^{(k)}| ∘ (affine), bounded by w^{−k}BA^k k^{sk} on a ramp of length w and 0 elsewhere.
Produces the interface `Params.GevreyPhiBound` (Zeta23/Taper/GevreyPhi.lean).
-/
import Zeta23.Taper.Gevrey
import Zeta23.Taper.GevreyPhi
import Zeta23.Taper

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace Zeta23
namespace Taper

variable {s A B : ℝ} {ϱ : ℝ → ℝ}

/-- for `i ≥ 1`, the `i`-th derivative of a profile vanishes off the open unit interval. -/
lemma GevreyProfile.iteratedDeriv_eq_zero (hϱ : GevreyProfile s A B ϱ) {i : ℕ} (hi : 1 ≤ i)
    {x : ℝ} (hx : x ∉ Set.Ioo (0:ℝ) 1) : iteratedDeriv i ϱ x = 0 := by
  have hi0 : i ≠ 0 := by omega
  have hcont : Continuous (iteratedDeriv i ϱ) := hϱ.smooth.continuous_iteratedDeriv i (WithTop.coe_le_coe.mpr le_top)
  have hcl : IsClosed {y : ℝ | iteratedDeriv i ϱ y = 0} := isClosed_eq hcont continuous_const
  -- zero on the open pieces
  have h1 : Set.Iio (0:ℝ) ⊆ {y | iteratedDeriv i ϱ y = 0} := by
    intro y hy
    have hev : ϱ =ᶠ[𝓝 y] (fun _ => (0:ℝ)) :=
      Filter.eventually_of_mem (Iio_mem_nhds hy) (fun z hz => hϱ.taper.eq_zero z (le_of_lt hz))
    show iteratedDeriv i ϱ y = 0
    rw [hev.iteratedDeriv_eq i, iteratedDeriv_const, if_neg hi0]
  have h2 : Set.Ioi (1:ℝ) ⊆ {y | iteratedDeriv i ϱ y = 0} := by
    intro y hy
    have hev : ϱ =ᶠ[𝓝 y] (fun _ => (1:ℝ)) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hy) (fun z hz => hϱ.taper.eq_one z (le_of_lt hz))
    show iteratedDeriv i ϱ y = 0
    rw [hev.iteratedDeriv_eq i, iteratedDeriv_const, if_neg hi0]
  -- hence on their closures
  have h1' : Set.Iic (0:ℝ) ⊆ {y | iteratedDeriv i ϱ y = 0} := by
    rw [← closure_Iio]; exact hcl.closure_subset_iff.mpr h1
  have h2' : Set.Ici (1:ℝ) ⊆ {y | iteratedDeriv i ϱ y = 0} := by
    rw [← closure_Ioi]; exact hcl.closure_subset_iff.mpr h2
  simp only [Set.mem_Ioo, not_and_or, not_lt] at hx
  rcases hx with hx | hx
  · exact h1' hx
  · exact h2' hx

/-- pointwise majorant: `|ϱ^{(k)}(x)| ≤ B A^k k^{sk} · 1_{(0,1)}(x)` for `k ≥ 1`. -/
lemma GevreyProfile.abs_iteratedDeriv_le_indicator (hϱ : GevreyProfile s A B ϱ) {k : ℕ}
    (hk : 1 ≤ k) (x : ℝ) :
    |iteratedDeriv k ϱ x| ≤ (Set.Ioo (0:ℝ) 1).indicator (fun _ => B * A ^ k * (k : ℝ) ^ (s * k)) x := by
  by_cases hx : x ∈ Set.Ioo (0:ℝ) 1
  · rw [Set.indicator_of_mem hx]; exact hϱ.bound k hk x
  · rw [Set.indicator_of_notMem hx, hϱ.iteratedDeriv_eq_zero hk hx, abs_zero]

/-- `iteratedDeriv` commutes with the coercion ℝ → ℂ for smooth functions. -/
lemma iteratedDeriv_ofReal_comp {f : ℝ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (k : ℕ) :
    iteratedDeriv k (fun u => (f u : ℂ)) = fun u => ((iteratedDeriv k f u : ℝ) : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    exact deriv_ofReal_comp (hf.differentiable_iteratedDeriv k (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top k)))

section Ramps
variable {L w : ℝ}

/-- the two one-sided ramps `f_±(u) = ϱ((L/2 ∓ u)/w)`. -/
def fP (ϱ : ℝ → ℝ) (L w : ℝ) (u : ℝ) : ℝ := ϱ ((L / 2 - u) / w)
def fM (ϱ : ℝ → ℝ) (L w : ℝ) (u : ℝ) : ℝ := ϱ ((L / 2 + u) / w)

lemma fP_eq (ϱ : ℝ → ℝ) (L w : ℝ) :
    fP ϱ L w = fun u => (fun x => ϱ (w⁻¹ * x)) (L / 2 - u) := by
  funext u; simp only [fP, div_eq_inv_mul]

lemma fM_eq (ϱ : ℝ → ℝ) (L w : ℝ) :
    fM ϱ L w = fun u => (fun x => ϱ (w⁻¹ * x)) (u + L / 2) := by
  funext u; simp only [fM, div_eq_inv_mul, add_comm u]

lemma fP_contDiff (hϱ : GevreyProfile s A B ϱ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fP ϱ L w) :=
  hϱ.smooth.comp (by fun_prop)

lemma fM_contDiff (hϱ : GevreyProfile s A B ϱ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fM ϱ L w) :=
  hϱ.smooth.comp (by fun_prop)

lemma iteratedDeriv_fP (hϱ : GevreyProfile s A B ϱ) (i : ℕ) (u : ℝ) :
    iteratedDeriv i (fP ϱ L w) u = (-1 : ℝ) ^ i * ((w⁻¹) ^ i * iteratedDeriv i ϱ ((L / 2 - u) / w)) := by
  have hg := iteratedDeriv_comp_const_mul (n := i) (hϱ.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) w⁻¹
  rw [fP_eq]
  refine (congrFun (iteratedDeriv_comp_const_sub i (fun x => ϱ (w⁻¹ * x)) (L / 2)) u).trans ?_
  simp only [smul_eq_mul, hg, div_eq_inv_mul]

lemma iteratedDeriv_fM (hϱ : GevreyProfile s A B ϱ) (i : ℕ) (u : ℝ) :
    iteratedDeriv i (fM ϱ L w) u = (w⁻¹) ^ i * iteratedDeriv i ϱ ((L / 2 + u) / w) := by
  have hg := iteratedDeriv_comp_const_mul (n := i) (hϱ.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) w⁻¹
  rw [fM_eq]
  refine (congrFun (iteratedDeriv_comp_add_const i (fun x => ϱ (w⁻¹ * x)) (L / 2)) u).trans ?_
  simp only [hg, div_eq_inv_mul, add_comm u]

/-- ramp majorants: `|f₊^{(k)}(u)| ≤ w^{−k}BA^k k^{sk}·1_{(L/2−w, L/2)}(u)` and symmetrically. -/
lemma abs_iteratedDeriv_fP_le (hϱ : GevreyProfile s A B ϱ) (hw : 0 < w) {k : ℕ} (hk : 1 ≤ k)
    (u : ℝ) : |iteratedDeriv k (fP ϱ L w) u|
      ≤ (Set.Ioo (L / 2 - w) (L / 2)).indicator (fun _ => (w⁻¹) ^ k * (B * A ^ k * (k : ℝ) ^ (s * k))) u := by
  rw [iteratedDeriv_fP hϱ, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_mul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (w⁻¹) ^ k)]
  have h := hϱ.abs_iteratedDeriv_le_indicator hk ((L / 2 - u) / w)
  have hset : ((L / 2 - u) / w ∈ Set.Ioo (0:ℝ) 1) ↔ (u ∈ Set.Ioo (L / 2 - w) (L / 2)) := by
    simp only [Set.mem_Ioo, div_pos_iff_of_pos_right hw, div_lt_one hw]
    constructor <;> intro h' <;> constructor <;> linarith [h'.1, h'.2]
  by_cases hu : u ∈ Set.Ioo (L / 2 - w) (L / 2)
  · rw [Set.indicator_of_mem hu]
    rw [Set.indicator_of_mem (hset.mpr hu)] at h
    exact mul_le_mul_of_nonneg_left h (by positivity)
  · rw [Set.indicator_of_notMem hu]
    rw [Set.indicator_of_notMem (fun h' => hu (hset.mp h'))] at h
    have : |iteratedDeriv k ϱ ((L / 2 - u) / w)| = 0 := le_antisymm h (abs_nonneg _)
    rw [this, mul_zero]

lemma abs_iteratedDeriv_fM_le (hϱ : GevreyProfile s A B ϱ) (hw : 0 < w) {k : ℕ} (hk : 1 ≤ k)
    (u : ℝ) : |iteratedDeriv k (fM ϱ L w) u|
      ≤ (Set.Ioo (-(L / 2)) (w - L / 2)).indicator (fun _ => (w⁻¹) ^ k * (B * A ^ k * (k : ℝ) ^ (s * k))) u := by
  rw [iteratedDeriv_fM hϱ, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (w⁻¹) ^ k)]
  have h := hϱ.abs_iteratedDeriv_le_indicator hk ((L / 2 + u) / w)
  have hset : ((L / 2 + u) / w ∈ Set.Ioo (0:ℝ) 1) ↔ (u ∈ Set.Ioo (-(L / 2)) (w - L / 2)) := by
    simp only [Set.mem_Ioo, div_pos_iff_of_pos_right hw, div_lt_one hw]
    constructor <;> intro h' <;> constructor <;> linarith [h'.1, h'.2]
  by_cases hu : u ∈ Set.Ioo (-(L / 2)) (w - L / 2)
  · rw [Set.indicator_of_mem hu]
    rw [Set.indicator_of_mem (hset.mpr hu)] at h
    exact mul_le_mul_of_nonneg_left h (by positivity)
  · rw [Set.indicator_of_notMem hu]
    rw [Set.indicator_of_notMem (fun h' => hu (hset.mp h'))] at h
    have : |iteratedDeriv k ϱ ((L / 2 + u) / w)| = 0 := le_antisymm h (abs_nonneg _)
    rw [this, mul_zero]

/-- mixed Leibniz terms vanish: for `1 ≤ i`, `1 ≤ j` and `2w ≤ L`,
`f₊^{(i)}(u)·f₋^{(j)}(u) = 0` (the open ramps are disjoint). -/
lemma iteratedDeriv_fP_mul_fM_eq_zero (hϱ : GevreyProfile s A B ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L)
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (u : ℝ) :
    iteratedDeriv i (fP ϱ L w) u * iteratedDeriv j (fM ϱ L w) u = 0 := by
  by_cases hu : u ∈ Set.Ioo (L / 2 - w) (L / 2)
  · -- then u ∉ the other ramp
    have hu' : (L / 2 + u) / w ∉ Set.Ioo (0:ℝ) 1 := by
      have h1 : 1 ≤ (L / 2 + u) / w := by rw [le_div_iff₀ hw]; linarith [hu.1]
      simp only [Set.mem_Ioo, not_and_or, not_lt]
      exact Or.inr h1
    rw [iteratedDeriv_fM hϱ, hϱ.iteratedDeriv_eq_zero hj hu']; ring
  · have hu' : (L / 2 - u) / w ∉ Set.Ioo (0:ℝ) 1 := by
      intro h
      apply hu
      simp only [Set.mem_Ioo, div_pos_iff_of_pos_right hw, div_lt_one hw] at h
      constructor <;> linarith [h.1, h.2]
    rw [iteratedDeriv_fP hϱ, hϱ.iteratedDeriv_eq_zero hi hu']; ring

/-- **|φ^{(k)}| ≤ |f₊^{(k)}| + |f₋^{(k)}|** for `k ≥ 1`. -/
lemma abs_iteratedDeriv_phi_le (hϱ : GevreyProfile s A B ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L)
    {k : ℕ} (hk : 1 ≤ k) (u : ℝ) :
    |iteratedDeriv k (phi ϱ L w) u|
      ≤ |iteratedDeriv k (fP ϱ L w) u| + |iteratedDeriv k (fM ϱ L w) u| := by
  have hprod : phi ϱ L w = fP ϱ L w * fM ϱ L w := by
    funext u; exact phi_eq_mul hϱ.taper hw hwL u
  have hPk : ContDiffAt ℝ k (fP ϱ L w) u := ((fP_contDiff hϱ).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hMk : ContDiffAt ℝ k (fM ϱ L w) u := ((fM_contDiff hϱ).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  rw [hprod, iteratedDeriv_mul hPk hMk]
  have hk0 : (0:ℕ) ≠ k := by omega
  rw [Finset.sum_eq_add 0 k hk0]
  · simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero, Nat.sub_zero,
      Nat.choose_self, Nat.sub_self]
    have h0 : |fP ϱ L w u| ≤ 1 := by
      unfold fP; rw [abs_of_nonneg (hϱ.taper.nonneg _)]; exact hϱ.taper.le_one _
    have h1 : |fM ϱ L w u| ≤ 1 := by
      unfold fM; rw [abs_of_nonneg (hϱ.taper.nonneg _)]; exact hϱ.taper.le_one _
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
    have hc2 : 1 ≤ k - c := by
      have := Finset.mem_range.mp hc
      omega
    rw [mul_assoc, iteratedDeriv_fP_mul_fM_eq_zero hϱ hw hwL hc1 hc2, mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **Gevrey ramp lemma**: `‖φ^{(k)}‖_{L¹} ≤ 2B·w·(A/w)^k·k^{sk}` (`k ≥ 1`, `2w ≤ L`). -/
theorem integral_abs_iteratedDeriv_phi_le (hϱ : GevreyProfile s A B ϱ) (hw : 0 < w)
    (hwL : 2 * w ≤ L) {k : ℕ} (hk : 1 ≤ k) :
    ∫ u, |iteratedDeriv k (phi ϱ L w) u| ≤ 2 * B * w * (A / w) ^ k * (k : ℝ) ^ (s * k) := by
  set M : ℝ := (w⁻¹) ^ k * (B * A ^ k * (k : ℝ) ^ (s * k)) with hM
  have hM0 : 0 ≤ M := by have := hϱ.A_pos; have := hϱ.B_pos; positivity
  set Rp := Set.Ioo (L / 2 - w) (L / 2)
  set Rm := Set.Ioo (-(L / 2)) (w - L / 2)
  have hIp : Integrable (Rp.indicator fun _ => M) :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const (by simp [Rp]))
  have hIm : Integrable (Rm.indicator fun _ => M) :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const (by simp [Rm]))
  have hmaj : ∀ u, |iteratedDeriv k (phi ϱ L w) u|
      ≤ Rp.indicator (fun _ => M) u + Rm.indicator (fun _ => M) u := fun u =>
    (abs_iteratedDeriv_phi_le hϱ hw hwL hk u).trans
      (add_le_add (abs_iteratedDeriv_fP_le hϱ hw hk u) (abs_iteratedDeriv_fM_le hϱ hw hk u))
  have hvol : ∀ a b : ℝ, b - a = w → ∫ u, (Set.Ioo a b).indicator (fun _ => M) u = M * w := by
    intro a b hab
    rw [integral_indicator_const _ measurableSet_Ioo, measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul, hab, mul_comm]
  calc ∫ u, |iteratedDeriv k (phi ϱ L w) u|
      ≤ ∫ u, (Rp.indicator (fun _ => M) u + Rm.indicator (fun _ => M) u) :=
        integral_mono_of_nonneg (Eventually.of_forall fun u => abs_nonneg _) (hIp.add hIm)
          (Eventually.of_forall hmaj)
    _ = M * w + M * w := by
        rw [integral_add hIp hIm, hvol _ _ (by ring), hvol _ _ (by ring)]
    _ = 2 * B * w * (A / w) ^ k * (k : ℝ) ^ (s * k) := by
        rw [hM, div_eq_mul_inv, mul_pow]; ring

end Ramps

end Taper

/-- **Gevrey ramp lemma, in the `Params.GevreyPhiBound` interface**: a Gevrey-s profile makes
`P.phi T` a C^∞ window with ‖φ^{(k)}‖₁ ≤ 2B·w·(A/w)^k·k^{sk}. -/
theorem Params.gevreyPhiBound_of_profile (P : Params) (T : ℝ) {s A B : ℝ}
    (hϱ : Taper.GevreyProfile s A B P.ϱ) (hw : 0 < P.w) (h2w : 2 * P.w ≤ P.L T) :
    P.GevreyPhiBound T s A B where
  one_lt := hϱ.one_lt
  A_pos := hϱ.A_pos
  B_pos := hϱ.B_pos
  smooth := by
    have hprod : P.phi T = Taper.fP P.ϱ (P.L T) P.w * Taper.fM P.ϱ (P.L T) P.w := by
      funext u; exact Taper.phi_eq_mul hϱ.taper hw h2w u
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P.phi T) := by
      rw [hprod]; exact (Taper.fP_contDiff hϱ).mul (Taper.fM_contDiff hϱ)
    exact Complex.ofRealCLM.contDiff.comp h
  bound := by
    intro k hk
    have hprod : P.phi T = Taper.fP P.ϱ (P.L T) P.w * Taper.fM P.ϱ (P.L T) P.w := by
      funext u; exact Taper.phi_eq_mul hϱ.taper hw h2w u
    have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P.phi T) := by
      rw [hprod]; exact (Taper.fP_contDiff hϱ).mul (Taper.fM_contDiff hϱ)
    have h2 := Taper.iteratedDeriv_ofReal_comp (f := P.phi T) hsm k
    rw [h2]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact Taper.integral_abs_iteratedDeriv_phi_le hϱ hw h2w hk

end Zeta23

end
