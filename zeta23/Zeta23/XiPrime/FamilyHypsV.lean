/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization.

Zeta23/XiPrime/FamilyHypsV.lean — the explicit formula's window-regularity class FamilyHyps
(ExplicitFormula.lean §7) for the PROFILED families T ↦ P.atV v T (φ_v = √(v(u/L))·φ), any
WindowProfile v (the flat family and the C³ ramp calculus are in Zeta23/XiPrime/FamilyHyps.lean,
consumed here).

  theorem familyHyps_atV {P : Params} (hP : P.Valid) (hlam : P.lam < 1) {v : ℝ → ℝ} (hv : WindowProfile v) :
      FamilyHyps (P.atV v)

ROUTE.  v > 0 on [−½, ½] and v continuous ⇒ v ≥ m > 0 on [−½−η, ½+η] (compactness: IsCompact.exists_isMinOn +
IsCompact.exists_cthickening_subset_open).  With a smooth cut-off χ (ContDiffBump, = 1 on |s| ≤ ½+η/2, = 0 off
|s| < ½+η) put ṽ := χ·v + (1−χ)·m ≥ m and h̃ := √ṽ: GLOBALLY C³, = √v on |s| ≤ ½+η/2, with |h̃^{(i)}| ≤ H (i ≤ 3).
Then φ_v = (h̃(·/L))·φ AS FUNCTIONS (where φ ≠ 0 we have |u/L| < ½; elsewhere both sides vanish), so φ_v is C³ and
Leibniz + iteratedDeriv_comp_const_mul (|(h̃(·/L))^{(i)}| ≤ H·L^{−i}) + the ramp bounds ‖φ^{(k)}‖₁ ≤ 2B
(k ≥ 1) and ∫|φ| ≤ L give ‖φ_v^{(j)}‖₁ ≤ 2^j·(2B+1)·H ≤ 8(2B+1)H, uniformly in T (L ≥ 1, w ≥ 1).
-/
import Zeta23.XiPrime.FamilyHyps
import Zeta23.XiPrime.QuarticWindow.Params
import Zeta23.XiPrime.QuarticWindow.ModWindow
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section

open Filter Set MeasureTheory Topology Metric

namespace Zeta23
namespace XiPrime
namespace FamilyHypsV

/-! ## §1. A globally C³ square root of the profile -/

/-- v ≥ m > 0 on a closed η-neighbourhood of [−½, ½]. -/
lemma exists_margin {v : ℝ → ℝ} (hv : WindowProfile v) :
    ∃ η m : ℝ, 0 < η ∧ 0 < m ∧ ∀ s : ℝ, |s| ≤ 1 / 2 + η → m ≤ v s := by
  set K : Set ℝ := Icc (-(1/2 : ℝ)) (1/2) with hK
  have hKc : IsCompact K := isCompact_Icc
  have hKne : K.Nonempty := ⟨0, by rw [hK]; constructor <;> norm_num⟩
  have hcont : Continuous v := hv.contDiff.continuous
  obtain ⟨s₀, hs₀K, hmin⟩ := hKc.exists_isMinOn hKne hcont.continuousOn
  have hm₀ : 0 < v s₀ := hv.pos s₀ hs₀K
  set O : Set ℝ := {s | v s₀ / 2 < v s} with hO
  have hOo : IsOpen O := isOpen_lt continuous_const hcont
  have hKO : K ⊆ O := fun s hs => by
    have : v s₀ ≤ v s := hmin hs
    show v s₀ / 2 < v s
    linarith
  obtain ⟨δ, hδ, hδO⟩ := hKc.exists_cthickening_subset_open hOo hKO
  refine ⟨δ, v s₀ / 2, hδ, by linarith, fun s hs => ?_⟩
  -- s is within δ of its projection onto K
  set y : ℝ := max (-(1/2)) (min (1/2) s) with hy
  have hyK : y ∈ K := by
    rw [hK, hy]; constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)
  have hdist : dist s y ≤ δ := by
    rw [Real.dist_eq, hy]
    have h1 := abs_le.1 hs
    rcases le_or_gt s (1/2) with h | h
    · rw [min_eq_right h]
      rcases le_or_gt (-(1/2)) s with h' | h'
      · rw [max_eq_right h']; simp [hδ.le]
      · rw [max_eq_left h'.le]; rw [abs_of_nonpos (by linarith)]; linarith
    · rw [min_eq_left h.le, max_eq_right (by norm_num)]
      rw [abs_of_nonneg (by linarith)]; linarith
  have hsO := hδO (mem_cthickening_of_dist_le s y δ K hyK hdist)
  exact le_of_lt hsO

/-- **a globally C³ square root of v near [−½, ½]** with uniformly bounded derivatives of order ≤ 3. -/
lemma exists_smooth_sqrt {v : ℝ → ℝ} (hv : WindowProfile v) :
    ∃ (h : ℝ → ℝ) (η H : ℝ), 0 < η ∧ 1 ≤ H ∧ ContDiff ℝ 3 h ∧
      (∀ s : ℝ, |s| ≤ 1 / 2 + η → 0 < v s ∧ h s = Real.sqrt (v s)) ∧
      (∀ i : ℕ, i ≤ 3 → ∀ s : ℝ, |iteratedDeriv i h s| ≤ H) := by
  obtain ⟨η₀, m, hη₀, hm, hvm⟩ := exists_margin hv
  -- smooth cut-off: 1 on |s| ≤ ½ + η₀/2, 0 off |s| < ½ + η₀
  let χ : ContDiffBump (0:ℝ) := ⟨1/2 + η₀/2, 1/2 + η₀, by positivity, by linarith⟩
  set vt : ℝ → ℝ := fun s => χ s * v s + (1 - χ s) * m with hvt
  have hvt_ge : ∀ s, m ≤ vt s := by
    intro s
    have h0 := χ.nonneg (x := s)
    have h1 := χ.le_one (x := s)
    by_cases hs : |s| ≤ 1/2 + η₀
    · have := hvm s hs
      simp only [hvt]
      nlinarith
    · have hz : χ s = 0 := χ.zero_of_le_dist (by
        rw [Real.dist_eq, sub_zero]; exact (lt_of_not_ge hs).le)
      simp [hvt, hz]
  have hvt_cd : ContDiff ℝ 3 vt := by
    have hχ : ContDiff ℝ 3 χ := χ.contDiff
    have hv3 := hv.contDiff
    simp only [hvt]
    fun_prop
  set h : ℝ → ℝ := fun s => Real.sqrt (vt s) with hh
  have hh_cd : ContDiff ℝ 3 h := by
    rw [contDiff_iff_contDiffAt]
    intro s
    exact hvt_cd.contDiffAt.sqrt (ne_of_gt (hm.trans_le (hvt_ge s)))
  have hagree : ∀ s : ℝ, |s| ≤ 1/2 + η₀/2 → h s = Real.sqrt (v s) := by
    intro s hs
    have h1 : χ s = 1 := χ.one_of_mem_closedBall (by
      rw [mem_closedBall, Real.dist_eq, sub_zero]; exact hs)
    simp [hh, hvt, h1]
  -- uniform derivative bounds: continuous on a compact, locally constant outside
  set K' : Set ℝ := Icc (-(1 + η₀)) (1 + η₀) with hK'
  have hbound : ∀ i : ℕ, i ≤ 3 → ∃ C : ℝ, ∀ s ∈ K', |iteratedDeriv i h s| ≤ C := by
    intro i hi
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((hh_cd.continuous_iteratedDeriv i (by exact_mod_cast hi)).continuousOn (s := K'))
    exact ⟨C, fun s hs => by simpa [Real.norm_eq_abs] using hC s hs⟩
  obtain ⟨C0, hC0⟩ := hbound 0 (by norm_num)
  obtain ⟨C1, hC1⟩ := hbound 1 (by norm_num)
  obtain ⟨C2, hC2⟩ := hbound 2 (by norm_num)
  obtain ⟨C3, hC3⟩ := hbound 3 le_rfl
  set H : ℝ := max (max (max (max C0 C1) (max C2 C3)) (Real.sqrt m)) 1 with hHdef
  have hout : ∀ s : ℝ, s ∉ K' → ∀ i : ℕ, i ≤ 3 →
      iteratedDeriv i h s = if i = 0 then Real.sqrt m else 0 := by
    intro s hs i hi
    -- h is eventually the constant √m near s
    have hs' : 1 + η₀ < |s| := by
      simp only [hK', mem_Icc, not_and_or, not_le] at hs
      rcases hs with hs | hs
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hopen : IsOpen {t : ℝ | 1/2 + η₀ < |t|} := isOpen_lt continuous_const continuous_abs
    have hev : h =ᶠ[𝓝 s] (fun _ => Real.sqrt m) := by
      refine eventually_of_mem (hopen.mem_nhds (by show 1/2 + η₀ < |s|; linarith)) fun t ht => ?_
      have hz : χ t = 0 := χ.zero_of_le_dist (by
        rw [Real.dist_eq, sub_zero]; exact le_of_lt ht)
      simp [hh, hvt, hz]
    rw [hev.iteratedDeriv_eq i]
    simp only [iteratedDeriv_const]
  refine ⟨h, η₀ / 2, H, by positivity, le_max_right _ _, hh_cd, fun s hs => ⟨?_, hagree s hs⟩, ?_⟩
  · exact hm.trans_le (hvm s (by linarith))
  · intro i hi s
    by_cases hs : s ∈ K'
    · have hle : |iteratedDeriv i h s| ≤ max (max C0 C1) (max C2 C3) := by
        interval_cases i
        · exact (hC0 s hs).trans (le_trans (le_max_left _ _) (le_max_left _ _))
        · exact (hC1 s hs).trans (le_trans (le_max_right _ _) (le_max_left _ _))
        · exact (hC2 s hs).trans (le_trans (le_max_left _ _) (le_max_right _ _))
        · exact (hC3 s hs).trans (le_trans (le_max_right _ _) (le_max_right _ _))
      exact hle.trans (by rw [hHdef]; exact le_trans (le_max_left _ _) (le_max_left _ _))
    · rw [hout s hs i hi]
      split_ifs
      · rw [abs_of_nonneg (Real.sqrt_nonneg _), hHdef]
        exact le_trans (le_max_right _ _) (le_max_left _ _)
      · rw [abs_zero]; positivity

/-! ## §2. φ_v as (h̃(·/L))·φ, and the L¹ size of its derivatives -/

section Window
variable {ϱ : ℝ → ℝ} {L w : ℝ} {v h : ℝ → ℝ} {η H : ℝ}

/-- the smooth factor in the u-variable: u ↦ h̃(u/L). -/
def gfac (h : ℝ → ℝ) (L : ℝ) (u : ℝ) : ℝ := h (L⁻¹ * u)

lemma gfac_contDiff (hh : ContDiff ℝ 3 h) : ContDiff ℝ 3 (gfac h L) := by
  unfold gfac; fun_prop

lemma iteratedDeriv_gfac (hh : ContDiff ℝ 3 h) {i : ℕ} (hi : i ≤ 3) (u : ℝ) :
    iteratedDeriv i (gfac h L) u = (L⁻¹) ^ i * iteratedDeriv i h (L⁻¹ * u) := by
  have := iteratedDeriv_comp_const_mul (n := i) (hh.of_le (by exact_mod_cast hi)) L⁻¹
  exact congrFun this u

lemma abs_iteratedDeriv_gfac_le (hh : ContDiff ℝ 3 h)
    (hH : ∀ i : ℕ, i ≤ 3 → ∀ s : ℝ, |iteratedDeriv i h s| ≤ H)
    (hL : 0 < L) {i : ℕ} (hi : i ≤ 3) (u : ℝ) :
    |iteratedDeriv i (gfac h L) u| ≤ (L⁻¹) ^ i * H := by
  rw [iteratedDeriv_gfac hh hi, abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (hH i hi _) (by positivity)

/-- **φ_v = (h̃(·/L))·φ as functions** (h̃ = √v on |s| ≤ ½+η where v > 0; φ = 0 off [−L/2, L/2]). -/
lemma phiV_eq_mul (hϱ : TaperProfile ϱ) (hw : 0 < w) (hL : 0 < L) (hη : 0 < η)
    (hagree : ∀ s : ℝ, |s| ≤ 1 / 2 + η → 0 < v s ∧ h s = Real.sqrt (v s)) :
    (fun u => Real.sqrt (max 0 (v (u / L))) * Taper.phi ϱ L w u)
      = fun u => gfac h L u * Taper.phi ϱ L w u := by
  funext u
  by_cases hu : |u| ≤ L / 2
  · have hs : |u / L| ≤ 1 / 2 + η := by
      rw [abs_div, abs_of_pos hL, div_le_iff₀ hL]; nlinarith
    obtain ⟨hpos, heq⟩ := hagree _ hs
    rw [gfac, show L⁻¹ * u = u / L by rw [div_eq_inv_mul], heq, max_eq_right hpos.le]
  · have : Taper.phi ϱ L w u = 0 := Taper.phi_eq_zero hϱ hw (le_of_lt (lt_of_not_ge hu))
    simp [this]

/-- **‖(h̃(·/L)·φ)^{(k)}‖_{L¹} ≤ 8(2B+1)H** for 1 ≤ k ≤ 3 (L ≥ 1, w ≥ 1, 2w ≤ L), and integrability. -/
theorem integral_abs_iteratedDeriv_mul_le (hϱ : TaperProfile ϱ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ i : ℕ, 1 ≤ i → i ≤ 3 → ∀ x : ℝ, |iteratedDeriv i ϱ x| ≤ B)
    (hw1 : 1 ≤ w) (hwL : 2 * w ≤ L) (hL1 : 1 ≤ L)
    (hh : ContDiff ℝ 3 h) (hH1 : 1 ≤ H) (hH : ∀ i : ℕ, i ≤ 3 → ∀ s : ℝ, |iteratedDeriv i h s| ≤ H)
    {k : ℕ} (hk : 1 ≤ k) (hk3 : k ≤ 3) :
    Integrable (iteratedDeriv k (fun u => gfac h L u * Taper.phi ϱ L w u)) ∧
    ∫ u, |iteratedDeriv k (fun u => gfac h L u * Taper.phi ϱ L w u) u| ≤ 8 * (2 * B + 1) * H := by
  have hw : 0 < w := by linarith
  have hL : 0 < L := by linarith
  set φ : ℝ → ℝ := Taper.phi ϱ L w with hφdef
  set g : ℝ → ℝ := gfac h L with hgdef
  have hφcd : ContDiff ℝ 3 φ := Taper.phi_contDiff hϱ hw hwL
  have hgcd : ContDiff ℝ 3 g := gfac_contDiff hh
  have hF : (fun u => g u * φ u) = g * φ := rfl
  have hFcd : ContDiff ℝ 3 (g * φ) := hgcd.mul hφcd
  have hFcs : HasCompactSupport (g * φ) := (Taper.phi_hasCompactSupport hϱ hw).mul_left
  rw [hF]
  refine ⟨(hFcd.continuous_iteratedDeriv k (by exact_mod_cast hk3)).integrable_of_hasCompactSupport
    (FamilyHypsC3.hasCompactSupport_iteratedDeriv' hFcs k), ?_⟩
  -- the Leibniz majorant  G(u) := Σ_i C(k,i)·(L⁻¹)^i·H·|φ^{(k−i)}(u)|
  set G : ℝ → ℝ := fun u => ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * ((L⁻¹) ^ i * H * |iteratedDeriv (k - i) φ u|) with hG
  have hφj_int : ∀ j : ℕ, j ≤ 3 → Integrable (fun u => |iteratedDeriv j φ u|) := by
    intro j hj
    exact ((hφcd.continuous_iteratedDeriv j (by exact_mod_cast hj)).integrable_of_hasCompactSupport
      (FamilyHypsC3.hasCompactSupport_iteratedDeriv' (Taper.phi_hasCompactSupport hϱ hw) j)).abs
  have hGint : Integrable G := by
    refine integrable_finset_sum _ fun i hi => ?_
    exact ((hφj_int (k - i) (by omega)).const_mul _).const_mul _
  have hpt : ∀ u : ℝ, |iteratedDeriv k (g * φ) u| ≤ G u := by
    intro u
    rw [iteratedDeriv_mul (hgcd.contDiffAt.of_le (by exact_mod_cast hk3))
      (hφcd.contDiffAt.of_le (by exact_mod_cast hk3))]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hi' : i ≤ 3 := by have := Finset.mem_range.1 hi; omega
    rw [abs_mul, abs_mul, Nat.abs_cast, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg (α := ℝ) _)
    exact mul_le_mul_of_nonneg_right (abs_iteratedDeriv_gfac_le hh hH hL hi' u) (abs_nonneg _)
  -- each term integrates to at most (2B+1)·H
  have hterm : ∀ i ∈ Finset.range (k + 1),
      ∫ u, (k.choose i : ℝ) * ((L⁻¹) ^ i * H * |iteratedDeriv (k - i) φ u|)
        ≤ (k.choose i : ℝ) * ((2 * B + 1) * H) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.1 hi)
    rw [integral_const_mul, integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hLi : (L⁻¹) ^ i ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hL1)
    rcases Nat.lt_or_ge i k with hlt | hge
    · -- k − i ≥ 1: ramp bound 2B
      have hj1 : 1 ≤ k - i := by omega
      have hb := FamilyHypsC3.integral_abs_iteratedDeriv_phi_le (L := L) (w := w) hϱ hB0 hB hw hwL
        hj1 (by omega : k - i ≤ 3)
      have hwj : (w⁻¹) ^ (k - i) * w ≤ 1 := by
        obtain ⟨m, hm⟩ : ∃ m, k - i = m + 1 := ⟨k - i - 1, by omega⟩
        rw [hm, pow_succ, mul_assoc, inv_mul_cancel₀ hw.ne', mul_one]
        exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hw1)
      have hI : ∫ u, |iteratedDeriv (k - i) φ u| ≤ 2 * B := by
        refine hb.trans ?_
        nlinarith
      calc (L⁻¹) ^ i * H * ∫ u, |iteratedDeriv (k - i) φ u| ≤ 1 * H * (2 * B) := by
            gcongr
        _ ≤ (2 * B + 1) * H := by nlinarith
    · -- i = k: the factor L⁻¹ against ∫|φ| ≤ L
      have hik' : i = k := le_antisymm hik hge
      subst hik'
      simp only [Nat.sub_self, iteratedDeriv_zero]
      have hI : ∫ u, |φ u| ≤ L := integral_abs_phi_le hϱ hw hwL
      obtain ⟨m, hm⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      have hLk : (L⁻¹) ^ i * L ≤ 1 := by
        rw [hm, pow_succ, mul_assoc, inv_mul_cancel₀ hL.ne', mul_one]
        exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hL1)
      calc (L⁻¹) ^ i * H * ∫ u, |φ u| ≤ (L⁻¹) ^ i * H * L := by gcongr
        _ = ((L⁻¹) ^ i * L) * H := by ring
        _ ≤ 1 * H := by gcongr
        _ ≤ (2 * B + 1) * H := by nlinarith
  calc ∫ u, |iteratedDeriv k (g * φ) u| ≤ ∫ u, G u :=
        integral_mono_of_nonneg (Eventually.of_forall fun u => abs_nonneg _) hGint
          (Eventually.of_forall hpt)
    _ = ∑ i ∈ Finset.range (k + 1),
          ∫ u, (k.choose i : ℝ) * ((L⁻¹) ^ i * H * |iteratedDeriv (k - i) φ u|) := by
        rw [hG, integral_finset_sum _ (fun i hi =>
          ((hφj_int (k - i) (by omega)).const_mul _).const_mul _)]
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ((2 * B + 1) * H) := Finset.sum_le_sum hterm
    _ = (2:ℝ) ^ k * ((2 * B + 1) * H) := by
        rw [← Finset.sum_mul]
        congr 1
        have := Nat.sum_range_choose k
        exact_mod_cast this
    _ ≤ (2:ℝ) ^ 3 * ((2 * B + 1) * H) := by
        gcongr
        · norm_num
    _ = 8 * (2 * B + 1) * H := by ring

end Window

/-! ## §3. FamilyHyps for the profiled families -/

/-- **FamilyHyps for T ↦ P.atV v T**, every valid P with λ < 1 and every WindowProfile v. -/
theorem _root_.Zeta23.XiPrime.familyHyps_atV {P : Params} (hP : P.Valid) (hlam : P.lam < 1)
    {v : ℝ → ℝ} (hv : WindowProfile v) : FamilyHyps (P.atV v) := by
  obtain ⟨B, hB0, hB⟩ := FamilyHypsC3.exists_deriv_bound hP.taper
  obtain ⟨h, η, H, hη, hH1, hh, hagree, hH⟩ := exists_smooth_sqrt hv
  have hw1 : 1 ≤ P.w := hP.one_le_w
  have hw : 0 < P.w := by linarith
  refine ⟨⟨P.lam, hP.lam_pos, hlam, fun _ => rfl⟩, ?_⟩
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp
    ((Assembly.tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop (8 * P.w))
  refine ⟨8 * (2 * B + 1) * H, T₀, fun T hT => ?_⟩
  have h8 : 8 * P.w ≤ P.L T := hT₀ T hT
  have hwL : 2 * P.w ≤ P.L T := by linarith
  have hL1 : 1 ≤ P.L T := by linarith
  have hL0 : 0 < P.L T := by linarith
  have hLT : (P.atV v T).L T = P.L T := rfl
  have hphi : (P.atV v T).phi T = P.phiV v T := Params.atV_phi_valid T hP hv.even
  have hF : P.phiV v T = fun u => gfac h (P.L T) u * Taper.phi P.ϱ (P.L T) P.w u := by
    have := phiV_eq_mul (L := P.L T) (w := P.w) hP.taper hw hL0 hη hagree
    funext u
    rw [Params.phiV_eq]
    exact congrFun this u
  rw [hphi, hLT]
  refine ⟨?_, ?_, fun u => Params.phiV_even P v T hv.even u, fun u => ?_, fun j hj1 hj3 => ?_⟩
  · rw [hF]; exact (gfac_contDiff hh).mul (Taper.phi_contDiff hP.taper hw hwL)
  · refine closure_minimal ?_ isClosed_Icc
    intro u hu
    have hφ : Taper.phi P.ϱ (P.L T) P.w u ≠ 0 := by
      intro h0; apply hu; rw [Params.phiV_eq, h0, mul_zero]
    exact Taper.phi_support_subset hP.taper hw hφ
  · rw [Params.phiV_eq, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (Taper.phi_nonneg hP.taper u)]
    have h1 : Real.sqrt (max 0 (v (u / P.L T))) ≤ 1 :=
      Real.sqrt_le_one.mpr (max_le zero_le_one (hv.le_one _)) |> fun h => by simpa using h
    have h2 := Taper.phi_le_one hP.taper (L := P.L T) (w := P.w) u
    have h3 := Taper.phi_nonneg hP.taper (L := P.L T) (w := P.w) u
    nlinarith [Real.sqrt_nonneg (max 0 (v (u / P.L T)))]
  · rw [hF]
    exact integral_abs_iteratedDeriv_mul_le hP.taper hB0 hB hw1 hwL hL1 hh hH1 hH hj1 hj3

/-- the quartic instance: the 0.86864 / 0.93432 ξ′ window family. -/
theorem _root_.Zeta23.XiPrime.familyHyps_atV_quartic {P : Params} (hP : P.Valid) (hlam : P.lam < 1)
    (hv : WindowProfile vQuartic) : FamilyHyps (P.atV vQuartic) :=
  familyHyps_atV hP hlam hv

end FamilyHypsV
end XiPrime
end Zeta23
