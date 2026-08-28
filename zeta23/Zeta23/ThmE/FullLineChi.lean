/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/FullLineChi.lean — statements for the χ-EF endgame: good heights for L(s,χ)
and zero-sum summability.
All ζ-side templates are named in each docstring; the f-generic machinery
(vertical_line_shift, norm_Hfn_le, exists_far_point, FoldChi, LGrowth) is proved
elsewhere in the repository.
-/
import Zeta23.ThmE.ContourChi
import Zeta23.ThmE.LocalCountChi
import Zeta23.ThmE.GzGpChi
import Zeta23.WeilEF.GoodHeights
import Zeta23.ThmE.LandauChi
import Zeta23.WeilEF.ZeroSummabilityGen

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Complex MeasureTheory Real Set Topology Filter DirichletCharacter
open scoped BigOperators

namespace Zeta23
namespace ThmE

open Zeta23.WeilEF

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- a zero of L(·,χ) (χ ≠ 1) in the closed ball of radius r < 2 about 2 + t i is a nontrivial zero. -/
lemma isNontrivialZeroL_of_mem_closedBall (hχ1 : χ ≠ 1) {t r : ℝ} (hr : r < 2) {ρ : ℂ}
    (hρ : ρ ∈ Metric.closedBall (2 + t * I) r) (hz : χ.LFunction ρ = 0) : IsNontrivialZeroL χ ρ := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hρ
  have hre : |ρ.re - 2| ≤ r := by
    have := Complex.abs_re_le_norm (ρ - (2 + t * I))
    simp at this; linarith
  refine ⟨hz, by rw [abs_le] at hre; linarith, ?_⟩
  by_contra h
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (not_lt.mp h) hz

/-- a finite set of nontrivial zeros with ordinates in (a, a+6] has total multiplicity
≤ 6 A₀ log(|a|+9) (six unit windows of the local count). -/
lemma sum_mult_six_windows_L (hs : LSeam χ) {A₀ : ℝ}
    (hLC : Tail.LocalCount (fun ρ : (LZeros hs).carrier => (ρ : ℂ).im)
      (fun ρ : (LZeros hs).carrier => (LZeros hs).mult ρ) A₀)
    {a : ℤ} (F : Finset (LZeros hs).carrier)
    (hF : ∀ ρ ∈ F, (a : ℝ) < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ (a : ℝ) + 6) :
    ∑ ρ ∈ F, ((LZeros hs).mult ρ : ℝ) ≤ 6 * (A₀ * Real.log (|(a : ℝ)| + 9)) := by
  classical
  have hA₀ := hLC.A₀_pos.le
  -- key k : ℕ with a + k < Im ≤ a + k + 1
  set key : (LZeros hs).carrier → ℕ := fun ρ => (⌈(ρ : ℂ).im⌉ - a - 1).toNat with hkey
  have hkey_spec : ∀ ρ ∈ F, ((a : ℝ) + key ρ < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ (a : ℝ) + key ρ + 1)
      ∧ key ρ < 6 := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := hF ρ hρ
    have hc1 := Int.le_ceil (ρ : ℂ).im
    have hc2 := Int.ceil_lt_add_one (ρ : ℂ).im
    have hlo : a + 1 ≤ ⌈(ρ : ℂ).im⌉ := by
      have : (a : ℝ) < ⌈(ρ : ℂ).im⌉ := lt_of_lt_of_le h1 hc1
      have : a < ⌈(ρ : ℂ).im⌉ := by exact_mod_cast this
      omega
    have hhi : ⌈(ρ : ℂ).im⌉ ≤ a + 6 := by
      have : (⌈(ρ : ℂ).im⌉ : ℝ) < (a : ℝ) + 6 + 1 := by linarith
      have : ⌈(ρ : ℂ).im⌉ < a + 6 + 1 := by exact_mod_cast this
      omega
    have hk : ((key ρ : ℕ) : ℤ) = ⌈(ρ : ℂ).im⌉ - a - 1 := by
      simp only [hkey]; rw [Int.toNat_of_nonneg (by omega)]
    have hkR : ((key ρ : ℕ) : ℝ) = (⌈(ρ : ℂ).im⌉ : ℝ) - a - 1 := by exact_mod_cast hk
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    have : ((key ρ : ℕ) : ℤ) < 6 := by omega
    exact_mod_cast this
  have h := Tail.sum_mult_le_of_windows F (fun ρ => (LZeros hs).mult ρ) key 6
    (C := A₀ * Real.log (|(a : ℝ)| + 9)) (fun ρ hρ => (hkey_spec ρ hρ).2) (fun k hk => by
      have hw := hLC.window ((a : ℝ) + k) (F.filter fun ρ => key ρ = k) (fun ρ hρ => by
        simp only [Finset.mem_filter] at hρ
        have := (hkey_spec ρ hρ.1).1
        rw [hρ.2] at this; exact this)
      refine hw.trans (mul_le_mul_of_nonneg_left ?_ hA₀)
      apply Real.log_le_log (by positivity)
      have : |(a : ℝ) + k| ≤ |(a : ℝ)| + k := by
        calc |(a:ℝ) + k| ≤ |(a:ℝ)| + |(k:ℝ)| := abs_add_le _ _
          _ = |(a:ℝ)| + k := by rw [Nat.abs_cast]
      have hk6 : (k : ℝ) < 6 := by exact_mod_cast hk
      linarith)
  simpa using h

/-- card ≤ total multiplicity (each nontrivial zero has multiplicity ≥ 1). -/
lemma card_le_sum_mult_L (hs : LSeam χ) (F : Finset (LZeros hs).carrier) :
    (F.card : ℝ) ≤ ∑ ρ ∈ F, ((LZeros hs).mult ρ : ℝ) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun ρ _ => ?_
  exact_mod_cast (LZeros hs).one_le_mult ρ ρ.2

set_option maxHeartbeats 1600000 in
/-- Good heights for L(s,χ) (template: Zeta23.WeilEF.good_heights; gap-selection via
exists_far_point + localCountChi; the L'/L bound via L_logDeriv_partial_fraction's count
conjunct, both ±R as in the ζ-case). -/
theorem good_heights_chi (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 7 ≤ j →
    ∃ R : ℝ, (j : ℝ) ≤ R ∧ R ≤ (j : ℝ) + 1 ∧
    ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1/2 ≤ s.re → s.re ≤ 2 →
      χ.LFunction s ≠ 0 ∧
      ‖logDeriv χ.LFunction s‖ ≤ C * (Real.log ((q:ℝ) * ((j : ℝ) + 3))) ^ 2 := by
  have hχ1 : χ ≠ 1 := ne_one_of_primitive hq hprim
  have hs : LSeam χ := LSeam_of hq hprim
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.le
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  classical
  obtain ⟨C, hC, hpf⟩ := L_logDeriv_partial_fraction hχ1
  obtain ⟨A₀, hA₀, hloc⟩ := localCountChi hq hprim
  have hloc' : ∀ t : ℝ, ((LZeros hs).N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3) := by
    intro t; rw [LZeros_N]; exact hloc t
  have hLC := Tail.LocalCount.ofWindowCount (LZeros hs) hA₀ hloc'
  refine ⟨2 * C * (48 * A₀ + 3), by positivity, fun j hj => ?_⟩
  have hj7 : (7 : ℝ) ≤ j := by exact_mod_cast hj
  set Lj : ℝ := Real.log ((j : ℝ) + 3) with hLj
  set Lg : ℝ := Real.log ((q : ℝ) * ((j : ℝ) + 3)) with hLg
  have hLgq : Lg = Real.log (q : ℝ) + Lj := by
    rw [hLg, hLj, Real.log_mul (by positivity) (by positivity)]
  have hLj1 : 1 ≤ Lj := by
    rw [hLj, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have hLjLg : Lj ≤ Lg := by rw [hLgq]; linarith
  have hLg1 : 1 ≤ Lg := hLj1.trans hLjLg
  have hlog2j : Real.log 2 ≤ Lj := by
    rw [hLj]; exact Real.log_le_log (by norm_num) (by linarith)
  have hlog2 : Real.log 2 ≤ Lg := hlog2j.trans hLjLg
  -- the two finite families of zeros near height ±j
  set Wp : Set ℂ := (LZeros hs).window ((j : ℝ) - 3) ((j : ℝ) + 3) with hWp
  set Wm : Set ℂ := (LZeros hs).window (-(j : ℝ) - 4) (-(j : ℝ) + 2) with hWm
  have hWpfin : ((fun ρ : (LZeros hs).carrier => (ρ : ℂ)) ⁻¹' Wp).Finite :=
    ((LZeros hs).finite_window _ _).preimage Subtype.val_injective.injOn
  have hWmfin : ((fun ρ : (LZeros hs).carrier => (ρ : ℂ)) ⁻¹' Wm).Finite :=
    ((LZeros hs).finite_window _ _).preimage Subtype.val_injective.injOn
  set Fp : Finset (LZeros hs).carrier := hWpfin.toFinset with hFp
  set Fm : Finset (LZeros hs).carrier := hWmfin.toFinset with hFm
  have hFp_mem : ∀ ρ : (LZeros hs).carrier, ρ ∈ Fp ↔ (ρ : ℂ) ∈ Wp := fun ρ => by
    rw [hFp, Set.Finite.mem_toFinset]; rfl
  have hFm_mem : ∀ ρ : (LZeros hs).carrier, ρ ∈ Fm ↔ (ρ : ℂ) ∈ Wm := fun ρ => by
    rw [hFm, Set.Finite.mem_toFinset]; rfl
  set S : Finset ℝ := Fp.image (fun ρ : (LZeros hs).carrier => (ρ : ℂ).im)
    ∪ Fm.image (fun ρ : (LZeros hs).carrier => -(ρ : ℂ).im) with hS
  -- count: |S| ≤ 24 A₀ Lg
  have hcountp : ∑ ρ ∈ Fp, ((LZeros hs).mult ρ : ℝ) ≤ 6 * (A₀ * (2 * Lg)) := by
    have h := sum_mult_six_windows_L hs hLC (a := (j : ℤ) - 3) Fp (fun ρ hρ => by
      have := ((hFp_mem ρ).mp hρ).2; push_cast; constructor <;> linarith [this.1, this.2])
    refine h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hLC.A₀_pos.le)
      (by norm_num))
    · have : |((j : ℤ) - 3 : ℤ)| = (j : ℤ) - 3 := abs_of_nonneg (by omega)
      have habs : |(((j:ℤ) - 3 : ℤ) : ℝ)| = (j : ℝ) - 3 := by
        rw [← Int.cast_abs, this]; push_cast; ring
      rw [habs]
      calc Real.log ((j:ℝ) - 3 + 9) ≤ Real.log (2 * ((j:ℝ) + 3)) :=
            Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 2 + Lj := by rw [Real.log_mul (by norm_num) (by linarith)]
        _ ≤ 2 * Lg := by linarith
  have hcountm : ∑ ρ ∈ Fm, ((LZeros hs).mult ρ : ℝ) ≤ 6 * (A₀ * (2 * Lg)) := by
    have h := sum_mult_six_windows_L hs hLC (a := -(j : ℤ) - 4) Fm (fun ρ hρ => by
      have := ((hFm_mem ρ).mp hρ).2; push_cast; constructor <;> linarith [this.1, this.2])
    refine h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hLC.A₀_pos.le)
      (by norm_num))
    · have : |(-(j : ℤ) - 4 : ℤ)| = (j : ℤ) + 4 := by
        rw [abs_of_nonpos (by omega)]; ring
      have habs : |((-(j:ℤ) - 4 : ℤ) : ℝ)| = (j : ℝ) + 4 := by
        rw [← Int.cast_abs, this]; push_cast; ring
      rw [habs]
      calc Real.log ((j:ℝ) + 4 + 9) ≤ Real.log (((j:ℝ) + 3) ^ 2) := by
            apply Real.log_le_log (by linarith); nlinarith
        _ = 2 * Lj := by rw [Real.log_pow]; push_cast; ring
        _ ≤ 2 * Lg := by linarith
  have hcard : (S.card : ℝ) ≤ 24 * A₀ * Lg := by
    have h1 : S.card ≤ Fp.card + Fm.card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
    have h1' : (S.card : ℝ) ≤ Fp.card + Fm.card := by exact_mod_cast h1
    linarith [card_le_sum_mult_L hs Fp, card_le_sum_mult_L hs Fm]
  -- the good height
  obtain ⟨R, hR1, hR2, hfar⟩ := exists_far_point S j
  set δ : ℝ := 1 / (2 * ((S.card : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδinv : 1 / δ = 2 * ((S.card : ℝ) + 1) := by rw [hδ, one_div_one_div]
  refine ⟨R, hR1, hR2, fun s hs' hσ1 hσ2 => ?_⟩
  have hR6 : (6 : ℝ) ≤ |R| := by rw [abs_of_nonneg (by linarith)]; linarith
  have hR6' : (6 : ℝ) ≤ |-R| := by rwa [abs_neg]
  have hlogR : Real.log ((q : ℝ) * (|R| + 3)) ≤ 2 * Lg := by
    rw [abs_of_nonneg (by linarith), Real.log_mul (by positivity) (by linarith)]
    have : Real.log (R + 3) ≤ Real.log 2 + Lj := by
      calc Real.log (R + 3) ≤ Real.log (2 * ((j:ℝ) + 3)) := Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 2 + Lj := by rw [Real.log_mul (by norm_num) (by linarith)]
    rw [hLgq]; linarith
  -- s in the conclusion ball of the partial fraction at t = s.im
  have hsball : s ∈ Metric.closedBall (2 + s.im * I) (3 / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have : s - (2 + s.im * I) = ((s.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  -- every zero in the pf ball at height s.im = ±R has its (signed) ordinate in S
  have hordS : ∀ ρ : ℂ, ρ ∈ Metric.closedBall (2 + s.im * I) (22/25 * (91/50)) →
      χ.LFunction ρ = 0 → δ ≤ ‖s - ρ‖ := by
    intro ρ hρ hz
    have hnt := isNontrivialZeroL_of_mem_closedBall hχ1 (by norm_num) hρ hz
    have him := im_mem_of_mem_closedBall hρ
    rw [abs_le] at him
    have hρc : ρ ∈ (LZeros hs).carrier := by rw [LZeros_carrier]; exact hnt
    refine le_trans ?_ (abs_im_sub_le_norm_sub s ρ)
    rcases hs' with hsR | hsR
    · -- Im ρ ∈ S via Fp
      have hmem : (⟨ρ, hρc⟩ : (LZeros hs).carrier) ∈ Fp := by
        rw [hFp_mem]
        refine ⟨hρc, ?_, ?_⟩ <;> rw [hsR] at him <;> nlinarith
      have : ρ.im ∈ S := by
        rw [hS, Finset.mem_union]; left
        exact Finset.mem_image.mpr ⟨(⟨ρ, hρc⟩ : (LZeros hs).carrier), hmem, rfl⟩
      have := hfar _ this
      rwa [hsR]
    · have hmem : (⟨ρ, hρc⟩ : (LZeros hs).carrier) ∈ Fm := by
        rw [hFm_mem]
        refine ⟨hρc, ?_, ?_⟩ <;> rw [hsR] at him <;> nlinarith
      have : -ρ.im ∈ S := by
        rw [hS, Finset.mem_union]; right
        exact Finset.mem_image.mpr ⟨(⟨ρ, hρc⟩ : (LZeros hs).carrier), hmem, rfl⟩
      have := hfar _ this
      rw [hsR, show |(-R) - ρ.im| = |R - (-ρ.im)| by rw [← abs_neg]; ring_nf]
      exact this
  -- L(s,χ) ≠ 0: s itself would be a zero in the ball at distance 0
  have hζ : χ.LFunction s ≠ 0 := by
    intro hz
    have h0 := hordS s (Metric.closedBall_subset_closedBall (by norm_num) hsball) hz
    simp at h0; linarith
  refine ⟨hζ, ?_⟩
  -- apply the partial fraction at t := s.im
  have ht6 : (6 : ℝ) ≤ |s.im| := by rcases hs' with h | h <;> rw [h] <;> assumption
  obtain ⟨Z, hZ, hZsum, hZpf⟩ := hpf s.im ht6
  have hZpf' := hZpf s hsball hζ
  have hlogt : Real.log ((q : ℝ) * (|s.im| + 3)) ≤ 2 * Lg := by
    rcases hs' with h | h
    · rw [h]; exact hlogR
    · rw [h, abs_neg]; exact hlogR
  -- the sum over Z
  have hZmem : ∀ ρ ∈ Z, ρ ∈ Metric.closedBall (2 + s.im * I) (22/25 * (91/50)) ∧ χ.LFunction ρ = 0 := by
    intro ρ hρ
    have : ρ ∈ (↑Z : Set ℂ) := hρ
    rw [hZ] at this
    exact this
  have hsumZ : ‖∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) / (s - ρ)‖
      ≤ (C * (2 * Lg)) * (1 / δ) := by
    calc ‖∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ Z, ‖(analyticOrderNatAt χ.LFunction ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / δ) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          obtain ⟨hρb, hρz⟩ := hZmem ρ hρ
          have hd := hordS ρ hρb hρz
          have hsρ : 0 < ‖s - ρ‖ := lt_of_lt_of_le hδpos hd
          rw [norm_div, Complex.norm_natCast, div_eq_mul_one_div]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact one_div_le_one_div_of_le hδpos hd
      _ = (∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℝ)) * (1 / δ) := by rw [Finset.sum_mul]
      _ ≤ (C * (2 * Lg)) * (1 / δ) := by
          refine mul_le_mul_of_nonneg_right (hZsum.trans ?_) (one_div_nonneg.mpr hδpos.le)
          exact mul_le_mul_of_nonneg_left hlogt hC.le
  -- assemble
  have hmain : ‖logDeriv χ.LFunction s‖ ≤ C * (2 * Lg) + (C * (2 * Lg)) * (1 / δ) := by
    have h1 : ‖logDeriv χ.LFunction s‖
        ≤ ‖logDeriv χ.LFunction s - ∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) / (s - ρ)‖
          + ‖∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) / (s - ρ)‖ := norm_le_norm_sub_add _ _
    have h2 := hZpf'.trans (mul_le_mul_of_nonneg_left hlogt hC.le)
    linarith [hsumZ]
  refine hmain.trans ?_
  rw [hδinv]
  have hc := hcard
  have hA := hLC.A₀_pos.le
  -- C·2Lg·(1 + 2(n+1)) ≤ 2C(48A₀+3) Lg²
  have : C * (2 * Lg) + C * (2 * Lg) * (2 * ((S.card : ℝ) + 1))
      = 2 * C * Lg * (2 * (S.card : ℝ) + 3) := by ring
  rw [this]
  have hn : 2 * (S.card : ℝ) + 3 ≤ (48 * A₀ + 3) * Lg := by nlinarith
  calc 2 * C * Lg * (2 * (S.card : ℝ) + 3) ≤ 2 * C * Lg * ((48 * A₀ + 3) * Lg) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
    _ = 2 * C * (48 * A₀ + 3) * Real.log ((q : ℝ) * ((j : ℝ) + 3)) ^ 2 := by rw [hLg]; ring

/-- Zero-sum summability for L(s,χ) (template: Zeta23.WeilEF.EF_zero_sum_summable via the
local count; with good_heights_chi). -/
theorem EF_zero_sum_summable_chi (hq : 1 < q) (hprim : χ.IsPrimitive)
    {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Summable (fun ρ : (LZeros (LSeam_of hq hprim)).carrier =>
      (((LZeros (LSeam_of hq hprim)).mult ρ : ℂ)) * paperFT k (gammaOf ρ)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := localCountChi hq hprim
  have hloc' : ∀ t : ℝ, ((LZeros (LSeam_of hq hprim)).N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3) := by
    intro t; rw [LZeros_N]; exact hloc t
  exact Zeta23.WeilEF.EF_zero_sum_summable_gen (LZeros (LSeam_of hq hprim)) hA₀ hloc' hk hkc

end ThmE
end Zeta23
