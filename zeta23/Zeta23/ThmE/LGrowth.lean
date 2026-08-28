/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/LGrowth.lean — growth of L(s,χ) in vertical strips (input to
H-RvM(χ): the local count, Backlund's bound and the contour count all consume it; analogue of
Zeta23/RvM/ZetaGrowth.lean).

For a nontrivial character χ mod q the partial sums S(t) := Σ_{1≤k≤t} χ(k) are bounded by q, so Abel
summation gives the representation
    L(s,χ) = s ∫_1^∞ S(t) t^{−s−1} dt        (Re s > 0)
(Mathlib: LSeries_eq_mul_integral for Re s > 1 + LFunction_eq_LSeries; extended to Re s > 0 by
analytic continuation — the right side is holomorphic there and L(·,χ) is entire). Consequences:
 • `norm_LFunction_le_of_re_pos` : ‖L(s,χ)‖ ≤ q·‖s‖ / Re s  (Re s > 0);
 • `LFunction_growth_right` : ∃ A C, ∀ s, 0.15 ≤ Re s → ‖L(s,χ)‖ ≤ C·(|Im s|+3)^A (C depends on q);
 • `norm_LFunction_sub_one_le` : ‖L(s,χ) − 1‖ ≤ π²/6 − 1 on Re s ≥ 2, hence 1/3 ≤ ‖L(2+it,χ)‖ ≤ π²/6.
The continuation to Re s > 0 uses that the
Abel integral is a Mellin transform (Mathlib's mellin_differentiableAt_of_isBigO_rpow) + the identity theorem.
[Dav00 §§ 4, 16; Tit86 §2.1 analogue]
-/
import Zeta23.ThmE.SeamL
import Mathlib.Analysis.MellinTransform
import Zeta23.RvM.ZetaGrowth
import Mathlib.NumberTheory.LSeries.SumCoeff

open Complex Set MeasureTheory Filter Topology DirichletCharacter

noncomputable section

namespace Zeta23
namespace ThmE

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-! ## Partial sums of a nontrivial character -/

/-- A full period of a nontrivial character sums to zero, from any starting point. -/
lemma sum_Ico_add_period_eq_zero (hχ1 : χ ≠ 1) (N : ℕ) :
    ∑ k ∈ Finset.Ico N (N + q), χ (k : ZMod q) = 0 := by
  rw [Finset.sum_Ico_eq_sum_range, add_tsub_cancel_left]
  have hinj : ∀ a ∈ Finset.range q, ∀ b ∈ Finset.range q,
      ((N + a : ℕ) : ZMod q) = ((N + b : ℕ) : ZMod q) → a = b := by
    intro a ha b hb hab
    rw [Finset.mem_range] at ha hb
    have h := (ZMod.natCast_eq_natCast_iff' (N + a) (N + b) q).mp hab
    have h' : a % q = b % q := by
      have := Nat.ModEq.add_left_cancel' N (h : N + a ≡ N + b [MOD q])
      exact this
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'
  have himage : (Finset.range q).image (fun k : ℕ => ((N + k : ℕ) : ZMod q)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn (fun a ha b hb h => hinj a ha b hb h), Finset.card_range,
      ZMod.card]
  calc ∑ k ∈ Finset.range q, χ ((N + k : ℕ) : ZMod q)
      = ∑ a ∈ (Finset.range q).image (fun k : ℕ => ((N + k : ℕ) : ZMod q)), χ a :=
        (Finset.sum_image hinj).symm
    _ = ∑ a, χ a := by rw [himage]
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ1

lemma sum_range_add_period (hχ1 : χ ≠ 1) (N : ℕ) :
    ∑ k ∈ Finset.range (N + q), χ (k : ZMod q) = ∑ k ∈ Finset.range N, χ (k : ZMod q) := by
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le N) (Nat.le_add_right N q),
    sum_Ico_add_period_eq_zero hχ1 N, add_zero, ← Finset.range_eq_Ico]

lemma sum_range_add_mul_period (hχ1 : χ ≠ 1) (N m : ℕ) :
    ∑ k ∈ Finset.range (N + q * m), χ (k : ZMod q) = ∑ k ∈ Finset.range N, χ (k : ZMod q) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, ← add_assoc, sum_range_add_period hχ1, ih]

lemma norm_sum_range_le (hχ1 : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, χ (k : ZMod q)‖ ≤ (q : ℝ) - 1 := by
  have hn : n = n % q + q * (n / q) := (Nat.mod_add_div n q).symm
  rw [hn, sum_range_add_mul_period hχ1]
  have hlt : ((n % q : ℕ) : ℝ) + 1 ≤ q := by exact_mod_cast Nat.mod_lt n (NeZero.pos q)
  calc ‖∑ k ∈ Finset.range (n % q), χ (k : ZMod q)‖
      ≤ ∑ k ∈ Finset.range (n % q), ‖χ (k : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (n % q), (1 : ℝ) := Finset.sum_le_sum (fun k _ => χ.norm_le_one _)
    _ = ((n % q : ℕ) : ℝ) := by simp
    _ ≤ q - 1 := by linarith

/-- Partial sums of a nontrivial character are bounded by the modulus:
‖Σ_{k=1}^{n} χ(k)‖ ≤ q. -/
theorem norm_sum_Icc_le (hχ1 : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)‖ ≤ q := by
  have hsplit : ∑ k ∈ Finset.range (n + 1), χ (k : ZMod q)
      = χ ((0 : ℕ) : ZMod q) + ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n)]
    congr 1
  have h1 := norm_sum_range_le hχ1 (n + 1)
  rw [hsplit] at h1
  have h0 : ‖χ ((0 : ℕ) : ZMod q)‖ ≤ 1 := χ.norm_le_one _
  calc ‖∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)‖
      = ‖(χ ((0 : ℕ) : ZMod q) + ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)) - χ ((0 : ℕ) : ZMod q)‖ := by
        congr 1; ring
    _ ≤ ‖χ ((0 : ℕ) : ZMod q) + ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)‖ + ‖χ ((0 : ℕ) : ZMod q)‖ :=
        norm_sub_le _ _
    _ ≤ (q - 1) + 1 := add_le_add h1 h0
    _ = q := by ring

/-! ## The Abel integral as a Mellin transform; continuation to Re s > 0 -/

/-- The Abel kernel: t ↦ 1_{t>1}·Σ_{1≤k≤t} χ(k). -/
def abelKernel (χ : DirichletCharacter ℂ q) : ℝ → ℂ :=
  (Set.Ioi (1 : ℝ)).indicator fun t => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q)

lemma norm_abelKernel_le (hχ1 : χ ≠ 1) (t : ℝ) : ‖abelKernel χ t‖ ≤ q := by
  unfold abelKernel
  by_cases ht : t ∈ Set.Ioi (1 : ℝ)
  · rw [Set.indicator_of_mem ht]; exact norm_sum_Icc_le hχ1 _
  · rw [Set.indicator_of_notMem ht, norm_zero]; positivity

omit [NeZero q] in
lemma measurable_abelKernel : Measurable (abelKernel χ) := by
  unfold abelKernel
  refine Measurable.indicator ?_ measurableSet_Ioi
  exact (measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q))).comp
    Nat.measurable_floor

lemma locallyIntegrable_abelKernel (hχ1 : χ ≠ 1) : LocallyIntegrable (abelKernel χ) := by
  rw [MeasureTheory.locallyIntegrable_iff]
  intro K hK
  refine Measure.integrableOn_of_bounded (M := (q : ℝ)) hK.measure_lt_top.ne
    measurable_abelKernel.aestronglyMeasurable ?_
  exact Eventually.of_forall (fun t => norm_abelKernel_le hχ1 t)

omit [NeZero q] in
lemma mellin_abelKernel (s : ℂ) :
    mellin (abelKernel χ) (-s)
      = ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(s + 1)) := by
  unfold mellin
  have hpt : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) • abelKernel χ t
      = (Set.Ioi (1 : ℝ)).indicator
          (fun t : ℝ => (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(s + 1))) t := by
    intro t
    unfold abelKernel
    by_cases ht : t ∈ Set.Ioi (1 : ℝ)
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, smul_eq_mul, mul_comm]
      congr 2; ring
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
  simp_rw [hpt]
  rw [setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi]
  norm_num

lemma differentiableAt_mellin_abelKernel (hχ1 : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => mellin (abelKernel χ) (-z)) s := by
  have htop : abelKernel χ =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    apply Asymptotics.IsBigO.of_bound (q : ℝ)
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [neg_zero, Real.rpow_zero, Real.norm_of_nonneg zero_le_one, mul_one]
    exact norm_abelKernel_le hχ1 t
  have hbot : abelKernel χ =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(-(s.re + 1)))) := by
    have hev : abelKernel χ =ᶠ[𝓝[>] 0] (fun _ => (0 : ℂ)) := by
      have : Set.Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)
      filter_upwards [this] with t ht
      unfold abelKernel
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_Ioi, not_lt]
      exact le_of_lt ht
    exact (Asymptotics.isBigO_zero _ _).congr' hev.symm EventuallyEq.rfl
  have h := mellin_differentiableAt_of_isBigO_rpow (E := ℂ) (a := 0) (b := -(s.re + 1))
    (f := abelKernel χ) (s := -s) ((locallyIntegrable_abelKernel hχ1).locallyIntegrableOn _)
    htop (by simpa using hs) hbot (by simp)
  exact h.comp s differentiableAt_id.neg

/-- **Abel-summation representation on Re s > 0**:
L(s,χ) = s · ∫_1^∞ (Σ_{1≤k≤t} χ(k)) · t^{−(s+1)} dt. -/
theorem LFunction_eq_mul_integral (hχ1 : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    χ.LFunction s = s * ∫ t in Set.Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(s + 1)) := by
  set G : ℂ → ℂ := fun z => z * mellin (abelKernel χ) (-z) with hG
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hG_an : AnalyticOnNhd ℂ G {z : ℂ | 0 < z.re} := by
    apply DifferentiableOn.analyticOnNhd _ hopen
    intro z hz
    exact (differentiableAt_id.mul (differentiableAt_mellin_abelKernel hχ1 hz)).differentiableWithinAt
  have hL_an : AnalyticOnNhd ℂ χ.LFunction {z : ℂ | 0 < z.re} :=
    (LFunction_analyticOnNhd hχ1).mono (Set.subset_univ _)
  have heq : ∀ z : ℂ, 1 < z.re → χ.LFunction z = G z := by
    intro z hz
    have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖χ (k : ZMod q)‖) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards with n
      rw [Real.rpow_one, one_mul, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _),
        Real.norm_of_nonneg (Nat.cast_nonneg n)]
      calc ∑ k ∈ Finset.Icc 1 n, ‖χ (k : ZMod q)‖ ≤ ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) :=
            Finset.sum_le_sum fun k _ => χ.norm_le_one _
        _ = n := by simp
    rw [LFunction_eq_LSeries χ hz,
      LSeries_eq_mul_integral' (fun n : ℕ => χ (n : ZMod q)) zero_le_one hz hO]
    simp only [hG, mellin_abelKernel]
  have hpre : IsPreconnected {z : ℂ | 0 < z.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have h2 : (2 : ℂ) ∈ {z : ℂ | 0 < z.re} := by simp
  have hev : χ.LFunction =ᶠ[𝓝 2] G := by
    have : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [this] with z hz using heq z hz
  have hEq := hL_an.eqOn_of_preconnected_of_eventuallyEq hG_an hpre h2 hev hs
  rw [hEq]
  simp only [hG, mellin_abelKernel]

/-! ## Growth bounds -/

/-- **Half-plane bound**: ‖L(s,χ)‖ ≤ q·‖s‖/Re s for Re s > 0. -/
theorem norm_LFunction_le_of_re_pos (hχ1 : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖χ.LFunction s‖ ≤ q * ‖s‖ / s.re := by
  rw [LFunction_eq_mul_integral hχ1 hs, norm_mul]
  have hmaj : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-(s.re + 1))) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  have hint : ‖∫ t in Set.Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(s + 1))‖ ≤ q / s.re := by
    calc ‖∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(s + 1))‖
        ≤ ∫ t in Set.Ioi (1 : ℝ), (q : ℝ) * t ^ (-(s.re + 1)) := by
          apply norm_integral_le_of_norm_le hmaj
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have ht0 : 0 < t := lt_trans zero_lt_one ht
          rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
          have hre : (-(s + 1)).re = -(s.re + 1) := by simp
          rw [hre]
          exact mul_le_mul_of_nonneg_right (norm_sum_Icc_le hχ1 _) (by positivity)
      _ = q * ∫ t in Set.Ioi (1 : ℝ), t ^ (-(s.re + 1)) := integral_const_mul _ _
      _ = q / s.re := by
          rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
          have : -(s.re + 1) + 1 = -s.re := by ring
          rw [this]
          field_simp
  calc ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(s + 1))‖
      ≤ ‖s‖ * (q / s.re) := by gcongr
    _ = q * ‖s‖ / s.re := by ring

/-- δ-form, linear: for Re s ≥ δ > 0, ‖L(s,χ)‖ ≤ q·(1 + δ⁻¹)·(|Im s| + 1). -/
theorem LFunction_linear_growth (hχ1 : χ ≠ 1) {δ : ℝ} (hδ : 0 < δ) {s : ℂ} (hσ : δ ≤ s.re) :
    ‖χ.LFunction s‖ ≤ q * (1 + δ⁻¹) * (|s.im| + 1) := by
  have hσpos : 0 < s.re := lt_of_lt_of_le hδ hσ
  have h := norm_LFunction_le_of_re_pos hχ1 hσpos
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hn : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_pos hσpos] at hn
  have h2 : ‖s‖ / s.re ≤ 1 + δ⁻¹ * |s.im| := by
    calc ‖s‖ / s.re ≤ (s.re + |s.im|) / s.re := by gcongr
      _ = 1 + |s.im| / s.re := by field_simp
      _ ≤ 1 + |s.im| / δ := by gcongr
      _ = 1 + δ⁻¹ * |s.im| := by rw [div_eq_inv_mul]
  have ht : 0 ≤ |s.im| := abs_nonneg _
  have hδ' : 0 ≤ δ⁻¹ := by positivity
  calc ‖χ.LFunction s‖ ≤ q * ‖s‖ / s.re := h
    _ = q * (‖s‖ / s.re) := by ring
    _ ≤ q * (1 + δ⁻¹ * |s.im|) := by gcongr
    _ ≤ q * (1 + δ⁻¹) * (|s.im| + 1) := by nlinarith

/-- **Polynomial (linear) growth to the right of σ = 0.15** (shape parallel to
Zeta23.RvM.zeta_growth_right; the constant depends on q; no condition at s = 1 — L(·,χ) is entire). -/
theorem LFunction_growth_right (hχ1 : χ ≠ 1) :
    ∃ A C : ℝ, 0 < C ∧ ∀ s : ℂ, (0.15 : ℝ) ≤ s.re → ‖χ.LFunction s‖ ≤ C * (|s.im| + 3) ^ A := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  refine ⟨1, q * (1 + (0.15 : ℝ)⁻¹), by positivity, fun s hσ => ?_⟩
  rw [Real.rpow_one]
  have h := LFunction_linear_growth hχ1 (by norm_num : (0 : ℝ) < 0.15) hσ
  have hpos : 0 ≤ (q : ℝ) * (1 + (0.15 : ℝ)⁻¹) := by positivity
  calc ‖χ.LFunction s‖ ≤ q * (1 + (0.15 : ℝ)⁻¹) * (|s.im| + 1) := h
    _ ≤ q * (1 + (0.15 : ℝ)⁻¹) * (|s.im| + 3) := by gcongr; norm_num

/-! ## Re s ≥ 2 -/

/-- On Re s ≥ 2: ‖L(s,χ) − 1‖ ≤ π²/6 − 1 (Dirichlet series, |χ| ≤ 1). -/
theorem norm_LFunction_sub_one_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖χ.LFunction s - 1‖ ≤ Real.pi ^ 2 / 6 - 1 := by
  have hs1 : 1 < s.re := by linarith
  rw [LFunction_eq_LSeries χ hs1]
  set f : ℕ → ℂ := fun n => χ (n : ZMod q) with hf
  have hsum : Summable (LSeries.term f s) := LSeriesSummable_of_one_lt_re χ hs1
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have h01 : ∑ i ∈ Finset.range 2, LSeries.term f s i = 1 := by
    simp [Finset.sum_range_succ, LSeries.term, hf]
  have hL : LSeries f s - 1 = ∑' i, LSeries.term f s (i + 2) := by
    rw [LSeries, ← hsplit, h01]; ring
  rw [hL]
  have hle : ∀ i : ℕ, ‖LSeries.term f s (i + 2)‖ ≤ 1 / ((i : ℝ) + 2) ^ 2 := by
    intro i
    have hpos : 0 < i + 2 := by omega
    rw [LSeries.term_of_ne_zero (by omega : i + 2 ≠ 0), norm_div,
      Complex.norm_natCast_cpow_of_pos hpos]
    have h1 : ‖f (i + 2)‖ ≤ 1 := χ.norm_le_one _
    have hbase : (1 : ℝ) ≤ ((i + 2 : ℕ) : ℝ) := by exact_mod_cast hpos
    have hpow : ((i + 2 : ℕ) : ℝ) ^ (2 : ℝ) ≤ ((i + 2 : ℕ) : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le hbase hs
    rw [Real.rpow_two] at hpow
    have h2pos : (0 : ℝ) < ((i + 2 : ℕ) : ℝ) ^ 2 := by positivity
    have hσpos : (0 : ℝ) < ((i + 2 : ℕ) : ℝ) ^ s.re := by positivity
    calc ‖f (i + 2)‖ / ((i + 2 : ℕ) : ℝ) ^ s.re ≤ 1 / ((i + 2 : ℕ) : ℝ) ^ s.re :=
          div_le_div_of_nonneg_right h1 hσpos.le
      _ ≤ 1 / ((i + 2 : ℕ) : ℝ) ^ 2 := one_div_le_one_div_of_le h2pos hpow
      _ = 1 / ((i : ℝ) + 2) ^ 2 := by push_cast; ring
  have htwo : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
    have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    norm_num [Finset.sum_range_succ] at h
    exact h.congr_fun fun n => by ring
  have hsum' : Summable (fun i => LSeries.term f s (i + 2)) := (summable_nat_add_iff 2).mpr hsum
  calc ‖∑' i, LSeries.term f s (i + 2)‖ ≤ ∑' i, ‖LSeries.term f s (i + 2)‖ :=
        norm_tsum_le_tsum_norm hsum'.norm
    _ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ 2 := hsum'.norm.tsum_le_tsum hle htwo.summable
    _ = Real.pi ^ 2 / 6 - 1 := htwo.tsum_eq

/-- Lower bound at the Jensen disc centre: 1/3 ≤ ‖L(s,χ)‖ for Re s ≥ 2. -/
theorem LFunction_lower_bound_two {s : ℂ} (hs : 2 ≤ s.re) : (1 / 3 : ℝ) ≤ ‖χ.LFunction s‖ := by
  have h := norm_LFunction_sub_one_le (χ := χ) hs
  have h' : ‖(1 : ℂ)‖ - ‖1 - χ.LFunction s‖ ≤ ‖χ.LFunction s‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) (1 - χ.LFunction s)
  rw [norm_sub_rev] at h'
  simp only [norm_one] at h'
  linarith [Zeta23.RvM.one_third_lt_two_sub_pi_sq_div_six]

/-- Upper bound on Re s ≥ 2: ‖L(s,χ)‖ ≤ π²/6. -/
theorem norm_LFunction_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖χ.LFunction s‖ ≤ Real.pi ^ 2 / 6 := by
  have h := norm_LFunction_sub_one_le (χ := χ) hs
  have h' : ‖χ.LFunction s‖ ≤ ‖χ.LFunction s - 1‖ + ‖(1 : ℂ)‖ := by
    simpa using norm_le_norm_sub_add (χ.LFunction s) (1 : ℂ)
  simp only [norm_one] at h'
  linarith

theorem LFunction_ne_zero_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) : χ.LFunction s ≠ 0 := by
  intro h
  have := LFunction_lower_bound_two (χ := χ) hs
  rw [h, norm_zero] at this
  norm_num at this

/-- **q-uniform growth, absolute constants** (for the hybrid range): for every nontrivial χ mod q and
Re s ≥ 0.15, ‖L(s,χ)‖ ≤ 8·q·(|Im s| + 3). -/
theorem LFunction_growth_right_uniform (hχ1 : χ ≠ 1) {s : ℂ} (hσ : (0.15 : ℝ) ≤ s.re) :
    ‖χ.LFunction s‖ ≤ 8 * q * (|s.im| + 3) := by
  have h := LFunction_linear_growth hχ1 (by norm_num : (0 : ℝ) < 0.15) hσ
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have ht : 0 ≤ |s.im| := abs_nonneg _
  have hc : (1 + (0.15 : ℝ)⁻¹) ≤ 8 := by norm_num
  calc ‖χ.LFunction s‖ ≤ q * (1 + (0.15 : ℝ)⁻¹) * (|s.im| + 1) := h
    _ ≤ q * 8 * (|s.im| + 3) := by
        apply mul_le_mul _ (by linarith) (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hc hq.le
    _ = 8 * q * (|s.im| + 3) := by ring

end ThmE
end Zeta23
