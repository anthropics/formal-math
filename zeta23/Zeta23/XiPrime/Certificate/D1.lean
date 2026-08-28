/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Certificate/D1.lean — analytic facts about the diagonal density D₁.

D₁(s) = s − 4s² + Σ_{k≥0} D1coeff k · s^{2k+3}
(Zeta23/XiPrime/Defs.lean §4), D1coeff k = 2·4^{k+1}·k!/(2k+2)!  (= the paper's a_{k+1}, Lemma 7.1).
This file proves:
  * D1coeff_succ      — the ratio  D1coeff (k+1) / D1coeff k = 2(k+1)/((k+2)(2k+3))  (↓ in k, ≤ 1/3);
  * summable_D1coeff_mul_pow — the series converges for every real s (so Defs.D1 is an honest sum);
  * continuous_D1     — D₁ is continuous on ℝ;
  * D1_eq_trunc_add_tail, D1trunc_le_D1 (s ≥ 0), D1_nonneg (s ≥ 0);
  * eps9 := 1024/2990212875 = D1coeff 9 · 231/211 and the CERTIFIED TAIL
      D1 s ≤ D1trunc 9 s + eps9   for s ∈ [0,1]
    (paper Thm 8.2 "Certified constants": ε₉ ≤ 3.43·10⁻⁷; here eps9 < 3.425·10⁻⁷), geometric
    comparison with ratio 20/231 = D1coeff 10 / D1coeff 9.  This is the bound that keeps the Lean
    constant on the CORRECT side: truncating D₁ without the tail would make 1/c smaller and the stated
    proportion larger than the paper proves.
-/
import Zeta23.XiPrime.Defs
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped BigOperators
open Set Filter

noncomputable section

namespace Zeta23
namespace XiPrime

/-! ### the coefficients -/

theorem D1coeff_pos (k : ℕ) : 0 < D1coeff k := by
  unfold D1coeff; positivity

theorem D1coeff_nonneg (k : ℕ) : 0 ≤ D1coeff k := (D1coeff_pos k).le

theorem D1coeff_zero : D1coeff 0 = 4 := by
  norm_num [D1coeff, Nat.factorial]

/-- the ratio recursion: D1coeff (k+1) = D1coeff k · 2(k+1)/((k+2)(2k+3)). -/
theorem D1coeff_succ (k : ℕ) :
    D1coeff (k + 1) = D1coeff k * (2 * (k + 1) / ((k + 2) * (2 * k + 3))) := by
  unfold D1coeff
  have h1 : (Nat.factorial (2 * (k + 1) + 2) : ℝ)
      = (2 * k + 4) * (2 * k + 3) * (Nat.factorial (2 * k + 2) : ℝ) := by
    have : 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 := by ring
    rw [this, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have h2 : (Nat.factorial (k + 1) : ℝ) = (k + 1) * (Nat.factorial k : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [h1, h2]
  have h3 : (Nat.factorial (2 * k + 2) : ℝ) ≠ 0 := by positivity
  have h4 : (Nat.factorial k : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- the ratio is at most 1/3 (its value at k = 0). -/
theorem D1coeff_succ_le_third (k : ℕ) : D1coeff (k + 1) ≤ D1coeff k / 3 := by
  rw [D1coeff_succ]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hpos : (0 : ℝ) < (k + 2) * (2 * k + 3) := by positivity
  have hr : 2 * ((k : ℝ) + 1) / ((k + 2) * (2 * k + 3)) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hpos (by norm_num)]
    nlinarith
  calc D1coeff k * (2 * (k + 1) / ((k + 2) * (2 * k + 3)))
      ≤ D1coeff k * (1 / 3) := mul_le_mul_of_nonneg_left hr (D1coeff_nonneg k)
    _ = D1coeff k / 3 := by ring

/-- for k ≥ 9 the ratio is at most 20/231 (its value at k = 9; the ratio decreases in k). -/
theorem D1coeff_succ_le (k : ℕ) (hk : 9 ≤ k) : D1coeff (k + 1) ≤ D1coeff k * (20 / 231) := by
  rw [D1coeff_succ]
  apply mul_le_mul_of_nonneg_left _ (D1coeff_nonneg k)
  have hk' : (9 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : (0 : ℝ) < (k + 2) * (2 * k + 3) := by positivity
  rw [div_le_div_iff₀ hpos (by norm_num)]
  nlinarith

/-- geometric domination of the tail coefficients. -/
theorem D1coeff_tail_le (j : ℕ) : D1coeff (9 + j) ≤ D1coeff 9 * (20 / 231) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := D1coeff_succ_le (9 + j) (by omega)
    have : 9 + (j + 1) = 9 + j + 1 := by ring
    rw [this]
    calc D1coeff (9 + j + 1) ≤ D1coeff (9 + j) * (20 / 231) := h
      _ ≤ D1coeff 9 * (20 / 231) ^ j * (20 / 231) :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
      _ = D1coeff 9 * (20 / 231) ^ (j + 1) := by ring

theorem D1coeff_nine : D1coeff 9 = 1024 / 3273645375 := by
  norm_num [D1coeff, Nat.factorial]

/-- the factorial comparison D1coeff k ≤ 2·4^{k+1}/(k+1)!  (from k!·(k+2)! ∣ (2k+2)!). -/
theorem D1coeff_le (k : ℕ) : D1coeff k ≤ 2 * 4 ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) := by
  unfold D1coeff
  have hdvd : Nat.factorial k * Nat.factorial (k + 2) ∣ Nat.factorial (2 * k + 2) := by
    have := Nat.factorial_mul_factorial_dvd_factorial_add k (k + 2)
    have e : k + (k + 2) = 2 * k + 2 := by ring
    rwa [e] at this
  have hle : (Nat.factorial k : ℝ) * Nat.factorial (k + 1) ≤ Nat.factorial (2 * k + 2) := by
    have h1 : Nat.factorial k * Nat.factorial (k + 1) ≤ Nat.factorial k * Nat.factorial (k + 2) :=
      Nat.mul_le_mul_left _ (Nat.factorial_le (by omega))
    have h2 : Nat.factorial k * Nat.factorial (k + 2) ≤ Nat.factorial (2 * k + 2) :=
      Nat.le_of_dvd (Nat.factorial_pos _) hdvd
    exact_mod_cast h1.trans h2
  have hA : (0 : ℝ) < Nat.factorial (2 * k + 2) := by positivity
  have hB : (0 : ℝ) < Nat.factorial (k + 1) := by positivity
  rw [div_le_div_iff₀ hA hB]
  have h4 : (0 : ℝ) ≤ 2 * 4 ^ (k + 1) := by positivity
  calc 2 * 4 ^ (k + 1) * (Nat.factorial k : ℝ) * Nat.factorial (k + 1)
      = 2 * 4 ^ (k + 1) * ((Nat.factorial k : ℝ) * Nat.factorial (k + 1)) := by ring
    _ ≤ 2 * 4 ^ (k + 1) * (Nat.factorial (2 * k + 2) : ℝ) := mul_le_mul_of_nonneg_left hle h4

/-! ### summability and continuity of the series -/

/-- the general term of the D₁ series. -/
def D1term (k : ℕ) (s : ℝ) : ℝ := D1coeff k * s ^ (2 * k + 3)

theorem norm_D1term_le (k : ℕ) {s R : ℝ} (h : |s| ≤ R) :
    ‖D1term k s‖ ≤ D1coeff k * R ^ (2 * k + 3) := by
  have hR : 0 ≤ R := (abs_nonneg s).trans h
  rw [Real.norm_eq_abs, D1term, abs_mul, abs_of_pos (D1coeff_pos k), abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg s) h _) (D1coeff_nonneg k)

/-- the majorant Σ_k D1coeff k · R^{2k+3} converges (comparison with 2R·Σ (4R²)^{k+1}/(k+1)!). -/
theorem summable_D1coeff_mul_pow (R : ℝ) : Summable (fun k => D1coeff k * R ^ (2 * k + 3)) := by
  have hexp : Summable (fun n : ℕ => (4 * R ^ 2) ^ n / (Nat.factorial n : ℝ)) :=
    Real.summable_pow_div_factorial (4 * R ^ 2)
  have hexp1 : Summable (fun k : ℕ => (4 * R ^ 2) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) :=
    (summable_nat_add_iff 1).mpr hexp
  have hg : Summable (fun k : ℕ => 2 * |R| * ((4 * R ^ 2) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ))) :=
    hexp1.mul_left _
  refine Summable.of_norm_bounded hg fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (D1coeff_pos k), abs_pow]
  have hpow : |R| ^ (2 * k + 3) = |R| * (R ^ 2) ^ (k + 1) := by
    rw [← sq_abs R, ← pow_mul]
    ring
  rw [hpow]
  have hfac : (0 : ℝ) < Nat.factorial (k + 1) := by positivity
  calc D1coeff k * (|R| * (R ^ 2) ^ (k + 1))
      ≤ (2 * 4 ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) * (|R| * (R ^ 2) ^ (k + 1)) :=
        mul_le_mul_of_nonneg_right (D1coeff_le k) (by positivity)
    _ = 2 * |R| * ((4 * R ^ 2) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) := by
        rw [mul_pow]; field_simp

theorem summable_D1term (s : ℝ) : Summable (fun k => D1term k s) :=
  summable_D1coeff_mul_pow s

theorem D1_eq_tsum_D1term (s : ℝ) : D1 s = s - 4 * s ^ 2 + ∑' k, D1term k s := rfl

/-- D₁ is continuous on every [−R, R], hence on ℝ. -/
theorem continuousOn_D1_Icc (R : ℝ) : ContinuousOn D1 (Icc (-R) R) := by
  have htail : ContinuousOn (fun s => ∑' k, D1term k s) (Icc (-R) R) := by
    refine continuousOn_tsum (u := fun k => D1coeff k * |R| ^ (2 * k + 3)) ?_
      (summable_D1coeff_mul_pow |R|) ?_
    · intro k
      exact (continuous_const.mul (continuous_pow _)).continuousOn
    · intro k s hs
      exact norm_D1term_le k (abs_le_abs hs.2 (by linarith [hs.1]))
  have hpoly : ContinuousOn (fun s : ℝ => s - 4 * s ^ 2) (Icc (-R) R) := by fun_prop
  exact (hpoly.add htail).congr fun s _ => rfl

theorem continuous_D1 : Continuous D1 := by
  rw [continuous_iff_continuousAt]
  intro s
  have h := continuousOn_D1_Icc (|s| + 1)
  apply h.continuousAt
  apply Icc_mem_nhds
  · linarith [neg_abs_le s]
  · linarith [le_abs_self s]

theorem continuousOn_D1 (S : Set ℝ) : ContinuousOn D1 S := continuous_D1.continuousOn

/-! ### truncation and tail -/

theorem D1trunc_eq (K : ℕ) (s : ℝ) :
    D1trunc K s = s - 4 * s ^ 2 + ∑ k ∈ Finset.range K, D1term k s := rfl

/-- D₁ = (its K-truncation) + (the tail from K on). -/
theorem D1_eq_trunc_add_tail (K : ℕ) (s : ℝ) :
    D1 s = D1trunc K s + ∑' k, D1term (k + K) s := by
  rw [D1_eq_tsum_D1term, D1trunc_eq, ← (summable_D1term s).sum_add_tsum_nat_add K]
  ring

theorem D1term_nonneg (k : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ D1term k s :=
  mul_nonneg (D1coeff_nonneg k) (pow_nonneg hs _)

theorem D1tail_nonneg (K : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ ∑' k, D1term (k + K) s :=
  tsum_nonneg fun _ => D1term_nonneg _ hs

/-- truncations UNDER-estimate D₁ on [0, ∞). -/
theorem D1trunc_le_D1 (K : ℕ) {s : ℝ} (hs : 0 ≤ s) : D1trunc K s ≤ D1 s := by
  rw [D1_eq_trunc_add_tail K]
  linarith [D1tail_nonneg K hs]

/-- D1trunc 1 s = s(1 − 2s)². -/
theorem D1trunc_one (s : ℝ) : D1trunc 1 s = s * (1 - 2 * s) ^ 2 := by
  simp [D1trunc_eq, D1term, D1coeff_zero]
  ring

/-- D₁ ≥ 0 on [0, ∞)  (D₁ = s(1−2s)² + a series of nonnegative terms). -/
theorem D1_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ D1 s := by
  have h := D1trunc_le_D1 1 hs
  rw [D1trunc_one] at h
  exact le_trans (by positivity) h

theorem D1_zero : D1 0 = 0 := by
  rw [D1_eq_trunc_add_tail 0]
  simp [D1trunc_eq, D1term]

/-- the certified tail constant ε₉ := D1coeff 9 · Σ_j (20/231)^j = (1024/3273645375)·(231/211). -/
def eps9 : ℝ := 1024 / 2990212875

theorem eps9_eq : eps9 = D1coeff 9 * (1 - 20 / 231)⁻¹ := by
  rw [D1coeff_nine, eps9]; norm_num

theorem eps9_pos : 0 < eps9 := by unfold eps9; norm_num

/-- ε₉ < 3.425·10⁻⁷ (the paper quotes ε₉ ≤ 3.43·10⁻⁷). -/
theorem eps9_lt : eps9 < 3425 / 10 ^ 10 := by unfold eps9; norm_num

/-- on [0,1] the tail from k = 9 on is at most ε₉. -/
theorem D1tail9_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : ∑' k, D1term (k + 9) s ≤ eps9 := by
  have hgeo : Summable (fun j : ℕ => D1coeff 9 * (20 / 231 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hle : ∀ j, D1term (j + 9) s ≤ D1coeff 9 * (20 / 231 : ℝ) ^ j := by
    intro j
    unfold D1term
    have hp : s ^ (2 * (j + 9) + 3) ≤ 1 := pow_le_one₀ hs0 hs1
    calc D1coeff (j + 9) * s ^ (2 * (j + 9) + 3)
        ≤ D1coeff (j + 9) * 1 := mul_le_mul_of_nonneg_left hp (D1coeff_nonneg _)
      _ = D1coeff (9 + j) := by rw [mul_one, add_comm]
      _ ≤ D1coeff 9 * (20 / 231) ^ j := D1coeff_tail_le j
  have hsum : Summable (fun j => D1term (j + 9) s) := (summable_nat_add_iff 9).mpr (summable_D1term s)
  calc ∑' j, D1term (j + 9) s ≤ ∑' j, D1coeff 9 * (20 / 231 : ℝ) ^ j := hsum.tsum_le_tsum hle hgeo
    _ = D1coeff 9 * ∑' j, (20 / 231 : ℝ) ^ j := tsum_mul_left
    _ = D1coeff 9 * (1 - 20 / 231)⁻¹ := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ = eps9 := eps9_eq.symm

/-- **the certified two-sided control of D₁ on [0,1]:**  D1trunc 9 ≤ D₁ ≤ D1trunc 9 + ε₉. -/
theorem D1_le_D1trunc9_add {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : D1 s ≤ D1trunc 9 s + eps9 := by
  rw [D1_eq_trunc_add_tail 9]
  linarith [D1tail9_le hs0 hs1]

theorem D1_mem_Icc {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    D1 s ∈ Icc (D1trunc 9 s) (D1trunc 9 s + eps9) :=
  ⟨D1trunc_le_D1 9 hs0, D1_le_D1trunc9_add hs0 hs1⟩

/-- D1trunc K is a polynomial, hence continuous. -/
theorem continuous_D1trunc (K : ℕ) : Continuous (D1trunc K) := by
  unfold D1trunc; fun_prop

/-! ### exports for the diagonal law (Coeff.lean H3) -/

theorem summable_D1coeff : Summable D1coeff := by
  have h := summable_D1coeff_mul_pow 1
  simpa using h

/-- the coefficient tail Σ_{k ≥ K} D1coeff k → 0. -/
theorem tendsto_D1coeff_tail : Tendsto (fun K => ∑' k, D1coeff (k + K)) atTop (nhds 0) :=
  tendsto_sum_nat_add D1coeff

/-- on [0,1] the function tail is dominated by the coefficient tail, uniformly in s. -/
theorem D1tail_le_coeff_tail (K : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∑' k, D1term (k + K) s ≤ ∑' k, D1coeff (k + K) := by
  have h1 : Summable (fun k => D1term (k + K) s) := (summable_nat_add_iff K).mpr (summable_D1term s)
  have h2 : Summable (fun k => D1coeff (k + K)) := (summable_nat_add_iff K).mpr summable_D1coeff
  refine h1.tsum_le_tsum (fun k => ?_) h2
  unfold D1term
  calc D1coeff (k + K) * s ^ (2 * (k + K) + 3) ≤ D1coeff (k + K) * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hs0 hs1) (D1coeff_nonneg _)
    _ = D1coeff (k + K) := mul_one _

/-- |D₁ − D1trunc K| ≤ Σ_{k≥K} D1coeff k on [0,1] (uniform truncation error, → 0 as K → ∞). -/
theorem abs_D1_sub_D1trunc_le (K : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |D1 s - D1trunc K s| ≤ ∑' k, D1coeff (k + K) := by
  rw [D1_eq_trunc_add_tail K, add_sub_cancel_left, abs_of_nonneg (D1tail_nonneg K hs0)]
  exact D1tail_le_coeff_tail K hs0 hs1

/-- ∫₀ˢ D1term k = D1coeff k · s^{2k+4}/(2k+4). -/
theorem integral_D1term (k : ℕ) (s : ℝ) :
    ∫ u in (0:ℝ)..s, D1term k u = D1coeff k * s ^ (2 * k + 4) / (2 * k + 4) := by
  unfold D1term
  rw [intervalIntegral.integral_const_mul, integral_pow]
  have : ((2 * k + 3 : ℕ) : ℝ) + 1 = 2 * k + 4 := by push_cast; ring
  rw [this]
  simp only [zero_pow (by omega : 2 * k + 3 + 1 ≠ 0), sub_zero]
  have e : 2 * k + 3 + 1 = 2 * k + 4 := by omega
  rw [e]
  ring

/-- termwise integration of the truncation (finite sum; no convergence issues). -/
theorem integral_D1trunc (K : ℕ) (s : ℝ) :
    ∫ u in (0:ℝ)..s, D1trunc K u
      = s ^ 2 / 2 - 4 * s ^ 3 / 3 + ∑ k ∈ Finset.range K, D1coeff k * s ^ (2 * k + 4) / (2 * k + 4) := by
  have hint : ∀ k, IntervalIntegrable (fun u => D1term k u) MeasureTheory.volume 0 s := fun k => by
    unfold D1term; exact (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _
  simp only [D1trunc_eq]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_finset_sum]
  · simp only [integral_D1term, integral_id, intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  · intro k _; exact hint k
  · exact continuous_id.intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
  · exact (continuous_id.intervalIntegrable _ _).sub
      ((continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _)
  · exact (continuous_finset_sum _ fun k _ =>
      (continuous_const.mul (continuous_pow _))).intervalIntegrable _ _

/-- **uniform diagonal-law main term:** for s ∈ [0,1],
|∫₀ˢ D₁ − ∫₀ˢ D1trunc K| ≤ Σ_{k≥K} D1coeff k  (→ 0), with ∫₀ˢ D1trunc K explicit above. -/
theorem abs_integral_D1_sub_le (K : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |(∫ u in (0:ℝ)..s, D1 u) - ∫ u in (0:ℝ)..s, D1trunc K u| ≤ ∑' k, D1coeff (k + K) := by
  rw [← intervalIntegral.integral_sub (continuous_D1.intervalIntegrable _ _)
    ((continuous_D1trunc K).intervalIntegrable _ _)]
  have hb : ∀ u ∈ Set.Ioc 0 s, ‖D1 u - D1trunc K u‖ ≤ ∑' k, D1coeff (k + K) := by
    intro u hu
    rw [Real.norm_eq_abs]
    exact abs_D1_sub_D1trunc_le K hu.1.le (hu.2.trans hs1)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := s)
    (f := fun u => D1 u - D1trunc K u) (C := ∑' k, D1coeff (k + K)) ?_
  · rw [sub_zero, abs_of_nonneg hs0] at h
    calc |∫ u in (0:ℝ)..s, D1 u - D1trunc K u| ≤ (∑' k, D1coeff (k + K)) * s := h
      _ ≤ (∑' k, D1coeff (k + K)) * 1 :=
          mul_le_mul_of_nonneg_left hs1 (tsum_nonneg fun _ => D1coeff_nonneg _)
      _ = _ := mul_one _
  · intro u hu
    rw [Set.uIoc_of_le hs0] at hu
    exact hb u hu

end XiPrime
end Zeta23
