/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Asymptotics.PowPolylog
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic

/-!
# Proof of Theorem 35: the arithmetic

Theorem 35 gives Las Vegas algorithms for 3SUM on `n` real numbers in `O(n^{1.998})` expected time,
and for the (min,+)-product, APSP and Exact Triangle with real inputs in `O(n^{2.998})` expected
time.  The proof takes `d := ⌊n^{1/40}⌋` (`listLen`), applies Lemma 36 with this `d`, and answers
every comparison count by Corollary 38.  The reductions behind Lemma 36 are cited and running times
are not defined here; this file checks the sums of the proof, in its order.  All that the sums use
about `d` is `1 ≤ d ≤ n^{1/40}` (`one_le_listLen`, `listLen_le_rpow`) and `1/d = O(n^{-1/40})`
(`isBigOPow_inv_listLen`).
* `d` meets the hypotheses of Lemma 36 and of Corollary 38 (`theorem_35_d`);
* a counting call costs `O(n^{2.0229} log n)` (`theorem_35_counting_call`, from
  `listLen_mul_sq_div_le` and `listLen_mul_rpow_le`), and forming its lists `O(n^{1.05})`
  (`theorem_35_forming_lists`);
* the `Õ(n/d)` counting calls cost `O(n^{2.998})` (`theorem_35_min_plus_total`), and so does the
  further time `Õ(n³/d)` (`theorem_35_further_time`);
* for 3SUM a comparison count costs `O(n^{1.9979} log n)` (`theorem_35_three_sum_count`), which
  gives `O(n^{1.998})` in all (`theorem_35_three_sum_total`);
* "with probability 1 - n^{-c}": Markov's inequality for one run (`theorem_35_one_run`) and
  independent restarts (`theorem_35_restarts`).
-/

public section

namespace ThreeSumApsp

open Finset Asymptotics Filter
open ComparisonCounts

/-! ### The parameter d := ⌊n^{1/40}⌋ -/

namespace Theorem35

/-- d ≥ 1. -/
theorem one_le_listLen {n : ℕ} (hn : 1 ≤ n) : (1 : ℝ) ≤ listLen n :=
  Nat.one_le_cast.2 (Nat.le_floor (by
    exact_mod_cast Real.one_le_rpow (Nat.one_le_cast.2 hn) (by norm_num : (0 : ℝ) ≤ 1 / 40)))

/-- d ≤ n^{1/40}. -/
theorem listLen_le_rpow (n : ℕ) : (listLen n : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ) :=
  Nat.floor_le (by positivity)

/-- `d = O(n^{1/40})`. -/
theorem isBigOPow_listLen : IsBigOPow (fun n => (listLen n : ℝ)) (1 / 40) :=
  isBigOPow_floor_rpow _

/-- `1/d = O(n^{-1/40})`. -/
theorem isBigOPow_inv_listLen : IsBigOPow (fun n => (listLen n : ℝ)⁻¹) (-(1 / 40)) :=
  isBigOPow_inv_floor_rpow (by norm_num)

/-- If `f(n) = O(n^a)`, then `f(n)/d = O(n^{a-1/40})`. -/
theorem isBigOPow_div_listLen {f : ℕ → ℝ} {a : ℝ} (hf : IsBigOPow f a) :
    IsBigOPow (fun n => f n / listLen n) (a - 1 / 40) := by
  simpa only [div_eq_mul_inv, sub_eq_add_neg] using hf.mul isBigOPow_inv_listLen

/-- `n²/d^{0.126} = O(n^{2-0.126/40})`. -/
theorem isBigOPow_sq_div_listLen_rpow :
    IsBigOPow (fun n : ℕ => (n : ℝ) ^ 2 / (listLen n : ℝ) ^ (0.126 : ℝ)) (2 - 0.126 / 40) := by
  refine IsBigOPow.mono ?_ (le_of_eq (by norm_num : ((2 : ℕ) : ℝ) + -(1 / 40) * 0.126 = _))
  simpa only [div_eq_mul_inv, Real.inv_rpow (Nat.cast_nonneg _)] using
    (isBigOPow_natCast_pow 2).mul (isBigOPow_inv_listLen.rpow (r := 0.126) (by norm_num))

/-- Proof of Theorem 35: "d · n²/d^{0.126} ≤ n^{2+0.874/40} ≤ n^{2.0219}". -/
theorem listLen_mul_sq_div_le {n : ℕ} (hn : 1 ≤ n) :
    (listLen n : ℝ) * ((n : ℝ) ^ 2 / (listLen n : ℝ) ^ (0.126 : ℝ)) ≤ (n : ℝ) ^ (2.0219 : ℝ) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hd0 : (0 : ℝ) < listLen n := one_pos.trans_le (one_le_listLen hn)
  calc (listLen n : ℝ) * ((n : ℝ) ^ 2 / (listLen n : ℝ) ^ (0.126 : ℝ))
      = (n : ℝ) ^ 2 * (listLen n : ℝ) ^ (1 - 0.126 : ℝ) := by
        rw [Real.rpow_sub hd0, Real.rpow_one]
        ring
    _ ≤ (n : ℝ) ^ 2 * ((n : ℝ) ^ (1 / 40 : ℝ)) ^ (1 - 0.126 : ℝ) := by
        gcongr
        exact listLen_le_rpow n
    _ = (n : ℝ) ^ (2 + 0.874 / 40 : ℝ) := by
        rw [← Real.rpow_mul hn0.le, ← Real.rpow_natCast, ← Real.rpow_add hn0]
        norm_num
    _ ≤ (n : ℝ) ^ (2.0219 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hn) (by norm_num)

/-- Proof of Theorem 35: "d · n^{2-1/440} ≤ n^{2+1/40-1/440} ≤ n^{2.0228}". -/
theorem listLen_mul_rpow_le {n : ℕ} (hn : 1 ≤ n) :
    (listLen n : ℝ) * (n : ℝ) ^ (2 - 1 / 440 : ℝ) ≤ (n : ℝ) ^ (2.0228 : ℝ) :=
  calc (listLen n : ℝ) * (n : ℝ) ^ (2 - 1 / 440 : ℝ)
      ≤ (n : ℝ) ^ (1 / 40 : ℝ) * (n : ℝ) ^ (2 - 1 / 440 : ℝ) := by
        gcongr
        exact listLen_le_rpow n
    _ = (n : ℝ) ^ (2 + 1 / 40 - 1 / 440 : ℝ) := by
        rw [← Real.rpow_add (Nat.cast_pos.2 hn)]
        norm_num
    _ ≤ (n : ℝ) ^ (2.0228 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hn) (by norm_num)

end Theorem35

/-- Proof of Theorem 35: "Let d := ⌊n^{1/40}⌋, apply Lemma 36 with this d, and answer every
comparison count by Corollary 38." This d satisfies the hypotheses 1 ≤ d ≤ n of Lemma 36 and d ≤
n^{1/40} of Corollary 38. -/
theorem theorem_35_d (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ listLen n ∧ listLen n ≤ n ∧ (listLen n : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ) := by
  have hone := Theorem35.one_le_listLen hn
  have hle := Theorem35.listLen_le_rpow n
  refine ⟨Nat.one_le_cast.1 hone, Nat.cast_le (α := ℝ).1 (hle.trans ?_), hle⟩
  exact Real.rpow_le_self_of_one_le (Nat.one_le_cast.2 hn) (by norm_num)

/-- Proof of Theorem 35: "the d comparison counts of a counting call cost ∑_{k ∈ [d]} O(|P_k|
n^{0.0229} + n²/d^{0.126} + n^{2-1/440} log n) = O(n^{2.0229} log n), since ∑_k |P_k| = n²". `p k`
is |P_k|. -/
theorem theorem_35_counting_call :
    ∃ (K : ℝ) (n₀ : ℕ), ∀ n : ℕ, n₀ ≤ n → ∀ p : Fin (listLen n) → ℕ, ∑ k, p k = n ^ 2 →
      ∑ k, ((p k : ℝ) * (n : ℝ) ^ (0.0229 : ℝ) + (n : ℝ) ^ 2 / (listLen n : ℝ) ^ (0.126 : ℝ)
          + (n : ℝ) ^ (2 - 1 / 440 : ℝ) * Real.log n)
        ≤ K * ((n : ℝ) ^ (2.0229 : ℝ) * Real.log n) := by
  refine ⟨3, 3, fun n hn p hp => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hcast : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn1
  have hlog := Real.one_le_log_natCast_of_three_le hn
  -- the three sums, without the logarithm, are at most `n^{2.0229}`
  have hfirst : (∑ k, (p k : ℝ)) * (n : ℝ) ^ (0.0229 : ℝ) = (n : ℝ) ^ (2.0229 : ℝ) := by
    rw [show ∑ k, (p k : ℝ) = (n : ℝ) ^ 2 by exact_mod_cast hp, ← Real.rpow_natCast,
      ← Real.rpow_add (by linarith)]
    norm_num
  have hsecond : (listLen n : ℝ) * ((n : ℝ) ^ 2 / (listLen n : ℝ) ^ (0.126 : ℝ))
      ≤ (n : ℝ) ^ (2.0229 : ℝ) :=
    (Theorem35.listLen_mul_sq_div_le hn1).trans
      (Real.rpow_le_rpow_of_exponent_le hcast (by norm_num))
  have hthird : (listLen n : ℝ) * (n : ℝ) ^ (2 - 1 / 440 : ℝ) ≤ (n : ℝ) ^ (2.0229 : ℝ) :=
    (Theorem35.listLen_mul_rpow_le hn1).trans (Real.rpow_le_rpow_of_exponent_le hcast (by norm_num))
  have habsorb : (n : ℝ) ^ (2.0229 : ℝ) ≤ (n : ℝ) ^ (2.0229 : ℝ) * Real.log n :=
    le_mul_of_one_le_right (by positivity) hlog
  calc ∑ k, ((p k : ℝ) * (n : ℝ) ^ (0.0229 : ℝ) + (n : ℝ) ^ 2 / (listLen n : ℝ) ^ (0.126 : ℝ)
          + (n : ℝ) ^ (2 - 1 / 440 : ℝ) * Real.log n)
      = (∑ k, (p k : ℝ)) * (n : ℝ) ^ (0.0229 : ℝ)
        + (listLen n : ℝ) * ((n : ℝ) ^ 2 / (listLen n : ℝ) ^ (0.126 : ℝ))
        + (listLen n : ℝ) * (n : ℝ) ^ (2 - 1 / 440 : ℝ) * Real.log n := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_assoc]
    _ ≤ (n : ℝ) ^ (2.0229 : ℝ) + (n : ℝ) ^ (2.0229 : ℝ)
        + (n : ℝ) ^ (2.0229 : ℝ) * Real.log n := by
        rw [hfirst]
        gcongr
    _ ≤ 3 * ((n : ℝ) ^ (2.0229 : ℝ) * Real.log n) := by linarith

/-- Proof of Theorem 35: "forming the lists costs O(nd²) = O(n^{1.05})". -/
theorem theorem_35_forming_lists (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * (listLen n : ℝ) ^ 2 ≤ (n : ℝ) ^ (1.05 : ℝ) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
  calc (n : ℝ) * (listLen n : ℝ) ^ 2 ≤ n * ((n : ℝ) ^ (1 / 40 : ℝ)) ^ 2 := by
        gcongr
        exact Theorem35.listLen_le_rpow n
    _ = (n : ℝ) ^ (1.05 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le, mul_comm, ← Real.rpow_add_one hn0.ne']
        norm_num

/-- Proof of Theorem 35: "So the Õ(n/d) counting calls of Lemma 36(a) cost Õ((n/d) n^{2.0229}) =
Õ(n^{3-1/40+0.0229}) ≤ O(n^{2.998})". -/
theorem theorem_35_min_plus_total (c : ℕ) :
    ((fun n : ℕ => (n : ℝ) / listLen n * (n : ℝ) ^ (2.0229 : ℝ) * Real.log n ^ c) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ (3 - 1 / 40 + 0.0229 : ℝ) * Real.log n ^ c)) ∧
      ((fun n : ℕ => (n : ℝ) ^ (3 - 1 / 40 + 0.0229 : ℝ) * Real.log n ^ c) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ (2.998 : ℝ))) := by
  refine ⟨.mul ?_ (isBigO_refl _ _), isBigO_rpow_mul_log_pow_rpow (by norm_num) c⟩
  -- `n/d = O(n^{1-1/40})`, and `1 - 1/40 + 2.0229 = 3 - 1/40 + 0.0229`
  exact ((Theorem35.isBigOPow_div_listLen isBigOPow_natCast).mul (isBigOPow_rpow 2.0229)).mono
    (by norm_num)

/-- Proof of Theorem 35: "and its additional time is Õ(n³/d) = Õ(n^{2.975})" (which is
O(n^{2.998})). -/
theorem theorem_35_further_time (c : ℕ) :
    ((fun n : ℕ => (n : ℝ) ^ 3 / listLen n * Real.log n ^ c) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ (2.975 : ℝ) * Real.log n ^ c)) ∧
      ((fun n : ℕ => (n : ℝ) ^ (2.975 : ℝ) * Real.log n ^ c) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ (2.998 : ℝ))) := by
  refine ⟨.mul ?_ (isBigO_refl _ _), isBigO_rpow_mul_log_pow_rpow (by norm_num) c⟩
  exact (Theorem35.isBigOPow_div_listLen (isBigOPow_natCast_pow 3)).mono (by norm_num)

/-- Proof of Theorem 35, 3SUM: "a comparison count of Lemma 36(b) costs O((n²/d) n^{0.0229} +
n²/d^{0.126} + n^{2-1/440} log n) = O(n^{2-1/40+0.0229} log n) = O(n^{1.9979} log n)". -/
theorem theorem_35_three_sum_count :
    ((fun n : ℕ => (n : ℝ) ^ 2 / listLen n * (n : ℝ) ^ (0.0229 : ℝ) +
          (n : ℝ) ^ 2 / (listLen n : ℝ) ^ (0.126 : ℝ) + (n : ℝ) ^ (2 - 1 / 440 : ℝ) * Real.log n)
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (2 - 1 / 40 + 0.0229 : ℝ) * Real.log n)) ∧
      (2 - 1 / 40 + 0.0229 : ℝ) = 1.9979 := by
  -- the exponents: `2 - 0.126/40 ≤ 2 - 1/40 + 0.0229` and `2 - 1/440 ≤ 2 - 1/40 + 0.0229`
  have hfirst : IsBigOPow (fun n : ℕ => (n : ℝ) ^ 2 / listLen n * (n : ℝ) ^ (0.0229 : ℝ))
      (2 - 1 / 40 + 0.0229) :=
    ((Theorem35.isBigOPow_div_listLen (isBigOPow_natCast_pow 2)).mul (isBigOPow_rpow 0.0229)).mono
      (by norm_num)
  have hsecond := Theorem35.isBigOPow_sq_div_listLen_rpow.mono (b := 2 - 1 / 40 + 0.0229)
    (by norm_num)
  have hthird := isBigO_rpow_mul_log_pow_of_le (a := 2 - 1 / 440) (b := 2 - 1 / 40 + 0.0229)
    (by norm_num) (le_refl 1)
  have habsorb := isBigO_rpow_mul_log_pow_of_le (le_refl (2 - 1 / 40 + 0.0229 : ℝ)) zero_le_one
  simp only [pow_zero, mul_one, pow_one] at hthird habsorb
  exact ⟨((hfirst.add hsecond).trans habsorb).add hthird, by norm_num⟩

/-- Proof of Theorem 35, 3SUM: "so 3SUM can also be solved in Õ(n^{1.9979}) ≤ O(n^{1.998}) expected
time"; the further time Õ(n²/d) of Lemma 36(b) is within the same bound. -/
theorem theorem_35_three_sum_total (c : ℕ) :
    ((fun n : ℕ => (n : ℝ) ^ (1.9979 : ℝ) * Real.log n ^ c) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ (1.998 : ℝ))) ∧
      ((fun n : ℕ => (n : ℝ) ^ 2 / listLen n * Real.log n ^ c) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ (1.998 : ℝ))) := by
  refine ⟨isBigO_rpow_mul_log_pow_rpow (by norm_num) c, ?_⟩
  refine .trans (.mul ?_ (isBigO_refl _ _))
    (isBigO_rpow_mul_log_pow_rpow (a := 2 - 1 / 40) (b := 1.998) (by norm_num) c)
  exact (Theorem35.isBigOPow_div_listLen (isBigOPow_natCast_pow 2)).mono (by norm_num)

/-- Proof of Theorem 35, "Las Vegas, and high probability": "we stop a run that exceeds twice the
bound on its expected time".  By Markov's inequality such a run is stopped with probability at most
1/2.  `T` is the running time of a run and `B` the bound on its expectation. -/
theorem theorem_35_one_run {Ω : Type} [MeasurableSpace Ω] (Pr : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure Pr] (T : Ω → ℝ) (hT : MeasureTheory.Integrable T Pr)
    (hT0 : ∀ ω, 0 ≤ T ω) (B : ℝ) (hB : 0 < B) (hTB : ∫ ω, T ω ∂Pr ≤ B) :
    Pr {ω | 2 * B < T ω} ≤ 1 / 2 := by
  have hmarkov : 2 * B * Pr.real {ω | 2 * B ≤ T ω} ≤ ∫ ω, T ω ∂Pr :=
    MeasureTheory.mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hT0) hT (2 * B)
  have hhalf : Pr.real {ω | 2 * B ≤ T ω} ≤ 1 / 2 := by
    rw [← mul_le_mul_iff_right₀ (show 0 < 2 * B by positivity)]
    linarith
  calc Pr {ω | 2 * B < T ω} ≤ Pr {ω | 2 * B ≤ T ω} :=
        MeasureTheory.measure_mono (Set.ofPred_subset_ofPred.2 fun _ => le_of_lt)
    _ = ENNReal.ofReal (Pr.real {ω | 2 * B ≤ T ω}) := (MeasureTheory.ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hhalf
    _ = 1 / 2 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        simp

/-- Proof of Theorem 35: "and start again, and c log₂ n runs all fail with probability at most
n^{-c}".  `T i` is the running time of the i-th run; the runs are independent, and there are m ≥ c
log₂ n of them. (The m runs take 2Bm time in all, a factor O(log n) more than B; the bounds of
Theorem 35 still hold because `theorem_35_min_plus_total` and `theorem_35_three_sum_total` hold for
every power of the logarithm.) -/
theorem theorem_35_restarts {Ω : Type} [MeasurableSpace Ω] (Pr : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure Pr] (m : ℕ) (T : Fin m → Ω → ℝ)
    (hind : ProbabilityTheory.iIndepFun T Pr) (B : ℝ) (hfail : ∀ i, Pr {ω | 2 * B < T i ω} ≤ 1 / 2)
    (n : ℕ) (hn : 2 ≤ n) (c : ℝ) (hm : c * Real.logb 2 n ≤ m) :
    Pr {ω | ∀ i, 2 * B < T i ω} ≤ ENNReal.ofReal ((n : ℝ) ^ (-c)) := by
  have hn0 : (0 : ℝ) < n := by positivity
  -- `2^{-m} ≤ 2^{-c log₂ n} = n^{-c}`
  have hpow : (2 : ℝ) ^ (-(m : ℝ)) ≤ (n : ℝ) ^ (-c) :=
    calc (2 : ℝ) ^ (-(m : ℝ)) ≤ (2 : ℝ) ^ (Real.logb 2 n * -c) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = (n : ℝ) ^ (-c) := by
          rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hn0]
  calc Pr {ω | ∀ i, 2 * B < T i ω}
      = Pr (⋂ i ∈ (Finset.univ : Finset (Fin m)), T i ⁻¹' Set.Ioi (2 * B)) := by
        congr 1
        ext ω
        simp
    _ = ∏ i, Pr (T i ⁻¹' Set.Ioi (2 * B)) :=
        hind.measure_inter_preimage_eq_mul Finset.univ fun i _ => measurableSet_Ioi
    _ ≤ ∏ _i : Fin m, (1 / 2 : ENNReal) := Finset.prod_le_prod' fun i _ => hfail i
    _ = ENNReal.ofReal ((2 : ℝ) ^ (-(m : ℝ))) := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, ← inv_pow,
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
        simp
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ (-c)) := ENNReal.ofReal_le_ofReal hpow

end ThreeSumApsp
