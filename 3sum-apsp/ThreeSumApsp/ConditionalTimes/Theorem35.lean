/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.ConditionalTimes.SmallFacts
public import ThreeSumApsp.Sec5.Theorem35

/-!
# Theorem 35 from Corollary 38, Lemma 36 and the restart argument

The proof takes `d = ⌊n^{1/40}⌋` in Lemma 36 and answers every comparison count by Corollary 38.

1. (min,+)-product, APSP and Exact Triangle: a counting call costs `O(n^{2.0229} log n)`
   (`exists_counting_call_le`, from `theorem_35_counting_call`), so the `Õ(n/d)` calls of
   Lemma 36(a) and the `Õ(n³/d)` further time give `Õ(n^{3-1/40+0.0229})`
   (`lasVegasInPolylog_of_corollary_38_lemma_36a`).
2. 3SUM: a comparison count of Lemma 36(b), with `O(n²/d)` pairs, costs `Õ(n^{1.9979})`
   (`isPowPolylog_countBound_listLen`, `lasVegasInPolylog_threeSum_of_corollary_38_lemma_36b`).
3. The logarithms are absorbed, and restarting gives the bounds with high probability
   (`lasVegasIn_and_whpIn_of_polylog`).

Sums and products of running times are handled by the closure properties of the classes `O(n^a)`
and `Õ(n^a)`. About `d` they need `d = O(n^{1/40})` and `1/d = O(n^{-1/40})` (`isBigOPow_listLen`,
`isBigOPow_inv_listLen`); the hypotheses of Lemma 36 and Corollary 38 need `1 ≤ d ≤ n` and
`d ≤ n^{1/40}` (`theorem_35_d`). The statements `theorem_35_min_plus_total`,
`theorem_35_further_time`, `theorem_35_three_sum_count` and `theorem_35_three_sum_total` check the
same sums with the paper's powers of the logarithm; they are not used here, where only the classes
matter.
-/

@[expose] public section

open ThreeSumApsp.ConditionalTimes

namespace ThreeSumApsp

namespace ConditionalTimes

open Filter ComparisonCounts Theorem35

/-- A Las Vegas algorithm solves the problem in `Õ(n^a)` expected time. -/
def LasVegasInPolylog (M : TimeModel) (prob : RealProblem) (a : ℝ) : Prop :=
  ∃ T : ℕ → ℝ, M.lasVegas prob T ∧ UpperPowPolylog T a

/-! ### The length `d = ⌊n^{1/40}⌋` of the lists -/

/-- `1 ≤ d ≤ n`, the hypothesis of Lemma 36. -/
private theorem one_le_listLen_and_listLen_le (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ listLen n ∧ listLen n ≤ n := by
  obtain ⟨hone, hle, -⟩ := theorem_35_d n hn
  exact ⟨hone, hle⟩

/-- If `f(n) d = Õ(n^a)`, then `f(n) = Õ(n^{a-1/40})`. -/
private theorem isPowPolylog_of_mul_listLen {f : ℕ → ℝ} {a : ℝ}
    (h : IsPowPolylog (fun n => f n * (listLen n : ℝ)) a) : IsPowPolylog f (a - 1 / 40) := by
  rw [sub_eq_add_neg]
  refine (h.mul isBigOPow_inv_listLen.isPowPolylog).congr ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hpos : (0 : ℝ) < listLen n := Nat.cast_pos.2 (one_le_listLen_and_listLen_le n hn).1
  rw [mul_assoc, mul_inv_cancel₀ hpos.ne', mul_one]

/-! ### (min,+)-product, APSP and Exact Triangle -/

/-- "answer every comparison count by Corollary 38": the `d` comparison counts of a counting call,
with `n²` pairs in all, cost `O(n^{2.0229} log n)`. The hypothesis is the bound of Corollary 38. -/
private theorem exists_counting_call_le {T : ℕ → ℕ → ℕ → ℝ} {C : ℝ} {n₀ : ℕ}
    (hcount : ∀ n d p : ℕ, n₀ ≤ n → 1 ≤ d → (d : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ) →
      T n d p ≤ C * countBound n d p) :
    ∃ K : ℝ, ∀ᶠ n : ℕ in atTop, ∀ p : Fin (listLen n) → ℕ, ∑ k, p k = n ^ 2 →
      ∑ k, T n (listLen n) (p k) ≤ K * ((n : ℝ) ^ (2.0229 : ℝ) * Real.log n) := by
  obtain ⟨K, n₁, hcall⟩ := theorem_35_counting_call
  refine ⟨|C| * K, ?_⟩
  filter_upwards [eventually_ge_atTop n₀, eventually_ge_atTop n₁, eventually_ge_atTop 1]
    with n hn₀ hn₁ hn p hp
  obtain ⟨hone, -, hroot⟩ := theorem_35_d n hn
  calc ∑ k, T n (listLen n) (p k)
      ≤ ∑ k, |C| * countBound n (listLen n) (p k) :=
        Finset.sum_le_sum fun k _ =>
          le_abs_mul_of_le_mul (hcount n _ (p k) hn₀ hone hroot) (countBound_nonneg _ _ _)
    _ = |C| * ∑ k, countBound n (listLen n) (p k) := (Finset.mul_sum _ _ _).symm
    _ ≤ |C| * (K * ((n : ℝ) ^ (2.0229 : ℝ) * Real.log n)) :=
        mul_le_mul_of_nonneg_left (hcall n hn₁ p hp) (abs_nonneg C)
    _ = |C| * K * ((n : ℝ) ^ (2.0229 : ℝ) * Real.log n) := (mul_assoc _ _ _).symm

/-- Proof of Theorem 35, "(min,+)-product, APSP, and Exact Triangle": "So the Õ(n/d)
counting calls of Lemma 36(a) cost Õ((n/d) n^{2.0229}) = Õ(n^{3-1/40+0.0229})", for any one of the
problems for which Lemma 36(a) is assumed. -/
theorem lasVegasInPolylog_of_corollary_38_lemma_36a (M : TimeModel) (prob : RealProblem)
    (h38 : Claim.Corollary_38 M) (h36 : Claim.Lemma_36a M prob listLen) :
    LasVegasInPolylog M prob (3 - 1 / 40 + 0.0229) := by
  obtain ⟨C, n₀, T, hT, hcount⟩ := h38
  obtain ⟨calls, further, C₀, -, hcalls, hfurther, hreduce⟩ := h36 one_le_listLen_and_listLen_le
  obtain ⟨T', hT', htime⟩ := hreduce T hT
  obtain ⟨K, hcall⟩ := exists_counting_call_le hcount
  -- One counting call, with the `O(n d²) = O(n^{1.05})` subtractions that form its lists.
  have hlists : IsPowPolylog (fun n : ℕ => (n : ℝ) * (listLen n : ℝ) ^ 2) 1.05 :=
    ((isBigOPow_natCast.mul (isBigOPow_listLen.pow 2)).mono (by norm_num)).isPowPolylog
  have hcallClass : IsPowPolylog (fun n : ℕ => K * ((n : ℝ) ^ (2.0229 : ℝ) * Real.log n)
      + C₀ * ((n : ℝ) * (listLen n : ℝ) ^ 2)) 2.0229 :=
    ((isPowPolylog_rpow_mul_log 2.0229).const_mul K).add
      ((hlists.const_mul C₀).mono (by norm_num))
  -- All calls, `(1 - 1/40) + 2.0229`, and the further time, `3 - 1/40`.
  have htotal := (((isPowPolylog_of_mul_listLen hcalls).mul hcallClass).mono
    (b := 3 - 1 / 40 + 0.0229) (by norm_num)).add
      ((isPowPolylog_of_mul_listLen hfurther).mono (by norm_num))
  refine ⟨T', hT', htotal.upperPowPolylog.mono_left ?_⟩
  filter_upwards [hcall, eventually_ge_atTop 1] with n hcalln hn
  exact htime n _ hn hcalln

/-! ### 3SUM -/

/-- "a comparison count of Lemma 36(b) costs ... O(n^{1.9979} log n)": the bound of Corollary 38 at
`d = ⌊n^{1/40}⌋` and `⌈K n²/d⌉` pairs. -/
private theorem isPowPolylog_countBound_listLen (K : ℝ) :
    IsPowPolylog (fun n : ℕ => countBound n (listLen n) ⌈K * (n : ℝ) ^ 2 / (listLen n : ℝ)⌉₊)
      1.9979 := by
  have hpairs : IsBigOPow (fun n : ℕ => (⌈K * (n : ℝ) ^ 2 / (listLen n : ℝ)⌉₊ : ℝ))
      (2 - 1 / 40) :=
    ((isBigOPow_div_listLen ((isBigOPow_natCast_pow 2).const_mul K)).mono (by norm_num)).natCeil
      (by norm_num)
  -- The exponents: `2 - 1/40 + 0.0229 = 1.9979`, `2 - 0.126/40 ≤ 1.9979`, `2 - 1/440 ≤ 1.9979`.
  exact (((hpairs.mul (isBigOPow_rpow 0.0229)).mono (by norm_num)).add
    (isBigOPow_sq_div_listLen_rpow.mono (by norm_num))).isPowPolylog.add
      ((isPowPolylog_rpow_mul_log _).mono (by norm_num))

/-- Proof of Theorem 35, "3SUM": "a comparison count of Lemma 36(b) costs ...
O(n^{1.9979} log n), so 3SUM can also be solved in Õ(n^{1.9979}) ... expected time." -/
theorem lasVegasInPolylog_threeSum_of_corollary_38_lemma_36b (M : TimeModel)
    (h38 : Claim.Corollary_38 M) (h36 : Claim.Lemma_36b M listLen) :
    LasVegasInPolylog M RealProblem.threeSum 1.9979 := by
  obtain ⟨C, n₀, T, hT, hcount⟩ := h38
  obtain ⟨Num, further, C₀, K, hNum0, hNum, hfurther, hreduce⟩ :=
    h36 one_le_listLen_and_listLen_le
  -- One comparison count, with the `O(n d) = O(n^{1.025})` subtractions that form its lists.
  have hlists : IsPowPolylog (fun n : ℕ => (n : ℝ) * (listLen n : ℝ)) (1 + 1 / 40) :=
    (isBigOPow_natCast.mul isBigOPow_listLen).isPowPolylog
  have hcountClass := ((isPowPolylog_countBound_listLen K).const_mul |C|).add
    ((hlists.const_mul C₀).mono (b := 1.9979) (by norm_num))
  -- The `(log n)^{O(1)}` counts, and the further time, `2 - 1/40`.
  have htotal := ((hNum.mul hcountClass).mono (b := 1.9979) (by norm_num)).add
    ((isPowPolylog_of_mul_listLen hfurther).mono (by norm_num))
  refine ⟨_, hreduce T hT, htotal.upperPowPolylog.mono_left ?_⟩
  filter_upwards [eventually_ge_atTop n₀, eventually_ge_atTop 1] with n hn₀ hn
  obtain ⟨hone, -, hroot⟩ := theorem_35_d n hn
  -- The time is `Num n * (T n d ⌈K n²/d⌉ + C₀ (n d)) + further n`; only `T` is replaced.
  have hcountn := le_abs_mul_of_le_mul
    (hcount n _ ⌈K * (n : ℝ) ^ 2 / (listLen n : ℝ)⌉₊ hn₀ hone hroot) (countBound_nonneg _ _ _)
  exact add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_left hcountn _) (hNum0 n)) _

/-! ### Absorbing the logarithms, and high probability -/

/-- `log₂ n = Õ(1)`. -/
private theorem isPowPolylog_logb_two : IsPowPolylog (fun n : ℕ => Real.logb 2 n) 0 := by
  simpa only [Real.logb, div_eq_mul_inv] using isPowPolylog_log.mul_const (Real.log 2)⁻¹

/-- Proof of Theorem 35: "Õ(n^a) ≤ O(n^b)" for `a < b`, at the level of claims, and "The bounds also
hold with probability 1 - n^{-c} for any constant c", by restarting. The factor `log n` of the
restarts is absorbed because `a < b`; `b > 0` absorbs the `+ 1` in the length `T n + 1` of a run. -/
theorem lasVegasIn_and_whpIn_of_polylog {M : TimeModel} {prob : RealProblem} {a b : ℝ}
    (hab : a < b) (hb : 0 < b) (hrestart : Claim.Restart M) (h : LasVegasInPolylog M prob a) :
    Claim.LasVegasIn M prob b ∧ Claim.LasVegasWhpIn M prob b := by
  obtain ⟨T, hT, hTa⟩ := h
  obtain ⟨C₀, hC₀, hwhp⟩ := hrestart
  obtain ⟨G, -, hG, hTG⟩ := hTa.exists_isPowPolylog
  refine ⟨⟨T, hT, hTa.upperBigOPow hab⟩, fun c hc => ?_⟩
  have hruns : IsPowPolylog (fun n : ℕ => c * Real.logb 2 n + 1) 0 :=
    (isPowPolylog_logb_two.const_mul c).add (isPowPolylog_const 1)
  have hrun : IsPowPolylog (fun n : ℕ => G n + 1) (max a 0) :=
    (hG.mono (le_max_left a 0)).add ((isPowPolylog_const 1).mono (le_max_right a 0))
  refine ⟨_, hwhp prob T c hc hT, (((hruns.mul hrun).const_mul C₀).isBigOPow
    ((zero_add _).trans_lt (max_lt hab hb))).upperBigOPow.mono_left ?_⟩
  filter_upwards [hTG, eventually_ge_atTop 1] with n hTGn hn
  have hruns0 : 0 ≤ c * Real.logb 2 n + 1 :=
    add_nonneg (mul_nonneg hc (Real.logb_nonneg one_lt_two (Nat.one_le_cast.2 hn))) zero_le_one
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (add_le_add_left hTGn 1) hruns0) hC₀

end ConditionalTimes

/-- The deduction of all the bounds of **Theorem 35** (and of the second half of
Theorem 2) from Corollary 38, Lemma 36 and the restart argument: "Let d := ⌊n^{1/40}⌋, apply
Lemma 36 with this d, and answer every comparison count by Corollary 38." `listLen n` is this d.
This theorem does not prove Theorem 35: every hypothesis is a running-time claim about `M` that is
assumed here, and Lemma 36 rests on results cited from [CVX22]. -/
theorem conditional_theorem_35 (M : TimeModel) (h38 : Claim.Corollary_38 M)
    (hm : Claim.Lemma_36a M RealProblem.minPlusProduct ComparisonCounts.listLen)
    (ha : Claim.Lemma_36a M RealProblem.apsp ComparisonCounts.listLen)
    (ht : Claim.Lemma_36a M RealProblem.exactTriangle ComparisonCounts.listLen)
    (hs : Claim.Lemma_36b M ComparisonCounts.listLen) (hr : Claim.Restart M) :
    Claim.Theorem_35 M := by
  -- `1.9979 < 1.998` and `3 - 1/40 + 0.0229 = 2.9979 < 2.998`
  have hsum := lasVegasIn_and_whpIn_of_polylog (b := 1.998) (by norm_num) (by norm_num) hr
    (lasVegasInPolylog_threeSum_of_corollary_38_lemma_36b M h38 hs)
  have hcubic (prob : RealProblem) (h36 : Claim.Lemma_36a M prob ComparisonCounts.listLen) :=
    lasVegasIn_and_whpIn_of_polylog (b := 2.998) (by norm_num) (by norm_num) hr
      (lasVegasInPolylog_of_corollary_38_lemma_36a M prob h38 h36)
  exact ⟨⟨hsum.1, (hcubic _ hm).1, (hcubic _ ha).1, (hcubic _ ht).1⟩,
    ⟨hsum.2, (hcubic _ hm).2, (hcubic _ ha).2, (hcubic _ ht).2⟩⟩

end ThreeSumApsp
