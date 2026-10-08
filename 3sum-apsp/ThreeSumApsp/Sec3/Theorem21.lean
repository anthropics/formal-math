/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Asymptotics.PowLittleO
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Theorem 21: 3SUM, the (min,+)-product and APSP reduce to Exact Triangle

Theorem 21 collects known reductions; the paper cites them and gives no proof.

Part (a), 3SUM.
* [CH20, Theorem 5.1], from 3SUM to Convolution-3SUM: `theorem_21a_threeSum_to_convolution`.
* [VW13, Theorem 4.3], from Convolution-3SUM to Exact Triangle: `theorem_21a_convolution_to_exact`.
* The arithmetic of composing the two: `n^{1/2+o(1)}` instances, each on `n^{1/2+o(1)}` vertices per
  part, in `n^{3/2+o(1)}` time (`theorem_21a_compose`, in this file).

Part (b), the (min,+)-product and APSP.
* Repeated squaring computes the distances, and the finite entries are bounded:
  `theorem_21b_repeated_squaring`, `theorem_21b_entries_bounded`.
* [VW13, Theorem 3.3], from Negative Triangle to Exact Triangle: `theorem_21b_negative_to_exact`.
* [VW18, Theorem 4.2 and Lemma 4.1] have no statement in this folder; the reductions are written as
  programs, with proofs (`claim_VW18_Theorem_4_2`).
* The logarithmic factors of the two running times (`theorem_21b_log_factors`, in this file).
-/

public section

namespace ThreeSumApsp

/-! ## Part (a): the two reductions composed -/

/-- For **Theorem 21(a)**: the arithmetic of the composition of the two reductions.  The first
reduction [CH20] takes time `E₁ = Õ(n^{3/2})` and produces `Num₁` arrays, polylogarithmically many,
of length `N = Õ(n)`; the second [VW13], on an array of length `N`, takes time `E₂ = N^{3/2+o(1)}`
and produces `Num₂ = O(√N)` instances with `size₂ = O(√N)` vertices in each part.  Together:
`n^{1/2+o(1)}` instances, each on `n^{1/2+o(1)}` vertices per part, in `n^{3/2+o(1)}` time, as
Theorem 21(a) says.  The six functions are arbitrary, so the statement is arithmetic only; it is not
applied to the bounds of the two reductions.

NOTE.  The hypothesis on `E₂` is what the time `n^{3/2+o(1)}` of Theorem 21(a) asks of the second
reduction. -/
theorem theorem_21a_compose {E₁ Num₁ E₂ Num₂ : ℕ → ℝ} {N size₂ : ℕ → ℕ}
    (hE₁ : IsPowPolylog E₁ (3 / 2)) (hNum₁ : IsPowPolylog Num₁ 0)
    (hN : IsPowPolylog (fun n => (N n : ℝ)) 1)
    (hE₂ : IsPowLittleO E₂ (3 / 2)) (hNum₂ : IsBigOPow Num₂ (1 / 2))
    (hsize₂ : IsBigOPow (fun m => (size₂ m : ℝ)) (1 / 2)) :
    IsPowLittleO (fun n => Num₁ n * Num₂ (N n)) (1 / 2) ∧
    IsPowLittleO (fun n => (size₂ (N n) : ℝ)) (1 / 2) ∧
    IsPowLittleO (fun n => E₁ n + Num₁ n * E₂ (N n)) (3 / 2) := by
  -- A quantity `g(N) = N^{a+o(1)}` of the second reduction is `n^{a+o(1)}`, because
  -- `N = n^{1+o(1)}`, and the factor `Num₁ = n^{o(1)}` does not change the exponent.
  have hcomp {g : ℕ → ℝ} {a : ℝ} (ha : 0 ≤ a) (hg : IsPowLittleO g a) :
      IsPowLittleO (fun n => g (N n)) a := by
    simpa only [mul_one] using hg.comp hN.isPowLittleO ha zero_le_one
  have hmul {g : ℕ → ℝ} {a : ℝ} (ha : 0 ≤ a) (hg : IsPowLittleO g a) :
      IsPowLittleO (fun n => Num₁ n * g (N n)) a := by
    simpa only [zero_add] using hNum₁.isPowLittleO.mul (hcomp ha hg)
  exact ⟨hmul (by norm_num) hNum₂.isPowLittleO, hcomp (by norm_num) hsize₂.isPowLittleO,
    hE₁.isPowLittleO.add (hmul (by norm_num) hE₂)⟩

/-! ## Part (b): the logarithmic factors -/

/-- `⌈log₂ n⌉ ≤ 3 ln n` for `n ≥ 2`, because `⌈log₂ n⌉ < log₂ n + 1 ≤ 2 log₂ n` and `ln 2 > 2/3`. -/
private theorem clog_two_le {n : ℕ} (hn : 2 ≤ n) : (Nat.clog 2 n : ℝ) ≤ 3 * Real.log n := by
  have hlog2 : 2 / 3 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn)
  have hlt : (Nat.clog 2 n : ℝ) < Real.log n / Real.log 2 + 1 := by
    exact_mod_cast Real.natCast_clog_lt_logb_add_one 2 n
  have hone : 1 ≤ Real.log n / Real.log 2 := (one_le_div (by linarith)).2 hlogn
  have hdiv : Real.log n / Real.log 2 ≤ 3 / 2 * Real.log n := by
    rw [div_le_iff₀ (by linarith)]
    have hmul := mul_le_mul_of_nonneg_left hlog2.le (by linarith : 0 ≤ 3 / 2 * Real.log n)
    linarith [hmul]
  linarith [hlt, hone, hdiv]

/-- For **Theorem 21(b)**: the logarithmic factors.  Let `τ` be the time of Exact Triangle and `τ'`
that of Negative Triangle, both on `n^{1/3}` vertices per part.  With `τ' = O(τ log U)`, the bound
`O(n² τ' log U)` of [VW18, Theorem 4.2] becomes `O(n² τ log² U)`, and `⌈log₂ n⌉` products with
`U = n^{κ+1}` cost `O(n² τ log³ n)`.  Here `κ` is the paper's ν, and `τ` stands for the `T(n^{1/3})`
of Theorem 21(b); `τ` and `τ'` are arbitrary numbers, so the statement is arithmetic only.

NOTE.
* Both halves are stated for `U = n^{κ+1}`, the first one too.
* The condition that T(s)/s is nondecreasing, and the like condition of [VW18, Theorem 4.2], do not
  occur. -/
theorem theorem_21b_log_factors {n : ℕ} {κ c τ τ' : ℝ} (hn : 2 ≤ n) (hκ : 0 ≤ κ) (hτ : 0 ≤ τ)
    (hτ' : τ' ≤ c * (τ * Real.log ((n : ℝ) ^ (κ + 1)))) :
    (n : ℝ) ^ 2 * τ' * Real.log ((n : ℝ) ^ (κ + 1))
      ≤ c * ((n : ℝ) ^ 2 * τ * Real.log ((n : ℝ) ^ (κ + 1)) ^ 2) ∧
    (Nat.clog 2 n : ℝ) * ((n : ℝ) ^ 2 * τ * Real.log ((n : ℝ) ^ (κ + 1)) ^ 2)
      ≤ 3 * (κ + 1) ^ 2 * ((n : ℝ) ^ 2 * τ * Real.log n ^ 3) := by
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  rw [Real.log_rpow (Nat.cast_pos.mpr (by omega))] at hτ' ⊢
  set Λ := (κ + 1) * Real.log n with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  constructor
  · calc (n : ℝ) ^ 2 * τ' * Λ ≤ (n : ℝ) ^ 2 * (c * (τ * Λ)) * Λ := by gcongr
      _ = c * ((n : ℝ) ^ 2 * τ * Λ ^ 2) := by ring
  · calc (Nat.clog 2 n : ℝ) * ((n : ℝ) ^ 2 * τ * Λ ^ 2)
        ≤ 3 * Real.log n * ((n : ℝ) ^ 2 * τ * Λ ^ 2) := by
          gcongr
          exact clog_two_le hn
      _ = 3 * (κ + 1) ^ 2 * ((n : ℝ) ^ 2 * τ * Real.log n ^ 3) := by
          rw [hΛ]
          ring

end ThreeSumApsp
