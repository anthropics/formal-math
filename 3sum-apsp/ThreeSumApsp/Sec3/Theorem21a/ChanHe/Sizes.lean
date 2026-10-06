/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec3.Theorem21a.ChanHe.FromNumbers
public import ThreeSumApsp.Util.Asymptotics.SoftOSqrtPow

/-!
# Theorem 21(a), the reduction of Chan and He: inputs of absolute value at most n ^ κ

From n integers bounded by a power of n, the reduction after [CH20, Theorem 5.1] computes
polylogarithmically many arrays of length Õ(n), in Õ(n^{3/2}) time.  This file puts `n ^ κ` for the
bound `U` on the input and proves the three bounds, the last one for the count `scanPairs` in place
of a running time.

* The numbers have `Lam (2 n^κ) = O(log n)` binary digits (`Lam_pow_le`).  So the bound `mPar` on
  the primes is `√n` times a polylogarithm (`softO_mPar`).
* The reduction is correct (`threeSum_iff_exists_convolution3SUM`), there are at most `numBound κ n`
  instances (`length_instances_pow_le`) with entries of absolute value at most `120 n^κ + 40`
  (`abs_instances_pow_le`), and the searches look at no more than `workBound κ n` pairs
  (`scanPairs_pow_le`).
* `numBound κ n` is a polylogarithm, the length `lenOf κ n` of the instances is `n` times a
  polylogarithm, and `workBound κ n` is `n^{3/2}` times a polylogarithm (`isPowPolylog_numBound`,
  `isPowPolylog_lenOf`, `isPowPolylog_workBound`).  These three bounds and `softO_mPar` follow the
  definitions of the parameters through the calculus `SoftOSqrtPow`.
-/

public section

namespace ThreeSumApsp

namespace ChanHe

open Finset

/-! ## The parameters -/

/-- `Lam (2 n^κ) ≤ κ(⌊log₂ n⌋ + 1) + 3`. -/
theorem Lam_pow_le (n κ : ℕ) : Lam (2 * n ^ κ) ≤ κ * (Nat.log 2 n + 1) + 3 := by
  have hn : n ≤ 2 ^ (Nat.log 2 n + 1) := (Nat.lt_pow_succ_log_self (by norm_num) n).le
  refine Nat.succ_le_succ ((Nat.log_mono_right ?_).trans_eq
    (Nat.log_pow (by norm_num) (κ * (Nat.log 2 n + 1) + 2)))
  calc 2 * (2 * n ^ κ) ≤ 2 * (2 * (2 ^ (Nat.log 2 n + 1)) ^ κ) := by gcongr
    _ = 2 ^ (κ * (Nat.log 2 n + 1) + 2) := by rw [← pow_mul, mul_comm κ]; ring

/-- The number of binary digits is a polylogarithm. -/
theorem softO_Lam (κ : ℕ) : SoftOSqrtPow (fun n => Lam (2 * n ^ κ)) 0 := by
  unfold Lam
  growth_sqrt []

/-- The number of primes that we want to choose from is `√n` times a polylogarithm. -/
theorem softO_wPar (κ : ℕ) : SoftOSqrtPow (fun n => wPar n (2 * n ^ κ) + 1) 1 := by
  unfold wPar
  growth_sqrt [softO_Lam κ]

/-- **The bound on the primes is `√n` times a polylogarithm.** -/
theorem softO_mPar (κ : ℕ) : SoftOSqrtPow (fun n => mPar n (2 * n ^ κ)) 1 := by
  unfold mPar
  growth_sqrt [softO_wPar κ]

/-- The instances are not empty arrays. -/
theorem one_le_lenOf (κ n : ℕ) : 1 ≤ lenOf κ n :=
  Nat.succ_le_of_lt (by unfold lenOf mPar; positivity)

/-! ## Correctness, the number of instances, their entries, and the count for the searches -/

/-- **The number of instances is at most `numBound κ n`.** -/
theorem length_instances_pow_le (n κ : ℕ) (hn : 2 ≤ n) (x : Fin n → ℤ) :
    (instances n (n ^ κ) x).length ≤ numBound κ n := by
  have hlog : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) hn
  have hΛ : Lam (2 * n ^ κ) ≤ (κ + 2) * (Nat.log 2 n + 1) :=
    (Lam_pow_le n κ).trans (by rw [add_mul]; omega)
  have hone : 1 ≤ ((κ + 2) * (Nat.log 2 n + 1)) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  calc (instances n (n ^ κ) x).length
      ≤ (2 * Lam (2 * n ^ κ) ^ 2 + 2) * (2 * Nat.log 2 n + 2) ^ 5 := length_instances_le ..
    _ ≤ (2 * ((κ + 2) * (Nat.log 2 n + 1)) ^ 2 + 2 * ((κ + 2) * (Nat.log 2 n + 1)) ^ 2) *
        (2 * Nat.log 2 n + 2) ^ 5 := by gcongr; omega
    _ = numBound κ n := by unfold numBound; ring

section input

variable {κ n : ℕ} {x : Fin n → ℤ}

/-- **The searches look at no more than `workBound κ n` pairs.**  This bounds the count
`scanPairs`, which we define; it is not a running time. -/
theorem scanPairs_pow_le (hn : 2 ≤ n) (hx : ∀ i, |x i| ≤ (n : ℤ) ^ κ) :
    scanPairs n (n ^ κ) x ≤ workBound κ n :=
  (scanPairs_le (by omega) (by exact_mod_cast hx)).trans
    (Nat.mul_le_mul_right _ (length_instances_pow_le n κ hn x))

/-- **The entries of the instances have absolute value at most `120 n^κ + 40`.** -/
theorem abs_instances_pow_le (hn : 2 ≤ n) (hx : ∀ i, |x i| ≤ (n : ℤ) ^ κ) {y : ℕ → ℤ}
    (hy : y ∈ instances n (n ^ κ) x) (u : ℕ) : |y u| ≤ 120 * (n : ℤ) ^ κ + 40 := by
  exact_mod_cast abs_instances_le (by omega) (by exact_mod_cast hx) hy u

/-- `Convolution3SUM` on the first `N` cells of an array `y : ℕ → ℤ` is the problem
`ConvOne N y`. -/
theorem convolution3SUM_iff_convOne (N : ℕ) (y : ℕ → ℤ) :
    Convolution3SUM (fun i : Fin N => y i) ↔ ConvOne N y :=
  ⟨fun ⟨i, j, h, e⟩ => ⟨i, j, h, e⟩, fun ⟨u, v, h, e⟩ => ⟨⟨u, by omega⟩, ⟨v, by omega⟩, h, e⟩⟩

/-- **The reduction is correct**: three of the numbers, at different positions, sum to 0 iff one of
the instances, read at the length `lenOf κ n`, is a yes-instance of Convolution-3SUM. -/
theorem threeSum_iff_exists_convolution3SUM (hn : 2 ≤ n) (hx : ∀ i, |x i| ≤ (n : ℤ) ^ κ) :
    ThreeSum x ↔
      ∃ y ∈ instances n (n ^ κ) x, Convolution3SUM fun i : Fin (lenOf κ n) => y i := by
  simp only [convolution3SUM_iff_convOne]
  -- `lenOf κ n` is `8 m²` by definition
  exact instances_correct n (n ^ κ) (by omega) x (by exact_mod_cast hx)

end input

/-! ## The three bounds in asymptotic form -/

/-- The bound on the number of instances, in the calculus. -/
private theorem softO_numBound (κ : ℕ) : SoftOSqrtPow (numBound κ) 0 := by
  unfold numBound
  growth_sqrt []

/-- The bound on the number of instances is a polylogarithm. -/
theorem isPowPolylog_numBound (κ : ℕ) : IsPowPolylog (fun n => (numBound κ n : ℝ)) 0 :=
  (softO_numBound κ).isPowPolylog (by norm_num)

/-- The length of the instances is `n` times a polylogarithm. -/
theorem isPowPolylog_lenOf (κ : ℕ) : IsPowPolylog (fun n => (lenOf κ n : ℝ)) 1 :=
  SoftOSqrtPow.isPowPolylog (i := 2) (by unfold lenOf; growth_sqrt [softO_mPar κ]) (by norm_num)

/-- The bound on the number of pairs that the searches look at is `n^{3/2}` times a polylogarithm.
It bounds a count of pairs, not a running time. -/
theorem isPowPolylog_workBound (κ : ℕ) : IsPowPolylog (fun n => (workBound κ n : ℝ)) (3 / 2) :=
  SoftOSqrtPow.isPowPolylog (i := 3)
    (by unfold workBound; growth_sqrt [softO_numBound κ, softO_mPar κ]) (by norm_num)

end ChanHe

end ThreeSumApsp
