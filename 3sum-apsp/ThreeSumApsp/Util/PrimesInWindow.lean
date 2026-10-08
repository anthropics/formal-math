/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Log
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.NumberTheory.Bertrand

/-!
# Counting the primes in a window of ratio two

The proof of Theorem 17 says: "By the prime number theorem there are Ω(√D / log D) primes
in the range", the range being `[√D/2, √D)`, and it uses this for every `16 ≤ D ≤ n`, not only for
large `D`.  This file proves the bound for every `D ≥ 16`, with some positive constant.

## Main results

* `Nat.exists_forall_mul_div_log_le_card_primes`: there is a `c > 0` such that for every real
  `x ≥ 4` there are at least `c · x / log x` primes `p` with `x/2 ≤ p < x`;
  `Nat.exists_prime_half_le_and_lt`: there is one.
* `Nat.exists_forall_mul_sqrt_div_log_le_card_primes`: there is a `c > 0` such that for every
  natural number `D ≥ 16` there are at least `c · √D / log D` primes `p` with `√D/2 ≤ p < √D`. This
  is the sentence of the proof of Theorem 17.

## The proof

The prime number theorem is not needed: Erdős's proof of Bertrand's postulate, read as a count
instead of as an existence statement, is enough.  Write `k` for the number of primes in `(n, 2n]`.

1. Split the prime factorization of the central binomial coefficient `C(2n, n)`.  Every prime power
   in it is at most `2n` (`prod_pow_factorization_le`), so the primes up to `√(2n)` contribute at
   most `(2n)^√(2n)` and the primes in `(n, 2n]` at most `(2n)^k`.  A prime above `√(2n)` occurs at
   most once, and the primes in `(2n/3, n]` do not occur at all, so the primes in `(√(2n), n]`
   contribute at most `4^(2n/3)` (`prod_middle_le`).  Together: `centralBinom_le`.
2. An elementary estimate: `n^6 · (2n)^(6√(2n)) ≤ 2^n` for `n ≥ 16562`
   (`pow_mul_pow_sqrt_le_two_pow`).
3. With `4^n < n · C(2n, n)` the two give `2^n ≤ (2n)^(2k)`, that is, `k ≥ n / (2 log₂ (2n))`, for
   `n ≥ 16562` (`two_pow_le_of_large`).
4. A window `[x/2, x)` with real endpoints contains `(n, 2n]` for an `n ≥ x/4`
   (`exists_nat_window`).  If `n ≥ 16562`, step 3 applies.  If not, `x` is bounded, and the one
   prime of Bertrand's postulate is enough.
5. The case `x = √D`.

## Credit

Mathlib proves Bertrand's postulate by the same argument.  The proofs of `centralBinom_le` (with
`prod_middle_le`), `concaveOn_log_add_sqrt_mul_log_sub` and `log_add_sqrt_mul_log_le` are adapted
from Mathlib, Mathlib/NumberTheory/Bertrand.lean (Copyright (c) 2020 Patrick Stevens, released under
the Apache 2.0 license; authors: Patrick Stevens, Bolton Bailey).
-/

public section

open Finset

namespace Nat

/-- The primes `p` with `n < p ≤ 2n`: the primes that Bertrand's postulate is about. -/
private def bertrandPrimes (n : ℕ) : Finset ℕ := (Ioc n (2 * n)).filter Nat.Prime

/-- Membership in `bertrandPrimes`, spelled out. -/
private theorem mem_bertrandPrimes {n p : ℕ} :
    p ∈ bertrandPrimes n ↔ (n < p ∧ p ≤ 2 * n) ∧ p.Prime := by
  simp only [bertrandPrimes, mem_filter, mem_Ioc]

/-! ## 1. Erdős's upper bound for the central binomial coefficient -/

/-- Every prime power in `C(2n, n)` is at most `2n`, so `|s|` of them multiply to at most
`(2n)^|s|`. -/
private theorem prod_pow_factorization_le {n : ℕ} (hn : 0 < n) (s : Finset ℕ) :
    ∏ p ∈ s, p ^ n.centralBinom.factorization p ≤ (2 * n) ^ s.card :=
  prod_le_pow_card _ _ _ fun _ _ => Nat.pow_factorization_choose_le (by omega)

/-- The primes in `(√(2n), n]` contribute at most `4^(2n/3)` to `C(2n, n)`: their exponent is at
most 1, it is 0 above `2n/3`, and the product of the primes up to `2n/3` is at most `4^(2n/3)`.
Adapted from Mathlib, Mathlib/NumberTheory/Bertrand.lean, Apache 2.0. -/
private theorem prod_middle_le {n : ℕ} (hn : 2 < n) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ Nat.sqrt (2 * n) < p ∧ p ≤ n) :
    ∏ p ∈ s, p ^ n.centralBinom.factorization p ≤ 4 ^ (2 * n / 3) :=
  calc ∏ p ∈ s, p ^ n.centralBinom.factorization p
      ≤ ∏ p ∈ s, (if p ≤ 2 * n / 3 then p else 1) := by
        refine prod_le_prod' fun p hp => ?_
        obtain ⟨hprime, hsqrt, hpn⟩ := hs p hp
        split_ifs with h3
        · exact (pow_right_mono₀ hprime.one_lt.le
            (Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp hsqrt))).trans (pow_one p).le
        · rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hpn (by omega),
            pow_zero]
    _ = ∏ p ∈ s.filter (· ≤ 2 * n / 3), p := (prod_filter _ _).symm
    _ ≤ primorial (2 * n / 3) := by
        refine prod_le_prod_of_subset_of_one_le' (fun p hp => ?_)
          fun p hp _ => (mem_filter.1 hp).2.one_lt.le
        obtain ⟨hps, hp3⟩ := mem_filter.1 hp
        exact mem_filter.2 ⟨mem_range.2 (by omega), (hs p hps).1⟩
    _ ≤ 4 ^ (2 * n / 3) := primorial_le_four_pow _

/-- Erdős's bound, keeping the primes of `(n, 2n]`:
`C(2n, n) ≤ (2n)^√(2n) · 4^(2n/3) · (2n)^k`, where `k` is the number of primes in `(n, 2n]`.
Mathlib proves the case `k = 0` on the way to Bertrand's postulate
(`centralBinom_le_of_no_bertrand_prime`).  Adapted from Mathlib, Mathlib/NumberTheory/Bertrand.lean,
Apache 2.0. -/
private theorem centralBinom_le (n : ℕ) (hn : 2 < n) :
    n.centralBinom ≤
      (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) * (2 * n) ^ (bertrandPrimes n).card := by
  -- `C(2n, n)` is the product of its prime powers over the set `T` of the primes up to `2n`.
  set T := (range (2 * n + 1)).filter Nat.Prime with hT
  have hprod : ∏ p ∈ T, p ^ n.centralBinom.factorization p = n.centralBinom :=
    (prod_filter_of_ne fun p _ h => by
      contrapose h
      rw [Nat.factorization_eq_zero_of_not_prime _ h, pow_zero]).trans
      n.prod_pow_factorization_centralBinom
  -- Split the primes at `n`, and those up to `n` at `√(2n)`.
  rw [← hprod, ← prod_filter_mul_prod_filter_not T (· ≤ n),
    ← prod_filter_mul_prod_filter_not (T.filter (· ≤ n)) (· ≤ Nat.sqrt (2 * n))]
  refine mul_le_mul' (mul_le_mul' ?_ ?_) ?_
  · -- There are at most `√(2n)` primes up to `√(2n)`.
    have hsub : (T.filter (· ≤ n)).filter (· ≤ Nat.sqrt (2 * n)) ⊆ Icc 1 (Nat.sqrt (2 * n)) := by
      intro p hp
      simp only [hT, mem_filter, mem_range] at hp
      obtain ⟨⟨⟨-, hprime⟩, -⟩, hsqrt⟩ := hp
      exact mem_Icc.mpr ⟨hprime.one_lt.le, hsqrt⟩
    exact (prod_pow_factorization_le (by omega) _).trans (pow_right_mono₀ (by omega)
      ((card_le_card hsub).trans_eq (by rw [Nat.card_Icc, Nat.add_sub_cancel])))
  · -- The primes in `(√(2n), n]`.
    refine prod_middle_le hn _ fun p hp => ?_
    simp only [hT, mem_filter, mem_range, not_le] at hp
    obtain ⟨⟨⟨-, hprime⟩, hpn⟩, hsqrt⟩ := hp
    exact ⟨hprime, hsqrt, hpn⟩
  · -- The primes above `n` are those of `(n, 2n]`.
    refine (prod_pow_factorization_le (by omega) _).trans
      (pow_right_mono₀ (by omega) (card_le_card fun p hp => ?_))
    simp only [hT, mem_filter, mem_range] at hp
    obtain ⟨⟨hp2n, hprime⟩, hnp⟩ := hp
    exact mem_bertrandPrimes.2 ⟨⟨by omega, by omega⟩, hprime⟩

/-! ## 2. The elementary estimate `n^6 · (2n)^(6√(2n)) ≤ 2^n` for `n ≥ 16562` -/

/-- For `a ≥ 0` the function `log x + √(2x) · log (2x) - a x` is concave for `x > 1/2`.
Adapted from Mathlib, Mathlib/NumberTheory/Bertrand.lean, Apache 2.0 (there inside
`Bertrand.real_main_inequality`, for `a = log 4 / 3`). -/
private theorem concaveOn_log_add_sqrt_mul_log_sub (a : ℝ) (ha : 0 ≤ a) :
    ConcaveOn ℝ (Set.Ioi (1 / 2 : ℝ))
    (fun x : ℝ => Real.log x + √(2 * x) * Real.log (2 * x) - a * x) := by
  apply ConcaveOn.sub
  · apply ConcaveOn.add
    · exact strictConcaveOn_log_Ioi.concaveOn.subset
        (Set.Ioi_subset_Ioi (by norm_num)) (convex_Ioi _)
    · have h := strictConcaveOn_sqrt_mul_log_Ioi.concaveOn.comp_linearMap
        ((2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
      have hset : (⇑((2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))) ⁻¹' Set.Ioi 1 = Set.Ioi (1 / 2) := by
        ext x
        simp only [Set.mem_Ioi, Set.mem_preimage, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
          smul_eq_mul]
        constructor <;> intro h <;> linarith
      rw [hset] at h
      exact h
  · exact ConvexOn.smul ha (convexOn_id (convex_Ioi _))

/-- `log x + √(2x) · log (2x) ≤ (log 2 / 6) · x` for `x ≥ 16562`.  The difference of the two sides
is concave, it is nonnegative at `x = 2` and nonpositive at `x = 16562 = 2 · 91²` (where
`√(2x) = 182`; the only numerical input is `91^13 ≤ 2^85`), so it is nonpositive from there on.
Adapted from Mathlib, Mathlib/NumberTheory/Bertrand.lean, Apache 2.0 (the same argument proves
`Bertrand.real_main_inequality` there, with other numbers). -/
private theorem log_add_sqrt_mul_log_le {x : ℝ} (hx : 16562 ≤ x) :
    Real.log x + √(2 * x) * Real.log (2 * x) ≤ Real.log 2 / 6 * x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hat2 : (0 : ℝ) ≤
      Real.log 2 + √(2 * 2) * Real.log (2 * 2) - Real.log 2 / 6 * 2 := by
    rw [Real.sqrt_mul_self (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have hat16562 : Real.log 16562 + √(2 * 16562) * Real.log (2 * 16562)
      - Real.log 2 / 6 * 16562 ≤ 0 := by
    have hlog91 : 13 * Real.log 91 ≤ 85 * Real.log 2 := by
      have h := Real.log_le_log (by positivity) (show (91 : ℝ) ^ 13 ≤ 2 ^ 85 by norm_num)
      rw [Real.log_pow, Real.log_pow] at h
      exact_mod_cast h
    have hlogx : Real.log 16562 = Real.log 2 + 2 * Real.log 91 := by
      rw [show (16562 : ℝ) = 2 * 91 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      norm_num
    have hlog2x : Real.log (182 * 182) = 2 * Real.log 2 + 2 * Real.log 91 := by
      rw [show (182 * 182 : ℝ) = 2 ^ 2 * 91 ^ 2 by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
      norm_num
    rw [show (2 * 16562 : ℝ) = 182 * 182 by norm_num, Real.sqrt_mul_self (by norm_num), hlogx,
      hlog2x]
    -- `366 log 91 ≤ 366 · (85/13) log 2 < (16562/6 - 365) log 2`
    linarith only [hlog91, hlog2]
  have hconcave := concaveOn_log_add_sqrt_mul_log_sub (Real.log 2 / 6) (by positivity)
  have hatx := hconcave.right_le_of_le_left''
    (x := 2) (y := 16562) (z := x) (by norm_num [Set.mem_Ioi]) (by rw [Set.mem_Ioi]; linarith)
    (by norm_num) hx (hat16562.trans hat2)
  linarith only [hatx, hat16562]

/-- The same estimate for natural numbers, without logarithms. -/
private theorem pow_mul_pow_sqrt_le_two_pow {n : ℕ} (hn : 16562 ≤ n) :
    n ^ 6 * (2 * n) ^ (6 * Nat.sqrt (2 * n)) ≤ 2 ^ n := by
  have hx : (16562 : ℝ) ≤ n := by exact_mod_cast hn
  have hreal := log_add_sqrt_mul_log_le hx
  have hsqrt : (Nat.sqrt (2 * n) : ℝ) ≤ √(2 * n) := by
    exact_mod_cast Real.nat_sqrt_le_real_sqrt (a := 2 * n)
  have hlog : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith)
  have hpos : (0 : ℝ) < n := by linarith
  rw [← Nat.cast_le (α := ℝ)]
  push_cast
  rw [← Real.log_le_log_iff (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  -- `6 log n + 6 ⌊√(2n)⌋ log(2n) ≤ 6 (log n + √(2n) log(2n)) ≤ n log 2`
  linarith [hreal, mul_le_mul_of_nonneg_right hsqrt hlog]

/-! ## 3. The count for `n ≥ 16562` -/

/-- `2^n ≤ (2n)^(2k)` for `n ≥ 16562`.  If it failed, the sixth power of
`4^n < n · (2n)^√(2n) · 4^(2n/3) · (2n)^k` would give
`2^(12n) < (n^6 (2n)^(6√(2n))) · 2^(8n) · 2^(3n) ≤ 2^(12n)`. -/
private theorem two_pow_le_of_large {n : ℕ} (hn : 16562 ≤ n) :
    2 ^ n ≤ (2 * n) ^ (2 * (bertrandPrimes n).card) := by
  by_contra hcon
  have hfew : (2 * n) ^ (2 * (bertrandPrimes n).card) ≤ 2 ^ n := (not_le.mp hcon).le
  have herdos : 4 ^ n < n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)
      * (2 * n) ^ (bertrandPrimes n).card) :=
    (Nat.four_pow_lt_mul_centralBinom n (by omega)).trans_le
      (Nat.mul_le_mul_left _ (centralBinom_le n (by omega)))
  have hsmall := pow_mul_pow_sqrt_le_two_pow hn
  have hmiddle : 4 ^ (6 * (2 * n / 3)) ≤ 4 ^ (4 * n) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  refine lt_irrefl ((4 ^ n) ^ 6) ?_
  calc (4 ^ n) ^ 6
      < (n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)
          * (2 * n) ^ (bertrandPrimes n).card)) ^ 6 := Nat.pow_lt_pow_left herdos (by norm_num)
    _ = (n ^ 6 * (2 * n) ^ (6 * Nat.sqrt (2 * n))) * 4 ^ (6 * (2 * n / 3))
          * ((2 * n) ^ (2 * (bertrandPrimes n).card)) ^ 3 := by ring
    _ ≤ 2 ^ n * 4 ^ (4 * n) * (2 ^ n) ^ 3 := by gcongr
    _ = (4 ^ n) ^ 6 := by
        rw [mul_comm 4 n, pow_mul 4 n 4, show (4 : ℕ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; rfl]
        ring

/-- The count of step 3 with natural logarithms: `n log 2 ≤ 2 k log (2n)`. -/
private theorem mul_log_two_le_card_bertrandPrimes_mul_log {n : ℕ} (hn : 16562 ≤ n) :
    (n : ℝ) * Real.log 2 ≤ 2 * (bertrandPrimes n).card * Real.log (2 * n) := by
  have hpow : (2 : ℝ) ^ n ≤ (2 * (n : ℝ)) ^ (2 * (bertrandPrimes n).card) := by
    exact_mod_cast two_pow_le_of_large hn
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  exact_mod_cast hlog

/-! ## 4. Half-open windows `[x/2, x)` with real endpoints -/

/-- For a real `x ≥ 4` the natural number `n = ⌈x/2⌉ - 1`, written below as `(⌈x⌉ - 1) / 2`,
satisfies `n ≥ 1`, `n ≥ x/4` and `2n < x`, and every natural number in `(n, 2n]` lies in `[x/2, x)`.
-/
private theorem exists_nat_window {x : ℝ} (hx : 4 ≤ x) :
    ∃ n : ℕ, 1 ≤ n ∧ x / 4 ≤ (n : ℝ) ∧ 2 * (n : ℝ) < x ∧
      ∀ p : ℕ, n < p → p ≤ 2 * n → x / 2 ≤ (p : ℝ) ∧ (p : ℝ) < x := by
  have hle : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hlt : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have hceil : 4 ≤ ⌈x⌉₊ := by exact_mod_cast hx.trans hle
  obtain ⟨n, hn⟩ : ∃ n, n = (⌈x⌉₊ - 1) / 2 := ⟨_, rfl⟩
  have hlow : (⌈x⌉₊ : ℝ) ≤ 2 * n + 2 := by exact_mod_cast (by omega : ⌈x⌉₊ ≤ 2 * n + 2)
  have hhigh : (2 * n + 1 : ℝ) ≤ (⌈x⌉₊ : ℝ) := by exact_mod_cast (by omega : 2 * n + 1 ≤ ⌈x⌉₊)
  refine ⟨n, by omega, by linarith, by linarith, fun p hnp hp2n => ?_⟩
  have hnp' : (n : ℝ) + 1 ≤ p := by exact_mod_cast hnp
  have hp2n' : (p : ℝ) ≤ 2 * n := by exact_mod_cast hp2n
  exact ⟨by linarith, by linarith⟩

/-- For every real `x ≥ 4` there is a prime `p` with `x/2 ≤ p < x`, by Bertrand's postulate. -/
theorem exists_prime_half_le_and_lt (x : ℝ) (hx : 4 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x / 2 ≤ (p : ℝ) ∧ (p : ℝ) < x := by
  obtain ⟨n, hn1, -, -, hwindow⟩ := exists_nat_window hx
  obtain ⟨p, hprime, hnp, hp2n⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  exact ⟨p, hprime, hwindow p hnp hp2n⟩

/-- If `(n, 2n]` lies in the window and `n ≥ x/4` is large, the window has at least `x / (12 log x)`
primes: `(x/4) log 2 ≤ n log 2 ≤ 2 k log (2n) ≤ 2 k log x`, and `log 2 ≥ 2/3`. -/
private theorem div_log_le_card_of_large {x : ℝ} {n : ℕ} {S : Finset ℕ} (hx : 4 ≤ x)
    (hn : 16562 ≤ n) (hn4 : x / 4 ≤ (n : ℝ)) (h2n : 2 * (n : ℝ) < x) (hsub : bertrandPrimes n ⊆ S) :
    x / (12 * Real.log x) ≤ (S.card : ℝ) := by
  have hcard : ((bertrandPrimes n).card : ℝ) ≤ S.card := by exact_mod_cast card_le_card hsub
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : Real.log (2 * n) ≤ Real.log x := Real.log_le_log (by linarith) h2n.le
  have hlog0 : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith)
  have hlog2 : 2 / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [div_le_iff₀ (mul_pos (by norm_num) (Real.log_pos (by linarith)))]
  calc x = 6 * (x / 4 * (2 / 3)) := by ring
    _ ≤ 6 * (n * Real.log 2) := by gcongr
    _ ≤ 6 * (2 * (bertrandPrimes n).card * Real.log (2 * n)) :=
        mul_le_mul_of_nonneg_left (mul_log_two_le_card_bertrandPrimes_mul_log hn) (by norm_num)
    _ ≤ 6 * (2 * S.card * Real.log x) := by gcongr
    _ = S.card * (12 * Real.log x) := by ring

/-- There is a `c > 0` such that, for every real `x ≥ 4`, every finite set of natural numbers that
contains all primes `p` with `x/2 ≤ p < x` has at least `c · x / log x` elements.  (This form
applies to the set of those primes however it is written down.) -/
theorem exists_forall_mul_div_log_le_card_primes :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 4 ≤ x → ∀ S : Finset ℕ,
      (∀ p : ℕ, p.Prime → x / 2 ≤ (p : ℝ) → (p : ℝ) < x → p ∈ S) →
      c * (x / Real.log x) ≤ (S.card : ℝ) := by
  -- `66248 = 4 · 16562`: for `x` below it one prime is enough
  refine ⟨1 / 66248, by norm_num, fun x hx S hS => ?_⟩
  obtain ⟨n, hn1, hn4, h2n, hwindow⟩ := exists_nat_window hx
  have hlogx : 1 ≤ Real.log x := Real.one_le_log_of_three_le (by linarith)
  rcases le_or_gt 16562 n with hlarge | hsmall
  · -- The primes of `(n, 2n]` lie in the window.
    have hsub : bertrandPrimes n ⊆ S := fun p hp => by
      obtain ⟨⟨hnp, hp2n⟩, hprime⟩ := mem_bertrandPrimes.1 hp
      exact hS p hprime (hwindow p hnp hp2n).1 (hwindow p hnp hp2n).2
    calc 1 / 66248 * (x / Real.log x) ≤ 1 / 12 * (x / Real.log x) := by gcongr; norm_num
      _ = x / (12 * Real.log x) := by field_simp
      _ ≤ (S.card : ℝ) := div_log_le_card_of_large hx hlarge hn4 h2n hsub
  · -- Here `x ≤ 4n < 66248`, and one prime is enough.
    obtain ⟨p, hprime, hlow, hhigh⟩ := exists_prime_half_le_and_lt x hx
    have hone : (1 : ℝ) ≤ S.card := by
      exact_mod_cast Finset.card_pos.mpr ⟨p, hS p hprime hlow hhigh⟩
    have hn : (n : ℝ) ≤ 16562 := by exact_mod_cast hsmall.le
    calc 1 / 66248 * (x / Real.log x) ≤ 1 / 66248 * (x / 1) := by gcongr
      _ ≤ 1 := by linarith
      _ ≤ (S.card : ℝ) := hone

/-! ## 5. The window `[√D/2, √D)` of the proof of Theorem 17 -/

/-- Proof of Theorem 17: "there are Ω(√D / log D) primes in the range".  There is a `c > 0` such
that, for every natural number `D ≥ 16`, every finite set of natural numbers that contains all
primes `p` with `√D/2 ≤ p < √D` has at least `c · √D / log D` elements. -/
theorem exists_forall_mul_sqrt_div_log_le_card_primes :
    ∃ c : ℝ, 0 < c ∧ ∀ D : ℕ, 16 ≤ D → ∀ S : Finset ℕ,
      (∀ p : ℕ, p.Prime → √D / 2 ≤ (p : ℝ) → (p : ℝ) < √D → p ∈ S) →
      c * (√D / Real.log D) ≤ (S.card : ℝ) := by
  obtain ⟨c, hc, hcount⟩ := exists_forall_mul_div_log_le_card_primes
  refine ⟨c, hc, fun D hD S hS => ?_⟩
  have hlog : 0 < Real.log D := Real.log_pos (by exact_mod_cast (by omega : 1 < D))
  calc c * (√D / Real.log D) ≤ c * (√D / (Real.log D / 2)) := by
        gcongr
        linarith
    _ = c * (√D / Real.log (√D)) := by rw [Real.log_sqrt (Nat.cast_nonneg D)]
    _ ≤ (S.card : ℝ) := hcount _ (Real.four_le_sqrt_natCast_of_sixteen_le hD) S hS

end Nat
