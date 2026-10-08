/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec3.Theorem21a.ChanHe.Definitions
public import ThreeSumApsp.Util.Average
public import ThreeSumApsp.Util.PrimeCounting
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Theorem 21(a), the reduction of Chan and He: the choice of the modulus

For Theorem 21(a): the deterministic reduction from 3SUM to
Convolution-3SUM after [CH20, Theorem 5.1] hashes the numbers by `x ↦ x mod pq`, for two primes
`p` and `q` that it finds by exhaustive search among the primes up to `m = mPar n U`.  This file
shows that both searches succeed and that few elements are badly hashed.

* An ordered pair of distinct elements of a set `S` collides modulo `M` if `M` divides their
  difference; `coll S M` counts these ordered pairs.  An element that collides with another one is
  heavy.  There are at most as many heavy elements as colliding pairs (`card_heavy_le_coll`).  The
  count is determined by the sizes of the residue classes (`coll_eq_sum`); the proofs below do not
  need this, a program that computes the count does.
* A nonzero difference has at most `Λ = Lam U` prime divisors.  So, summed over the candidates `q`
  in the set `Q` of primes that a search goes through, the pairs that collide modulo `M₀ q` number
  at most `Λ` times those that collide modulo `M₀` (`sum_coll_mul_le`).
* By counting (the finite form of Markov's inequality and of the union bound, which [CH20] uses),
  some candidate is, for each of the three sets, at most three times as bad as the average
  (`Finset.exists_forall_mul_card_le_mul_sum`, `exists_prime_coll_le`). So both searches succeed
  (`firstP_spec`, `secondP_spec`), and the modulus `pq` leaves at most `9Λ²|S|²/|Q|²` colliding
  pairs in each set `S` (`modulus_spec`).
* There are at least `wPar n U` primes up to `mPar n U` (`wPar_le_card_primesLE`, from the bound
  `2^m ≤ (m + 1) lcm(1, …, m)` of Mathlib).  With that many candidates a set `S` has at most
  `|S|²/(2n)` heavy elements (`card_heavy_modulus_le`, `le_card_primesLE_mPar_sq`).
-/

public section

namespace ThreeSumApsp

namespace ChanHe

open Finset

/-! ## Colliding pairs and heavy elements -/

/-- Two integers are congruent modulo `M` iff they have the same remainder. -/
theorem natCast_dvd_sub_iff_emod_eq (M : ℕ) (x y : ℤ) :
    (M : ℤ) ∣ x - y ↔ x % (M : ℤ) = y % (M : ℤ) :=
  Int.modEq_iff_dvd.symm.trans eq_comm

/-- Each heavy element is the first component of a colliding pair. -/
theorem card_heavy_le_coll (S : Finset ℤ) (M : ℕ) : #(heavy S M) ≤ coll S M := by
  refine (card_le_card fun x hx => ?_).trans (card_image_le (f := Prod.fst))
  obtain ⟨hxS, y, hyS, hne, hd⟩ := mem_filter.mp hx
  exact mem_image.mpr ⟨(x, y), mem_filter.mpr ⟨mem_offDiag.mpr ⟨hxS, hyS, hne.symm⟩, hd⟩, rfl⟩

/-- There are at most `|S|²` colliding ordered pairs. -/
theorem coll_le_sq (S : Finset ℤ) (M : ℕ) : coll S M ≤ #S ^ 2 :=
  calc coll S M ≤ #S.offDiag := card_filter_le _ _
    _ = #S * #S - #S := offDiag_card S
    _ ≤ #S ^ 2 := by rw [sq]; omega

/-- The collision count is determined by the sizes of the buckets: an element collides with the
other members of its bucket. -/
theorem coll_eq_sum (S : Finset ℤ) (M : ℕ) :
    coll S M = ∑ x ∈ S, (#(bucket S M (x % (M : ℤ))) - 1) := by
  have hfiber : ∀ x ∈ S,
      #(bucket S M (x % (M : ℤ))) - 1 = #{y ∈ S | x ≠ y ∧ (M : ℤ) ∣ x - y} := by
    intro x hx
    rw [← card_erase_of_mem (show x ∈ bucket S M (x % (M : ℤ)) from mem_filter.mpr ⟨hx, rfl⟩)]
    congr 1
    ext y
    simp only [bucket, mem_filter, mem_erase, natCast_dvd_sub_iff_emod_eq, ne_comm (a := x),
      eq_comm (a := x % _)]
    tauto
  have hpairs : {p ∈ S.offDiag | (M : ℤ) ∣ p.1 - p.2} =
      {p ∈ S ×ˢ S | p.1 ≠ p.2 ∧ (M : ℤ) ∣ p.1 - p.2} := by
    ext p
    simp only [mem_filter, mem_offDiag, mem_product, and_assoc]
  rw [sum_congr rfl hfiber, coll, hpairs, card_filter, sum_product]
  simp only [card_filter]

/-- `Lam U` is at least 1. -/
private theorem Lam_pos (U : ℕ) : 1 ≤ Lam U := Nat.succ_pos _

/-- A nonzero integer of absolute value at most `2U` is divisible by at most `Lam U` primes,
because their product divides it. -/
private theorem card_prime_divisors_le {Q : Finset ℕ} (hP : ∀ p ∈ Q, p.Prime) {U : ℕ} {d : ℤ}
    (hd : d ≠ 0) (hb : |d| ≤ 2 * (U : ℤ)) : #{p ∈ Q | ((p : ℕ) : ℤ) ∣ d} ≤ Lam U := by
  set T := {p ∈ Q | ((p : ℕ) : ℤ) ∣ d}
  have hprime : ∀ p ∈ T, p.Prime := fun p hp => hP p (mem_filter.mp hp).1
  have hsub : T ⊆ d.natAbs.primeFactors := fun p hp => Nat.mem_primeFactors.mpr
    ⟨hprime p hp, Int.natCast_dvd.mp (mem_filter.mp hp).2, Int.natAbs_ne_zero.mpr hd⟩
  have hpow : 2 ^ #T ≤ 2 * U :=
    calc 2 ^ #T ≤ ∏ p ∈ T, p := pow_card_le_prod _ _ _ fun p hp => (hprime p hp).two_le
      _ ≤ d.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hd)
          ((prod_dvd_prod_of_subset _ _ _ hsub).trans (Nat.prod_primeFactors_dvd _))
      _ ≤ 2 * U := by have := abs_le.mp hb; omega
  exact (Nat.le_log_of_pow_le (by norm_num) hpow).trans (Nat.le_succ _)

/-- Double counting.  Summed over the candidates `q ∈ Q`, the pairs that collide modulo `M₀ q`
number at most `Lam U` times those that collide modulo `M₀`: such a pair collides modulo `M₀`, and
`q` divides its difference.  Coprimality of `q` and `M₀` is not used, so the two primes of a modulus
are allowed to coincide. -/
theorem sum_coll_mul_le {Q : Finset ℕ} (hP : ∀ p ∈ Q, p.Prime) {U : ℕ} {S : Finset ℤ}
    (hS : Bdd U S) (M₀ : ℕ) : ∑ q ∈ Q, coll S (M₀ * q) ≤ Lam U * coll S M₀ := by
  set C := {xy ∈ S.offDiag | (M₀ : ℤ) ∣ xy.1 - xy.2}
  calc ∑ q ∈ Q, coll S (M₀ * q)
      ≤ ∑ q ∈ Q, #{xy ∈ C | (q : ℤ) ∣ xy.1 - xy.2} := by
        refine sum_le_sum fun q _ => card_le_card fun xy h => ?_
        obtain ⟨hxy, hd⟩ := mem_filter.mp h
        rw [Nat.cast_mul] at hd
        exact mem_filter.mpr
          ⟨mem_filter.mpr ⟨hxy, dvd_of_mul_right_dvd hd⟩, dvd_of_mul_left_dvd hd⟩
    _ = ∑ xy ∈ C, #{q ∈ Q | ((q : ℕ) : ℤ) ∣ xy.1 - xy.2} :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
    _ ≤ ∑ _xy ∈ C, Lam U := by
        refine sum_le_sum fun xy h => ?_
        obtain ⟨hx, hy, hne⟩ := mem_offDiag.mp (mem_filter.mp h).1
        exact card_prime_divisors_le hP (sub_ne_zero.mpr hne)
          ((abs_sub _ _).trans (by linarith [hS _ hx, hS _ hy]))
    _ = Lam U * coll S M₀ := by rw [sum_const, smul_eq_mul, mul_comm, coll]

/-! ## The two searches succeed -/

section searches

variable {Q : Finset ℕ} {U : ℕ} {S₁ S₂ S₃ : Finset ℤ}

/-- On a nonempty set, `pick` returns a member. -/
private theorem pick_mem {T : Finset ℕ} (h : T.Nonempty) : pick T ∈ T := by
  rw [pick, dif_pos h]
  exact T.min'_mem h

/-- Some candidate `q` is good for the three sets at once: in each of them at most the fraction
`3Λ/|Q|` of the pairs that collide modulo `M₀` still collide modulo `M₀ q`. -/
private theorem exists_prime_coll_le (hQ : Q.Nonempty) (hP : ∀ p ∈ Q, p.Prime) (h₁ : Bdd U S₁)
    (h₂ : Bdd U S₂) (h₃ : Bdd U S₃) (M₀ : ℕ) :
    ∃ q ∈ Q, coll S₁ (M₀ * q) * #Q ≤ 3 * Lam U * coll S₁ M₀ ∧
      coll S₂ (M₀ * q) * #Q ≤ 3 * Lam U * coll S₂ M₀ ∧
      coll S₃ (M₀ * q) * #Q ≤ 3 * Lam U * coll S₃ M₀ := by
  obtain ⟨q, hq, hgood⟩ :=
    Finset.exists_forall_mul_card_le_mul_sum hQ 3 fun i q => coll (![S₁, S₂, S₃] i) (M₀ * q)
  have havg : ∀ {S : Finset ℤ}, Bdd U S →
      3 * ∑ q' ∈ Q, coll S (M₀ * q') ≤ 3 * Lam U * coll S M₀ := fun hS => by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (sum_coll_mul_le hP hS M₀)
  exact ⟨q, hq, (hgood 0).trans (havg h₁), (hgood 1).trans (havg h₂), (hgood 2).trans (havg h₃)⟩

/-- The first search succeeds: `firstP` lies in `Q` and passes its three tests. -/
theorem firstP_spec (hQ : Q.Nonempty) (hP : ∀ p ∈ Q, p.Prime) (h₁ : Bdd U S₁) (h₂ : Bdd U S₂)
    (h₃ : Bdd U S₃) :
    firstP Q (Lam U) S₁ S₂ S₃ ∈ {p ∈ Q | coll S₁ p * #Q ≤ 3 * Lam U * #S₁ ^ 2 ∧
      coll S₂ p * #Q ≤ 3 * Lam U * #S₂ ^ 2 ∧ coll S₃ p * #Q ≤ 3 * Lam U * #S₃ ^ 2} := by
  obtain ⟨p, hp, c₁, c₂, c₃⟩ := exists_prime_coll_le hQ hP h₁ h₂ h₃ 1
  rw [one_mul] at c₁ c₂ c₃
  have hall : ∀ S : Finset ℤ, 3 * Lam U * coll S 1 ≤ 3 * Lam U * #S ^ 2 :=
    fun S => Nat.mul_le_mul_left _ (coll_le_sq S 1)
  exact pick_mem
    ⟨p, mem_filter.mpr ⟨hp, c₁.trans (hall S₁), c₂.trans (hall S₂), c₃.trans (hall S₃)⟩⟩

/-- The second search succeeds, for any first factor `p`. -/
theorem secondP_spec (hQ : Q.Nonempty) (hP : ∀ p ∈ Q, p.Prime) (h₁ : Bdd U S₁) (h₂ : Bdd U S₂)
    (h₃ : Bdd U S₃) (p : ℕ) :
    secondP Q (Lam U) S₁ S₂ S₃ p ∈ {q ∈ Q | coll S₁ (p * q) * #Q ≤ 3 * Lam U * coll S₁ p ∧
      coll S₂ (p * q) * #Q ≤ 3 * Lam U * coll S₂ p ∧
      coll S₃ (p * q) * #Q ≤ 3 * Lam U * coll S₃ p} := by
  obtain ⟨q, hq, hc⟩ := exists_prime_coll_le hQ hP h₁ h₂ h₃ p
  exact pick_mem ⟨q, mem_filter.mpr ⟨hq, hc⟩⟩

/-- Both searches succeed, and the modulus leaves at most `9Λ²|S|²/|Q|²` colliding pairs in each of
the three sets.  (A search that fails returns 1, which is not in `Q`.) -/
theorem modulus_spec (hQ : Q.Nonempty) (hP : ∀ p ∈ Q, p.Prime) (h₁ : Bdd U S₁) (h₂ : Bdd U S₂)
    (h₃ : Bdd U S₃) :
    firstP Q (Lam U) S₁ S₂ S₃ ∈ Q ∧ secondP Q (Lam U) S₁ S₂ S₃ (firstP Q (Lam U) S₁ S₂ S₃) ∈ Q ∧
    ∀ S ∈ [S₁, S₂, S₃], coll S (modulus Q (Lam U) S₁ S₂ S₃) * #Q ^ 2 ≤ 9 * Lam U ^ 2 * #S ^ 2 := by
  obtain ⟨hp, p₁, p₂, p₃⟩ := mem_filter.mp (firstP_spec hQ hP h₁ h₂ h₃)
  obtain ⟨hq, q₁, q₂, q₃⟩ :=
    mem_filter.mp (secondP_spec hQ hP h₁ h₂ h₃ (firstP Q (Lam U) S₁ S₂ S₃))
  -- the two tests multiply: `c` counts collisions modulo `pq`, `c'` modulo `p`, and `s = |S|`
  have hmul : ∀ {c c' s : ℕ}, c' * #Q ≤ 3 * Lam U * s ^ 2 → c * #Q ≤ 3 * Lam U * c' →
      c * #Q ^ 2 ≤ 9 * Lam U ^ 2 * s ^ 2 := fun {c c' s} hfirst hsecond =>
    calc c * #Q ^ 2 = c * #Q * #Q := by ring
      _ ≤ 3 * Lam U * c' * #Q := Nat.mul_le_mul_right _ hsecond
      _ = 3 * Lam U * (c' * #Q) := by ring
      _ ≤ 3 * Lam U * (3 * Lam U * s ^ 2) := Nat.mul_le_mul_left _ hfirst
      _ = 9 * Lam U ^ 2 * s ^ 2 := by ring
  refine ⟨hp, hq, fun S hS => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl
  · exact hmul p₁ q₁
  · exact hmul p₂ q₂
  · exact hmul p₃ q₃

/-- The modulus lies between 1 and `m²` when all primes in `Q` are at most `m`. -/
theorem modulus_bounds (hQ : Q.Nonempty) (hP : ∀ p ∈ Q, p.Prime) {m : ℕ} (hm : ∀ p ∈ Q, p ≤ m)
    (h₁ : Bdd U S₁) (h₂ : Bdd U S₂) (h₃ : Bdd U S₃) :
    1 ≤ modulus Q (Lam U) S₁ S₂ S₃ ∧ modulus Q (Lam U) S₁ S₂ S₃ ≤ m ^ 2 := by
  obtain ⟨hp, hq, -⟩ := modulus_spec hQ hP h₁ h₂ h₃
  exact ⟨Nat.mul_pos (hP _ hp).pos (hP _ hq).pos, sq m ▸ Nat.mul_le_mul (hm _ hp) (hm _ hq)⟩

/-- The hypothesis of `card_heavy_modulus_le` on the number of candidates implies that there is
one. -/
theorem nonempty_of_le_card_sq {n : ℕ} (hbig : 18 * Lam U ^ 2 * n ≤ #Q ^ 2) (hn : 1 ≤ n) :
    Q.Nonempty := by
  have hpos : 0 < 18 * Lam U ^ 2 * n := by have := Lam_pos U; positivity
  exact card_pos.mp ((pow_pos_iff two_ne_zero).mp (hpos.trans_le hbig))

/-- With at least `√(18n) Λ` primes to choose from, each of the three sets `S` has at most
`|S|²/(2n)` heavy elements.  This is why the sizes of the sets fall doubly exponentially along the
recursion. -/
theorem card_heavy_modulus_le (hP : ∀ p ∈ Q, p.Prime) {n : ℕ}
    (hbig : 18 * Lam U ^ 2 * n ≤ #Q ^ 2) (hn : 1 ≤ n) (h₁ : Bdd U S₁) (h₂ : Bdd U S₂)
    (h₃ : Bdd U S₃) :
    ∀ S ∈ [S₁, S₂, S₃], 2 * n * #(heavy S (modulus Q (Lam U) S₁ S₂ S₃)) ≤ #S ^ 2 := by
  intro S hS
  obtain ⟨-, -, hcoll⟩ := modulus_spec (nonempty_of_le_card_sq hbig hn) hP h₁ h₂ h₃
  set M := modulus Q (Lam U) S₁ S₂ S₃
  have hΛ : 0 < 9 * Lam U ^ 2 := by have := Lam_pos U; positivity
  refine Nat.le_of_mul_le_mul_left ?_ hΛ
  calc 9 * Lam U ^ 2 * (2 * n * #(heavy S M))
      ≤ 9 * Lam U ^ 2 * (2 * n * coll S M) := by gcongr; exact card_heavy_le_coll S M
    _ = coll S M * (18 * Lam U ^ 2 * n) := by ring
    _ ≤ coll S M * #Q ^ 2 := Nat.mul_le_mul_left _ hbig
    _ ≤ 9 * Lam U ^ 2 * #S ^ 2 := hcoll S hS

end searches

/-! ## Enough primes -/

/-- There are at least `wPar n U` primes up to `mPar n U`. -/
theorem wPar_le_card_primesLE (n U : ℕ) : wPar n U ≤ #(Nat.primesLE (mPar n U)) :=
  Nat.le_card_primesLE_mul_log _

/-- The primes up to `mPar n U` are enough for `card_heavy_modulus_le`. -/
theorem le_card_primesLE_mPar_sq (n U : ℕ) : 18 * Lam U ^ 2 * n ≤ #(Nat.primesLE (mPar n U)) ^ 2 :=
  calc 18 * Lam U ^ 2 * n ≤ 25 * Lam U ^ 2 * ((Nat.sqrt n + 1) * (Nat.sqrt n + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (by norm_num)) (Nat.lt_succ_sqrt n).le
    _ = wPar n U ^ 2 := by unfold wPar; ring
    _ ≤ #(Nat.primesLE (mPar n U)) ^ 2 := Nat.pow_le_pow_left (wPar_le_card_primesLE n U) 2

end ChanHe

end ThreeSumApsp
