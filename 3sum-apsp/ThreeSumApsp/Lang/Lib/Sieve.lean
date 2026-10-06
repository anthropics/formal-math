/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Seg
public import ThreeSumApsp.Lang.Tactics
public import Mathlib.NumberTheory.PrimeCounting

/-!
# The sieve of Eratosthenes

sieve(m, out, fr) writes the primes up to m in ascending order to the cells from out and returns
their number (`sieve_meets`).  It uses a table of m + 1 cells at the free pointer fr, about which
nothing is assumed.

* The table is cleared (`clear_ends`).
* The candidates i = 2, …, m are tried in turn (`round_ends`).  Before the round for i, cell fr + j
  holds 0 unless j is a proper multiple of a prime below i (`Sieved`, `Marked`); so i is a prime if
  and only if cell fr + i holds 0 (`prime_iff_not_marked`).
* A prime is appended to the list, and its proper multiples are marked (`take_ends`, `mark_ends`).

The number of steps, `sieveTime m`, is of the order m log m: a prime i costs m / i rounds of
marking, and the sum of m / i over all i ≤ m is at most m (⌊log₂ m⌋ + 1) (`sum_div_le`, `time_le`).

Everything but `sieveBody`, `sieveTime` and `sieve_meets` is in the namespace `Sieve`.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Sieve

/-! ## The pure side -/

/-- The primes below c in ascending order. -/
def primesBelow (c : ℕ) : List ℕ := (List.range c).filter fun q => q.Prime

theorem primesBelow_two : primesBelow 2 = [] := by decide

theorem primesBelow_one : primesBelow 1 = [] := by decide

theorem primesBelow_succ_of_prime {c : ℕ} (h : c.Prime) :
    primesBelow (c + 1) = primesBelow c ++ [c] := by
  simp [primesBelow, List.range_succ, List.filter_append, h]

theorem primesBelow_succ_of_not_prime {c : ℕ} (h : ¬ c.Prime) :
    primesBelow (c + 1) = primesBelow c := by
  simp [primesBelow, List.range_succ, List.filter_append, h]

/-- There are at most i - 2 primes below i. -/
theorem length_primesBelow_add_two_le {i : ℕ} (hi : 2 ≤ i) : (primesBelow i).length + 2 ≤ i := by
  induction i, hi using Nat.le_induction with
  | base => simp [primesBelow_two]
  | succ i _ ih =>
    by_cases h : i.Prime
    · rw [primesBelow_succ_of_prime h]
      simpa using ih
    · rw [primesBelow_succ_of_not_prime h]
      omega

/-- The list is the sorted list of the set of primes up to m. -/
theorem sort_primesLE (m : ℕ) : (Nat.primesLE m).sort (· ≤ ·) = primesBelow (m + 1) := by
  refine List.Perm.eq_of_pairwise' (Finset.pairwise_sort _ _) ?_ ?_
  · exact (List.pairwise_le_range).filter _
  · refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) (List.nodup_range.filter _)).2
      fun q => ?_
    simp [Nat.mem_primesLE]

theorem length_primesBelow (m : ℕ) : (primesBelow (m + 1)).length = (Nat.primesLE m).card := by
  rw [← sort_primesLE, Finset.length_sort]

/-- The number j is a proper multiple of a prime below c. -/
def Marked (c j : ℕ) : Prop := ∃ p, p.Prime ∧ p < c ∧ p ∣ j ∧ p < j

theorem not_marked_two (j : ℕ) : ¬ Marked 2 j := by
  rintro ⟨p, hp, h2, -, -⟩
  exact absurd hp.two_le (by omega)

/-- A number from 2 on is prime if and only if it is not a proper multiple of a smaller prime. -/
theorem prime_iff_not_marked {i : ℕ} (hi : 2 ≤ i) : i.Prime ↔ ¬ Marked i i := by
  constructor
  · rintro h ⟨p, hp, hlt, hdvd, -⟩
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp h).1 hdvd) (by omega)
  · intro h
    by_contra hn
    have hlt := (Nat.not_prime_iff_minFac_lt hi).1 hn
    exact h ⟨i.minFac, Nat.minFac_prime (by omega), hlt, Nat.minFac_dvd i, hlt⟩

theorem marked_succ_of_not_prime {i : ℕ} (h : ¬ i.Prime) (j : ℕ) :
    Marked (i + 1) j ↔ Marked i j := by
  constructor
  · rintro ⟨p, hp, hlt, h1, h2⟩
    have : p ≠ i := by
      rintro rfl
      exact h hp
    exact ⟨p, hp, by omega, h1, h2⟩
  · rintro ⟨p, hp, hlt, h1, h2⟩
    exact ⟨p, hp, by omega, h1, h2⟩

theorem marked_succ_of_prime {i : ℕ} (h : i.Prime) (j : ℕ) :
    Marked (i + 1) j ↔ Marked i j ∨ (i ∣ j ∧ i < j) := by
  constructor
  · rintro ⟨p, hp, hlt, h1, h2⟩
    by_cases hpi : p = i
    · subst hpi
      exact Or.inr ⟨h1, h2⟩
    · exact Or.inl ⟨p, hp, by omega, h1, h2⟩
  · rintro (⟨p, hp, hlt, h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨p, hp, by omega, h1, h2⟩
    · exact ⟨i, h, by omega, h1, h2⟩

/-- The sum of m / i over 1 ≤ i < 2^k is at most k m. -/
theorem sum_div_pow_le (m k : ℕ) : ∑ r ∈ Finset.range (2 ^ k - 1), m / (r + 1) ≤ k * m := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : 2 ^ (k + 1) - 1 = (2 ^ k - 1) + 2 ^ k := by
      have := Nat.one_le_two_pow (n := k)
      rw [pow_succ]
      omega
    rw [h2, Finset.sum_range_add]
    have hblock : ∑ x ∈ Finset.range (2 ^ k), m / (2 ^ k - 1 + x + 1) ≤ m := by
      calc ∑ x ∈ Finset.range (2 ^ k), m / (2 ^ k - 1 + x + 1)
          ≤ ∑ _x ∈ Finset.range (2 ^ k), m / 2 ^ k := by
            refine Finset.sum_le_sum fun x _ => Nat.div_le_div_left ?_ (by positivity)
            have := Nat.one_le_two_pow (n := k)
            omega
        _ = 2 ^ k * (m / 2 ^ k) := by simp
        _ ≤ m := Nat.mul_div_le m _
    have : (k + 1) * m = k * m + m := by ring
    omega

/-- The sum of m / i over 2 ≤ i ≤ m is at most m (⌊log₂ m⌋ + 1). -/
theorem sum_div_le (m : ℕ) : ∑ r ∈ Finset.range (m - 1), m / (r + 2) ≤ (Nat.log 2 m + 1) * m := by
  have h1 : ∑ r ∈ Finset.range (m - 1), m / (r + 2)
      ≤ ∑ r ∈ Finset.range (m - 1 + 1), m / (r + 1) := by
    rw [Finset.sum_range_succ']
    exact Nat.le_add_right _ _
  have h2 : ∑ r ∈ Finset.range (m - 1 + 1), m / (r + 1)
      ≤ ∑ r ∈ Finset.range (2 ^ (Nat.log 2 m + 1) - 1), m / (r + 1) := by
    refine Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 ?_)
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m
    have h3 : 2 ≤ 2 ^ (Nat.log 2 m + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (Nat.log 2 m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [Nat.succ_eq_add_one] at this
    omega
  exact h1.trans (h2.trans (sum_div_pow_le m _))

/-! ## The program -/

/-- The local variables of sieve: the arguments m, out and fr, the candidate i, a multiple J of i,
and the number cnt of primes found. -/
abbrev Bound : ℕ := 0
@[inherit_doc Bound] abbrev Dest : ℕ := 1
@[inherit_doc Bound] abbrev Table : ℕ := 2
@[inherit_doc Bound] abbrev Cand : ℕ := 3
@[inherit_doc Bound] abbrev Mult : ℕ := 4
@[inherit_doc Bound] abbrev Count : ℕ := 5

/-- Clearing the table: the cells fr, …, fr + m become 0. -/
def clear : Stmt :=
  .set Cand (k 0) ;;
  .while (v Cand ≤' v Bound) (
    .store (v Table +' v Cand) (k 0) ;;
    .set Cand (v Cand +' k 1))

/-- Marking the proper multiples 2 i, 3 i, … of i. -/
def mark : Stmt :=
  .while (v Mult ≤' v Bound) (
    .store (v Table +' v Mult) (k 1) ;;
    .set Mult (v Mult +' v Cand))

/-- The candidate i is a prime: it is appended to the list, and its proper multiples are marked. -/
def take : Stmt :=
  .store (v Dest +' v Count) (v Cand) ;;
  .set Count (v Count +' k 1) ;;
  .set Mult (v Cand +' v Cand) ;;
  mark

/-- The round for the candidate i, which is a prime if its cell of the table holds 0. -/
def round : Stmt :=
  .ite (M (v Table +' v Cand) =' k 0) take .skip ;;
  .set Cand (v Cand +' k 1)

/-- sieve(m, out, fr). -/
def _root_.Light.sieveBody : Stmt :=
  clear ;;
  .set Cand (k 2) ;;
  .set Count (k 0) ;;
  .while (v Cand ≤' v Bound) round ;;
  .set Bound (v Count)

/-- The time of sieve. -/
def _root_.Light.sieveTime (m : ℕ) : ℕ := 15 * m * (Nat.log 2 m + 5) + 35

variable {μ : ℕ → ℤ} {m out fr : ℕ}

/-- What sieve asks of the limits and of its arguments: an address fits in a word, and so does
2 m + 2; the m cells from out lie before the table; the table lies within the memory. -/
structure Pre (lim : Limits) (m out fr : ℕ) : Prop where
  space : (lim.space : ℤ) ≤ lim.word
  word : ((2 * m + 2 : ℕ) : ℤ) ≤ lim.word
  out : out + m ≤ fr
  free : fr + (m + 1) ≤ lim.space

/-- The number of steps of the main loop: 6 for each test, 15 (m / i) + 30 for the candidate i. -/
def loopTime (m : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (m - 1), (5 + 1 + (15 * (m / (r + 2)) + 30)) + (5 + 1)

/-- Clearing the table, two assignments, the main loop and the last assignment. -/
theorem time_le (m : ℕ) : 15 * m + 23 + 4 + loopTime m + 2 ≤ sieveTime m := by
  have hsum := sum_div_le m
  have hmul : 15 * m * (Nat.log 2 m + 5) = 15 * ((Nat.log 2 m + 1) * m) + 60 * m := by ring
  simp only [loopTime, sieveTime, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul, ← Finset.mul_sum]
  omega

/-- The first j cells of the table have been cleared, and no cell outside the table has changed. -/
def Cleared (μ : ℕ → ℤ) (m out fr j : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ, σ = ⟨frame [m, out, fr, j], μ'⟩ ∧ (∀ i < j, μ' (fr + i) = 0) ∧
    SameOutside μ μ' fr (m + 1)

/-- The table is cleared. -/
theorem clear_ends (pre : Pre lim m out fr) :
    Ends lim P d clear ⟨frame [m, out, fr], μ⟩ (15 * m + 23) (Cleared μ m out fr (m + 1)) := by
  light_facts pre
  -- i := 0
  light_set (0 : ℕ)
  -- while i ≤ m
  refine Ends.whileBlock (Cleared μ m out fr) (m + 1) ?start ?round ?done
  case start => exact ⟨μ, rfl, fun i hi => absurd hi (by omega), .refl⟩
  case done =>
    rintro _ ⟨μ', rfl, hzero, same⟩
    exact ⟨by light_side, by light_side, μ', rfl, hzero, same⟩
  case round =>
    rintro j _ hj ⟨μ', rfl, hzero, same⟩
    -- table[i] := 0; i := i + 1
    refine ⟨by light_side, by light_side, by light_side, Function.update μ' (fr + j) 0, ?_, ?_,
      same.update ⟨by omega, by omega⟩ _⟩
    · simp [update_frame_setLocal]
    · intro i hi
      by_cases h : i = j
      · simp [h]
      · rw [Function.update_of_ne (by omega)]
        exact hzero i (by omega)

/-- Among the multiples of i, those below J + i are those below J, and J itself. -/
theorem lt_add_iff_of_dvd {i j J : ℕ} (hJ : i ∣ J) (hj : i ∣ j) (hne : j ≠ J) : j < J + i ↔ j < J :=
  ⟨fun h => lt_of_le_of_ne (Nat.le_of_lt_add_of_dvd h hj hJ) hne, fun h => by omega⟩

/-- The proper multiples of i below J have been marked, J is the next one, and no other cell has
changed. -/
def Marking (μ : ℕ → ℤ) (m out fr i cnt J : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ, σ = ⟨frame [m, out, fr, i, J, cnt], μ'⟩ ∧
    (∀ j ≤ m, μ' (fr + j) = if i ∣ j ∧ i < j ∧ j < J then 1 else μ (fr + j)) ∧
    SameOutside μ μ' fr (m + 1)

/-- table[J] := 1; J := J + i. -/
theorem mark_round {i cnt J : ℕ} {σ : State} (pre : Pre lim m out fr) (hi : 1 ≤ i) (hJ : i ∣ J)
    (hiJ : i < J) (hJm : J ≤ m) (h : Marking μ m out fr i cnt J σ) :
    (Stmt.store (v Table +' v Mult) (k 1) ;; .set Mult (v Mult +' v Cand)).Runs lim σ
      (Marking μ m out fr i cnt (J + i)) := by
  light_facts pre
  obtain ⟨μ', rfl, htab, same⟩ := h
  refine ⟨by light_side, Function.update μ' (fr + J) 1, by simp [update_frame_setLocal], ?_,
    same.update ⟨by omega, by omega⟩ _⟩
  intro j hj
  by_cases hjJ : j = J
  · subst hjJ
    rw [Function.update_self, if_pos ⟨hJ, hiJ, by omega⟩]
  · rw [Function.update_of_ne (by omega), htab j hj]
    by_cases hdvd : i ∣ j
    · simp only [hdvd, true_and, lt_add_iff_of_dvd hJ hdvd hjJ]
    · simp only [hdvd, false_and]

/-- The proper multiples of i are marked, in m / i - 1 rounds. -/
theorem mark_ends {i cnt : ℕ} (pre : Pre lim m out fr) (hi : 1 ≤ i) (him : i ≤ m) :
    Ends lim P d mark ⟨frame [m, out, fr, i, (2 * i : ℕ), cnt], μ⟩ (15 * (m / i) + 6) fun σ' =>
      ∃ J, m < J ∧ Marking μ m out fr i cnt J σ' := by
  light_facts pre
  have hq : 1 ≤ m / i := (Nat.le_div_iff_mul_le hi).2 (by omega)
  -- while J ≤ m
  refine Ends.whileBlock (fun t => Marking μ m out fr i cnt ((t + 2) * i)) (m / i - 1) ?start ?round
    ?done (by light_time)
  case start =>
    refine ⟨μ, by simp, fun j _ => (if_neg ?_).symm, .refl⟩
    rintro ⟨hdvd, hlt, hlt2⟩
    exact absurd (Nat.le_of_lt_add_of_dvd (by omega : j < i + i) hdvd dvd_rfl) (by omega)
  case done =>
    rintro _ h
    have hgt : m < (m / i - 1 + 2) * i := by
      rw [show m / i - 1 + 2 = m / i + 1 by omega]
      exact (Nat.div_lt_iff_lt_mul hi).1 (Nat.lt_succ_self _)
    generalize (m / i - 1 + 2) * i = J at h hgt
    obtain ⟨μ', rfl, -⟩ := id h
    exact ⟨by light_side, by light_side, J, hgt, h⟩
  case round =>
    rintro t σ ht h
    have hle : (t + 2) * i ≤ m := (Nat.le_div_iff_mul_le hi).1 (by omega)
    have hlt : i < (t + 2) * i :=
      lt_of_lt_of_le (by omega : i < 2 * i) (Nat.mul_le_mul_right i (by omega))
    have hrun := mark_round pre hi (Dvd.intro_left _ rfl) hlt hle h
    rw [show (t + 2) * i + i = (t + 1 + 2) * i by ring] at hrun
    generalize (t + 2) * i = J at h hle
    obtain ⟨μ', rfl, -⟩ := h
    exact ⟨by light_side, by light_side, hrun⟩

/-- The candidate is i, and the numbers below c have been dealt with: the primes below c stand at
out, and their number is in the local Count; a cell of the table holds 0 unless its index is a
proper multiple of a prime below c; no cell outside the m cells from out and the table has
changed. -/
def Sieved (μ : ℕ → ℤ) (m out fr i c : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (J : ℕ), σ = ⟨frame [m, out, fr, i, J, (primesBelow c).length], μ'⟩ ∧
    SegN μ' out (primesBelow c) ∧ (∀ j ≤ m, μ' (fr + j) = 0 ↔ ¬ Marked c j) ∧
    SameOutside2 μ μ' out m fr (m + 1)

/-- A prime candidate is written to the list, and its proper multiples are marked. -/
theorem take_ends {i : ℕ} {σ : State} (pre : Pre lim m out fr) (him : i ≤ m) (hprime : i.Prime)
    (h : Sieved μ m out fr i i σ) :
    Ends lim P d take σ (15 * (m / i) + 19) (Sieved μ m out fr i (i + 1)) := by
  light_facts pre
  obtain ⟨μ', J, rfl, seg, htab, kept⟩ := h
  have hcnt := length_primesBelow_add_two_le hprime.two_le
  -- out[cnt] := i
  light_store (out + (primesBelow i).length) i
  -- cnt := cnt + 1
  light_set ((primesBelow i).length + 1 : ℕ)
  -- J := i + i
  light_set (2 * i : ℕ)
  -- the proper multiples of i
  light_piece (mark_ends pre hprime.one_le him) with _ ⟨J', hJ', μ'', rfl, htab', same⟩
  rw [Sieved, primesBelow_succ_of_prime hprime]
  refine ⟨μ'', J', by simp,
    (seg.snoc i).keep (SameOn.mono same fun b hb => Or.inl (by simp at hb; omega)), fun j hj => ?_,
    (kept.write (by omega) _).then same fun b hb => ⟨hb, hb.2⟩⟩
  rw [htab' j hj, Function.update_of_ne (by omega), marked_succ_of_prime hprime]
  by_cases hmul : i ∣ j ∧ i < j
  · simp [hmul, show j < J' by omega]
  · have : ¬ (i ∣ j ∧ i < j ∧ j < J') := fun hc => hmul ⟨hc.1, hc.2.1⟩
    rw [if_neg this, htab j hj]
    tauto

/-- i := i + 1. -/
theorem next_ends {i T : ℕ} {σ : State} (pre : Pre lim m out fr) (him : i ≤ m)
    (h : Sieved μ m out fr i (i + 1) σ) (hT : 4 ≤ T) :
    Ends lim P d (.set Cand (v Cand +' k 1)) σ T (Sieved μ m out fr (i + 1) (i + 1)) := by
  light_facts pre
  obtain ⟨μ', J, rfl, hrest⟩ := h
  exact Ends.setTo (i + 1 : ℕ) ⟨μ', J, rfl, hrest⟩

/-- One round of the main loop: the candidate i is dealt with, and the next candidate is i + 1. -/
theorem round_ends {i : ℕ} {σ : State} (pre : Pre lim m out fr) (hi : 2 ≤ i) (him : i ≤ m)
    (h : Sieved μ m out fr i i σ) :
    Ends lim P d round σ (15 * (m / i) + 30) (Sieved μ m out fr (i + 1) (i + 1)) := by
  light_facts pre
  have htake := fun hprime => take_ends (P := P) (d := d) pre him hprime h
  obtain ⟨μ', J, rfl, seg, htab, kept⟩ := h
  -- if table[i] = 0
  refine Ends.iteThen (fun hc => ?_) fun hc => ?_
  · have hzero : μ' (fr + i) = 0 := by simpa using hc
    have hprime : i.Prime := (prime_iff_not_marked hi).2 ((htab i him).1 hzero)
    exact Ends.next _
      ((htake hprime).mono le_rfl fun _ h' => next_ends pre him h' (by light_time))
  · have hzero : μ' (fr + i) ≠ 0 := by simpa using hc
    have hprime : ¬ i.Prime := fun hp => hzero ((htab i him).2 ((prime_iff_not_marked hi).1 hp))
    refine Ends.next 0 (Ends.skip (next_ends pre him ?_ (by light_time)))
    rw [Sieved, primesBelow_succ_of_not_prime hprime]
    exact ⟨μ', J, rfl, seg,
      fun j hj => (htab j hj).trans (marked_succ_of_not_prime hprime j).not.symm, kept⟩

/-- **sieve(m, out, fr)** writes the primes up to m in ascending order to out and returns their
number.  Only the m cells from out and the m + 1 cells from fr may change. -/
theorem _root_.Light.sieve_meets {p : ℕ} (hp : P[p]? = some sieveBody) (pre : Pre lim m out fr) :
    Meets lim P p d [m, out, fr] μ (sieveTime m) fun r μ' =>
      r = ((Nat.primesLE m).card : ℤ) ∧ SegN μ' out ((Nat.primesLE m).sort (· ≤ ·)) ∧
        SameOutside2 μ μ' out m fr (m + 1) := by
  light_facts pre
  have htime := time_le m
  refine .of_body hp ?_
  -- the table is cleared
  light_piece (clear_ends pre) with _ ⟨μ₁, rfl, hzero, same⟩
  -- i := 2; cnt := 0
  light_set (2 : ℕ)
  light_set (0 : ℕ)
  -- while i ≤ m
  refine Ends.next (loopTime m) ((Ends.while (fun r => Sieved μ m out fr (r + 2) (r + 2)) (m - 1)
    (fun r => 15 * (m / (r + 2)) + 30) ?start ?round ?done).mono (le_of_eq (by simp [loopTime]))
    fun _ h => h)
  case start =>
    rw [Sieved, primesBelow_two]
    exact ⟨μ₁, 0, rfl, Seg.nil, fun j hj => by simp [hzero j (by omega), not_marked_two],
      SameOn.mono same fun b hb => hb.2⟩
  case round =>
    rintro r σ hr h
    have hrun := round_ends (P := P) (d := d) pre (by omega) (by omega : r + 2 ≤ m) h
    obtain ⟨μ', J, rfl, -⟩ := h
    exact ⟨by light_side, by light_side, hrun⟩
  case done =>
    rintro _ ⟨μ', J, rfl, seg, -, kept⟩
    have hlist : primesBelow (m - 1 + 2) = primesBelow (m + 1) := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · rw [primesBelow_two, primesBelow_one]
      · rw [show m - 1 + 2 = m + 1 by omega]
    rw [hlist] at seg
    refine ⟨by light_side, by light_side, ?_⟩
    -- the result is cnt
    light_set ((primesBelow (m + 1)).length : ℕ) using hlist
    refine ⟨?_, ?_, kept⟩
    · simp [length_primesBelow]
    · rw [sort_primesLE]
      exact seg

end Sieve

end Light
