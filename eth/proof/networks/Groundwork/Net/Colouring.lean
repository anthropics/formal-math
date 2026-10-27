/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fin.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Zify
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Order.Floor.Semifield

/-!
# The colouring lemma

The Chebyshev step in the proof of Lemma 1 of the paper (a good grouping exists): g ≥ 3K^8 points
carry symmetric capacities c(a,b) that sum to at
most P at every point; then some colouring with K colours has all classes of size < 2g/K and,
between any two classes,
capacity at most (U + gP/K)/K², where U is the sum of all capacities over ordered pairs.
Second-moment argument over the finite type of all colourings, written with finite sums.
Main results: Groundwork.Colouring.exists_colouring, Groundwork.Colouring.exists_colouring_beta.
-/

open Finset

namespace Groundwork.Colouring

section core

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

local notation "K" => Fintype.card κ
local notation "g" => Fintype.card ι
-- the number K^g of colourings (not the N = C(K,2)·λ of NetworkStatements.lean)
local notation "N" => (Fintype.card κ ^ Fintype.card ι)

/-- The number of colourings with prescribed values on S is K^(g-#S). -/
theorem card_prescribed (S : Finset ι) (f : ι → κ) :
    #{χ : ι → κ | ∀ a ∈ S, χ a = f a} * K ^ #S = N := by
  have h : ({χ : ι → κ | ∀ a ∈ S, χ a = f a} : Finset (ι → κ)) =
      Fintype.piFinset (fun a => if a ∈ S then {f a} else univ) := by
    ext χ
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    refine forall_congr' fun a => ?_
    split_ifs with h <;> simp [h]
  rw [h, Fintype.card_piFinset]
  have h1 : ∀ a, #(if a ∈ S then {f a} else (univ : Finset κ)) = if a ∈ S then 1 else K := by
    intro a; split_ifs <;> simp
  simp only [h1]
  have h2 : K ^ #S = ∏ a : ι, if a ∈ S then K else 1 := by
    rw [Finset.prod_ite_mem, univ_inter, prod_const]
  rw [h2, ← prod_mul_distrib, ← card_univ (α := ι), ← prod_const]
  refine prod_congr rfl fun a _ => ?_
  split_ifs <;> simp

/-- A fraction 1/K of the colourings gives one point a prescribed colour. -/
theorem card_one (a : ι) (γ : κ) : #{χ : ι → κ | χ a = γ} * K = N := by
  have := card_prescribed (κ := κ) {a} (fun _ => γ)
  simpa using this

/-- A fraction 1/K² of the colourings gives two points prescribed colours. -/
theorem card_two {a b : ι} (hab : a ≠ b) (γ γ' : κ) :
    #{χ : ι → κ | χ a = γ ∧ χ b = γ'} * K ^ 2 = N := by
  have := card_prescribed (κ := κ) {a, b} (fun x => if x = a then γ else γ')
  rw [card_pair hab] at this
  simpa [hab.symm] using this

/-- A fraction 1/K⁴ of the colourings gives four points prescribed colours. -/
theorem card_four {a b a' b' : ι} (hab : a ≠ b) (h1 : a ≠ a') (h2 : a ≠ b') (h3 : b ≠ a')
    (h4 : b ≠ b') (h5 : a' ≠ b') (γ γ' : κ) :
    #{χ : ι → κ | (χ a = γ ∧ χ b = γ') ∧ (χ a' = γ ∧ χ b' = γ')} * K ^ 4 = N := by
  have := card_prescribed (κ := κ) {a, b, a', b'} (fun x => if x = a ∨ x = a' then γ else γ')
  have hc : #({a, b, a', b'} : Finset ι) = 4 := by
    rw [card_insert_of_notMem (by simp [hab, h1, h2]), card_insert_of_notMem (by simp [h3, h4]),
      card_pair h5]
  rw [hc] at this
  simpa [hab.symm, h1.symm, h2.symm, h3, h3.symm, h4.symm, h5.symm, and_assoc] using this

/-- Chebyshev, as a count. -/
theorem cheb {Ω : Type*} [Fintype Ω] (f : Ω → ℤ) (s : ℤ) (hs : 0 ≤ s) :
    (#{χ : Ω | s ≤ f χ} : ℤ) * s ^ 2 ≤ ∑ χ, f χ ^ 2 := by
  calc (#{χ : Ω | s ≤ f χ} : ℤ) * s ^ 2 = ∑ χ with s ≤ f χ, s ^ 2 := by
        simp [sum_const]
    _ ≤ ∑ χ with s ≤ f χ, f χ ^ 2 :=
        sum_le_sum fun χ h => pow_le_pow_left₀ hs (mem_filter.1 h).2 2
    _ ≤ ∑ χ, f χ ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _

/-- Chebyshev from the first two moments, in natural numbers with denominators cleared. -/
theorem cheb_nat {Ω : Type*} [Fintype Ω] (Y : Ω → ℕ) (A m V t s : ℕ)
    (S1 : (∑ χ, Y χ) * A = Fintype.card Ω * m)
    (S2 : (∑ χ, Y χ ^ 2) * A ^ 2 ≤ Fintype.card Ω * m ^ 2 + V) :
    #{χ : Ω | t * m + s ≤ t * (A * Y χ)} * s ^ 2 ≤ t ^ 2 * V := by
  have hc := cheb (fun χ : Ω => (t : ℤ) * ((A : ℤ) * Y χ - m)) s (by positivity)
  have hsub : #{χ : Ω | t * m + s ≤ t * (A * Y χ)}
      ≤ #{χ : Ω | (s : ℤ) ≤ (t : ℤ) * ((A : ℤ) * Y χ - m)} := by
    refine card_le_card fun χ h => ?_
    simp only [mem_filter, mem_univ, true_and] at h ⊢
    zify at h
    linarith
  have key : ∀ B : ℕ, B ≤ #{χ : Ω | (s : ℤ) ≤ (t : ℤ) * ((A : ℤ) * Y χ - m)} →
      B * s ^ 2 ≤ t ^ 2 * V := by
    intro B hB
    have hB' : (B : ℤ) ≤ (#{χ : Ω | (s : ℤ) ≤ (t : ℤ) * ((A : ℤ) * Y χ - m)} : ℤ) :=
      Nat.cast_le.2 hB
    zify at S1 S2
    have hsum : ∑ χ : Ω, ((t : ℤ) * ((A : ℤ) * Y χ - m)) ^ 2
        = (t : ℤ) ^ 2 * ((∑ χ : Ω, (Y χ : ℤ) ^ 2) * A ^ 2
          - 2 * m * ((∑ χ : Ω, (Y χ : ℤ)) * A) + (Fintype.card Ω : ℤ) * m ^ 2) := by
      have : ∀ χ : Ω, ((t : ℤ) * ((A : ℤ) * Y χ - m)) ^ 2
          = (t : ℤ) ^ 2 * ((Y χ : ℤ) ^ 2 * A ^ 2 - 2 * m * ((Y χ : ℤ) * A) + (m : ℤ) ^ 2) := by
        intro χ; ring
      simp only [this, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, sum_const,
        card_univ, nsmul_eq_mul]
    rw [hsum, S1] at hc
    have a1 : (B : ℤ) * (s : ℤ) ^ 2
        ≤ (#{χ : Ω | (s : ℤ) ≤ (t : ℤ) * ((A : ℤ) * Y χ - m)} : ℤ) * (s : ℤ) ^ 2 :=
      mul_le_mul_of_nonneg_right hB' (sq_nonneg _)
    have a2 : (t : ℤ) ^ 2 * ((∑ χ : Ω, (Y χ : ℤ) ^ 2) * A ^ 2
          - 2 * m * ((Fintype.card Ω : ℤ) * m) + (Fintype.card Ω : ℤ) * m ^ 2)
        ≤ (t : ℤ) ^ 2 * V :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    have a3 : (B : ℤ) * (s : ℤ) ^ 2 ≤ (t : ℤ) ^ 2 * V := a1.trans (hc.trans a2)
    exact_mod_cast a3
  exact key _ hsub

/-! ### Class sizes -/

/-- The size of the class of colour γ, as a sum of indicators. -/
def Zs (γ : κ) (χ : ι → κ) : ℕ := ∑ a : ι, if χ a = γ then 1 else 0

omit [DecidableEq ι] [Fintype κ] in
/-- The sum of indicators is the size of the class. -/
theorem Zs_eq (γ : κ) (χ : ι → κ) : Zs γ χ = #{a | χ a = γ} := by
  simp [Zs]

/-- First moment of the class size: its mean is g/K. -/
theorem sum_Zs (γ : κ) : (∑ χ : ι → κ, Zs γ χ) * K = g * N := by
  unfold Zs
  rw [sum_comm, sum_mul]
  have : ∀ a : ι, (∑ χ : ι → κ, if χ a = γ then 1 else 0) * K = N := by
    intro a
    rw [← card_one a γ]; simp
  rw [sum_congr rfl fun a _ => this a]; simp

/-- Second moment of the class size: at most (g/K)² + g/K. -/
theorem sum_Zs_sq (γ : κ) : (∑ χ : ι → κ, Zs γ χ ^ 2) * K ^ 2 ≤ g ^ 2 * N + g * K * N := by
  have h0 : ∀ χ : ι → κ, Zs γ χ ^ 2 = ∑ a : ι, ∑ b : ι, if χ a = γ ∧ χ b = γ then 1 else 0 := by
    intro χ
    unfold Zs
    rw [sq, sum_mul_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    split_ifs <;> simp_all
  simp only [h0]
  rw [sum_comm, sum_mul]
  have h1 : ∀ a : ι, (∑ χ : ι → κ, ∑ b : ι, if χ a = γ ∧ χ b = γ then 1 else 0) * K ^ 2
      ≤ g * N + K * N := by
    intro a
    rw [sum_comm, sum_mul]
    have h2 : ∀ b : ι, (∑ χ : ι → κ, if χ a = γ ∧ χ b = γ then 1 else 0) * K ^ 2
        ≤ N + if b = a then K * N else 0 := by
      intro b
      by_cases hab : b = a
      · subst hab
        have := card_one (κ := κ) b γ
        simp only [and_self, ite_true]
        have e : (∑ χ : ι → κ, if χ b = γ then 1 else 0) = #{χ : ι → κ | χ b = γ} := by simp
        rw [e]
        calc #{χ : ι → κ | χ b = γ} * K ^ 2 = (#{χ : ι → κ | χ b = γ} * K) * K := by ring
          _ = K * N := by rw [this]; ring
          _ ≤ N + K * N := Nat.le_add_left _ _
      · have := card_two (κ := κ) (Ne.symm hab) γ γ
        have e : (∑ χ : ι → κ, if χ a = γ ∧ χ b = γ then 1 else 0)
            = #{χ : ι → κ | χ a = γ ∧ χ b = γ} := by simp
        rw [e, this]; simp [hab]
    calc ∑ b : ι, (∑ χ : ι → κ, if χ a = γ ∧ χ b = γ then 1 else 0) * K ^ 2
        ≤ ∑ b : ι, (N + if b = a then K * N else 0) := sum_le_sum fun b _ => h2 b
      _ = g * N + K * N := by simp [sum_add_distrib]
  calc ∑ a : ι, (∑ χ : ι → κ, ∑ b : ι, if χ a = γ ∧ χ b = γ then 1 else 0) * K ^ 2
      ≤ ∑ _a : ι, (g * N + K * N) := sum_le_sum fun a _ => h1 a
    _ = g ^ 2 * N + g * K * N := by simp; ring

/-- The number of colourings whose class γ is too large, times g, is at most K·K^g. -/
theorem card_badZ (γ : κ) : #{χ : ι → κ | 2 * g ≤ K * Zs γ χ} * g ≤ K * N := by
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · rw [h0]; simp
  have hc := cheb_nat (fun χ : ι → κ => Zs γ χ) K g (g * K * N) 1 g
    (by rw [sum_Zs]; simp [mul_comm]) (by simpa [mul_comm] using sum_Zs_sq (ι := ι) γ)
  have e : ∀ χ : ι → κ, (1 * g + g ≤ 1 * (K * Zs γ χ)) ↔ (2 * g ≤ K * Zs γ χ) := by
    intro χ; omega
  simp only [e] at hc
  have : (#{χ : ι → κ | 2 * g ≤ K * Zs γ χ} * g) * g ≤ (K * N) * g := by
    calc _ = #{χ : ι → κ | 2 * g ≤ K * Zs γ χ} * g ^ 2 := by ring
      _ ≤ 1 ^ 2 * (g * K * N) := hc
      _ = (K * N) * g := by ring
  exact Nat.le_of_mul_le_mul_right this hpos

/-! ### Capacities between classes -/

variable (c : ι → ι → ℕ)

/-- The capacity from class γ to class γ'. -/
def Ys (γ γ' : κ) (χ : ι → κ) : ℕ :=
  ∑ p : ι × ι, if χ p.1 = γ ∧ χ p.2 = γ' then c p.1 p.2 else 0

/-- The total capacity, over ordered pairs. -/
def Us : ℕ := ∑ p : ι × ι, c p.1 p.2

omit [DecidableEq ι] [Fintype κ] in
/-- The capacity between two classes is at most the total capacity. -/
theorem Ys_le_Us (γ γ' : κ) (χ : ι → κ) : Ys c γ γ' χ ≤ Us c := by
  unfold Ys Us
  refine sum_le_sum fun p _ => ?_
  split_ifs <;> simp

omit [DecidableEq ι] in
/-- The total capacity is at most g·P. -/
theorem Us_le (P : ℕ) (hP : ∀ a, ∑ b, c a b ≤ P) : Us c ≤ g * P := by
  unfold Us
  rw [Fintype.sum_prod_type]
  calc ∑ a, ∑ b, c a b ≤ ∑ _a : ι, P := sum_le_sum fun a _ => hP a
    _ = g * P := by simp

/-- First moment of the capacity between two classes: its mean is U/K². -/
theorem sum_Ys (hd : ∀ a, c a a = 0) (γ γ' : κ) :
    (∑ χ : ι → κ, Ys c γ γ' χ) * K ^ 2 = N * Us c := by
  unfold Ys Us
  rw [sum_comm, sum_mul, mul_sum]
  refine sum_congr rfl fun p _ => ?_
  rw [← sum_filter, sum_const, smul_eq_mul]
  by_cases hp : p.1 = p.2
  · rw [hp, hd]; simp
  · rw [← card_two hp γ γ']; ring

/-- How often the ordered pair q meets the ordered pair p. -/
def meet (p q : ι × ι) : ℕ :=
  (if q.1 = p.1 then 1 else 0) + (if q.1 = p.2 then 1 else 0) +
  (if q.2 = p.1 then 1 else 0) + (if q.2 = p.2 then 1 else 0)

/-- The fraction of colourings that send two ordered pairs from γ to γ' is at most 1/K⁴, plus 1/K²
for every time the pairs
meet. -/
theorem card_pairs_le (γ γ' : κ) (p q : ι × ι) (hp : p.1 ≠ p.2) (hq : q.1 ≠ q.2) :
    #{χ : ι → κ | (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ')} * K ^ 4
      ≤ N + K ^ 2 * N * meet p q := by
  rcases Nat.eq_zero_or_pos (meet p q) with hm | hm
  · rw [hm]
    simp only [meet, Nat.add_eq_zero_iff, ite_eq_right_iff, one_ne_zero, imp_false] at hm
    obtain ⟨⟨⟨m1, m2⟩, m3⟩, m4⟩ := hm
    rw [card_four hp (Ne.symm m1) (Ne.symm m3) (Ne.symm m2) (Ne.symm m4) hq γ γ']
    simp
  · have hle : #{χ : ι → κ | (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ')}
        ≤ #{χ : ι → κ | χ p.1 = γ ∧ χ p.2 = γ'} := by
      refine card_le_card fun χ h => ?_
      simp only [mem_filter, mem_univ, true_and] at h ⊢
      exact h.1
    calc #{χ : ι → κ | (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ')} * K ^ 4
        ≤ #{χ : ι → κ | χ p.1 = γ ∧ χ p.2 = γ'} * K ^ 4 := Nat.mul_le_mul_right _ hle
      _ = K ^ 2 * (#{χ : ι → κ | χ p.1 = γ ∧ χ p.2 = γ'} * K ^ 2) := by ring
      _ = K ^ 2 * N * 1 := by rw [card_two hp γ γ']; ring
      _ ≤ K ^ 2 * N * meet p q := Nat.mul_le_mul_left _ hm
      _ ≤ N + K ^ 2 * N * meet p q := Nat.le_add_left _ _

/-- The capacities of the pairs that meet a given pair sum to at most 4P. -/
theorem sum_meet (hs : ∀ a b, c a b = c b a) (P : ℕ) (hP : ∀ a, ∑ b, c a b ≤ P) (p : ι × ι) :
    ∑ q : ι × ι, c q.1 q.2 * meet p q ≤ 4 * P := by
  have r1 : ∀ x : ι, ∑ q : ι × ι, c q.1 q.2 * (if q.1 = x then 1 else 0) ≤ P := by
    intro x
    rw [Fintype.sum_prod_type, sum_comm]
    simpa using hP x
  have r2 : ∀ x : ι, ∑ q : ι × ι, c q.1 q.2 * (if q.2 = x then 1 else 0) ≤ P := by
    intro x
    rw [Fintype.sum_prod_type]
    have := hP x
    simp only [hs x] at this
    simpa using this
  unfold meet
  simp only [mul_add, sum_add_distrib]
  have := r1 p.1; have := r1 p.2; have := r2 p.1; have := r2 p.2
  omega

/-- Second moment of the capacity between two classes: at most (U/K²)² + 4PU/K². -/
theorem sum_Ys_sq (hd : ∀ a, c a a = 0) (hs : ∀ a b, c a b = c b a) (P : ℕ)
    (hP : ∀ a, ∑ b, c a b ≤ P) (γ γ' : κ) :
    (∑ χ : ι → κ, Ys c γ γ' χ ^ 2) * K ^ 4 ≤ N * Us c ^ 2 + 4 * K ^ 2 * N * P * Us c := by
  have h0 : ∀ χ : ι → κ, Ys c γ γ' χ ^ 2 = ∑ p : ι × ι, ∑ q : ι × ι,
      if (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ') then c p.1 p.2 * c q.1 q.2 else 0 := by
    intro χ
    unfold Ys
    rw [sq, sum_mul_sum]
    refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
    split_ifs <;> simp_all
  simp only [h0]
  rw [sum_comm, sum_mul]
  have h1 : ∀ p : ι × ι, (∑ χ : ι → κ, ∑ q : ι × ι,
      if (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ') then c p.1 p.2 * c q.1 q.2 else 0)
        * K ^ 4 ≤ c p.1 p.2 * (N * Us c + K ^ 2 * N * (4 * P)) := by
    intro p
    rw [sum_comm, sum_mul]
    have h2 : ∀ q : ι × ι, (∑ χ : ι → κ,
        if (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ') then c p.1 p.2 * c q.1 q.2 else 0)
          * K ^ 4 ≤ c p.1 p.2 * (N * c q.1 q.2 + K ^ 2 * N * (c q.1 q.2 * meet p q)) := by
      intro q
      rw [← sum_filter, sum_const, smul_eq_mul]
      by_cases hp : p.1 = p.2
      · rw [hp, hd]; simp
      by_cases hq : q.1 = q.2
      · rw [hq, hd]; simp
      calc #{χ : ι → κ | (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ')}
            * (c p.1 p.2 * c q.1 q.2) * K ^ 4
          = (c p.1 p.2 * c q.1 q.2) *
            (#{χ : ι → κ | (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ')} * K ^ 4) := by ring
        _ ≤ (c p.1 p.2 * c q.1 q.2) * (N + K ^ 2 * N * meet p q) :=
            Nat.mul_le_mul_left _ (card_pairs_le γ γ' p q hp hq)
        _ = c p.1 p.2 * (N * c q.1 q.2 + K ^ 2 * N * (c q.1 q.2 * meet p q)) := by ring
    calc ∑ q : ι × ι, (∑ χ : ι → κ,
        if (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ') then c p.1 p.2 * c q.1 q.2 else 0)
          * K ^ 4
        ≤ ∑ q : ι × ι, c p.1 p.2 * (N * c q.1 q.2 + K ^ 2 * N * (c q.1 q.2 * meet p q)) :=
          sum_le_sum fun q _ => h2 q
      _ = c p.1 p.2 * (N * Us c + K ^ 2 * N * ∑ q : ι × ι, c q.1 q.2 * meet p q) := by
          simp only [← mul_sum, sum_add_distrib, Us]
      _ ≤ c p.1 p.2 * (N * Us c + K ^ 2 * N * (4 * P)) := by
          gcongr
          exact sum_meet c hs P hP p
  calc ∑ p : ι × ι, (∑ χ : ι → κ, ∑ q : ι × ι,
      if (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ') then c p.1 p.2 * c q.1 q.2 else 0)
        * K ^ 4
      ≤ ∑ p : ι × ι, c p.1 p.2 * (N * Us c + K ^ 2 * N * (4 * P)) := sum_le_sum fun p _ => h1 p
    _ = Us c * (N * Us c + K ^ 2 * N * (4 * P)) := by rw [← sum_mul, Us]
    _ = N * Us c ^ 2 + 4 * K ^ 2 * N * P * Us c := by ring

/-- The number of colourings for which the capacity from γ to γ' is too large, times g, is at most
4K⁴·K^g. -/
theorem card_badY (hd : ∀ a, c a a = 0) (hs : ∀ a b, c a b = c b a) (P : ℕ)
    (hP : ∀ a, ∑ b, c a b ≤ P) (γ γ' : κ) :
    #{χ : ι → κ | K * Us c + g * P < K ^ 3 * Ys c γ γ' χ} * g ≤ 4 * K ^ 4 * N := by
  have hU := Us_le c P hP
  rcases Nat.eq_zero_or_pos (g * P) with h0 | hpos
  · have hU0 : Us c = 0 := by omega
    have : ({χ : ι → κ | K * Us c + g * P < K ^ 3 * Ys c γ γ' χ} : Finset (ι → κ)) = ∅ := by
      refine filter_false_of_mem fun χ _ => ?_
      have := Ys_le_Us c γ γ' χ
      have hY : Ys c γ γ' χ = 0 := by omega
      simp [hY]
    rw [this]; simp
  have hc := cheb_nat (fun χ : ι → κ => Ys c γ γ' χ) (K ^ 2) (Us c) (4 * K ^ 2 * N * P * Us c) K
    (g * P) (by rw [sum_Ys c hd]; simp)
    (by
      have := sum_Ys_sq c hd hs P hP γ γ'
      rw [← pow_mul]
      simpa using this)
  have hsub : #{χ : ι → κ | K * Us c + g * P < K ^ 3 * Ys c γ γ' χ}
      ≤ #{χ : ι → κ | K * Us c + g * P ≤ K * (K ^ 2 * Ys c γ γ' χ)} := by
    refine card_le_card fun χ h => ?_
    simp only [mem_filter, mem_univ, true_and] at h ⊢
    calc K * Us c + g * P ≤ K ^ 3 * Ys c γ γ' χ := h.le
      _ = K * (K ^ 2 * Ys c γ γ' χ) := by ring
  have hPpos : 0 < P := Nat.pos_of_mul_pos_left hpos
  have : (#{χ : ι → κ | K * Us c + g * P < K ^ 3 * Ys c γ γ' χ} * g) * (g * P * P)
      ≤ (4 * K ^ 4 * N) * (g * P * P) := by
    calc _ = #{χ : ι → κ | K * Us c + g * P < K ^ 3 * Ys c γ γ' χ} * (g * P) ^ 2 := by ring
      _ ≤ #{χ : ι → κ | K * Us c + g * P ≤ K * (K ^ 2 * Ys c γ γ' χ)} * (g * P) ^ 2 :=
          Nat.mul_le_mul_right _ hsub
      _ ≤ K ^ 2 * (4 * K ^ 2 * N * P * Us c) := hc
      _ = (4 * K ^ 4 * N * P) * Us c := by ring
      _ ≤ (4 * K ^ 4 * N * P) * (g * P) := Nat.mul_le_mul_left _ hU
      _ = (4 * K ^ 4 * N) * (g * P * P) := by ring
  exact Nat.le_of_mul_le_mul_right this (Nat.mul_pos hpos hPpos)

/-- Core form: zero diagonal, general finite index and colour types. -/
theorem exists_colouring_core (hd : ∀ a, c a a = 0) (hs : ∀ a b, c a b = c b a) (P : ℕ)
    (hP : ∀ a, ∑ b, c a b ≤ P) (hK : 0 < K) (hg : 4 * K ^ 6 + K ^ 2 < g) :
    ∃ χ : ι → κ, (∀ γ, K * Zs γ χ < 2 * g) ∧
      ∀ γ γ', K ^ 3 * Ys c γ γ' χ ≤ K * Us c + g * P := by
  by_contra hcon
  push Not at hcon
  have hcov : (univ : Finset (ι → κ)) ⊆
      (univ.biUnion fun γ : κ => {χ : ι → κ | 2 * g ≤ K * Zs γ χ}) ∪
      (univ.biUnion fun p : κ × κ => {χ : ι → κ | K * Us c + g * P < K ^ 3 * Ys c p.1 p.2 χ}) := by
    intro χ _
    simp only [mem_union, mem_biUnion, mem_univ, mem_filter, true_and, Prod.exists]
    by_cases h : ∀ γ, K * Zs γ χ < 2 * g
    · right; exact hcon χ h
    · left; push Not at h; exact h
  have h1 := card_le_card hcov
  have h2 := card_union_le
      (univ.biUnion fun γ : κ => ({χ : ι → κ | 2 * g ≤ K * Zs γ χ} : Finset (ι → κ)))
      (univ.biUnion fun p : κ × κ =>
        ({χ : ι → κ | K * Us c + g * P < K ^ 3 * Ys c p.1 p.2 χ} : Finset (ι → κ)))
  have h3 : #(univ.biUnion fun γ : κ => ({χ : ι → κ | 2 * g ≤ K * Zs γ χ} : Finset (ι → κ))) * g
      ≤ K * (K * N) := by
    calc _ ≤ (∑ γ : κ, #{χ : ι → κ | 2 * g ≤ K * Zs γ χ}) * g :=
          Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ γ : κ, #{χ : ι → κ | 2 * g ≤ K * Zs γ χ} * g := sum_mul _ _ _
      _ ≤ ∑ _γ : κ, K * N := sum_le_sum fun γ _ => card_badZ γ
      _ = K * (K * N) := by simp
  have h4 : #(univ.biUnion fun p : κ × κ =>
        ({χ : ι → κ | K * Us c + g * P < K ^ 3 * Ys c p.1 p.2 χ} : Finset (ι → κ))) * g
      ≤ (K * K) * (4 * K ^ 4 * N) := by
    calc _ ≤ (∑ p : κ × κ, #{χ : ι → κ | K * Us c + g * P < K ^ 3 * Ys c p.1 p.2 χ}) * g :=
          Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ p : κ × κ, #{χ : ι → κ | K * Us c + g * P < K ^ 3 * Ys c p.1 p.2 χ} * g :=
          sum_mul _ _ _
      _ ≤ ∑ _p : κ × κ, 4 * K ^ 4 * N := sum_le_sum fun p _ => card_badY c hd hs P hP p.1 p.2
      _ = (K * K) * (4 * K ^ 4 * N) := by simp
  have h5 : #(univ : Finset (ι → κ)) = N := by simp
  rw [h5] at h1
  have h6 : N * g ≤ (4 * K ^ 6 + K ^ 2) * N := by
    calc N * g ≤ (_ + _) * g := Nat.mul_le_mul_right _ (h1.trans h2)
      _ = _ * g + _ * g := add_mul _ _ _
      _ ≤ K * (K * N) + (K * K) * (4 * K ^ 4 * N) := Nat.add_le_add h3 h4
      _ = (4 * K ^ 6 + K ^ 2) * N := by ring
  have hN : 0 < N := pow_pos hK g
  have : N * g ≤ N * (4 * K ^ 6 + K ^ 2) := by rw [mul_comm N (4 * K ^ 6 + K ^ 2)]; exact h6
  exact absurd (Nat.le_of_mul_le_mul_left this hN) (not_le.2 hg)

/-- The colouring lemma for finite types: K colours, g points, g ≥ 3K^8. The diagonal of c is
ignored. -/
public theorem exists_colouring_fintype (hK : 2 ≤ K) (hg : 3 * K ^ 8 ≤ g)
    (hs : ∀ a b, c a b = c b a) (P : ℕ) (hP : ∀ a, ∑ b with b ≠ a, c a b ≤ P) :
    ∃ χ : ι → κ, (∀ γ, K * #{a | χ a = γ} < 2 * g) ∧
      ∀ γ γ', γ ≠ γ' → K ^ 3 * ∑ a with χ a = γ, ∑ b with χ b = γ', c a b
        ≤ K * (∑ a, ∑ b with b ≠ a, c a b) + g * P := by
  have hg' : 4 * K ^ 6 + K ^ 2 < g := by
    have h4 : 4 ≤ K ^ 2 := by nlinarith
    have h6 : 4 * K ^ 6 ≤ K ^ 8 := by
      calc 4 * K ^ 6 ≤ K ^ 2 * K ^ 6 := Nat.mul_le_mul_right _ h4
        _ = K ^ 8 := by ring
    have h2 : K ^ 2 ≤ K ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
    have h0 : 0 < K ^ 8 := pow_pos (by omega) 8
    omega
  obtain ⟨χ, h1, h2⟩ := exists_colouring_core (κ := κ) (fun a b => if b ≠ a then c a b else 0)
    (by simp) (fun a b => by simp only [hs a b, ne_comm]) P
    (fun a => by rw [← sum_filter]; exact hP a) (by omega) hg'
  refine ⟨χ, fun γ => by rw [← Zs_eq]; exact h1 γ, fun γ γ' hne => ?_⟩
  have hU : Us (fun a b => if b ≠ a then c a b else 0) = ∑ a, ∑ b with b ≠ a, c a b := by
    unfold Us
    rw [Fintype.sum_prod_type]
    exact sum_congr rfl fun a _ => (sum_filter _ _).symm
  have hY : Ys (fun a b => if b ≠ a then c a b else 0) γ γ' χ
      = ∑ a with χ a = γ, ∑ b with χ b = γ', c a b := by
    unfold Ys
    rw [Fintype.sum_prod_type, sum_filter]
    refine sum_congr rfl fun a _ => ?_
    by_cases ha : χ a = γ
    · rw [if_pos ha, sum_filter]
      refine sum_congr rfl fun b _ => ?_
      by_cases hb : χ b = γ'
      · have hba : b ≠ a := by
          rintro rfl
          exact hne (ha.symm.trans hb)
        simp [ha, hb, hba]
      · simp [hb]
    · simp [ha]
  have := h2 γ γ'
  rwa [hU, hY] at this

end core

/-- The colouring lemma: K ≥ 2 colours, g ≥ 3K^8 points (Lemma 1 of the paper has g = 3K^8). -/
public theorem exists_colouring {K g : ℕ} (hK : 2 ≤ K) (hg : 3 * K ^ 8 ≤ g) (c : Fin g → Fin g → ℕ)
    (hs : ∀ a b, c a b = c b a) (P : ℕ) (hP : ∀ a, ∑ b with b ≠ a, c a b ≤ P) :
    ∃ χ : Fin g → Fin K, (∀ γ, K * #{a | χ a = γ} < 2 * g) ∧
      ∀ γ γ', γ ≠ γ' → K ^ 3 * ∑ a with χ a = γ, ∑ b with χ b = γ', c a b
        ≤ K * (∑ a, ∑ b with b ≠ a, c a b) + g * P := by
  have := exists_colouring_fintype (ι := Fin g) (κ := Fin K) c (by simpa using hK)
    (by simpa using hg) hs P hP
  simpa only [Fintype.card_fin] using this

/-- The label length after merging: max 1 ⌊(U + gP/K)/K²⌋, written as max 1 ⌊(KU + gP)/K³⌋. -/
@[expose] public def beta (K g U P : ℕ) : ℕ := max 1 ((K * U + g * P) / K ^ 3)

/-- The label length is at least 1. -/
public theorem one_le_beta (K g U P : ℕ) : 1 ≤ beta K g U P := le_max_left _ _

/-- K²β ≤ K² + U + gP/K, multiplied by K. -/
public theorem beta_le (K g U P : ℕ) : K ^ 3 * beta K g U P ≤ K ^ 3 + K * U + g * P := by
  unfold beta
  have := Nat.mul_div_le (K * U + g * P) (K ^ 3)
  rcases le_total 1 ((K * U + g * P) / K ^ 3) with h | h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]; omega

/-- What a class-pair capacity needs in order to be at most β. -/
public theorem le_beta {K g U P Y : ℕ} (hK : 0 < K) (h : K ^ 3 * Y ≤ K * U + g * P) :
    Y ≤ beta K g U P :=
  le_max_of_le_right ((Nat.le_div_iff_mul_le (pow_pos hK 3)).2 (by rwa [mul_comm]))

/-- The colouring lemma with β: small classes, every class-pair capacity at most β. -/
public theorem exists_colouring_beta {K g : ℕ} (hK : 2 ≤ K) (hg : 3 * K ^ 8 ≤ g)
    (c : Fin g → Fin g → ℕ) (hs : ∀ a b, c a b = c b a) (P : ℕ)
    (hP : ∀ a, ∑ b with b ≠ a, c a b ≤ P) :
    ∃ χ : Fin g → Fin K, (∀ γ, K * #{a | χ a = γ} < 2 * g) ∧
      ∀ γ γ', γ ≠ γ' → ∑ a with χ a = γ, ∑ b with χ b = γ', c a b
        ≤ beta K g (∑ a, ∑ b with b ≠ a, c a b) P := by
  obtain ⟨χ, h1, h2⟩ := exists_colouring hK hg c hs P hP
  exact ⟨χ, h1, fun γ γ' hne => le_beta (by omega) (h2 γ γ' hne)⟩

end Groundwork.Colouring

