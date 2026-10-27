/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import AppVariablesStatement
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.LinearCombination

/-! # Lemma 13 (Family of checks): the events H_E

The part of the printed proof that speaks of (u₁, u₂), one theorem for each of its steps, with
fractions cleared: a probability is a number of pairs (u₁, u₂) ∈ 𝔽², out of |𝔽|².
Throughout, 𝔽 is a finite field, `bits` writes its elements as strings of s bits (linearly over the
field with two elements), ϑ gives the m clauses distinct elements of 𝔽, and v = 2^a.

* `pair_uniform`: for ϑ ≠ ϑ' the pair (u₁ϑ + u₂, u₁ϑ' + u₂) is uniformly distributed in 𝔽².
* `card_H`: the event H_E has probability 2/v.
* `card_H_and`: the events H_E are pairwise independent.
* `sum_Y`, `sum_Y_sq`: the mean y of Y, and E(Y²) ≤ y² + y.
* `second_moment`: Pr(Y > 0) > 2/3 for a set V of more than v clauses. -/

@[expose] public section

namespace VariableBound.Pairwise

open Finset AppVariables

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}

/-- The event H_E for the pair p = (u₁, u₂): the first a − 1 = log v − 1 bits of u₁·ϑ_E + u₂ are 0. -/
def H (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (p : F × F) (E : Fin m) : Prop :=
  ∀ i : Fin s, i.val < a - 1 → bits (p.1 * ϑ E + p.2) i = 0

/-- Whether H_E holds can be decided. -/
instance (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (p : F × F) (E : Fin m) : Decidable (H bits ϑ a p E) := by
  unfold H; infer_instance

/-- The elements of 𝔽 whose first a − 1 bits are 0. -/
def Z (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (a : ℕ) : Finset F := univ.filter fun x => ∀ i : Fin s, i.val < a - 1 → bits x i = 0

/-- Y: the number of the clauses E ∈ V for which H_E holds. -/
def Y (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (V : Finset (Fin m)) (p : F × F) : ℕ := #{E ∈ V | H bits ϑ a p E}

omit [DecidableEq F] in
/-- 𝔽 has 2^s elements, since its elements are written as strings of s bits. -/
theorem card_F (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) : Fintype.card F = 2 ^ s := by
  rw [Fintype.card_congr bits.toEquiv, Fintype.card_fun, ZMod.card, Fintype.card_fin]

omit [DecidableEq F] in
/-- If a − 1 ≤ s, one element of 𝔽 in 2^(a−1) has its first a − 1 bits equal to 0. -/
theorem card_Z (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (a : ℕ) (ha : a - 1 ≤ s) : 2 ^ (a - 1) * #(Z bits a) = Fintype.card F := by
  have h1 : #(Z bits a) = #(Fintype.piFinset fun i : Fin s => if i.val < a - 1 then ({0} : Finset (ZMod 2)) else univ) := by
    refine card_equiv bits.toEquiv fun x => ?_
    simp only [Z, mem_filter, mem_univ, true_and, Fintype.mem_piFinset, LinearEquiv.coe_toEquiv]
    refine forall_congr' fun i => ?_
    by_cases h : i.val < a - 1 <;> simp [h]
  have h2 : (2 : ℕ) ^ (a - 1) = ∏ i : Fin s, if i.val < a - 1 then 2 else 1 := by
    rw [prod_ite, prod_const, prod_const_one, mul_one, Fin.card_filter_val_lt, min_eq_right ha]
  rw [h1, Fintype.card_piFinset, h2, ← prod_mul_distrib, card_F bits]
  have : ∀ i : Fin s, ((if i.val < a - 1 then 2 else 1) * #(if i.val < a - 1 then ({0} : Finset (ZMod 2)) else univ)) = 2 := by
    intro i
    by_cases h : i.val < a - 1 <;> simp [h, ZMod.card]
  simp [this]

omit [DecidableEq F] [Algebra (ZMod 2) F] in
/-- Proof of Lemma 13 (Family of checks): for distinct ϑ, ϑ' ∈ 𝔽 the pair (u₁ϑ + u₂, u₁ϑ' + u₂) is
uniformly distributed in 𝔽² when (u₁, u₂) is: the map is a bijection of 𝔽². -/
theorem pair_uniform (θ θ' : F) (h : θ ≠ θ') : Function.Bijective fun p : F × F => (p.1 * θ + p.2, p.1 * θ' + p.2) := by
  refine Finite.injective_iff_bijective.1 fun p q hpq => ?_
  simp only [Prod.mk.injEq] at hpq
  obtain ⟨h1, h2⟩ := hpq
  have h3 : (p.1 - q.1) * (θ - θ') = 0 := by linear_combination h1 - h2
  have h4 : p.1 = q.1 := by
    rcases mul_eq_zero.1 h3 with h5 | h5
    · exact sub_eq_zero.1 h5
    · exact absurd (sub_eq_zero.1 h5) h
  refine Prod.ext h4 ?_
  rw [h4] at h1
  exact add_left_cancel h1

omit [Algebra (ZMod 2) F] in
/-- The number of pairs (u₁, u₂) whose image (u₁ϑ + u₂, u₁ϑ' + u₂), ϑ ≠ ϑ', lies in a set S ⊆ 𝔽² is |S|. -/
theorem card_pair_mem (θ θ' : F) (h : θ ≠ θ') (S : Finset (F × F)) : #{p : F × F | (p.1 * θ + p.2, p.1 * θ' + p.2) ∈ S} = #S :=
  card_equiv (Equiv.ofBijective _ (pair_uniform θ θ' h)) fun p => by simp

/-- Proof of Lemma 13 (Family of checks): the event H_E has probability 1/2^(a−1), which is 2/v for
v = 2^a and a ≥ 1, if a − 1 ≤ s: 2^(a−1) times the number of pairs (u₁, u₂) with H_E is |𝔽|². -/
theorem card_H (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha : a - 1 ≤ s) (E : Fin m) :
    2 ^ (a - 1) * #{p : F × F | H bits ϑ a p E} = Fintype.card F ^ 2 := by
  have h1 : ϑ E ≠ ϑ E + 1 := by simp
  have h2 : #{p : F × F | H bits ϑ a p E} = #(Z bits a ×ˢ (univ : Finset F)) := by
    rw [← card_pair_mem (ϑ E) (ϑ E + 1) h1 (Z bits a ×ˢ univ)]
    congr 1
    ext p
    simp [H, Z]
  rw [h2, card_product, card_univ, ← mul_assoc, card_Z bits a ha, sq]

/-- Proof of Lemma 13 (Family of checks): the events H_E are pairwise independent, if a − 1 ≤ s: for
E ≠ E', 4^(a−1) times the number of pairs (u₁, u₂) with H_E and H_E' is |𝔽|². -/
theorem card_H_and (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha : a - 1 ≤ s) (E E' : Fin m) (hE : E ≠ E') :
    4 ^ (a - 1) * #{p : F × F | H bits ϑ a p E ∧ H bits ϑ a p E'} = Fintype.card F ^ 2 := by
  have h1 : ϑ E ≠ ϑ E' := fun h => hE (ϑ.injective h)
  have h2 : #{p : F × F | H bits ϑ a p E ∧ H bits ϑ a p E'} = #(Z bits a ×ˢ Z bits a) := by
    rw [← card_pair_mem (ϑ E) (ϑ E') h1 (Z bits a ×ˢ Z bits a)]
    congr 1
    ext p
    simp [H, Z]
  rw [h2, card_product, ← card_Z bits a ha, show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  ring

/-- Proof of Lemma 13 (Family of checks): the mean of Y is |V|/2^(a−1), which is y = 2|V|/v for v =
2^a and a ≥ 1, if a − 1 ≤ s: 2^(a−1) times the sum of Y over all pairs (u₁, u₂) is |V|·|𝔽|². -/
theorem sum_Y (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha : a - 1 ≤ s) (V : Finset (Fin m)) :
    2 ^ (a - 1) * ∑ p : F × F, Y bits ϑ a V p = #V * Fintype.card F ^ 2 := by
  simp_rw [Y, card_filter]
  rw [sum_comm, mul_sum]
  have h : ∀ E ∈ V, 2 ^ (a - 1) * ∑ p : F × F, (if H bits ϑ a p E then 1 else 0) = Fintype.card F ^ 2 := by
    intro E _
    rw [← card_filter]
    exact card_H bits ϑ a ha E
  rw [sum_congr rfl h, sum_const, smul_eq_mul]

/-- Proof of Lemma 13 (Family of checks): E(Y²) ≤ y² + y (the variance of Y is at most its mean y =
2|V|/v), if a − 1 ≤ s: 4^(a−1) times the sum of Y² over all pairs (u₁, u₂) is at most (|V|² +
2^(a−1)·|V|)·|𝔽|². -/
theorem sum_Y_sq (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha : a - 1 ≤ s) (V : Finset (Fin m)) :
    4 ^ (a - 1) * ∑ p : F × F, Y bits ϑ a V p ^ 2 ≤ (#V ^ 2 + 2 ^ (a - 1) * #V) * Fintype.card F ^ 2 := by
  have h1 : ∀ p : F × F, Y bits ϑ a V p ^ 2 = ∑ E ∈ V, ∑ E' ∈ V, if H bits ϑ a p E ∧ H bits ϑ a p E' then 1 else 0 := by
    intro p
    rw [Y, card_filter, sq, sum_mul_sum]
    refine sum_congr rfl fun E _ => sum_congr rfl fun E' _ => ?_
    by_cases h : H bits ϑ a p E <;> by_cases h' : H bits ϑ a p E' <;> simp [h, h']
  have h2 : ∀ E E' : Fin m, 4 ^ (a - 1) * ∑ p : F × F, (if H bits ϑ a p E ∧ H bits ϑ a p E' then 1 else 0)
      ≤ Fintype.card F ^ 2 + if E = E' then 2 ^ (a - 1) * Fintype.card F ^ 2 else 0 := by
    intro E E'
    rw [← card_filter]
    by_cases h : E = E'
    · subst h
      simp only [and_self, if_true]
      rw [← card_H bits ϑ a ha E, show (4 : ℕ) = 2 * 2 by norm_num, mul_pow, mul_assoc]
      exact Nat.le_add_left _ _
    · rw [card_H_and bits ϑ a ha E E' h, if_neg h]
      exact Nat.le_add_right _ _
  simp_rw [h1]
  rw [sum_comm, mul_sum]
  calc ∑ E ∈ V, 4 ^ (a - 1) * ∑ p : F × F, ∑ E' ∈ V, (if H bits ϑ a p E ∧ H bits ϑ a p E' then 1 else 0)
      = ∑ E ∈ V, ∑ E' ∈ V, 4 ^ (a - 1) * ∑ p : F × F, (if H bits ϑ a p E ∧ H bits ϑ a p E' then 1 else 0) := by
        refine sum_congr rfl fun E _ => ?_
        rw [sum_comm, mul_sum]
    _ ≤ ∑ E ∈ V, ∑ E' ∈ V, (Fintype.card F ^ 2 + if E = E' then 2 ^ (a - 1) * Fintype.card F ^ 2 else 0) :=
        sum_le_sum fun E _ => sum_le_sum fun E' _ => h2 E E'
    _ = ∑ E ∈ V, (#V * Fintype.card F ^ 2 + 2 ^ (a - 1) * Fintype.card F ^ 2) := by
        refine sum_congr rfl fun E hE => ?_
        rw [sum_add_distrib, sum_const, smul_eq_mul, sum_ite_eq, if_pos hE]
    _ = (#V ^ 2 + 2 ^ (a - 1) * #V) * Fintype.card F ^ 2 := by
        rw [sum_const, smul_eq_mul]
        ring

omit [DecidableEq F] in
/-- Proof of Lemma 13 (Family of checks): the Cauchy–Schwarz inequality in the form Pr(Y > 0) ≥
(EY)²/E(Y²): the square of the sum of Y is at most the number of pairs (u₁, u₂) with Y > 0 times the
sum of Y². -/
theorem cauchy_schwarz (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (V : Finset (Fin m)) :
    (∑ p : F × F, Y bits ϑ a V p) ^ 2 ≤ #{p : F × F | 0 < Y bits ϑ a V p} * ∑ p : F × F, Y bits ϑ a V p ^ 2 := by
  have h := sum_mul_sq_le_sq_mul_sq (univ : Finset (F × F)) (fun p => if 0 < Y bits ϑ a V p then 1 else 0) (Y bits ϑ a V)
  have h1 : ∀ p : F × F, (if 0 < Y bits ϑ a V p then 1 else 0) * Y bits ϑ a V p = Y bits ϑ a V p := by
    intro p
    rcases Nat.eq_zero_or_pos (Y bits ϑ a V p) with h0 | h0 <;> simp [h0]
  have h2 : ∀ p : F × F, (if 0 < Y bits ϑ a V p then 1 else 0) ^ 2 = if 0 < Y bits ϑ a V p then 1 else 0 := by
    intro p
    split_ifs <;> simp
  simp_rw [h1, h2] at h
  rwa [← card_filter] at h

/-- Proof of Lemma 13 (Family of checks): Pr(Y > 0) > 2/3 for a set V of more than v = 2^a clauses,
if 1 ≤ a and a − 1 ≤ s: three times the number of pairs (u₁, u₂) for which H_E holds for some E ∈ V
is more than 2·|𝔽|². -/
theorem second_moment (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha1 : 1 ≤ a) (ha : a - 1 ≤ s) (V : Finset (Fin m)) (hV : 2 ^ a < #V) :
    2 * Fintype.card F ^ 2 < 3 * #{p : F × F | ∃ E ∈ V, H bits ϑ a p E} := by
  have hP : #{p : F × F | ∃ E ∈ V, H bits ϑ a p E} = #{p : F × F | 0 < Y bits ϑ a V p} := by
    congr 1
    ext p
    simp [Y, card_pos, Finset.Nonempty]
  rw [hP]
  have hw : 2 ^ a = 2 * 2 ^ (a - 1) := by rw [← pow_succ', Nat.sub_add_cancel ha1]
  have h4 : (4 : ℕ) ^ (a - 1) = 2 ^ (a - 1) * 2 ^ (a - 1) := by rw [← mul_pow]; norm_num
  have hq : 0 < Fintype.card F ^ 2 := pow_pos Fintype.card_pos 2
  have e1 := sum_Y bits ϑ a ha V
  have e2 := sum_Y_sq bits ϑ a ha V
  have e3 := cauchy_schwarz bits ϑ a V
  rw [h4] at e2
  rw [hw] at hV
  generalize (2 : ℕ) ^ (a - 1) = w at *
  generalize Fintype.card F ^ 2 = Q at *
  generalize ∑ p : F × F, Y bits ϑ a V p = S₁ at *
  generalize ∑ p : F × F, Y bits ϑ a V p ^ 2 = S₂ at *
  generalize #{p : F × F | 0 < Y bits ϑ a V p} = P at *
  generalize #V = n at *
  have hn : 0 < n := by omega
  -- n·Q ≤ P·(n + w), which is Pr(Y > 0) ≥ y/(y + 1)
  have h5 : n * Q * (n * Q) ≤ P * (n + w) * (n * Q) :=
    calc n * Q * (n * Q) = w * w * S₁ ^ 2 := by rw [← e1]; ring
      _ ≤ w * w * (P * S₂) := Nat.mul_le_mul_left _ e3
      _ = P * (w * w * S₂) := by ring
      _ ≤ P * ((n ^ 2 + w * n) * Q) := Nat.mul_le_mul_left _ e2
      _ = P * (n + w) * (n * Q) := by ring
  have h6 : n * Q ≤ P * (n + w) := Nat.le_of_mul_le_mul_right h5 (Nat.mul_pos hn hq)
  by_contra hc
  have hc' : 3 * P ≤ 2 * Q := not_lt.1 hc
  have h7 : 3 * n * Q ≤ 2 * (n + w) * Q :=
    calc 3 * n * Q = 3 * (n * Q) := by ring
      _ ≤ 3 * (P * (n + w)) := Nat.mul_le_mul_left _ h6
      _ = 3 * P * (n + w) := by ring
      _ ≤ 2 * Q * (n + w) := Nat.mul_le_mul_right _ hc'
      _ = 2 * (n + w) * Q := by ring
  have h8 := Nat.le_of_mul_le_mul_right h7 hq
  omega

end VariableBound.Pairwise
