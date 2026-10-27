/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.Interfaces
public import PaddedDescent.F.RebalG
public import PaddedDescent.Col.Good
public import PaddedDescent.F.Interfaces
public import PaddedDescent.F.Table

/-! # Facts for one level

An instance on p·d nodes is laid out on a grid with p rows and d columns, and the factor d^|R| times
its value is the sum of the terms Z_ι over all patterns ι. This file holds facts used
at such a level: sums over lists as sums over ranges and over a filterMap, an arithmetic bound, a
bound on the absolute value of the value of a network, and the fact that the network
that is rebalanced has p nodes, each of them d merged nodes of the grid (it is the row network, or
the grid is square). -/

public section

namespace ClauseBound.Alg.Level

open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset

/-! ### Helpers -/

/-- A sum over a list of numbers 0, …, n − 1 is a sum over a range. -/
theorem sum_map_range (f : ℕ → ℤ) (n : ℕ) : ((List.range n).map f).sum = ∑ y ∈ range n, f y := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]; simp

/-- A filterMap in which every element is either dropped, and then counts 0, or kept, and then
counts the value of its image. -/
theorem filterMap_spec {α β : Type} {f : α → Option β} {z : β → ℤ} {v : α → ℤ} {Q : β → Prop} :
    ∀ (l : List α), (∀ a ∈ l, (f a = none ∧ v a = 0) ∨ ∃ b, f a = some b ∧ z b = v a ∧ Q b) →
      ((l.filterMap f).map z).sum = (l.map v).sum ∧ (∀ b ∈ l.filterMap f, Q b) ∧ (l.filterMap f).length ≤ l.length
  | [], _ => by simp
  | a :: l, h => by
    obtain ⟨i1, i2, i3⟩ := filterMap_spec l fun c hc => h c (List.mem_cons_of_mem _ hc)
    rcases h a List.mem_cons_self with ⟨h1, h2⟩ | ⟨b, h1, h2, h3⟩
    · rw [List.filterMap_cons, h1]
      exact ⟨by simp [i1, h2], i2, by simp only [List.length_cons]; omega⟩
    · rw [List.filterMap_cons, h1]
      refine ⟨by simp [i1, h2], fun c hc => ?_, by simp only [List.length_cons]; omega⟩
      rcases List.mem_cons.1 hc with rfl | hc
      · exact h3
      · exact i2 c hc

/-- x ≤ y·(x / y + 1) for y > 0. -/
theorem le_mul_div_succ (x : ℕ) {y : ℕ} (hy : 0 < y) : x ≤ y * (x / y + 1) :=
  (Nat.lt_mul_div_succ x hy).le

/-- The nodes and the pairs a < b of a set of g elements are together at most g² things. -/
theorem card_add_card_pairs_le (J : Type) [Fintype J] [LinearOrder J] :
    Fintype.card J + #(pairs J) ≤ Fintype.card J * Fintype.card J := by
  rw [card_pairs, Nat.choose_two_right]
  rcases Nat.eq_zero_or_pos (Fintype.card J) with h | h
  · simp [h]
  · have h1 : Fintype.card J * (Fintype.card J - 1) / 2 ≤ Fintype.card J * (Fintype.card J - 1) := Nat.div_le_self _ _
    have h2 : Fintype.card J + Fintype.card J * (Fintype.card J - 1) = Fintype.card J * Fintype.card J := by
      obtain ⟨k, hk⟩ : ∃ k, Fintype.card J = k + 1 := ⟨Fintype.card J - 1, by omega⟩
      rw [hk]; simp only [Nat.add_sub_cancel]; ring
    omega

/-- A network on the nodes J with at most 2^n states a node and all weights W and interactions Ψ at
most 2^B in absolute value has a value Z with |Z| ≤ 2^{|J|·n + |J|²·B}. -/
theorem abs_value_le {J σ τ : Type} [Fintype J] [LinearOrder J] (N : Network J σ τ) {n P B : ℕ}
    (h : N.Sized P B) (hn : ∀ a, #(N.S a) ≤ 2 ^ n) :
    |N.value| ≤ 2 ^ (Fintype.card J * n + Fintype.card J * Fintype.card J * B) := by
  unfold Network.value
  have hW : ∀ z : J → σ, |∏ a, N.W a (z a)| ≤ (2 ^ B) ^ Fintype.card J := by
    intro z
    rw [Finset.abs_prod]
    calc _ ≤ ∏ _a : J, (2 : ℤ) ^ B := Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun a _ => h.abs_W a _
      _ = _ := by rw [Finset.prod_const, card_univ]
  have hΨ : ∀ z : J → σ, |∏ p ∈ pairs J, N.Ψ p.1 p.2 (z p.1) (z p.2)| ≤ (2 ^ B) ^ #(pairs J) := by
    intro z
    rw [Finset.abs_prod]
    calc _ ≤ ∏ _p ∈ pairs J, (2 : ℤ) ^ B := Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun p hp =>
          h.abs_Ψ _ _ _ _ (ne_of_lt (by simpa [pairs] using hp))
      _ = ((2 : ℤ) ^ B) ^ #(pairs J) := by rw [Finset.prod_const]
  have hS : (#(Fintype.piFinset N.S) : ℤ) ≤ (2 ^ n) ^ Fintype.card J := by
    rw [Fintype.card_piFinset]
    have : ∏ a, #(N.S a) ≤ ∏ _a : J, 2 ^ n := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun a _ => hn a
    rw [Finset.prod_const, card_univ] at this
    exact_mod_cast this
  calc _ ≤ ∑ z ∈ Fintype.piFinset N.S, |(∏ a, N.W a (z a)) * ∏ p ∈ pairs J, N.Ψ p.1 p.2 (z p.1) (z p.2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z ∈ Fintype.piFinset N.S, ((2 : ℤ) ^ B) ^ Fintype.card J * ((2 : ℤ) ^ B) ^ #(pairs J) := by
        refine Finset.sum_le_sum fun z _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hW z) (hΨ z) (abs_nonneg _) (by positivity)
    _ = (#(Fintype.piFinset N.S) : ℤ) * (((2 : ℤ) ^ B) ^ Fintype.card J * ((2 : ℤ) ^ B) ^ #(pairs J)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 ^ n) ^ Fintype.card J * (((2 : ℤ) ^ B) ^ Fintype.card J * ((2 : ℤ) ^ B) ^ #(pairs J)) :=
        mul_le_mul_of_nonneg_right hS (by positivity)
    _ = 2 ^ (Fintype.card J * n + (Fintype.card J + #(pairs J)) * B) := by
        rw [← pow_add, ← pow_mul, ← pow_mul, ← pow_add]
        congr 1
        ring
    _ ≤ _ := pow_le_pow_right₀ (by norm_num)
        (Nat.add_le_add_left (Nat.mul_le_mul_right _ (card_add_card_pairs_le J)) _)

/-- The network that is rebalanced has p nodes, each of them d merged nodes of the grid: it is the
row network, or the grid is square. -/
theorem parts_eq (s : Step) (hsq : s.thin = false → s.p = s.d) (c : Bool) :
    nParts s.p s.d (!s.thin && c) = s.p ∧ nMemb s.p s.d (!s.thin && c) = s.d := by
  cases ht : s.thin with
  | false => simp [nParts, nMemb, hsq ht]
  | true => simp [nParts, nMemb]

end ClauseBound.Alg.Level
