/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.SecCrossing_FactDefs
import Mathlib.Tactic

/-! # Lemma 2(b): the factorization of the product that belongs to one set Q

In the proof of Lemma 2(b), the display that defines R and C and observation (a) after Definition 1
give this product a row-wise factorization (f_Q, f'_Q) through 3(t − i) + 6i bits, whose index θ'
lists the indices of the blocks s = 1, …, t in this order.
The file proves `StChunk`: for a fixed Q, the sum over all words θ' of the product of the two
functions is the product over the blocks. The proof is observation (a) (a product of functions of
separate arguments factors through the
sum of the numbers of bits) carried out by induction on the number of blocks: a word θ' for t + 1
blocks is a word for t blocks followed by the index of the last block, the first t factors read only
the first part and the last
factor reads only the second, so the sum splits into a product of two sums. -/

public section

namespace Eight

open Groundwork Groundwork.Prog PaddedDescent.F Finset

/-! ### Words -/

/-- A sum over the words of m + n bits is a double sum: a word of m bits followed by a word of n
bits. -/
theorem sum_words_add {X : Type*} [AddCommMonoid X] (m n : ℕ) (G : List Bool → X) :
    ∑ w ∈ words (m + n), G w = ∑ u ∈ words m, ∑ v ∈ words n, G (u ++ v) := by
  rw [← sum_product']
  symm
  refine sum_nbij' (fun p => p.1 ++ p.2) (fun w => (w.take m, w.drop m)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [mem_product, mem_words] at hp
    simp [hp.1, hp.2]
  · intro w hw
    simp only [mem_words] at hw
    simp only [mem_product, mem_words, List.length_take, List.length_drop]
    omega
  · intro p hp
    simp only [mem_product, mem_words] at hp
    simp [← hp.1]
  · intro w _
    simp
  · intro p _
    rfl

/-- The three bits from position j on of u ++ v are those of u, if they lie inside u. -/
theorem blkAt_append_left {u : List Bool} (v : List Bool) {j : ℕ} (h : j + 3 ≤ u.length) : blkAt (u ++ v) j = blkAt u j := by
  simp only [blkAt]
  rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]

/-- The three bits from position |u| + j on of u ++ v are those of v from position j on. -/
theorem blkAt_append_right (u v : List Bool) (j : ℕ) : blkAt (u ++ v) (u.length + j) = blkAt v j := by
  simp only [blkAt]
  rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
  congr 3 <;> omega

/-- A sum over the words of 3 bits is a sum over the blocks. -/
theorem sum_words_three {X : Type*} [AddCommMonoid X] (G : Block → X) : ∑ w ∈ words 3, G (blkAt w 0) = ∑ k : Block, G k := by
  refine sum_nbij' (fun w => blkAt w 0) (fun k => [k.1, k.2.1, k.2.2]) ?_ ?_ ?_ ?_ ?_
  · intro w _
    exact mem_univ _
  · intro k _
    simp
  · intro w hw
    simp only [mem_words] at hw
    match w, hw with
    | [_, _, _], _ => rfl
  · intro k _
    rfl
  · intro w _
    rfl

/-- A sum over the words of 6 bits is a sum over the pairs of blocks. -/
theorem sum_words_six {X : Type*} [AddCommMonoid X] (G : Block → Block → X) :
    ∑ w ∈ words 6, G (blkAt w 0) (blkAt w 3) = ∑ k : Block, ∑ k' : Block, G k k' := by
  rw [show (6 : ℕ) = 3 + 3 from rfl, sum_words_add, ← sum_words_three]
  refine sum_congr rfl fun u hu => ?_
  simp only [mem_words] at hu
  rw [← sum_words_three]
  refine sum_congr rfl fun v _ => ?_
  have h := blkAt_append_right u v 0
  rw [hu] at h
  rw [blkAt_append_left v (by omega), h]

/-! ### The length of θ' -/

/-- The index of the block number s begins where the indices of the s earlier blocks end. -/
theorem off_eq_lenW (tr : Bool) (Q : List Bool) (s : ℕ) : off tr Q s = lenW tr Q s := rfl

/-- One more block makes θ' longer by 6 bits if the block is wide, by 3 bits if not. -/
theorem lenW_succ (tr : Bool) (Q : List Bool) (t : ℕ) : lenW tr Q (t + 1) = lenW tr Q t + if wide tr Q t = true then 6 else 3 := by
  unfold lenW
  rw [List.range_succ, List.countP_append, List.countP_singleton]
  split_ifs <;> omega

/-- The length of θ' grows with the number of blocks. -/
theorem lenW_mono (tr : Bool) (Q : List Bool) : Monotone (lenW tr Q) :=
  monotone_nat_of_le_succ fun t => by rw [lenW_succ]; omega

/-! ### What a factor reads -/

/-- The factor of the block number s < t in the first function reads only the part of θ' that
belongs to the first t blocks. -/
theorem topAt_append_left (tr : Bool) (Q a b : List Bool) {u : List Bool} (v : List Bool) {s t : ℕ} (hs : s < t) (hu : u.length = lenW tr Q t) :
    topAt tr Q (u ++ v) a b s = topAt tr Q u a b s := by
  have h1 := lenW_mono tr Q (Nat.succ_le_of_lt hs)
  rw [Nat.succ_eq_add_one, lenW_succ] at h1
  unfold topAt
  rw [off_eq_lenW]
  split_ifs at h1 with hw
  · rw [blkAt_append_left v (by omega), blkAt_append_left v (by omega)]
  · rw [if_neg hw, if_neg hw, blkAt_append_left v (by omega)]

/-- The same for the second function. -/
theorem botAt_append_left (tr : Bool) (Q a b : List Bool) {u : List Bool} (v : List Bool) {s t : ℕ} (hs : s < t) (hu : u.length = lenW tr Q t) :
    botAt tr Q (u ++ v) a b s = botAt tr Q u a b s := by
  have h1 := lenW_mono tr Q (Nat.succ_le_of_lt hs)
  rw [Nat.succ_eq_add_one, lenW_succ] at h1
  unfold botAt
  rw [off_eq_lenW]
  split_ifs at h1 with hw
  · rw [blkAt_append_left v (by omega), blkAt_append_left v (by omega)]
  · rw [if_neg hw, if_neg hw, blkAt_append_left v (by omega)]

/-! ### One block -/

/-- A block that is not wide: Σ_k ψ_k(a,b)·ψ_k(b',a') = R(a,b,a',b'), the definition of R. A wide
block: Σ_{k,k'} [(a,b) = (k,k')]·R(k,a',k',b') = R(a,a',b,b'), the factorization through all 6 bits
of (a,b). Here u is the part
of θ' before the index of the block number t. -/
theorem sum_last (tr : Bool) (t : ℕ) (Q a b a' b' : List Bool) {u : List Bool} (hu : u.length = lenW tr Q t) :
    ∑ v ∈ words (if wide tr Q t = true then 6 else 3), topAt tr Q (u ++ v) a b t * botAt tr Q (u ++ v) a' b' t =
      if wide tr Q t = true then Rb (blkL a t) (blkL a' t) (blkL b t) (blkL b' t) else Rb (blkL a t) (blkL b t) (blkL a' t) (blkL b' t) := by
  have h0 : ∀ v, blkAt (u ++ v) (lenW tr Q t) = blkAt v 0 := fun v => by rw [← hu]; exact blkAt_append_right u v 0
  have h3 : ∀ v, blkAt (u ++ v) (lenW tr Q t + 3) = blkAt v 3 := fun v => by rw [← hu]; exact blkAt_append_right u v 3
  unfold topAt botAt
  simp only [off_eq_lenW, h0, h3]
  split_ifs with hw
  · rw [sum_words_six fun k k' => (if blkL a t = k ∧ blkL b t = k' then (1 : ℤ) else 0) * Rb k (blkL a' t) k' (blkL b' t)]
    simp [ite_and]
  · rw [sum_words_three fun k => psi k (blkL a t) (blkL b t) * psi k (blkL b' t) (blkL a' t)]
    rfl

/-! ### All blocks -/

/-- «This product has a row-wise factorization (f_Q, f'_Q) through 3(t − i) + 6i bits, whose index
θ' lists the indices of the blocks s = 1, …, t in this order». The paper states this row-wise and
obtains it from
observation (a) after Definition 1; here it is proved for both directions, and the induction behind
that observation is written out. -/
theorem stChunk : StChunk := by
  intro tr t Q a b a' b'
  simp only [prodL_eq]
  induction t with
  | zero =>
    have h : words (lenW tr Q 0) = {[]} := by
      ext w
      simp [lenW]
    simp [h]
  | succ t ih =>
    rw [lenW_succ, sum_words_add, prod_range_succ, ← ih, sum_mul]
    refine sum_congr rfl fun u hu => ?_
    simp only [mem_words] at hu
    rw [← sum_last tr t Q a b a' b' hu, mul_sum]
    refine sum_congr rfl fun v _ => ?_
    rw [prod_range_succ, prod_range_succ,
      prod_congr rfl fun s hs => topAt_append_left tr Q a b v (mem_range.1 hs) hu,
      prod_congr rfl fun s hs => botAt_append_left tr Q a' b' v (mem_range.1 hs) hu]
    ring

end Eight
