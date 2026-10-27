/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.GridProcedures
public import ClauseBound.Alg.CertGridG
import Mathlib.Tactic

/-! # The numbers of the grid, jointly in the lists

The certificates of proof/rates/ClauseBound/Alg/CertGridG.lean for `digG`, `lenG`, `capG`, `priceG`,
`totalG` are for ONE family of pieces with certificates of its own (`P.Keeps`). In the recursion the
numbers |𝓘|, c^row_i, c^col_i are read from lists in the context (`listsAsPieces`), so the pieces
vary with the input. Here are the same certificates jointly in the lists. They hold on EVERY input
because `listsAsPieces` cuts each number at 2λ and λ is given in unary.

Besides: a chunk of a label for a chunk number that is NOT given in unary (`chunkL_polyT`). The loop
over the rectangles passes its counter j, in binary, to the computation of the chunk, and a
certificate must cover every j. The digits of the pattern y beyond its length are 0, so the lengths
of the chunks are constant from the place (number of binary digits of y) on, and the sum of the
first κ lengths is a sum of at most that many terms and a product. -/

public section

namespace ExplicitCost

open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG

variable {α : Type} [Enc α]

/-! ### The numbers -/

section Lists

variable {L : α → Lists} (hL : PolyT L)
include hL

/-- c^row_i or c^col_i, cut at 2λ, is given in unary. -/
theorem capL_unary {tr : α → Bool} {lam i : α → ℕ} (ht : PolyT tr) (hl : Unary lam) (hi : PolyT i) : Unary fun x => (listsAsPieces (L x)).cap (tr x) 0 (lam x) (i x) :=
  unary_min_right (f := fun x => (if tr x = true then (L x).2.2 else (L x).2.1).getD (i x) 0) (by fun_prop) (by fun_prop)

/-- The digit of a pattern at a rectangle. -/
@[fun_prop] theorem digL_polyT {d lam y q κ : α → ℕ} {tr : α → Bool} (hd : PolyT d) (ht : PolyT tr) (hy : PolyT y) (hq : PolyT q) (hκ : PolyT κ) :
    PolyT fun x => digG (listsAsPieces (L x)) (d x) (tr x) 0 (lam x) (y x) (q x) (κ x) :=
  (by fun_prop : PolyT fun x => digit ((L x).1.length - 1) (y x) (rectIxG (d x) (tr x) (q x) (κ x)))

/-- The length of the chunk of a rectangle is given in unary. -/
@[fun_prop] theorem lenL_unary {d lam y q κ : α → ℕ} {tr : α → Bool} (hd : PolyT d) (ht : PolyT tr) (hl : Unary lam) (hy : PolyT y) (hq : PolyT q) (hκ : PolyT κ) :
    Unary fun x => lenG (listsAsPieces (L x)) (d x) (tr x) 0 (lam x) (y x) (q x) (κ x) :=
  capL_unary hL ht hl (digL_polyT hL hd ht hy hq hκ)

/-- The length of the labels of two parts is given in unary. -/
@[fun_prop] theorem capGL_unary {p d lam y a b : α → ℕ} {tr : α → Bool} (hp : Unary p) (hd : Unary d) (ht : PolyT tr) (hl : Unary lam) (hy : PolyT y) (ha : PolyT a) (hb : PolyT b) :
    Unary fun x => capG (listsAsPieces (L x)) (p x) (d x) (tr x) 0 (lam x) (y x) (a x) (b x) := by
  have h1 : Unary fun q : α × ℕ => lenG (listsAsPieces (L q.1)) (d q.1) (tr q.1) 0 (lam q.1) (y q.1) (tri (min (a q.1) (b q.1)) (max (a q.1) (b q.1))) q.2 :=
    lenL_unary (L := fun q : α × ℕ => L q.1) (by fun_prop) (by have := hd.poly; fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have h2 : Unary fun x => nMemb (p x) (d x) (tr x) * lam x + ((List.range (c2 (nMemb (p x) (d x) (tr x)))).map fun κ =>
      lenG (listsAsPieces (L x)) (d x) (tr x) 0 (lam x) (y x) (tri (min (a x) (b x)) (max (a x) (b x))) κ).sum := by fun_prop
  exact unary_congr h2 fun x => by rw [capG, sum_range_eq_list]

/-- What the rectangles cost is given in unary. -/
theorem priceL_unary {p d lam y : α → ℕ} {tr : α → Bool} (hp : Unary p) (hd : Unary d) (ht : PolyT tr) (hl : Unary lam) (hy : PolyT y) :
    Unary fun x => priceG (listsAsPieces (L x)) (p x) (d x) (tr x) 0 (lam x) (y x) := by
  have h1 : Unary fun q : α × ℕ => (listsAsPieces (L q.1)).cap (tr q.1) 0 (lam q.1) (digit ((L q.1).1.length - 1) (y q.1) q.2) :=
    capL_unary (L := fun q : α × ℕ => L q.1) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have h2 : Unary fun x => 2 * ((List.range (nRectG (p x) (d x))).map fun q => (listsAsPieces (L x)).cap (tr x) 0 (lam x) (digit ((L x).1.length - 1) (y x) q)).sum := by fun_prop
  exact unary_congr h2 fun x => by rw [priceG, sum_range_eq_list]; rfl

/-- The total of the network of a pattern is given in unary. -/
@[fun_prop] theorem totalL_unary {p d lam y : α → ℕ} {tr : α → Bool} (hp : Unary p) (hd : Unary d) (ht : PolyT tr) (hl : Unary lam) (hy : PolyT y) :
    Unary fun x => totalG (listsAsPieces (L x)) (p x) (d x) (tr x) 0 (lam x) (y x) := by
  have := priceL_unary hL hp hd ht hl hy
  unfold totalG; fun_prop

end Lists

/-! ### A chunk whose number is given in binary -/

/-- The digits of y beyond its length are 0. -/
theorem digit_eq_zero (n y r : ℕ) (h : (Nat.bits y).length ≤ r) : digit n y r = 0 := by
  unfold digit
  rcases n with _ | n
  · simp [Nat.mod_one]
  · have h1 : y < (n + 1 + 1) ^ r := calc
      y < 2 ^ y.size := Nat.lt_size_self y
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by rw [← Nat.size_eq_bits_len]; exact h)
      _ ≤ (n + 1 + 1) ^ r := Nat.pow_le_pow_left (by omega) r
    rw [Nat.div_eq_of_lt h1, Nat.zero_mod]

/-- From the place (number of binary digits of y) on, all chunks have the same length. -/
theorem lenG_tail (P : PiecesF) (d : ℕ) (tr : Bool) (h lam y q k : ℕ) (hk : (Nat.bits y).length ≤ k) : lenG P d tr h lam y q k = lenG P d tr h lam y q (Nat.bits y).length := by
  unfold lenG digG rectIxG
  cases tr
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [digit_eq_zero _ _ _ (by omega), digit_eq_zero _ _ _ (by omega)]
  · simp only [↓reduceIte]
    rcases Nat.eq_zero_or_pos (c2 d) with h0 | h0
    · rw [h0]; simp
    · rw [digit_eq_zero _ _ _ (le_trans hk (le_trans (Nat.le_mul_of_pos_right _ h0) (Nat.le_add_right _ _))), digit_eq_zero _ _ _ (le_trans (Nat.le_mul_of_pos_right _ h0) (Nat.le_add_right _ _))]

/-- The sum of the first κ of numbers that are constant from the place m on. -/
theorem sum_range_tail (n : ℕ → ℕ) (m κ : ℕ) (h : ∀ k, m ≤ k → n k = n m) : ∑ i ∈ Finset.range κ, n i = ((List.range (min κ m)).map n).sum + (κ - m) * n m := by
  rw [← sum_range_eq_list]
  rcases le_total κ m with h1 | h1
  · rw [min_eq_left h1, Nat.sub_eq_zero_of_le h1, Nat.zero_mul, Nat.add_zero]
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h1
    rw [min_eq_right h1, Nat.add_sub_cancel_left, Finset.sum_range_add, Finset.sum_congr rfl fun i _ => h (m + i) (Nat.le_add_right _ _), Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- Drop and take, for a number of terms given in unary. -/
theorem dropTake_polyT {n : α → ℕ → ℕ} {k a b : α → ℕ} {w : α → List Bool} (hn : PolyT fun p : α × ℕ => n p.1 p.2) (hk : Unary k) (ha : PolyT a) (hb : PolyT b) (hw : PolyT w) :
    PolyT fun x => ((w x).drop (((List.range (k x)).map (n x)).sum + a x)).take (b x) := by
  have := hk.poly
  fun_prop

/-- A chunk of a word, for lengths that are constant from a place given in unary on; the number of
the chunk may be given in binary. -/
theorem chunkAt_polyT_tail {n : α → ℕ → ℕ} {m κ : α → ℕ} {w : α → List Bool} (hn : PolyT fun p : α × ℕ => n p.1 p.2) (hm : Unary m) (hκ : PolyT κ) (hw : PolyT w)
    (h : ∀ x k, m x ≤ k → n x k = n x (m x)) : PolyT fun x => chunkAt (n x) (κ x) (w x) := by
  have hm' := hm.poly
  have h1 : PolyT fun x => n x (κ x) := PolyT.comp₂ hn (by fun_prop) hκ
  have h2 : PolyT fun x => n x (m x) := PolyT.comp₂ hn (by fun_prop) hm'
  exact (dropTake_polyT (k := fun x => min (κ x) (m x)) (a := fun x => (κ x - m x) * n x (m x)) hn (unary_min_right hκ hm) (by fun_prop) h1 hw).congr fun x => by
    rw [chunkAt, sum_range_tail (n x) (m x) (κ x) (h x)]

/-- The chunk of a rectangle in a label, jointly in the lists, for every number of a rectangle. -/
@[fun_prop] theorem chunkL_polyT {L : α → Lists} {d lam y q κ : α → ℕ} {tr : α → Bool} {w : α → List Bool} (hL : PolyT L) (hd : PolyT d) (ht : PolyT tr) (hl : Unary lam) (hy : PolyT y) (hq : PolyT q)
    (hκ : PolyT κ) (hw : PolyT w) : PolyT fun x => chunkAt (lenG (listsAsPieces (L x)) (d x) (tr x) 0 (lam x) (y x) (q x)) (κ x) (w x) :=
  chunkAt_polyT_tail (n := fun x => lenG (listsAsPieces (L x)) (d x) (tr x) 0 (lam x) (y x) (q x)) (m := fun x => (Nat.bits (y x)).length)
    (lenL_unary (L := fun p : α × ℕ => L p.1) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)).poly
    (Unary.of_length (by fun_prop)) hκ hw fun x k hk => lenG_tail _ _ _ _ _ _ _ _ hk

end ExplicitCost
