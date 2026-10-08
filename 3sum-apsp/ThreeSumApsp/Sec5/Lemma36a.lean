/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements

/-!
# Lemma 36(a)

Lemma 36(a) reduces the (min,+)-product, APSP and Exact Triangle with real inputs to `Õ(n/d)`
counting calls, each of `d` comparison counts, and `Õ(n³/d)` further time.  The randomized search
behind it is cited from [CVX22].  The sentence on APSP, "by successive squaring of the weight
matrix, performing ⌈log₂ n⌉ such products", is `theorem_21b_repeated_squaring`, which covers real
weights.  This file proves the other parts that the paper argues itself.
* Fredman's trick (`fredman_trick`, `fredman_trick_le`).
* From the problems to predecessors and successors among the `d` sums of a block.  Exact Triangle:
  `lemma_36a_exact_triangle`.  For the (min,+)-product, `C[i,j]` is chosen below all sums
  (`lemma_36a_min_plus_below`); then its successor is the smallest sum of the block
  (`lemma_36a_min_plus_successor`), and the product is the entrywise minimum over the blocks
  (`lemma_36a_min_plus_blocks`), which are `n/d` blocks of `n²` entries
  (`Lemma36a.mul_sq_eq_cube_div`).
* A counting call is `d` comparison counts.  Its lists have at most `d` numbers
  (`lemma_36a_valid`) and at most one number of each color (`lemma_36a_colors`), so a comparison
  count is a number of colors (Section 5.2, `comparisonCount_eq_card_colors`), and by Fredman's
  trick it is the count that the call asks for (`lemma_36a_count`).  The pair sets have `n²`
  elements in all (`lemma_36a_pairs`), and forming the lists costs `O(nd²)` subtractions
  (`lemma_36a_subtractions`).
-/

public section

namespace ThreeSumApsp

open Finset Asymptotics Filter
open ComparisonCounts

/-! ### Fredman's trick -/

/-- Section 5.2, Fredman's trick: "a' + b' < a + b if and only if a' - a < b - b'". -/
theorem fredman_trick (a a' b b' : ℝ) : a' + b' < a + b ↔ a' - a < b - b' := by
  constructor <;> intro h <;> linarith

/-- Fredman's trick with "≤ in place of <" (Lemma 36). -/
theorem fredman_trick_le (a a' b b' : ℝ) : a' + b' ≤ a + b ↔ a' - a ≤ b - b' := by
  constructor <;> intro h <;> linarith

/-- Fredman's trick for either comparison. -/
theorem ComparisonCounts.Cmp.fredman (cmp : Cmp) (a a' b b' : ℝ) :
    cmp.Holds (a' + b') (a + b) ↔ cmp.Holds (a' - a) (b - b') := by
  cases cmp
  · exact fredman_trick a a' b b'
  · exact fredman_trick_le a a' b b'

/-! ### Predecessors and successors in the blocks -/

/-- Proof of Lemma 36(a): "For Exact Triangle, A[i,k] := w(i,k), B[k,j] := w(k,j), and
C[i,j] := -w(i,j), and there is a triangle of weight zero if and only if, in some block, some C[i,j]
is its own predecessor." The instance has n = b * d vertices per part; A is cut into b blocks of d
consecutive columns and B into the corresponding blocks of d consecutive rows.  In the notation of
Section 3.2, i, k, j run over the parts A, B, C of the instance. -/
theorem lemma_36a_exact_triangle {b d : ℕ} (T : TriangleInstance ℝ (b * d)) :
    T.HasZeroTriangle ↔
      ∃ (p : Fin b) (i j : Fin (b * d)),
        IsPredecessor
          (fun k : Fin d =>
            blockOfCols (fun i k => T.wAB i k) p i k + blockOfRows (fun k j => T.wBC k j) p k j)
          (-T.wAC i j) (-T.wAC i j) := by
  constructor
  · rintro ⟨i, k, j, hzero⟩
    obtain ⟨⟨p, k'⟩, rfl⟩ := finProdFinEquiv.surjective k
    exact ⟨p, i, j, ⟨k', eq_neg_of_add_eq_zero_left hzero⟩, le_rfl, fun _ h => h⟩
  · rintro ⟨p, i, j, ⟨k, hk⟩, -, -⟩
    exact ⟨i, finProdFinEquiv (p, k), j, add_eq_zero_iff_eq_neg.2 hk⟩

/-- Proof of Lemma 36(a): "For the (min,+)-product of A and B, we take every C[i,j] smaller
than all the sums, for instance C[i,j] := min_k A[i,k] + min_k B[k,j] - 1."  `rowMin i` is min_k
A[i,k] and `colMin j` is min_k B[k,j]. -/
theorem lemma_36a_min_plus_below {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (rowMin colMin : Fin n → ℝ) (hrow : ∀ i, IsLeast (Set.range fun k => A i k) (rowMin i))
    (hcol : ∀ j, IsLeast (Set.range fun k => B k j) (colMin j)) (i j k : Fin n) :
    rowMin i + colMin j - 1 < A i k + B k j := by
  have hA : rowMin i ≤ A i k := (hrow i).2 ⟨k, rfl⟩
  have hB : colMin j ≤ B k j := (hcol j).2 ⟨k, rfl⟩
  linarith

/-- Proof of Lemma 36(a): "Then the successor of C[i,j] in a block is the smallest sum of
the block". `sums` are the d sums of the block and `c` is a number smaller than all of them. -/
theorem lemma_36a_min_plus_successor {d : ℕ} (sums : Fin d → ℝ) (c : ℝ) (hc : ∀ k, c < sums k)
    (v : ℝ) : IsSuccessor sums c v ↔ IsLeast (Set.range sums) v := by
  constructor
  · rintro ⟨hv, -, hmin⟩
    exact ⟨hv, Set.forall_mem_range.2 fun k => hmin k (hc k)⟩
  · rintro ⟨⟨k, rfl⟩, hmin⟩
    exact ⟨⟨k, rfl⟩, hc k, fun k' _ => hmin ⟨k', rfl⟩⟩

/-- Proof of Lemma 36(a): "and the product is the entrywise minimum over the n/d blocks".
`M p` is the matrix of the smallest sums of block `p`, that is, the (min,+)-product of the p-th
blocks. -/
theorem lemma_36a_min_plus_blocks {b d : ℕ} (A B C : Matrix (Fin (b * d)) (Fin (b * d)) ℝ)
    (M : Fin b → Matrix (Fin (b * d)) (Fin (b * d)) ℝ)
    (hM : ∀ p, IsMinPlusProduct (blockOfCols A p) (blockOfRows B p) (M p)) :
    IsMinPlusProduct A B C ↔ ∀ i j, IsLeast (Set.range fun p => M p i j) (C i j) := by
  refine forall₂_congr fun i j => ⟨?_, ?_⟩
  · rintro ⟨⟨k, hk⟩, hle⟩
    -- every `M p i j` is one of the sums, so it is at least `C i j`
    have hCM (p : Fin b) : C i j ≤ M p i j := by
      obtain ⟨k', hk'⟩ := (hM p i j).1
      exact (hle _).trans_eq hk'.symm
    -- the block that contains the index `k` of the smallest sum has this sum as its smallest sum
    obtain ⟨⟨p, k'⟩, rfl⟩ := finProdFinEquiv.surjective k
    exact ⟨⟨p, le_antisymm (((hM p i j).2 k').trans_eq hk.symm) (hCM p)⟩,
      Set.forall_mem_range.2 hCM⟩
  · rintro ⟨⟨p, hp⟩, hle⟩
    -- `C i j = M p i j` is a sum of block `p`, and every sum is at least the minimum of its block
    refine ⟨?_, fun k => ?_⟩
    · obtain ⟨k', hk'⟩ := (hM p i j).1
      exact ⟨finProdFinEquiv (p, k'), hp.symm.trans hk'⟩
    · obtain ⟨⟨q, k'⟩, rfl⟩ := finProdFinEquiv.surjective k
      exact (hle ⟨q, rfl⟩).trans ((hM q i j).2 k')

/-- Proof of Lemma 36(a): "the entrywise minimum over the n/d blocks, which costs O(n³/d)
comparisons", and "Over the n/d pairs (A',B') ... Õ(n³/d) additional time" (Õ(n²) for each pair).
Here n = b * d: b blocks times n² entries is n³/d. -/
theorem Lemma36a.mul_sq_eq_cube_div (b d : ℕ) (hd : 1 ≤ d) :
    (b : ℝ) * ((b * d : ℕ) : ℝ) ^ 2 = ((b * d : ℕ) : ℝ) ^ 3 / d := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  push_cast
  field_simp

/-! ### The list of the elements of a subset of `[d]` -/

namespace ComparisonCounts

/-- The list of the elements of `S` has no repetitions. -/
theorem nodup_listOf {d : ℕ} (S : Finset (Fin d)) : (listOf S).Nodup :=
  (List.nodup_finRange d).filter _

/-- The list of the elements of `S` contains exactly the elements of `S`. -/
theorem mem_listOf {d : ℕ} (S : Finset (Fin d)) (k : Fin d) : k ∈ listOf S ↔ k ∈ S := by
  simp [listOf]

/-- The list of the elements of `S` has `|S|` entries. -/
theorem length_listOf {d : ℕ} (S : Finset (Fin d)) : (listOf S).length = S.card := by
  rw [← List.toFinset_card_of_nodup (nodup_listOf S)]
  congr 1
  ext k
  simp [mem_listOf]

/-- The list of the elements of `S` has at most `d` entries. -/
theorem length_listOf_le {d : ℕ} (S : Finset (Fin d)) : (listOf S).length ≤ d := by
  rw [length_listOf]
  simpa using S.card_le_univ

/-! ### Comparison counts -/

/-- `n` row lists and `n` column lists of at most `d` numbers contain at most `2nd` numbers. -/
theorem Lists.Valid.sum_length_le {n d : ℕ} {Ls : Lists n d} (hLs : Ls.Valid) :
    ∑ r, (Ls.row r).length + ∑ c, (Ls.col c).length ≤ 2 * n * d :=
  calc ∑ r, (Ls.row r).length + ∑ c, (Ls.col c).length
      ≤ ∑ _r : Fin n, d + ∑ _c : Fin n, d :=
        add_le_add (sum_le_sum fun r _ => hLs.1 r) (sum_le_sum fun c _ => hLs.2 c)
    _ = 2 * n * d := by
        simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
        ring

end ComparisonCounts

/-- In a list with at most one number of each color, the color determines the place. -/
private theorem place_eq_of_color_eq {d : ℕ} {l : List (ℝ × Fin d)}
    (hnodup : (l.map Prod.snd).Nodup) (i j : Fin l.length) (hij : (l.get i).2 = (l.get j).2) :
    i = j := by
  have hi : i.1 < (l.map Prod.snd).length := by simp
  have hj : j.1 < (l.map Prod.snd).length := by simp
  exact Fin.ext ((hnodup.getElem_inj_iff (hi := hi) (hj := hj)).1 (by simpa using hij))

open Classical in
/-- Section 5.2: "In the comparison counts of Lemma 36(a), every list has at most one number of each
color, so that γ(r,c) is the number of colors k with A[r,k] < B[k,c], where A[r,k] is the number of
color k in R_r and B[k,c] the one in C_c (a color missing from either list is skipped)".  The
bijection sends a pair of places of the same color to that color. -/
theorem comparisonCount_eq_card_colors {n d : ℕ} (cmp : Cmp) (Ls : Lists n d)
    (hrow : ∀ r, ((Ls.row r).map Prod.snd).Nodup) (hcol : ∀ c, ((Ls.col c).map Prod.snd).Nodup)
    (r c : Fin n) :
    comparisonCount cmp Ls r c =
      (univ.filter fun k : Fin d =>
        ∃ x y : ℝ, (x, k) ∈ Ls.row r ∧ (y, k) ∈ Ls.col c ∧ cmp.Holds x y).card := by
  refine card_bij (fun p _ => ((Ls.row r).get p.1).2) ?_ ?_ ?_
  · intro p hp
    obtain ⟨hcolor, hholds⟩ := (mem_filter.1 hp).2
    refine mem_filter.2 ⟨mem_univ _, _, _, List.get_mem _ p.1, ?_, hholds⟩
    rw [show ((Ls.row r).get p.1).2 = ((Ls.col c).get p.2).2 from hcolor]
    exact List.get_mem _ _
  · intro p hp q hq hpq
    have hp' : ((Ls.row r).get p.1).2 = ((Ls.col c).get p.2).2 := (mem_filter.1 hp).2.1
    have hq' : ((Ls.row r).get q.1).2 = ((Ls.col c).get q.2).2 := (mem_filter.1 hq).2.1
    exact Prod.ext (place_eq_of_color_eq (hrow r) _ _ hpq)
      (place_eq_of_color_eq (hcol c) _ _ (by rw [← hp', ← hq', hpq]))
  · intro k hk
    obtain ⟨x, y, hx, hy, hxy⟩ := (mem_filter.1 hk).2
    obtain ⟨i, hi⟩ := List.get_of_mem hx
    obtain ⟨j, hj⟩ := List.get_of_mem hy
    refine ⟨(i, j), mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, ?_⟩
    · change ((Ls.row r).get i).2 = ((Ls.col c).get j).2
      rw [hi, hj]
    · change cmp.Holds ((Ls.row r).get i).1 ((Ls.col c).get j).1
      rwa [hi, hj]
    · change ((Ls.row r).get i).2 = k
      rw [hi]

/-! ### A counting call is `d` comparison counts -/

/-- Lemma 36(a): the comparison counts of a counting call have "n row lists and n column
lists of at most d numbers". -/
theorem lemma_36a_valid {n d : ℕ} (A' : Matrix (Fin n) (Fin d) ℝ) (B' : Matrix (Fin d) (Fin n) ℝ)
    (S : Finset (Fin d)) (k : Fin d) : (lists41 A' B' S k).Valid := by
  constructor <;> intro _ <;> simpa [lists41] using length_listOf_le S

/-- Lemma 36(a): "with at most one number of each color in a list". -/
theorem lemma_36a_colors {n d : ℕ} (A' : Matrix (Fin n) (Fin d) ℝ) (B' : Matrix (Fin d) (Fin n) ℝ)
    (S : Finset (Fin d)) (k : Fin d) :
    (∀ i, (((lists41 A' B' S k).row i).map Prod.snd).Nodup) ∧
      (∀ j, (((lists41 A' B' S k).col j).map Prod.snd).Nodup) := by
  constructor <;> intro _ <;> simpa [lists41, Function.comp_def] using nodup_listOf S

/-- Proof of Lemma 36(a): "By Fredman's trick, A'[i,k'] + B'[k',j] < A'[i,k] + B'[k,j] if
and only if A'[i,k'] - A'[i,k] < B'[k,j] - B'[k',j] ...  Thus the count of a pair (i,j) ∈ P_k is the
comparison count γ(i,j) of these lists with P := P_k."  Also with ≤. -/
theorem lemma_36a_count {n d : ℕ} (cmp : Cmp) (A' : Matrix (Fin n) (Fin d) ℝ)
    (B' : Matrix (Fin d) (Fin n) ℝ) (pivot : Fin n → Fin n → Fin d) (S : Finset (Fin d))
    (k : Fin d) (i j : Fin n) (hij : (i, j) ∈ pairs41 pivot k) :
    count41 cmp A' B' pivot S i j = comparisonCount cmp (lists41 A' B' S k) i j := by
  classical
  have hk : pivot i j = k := (mem_filter.1 hij).2
  -- both sides count colors `k' ∈ S`, and the two conditions on `k'` agree by Fredman's trick
  rw [comparisonCount_eq_card_colors cmp _ (lemma_36a_colors A' B' S k).1
    (lemma_36a_colors A' B' S k).2, count41]
  refine congrArg card ?_
  ext k'
  simp only [mem_filter, mem_univ, true_and, lists41, List.mem_map, Prod.mk.injEq, mem_listOf, hk]
  constructor
  · rintro ⟨hS, h⟩
    exact ⟨_, _, ⟨k', hS, rfl, rfl⟩, ⟨k', hS, rfl, rfl⟩, (cmp.fredman _ _ _ _).1 h⟩
  · rintro ⟨x, y, ⟨k₁, hS, rfl, rfl⟩, ⟨k₂, -, rfl, rfl⟩, h⟩
    exact ⟨hS, (cmp.fredman _ _ _ _).2 h⟩

/-- Lemma 36(a): "with pair sets P_1, …, P_d satisfying ∑_k |P_k| = n²". -/
theorem lemma_36a_pairs {n d : ℕ} (pivot : Fin n → Fin n → Fin d) :
    ∑ k : Fin d, (pairs41 pivot k).card = n ^ 2 := by
  have hfibers := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n × Fin n)))
    (t := (univ : Finset (Fin d))) (f := fun ij => pivot ij.1 ij.2)
    (fun _ _ => mem_coe.2 (mem_univ _))
  rw [card_univ, Fintype.card_prod, Fintype.card_fin] at hfibers
  rw [sq, hfibers]
  rfl

/-- Lemma 36(a): "forming its lists costs O(nd²) subtractions" (the proof of Lemma 36: "O(nd)
subtractions for each k").  Every number in a list is formed by one subtraction, so the number of
subtractions is the total length of the lists. -/
theorem lemma_36a_subtractions {n d : ℕ} (A' : Matrix (Fin n) (Fin d) ℝ)
    (B' : Matrix (Fin d) (Fin n) ℝ) (S : Finset (Fin d)) :
    (∀ k,
        ∑ i, ((lists41 A' B' S k).row i).length + ∑ j, ((lists41 A' B' S k).col j).length
          ≤ 2 * n * d) ∧
      ∑ k : Fin d,
          (∑ i, ((lists41 A' B' S k).row i).length + ∑ j, ((lists41 A' B' S k).col j).length)
        ≤ 2 * n * d ^ 2 := by
  have hone (k : Fin d) := (lemma_36a_valid A' B' S k).sum_length_le
  refine ⟨hone, (sum_le_sum fun k _ => hone k).trans_eq ?_⟩
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  ring

end ThreeSumApsp
