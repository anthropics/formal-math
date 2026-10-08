/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec5.Lemma36a
public import Mathlib.Algebra.BigOperators.Field

/-!
# Lemma 37, after Matoušek

Comparison counts reduce to the wanted entries of one thin matrix product: `γ(r,c) = (XY)[r,c] +
γ₂(r,c)` for `(r,c) ∈ P` (`lemma_37`), where `X` and `Y` have entries in `{0,…,d}` and inner
dimension `D'' = ⌈2nd/s⌉ + d`.  The time `O(nD'' + (|P| + nds + ds²) log n)` is not stated here,
only the number of pairs that the algorithm enumerates.  The steps are the paper's.
* Sort the numbers of each color, with the tie-breaking rule (such an order exists:
  `lemma_37_order_exists`).  Then `x < y` if and only if `pos(x) < pos(y)` (`holds_iff_pos_lt`), if
  and only if `blk(x) < blk(y)`, or `blk(x) = blk(y)` and `pos(x) < pos(y)` (`holds_iff_blk_lt_or`).
* Different blocks.  There are at most `2nd` numbers (`card_item_le`), so at most `2nd/s + d ≤ D''`
  pairs (color, block) (`card_blockPairs_le`, `div_add_le_D''`), which index the columns of `X` and
  the rows of `Y` (`lemma_37_index_exists`).  Then `(XY)[r,c]` is a sum over these pairs
  (`mul_apply_eq_sum`) and counts the pairs of the first kind (`mul_apply_eq_card`).  The entries of
  `X` and `Y` are between 0 and `d` (`entry_bounds`).
* Same block.  `γ₂` counts the pairs of the second kind (`sameBlockCount_eq_card`).  A block has
  `|I| + |J| ≤ s` numbers (`card_blockItems_le`), so at most `nds + ds²` pairs are enumerated
  (`lemma_37_enumerated`).

The steps are lemmas of the namespace `Lemma37`.
-/

@[expose] public section

namespace ThreeSumApsp

open Finset Asymptotics Filter
open ComparisonCounts

/-! ### The sorted order -/

namespace Lemma37

variable {n d : ℕ}

/-- The tie-breaking rule of the sort (proof of Lemma 37).  For `<`, numbers from column lists come
first among equal numbers; for `≤`, numbers from row lists come first. -/
private def tieRank {Ls : Lists n d} : Cmp → Item Ls → ℕ
  | .lt, .inl _ => 1
  | .lt, .inr _ => 0
  | .le, .inl _ => 0
  | .le, .inr _ => 1

/-- The key by which the numbers are sorted: the number, then the tie-breaking rule, then an
arbitrary numbering of all the numbers of the lists, which breaks the remaining ties. -/
private noncomputable def key (cmp : Cmp) (Ls : Lists n d) (x : Item Ls) : ℝ ×ₗ ℕ ×ₗ ℕ :=
  toLex (x.val, toLex (tieRank cmp x, (Fintype.equivFin (Item Ls) x : ℕ)))

/-- Different numbers of the lists have different keys. -/
private theorem key_injective (cmp : Cmp) (Ls : Lists n d) : Function.Injective (key cmp Ls) := by
  intro x y h
  have hnum := congrArg (fun k => (ofLex (ofLex k).2).2) h
  simp only [key, ofLex_toLex] at hnum
  exact (Fintype.equivFin (Item Ls)).injective (Fin.ext hnum)

open Classical in
/-- The position of `x`: the number of numbers of its color with a smaller key. -/
private noncomputable def pos (cmp : Cmp) (Ls : Lists n d) (x : Item Ls) : ℕ :=
  (univ.filter fun y : Item Ls => y.color = x.color ∧ key cmp Ls y < key cmp Ls x).card

/-- Among numbers of the same color, a smaller key means a smaller position. -/
private theorem pos_lt_pos (cmp : Cmp) (Ls : Lists n d) (x y : Item Ls)
    (hc : x.color = y.color) (h : key cmp Ls x < key cmp Ls y) : pos cmp Ls x < pos cmp Ls y := by
  classical
  refine card_lt_card ((ssubset_iff_of_subset fun z hz => ?_).2
    ⟨x, mem_filter.2 ⟨mem_univ _, hc, h⟩, fun hx => lt_irrefl _ (mem_filter.1 hx).2.2⟩)
  obtain ⟨-, hcolor, hkey⟩ := mem_filter.1 hz
  exact mem_filter.2 ⟨mem_univ _, hcolor.trans hc, hkey.trans h⟩

end Lemma37

/-- Proof of Lemma 37: the sort can be carried out, that is, an order as described
exists. -/
theorem lemma_37_order_exists {n d : ℕ} (cmp : Cmp) (Ls : Lists n d) :
    Nonempty (SortedOrder cmp Ls) := by
  classical
  refine ⟨{
    pos := Lemma37.pos cmp Ls
    pos_injective := ?pos_injective
    pos_lt := ?pos_lt
    sorted := ?sorted
    ties_lt := ?ties_lt
    ties_le := ?ties_le }⟩
  case pos_injective =>
    intro x y hc h
    rcases lt_trichotomy (Lemma37.key cmp Ls x) (Lemma37.key cmp Ls y) with hlt | heq | hgt
    · exact absurd h (Lemma37.pos_lt_pos cmp Ls x y hc hlt).ne
    · exact Lemma37.key_injective cmp Ls heq
    · exact absurd h (Lemma37.pos_lt_pos cmp Ls y x hc.symm hgt).ne'
  case pos_lt =>
    intro x
    refine card_lt_card ((ssubset_iff_of_subset fun z hz => ?_).2
      ⟨x, mem_filter.2 ⟨mem_univ _, rfl⟩, fun hx => lt_irrefl _ (mem_filter.1 hx).2.2⟩)
    exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hz).2.1⟩
  case sorted =>
    intro x y hc h
    exact Lemma37.pos_lt_pos cmp Ls x y hc (Prod.Lex.toLex_lt_toLex.2 (Or.inl h))
  case ties_lt =>
    rintro rfl x y hc h
    refine Lemma37.pos_lt_pos _ Ls _ _ hc.symm (Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨h.symm, ?_⟩))
    exact Prod.Lex.toLex_lt_toLex.2 (Or.inl Nat.zero_lt_one)
  case ties_le =>
    rintro rfl x y hc h
    refine Lemma37.pos_lt_pos _ Ls _ _ hc (Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨h, ?_⟩))
    exact Prod.Lex.toLex_lt_toLex.2 (Or.inl Nat.zero_lt_one)

namespace Lemma37

variable {n d : ℕ} {cmp : Cmp} {Ls : Lists n d}

/-- Proof of Lemma 37: "For x from a row list and y from a column list of the same color,
x < y holds if and only if pos(x) < pos(y).  (For ≤, we reverse the tie-breaking rule.)" -/
theorem holds_iff_pos_lt (o : SortedOrder cmp Ls) (x : RowItem Ls) (y : ColItem Ls)
    (hxy : (Item.ofRow x).color = (Item.ofCol y).color) :
    cmp.Holds ((Item.ofRow x).val) ((Item.ofCol y).val) ↔
      o.pos (Item.ofRow x) < o.pos (Item.ofCol y) := by
  cases cmp with
  | lt =>
    refine ⟨o.sorted _ _ hxy, fun h => lt_of_not_ge fun hle => ?_⟩
    rcases hle.lt_or_eq with hlt | heq
    · exact (o.sorted _ _ hxy.symm hlt).asymm h
    · exact (o.ties_lt rfl x y hxy heq.symm).asymm h
  | le =>
    refine ⟨fun h => ?_, fun h => le_of_not_gt fun hlt => (o.sorted _ _ hxy.symm hlt).asymm h⟩
    rcases (show (Item.ofRow x).val ≤ (Item.ofCol y).val from h).lt_or_eq with hlt | heq
    · exact o.sorted _ _ hxy hlt
    · exact o.ties_le rfl x y hxy heq

/-- Proof of Lemma 37: "Then x < y holds if and only if either blk(x) < blk(y), or blk(x) =
blk(y) and pos(x) < pos(y)." -/
theorem holds_iff_blk_lt_or (o : SortedOrder cmp Ls) (s : ℕ) (x : RowItem Ls) (y : ColItem Ls)
    (hxy : (Item.ofRow x).color = (Item.ofCol y).color) :
    cmp.Holds ((Item.ofRow x).val) ((Item.ofCol y).val) ↔
      blk o s (Item.ofRow x) < blk o s (Item.ofCol y) ∨
        (blk o s (Item.ofRow x) = blk o s (Item.ofCol y) ∧
          o.pos (Item.ofRow x) < o.pos (Item.ofCol y)) := by
  rw [holds_iff_pos_lt o x y hxy, blk, blk]
  constructor
  · intro h
    exact (Nat.div_le_div_right (c := s) h.le).lt_or_eq.imp_right fun heq => ⟨heq, h⟩
  · rintro (h | ⟨-, h⟩)
    · exact lt_of_not_ge fun hle => (Nat.div_le_div_right (c := s) hle).not_gt h
    · exact h

/-! ### Different blocks -/

/-- Proof of Lemma 37: "The lists contain at most 2nd numbers in all". -/
theorem card_item_le (hLs : Ls.Valid) : Fintype.card (Item Ls) ≤ 2 * n * d := by
  rw [Fintype.card_sum, Fintype.card_sigma, Fintype.card_sigma]
  simpa only [Fintype.card_fin] using hLs.sum_length_le

/-- The numbers of the `d` colors together are all the numbers of the lists. -/
private theorem sum_numOfColor (Ls : Lists n d) :
    ∑ k, numOfColor Ls k = Fintype.card (Item Ls) :=
  (card_eq_sum_card_fiberwise (s := (univ : Finset (Item Ls)))
    (t := (univ : Finset (Fin d))) (f := Item.color) fun _ _ => mem_coe.2 (mem_univ _)).symm

/-- A color with `N` numbers has at most `⌊N/s⌋ + 1` blocks, so there are at most
`∑_k (⌊N_k/s⌋ + 1)` pairs (color, block). -/
private theorem card_blockPairs_le_sum (o : SortedOrder cmp Ls) (s : ℕ) :
    (blockPairs o s).card ≤ ∑ k : Fin d, (numOfColor Ls k / s + 1) := by
  classical
  have hsub : blockPairs o s ⊆ (univ : Finset (Fin d)).biUnion fun k =>
      (range (numOfColor Ls k / s + 1)).image fun β => (k, β) := by
    intro kβ h
    obtain ⟨x, -, rfl⟩ := mem_image.1 h
    refine mem_biUnion.2 ⟨x.color, mem_univ _, mem_image.2 ⟨blk o s x, mem_range.2 ?_, rfl⟩⟩
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (o.pos_lt x).le)
  exact (card_le_card hsub).trans <| card_biUnion_le.trans <|
    sum_le_sum fun k _ => card_image_le.trans (by simp)

/-- Proof of Lemma 37: "so there are at most 2nd/s + d ≤ D'' pairs (color, block)", the first
inequality. -/
theorem card_blockPairs_le (hLs : Ls.Valid) (o : SortedOrder cmp Ls) (s : ℕ) :
    ((blockPairs o s).card : ℚ) ≤ (2 * n * d : ℚ) / s + d :=
  calc ((blockPairs o s).card : ℚ)
      ≤ ((∑ k : Fin d, (numOfColor Ls k / s + 1) : ℕ) : ℚ) := by
        exact_mod_cast card_blockPairs_le_sum o s
    _ = ∑ k : Fin d, (((numOfColor Ls k / s : ℕ) : ℚ) + 1) := by
        push_cast
        rfl
    _ ≤ ∑ k : Fin d, ((numOfColor Ls k : ℚ) / s + 1) :=
        sum_le_sum fun k _ => add_le_add_left Nat.cast_div_le 1
    _ = (Fintype.card (Item Ls) : ℚ) / s + d := by
        rw [sum_add_distrib, ← sum_div, ← Nat.cast_sum, sum_numOfColor]
        simp
    _ ≤ (2 * n * d : ℚ) / s + d := by
        gcongr
        exact_mod_cast card_item_le hLs

/-- Proof of Lemma 37: "2nd/s + d ≤ D''". -/
theorem div_add_le_D'' (n d s : ℕ) : (2 * n * d : ℚ) / s + d ≤ (D'' n d s : ℚ) := by
  rw [D'', Nat.cast_add]
  gcongr
  exact Nat.le_ceil _

end Lemma37

/-- Proof of Lemma 37: "and we index the columns of X and the rows of Y by the pairs": an indexing
exists. -/
theorem lemma_37_index_exists {n d : ℕ} {cmp : Cmp} {Ls : Lists n d} (hLs : Ls.Valid)
    (o : SortedOrder cmp Ls) (s : ℕ) (hs : 1 ≤ s) :
    ∃ idx : Fin d × ℕ → Fin (D'' n d s), Set.InjOn idx (blockPairs o s) := by
  classical
  have _ := hs -- the paper's hypothesis `s ≥ 1` is not needed here
  have hcard : (blockPairs o s).card ≤ D'' n d s := by
    exact_mod_cast (Lemma37.card_blockPairs_le hLs o s).trans (Lemma37.div_add_le_D'' n d s)
  -- number the pairs; the other arguments `(k, β)` go to 0, and `D'' ≥ d > k`
  refine ⟨fun kβ => if h : kβ ∈ blockPairs o s then
      Fin.castLE hcard ((blockPairs o s).equivFin ⟨kβ, h⟩)
    else ⟨0, kβ.1.pos.trans_le (Nat.le_add_left _ _)⟩, ?_⟩
  intro a ha b hb hab
  rw [mem_coe] at ha hb
  simp only [dif_pos ha, dif_pos hb] at hab
  exact congrArg Subtype.val
    ((blockPairs o s).equivFin.injective (Fin.castLE_injective hcard hab))

namespace Lemma37

variable {n d : ℕ} {cmp : Cmp} {Ls : Lists n d}

/-- The column of `X` (or row of `Y`) with the index of a pair (color, block) belongs to that pair
only. -/
private theorem sum_filter_idx (o : SortedOrder cmp Ls) (s : ℕ) (idx : Fin d × ℕ → Fin (D'' n d s))
    (hidx : Set.InjOn idx (blockPairs o s)) (f : Fin d × ℕ → ℤ) (a : Fin d × ℕ)
    (ha : a ∈ blockPairs o s) :
    ∑ kβ ∈ (blockPairs o s).filter (fun kβ => idx kβ = idx a), f kβ = f a :=
  sum_eq_single_of_mem a (mem_filter.2 ⟨ha, rfl⟩) fun _ hb hne =>
    absurd (hidx (mem_filter.1 hb).1 ha (mem_filter.1 hb).2) hne

/-- Proof of Lemma 37: "Then (XY)[r,c] = ∑_{(k,β)} X[r,(k,β)] Y[(k,β),c] ...". -/
theorem mul_apply_eq_sum (o : SortedOrder cmp Ls) (s : ℕ) (idx : Fin d × ℕ → Fin (D'' n d s))
    (hidx : Set.InjOn idx (blockPairs o s)) (r c : Fin n) :
    (matX o s idx * matY o s idx) r c =
      ∑ kβ ∈ blockPairs o s, (xCount o s r kβ.1 kβ.2 : ℤ) * (yCount o s kβ.1 kβ.2 c : ℤ) := by
  -- group the pairs (color, block) by their index `j`; column `j` belongs to one pair only
  rw [Matrix.mul_apply, ← sum_fiberwise_of_maps_to (s := blockPairs o s) (t := univ)
    (g := idx) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun j _ => ?_
  rw [matX, matY, sum_mul]
  refine sum_congr rfl fun a ha => ?_
  obtain ⟨ha', rfl⟩ := mem_filter.1 ha
  rw [sum_filter_idx o s idx hidx _ a ha']

/-- Pairs of places in `R_r` and `C_c`, grouped by the color and the block of the number in `R_r`.
-/
private theorem card_eq_sum_card_blockPairs (o : SortedOrder cmp Ls) (s : ℕ) {r c : Fin n}
    (S : Finset (Fin (Ls.row r).length × Fin (Ls.col c).length)) :
    S.card = ∑ kβ ∈ blockPairs o s, (S.filter fun p =>
      ((rowItem r p.1 : Item Ls).color, blk o s (rowItem r p.1 : Item Ls)) = kβ).card :=
  card_eq_sum_card_fiberwise fun p _ => mem_coe.2 (mem_image.2 ⟨rowItem r p.1, mem_univ _, rfl⟩)

/-- Proof of Lemma 37: "... is the number of pairs (x,y) of the same color with blk(x) <
blk(y), as required". -/
theorem mul_apply_eq_card (o : SortedOrder cmp Ls) (s : ℕ) (idx : Fin d × ℕ → Fin (D'' n d s))
    (hidx : Set.InjOn idx (blockPairs o s)) (r c : Fin n) :
    (matX o s idx * matY o s idx) r c =
      ((univ.filter fun p : Fin (Ls.row r).length × Fin (Ls.col c).length =>
        (rowItem r p.1).color = (colItem c p.2).color ∧
          blk o s (rowItem r p.1) < blk o s (colItem c p.2)).card : ℤ) := by
  classical
  -- group the pairs `(x,y)` by the color and the block of `x`
  rw [mul_apply_eq_sum o s idx hidx r c, card_eq_sum_card_blockPairs o s]
  push_cast
  refine sum_congr rfl fun kβ _ => ?_
  rw [← Nat.cast_mul, xCount, yCount, ← card_product]
  refine congrArg (fun t : Finset _ => (t.card : ℤ)) ?_
  ext p
  simp only [mem_product, mem_filter, mem_univ, true_and, Prod.ext_iff]
  constructor
  · rintro ⟨⟨hx, hβ⟩, hy, hlt⟩
    exact ⟨⟨hx.trans hy.symm, hβ ▸ hlt⟩, hx, hβ⟩
  · rintro ⟨⟨hxy, hlt⟩, hx, hβ⟩
    exact ⟨⟨hx, hβ⟩, hxy.symm.trans hx, hβ ▸ hlt⟩

/-- "the entries of X and Y are between 0 and d because a list has at most d numbers": an entry is
one of the counts, or zero (padding). -/
private theorem entry_bounds (o : SortedOrder cmp Ls) (s : ℕ) (idx : Fin d × ℕ → Fin (D'' n d s))
    (hidx : Set.InjOn idx (blockPairs o s)) (f : Fin d × ℕ → ℕ) (hf : ∀ kβ, f kβ ≤ d)
    (j : Fin (D'' n d s)) :
    0 ≤ ∑ kβ ∈ (blockPairs o s).filter (fun kβ => idx kβ = j), (f kβ : ℤ) ∧
      ∑ kβ ∈ (blockPairs o s).filter (fun kβ => idx kβ = j), (f kβ : ℤ) ≤ d := by
  by_cases h : ∃ a ∈ blockPairs o s, idx a = j
  · obtain ⟨a, ha, rfl⟩ := h
    rw [sum_filter_idx o s idx hidx (fun kβ => (f kβ : ℤ)) a ha]
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast hf a⟩
  · rw [sum_eq_zero fun b hb => absurd ⟨b, (mem_filter.1 hb).1, (mem_filter.1 hb).2⟩ h]
    exact ⟨le_rfl, Int.natCast_nonneg _⟩

/-! ### Same block -/

/-- An entry of a row list is in `blockRowItems o s kβ` if and only if it has the color and the
block of the pair `kβ`. -/
private theorem mem_blockRowItems {o : SortedOrder cmp Ls} {s : ℕ} {kβ : Fin d × ℕ}
    {x : RowItem Ls} : x ∈ blockRowItems o s kβ ↔
      (Item.ofRow x).color = kβ.1 ∧ blk o s (Item.ofRow x) = kβ.2 := by
  simp only [blockRowItems, mem_filter, mem_univ, true_and]

/-- An entry of a column list is in `blockColItems o s kβ` if and only if it has the color and the
block of the pair `kβ`. -/
private theorem mem_blockColItems {o : SortedOrder cmp Ls} {s : ℕ} {kβ : Fin d × ℕ}
    {y : ColItem Ls} : y ∈ blockColItems o s kβ ↔
      (Item.ofCol y).color = kβ.1 ∧ blk o s (Item.ofCol y) = kβ.2 := by
  simp only [blockColItems, mem_filter, mem_univ, true_and]

/-- Proof of Lemma 37: "Then γ₂ counts the pairs of the second kind", for the pairs (r,c) ∈
P. -/
theorem sameBlockCount_eq_card (o : SortedOrder cmp Ls) (s : ℕ) (P : Finset (Fin n × Fin n))
    (r c : Fin n) (hrc : (r, c) ∈ P) :
    sameBlockCount o s P r c =
      ((univ.filter fun p : Fin (Ls.row r).length × Fin (Ls.col c).length =>
        (rowItem r p.1).color = (colItem c p.2).color ∧
          blk o s (rowItem r p.1) = blk o s (colItem c p.2) ∧
          o.pos (rowItem r p.1) < o.pos (colItem c p.2)).card : ℤ) := by
  classical
  -- group the pairs `(x,y)` by the color and the block of `x`
  rw [sameBlockCount, card_eq_sum_card_blockPairs o s]
  push_cast
  refine sum_congr rfl fun kβ _ => congrArg (fun m : ℕ => (m : ℤ)) (Eq.symm ?_)
  -- a pair of places in `R_r` and `C_c` is a pair in `I × J` with row `r` and column `c`
  refine card_bij (fun p _ => ((⟨r, p.1⟩ : RowItem Ls), (⟨c, p.2⟩ : ColItem Ls))) ?_ ?_ ?_
  · simp only [mem_filter, mem_univ, true_and, mem_product, mem_blockRowItems, mem_blockColItems,
      Prod.ext_iff]
    rintro p ⟨⟨hcolor, hblk, hpos⟩, hk, hβ⟩
    exact ⟨⟨⟨hk, hβ⟩, hcolor.symm.trans hk, hblk.symm.trans hβ⟩, hpos, hrc, trivial⟩
  · intro p _ q _ hpq
    simp only [Prod.mk.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at hpq
    exact Prod.ext hpq.1 hpq.2
  · simp only [mem_filter, mem_univ, true_and, mem_product, mem_blockRowItems, mem_blockColItems,
      Prod.ext_iff]
    rintro ⟨⟨r', i⟩, ⟨c', i'⟩⟩ ⟨⟨⟨hxk, hxβ⟩, hyk, hyβ⟩, hpos, -, rfl, rfl⟩
    exact ⟨(i, i'), ⟨⟨hxk.trans hyk.symm, hxβ.trans hyβ.symm, hpos⟩, hxk, hxβ⟩, rfl, rfl⟩

/-- Proof of Lemma 37: "so that |I| + |J| ≤ s".  The positions of the numbers of a block
are different and lie among `s` consecutive positions. -/
theorem card_blockItems_le (o : SortedOrder cmp Ls) (s : ℕ) (hs : 1 ≤ s) (kβ : Fin d × ℕ) :
    (blockRowItems o s kβ).card + (blockColItems o s kβ).card ≤ s := by
  classical
  have hmem : ∀ x : Item Ls, x ∈ (blockRowItems o s kβ).disjSum (blockColItems o s kβ) →
      x.color = kβ.1 ∧ blk o s x = kβ.2 := by
    intro x hx
    rcases mem_disjSum.1 hx with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
    · exact mem_blockRowItems.1 ha
    · exact mem_blockColItems.1 hb
  have hcard : ((blockRowItems o s kβ).disjSum (blockColItems o s kβ)).card
      ≤ (Finset.Ico (s * kβ.2) (s * kβ.2 + s)).card := by
    refine card_le_card_of_injOn o.pos (fun x hx => ?_) fun x hx y hy hxy =>
      o.pos_injective x y ((hmem x hx).1.trans (hmem y hy).1.symm) hxy
    have hblk : o.pos x / s = kβ.2 := (hmem x hx).2
    have hdiv := Nat.div_add_mod (o.pos x) s
    have hmod := Nat.mod_lt (o.pos x) (show 0 < s by omega)
    rw [hblk] at hdiv
    rw [mem_coe, mem_Ico]
    omega
  simpa using hcard

end Lemma37

/-- Proof of Lemma 37: "Since |I||J| ≤ s²/4 and there are at most 2nd/s + d blocks, we
enumerate at most (2nd/s + d)s²/4 ≤ nds + ds² pairs (x,y)". -/
theorem lemma_37_enumerated {n d : ℕ} {cmp : Cmp} {Ls : Lists n d} (hLs : Ls.Valid)
    (o : SortedOrder cmp Ls) (s : ℕ) (hs : 1 ≤ s) :
    (∀ kβ, ((blockRowItems o s kβ).card * (blockColItems o s kβ).card : ℚ) ≤ (s : ℚ) ^ 2 / 4) ∧
      (enumeratedPairs o s : ℚ) ≤ ((2 * n * d : ℚ) / s + d) * (s : ℚ) ^ 2 / 4 ∧
      ((2 * n * d : ℚ) / s + d) * (s : ℚ) ^ 2 / 4 ≤ (n * d * s + d * s ^ 2 : ℚ) := by
  have hspos : (0 : ℚ) < s := by exact_mod_cast hs
  -- `4|I||J| ≤ (|I| + |J|)² ≤ s²`
  have hprod (kβ) :
      ((blockRowItems o s kβ).card * (blockColItems o s kβ).card : ℚ) ≤ (s : ℚ) ^ 2 / 4 := by
    have hsum : ((blockRowItems o s kβ).card : ℚ) + (blockColItems o s kβ).card ≤ s := by
      exact_mod_cast Lemma37.card_blockItems_le o s hs kβ
    linarith [four_mul_le_sq_add ((blockRowItems o s kβ).card : ℚ) (blockColItems o s kβ).card,
      pow_le_pow_left₀ (by positivity) hsum 2]
  refine ⟨hprod, ?_, ?_⟩
  · calc (enumeratedPairs o s : ℚ)
        = ∑ kβ ∈ blockPairs o s,
            ((blockRowItems o s kβ).card * (blockColItems o s kβ).card : ℚ) := by
          rw [enumeratedPairs]
          push_cast
          rfl
      _ ≤ ∑ _kβ ∈ blockPairs o s, (s : ℚ) ^ 2 / 4 := sum_le_sum fun kβ _ => hprod kβ
      _ = ((blockPairs o s).card : ℚ) * ((s : ℚ) ^ 2 / 4) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ((2 * n * d : ℚ) / s + d) * ((s : ℚ) ^ 2 / 4) := by
          gcongr
          exact Lemma37.card_blockPairs_le hLs o s
      _ = ((2 * n * d : ℚ) / s + d) * (s : ℚ) ^ 2 / 4 := by ring
  · calc ((2 * n * d : ℚ) / s + d) * (s : ℚ) ^ 2 / 4 = n * d * s / 2 + d * s ^ 2 / 4 := by
          field_simp
          ring
      _ ≤ (n * d * s + d * s ^ 2 : ℚ) := by
          have hfirst : (0 : ℚ) ≤ n * d * s := by positivity
          have hsecond : (0 : ℚ) ≤ d * s ^ 2 := by positivity
          linarith

/-! ### Lemma 37 -/

/-- **Lemma 37** (after Matoušek), the part that is not a running time.  "Let s ≥ 1 be an
integer and D'' := ⌈2nd/s⌉ + d.  Given row lists R_r and column lists C_c as above and a set P ⊆
[n]², we can build matrices X ∈ {0,…,d}^{n×D''} and Y ∈ {0,…,d}^{D''×n} and compute integers
γ₂(r,c), (r,c) ∈ P, with γ(r,c) = (XY)[r,c] + γ₂(r,c) for every (r,c) ∈ P ...  The same holds with ≤
in place of < in the definition of γ." The matrices and the integers γ₂ depend on the real numbers
only through the positions `o.pos`, in accordance with "The only operations on real numbers are the
comparisons made when sorting the numbers of each color." -/
theorem lemma_37 {n d : ℕ} (cmp : Cmp) (Ls : Lists n d) (hLs : Ls.Valid) (s : ℕ) (hs : 1 ≤ s)
    (P : Finset (Fin n × Fin n)) (o : SortedOrder cmp Ls) (idx : Fin d × ℕ → Fin (D'' n d s))
    (hidx : Set.InjOn idx (blockPairs o s)) :
    (∀ r j, 0 ≤ matX o s idx r j ∧ matX o s idx r j ≤ d) ∧
      (∀ j c, 0 ≤ matY o s idx j c ∧ matY o s idx j c ≤ d) ∧
      ∀ r c, (r, c) ∈ P →
        (comparisonCount cmp Ls r c : ℤ) =
          (matX o s idx * matY o s idx) r c + sameBlockCount o s P r c := by
  classical
  have _ := hs -- the paper's hypothesis `s ≥ 1` is needed only for the number of enumerated pairs
  refine ⟨fun r j => ?_, fun j c => ?_, fun r c hrc => ?_⟩
  · refine Lemma37.entry_bounds o s idx hidx (fun kβ => xCount o s r kβ.1 kβ.2) (fun kβ => ?_) j
    exact (card_le_univ _).trans (by simpa using hLs.1 r)
  · refine Lemma37.entry_bounds o s idx hidx (fun kβ => yCount o s kβ.1 kβ.2 c) (fun kβ => ?_) j
    exact (card_le_univ _).trans (by simpa using hLs.2 c)
  · -- a pair `x < y` of the same color is of the first kind or of the second kind, and not of both
    rw [Lemma37.mul_apply_eq_card o s idx hidx r c, Lemma37.sameBlockCount_eq_card o s P r c hrc,
      ← Nat.cast_add, ← card_union_of_disjoint, ← filter_or, comparisonCount]
    · refine congrArg (fun t : Finset _ => (t.card : ℤ)) (filter_congr fun p _ => ?_)
      rw [← and_or_left]
      exact and_congr_right fun hcolor => Lemma37.holds_iff_blk_lt_or o s ⟨r, p.1⟩ ⟨c, p.2⟩ hcolor
    · rw [disjoint_filter]
      rintro p - ⟨-, hlt⟩ ⟨-, heq, -⟩
      exact hlt.ne heq

end ThreeSumApsp
