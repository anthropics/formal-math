/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Count

/-!
# Lists: entries with a default, blocks, sums, counting, sorted lists

General facts about lists. Arrays are lists here, and entry `i` of a list is `l.getD i d`. The
sections:

* Entries with a default: `getD` of a list that was appended to, cut, tabulated, mapped or changed
  in one place.
* Blocks: `(List.range n).flatMap f` puts the blocks `f 0, …, f (n - 1)` one after the other. Where
  an entry of a block stands, for blocks of any lengths and for blocks of one length.
* Sums: partial sums, the triangle inequality, and the sum over a list that enumerates the image of
  a finite set.
* A running minimum.
* Counting: how often a value occurs among the first entries of a list, or among the values of a
  function on `Fin n`; the list of the `j < n` with a property.
* Sorted lists: what `dropWhile` and `takeWhile` leave of a strictly increasing list; first
  occurrences in a weakly increasing list.
* Two notions of this project: `AbsLe l U` says that all members of `l` have absolute value at most
  `U`, and `sumLists` is the entrywise sum of lists of one length.
-/

@[expose] public section

namespace List

variable {α β : Type*}

/-! ## Entries with a default -/

/-- What holds for the default and for every member of a list holds for every `getD`. -/
theorem getD_of_forall_mem {p : α → Prop} {l : List α} {d : α} (hd : p d) (h : ∀ x ∈ l, p x)
    (i : ℕ) : p (l.getD i d) := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem l d hi]
    exact h _ (List.getElem_mem hi)
  · rwa [List.getD_eq_default l d hi]

/-- Entry `j` of the second of two lists put together. -/
theorem getD_append_add (l l' : List α) (j : ℕ) (d : α) :
    (l ++ l').getD (l.length + j) d = l'.getD j d := by
  rw [List.getD_append_right l l' d _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- Entry `j` of a list without its first `a` entries. -/
theorem getD_drop (l : List α) (a j : ℕ) (d : α) : (l.drop a).getD j d = l.getD (a + j) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- Entry `j < n` of the first `n` entries. -/
theorem getD_take_of_lt (l : List α) {n j : ℕ} (hj : j < n) (d : α) :
    (l.take n).getD j d = l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]

/-- Entry `i < n` of the table `f 0, …, f (n - 1)`. -/
theorem getD_map_range (f : ℕ → α) {n i : ℕ} (hi : i < n) (d : α) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

/-- Entry `i < l.length` of `l.map f`, whatever the two defaults. Mathlib's `List.getD_map` is for
all `i`, with the default `f d`. -/
theorem getD_map_of_lt (f : α → β) {l : List α} {i : ℕ} (hi : i < l.length) (d : α) (d' : β) :
    (l.map f).getD i d' = f (l.getD i d) := by
  rw [List.getD_eq_getElem _ _ (by rwa [List.length_map]), List.getD_eq_getElem _ _ hi,
    List.getElem_map]

/-- The entries of a list in which entry `q < l.length` was replaced by `a`. -/
theorem getD_set_of_lt {l : List α} {q : ℕ} (hq : q < l.length) (a d : α) (q' : ℕ) :
    (l.set q a).getD q' d = if q' = q then a else l.getD q' d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs with h1 h2 h3
  · rfl
  · exact absurd h1.symm h2
  · exact absurd (h3 ▸ hq) (by omega)
  · rfl

/-- One more member at the end changes the entry number `l.length` only. -/
theorem getD_append_singleton (l : List α) (a d : α) :
    (fun e => (l ++ [a]).getD e d) = Function.update (fun e => l.getD e d) l.length a := by
  funext e
  rcases Nat.lt_trichotomy e l.length with he | rfl | he
  · rw [Function.update_of_ne he.ne, List.getD_append _ _ _ _ he]
  · rw [Function.update_self, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self,
      List.getD_cons_zero]
  · rw [Function.update_of_ne he.ne', List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ he.le]

/-- The first `i + 1` entries are the first `i` entries and entry `i`. -/
theorem take_succ_getD (l : List α) {i : ℕ} (hi : i < l.length) (d : α) :
    l.take (i + 1) = l.take i ++ [l.getD i d] := by
  rw [List.take_add_one, List.getD_eq_getElem l d hi, List.getElem?_eq_getElem hi,
    Option.toList_some]

/-! ## Blocks one after the other -/

/-- Blocks of any lengths: entry `o` of block `r` stands after the blocks `0, …, r - 1`. -/
theorem getD_flatMap_range_sum (f : ℕ → List α) {n r o : ℕ} (hr : r < n) (ho : o < (f r).length)
    (d : α) :
    ((List.range n).flatMap f).getD (((List.range r).map fun s => (f s).length).sum + o) d =
      (f r).getD o d := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hr
  rw [Nat.add_assoc, List.range_add, List.flatMap_append, ← List.length_flatMap, getD_append_add,
    Nat.add_comm c 1, List.range_add, List.map_append, List.flatMap_append,
    List.getD_append _ _ _ _ (by simpa using ho)]
  simp

/-- The length of `n` blocks of length `k`. -/
theorem length_flatMap_range {k : ℕ} (n : ℕ) (f : ℕ → List α) (hf : ∀ z < n, (f z).length = k) :
    ((List.range n).flatMap f).length = n * k := by
  rw [List.length_flatMap,
    List.map_congr_left (g := fun _ => k) fun z hz => hf z (List.mem_range.1 hz)]
  simp

/-- Blocks of length `k`: entry `r` of block `z` has the index `z * k + r`. -/
theorem getD_flatMap_range {k n : ℕ} (f : ℕ → List α) (hf : ∀ z < n, (f z).length = k) {z r : ℕ}
    (hz : z < n) (hr : r < k) (d : α) :
    ((List.range n).flatMap f).getD (z * k + r) d = (f z).getD r d := by
  rw [← length_flatMap_range z f fun s hs => hf s (hs.trans hz), List.length_flatMap]
  exact getD_flatMap_range_sum f hz (hf z hz ▸ hr) d

/-- The length of `n` blocks of length `k`, numbered by `Fin n`. -/
theorem length_flatMap_finRange {n k : ℕ} (f : Fin n → List α) (hf : ∀ i, (f i).length = k) :
    ((List.finRange n).flatMap f).length = n * k := by
  simp [List.length_flatMap, hf]

/-- Blocks of length `k`, numbered by `Fin n`: entry `r` of block `i` has the index `i * k + r`. -/
theorem getD_flatMap_finRange {n k : ℕ} (f : Fin n → List α) (hf : ∀ i, (f i).length = k)
    (i : Fin n) {r : ℕ} (hr : r < k) (d : α) :
    ((List.finRange n).flatMap f).getD ((i : ℕ) * k + r) d = (f i).getD r d := by
  have hrange : (List.finRange n).flatMap f =
      (List.range n).flatMap fun z => if h : z < n then f ⟨z, h⟩ else [] := by
    rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
    exact List.flatMap_congr fun j _ => by simp
  rw [hrange, getD_flatMap_range _ (fun z hz => by simp [hz, hf]) i.isLt hr]
  simp

/-- A run of `n` blocks, cut out of a list of blocks of length `k`. -/
theorem take_drop_flatMap_range {k : ℕ} (m n c : ℕ) (f : ℕ → List α)
    (hf : ∀ z < m + n + c, (f z).length = k) :
    (((List.range (m + n + c)).flatMap f).drop (m * k)).take (n * k) =
      (List.range n).flatMap fun z => f (m + z) := by
  have hm : ((List.range m).flatMap f).length = m * k :=
    length_flatMap_range m f fun z hz => hf z (by omega)
  have hn : ((List.range n).flatMap fun z => f (m + z)).length = n * k :=
    length_flatMap_range n _ fun z hz => hf _ (by omega)
  rw [List.range_add, List.range_add, List.flatMap_append, List.flatMap_append, List.append_assoc,
    List.flatMap_map, ← hm, List.drop_left, ← hn, List.take_left]

/-- An entrywise operation on two lists of blocks of one length works block by block. -/
theorem zipWith_flatMap_range {γ : Type*} {k : ℕ} (g : α → β → γ) (n : ℕ) (f : ℕ → List α)
    (f' : ℕ → List β) (hf : ∀ z, (f z).length = k) (hf' : ∀ z, (f' z).length = k) :
    List.zipWith g ((List.range n).flatMap f) ((List.range n).flatMap f') =
      (List.range n).flatMap fun z => List.zipWith g (f z) (f' z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlen : ((List.range n).flatMap f).length = ((List.range n).flatMap f').length := by
      rw [length_flatMap_range n f fun z _ => hf z, length_flatMap_range n f' fun z _ => hf' z]
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, List.flatMap_append,
      List.zipWith_append hlen, ih]
    simp

/-- Blocks of length at most `c`, one for each member of `l`, have length at most `l.length * c`
in all. -/
theorem length_flatMap_le (l : List α) (f : α → List β) (c : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ c) : (l.flatMap f).length ≤ l.length * c := by
  rw [List.length_flatMap]
  simpa using List.sum_le_card_nsmul (l.map fun a => (f a).length) c (by simpa using h)

/-! ## Sums -/

/-- The sum of the table `f 0, …, f (n - 1)` is the sum over `Finset.range n`. For a sum over
`Fin n` go on with `Finset.sum_range`. -/
theorem sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i :=
  rfl

/-- Partial sums of natural numbers grow. -/
theorem sum_map_range_mono (g : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) :
    ((List.range a).map g).sum ≤ ((List.range b).map g).sum := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

/-- One more term of a partial sum; beyond the end of the list the term is `0`. Within the list,
`List.sum_take_succ` has `l[j]` in place of `l.getD j 0`. -/
theorem sum_take_succ_getD {M : Type*} [AddMonoid M] (l : List M) (j : ℕ) :
    (l.take (j + 1)).sum = (l.take j).sum + l.getD j 0 := by
  rcases Nat.lt_or_ge j l.length with hj | hj
  · rw [List.sum_take_succ l j hj, List.getD_eq_getElem l 0 hj]
  · rw [List.getD_eq_default l 0 hj, List.take_of_length_le hj,
      List.take_of_length_le (Nat.le_succ_of_le hj), add_zero]

/-- One more term of a partial sum of the table `f 0, …, f (n - 1)`. -/
theorem sum_take_map_range_succ {M : Type*} [AddMonoid M] (f : ℕ → M) {n j : ℕ} (hj : j < n) :
    (((List.range n).map f).take (j + 1)).sum = (((List.range n).map f).take j).sum + f j := by
  rw [sum_take_succ_getD, getD_map_range f hj]

/-- A sum over a concatenation of lists is the sum of the sums over the lists. -/
theorem sum_flatMap_map {α β : Type*} (l : List α) (g : α → List β) (F : β → ℤ) :
    ((l.flatMap g).map F).sum = (l.map fun x => ((g x).map F).sum).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.flatMap_cons, ih]

/-- A sum over the list of the indices with a property, as a sum over a finite set. -/
theorem sum_filter_finRange {m : ℕ} (p : Fin m → Prop) [DecidablePred p] (F : Fin m → ℤ) :
    (((List.finRange m).filter fun x => p x).map F).sum = ∑ x ∈ Finset.univ.filter p, F x := by
  rw [← List.sum_toFinset _ ((List.nodup_finRange m).filter _)]
  exact Finset.sum_congr (by ext x; simp) fun _ _ => rfl

section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]

/-- The triangle inequality for the sum of a list. -/
theorem abs_sum_le_sum_abs (l : List R) : |l.sum| ≤ (l.map fun x => |x|).sum :=
  Multiset.abs_sum_le_sum_abs (s := (l : Multiset R))

/-- The sum of an initial part of a list is at most the sum of the absolute values of the whole
list, in absolute value. -/
theorem abs_sum_take_le_sum_abs (l : List R) (k : ℕ) :
    |(l.take k).sum| ≤ (l.map fun x => |x|).sum := by
  refine (abs_sum_le_sum_abs _).trans ?_
  refine Sublist.sum_le_sum ((take_sublist k l).map _) fun a ha => ?_
  obtain ⟨x, -, rfl⟩ := mem_map.mp ha
  exact abs_nonneg x

end

/-- If `|f x| ≤ B` for all `x ∈ l`, then every initial part of the numbers `f x` has a sum of
absolute value at most `l.length * B`. -/
theorem abs_sum_take_map_le (l : List α) (f : α → ℤ) {B : ℤ} (h : ∀ x ∈ l, |f x| ≤ B) (k : ℕ) :
    |((l.map f).take k).sum| ≤ l.length * B := by
  refine (List.abs_sum_take_le_sum_abs _ k).trans ?_
  simpa using List.sum_le_card_nsmul ((l.map f).map fun x => |x|) B (by simpa using h)

/-- If `|f x| ≤ B` for all `x ∈ l`, then `|(l.map f).sum| ≤ l.length * B`. -/
theorem abs_sum_map_le (l : List α) (f : α → ℤ) {B : ℤ} (h : ∀ x ∈ l, |f x| ≤ B) :
    |(l.map f).sum| ≤ l.length * B := by
  have htake := abs_sum_take_map_le l f h l.length
  rwa [← List.length_map (f := f), List.take_length, List.length_map] at htake

/-- If `l` has no repetitions, every member of `l` is `g x` for some `x ∈ S`, `g` is injective and
`l` has as many members as `S` has elements, then the members of `l` are exactly the `g x` with
`x ∈ S`. -/
theorem toFinset_eq_image_of_length_eq_card [DecidableEq β] (l : List β) (hl : l.Nodup)
    (S : Finset α) (g : α → β)
    (hinj : Function.Injective g) (hsub : ∀ y ∈ l, ∃ x ∈ S, g x = y) (hcard : l.length = S.card) :
    l.toFinset = S.image g := by
  refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
  · obtain ⟨x, hx, rfl⟩ := hsub y (List.mem_toFinset.mp hy)
    exact Finset.mem_image_of_mem g hx
  · rw [Finset.card_image_of_injective S hinj, List.toFinset_card_of_nodup hl, hcard]

/-- Under the same hypotheses, a sum over `l` is a sum over `S`. -/
theorem sum_map_eq_sum_of_length_eq_card {M : Type*} [AddCommMonoid M] (l : List β) (hl : l.Nodup)
    (S : Finset α)
    (g : α → β) (hinj : Function.Injective g) (hsub : ∀ y ∈ l, ∃ x ∈ S, g x = y)
    (hcard : l.length = S.card) (F : β → M) : (l.map F).sum = ∑ x ∈ S, F (g x) := by
  classical
  rw [← List.sum_toFinset F hl, toFinset_eq_image_of_length_eq_card l hl S g hinj hsub hcard,
    Finset.sum_image fun x _ y _ hxy => hinj hxy]

/-! ## A running minimum -/

/-- A running minimum over `f 0, …, f m` is a lower bound of these values. -/
theorem foldl_min_le [LinearOrder β] (f : ℕ → β) (m : ℕ) {k : ℕ} (hk : k ≤ m) :
    (List.range m).foldl (fun acc j => min acc (f (j + 1))) (f 0) ≤ f k := by
  induction m with
  | zero => exact (Nat.le_zero.1 hk ▸ le_rfl : f 0 ≤ f k)
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rcases Nat.le_succ_iff.1 hk with h | rfl
    · exact (min_le_left _ _).trans (ih h)
    · exact min_le_right _ _

/-- A running minimum over `f 0, …, f m` is one of these values. -/
theorem exists_foldl_min_eq [LinearOrder β] (f : ℕ → β) (m : ℕ) :
    ∃ k ≤ m, (List.range m).foldl (fun acc j => min acc (f (j + 1))) (f 0) = f k := by
  induction m with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ m ih =>
    obtain ⟨k, hk, he⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, he]
    rcases le_total (f k) (f (m + 1)) with h | h
    · exact ⟨k, Nat.le_succ_of_le hk, min_eq_left h⟩
    · exact ⟨m + 1, le_rfl, min_eq_right h⟩

/-! ## Counting -/

/-- A count among the first `i + 1` entries, from the count among the first `i` and entry `i`. -/
theorem count_take_succ [DecidableEq α] (l : List α) (x : α) {i : ℕ}
    (hi : i < l.length) :
    (l.take (i + 1)).count x = (l.take i).count x + if l[i] = x then 1 else 0 := by
  rw [List.take_succ_eq_append_getElem hi, List.count_append, List.count_singleton]
  simp

/-- A count among the first `i + 1` entries, with entry `i` read by `getD`. -/
theorem count_take_succ_getD [DecidableEq α] (l : List α) (x : α) {i : ℕ} (hi : i < l.length)
    (d : α) :
    (l.take (i + 1)).count x = (l.take i).count x + if l.getD i d = x then 1 else 0 := by
  rw [List.count_take_succ l x hi, List.getD_eq_getElem l d hi]

/-- If entry `i < l.length` is `x`, then `x` occurs less often before place `i` than in the whole
list. -/
theorem count_take_lt [DecidableEq α] {l : List α} {i : ℕ} {x : α} (hi : i < l.length) (d : α)
    (hx : l.getD i d = x) : (l.take i).count x < l.count x := by
  have hle : (l.take (i + 1)).count x ≤ l.count x := (List.take_sublist _ _).count_le _
  rw [count_take_succ_getD l x hi d, if_pos hx] at hle
  omega

/-- The members with `t a < z + 1` are those with `t a < z` and those with `t a = z`. -/
theorem length_filter_lt_succ (t : α → ℕ) (z : ℕ) (l : List α) :
    (l.filter fun a => decide (t a < z + 1)).length =
      (l.filter fun a => decide (t a < z)).length +
        (l.filter fun a => decide (t a = z)).length := by
  simp only [← List.countP_eq_length_filter]
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.countP_cons, ih, decide_eq_true_eq]
    split_ifs <;> omega

/-- The list of the `j < n` with `q j` has `Nat.count q n` members. -/
theorem length_filter_range (q : ℕ → Prop) [DecidablePred q] (n : ℕ) :
    ((List.range n).filter fun j => decide (q j)).length = Nat.count q n := by
  rw [Nat.count, List.countP_eq_length_filter]

/-- In the increasing list of the `j < n` with `q j`, the member `i` has the number
`Nat.count q i`. -/
theorem getD_filter_range_count (q : ℕ → Prop) [DecidablePred q] (n : ℕ) {i : ℕ}
    (hi : i < n) (hq : q i) :
    ((List.range n).filter fun j => decide (q j)).getD (Nat.count q i) 0 = i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.filter_append]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
    · rw [List.getD_append _ _ _ _ (by
        rw [List.length_filter_range]
        exact (Nat.count_lt_count_succ_iff.2 hq).trans_le (Nat.count_monotone q h))]
      exact ih h
    · rw [List.getD_append_right _ _ _ _ (List.length_filter_range q i).le,
        List.length_filter_range, Nat.sub_self]
      simp [hq]

/-- How often a value occurs among the first `i` values of a function on `Fin n`. -/
theorem count_take_ofFn [DecidableEq α] {n : ℕ} (f : Fin n → α) (a : α) (i : ℕ) :
    ((List.ofFn f).take i).count a =
      (Finset.univ.filter fun j : Fin n => (j : ℕ) < i ∧ f j = a).card := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    cases i with
    | zero => simp
    | succ i =>
      rw [List.ofFn_succ, List.take_succ_cons, List.count_cons, ih, Finset.card_filter,
        Finset.card_filter, Fin.sum_univ_succ, add_comm]
      simp

/-- How often a value occurs in the table of a function on `Fin n`. -/
theorem count_ofFn [DecidableEq α] {n : ℕ} (f : Fin n → α) (a : α) :
    (List.ofFn f).count a = (Finset.univ.filter fun i => f i = a).card := by
  simpa [List.take_of_length_le] using count_take_ofFn f a n

/-! ## Sorted lists -/

section Sorted

variable [LinearOrder α]

/-- What remains of a strictly increasing list after the members below `a` are skipped. -/
theorem mem_dropWhile_lt {a c : α} {l : List α} (h : l.Pairwise (· < ·)) :
    (c ∈ l.dropWhile fun c => c < a) ↔ c ∈ l ∧ a ≤ c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    -- If `x < a`, then `x` is skipped. Otherwise nothing is skipped, and `xs` lies above `x ≥ a`.
    grind [List.dropWhile_cons, List.pairwise_cons]

/-- The members below `b` at the beginning of a strictly increasing list are all its members
below `b`. -/
theorem mem_takeWhile_lt {b c : α} {l : List α} (h : l.Pairwise (· < ·)) :
    (c ∈ l.takeWhile fun c => c < b) ↔ c ∈ l ∧ c < b := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    -- If `x < b`, then `x` is taken. Otherwise nothing is taken, and `xs` lies above `x ≥ b`.
    grind [List.takeWhile_cons, List.pairwise_cons]

/-- In a weakly increasing list, an entry that is the first or differs from its predecessor has not
occurred before. -/
theorem getD_notMem_take_of_sorted {l : List α} (hs : l.Pairwise (· ≤ ·)) {i : ℕ}
    (hi : i < l.length)
    (d : α) (h : i = 0 ∨ l.getD i d ≠ l.getD (i - 1) d) : l.getD i d ∉ l.take i := by
  intro hm
  obtain ⟨j, hj, hsame⟩ := List.mem_iff_getElem.1 hm
  have hji : j < i := (List.length_take_le i l).trans_lt' hj
  rcases h with rfl | hne
  · omega
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (show i - 1 < l.length by omega)] at hne
  rw [List.getElem_take, List.getD_eq_getElem _ _ hi] at hsame
  have hpred : l[i - 1] ≤ l[i] := List.pairwise_iff_getElem.1 hs _ _ _ _ (by omega)
  have hle : l[j] ≤ l[i - 1] := by
    rcases Nat.lt_or_ge j (i - 1) with hlt | hge
    · exact List.pairwise_iff_getElem.1 hs _ _ _ _ hlt
    · exact le_of_eq (by congr 1; omega)
  -- `l[j] ≤ l[i - 1] ≤ l[i] = l[j]`, so `l[i - 1] = l[i]`
  exact hne (le_antisymm (hsame ▸ hle) hpred)

end Sorted

end List

namespace ThreeSumApsp

variable {α β : Type*}

/-! ## Lists of integers that are bounded in absolute value -/

/-- All members of the list `l` have absolute value at most `U`. -/
def AbsLe (l : List ℤ) (U : ℤ) : Prop := ∀ x ∈ l, |x| ≤ U

/-- A bound on the absolute values of all members bounds every entry. -/
theorem AbsLe.getElem {l : List ℤ} {U : ℤ} (h : AbsLe l U) {i : ℕ} (hi : i < l.length) :
    |l[i]| ≤ U :=
  h _ (List.getElem_mem hi)

/-- Two lists with a common bound, one after the other. -/
theorem AbsLe.append {l₁ l₂ : List ℤ} {U : ℤ} (h₁ : AbsLe l₁ U) (h₂ : AbsLe l₂ U) :
    AbsLe (l₁ ++ l₂) U :=
  List.forall_mem_append.2 ⟨h₁, h₂⟩

/-- A bound on the absolute values of all members bounds every `getD` with default `0`. -/
theorem AbsLe.abs_getD_le {l : List ℤ} {U : ℤ} (hU : 0 ≤ U) (h : AbsLe l U) (i : ℕ) :
    |l.getD i 0| ≤ U :=
  List.getD_of_forall_mem (p := fun x => |x| ≤ U) (by rwa [abs_zero]) h i

/-! ## The entrywise sum of lists -/

/-- The entrywise sum of lists of length `len`. -/
def sumLists (len : ℕ) (ls : List (List ℤ)) : List ℤ :=
  ls.foldl (fun acc l => List.zipWith (· + ·) acc l) (List.replicate len 0)

/-- The entrywise sum of lists that are images of one list. -/
theorem sumLists_map (l : List α) (ts : List β) (f : β → α → ℤ) :
    sumLists l.length (ts.map fun t => l.map (f t)) =
      l.map fun c => (ts.map fun t => f t c).sum := by
  have hfold : ∀ (ts : List β) (g : α → ℤ),
      (ts.map fun t => l.map (f t)).foldl (fun acc l' => List.zipWith (· + ·) acc l') (l.map g) =
        l.map fun c => g c + (ts.map fun t => f t c).sum := by
    intro ts
    induction ts with
    | nil => simp
    | cons t ts ih =>
      intro g
      rw [List.map_cons, List.foldl_cons, List.zipWith_map, List.zipWith_self, ih]
      simp only [List.map_cons, List.sum_cons, add_assoc]
  rw [sumLists, ← List.map_const', hfold]
  simp only [zero_add]

end ThreeSumApsp
