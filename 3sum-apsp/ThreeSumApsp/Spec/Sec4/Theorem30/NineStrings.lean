/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.List.Range
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Strings of digits with a bounded number of nines (Section 4.2, proofs of Lemma 29, Theorem 30)

All three enumerations of Section 4 come from one: `nineStrs n lo hi`, the strings of n digits
0, …, 9 in which the digit 9 (the digit of P₀) occurs at least lo and at most hi times, in
lexicographic order.

* The boxes with e stars are the leaves with between e and m - t symbols P₀, with their e lowest
  symbols P₀ turned into stars (the proof of Lemma 29).
* The leaves of order below t contributing to an output string η (the paper's w) have, at the m
  levels of its inner set Q, a string with at least m - t + 1 nines (proof of Theorem 30).
* The boxes of η have, at the m levels of Q, a string with exactly m - t nines, the nines being the
  levels of V (Section 4.2).

The file proves what the list contains (`mem_nineStrs`), that it is increasing
(`pairwise_lt_nineStrs`), how long it is (`length_nineStrs`: ∑_f binom(n, f) 9^{n-f}), and how a
routine goes through it: it starts with `nineFirst` (`head?_nineStrs`), and `nineNext` goes from
each string to the next (`nineNext_getElem`); so the string reached after i steps,
`nineStr n lo hi i`, is the member number i (`getElem_nineStrs`).  Read from the right end of the
string, `nineNext` is one pass: skip the positions that cannot be raised, raise one digit
(`nineRaise`), and fill the rest with the least admissible string, zeros followed by nines.  The
proof follows the recursion of the list: the strings with the first digit d form a block,
`nineNext` goes through each block (`nextTo_map_cons`), and from the last string of a block to the
first string of the next block (`head_nineBlocks`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-- The strings of n digits below 10 with between lo and hi digits 9, in lexicographic order. -/
def nineStrs : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, lo, _ => if lo = 0 then [[]] else []
  | n + 1, lo, hi =>
    (List.range 9).flatMap (fun d => (nineStrs n lo hi).map (d :: ·)) ++
      (if hi = 0 then [] else (nineStrs n (lo - 1) (hi - 1)).map (9 :: ·))

/-- The least string of n digits with at least lo digits 9: zeros, then lo nines. -/
def nineFirst (n lo : ℕ) : List ℕ := List.replicate (n - lo) 0 ++ List.replicate lo 9

/-- The first digit d raised by one, if that is possible, and the least admissible string of n
digits behind it. -/
def nineRaise (lo hi n d : ℕ) : Option (List ℕ) :=
  if d < 8 then some ((d + 1) :: nineFirst n lo)
  else if d = 8 ∧ 0 < hi then some (9 :: nineFirst n (lo - 1))
  else none

/-- The string after l, or none if l is the last one: the rest of the string goes to the string
after it, or, if it is the last one, the first digit is raised. -/
def nineNext : ℕ → ℕ → List ℕ → Option (List ℕ)
  | _, _, [] => none
  | lo, hi, d :: l =>
    match nineNext (if d = 9 then lo - 1 else lo) (if d = 9 then hi - 1 else hi) l with
    | some l' => some (d :: l')
    | none => nineRaise lo hi l.length d

/-- The string number i of the list, as a routine reaches it: from the first string by going to the
next one i times. -/
def nineStr (n lo hi i : ℕ) : List ℕ := (fun l => (nineNext lo hi l).getD l)^[i] (nineFirst n lo)

/-! ## The members of the list -/

/-- The first digit is below 9, or it is a 9 and counts. -/
private theorem cons_mem_nineStrs {n lo hi d : ℕ} {l : List ℕ} :
    d :: l ∈ nineStrs (n + 1) lo hi ↔
      (d < 9 ∧ l ∈ nineStrs n lo hi) ∨ (d = 9 ∧ hi ≠ 0 ∧ l ∈ nineStrs n (lo - 1) (hi - 1)) := by
  rw [nineStrs, List.mem_append, List.mem_flatMap]
  refine or_congr ?_ ?_
  · simp only [List.mem_range, List.mem_map, List.cons.injEq]
    exact ⟨fun ⟨a, ha, l', hl', had, hll⟩ => ⟨had ▸ ha, hll ▸ hl'⟩,
      fun ⟨hd, hl⟩ => ⟨d, hd, l, hl, rfl, rfl⟩⟩
  · by_cases hhi : hi = 0
    · simp [hhi]
    · simp only [if_neg hhi, List.mem_map, List.cons.injEq]
      exact ⟨fun ⟨l', hl', hd, hll⟩ => ⟨hd.symm, hhi, hll ▸ hl'⟩,
        fun ⟨hd, _, hl⟩ => ⟨l, hl, hd.symm, rfl⟩⟩

theorem mem_nineStrs {n lo hi : ℕ} (l : List ℕ) :
    l ∈ nineStrs n lo hi ↔
      l.length = n ∧ (∀ d ∈ l, d < 10) ∧ lo ≤ l.count 9 ∧ l.count 9 ≤ hi := by
  induction n generalizing lo hi l with
  | zero => cases l <;> by_cases h : lo = 0 <;> simp [nineStrs, h]
  | succ n ih =>
    rcases l with _ | ⟨d, l⟩
    · simp [nineStrs]
    rw [cons_mem_nineStrs, ih, ih, List.length_cons, List.forall_mem_cons,
      Nat.add_right_cancel_iff]
    by_cases hd : d = 9
    · -- a nine less is needed, and a nine less is allowed, in the rest
      subst hd
      rw [List.count_cons_self]
      grind
    · rw [List.count_cons_of_ne hd]
      grind

theorem length_of_mem_nineStrs {n lo hi : ℕ} {l : List ℕ} (hl : l ∈ nineStrs n lo hi) :
    l.length = n :=
  ((mem_nineStrs l).1 hl).1

/-- The digit of the star does not occur. -/
theorem ten_notMem_of_mem_nineStrs {n lo hi : ℕ} {l : List ℕ} (hl : l ∈ nineStrs n lo hi) :
    10 ∉ l :=
  fun h => absurd (((mem_nineStrs l).1 hl).2.1 10 h) (lt_irrefl 10)

/-- There is no string with more nines than digits, or if the bounds contradict each other. -/
private theorem nineStrs_eq_nil {n lo hi : ℕ} (h : n < lo ∨ hi < lo) : nineStrs n lo hi = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro l hl
  obtain ⟨hlen, -, hlo, hhi⟩ := (mem_nineStrs l).1 hl
  have hcount := List.count_le_length (a := 9) (l := l)
  omega

/-- The list is strictly increasing in the lexicographic order. -/
theorem pairwise_lt_nineStrs (n lo hi : ℕ) : (nineStrs n lo hi).Pairwise (· < ·) := by
  induction n generalizing lo hi with
  | zero =>
    rw [nineStrs]
    split_ifs <;> simp
  | succ n ih =>
    rw [nineStrs, List.pairwise_append, List.pairwise_flatMap]
    refine ⟨⟨fun d _ => ?_, ?_⟩, ?_, ?_⟩
    · rw [List.pairwise_map]
      exact (ih lo hi).imp fun h => List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, h⟩)
    · refine List.pairwise_lt_range.imp fun {a b} hab x hx y hy => ?_
      obtain ⟨x', -, rfl⟩ := List.mem_map.1 hx
      obtain ⟨y', -, rfl⟩ := List.mem_map.1 hy
      exact List.cons_lt_cons_iff.2 (Or.inl hab)
    · split_ifs
      · simp
      · rw [List.pairwise_map]
        exact (ih _ _).imp fun h => List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, h⟩)
    · intro x hx y hy
      obtain ⟨d, hd, hx⟩ := List.mem_flatMap.1 hx
      obtain ⟨x', -, rfl⟩ := List.mem_map.1 hx
      split_ifs at hy
      · simp at hy
      · obtain ⟨y', -, rfl⟩ := List.mem_map.1 hy
        exact List.cons_lt_cons_iff.2 (Or.inl (List.mem_range.1 hd))

theorem nineStrs_nodup (n lo hi : ℕ) : (nineStrs n lo hi).Nodup :=
  (pairwise_lt_nineStrs n lo hi).imp fun h => ne_of_lt h

/-! ## The length of the list -/

/-- The recursion for the length of the list. -/
private theorem length_nineStrs_succ (n lo hi : ℕ) :
    (nineStrs (n + 1) lo hi).length = 9 * (nineStrs n lo hi).length
      + if hi = 0 then 0 else (nineStrs n (lo - 1) (hi - 1)).length := by
  rw [nineStrs, List.length_append, List.length_flatMap]
  congr 1
  · simp only [List.length_map, List.map_const', List.length_range, List.sum_replicate_nat]
  · split_ifs <;> simp

/-- Strings without a nine: one more digit, nine times as many. -/
private theorem nineTerm_zero (n : ℕ) :
    (n + 1).choose 0 * 9 ^ (n + 1 - 0) = 9 * (n.choose 0 * 9 ^ (n - 0)) := by
  simp [pow_succ, mul_comm]

/-- Strings with g + 1 nines: the first digit is a nine or one of the nine other digits. -/
private theorem nineTerm_succ (n g : ℕ) :
    (n + 1).choose (g + 1) * 9 ^ (n + 1 - (g + 1))
      = n.choose g * 9 ^ (n - g) + 9 * (n.choose (g + 1) * 9 ^ (n - (g + 1))) := by
  rw [Nat.choose_succ_succ, Nat.add_sub_add_right, add_mul]
  congr 1
  rcases Nat.lt_or_ge n (g + 1) with h | h
  · rw [Nat.choose_eq_zero_of_lt h]
    simp
  · rw [show n - g = n - (g + 1) + 1 by omega, pow_succ]
    ring

/-- A sum from 0: the first summand apart. -/
private theorem sum_Icc_zero_succ (h : ℕ) (G : ℕ → ℕ) :
    ∑ f ∈ Finset.Icc 0 (h + 1), G f = G 0 + ∑ g ∈ Finset.Icc 0 h, G (g + 1) := by
  rw [← Nat.range_succ_eq_Icc_zero, ← Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ', add_comm]

/-- A sum with both ends shifted by one. -/
private theorem sum_Icc_succ_succ (l h : ℕ) (G : ℕ → ℕ) :
    ∑ f ∈ Finset.Icc (l + 1) (h + 1), G f = ∑ g ∈ Finset.Icc l h, G (g + 1) := by
  rw [← Finset.map_add_right_Icc, Finset.sum_map]
  rfl

/-- There are binom(n, f) 9^{n-f} strings with exactly f nines. -/
theorem length_nineStrs (n lo hi : ℕ) :
    (nineStrs n lo hi).length = ∑ f ∈ Finset.Icc lo hi, n.choose f * 9 ^ (n - f) := by
  induction n generalizing lo hi with
  | zero =>
    rw [nineStrs]
    split_ifs with h
    · subst h
      rw [Finset.sum_eq_single_of_mem 0 (by simp) fun b _ hb => by
        rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb), zero_mul]]
      rfl
    · refine (Finset.sum_eq_zero fun f hf => ?_).symm
      have := (Finset.mem_Icc.1 hf).1
      rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
  | succ n ih =>
    rw [length_nineStrs_succ, ih]
    rcases hi with _ | h
    · -- no nine is allowed
      rw [if_pos rfl, add_zero, Finset.mul_sum]
      refine Finset.sum_congr rfl fun f hf => ?_
      obtain rfl : f = 0 := Nat.le_zero.mp (Finset.mem_Icc.1 hf).2
      exact (nineTerm_zero n).symm
    · rw [if_neg (Nat.succ_ne_zero h), ih, Nat.add_sub_cancel]
      rcases lo with _ | l
      · rw [sum_Icc_zero_succ, sum_Icc_zero_succ, nineTerm_zero, Nat.zero_sub, mul_add,
          Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
        refine congrArg _ (Finset.sum_congr rfl fun g _ => ?_)
        rw [nineTerm_succ, add_comm]
      · rw [sum_Icc_succ_succ, sum_Icc_succ_succ, Nat.add_sub_cancel, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [nineTerm_succ, add_comm]

/-! ## The first string -/

/-- If there is a string at all, the bounds are consistent. -/
private theorem le_of_mem_nineStrs {n lo hi : ℕ} {l : List ℕ} (hl : l ∈ nineStrs n lo hi) :
    lo ≤ n ∧ lo ≤ hi := by
  obtain ⟨hlen, -, hlo, hhi⟩ := (mem_nineStrs l).1 hl
  have hcount := List.count_le_length (a := 9) (l := l)
  omega

/-- The least string begins with 0 if not all digits have to be nines. -/
private theorem nineFirst_succ {n lo : ℕ} (h : lo ≤ n) :
    nineFirst (n + 1) lo = 0 :: nineFirst n lo := by
  rw [nineFirst, nineFirst, Nat.succ_sub h, List.replicate_succ, List.cons_append]

/-- The string of nines. -/
private theorem nineFirst_self_succ (n : ℕ) : nineFirst (n + 1) (n + 1) = 9 :: nineFirst n n := by
  simp [nineFirst, List.replicate_succ]

/-- Without strings of n digits there are no strings of n + 1 digits that begin below 9. -/
private theorem flatMap_map_nil (l : List ℕ) :
    l.flatMap (fun d => ([] : List (List ℕ)).map (d :: ·)) = [] :=
  List.flatMap_eq_nil_iff.2 fun _ _ => rfl

theorem head?_nineStrs {n lo hi : ℕ} (h : lo ≤ n) (h' : lo ≤ hi) :
    (nineStrs n lo hi).head? = some (nineFirst n lo) := by
  induction n generalizing lo hi with
  | zero =>
    obtain rfl : lo = 0 := by omega
    rfl
  | succ n ih =>
    rw [nineStrs]
    rcases Nat.lt_or_ge n lo with hlo | hlo
    · -- all digits are nines
      obtain rfl : lo = n + 1 := by omega
      rw [nineStrs_eq_nil (Or.inl (Nat.lt_succ_self n)), if_neg (by omega), flatMap_map_nil,
        List.nil_append, List.head?_map, Nat.add_sub_cancel, ih le_rfl (by omega),
        nineFirst_self_succ]
      rfl
    · rw [List.range_succ_eq_map, List.flatMap_cons, List.append_assoc, List.head?_append,
        List.head?_map, ih hlo h', nineFirst_succ hlo]
      rfl

/-! ## From each string to the next -/

/-- f takes each member of the list to the following one, and the last one to z. -/
private def NextTo {α : Type} (f : α → Option α) : List α → Option α → Prop
  | [], _ => True
  | x :: r, z => f x = r.head?.or z ∧ NextTo f r z

/-- f goes through two lists one after the other exactly if it goes through both, and from the last
member of the first list to the first member of the second (to z if the second list is empty). -/
private theorem nextTo_append {α : Type} {f : α → Option α} {A B : List α} {z : Option α} :
    NextTo f (A ++ B) z ↔ NextTo f A (B.head?.or z) ∧ NextTo f B z := by
  induction A with
  | nil => simp [NextTo]
  | cons x A ih =>
    rw [List.cons_append, NextTo, NextTo, ih, List.head?_append, Option.or_assoc, and_assoc]

/-- What `NextTo` says about the member number i. -/
private theorem NextTo.getElem {α : Type} {f : α → Option α} {A : List α} {z : Option α}
    (h : NextTo f A z) (i : ℕ) (hi : i < A.length) : f A[i] = A[i + 1]?.or z := by
  induction A generalizing i with
  | nil => simp at hi
  | cons x A ih =>
    cases i with
    | zero => rw [List.getElem_cons_zero, h.1, List.getElem?_cons_succ, List.head?_eq_getElem?]
    | succ i =>
      rw [List.getElem_cons_succ, List.getElem?_cons_succ]
      exact ih h.2 i (by simpa using hi)

/-- The block of the strings with the first digit d. -/
private theorem nextTo_map_cons (lo hi n d : ℕ) (S : List (List ℕ)) (hS : ∀ l ∈ S, l.length = n)
    (h : NextTo (nineNext (if d = 9 then lo - 1 else lo) (if d = 9 then hi - 1 else hi)) S none) :
    NextTo (nineNext lo hi) (S.map (d :: ·)) (nineRaise lo hi n d) := by
  induction S with
  | nil => trivial
  | cons x r ih =>
    refine ⟨?_, ih (fun l hl => hS l (by simp [hl])) h.2⟩
    rw [nineNext, h.1, Option.or_none]
    rcases r with _ | ⟨y, r⟩
    · simp only [List.head?_nil, List.map_nil, Option.none_or, hS x (by simp)]
    · rfl

/-- The blocks of the strings with the first digits a, a + 1, …, a + k - 1, followed by the block
with the first digit 9: the end of the list `nineStrs (n + 1) lo hi`. -/
private def nineBlocks (n lo hi a k : ℕ) : List (List ℕ) :=
  (List.range' a k).flatMap (fun d => (nineStrs n lo hi).map (d :: ·)) ++
    (if hi = 0 then [] else (nineStrs n (lo - 1) (hi - 1)).map (9 :: ·))

section

variable {n lo hi : ℕ}

/-- `nineNext` goes through the last block, the strings with the first digit 9. -/
private theorem nextTo_nineBlocks_zero (a : ℕ)
    (h9 : NextTo (nineNext (lo - 1) (hi - 1)) (nineStrs n (lo - 1) (hi - 1)) none) :
    NextTo (nineNext lo hi) (nineBlocks n lo hi a 0) none := by
  rw [nineBlocks, List.range'_zero, List.flatMap_nil, List.nil_append]
  split_ifs
  · trivial
  · exact nextTo_map_cons lo hi n 9 _ (fun _ => length_of_mem_nineStrs) h9

/-- The first string after the block with the first digit a is the one to which `nineNext` goes by
raising the digit a. -/
private theorem head_nineBlocks (hn : lo ≤ n) (hh : lo ≤ hi) {a k : ℕ} (hak : a + 1 + k = 9) :
    (nineBlocks n lo hi (a + 1) k).head? = nineRaise lo hi n a := by
  rw [nineBlocks, nineRaise]
  cases k with
  | zero =>
    obtain rfl : a = 8 := by omega
    rw [List.range'_zero, List.flatMap_nil, List.nil_append]
    by_cases h0 : hi = 0
    · simp [h0]
    · rw [if_neg h0, List.head?_map, head?_nineStrs (by omega) (by omega), if_neg (lt_irrefl 8),
        if_pos ⟨rfl, Nat.pos_of_ne_zero h0⟩]
      rfl
  | succ k =>
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc, List.head?_append, List.head?_map,
      head?_nineStrs hn hh, if_pos (show a < 8 by omega)]
    rfl

/-- `nineNext` goes through the blocks. -/
private theorem nextTo_nineBlocks (hn : lo ≤ n) (hh : lo ≤ hi)
    (h : NextTo (nineNext lo hi) (nineStrs n lo hi) none)
    (h9 : NextTo (nineNext (lo - 1) (hi - 1)) (nineStrs n (lo - 1) (hi - 1)) none) (k a : ℕ)
    (hak : a + k = 9) : NextTo (nineNext lo hi) (nineBlocks n lo hi a k) none := by
  induction k generalizing a with
  | zero => exact nextTo_nineBlocks_zero a h9
  | succ k ih =>
    have hsplit : nineBlocks n lo hi a (k + 1)
        = (nineStrs n lo hi).map (a :: ·) ++ nineBlocks n lo hi (a + 1) k := by
      rw [nineBlocks, nineBlocks, List.range'_succ, List.flatMap_cons, List.append_assoc]
    rw [hsplit, nextTo_append, Option.or_none, head_nineBlocks hn hh (by omega)]
    refine ⟨nextTo_map_cons lo hi n a _ (fun _ => length_of_mem_nineStrs) ?_, ih (a + 1) (by omega)⟩
    rwa [if_neg (by omega), if_neg (by omega)]

end

/-- `nineNext` goes through the list. -/
private theorem nextTo_nineStrs (n lo hi : ℕ) :
    NextTo (nineNext lo hi) (nineStrs n lo hi) none := by
  induction n generalizing lo hi with
  | zero =>
    rw [nineStrs]
    split_ifs
    · exact ⟨rfl, trivial⟩
    · trivial
  | succ n ih =>
    by_cases h : lo ≤ n ∧ lo ≤ hi
    · rw [nineStrs, List.range_eq_range']
      exact nextTo_nineBlocks h.1 h.2 (ih lo hi) (ih _ _) 9 0 rfl
    · -- only strings that begin with a nine
      rw [nineStrs, nineStrs_eq_nil (by omega), flatMap_map_nil]
      exact nextTo_nineBlocks_zero 0 (ih _ _)

/-- `nineNext` goes from each string of the list to the following one, and from the last one to
none. -/
theorem nineNext_getElem (n lo hi i : ℕ) (h : i < (nineStrs n lo hi).length) :
    nineNext lo hi ((nineStrs n lo hi)[i]) = (nineStrs n lo hi)[i + 1]? := by
  rw [(nextTo_nineStrs n lo hi).getElem i h, Option.or_none]

section

variable {n lo hi i : ℕ}

theorem nineStr_succ (n lo hi i : ℕ) :
    nineStr n lo hi (i + 1) = (nineNext lo hi (nineStr n lo hi i)).getD (nineStr n lo hi i) :=
  Function.iterate_succ_apply' _ _ _

/-- `nineStr n lo hi i` is the member number i of the list. -/
theorem getElem_nineStrs (h : i < (nineStrs n lo hi).length) :
    (nineStrs n lo hi)[i] = nineStr n lo hi i := by
  induction i with
  | zero =>
    obtain ⟨hn, hh⟩ := le_of_mem_nineStrs (List.getElem_mem h)
    refine Option.some.inj ?_
    rw [← List.getElem?_eq_getElem h, ← List.head?_eq_getElem?, head?_nineStrs hn hh]
    rfl
  | succ i ih =>
    rw [nineStr_succ, ← ih (Nat.lt_of_succ_lt h), nineNext_getElem, List.getElem?_eq_getElem h]
    rfl

theorem nineStr_mem (h : i < (nineStrs n lo hi).length) : nineStr n lo hi i ∈ nineStrs n lo hi :=
  getElem_nineStrs h ▸ List.getElem_mem h

/-- There is a next string exactly if the string is not the last one of the list. -/
theorem isSome_nineNext_nineStr (h : i < (nineStrs n lo hi).length) :
    (nineNext lo hi (nineStr n lo hi i)).isSome = decide (i + 1 < (nineStrs n lo hi).length) := by
  rw [← getElem_nineStrs h, nineNext_getElem]
  by_cases h' : i + 1 < (nineStrs n lo hi).length <;> simp [h']

/-- If the bounds are consistent, there is a string. -/
theorem length_nineStrs_pos (hn : lo ≤ n) (hh : lo ≤ hi) : 0 < (nineStrs n lo hi).length :=
  List.length_pos_iff.mpr fun hnil => by simpa [hnil] using head?_nineStrs hn hh

end

end ThreeSumApsp.Spec
