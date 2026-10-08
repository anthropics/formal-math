/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Ceil
public import ThreeSumApsp.Util.List
public import Mathlib.Algebra.Order.Floor.Div

/-!
# The table of the chunks (proof of Theorem 17)

"For ϱ ∈ ℤ_p let W_ϱ be the set of edges (a,b) ∈ A × B with w(a,b) ≡ ϱ (mod p), and cut it into
chunks of at most n²/√D query pairs."  The routine lists the pairs class after class (`sortedIdx`).
Then a class is a segment of the list, from `classStart ϱ` to `classStart (ϱ + 1)`, and a chunk is a
segment of a class.  The table `chunkTab` has one entry for each chunk: its residue, the place where
it starts, and its number of pairs.

* The list has every pair once (`sortedIdx_nodup`, `classStart_eq_sq`), and the places of a class
  hold pairs of that class (`getD_sortedIdx_class`).
* An entry of the table is a nonempty segment of at most `cap` places (`chunkTab_entry`) whose pairs
  have the residue of the entry (`chunkTab_class`).
* The chunks follow each other (`chunkTab_pairwise`), so every place lies in exactly one chunk
  (`chunkTab_cover`, `chunkTab_unique`).
* "There are at most p + √D ≤ 2√D chunks in all" (`length_chunkTab_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

variable {n p cap : ℕ} {RAB : List ℕ}

/-! ## The classes and the list of all the pairs -/

/-- The places `a n + b` of the pairs of the class `W_ϱ`, in increasing order; `RAB` holds the
residues. -/
def classIdx (n : ℕ) (RAB : List ℕ) (rho : ℕ) : List ℕ :=
  (List.range (n * n)).filter fun i => RAB.getD i 0 = rho

/-- All the places, class after class. -/
def sortedIdx (n p : ℕ) (RAB : List ℕ) : List ℕ := (List.range p).flatMap (classIdx n RAB)

/-- The rows of the pairs, class after class. -/
def queryRows (n p : ℕ) (RAB : List ℕ) : List ℕ := (sortedIdx n p RAB).map (· / n)

/-- The columns of the pairs, class after class. -/
def queryCols (n p : ℕ) (RAB : List ℕ) : List ℕ := (sortedIdx n p RAB).map (· % n)

/-- The places of a class. -/
theorem mem_classIdx {rho x : ℕ} : x ∈ classIdx n RAB rho ↔ x < n * n ∧ RAB.getD x 0 = rho := by
  simp [classIdx]

/-- The list holds places of pairs. -/
theorem lt_of_mem_sortedIdx {x : ℕ} (h : x ∈ sortedIdx n p RAB) : x < n * n := by
  obtain ⟨rho, -, hx⟩ := List.mem_flatMap.1 h
  exact (mem_classIdx.1 hx).1

/-- No pair is listed twice. -/
theorem sortedIdx_nodup (n p : ℕ) (RAB : List ℕ) : (sortedIdx n p RAB).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun rho _ => List.nodup_range.filter _, ?_⟩
  refine (List.nodup_range (n := p)).imp fun {a b} hab x hxa hxb => ?_
  exact hab ((mem_classIdx.1 hxa).2.symm.trans (mem_classIdx.1 hxb).2)

/-! ## The starts of the classes -/

/-- The place where the class `rho` starts: the number of pairs with a residue below `rho`. -/
def classStart (n : ℕ) (RAB : List ℕ) (rho : ℕ) : ℕ :=
  ((List.range rho).map fun r => (classIdx n RAB r).length).sum

/-- The table of the places where the classes start: entry `ϱ ≤ p` is `classStart n RAB ϱ`. -/
def classStarts (n p : ℕ) (RAB : List ℕ) : List ℕ := (List.range (p + 1)).map (classStart n RAB)

/-- The next class starts where the class ends. -/
theorem classStart_succ (n : ℕ) (RAB : List ℕ) (rho : ℕ) :
    classStart n RAB (rho + 1) = classStart n RAB rho + (classIdx n RAB rho).length :=
  List.sum_range_succ _ _

/-- Later classes start later. -/
theorem classStart_mono (n : ℕ) (RAB : List ℕ) {a b : ℕ} (h : a ≤ b) :
    classStart n RAB a ≤ classStart n RAB b :=
  List.sum_map_range_mono _ h

/-- The list `classStarts` holds the starts of the classes. -/
theorem getD_classStarts_eq (n p : ℕ) (RAB : List ℕ) {rho : ℕ} (h : rho ≤ p) :
    (classStarts n p RAB).getD rho 0 = classStart n RAB rho :=
  List.getD_map_range _ (Nat.lt_succ_of_le h) 0

/-- The list of all the pairs ends where the class `p` would start. -/
theorem length_sortedIdx_eq (n p : ℕ) (RAB : List ℕ) :
    (sortedIdx n p RAB).length = classStart n RAB p :=
  List.length_flatMap

/-- The class `p` starts after the pairs with a residue below `p`. -/
theorem classStart_eq_length_filter (n : ℕ) (RAB : List ℕ) (p : ℕ) :
    classStart n RAB p =
      ((List.range (n * n)).filter fun i => decide (RAB.getD i 0 < p)).length := by
  induction p with
  | zero => simp [classStart]
  | succ p ih =>
    rw [classStart_succ, ih, List.length_filter_lt_succ fun i => RAB.getD i 0]
    rfl

/-- All the pairs are listed if all the residues are below `p`. -/
theorem classStart_eq_sq (hlt : ∀ i < n * n, RAB.getD i 0 < p) : classStart n RAB p = n * n := by
  rw [classStart_eq_length_filter, List.filter_eq_self.2, List.length_range]
  exact fun i hi => decide_eq_true (hlt i (List.mem_range.1 hi))

/-- A place below the start of the class `p` lies in one of the classes before. -/
theorem exists_class {j : ℕ} (hj : j < classStart n RAB p) :
    ∃ rho < p, classStart n RAB rho ≤ j ∧ j < classStart n RAB (rho + 1) := by
  induction p with
  | zero => exact absurd hj (Nat.not_lt_zero j)
  | succ p ih =>
    by_cases h : j < classStart n RAB p
    · obtain ⟨rho, hrho, hseg⟩ := ih h
      exact ⟨rho, by omega, hseg⟩
    · exact ⟨p, by omega, by omega, hj⟩

/-- The places from the start of the class `rho` to the start of the next class hold pairs with the
residue `rho`. -/
theorem getD_sortedIdx_class {rho j : ℕ} (hrho : rho < p) (hlo : classStart n RAB rho ≤ j)
    (hhi : j < classStart n RAB (rho + 1)) : RAB.getD ((sortedIdx n p RAB).getD j 0) 0 = rho := by
  rw [classStart_succ] at hhi
  obtain ⟨o, rfl⟩ := Nat.exists_eq_add_of_le hlo
  have ho : o < (classIdx n RAB rho).length := by omega
  rw [sortedIdx, classStart, List.getD_flatMap_range_sum _ hrho ho, List.getD_eq_getElem _ 0 ho]
  exact (mem_classIdx.1 (List.getElem_mem ho)).2

/-! ## The chunks -/

/-- A chunk: a segment of the list of all the pairs that lies within one class. -/
structure Chunk where
  /-- The residue of the class. -/
  residue : ℕ
  /-- The place in the list where the chunk starts. -/
  start : ℕ
  /-- The number of places of the chunk. -/
  len : ℕ

/-- The place `j` lies in the chunk. -/
def Chunk.Contains (x : Chunk) (j : ℕ) : Prop := x.start ≤ j ∧ j < x.start + x.len

/-- The chunk has a residue below `p`, and it is a nonempty segment of at most `cap` of the `n²`
places. -/
structure Chunk.Fits (x : Chunk) (n p cap : ℕ) : Prop where
  residue_lt : x.residue < p
  len_pos : 1 ≤ x.len
  len_le : x.len ≤ cap
  end_le : x.start + x.len ≤ n * n

/-- The segment `[lo, hi)` of the class `rho`, cut into chunks of `cap` places; the last one may be
shorter. -/
def chunksOf (cap lo hi rho : ℕ) : List Chunk :=
  (List.range ((hi - lo) ⌈/⌉ cap)).map fun i => ⟨rho, lo + i * cap, min cap (hi - lo - i * cap)⟩

/-- The chunks of `p` segments, of which number `rho` goes from entry `rho` to entry `rho + 1` of
the list `C`. -/
def chunkTabOf (p cap : ℕ) (C : List ℕ) : List Chunk :=
  (List.range p).flatMap fun rho => chunksOf cap (C.getD rho 0) (C.getD (rho + 1) 0) rho

/-- The table of the chunks, with one entry for each chunk of each class. -/
def chunkTab (n p cap : ℕ) (RAB : List ℕ) : List Chunk := chunkTabOf p cap (classStarts n p RAB)

/-- Chunk number `i` of the class `rho`. -/
def chunkAt (n cap : ℕ) (RAB : List ℕ) (rho i : ℕ) : Chunk :=
  ⟨rho, classStart n RAB rho + i * cap, min cap ((classIdx n RAB rho).length - i * cap)⟩

/-- The table, in terms of the starts of the classes. -/
theorem chunkTab_eq (n p cap : ℕ) (RAB : List ℕ) :
    chunkTab n p cap RAB = (List.range p).flatMap fun rho =>
      (List.range ((classIdx n RAB rho).length ⌈/⌉ cap)).map (chunkAt n cap RAB rho) := by
  unfold chunkTab chunkTabOf
  refine List.flatMap_congr fun rho hrho => ?_
  have h := List.mem_range.1 hrho
  rw [getD_classStarts_eq n p RAB (by omega), getD_classStarts_eq n p RAB (by omega), chunksOf,
    classStart_succ, Nat.add_sub_cancel_left]
  rfl

/-- The entries of the table: chunk number `i` of the class `rho`. -/
theorem mem_chunkTab (x : Chunk) :
    x ∈ chunkTab n p cap RAB ↔
      ∃ rho < p, ∃ i < (classIdx n RAB rho).length ⌈/⌉ cap, x = chunkAt n cap RAB rho i := by
  simp only [chunkTab_eq, List.mem_flatMap, List.mem_range, List.mem_map, eq_comm (a := x)]

/-- An entry of the table has a residue below `p`, and it is a nonempty segment of at most `cap`
places of the list. -/
theorem chunkTab_entry (hcap : 1 ≤ cap) (hlt : ∀ i < n * n, RAB.getD i 0 < p) {x : Chunk}
    (hx : x ∈ chunkTab n p cap RAB) : x.Fits n p cap := by
  obtain ⟨rho, hrho, i, hi, rfl⟩ := (mem_chunkTab x).1 hx
  have hleft := (Nat.lt_ceilDiv_iff hcap).1 hi
  have hend := classStart_mono n RAB (show rho + 1 ≤ p by omega)
  rw [classStart_succ, classStart_eq_sq hlt] at hend
  constructor <;> simp only [chunkAt] <;> omega

/-- The pairs of a chunk have the residue of its entry. -/
theorem chunkTab_class (hcap : 1 ≤ cap) {x : Chunk} (hx : x ∈ chunkTab n p cap RAB) {i : ℕ}
    (hi : i < x.len) : RAB.getD ((sortedIdx n p RAB).getD (x.start + i) 0) 0 = x.residue := by
  obtain ⟨rho, hrho, i', hi', rfl⟩ := (mem_chunkTab x).1 hx
  have hleft := (Nat.lt_ceilDiv_iff hcap).1 hi'
  simp only [chunkAt] at hi ⊢
  exact getD_sortedIdx_class hrho (by omega) (by rw [classStart_succ]; omega)

/-- The chunks follow each other: a chunk ends where a later one starts, or before. -/
theorem chunkTab_pairwise (hcap : 1 ≤ cap) :
    (chunkTab n p cap RAB).Pairwise fun x y => x.start + x.len ≤ y.start := by
  rw [chunkTab_eq, List.pairwise_flatMap]
  constructor
  · -- two chunks of one class
    intro rho _
    rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp fun {i i'} hii => ?_
    have hmul : (i + 1) * cap ≤ i' * cap := Nat.mul_le_mul_right cap hii
    rw [Nat.add_mul, Nat.one_mul] at hmul
    simp only [chunkAt]
    omega
  · -- two chunks of different classes
    refine List.pairwise_lt_range.imp fun {rho rho'} hrr x hx y hy => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i', -, rfl⟩ := List.mem_map.1 hy
    have hleft := (Nat.lt_ceilDiv_iff hcap).1 (List.mem_range.1 hi)
    have hnext := classStart_mono n RAB (show rho + 1 ≤ rho' by omega)
    rw [classStart_succ] at hnext
    simp only [chunkAt]
    omega

/-- Every place lies in a chunk. -/
theorem chunkTab_cover (hcap : 1 ≤ cap) (hlt : ∀ i < n * n, RAB.getD i 0 < p) {j : ℕ}
    (hj : j < n * n) : ∃ x ∈ chunkTab n p cap RAB, x.Contains j := by
  -- The place `j` lies in a class `rho`, and there in chunk number `i = (j - start) / cap`.
  rw [← classStart_eq_sq hlt] at hj
  obtain ⟨rho, hrho, hlo, hhi⟩ := exists_class hj
  rw [classStart_succ] at hhi
  have hdiv := Nat.div_add_mod' (j - classStart n RAB rho) cap
  have hmod := Nat.mod_lt (j - classStart n RAB rho) hcap
  generalize (j - classStart n RAB rho) / cap = i at hdiv
  have hi : i < (classIdx n RAB rho).length ⌈/⌉ cap := (Nat.lt_ceilDiv_iff hcap).2 (by omega)
  refine ⟨_, (mem_chunkTab _).2 ⟨rho, hrho, i, hi, rfl⟩, ?_⟩
  -- `start + i cap ≤ j < start + i cap + min cap (len - i cap)`, from `hdiv`, `hmod` and `hhi`.
  simp only [Chunk.Contains, chunkAt]
  omega

/-- A place lies in one chunk only. -/
theorem chunkTab_unique (hcap : 1 ≤ cap) {j k k' : ℕ} (h : k < (chunkTab n p cap RAB).length)
    (h' : k' < (chunkTab n p cap RAB).length) (hj : (chunkTab n p cap RAB)[k].Contains j)
    (hj' : (chunkTab n p cap RAB)[k'].Contains j) : k = k' := by
  have hpair := List.pairwise_iff_getElem.1 (chunkTab_pairwise (n := n) (p := p) (RAB := RAB) hcap)
  obtain ⟨hlo, hhi⟩ := hj
  obtain ⟨hlo', hhi'⟩ := hj'
  rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
  · have := hpair k k' h h' hlt
    omega
  · exact heq
  · have := hpair k' k h' h hgt
    omega

/-- The number of chunks, class by class. -/
theorem length_chunkTab (n p cap : ℕ) (RAB : List ℕ) :
    (chunkTab n p cap RAB).length =
      ((List.range p).map fun rho => (classIdx n RAB rho).length ⌈/⌉ cap).sum := by
  rw [chunkTab_eq, List.length_flatMap]
  simp

/-- Proof of Theorem 17: "There are at most p + √D ≤ 2√D chunks in all", in the form: at most `p +
n²/cap`. -/
theorem length_chunkTab_le (hcap : 1 ≤ cap) (hlt : ∀ i < n * n, RAB.getD i 0 < p) :
    (chunkTab n p cap RAB).length ≤ p + n * n / cap := by
  -- The bound holds for the first `q` classes, for every `q`.
  rw [length_chunkTab, ← classStart_eq_sq hlt]
  generalize p = q
  induction q with
  | zero => simp
  | succ q ih =>
    -- One more class: `⌈x/cap⌉ ≤ x/cap + 1`, and rounding down is superadditive.
    have hceil : (classIdx n RAB q).length ⌈/⌉ cap ≤ (classIdx n RAB q).length / cap + 1 := by
      rw [Nat.ceilDiv_eq_add_pred_div, ← Nat.add_div_right _ hcap]
      exact Nat.div_le_div_right (by omega)
    have hfloor : classStart n RAB q / cap + (classIdx n RAB q).length / cap ≤
        (classStart n RAB q + (classIdx n RAB q).length) / cap := Nat.div_add_div_le_add_div
    rw [List.sum_range_succ, classStart_succ]
    omega

end ThreeSumApsp.Spec
