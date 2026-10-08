/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Logic
public import ThreeSumApsp.Lang.Regions
public import ThreeSumApsp.Util.Index
public import ThreeSumApsp.Util.List
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Tactic.Positivity

/-!
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

/-- The cells a, a + 1, … of the memory μ hold the list l. -/
def Seg (μ : ℕ → ℤ) (a : ℕ) (l : List ℤ) : Prop := ∀ i (h : i < l.length), μ (a + i) = l[i]

/-- The list held by the n cells from address a. -/
def readSeg (μ : ℕ → ℤ) (a n : ℕ) : List ℤ := (List.range n).map fun i => μ (a + i)

variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}

@[simp] theorem length_readSeg : (readSeg μ a n).length = n := by simp [readSeg]

@[simp] theorem getElem_readSeg {i : ℕ} (h : i < (readSeg μ a n).length) :
    (readSeg μ a n)[i] = μ (a + i) := by
  simp [readSeg]

theorem getD_readSeg {i : ℕ} (hi : i < n) : (readSeg μ a n).getD i 0 = μ (a + i) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), getElem_readSeg]

theorem seg_readSeg : Seg μ a (readSeg μ a n) := fun i h => by simp

@[simp] theorem Seg.nil : Seg μ a [] := fun i h => absurd h (by simp)

/-- Reading a cell of a segment. -/
theorem Seg.get (h : Seg μ a l) {i : ℕ} (hi : i < l.length) : μ (a + i) = l[i] := h i hi

/-- Reading a cell of a segment, with a default value for the list. -/
theorem Seg.getD (h : Seg μ a l) {i : ℕ} (hi : i < l.length) (d : ℤ) : μ (a + i) = l.getD i d := by
  rw [h i hi, List.getD_eq_getElem _ _ hi]

/-- A segment determines its list. -/
theorem Seg.eq_readSeg (h : Seg μ a l) : l = readSeg μ a l.length :=
  List.ext_getElem (by simp) fun i h₁ h₂ => by rw [getElem_readSeg, h i h₁]

theorem seg_cons : Seg μ a (x :: l) ↔ μ a = x ∧ Seg μ (a + 1) l := by
  constructor
  · intro h
    refine ⟨by have h0 := h 0 (by simp); rwa [Nat.add_zero, List.getElem_cons_zero] at h0,
      fun i hi => ?_⟩
    have := h (i + 1) (by simpa using hi)
    simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => simpa using h0
    | succ i =>
      have := h i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem seg_append : Seg μ a (l₁ ++ l₂) ↔ Seg μ a l₁ ∧ Seg μ (a + l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [h i (by simp; omega), List.getElem_append_left hi]
    · have := h (l₁.length + i) (by simp; omega)
      rw [List.getElem_append_right (by omega)] at this
      simpa [Nat.add_assoc] using this
  · rintro ⟨h₁, h₂⟩ i hi
    by_cases hi₁ : i < l₁.length
    · rw [List.getElem_append_left hi₁, h₁ i hi₁]
    · have hi₂ : i - l₁.length < l₂.length := by simp at hi; omega
      rw [List.getElem_append_right (by omega), ← h₂ _ hi₂]
      congr 1
      omega

theorem Seg.take (h : Seg μ a l) (k : ℕ) : Seg μ a (l.take k) := fun i hi => by
  have hi' : i < l.length := by simp at hi; omega
  rw [List.getElem_take, h i hi']

theorem Seg.drop (h : Seg μ a l) (k : ℕ) : Seg μ (a + k) (l.drop k) := fun i hi => by
  have hi' : k + i < l.length := by simp at hi; omega
  rw [List.getElem_drop, ← h _ hi', Nat.add_assoc]

/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]

/-- A segment stays where it is if its cells do not change.  By the default proof of `hs`, the term
`h.keep` carries `h` to a later memory across the steps whose promises are in the context. -/
theorem Seg.keep (h : Seg μ a l) (hs : SameOn (Inside a l.length) μ μ' := by light_keep) :
    Seg μ' a l :=
  h.congr fun i hi => hs _ ⟨by omega, by omega⟩

/-- Writing into a segment. -/
theorem Seg.update_in (h : Seg μ a l) {i : ℕ} (hi : i < l.length) (x : ℤ) :
    Seg (Function.update μ (a + i) x) a (l.set i x) := by
  intro j hj
  have hj' : j < l.length := by simpa using hj
  by_cases hji : j = i
  · subst hji; simp
  · rw [Function.update_of_ne (by omega), List.getElem_set_of_ne (by omega), h j hj']

/-- Writing outside a segment. -/
theorem Seg.update_out (h : Seg μ a l) (hb : b < a ∨ a + l.length ≤ b) (x : ℤ) :
    Seg (Function.update μ b x) a l :=
  h.congr fun i hi => Function.update_of_ne (by omega) _ _

/-- Writing just after a segment makes it longer. -/
theorem Seg.snoc (h : Seg μ a l) (x : ℤ) : Seg (Function.update μ (a + l.length) x) a (l ++ [x]) :=
  seg_append.2 ⟨h.update_out (Or.inr le_rfl) x, by simp [seg_cons]⟩

/-- A segment all of whose cells are kept. -/
theorem Seg.of_sameOn {K : ℕ → Prop} (h : Seg μ b l) (hs : SameOn K μ μ')
    (hK : ∀ i < l.length, K (b + i)) : Seg μ' b l := h.congr fun i hi => hs _ (hK i hi)

theorem SameOutside.refl : SameOutside μ μ a n := SameOn.refl

/-- A larger region may change. -/
theorem SameOutside.mono {a' n' : ℕ} (h : SameOutside μ μ' a n) (ha : a' ≤ a)
    (hn : a + n ≤ a' + n') :
    SameOutside μ μ' a' n' := fun b hb => h b (by omega)

/-- Writing inside the region. -/
theorem SameOutside.update (h : SameOutside μ μ' a n) (hb : a ≤ b ∧ b < a + n) (x : ℤ) :
    SameOutside μ (Function.update μ' b x) a n := fun c hc => by
  rw [Function.update_of_ne (by omega)]; exact h c hc

theorem SameOutside2.refl {m : ℕ} : SameOutside2 μ μ a n b m := SameOn.refl

/-- Writing into one of the two regions. -/
theorem SameOutside2.update {m c : ℕ} (h : SameOutside2 μ μ' a n b m)
    (hc : (a ≤ c ∧ c < a + n) ∨ (b ≤ c ∧ c < b + m)) (x : ℤ) :
    SameOutside2 μ (Function.update μ' c x) a n b m :=
  h.write (by omega) x

/-- A segment that does not meet the region is kept. -/
theorem Seg.of_sameOutside (h : Seg μ b l) (hs : SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : Seg μ' b l :=
  h.congr fun i hi => hs _ (by omega)

/-- The cells a, a + 1, … hold a list of natural numbers. -/
abbrev SegN (μ : ℕ → ℤ) (a : ℕ) (l : List ℕ) : Prop := Seg μ a (l.map fun x : ℕ => (x : ℤ))

/-- Reading a cell of a segment of natural numbers. -/
theorem SegN.read {l : List ℕ} (h : SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = ((l.getD i 0 : ℕ) : ℤ) := by
  rw [h i (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]

/-- Reading a cell of a segment of natural numbers, with the proof that the index is in range. -/
theorem SegN.getElem {l : List ℕ} (h : SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = (l[i] : ℕ) := by
  rw [h i (by simpa using hi), List.getElem_map]

/-- Writing just after a segment of natural numbers makes it longer. -/
theorem SegN.snoc {l : List ℕ} (h : SegN μ a l) (x : ℕ) :
    SegN (Function.update μ (a + l.length) (x : ℤ)) a (l ++ [x]) := by
  simpa [SegN] using Seg.snoc h (x : ℤ)

/-- One more entry of a list of natural numbers is written behind its first k entries. -/
theorem SegN.take_succ {l : List ℕ} {k : ℕ} (h : SegN μ a (l.take k)) (hk : k < l.length) :
    SegN (Function.update μ (a + k) ((l.getD k 0 : ℕ) : ℤ)) a (l.take (k + 1)) := by
  have hsnoc := h.snoc (l.getD k 0)
  rwa [List.length_take, Nat.min_eq_left hk.le, ← List.take_succ_getD l hk 0] at hsnoc

/-- A piece of a segment of natural numbers: w cells from the place lo on. -/
theorem SegN.drop_take {l : List ℕ} (h : SegN μ a l) (lo w : ℕ) :
    SegN μ (a + lo) ((l.drop lo).take w) := by
  simpa only [SegN, List.map_take, List.map_drop] using (Seg.drop h lo).take w

/-- A segment of natural numbers stays where it is if its cells do not change. -/
theorem SegN.keep {l : List ℕ} (h : SegN μ a l)
    (hs : SameOn (Inside a l.length) μ μ' := by light_keep) : SegN μ' a l :=
  Seg.keep h (by simpa using hs)

/-- A segment of natural numbers that does not meet the region is kept. -/
theorem SegN.of_sameOutside {l : List ℕ} (h : SegN μ b l) (hs : SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : SegN μ' b l :=
  Seg.of_sameOutside h hs (by simpa using hd)

/-- The cells from a on hold the matrix A, row by row. -/
def MatAt {n k : ℕ} (μ : ℕ → ℤ) (a : ℕ) (A : Matrix (Fin n) (Fin k) ℤ) : Prop :=
  ∀ (i : Fin n) (j : Fin k), μ (a + i * k + j) = A i j

/-- A matrix stays where it is if its cells do not change. -/
theorem MatAt.congr {n k : ℕ} {A : Matrix (Fin n) (Fin k) ℤ} (h : MatAt μ a A)
    (he : ∀ b, a ≤ b → b < a + n * k → μ' b = μ b) : MatAt μ' a A := fun i j => by
  have := Nat.mul_add_lt_mul i.isLt j.isLt
  rw [he _ (by omega) (by omega)]
  exact h i j

/-- A matrix stays where it is if its cells do not change. -/
theorem MatAt.keep {n k : ℕ} {A : Matrix (Fin n) (Fin k) ℤ} (h : MatAt μ a A)
    (hs : SameOn (Inside a (n * k)) μ μ' := by light_keep) : MatAt μ' a A :=
  h.congr fun b h₁ h₂ => hs b ⟨h₁, h₂⟩

/-- A matrix that lies below e is still there in a memory that agrees below e. -/
theorem MatAt.congr_below {n k e : ℕ} {A : Matrix (Fin n) (Fin k) ℤ} (h : MatAt μ a A)
    (hlow : ∀ x < e, μ' x = μ x) (hle : a + n * k ≤ e) : MatAt μ' a A :=
  h.congr fun b _ hb => hlow b (by omega)

/-- The cells from a on hold the indices I 0, I 1, …. -/
def VecAt {t n : ℕ} (μ : ℕ → ℤ) (a : ℕ) (I : Fin t → Fin n) : Prop :=
  ∀ k : Fin t, μ (a + k.val) = ((I k).val : ℤ)

/-- A vector of indices that has been written as a list. -/
theorem vecAt_of_seg {t n : ℕ} {I : Fin t → Fin n}
    (h : Seg μ a (List.ofFn fun k => ((I k).val : ℤ))) : VecAt μ a I := fun k => by
  rw [h k.val (by simp)]
  simp

/-- A vector of indices stays where it is if its cells do not change. -/
theorem VecAt.keep {t n : ℕ} {I : Fin t → Fin n} (h : VecAt μ a I)
    (hs : SameOn (Inside a t) μ μ' := by light_keep) : VecAt μ' a I :=
  fun k => (hs _ ⟨by omega, by omega⟩).trans (h k)

end Light
