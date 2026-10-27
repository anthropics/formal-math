/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Math.CodeMore

/-! Tuples coded by words cut into chunks of various lengths: the entry at i is decoded from chunk
number pos i, and chunk
number κ has length n κ and starts at the offset Σ_{κ' < κ} n κ'. -/

namespace Groundwork

open Finset

variable {X : Type*}

/-- The chunk number κ of a word cut into chunks of lengths n 0, n 1, … -/
@[expose] public def chunkAt (n : ℕ → ℕ) (κ : ℕ) (w : List Bool) : List Bool :=
  (w.drop (∑ κ' ∈ range κ, n κ')).take (n κ)

theorem chunkAt_zero (n : ℕ → ℕ) (w : List Bool) : chunkAt n 0 w = w.take (n 0) := by simp [chunkAt]

theorem chunkAt_succ (n : ℕ → ℕ) (κ : ℕ) (w : List Bool) :
    chunkAt n (κ + 1) w = chunkAt (fun k => n (k + 1)) κ (w.drop (n 0)) := by
  rw [chunkAt, chunkAt, List.drop_drop, sum_range_succ', Nat.add_comm (n 0)]

/-- A word of the full length is known by its chunks. -/
theorem chunk_ext (r : ℕ) : ∀ (n : ℕ → ℕ) (w w' : List Bool), w.length = ∑ κ ∈ range r, n κ →
    w'.length = ∑ κ ∈ range r, n κ → (∀ κ < r, chunkAt n κ w = chunkAt n κ w') → w = w' := by
  induction r with
  | zero =>
    intro n w w' hw hw' _
    rw [range_zero, sum_empty, List.length_eq_zero_iff] at hw hw'
    rw [hw, hw']
  | succ r ih =>
    intro n w w' hw hw' h
    rw [sum_range_succ'] at hw hw'
    have h0 := h 0 (by omega)
    rw [chunkAt_zero, chunkAt_zero] at h0
    have h1 := ih (fun k => n (k + 1)) (w.drop (n 0)) (w'.drop (n 0)) (by rw [List.length_drop]; omega)
      (by rw [List.length_drop]; omega) fun κ hκ => by
        rw [← chunkAt_succ, ← chunkAt_succ]; exact h (κ + 1) (by omega)
    rw [← List.take_append_drop (n 0) w, h0, h1, List.take_append_drop]

/-- Every list of chunks of the right lengths comes from a word. -/
theorem exists_chunks (r : ℕ) : ∀ (n : ℕ → ℕ) (v : ℕ → List Bool), (∀ κ < r, (v κ).length = n κ) →
    ∃ w : List Bool, w.length = ∑ κ ∈ range r, n κ ∧ ∀ κ < r, chunkAt n κ w = v κ := by
  induction r with
  | zero => exact fun n v _ => ⟨[], by simp, fun κ hκ => absurd hκ (by omega)⟩
  | succ r ih =>
    intro n v hv
    obtain ⟨w, hw, hb⟩ := ih (fun k => n (k + 1)) (fun k => v (k + 1)) fun κ hκ => hv (κ + 1) (by omega)
    have h0 := hv 0 (by omega)
    refine ⟨v 0 ++ w, by rw [List.length_append, h0, hw, sum_range_succ']; omega, fun κ hκ => ?_⟩
    cases κ with
    | zero => rw [chunkAt_zero, ← h0, List.take_left]
    | succ κ => rw [chunkAt_succ, ← h0, List.drop_left]; exact hb κ (by omega)

namespace Code

/-- The code of the tuples that have an entry of T i at every i with P i and d elsewhere, where pos
numbers the i with P i
by 0, …, r - 1: a word of Σ_{κ < r} n κ bits whose chunk number pos i is a code word in Dk i,
decoded by deck i. -/
@[expose] public def seq {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (pos : ι → ℕ) (r : ℕ)
    (_hpos : Set.BijOn pos {i | P i} (range r)) {T : ι → Finset X} (n : ℕ → ℕ) (Dk : ι → Finset (List Bool))
    (deck : ι → List Bool → X) (_hlen : ∀ i, P i → ∀ w ∈ Dk i, w.length = n (pos i))
    (_hbij : ∀ i, P i → Set.BijOn (deck i) (Dk i) (T i)) (d : X) :
    Code (Groundwork.tuples P T d) (∑ κ ∈ range r, n κ) where
  D := (words (∑ κ ∈ range r, n κ)).filter fun w => ∀ i, P i → chunkAt n (pos i) w ∈ Dk i
  dec w i := if P i then deck i (chunkAt n (pos i) w) else d
  len w h := mem_words.1 (mem_filter.1 h).1
  bij := by
    have hm : ∀ t : ι → X, t ∈ Groundwork.tuples P T d ↔ (∀ i, P i → t i ∈ T i) ∧ ∀ i, ¬ P i → t i = d := by
      intro t
      simp only [Groundwork.tuples, Fintype.mem_piFinset]
      constructor
      · intro h
        exact ⟨fun i hi => by have := h i; rwa [if_pos hi] at this,
          fun i hi => by have := h i; rw [if_neg hi] at this; exact mem_singleton.1 this⟩
      · rintro ⟨h1, h2⟩ i
        by_cases hi : P i
        · rw [if_pos hi]; exact h1 i hi
        · rw [if_neg hi]; exact mem_singleton.2 (h2 i hi)
    refine ⟨fun w hw => ?_, fun w hw w' hw' h => ?_, fun t ht => ?_⟩
    · have hw := (mem_filter.1 (mem_coe.1 hw)).2
      refine mem_coe.2 ((hm _).2 ⟨fun i hi => ?_, fun i hi => if_neg hi⟩)
      simp only [if_pos hi]
      exact (_hbij i hi).mapsTo (hw i hi)
    · obtain ⟨hl, hw⟩ := mem_filter.1 (mem_coe.1 hw)
      obtain ⟨hl', hw'⟩ := mem_filter.1 (mem_coe.1 hw')
      refine chunk_ext r n w w' (mem_words.1 hl) (mem_words.1 hl') fun κ hκ => ?_
      obtain ⟨i, hi, rfl⟩ := _hpos.surjOn (mem_coe.2 (mem_range.2 hκ))
      refine (_hbij i hi).injOn (hw i hi) (hw' i hi) ?_
      have := congrFun h i
      simpa only [if_pos (show P i from hi)] using this
    · obtain ⟨h1, h2⟩ := (hm t).1 (mem_coe.1 ht)
      have hex : ∀ i, ∃ v, P i → v ∈ Dk i ∧ deck i v = t i := fun i => by
        by_cases hi : P i
        · obtain ⟨v, hv, e⟩ := (_hbij i hi).surjOn (h1 i hi)
          exact ⟨v, fun _ => ⟨hv, e⟩⟩
        · exact ⟨[], fun h => absurd h hi⟩
      choose v hv using hex
      choose inv hinv using fun (κ : ℕ) (hκ : κ < r) => _hpos.surjOn (mem_coe.2 (mem_range.2 hκ))
      obtain ⟨w, hl, hb⟩ := exists_chunks r n (fun κ => if hκ : κ < r then v (inv κ hκ) else []) fun κ hκ => by
          simp only [dif_pos hκ]
          rw [_hlen _ (hinv κ hκ).1 _ (hv _ (hinv κ hκ).1).1, (hinv κ hκ).2]
      have hlt : ∀ i, P i → pos i < r := fun i hi => mem_range.1 (mem_coe.1 (_hpos.mapsTo hi))
      have hb' : ∀ i, P i → chunkAt n (pos i) w = v i := fun i hi => by
        rw [hb _ (hlt i hi)]
        simp only [dif_pos (hlt i hi)]
        rw [_hpos.injOn (hinv _ (hlt i hi)).1 hi (hinv _ (hlt i hi)).2]
      refine ⟨w, mem_coe.2 (mem_filter.2 ⟨mem_words.2 hl, fun i hi => ?_⟩), funext fun i => ?_⟩
      · rw [hb' i hi]; exact (hv i hi).1
      · by_cases hi : P i
        · simp only [if_pos hi]
          rw [hb' i hi, (hv i hi).2]
        · simp only [if_neg hi]
          exact (h2 i hi).symm

end Code

/-- The length of a chunk of a word of the full length. -/
public theorem length_chunkAt (n : ℕ → ℕ) {r κ : ℕ} (hκ : κ < r) {w : List Bool} (hw : w.length = ∑ κ' ∈ range r, n κ') :
    (chunkAt n κ w).length = n κ := by
  have h : ∑ κ' ∈ range (κ + 1), n κ' ≤ ∑ κ' ∈ range r, n κ' :=
    sum_le_sum_of_subset (range_mono hκ)
  rw [sum_range_succ] at h
  rw [chunkAt, List.length_take, List.length_drop, hw]
  omega

end Groundwork
