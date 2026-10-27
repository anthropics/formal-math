/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Math.Code
import Mathlib.Data.List.GetD

/-! More codes: the inverse of a code, entries of equal length found by position, subsets of a
finite set. -/

namespace Groundwork

open Finset

variable {X Y : Type*}

namespace Code

variable {S : Finset X} {n : ℕ}

/-- The name of an element x of S: the word of c.D that c.dec sends to x. -/
public noncomputable def enc (c : Code S n) (x : X) : List Bool := Function.invFunOn c.dec c.D x

public theorem enc_mem (c : Code S n) {x : X} (hx : x ∈ S) : c.enc x ∈ c.D :=
  mem_coe.1 (Function.invFunOn_mem (c.bij.surjOn (mem_coe.2 hx)))

public theorem dec_enc (c : Code S n) {x : X} (hx : x ∈ S) : c.dec (c.enc x) = x :=
  Function.invFunOn_eq (c.bij.surjOn (mem_coe.2 hx))

public theorem enc_dec (c : Code S n) {w : List Bool} (hw : w ∈ c.D) : c.enc (c.dec w) = w :=
  c.bij.injOn (mem_coe.2 (c.enc_mem (c.bij.mapsTo hw))) (mem_coe.2 hw) (c.dec_enc (c.bij.mapsTo hw))

public theorem dec_inj (c : Code S n) {w w' : List Bool} (hw : w ∈ c.D) (hw' : w' ∈ c.D) :
    c.dec w = c.dec w' ↔ w = w' := c.bij.injOn.eq_iff hw hw'

public theorem length_enc (c : Code S n) {x : X} (hx : x ∈ S) : (c.enc x).length = n := c.len _ (c.enc_mem hx)

public theorem bijOn_enc (c : Code S n) : Set.BijOn c.enc S c.D := by
  refine ⟨fun x hx => mem_coe.2 (c.enc_mem (mem_coe.1 hx)), fun x hx x' hx' h => ?_, fun w hw => ?_⟩
  · rw [← c.dec_enc (mem_coe.1 hx), h, c.dec_enc (mem_coe.1 hx')]
  · exact ⟨c.dec w, c.bij.mapsTo hw, c.enc_dec (mem_coe.1 hw)⟩

theorem block_zero (m : ℕ) (w : List Bool) : block m 0 w = w.take m := by simp [block]

theorem block_succ (m j : ℕ) (w : List Bool) : block m (j + 1) w = block m j (w.drop m) := by
  rw [block, block, List.drop_drop]
  congr 2
  ring

/-- A word of r·m bits is known by its r blocks. -/
theorem block_ext (m r : ℕ) (w w' : List Bool) (hw : w.length = r * m) (hw' : w'.length = r * m)
    (h : ∀ j < r, block m j w = block m j w') : w = w' := by
  induction r generalizing w w' with
  | zero =>
    rw [Nat.zero_mul, List.length_eq_zero_iff] at hw hw'
    rw [hw, hw']
  | succ r ih =>
    rw [Nat.succ_mul] at hw hw'
    have h0 := h 0 (by omega)
    rw [block_zero, block_zero] at h0
    have h1 := ih (w.drop m) (w'.drop m) (by rw [List.length_drop]; omega) (by rw [List.length_drop]; omega)
      fun j hj => by rw [← block_succ, ← block_succ]; exact h (j + 1) (by omega)
    rw [← List.take_append_drop m w, h0, h1, List.take_append_drop]

/-- Every list of r blocks of m bits comes from a word. -/
theorem exists_blocks (m r : ℕ) (v : ℕ → List Bool) (hv : ∀ j < r, (v j).length = m) :
    ∃ w : List Bool, w.length = r * m ∧ ∀ j < r, block m j w = v j := by
  induction r generalizing v with
  | zero => exact ⟨[], by simp, fun j hj => absurd hj (by omega)⟩
  | succ r ih =>
    obtain ⟨w, hw, hb⟩ := ih (fun j => v (j + 1)) fun j hj => hv (j + 1) (by omega)
    have h0 := hv 0 (by omega)
    refine ⟨v 0 ++ w, by rw [List.length_append, h0, hw, Nat.succ_mul]; omega, fun j hj => ?_⟩
    cases j with
    | zero => rw [block_zero, ← h0, List.take_left]
    | succ j =>
      have hd : (v 0 ++ w).drop m = w := by rw [← h0, List.drop_left]
      rw [block_succ, hd]
      exact hb j (by omega)

/-- Functions on ι with values in S: r = card ι names of length m one after the other; the name of
the value at i is
block number pos i. -/
@[expose] public def blocks {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (pos : ι ≃ Fin r) {m : ℕ} (c : Code S m) :
    Code (Fintype.piFinset fun _ : ι => S) (r * m) where
  D := (words (r * m)).filter fun w => ∀ i, block m (pos i) w ∈ c.D
  dec w i := c.dec (block m (pos i) w)
  len w h := mem_words.1 (mem_filter.1 h).1
  bij := by
    refine ⟨fun w hw => ?_, fun w hw w' hw' h => ?_, fun x hx => ?_⟩
    · have hw := (mem_filter.1 (mem_coe.1 hw)).2
      exact mem_coe.2 (Fintype.mem_piFinset.2 fun i => c.bij.mapsTo (hw i))
    · obtain ⟨hl, hw⟩ := mem_filter.1 (mem_coe.1 hw)
      obtain ⟨hl', hw'⟩ := mem_filter.1 (mem_coe.1 hw')
      refine block_ext m r w w' (mem_words.1 hl) (mem_words.1 hl') fun j hj => ?_
      have h1 := c.bij.injOn (hw (pos.symm ⟨j, hj⟩)) (hw' (pos.symm ⟨j, hj⟩)) (congrFun h (pos.symm ⟨j, hj⟩))
      simpa using h1
    · have hx := Fintype.mem_piFinset.1 (mem_coe.1 hx)
      obtain ⟨w, hl, hb⟩ := exists_blocks m r (fun j => if hj : j < r then c.enc (x (pos.symm ⟨j, hj⟩)) else [])
        fun j hj => by simp only [dif_pos hj]; exact c.length_enc (hx _)
      have hb' : ∀ i, block m (pos i) w = c.enc (x i) := fun i => by
        rw [hb _ (pos i).2]; simp
      refine ⟨w, mem_coe.2 (mem_filter.2 ⟨mem_words.2 hl, fun i => ?_⟩), funext fun i => ?_⟩
      · rw [hb']; exact c.enc_mem (hx i)
      · change c.dec (block m (pos i) w) = x i
        rw [hb', c.dec_enc (hx i)]

public theorem full_blocks {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (pos : ι ≃ Fin r) {m : ℕ} (c : Code S m)
    (h : c.Full) : (blocks pos c).Full := by
  refine filter_true_of_mem fun w hw i => ?_
  rw [h, mem_words]
  refine length_block ?_
  rw [mem_words.1 hw]
  exact Nat.mul_le_mul_right _ (pos i).2

/-- The subsets of Ω: bit idx ω of the word says whether ω is in the subset. -/
@[expose] public def subsets {ι : Type*} [DecidableEq ι] (Ω : Finset ι) (M : ℕ) (idx : ι → ℕ)
    (_h : Set.BijOn idx Ω (range M)) : Code Ω.powerset M where
  D := words M
  dec τ := Ω.filter fun ω => τ.getD (idx ω) false = true
  len _ h := mem_words.1 h
  bij := by
    refine ⟨fun τ _ => mem_coe.2 (mem_powerset.2 (filter_subset _ _)), fun τ hτ τ' hτ' h => ?_, fun A hA => ?_⟩
    · have l := mem_words.1 (mem_coe.1 hτ)
      have l' := mem_words.1 (mem_coe.1 hτ')
      refine List.ext_getElem (l.trans l'.symm) fun j hj hj' => ?_
      obtain ⟨ω, hω, rfl⟩ := _h.surjOn (mem_coe.2 (mem_range.2 (l ▸ hj)))
      have h1 := Finset.ext_iff.1 h ω
      simp only [mem_filter, mem_coe.1 hω, true_and, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] at h1
      exact Bool.eq_iff_iff.2 h1
    · have hA := mem_powerset.1 (mem_coe.1 hA)
      refine ⟨(List.range M).map fun j => decide (∃ ω ∈ A, idx ω = j), mem_coe.2 (mem_words.2 (by simp)), ?_⟩
      ext ω
      simp only [mem_filter]
      constructor
      · rintro ⟨hω, h1⟩
        have hlt : idx ω < M := mem_range.1 (_h.mapsTo (mem_coe.2 hω))
        rw [List.getD_eq_getElem _ _ (by simpa using hlt)] at h1
        simp only [List.getElem_map, List.getElem_range, decide_eq_true_eq] at h1
        obtain ⟨ω', hω', e⟩ := h1
        rwa [← _h.injOn (mem_coe.2 (hA hω')) (mem_coe.2 hω) e]
      · intro hω
        have hlt : idx ω < M := mem_range.1 (_h.mapsTo (mem_coe.2 (hA hω)))
        refine ⟨hA hω, ?_⟩
        rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
        simp only [List.getElem_map, List.getElem_range, decide_eq_true_eq]
        exact ⟨ω, hω, rfl⟩

theorem card_filter_getD (τ : List Bool) : #{j ∈ range τ.length | τ.getD j false = true} = τ.count true := by
  induction τ with
  | nil => simp
  | cons b τ ih =>
    rw [card_filter] at ih ⊢
    rw [List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih, List.count_cons]
    cases b <;> simp

public theorem card_dec_subsets {ι : Type*} [DecidableEq ι] (Ω : Finset ι) (M : ℕ) (idx : ι → ℕ)
    (h : Set.BijOn idx Ω (range M)) {τ : List Bool} (hτ : τ.length = M) :
    #((subsets Ω M idx h).dec τ) = τ.count true := by
  rw [← card_filter_getD, hτ]
  refine card_nbij idx (fun ω hω => ?_) (fun ω hω ω' hω' e => ?_) fun j hj => ?_
  · obtain ⟨h1, h2⟩ := mem_filter.1 hω
    exact mem_filter.2 ⟨h.mapsTo (mem_coe.2 h1), h2⟩
  · exact h.injOn (mem_coe.2 (mem_filter.1 (mem_coe.1 hω)).1) (mem_coe.2 (mem_filter.1 (mem_coe.1 hω')).1) e
  · obtain ⟨h1, h2⟩ := mem_filter.1 (mem_coe.1 hj)
    obtain ⟨ω, hω, rfl⟩ := h.surjOn (mem_coe.2 h1)
    exact ⟨ω, mem_coe.2 (mem_filter.2 ⟨mem_coe.1 hω, h2⟩), rfl⟩

end Code

/-- A sum over tuples, carried along bijections φ i of T' i with T i. -/
public theorem sum_tuples_map {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M] (P : ι → Prop) [DecidablePred P]
    {T : ι → Finset X} {T' : ι → Finset Y} (d : X) (d' : Y) (φ : ι → Y → X) (h : ∀ i, P i → Set.BijOn (φ i) (T' i) (T i))
    (F : (ι → X) → M) :
    ∑ t ∈ tuples P T d, F t = ∑ t' ∈ tuples P T' d', F fun i => if P i then φ i (t' i) else d := by
  symm
  refine sum_nbij (fun t' i => if P i then φ i (t' i) else d) (fun t' ht' => ?_) (fun t' ht' t'' ht'' e => ?_)
    (fun t ht => ?_) fun _ _ => rfl
  · have ht' := (mem_tuples _ _ _ _).1 ht'
    refine (mem_tuples _ _ _ _).2 fun i => ⟨fun hi => ?_, fun hi => if_neg hi⟩
    rw [if_pos hi]
    exact (h i hi).mapsTo ((ht' i).1 hi)
  · have ht' := (mem_tuples _ _ _ _).1 (mem_coe.1 ht')
    have ht'' := (mem_tuples _ _ _ _).1 (mem_coe.1 ht'')
    funext i
    by_cases hi : P i
    · have e1 := congrFun e i
      simp only [if_pos hi] at e1
      exact (h i hi).injOn ((ht' i).1 hi) ((ht'' i).1 hi) e1
    · rw [(ht' i).2 hi, (ht'' i).2 hi]
  · have ht := (mem_tuples _ _ _ _).1 (mem_coe.1 ht)
    have hex : ∀ i, ∃ y, (P i → y ∈ T' i ∧ φ i y = t i) ∧ (¬P i → y = d') := fun i => by
      by_cases hi : P i
      · obtain ⟨y, hy, e⟩ := (h i hi).surjOn ((ht i).1 hi)
        exact ⟨y, fun _ => ⟨hy, e⟩, fun hn => absurd hi hn⟩
      · exact ⟨d', fun hp => absurd hp hi, fun _ => rfl⟩
    choose y hy using hex
    refine ⟨y, mem_coe.2 ((mem_tuples _ _ _ _).2 fun i => ⟨fun hi => ((hy i).1 hi).1, (hy i).2⟩), funext fun i => ?_⟩
    by_cases hi : P i
    · simp only [if_pos hi]; exact ((hy i).1 hi).2
    · simp only [if_neg hi]; exact ((ht i).2 hi).symm

end Groundwork
