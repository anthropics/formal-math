/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cut.Blocks
import Nc.Grp.Seg

/-!
# The sum over the ways to cut a word
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open Finset

theorem segL_eq' (sep : List Bool) (f : ℕ) (tk : Bool) (cur : List Bool) (fs : List ℕ) (as rest out : List (List Bool)) :
    segL sep f tk cur fs as rest out =
      (if okFlag f tk then closeL sep cur fs as rest out else []) ++
      match rest with
      | [] => []
      | a :: r => segL sep f true (a ++ cur) fs as r out := by
  rw [segL.eq_def]
  cases fs <;> cases rest <;> rfl

variable {A : Type} [CommRing A]

/-- The sum over the number of letters that are taken. -/
theorem sum_segL (sep : List Bool) (f : ℕ) (tk : Bool) (cur : List Bool) (fs : List ℕ) (as rest out : List (List Bool))
    (G : List (List Bool) → A) : ((segL sep f tk cur fs as rest out).map G).sum =
      ∑ j ∈ range (rest.length + 1), if okFlag f (tk || decide (0 < j)) then
        ((closeL sep ((rest.take j).reverse.flatten ++ cur) fs as (rest.drop j) out).map G).sum else 0 := by
  induction rest generalizing tk cur with
  | nil =>
    rw [segL_eq']
    simp only [List.append_nil, List.length_nil, zero_add, range_one, sum_singleton, lt_self_iff_false,
      decide_false, Bool.or_false, List.take_nil, List.reverse_nil, List.flatten_nil, List.nil_append, List.drop_nil]
    split_ifs <;> simp
  | cons a r ih =>
    rw [segL_eq', List.map_append, List.sum_append, sum_range_succ']
    simp only [ih, List.length_cons, lt_self_iff_false, decide_false, Bool.or_false, List.take_zero,
      List.reverse_nil, List.flatten_nil, List.nil_append, List.drop_zero, List.take_succ_cons, List.drop_succ_cons,
      List.reverse_cons, List.flatten_append, List.flatten_cons, List.append_nil, List.append_assoc, Bool.true_or,
      Nat.zero_lt_succ, decide_true, Bool.or_true]
    rw [add_comm]
    congr 1
    split_ifs <;> simp

variable {Γ : Type} [Fintype Γ] [DecidableEq Γ]

theorem cat_snoc {m : ℕ} (X : Fin m → List Γ) (y : List Γ) :
    cat (Fin.snoc X y : Fin (m + 1) → List Γ) = cat X ++ y := by
  simp only [cat, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil]

/-- Cutting off the last segment. -/
theorem sum_cut {m : ℕ} (T : ℕ) (l : List Γ) (hT : l.length ≤ T) (p : Fin (m + 1) → List Γ → Prop)
    [∀ b, DecidablePred (p b)] (H : (Fin (m + 1) → List Γ) → A) :
    ∑ X ∈ (Fintype.piFinset fun _ : Fin (m + 1) => wordsLe Γ T).filter (fun X => cat X = l ∧ ∀ b, p b (X b)), H X =
      ∑ j ∈ range (l.length + 1), if p (Fin.last m) (l.drop (l.length - j)) then
        ∑ X ∈ (Fintype.piFinset fun _ : Fin m => wordsLe Γ T).filter
          (fun X => cat X = l.take (l.length - j) ∧ ∀ b, p b.castSucc (X b)),
          H (Fin.snoc X (l.drop (l.length - j))) else 0 := by
  have hinit : ∀ X : Fin (m + 1) → List Γ, cat X = cat (Fin.init X) ++ X (Fin.last m) := by
    intro X
    conv_lhs => rw [← Fin.snoc_init_self X]
    rw [cat_snoc]
  have hdrop : ∀ X : Fin (m + 1) → List Γ, cat X = l →
      cat (Fin.init X) = l.take (l.length - (X (Fin.last m)).length) ∧
      X (Fin.last m) = l.drop (l.length - (X (Fin.last m)).length) := by
    intro X hX
    rw [hinit] at hX
    have h1 : l.length = (cat (Fin.init X)).length + (X (Fin.last m)).length := by rw [← hX, List.length_append]
    have h2 : l.length - (X (Fin.last m)).length = (cat (Fin.init X)).length := by omega
    rw [h2, ← hX]
    simp
  rw [← sum_fiberwise_of_maps_to (s := (Fintype.piFinset fun _ : Fin (m + 1) => wordsLe Γ T).filter
    (fun X => cat X = l ∧ ∀ b, p b (X b))) (t := range (l.length + 1)) (g := fun X => (X (Fin.last m)).length)]
  · refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    split_ifs with hp
    · refine sum_nbij' (i := fun X => Fin.init X) (j := fun X => Fin.snoc X (l.drop (l.length - j))) ?_ ?_ ?_ ?_ ?_
      · intro X hX
        simp only [mem_filter, Fintype.mem_piFinset] at hX ⊢
        obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hX
        refine ⟨fun b => h1 _, ?_, fun b => h3 _⟩
        rw [← h4]
        exact (hdrop X h2).1
      · intro X hX
        simp only [mem_filter, Fintype.mem_piFinset] at hX ⊢
        obtain ⟨h1, h2, h3⟩ := hX
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · intro b
          refine Fin.lastCases ?_ (fun b => ?_) b
          · rw [Fin.snoc_last, mem_wordsLe, List.length_drop]
            omega
          · rw [Fin.snoc_castSucc]
            exact h1 b
        · rw [cat_snoc, h2, List.take_append_drop]
        · intro b
          refine Fin.lastCases ?_ (fun b => ?_) b
          · rw [Fin.snoc_last]
            exact hp
          · rw [Fin.snoc_castSucc]
            exact h3 b
        · rw [Fin.snoc_last, List.length_drop]
          omega
      · intro X hX
        simp only [mem_filter] at hX
        obtain ⟨⟨-, h2, -⟩, h4⟩ := hX
        have := (hdrop X h2).2
        rw [h4] at this
        rw [← this, Fin.snoc_init_self]
      · intro X _
        exact Fin.init_snoc _ _
      · intro X hX
        simp only [mem_filter] at hX
        obtain ⟨⟨-, h2, -⟩, h4⟩ := hX
        have := (hdrop X h2).2
        rw [h4] at this
        rw [← this, Fin.snoc_init_self]
    · refine sum_eq_zero fun X hX => ?_
      simp only [mem_filter] at hX
      obtain ⟨⟨-, h2, h3⟩, h4⟩ := hX
      exfalso
      apply hp
      have := (hdrop X h2).2
      rw [h4] at this
      rw [← this]
      exact h3 _
  · intro X hX
    simp only [mem_filter] at hX
    rw [mem_range, ← hX.2.1, hinit, List.length_append]
    omega

theorem drop_rev (bits : Γ → List Bool) (l : List Γ) (j : ℕ) :
    (l.map bits).reverse.drop j = ((l.take (l.length - j)).map bits).reverse := by
  rw [List.drop_reverse, List.length_map, List.map_take]

theorem take_rev (bits : Γ → List Bool) (l : List Γ) (j : ℕ) :
    ((l.map bits).reverse.take j).reverse.flatten = (l.drop (l.length - j)).flatMap bits := by
  rw [List.take_reverse, List.length_map, List.reverse_reverse, ← List.map_drop, List.flatMap_def]

theorem ofFn_rev {α : Type} {m : ℕ} (f : Fin (m + 1) → α) :
    (List.ofFn f).reverse = f (Fin.last m) :: (List.ofFn fun b => f b.castSucc).reverse := by
  rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
  rfl

theorem sum_segL_start (sep : List Bool) (bits : Γ → List Bool) (T : ℕ) {m : ℕ} (fl : Fin (m + 1) → ℕ)
    (acc : Fin (m + 1) → List Bool) (l : List Γ) (hT : l.length ≤ T) (out : List (List Bool))
    (G : List (List Bool) → A) :
    ((segL sep (fl (Fin.last m)) false (sep ++ acc (Fin.last m)) (List.ofFn fun b => fl b.castSucc).reverse
      (List.ofFn fun b => acc b.castSucc).reverse (l.map bits).reverse out).map G).sum =
    ∑ X ∈ (Fintype.piFinset fun _ : Fin (m + 1) => wordsLe Γ T).filter
      (fun X => cat X = l ∧ ∀ b, okFlag (fl b) (decide (X b ≠ [])) = true),
      G ((List.ofFn fun b => (X b).flatMap bits ++ (sep ++ acc b)) ++ out) := by
  induction m generalizing l out with
  | zero =>
    rw [sum_segL, sum_cut T l hT (fun b x => okFlag (fl b) (decide (x ≠ [])) = true), List.length_reverse,
      List.length_map]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    have e1 : decide (l.drop (l.length - j) ≠ []) = decide (0 < j) := by
      apply decide_eq_decide.2
      rw [← List.length_pos_iff, List.length_drop]
      omega
    simp only [Bool.false_or, e1]
    refine if_congr Iff.rfl ?_ rfl
    rw [take_rev, drop_rev]
    simp only [List.ofFn_zero, List.reverse_nil, closeL]
    have e2 : ∀ X : Fin 0 → List Γ, cat X = [] := fun X => by simp [cat]
    by_cases h : l.take (l.length - j) = []
    · rw [if_pos (by rw [h]; rfl), Finset.sum_eq_single (fun b : Fin 0 => b.elim0)]
      · have e3 : ∀ (X : Fin 0 → List Γ) (y : List Γ), (Fin.snoc X y : Fin 1 → List Γ) 0 = y :=
          fun X y => Fin.snoc_last (α := fun _ => List Γ) y X
        simp [List.ofFn_succ, e3]
      · intro X _ hX
        exact absurd (Subsingleton.elim _ _) hX
      · intro hX
        exfalso
        apply hX
        rw [mem_filter, Fintype.mem_piFinset]
        exact ⟨fun b => b.elim0, by rw [e2, h], fun b => b.elim0⟩
    · rw [if_neg (by simpa using h), Finset.sum_eq_zero]
      · rfl
      · intro X hX
        simp only [mem_filter, e2] at hX
        exact absurd hX.2.1.symm h
  | succ m ih =>
    rw [sum_segL, sum_cut T l hT (fun b x => okFlag (fl b) (decide (x ≠ [])) = true), List.length_reverse,
      List.length_map]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    have e1 : decide (l.drop (l.length - j) ≠ []) = decide (0 < j) := by
      apply decide_eq_decide.2
      rw [← List.length_pos_iff, List.length_drop]
      omega
    simp only [Bool.false_or, e1]
    refine if_congr Iff.rfl ?_ rfl
    rw [take_rev, drop_rev, ofFn_rev, ofFn_rev, closeL]
    have h := ih (fun b => fl b.castSucc) (fun b => acc b.castSucc) (l.take (l.length - j))
      ((List.length_take_le _ _).trans ((Nat.sub_le _ _).trans hT))
      (((l.drop (l.length - j)).flatMap bits ++ (sep ++ acc (Fin.last (m + 1)))) :: out)
    simp only [List.headD_cons, List.tail_cons]
    rw [h]
    refine sum_congr rfl fun X _ => ?_
    rw [List.ofFn_succ' (n := m + 1)]
    simp

/-- **The sum over the ways to cut a word.** -/
theorem sum_segRow' (sep : List Bool) {m : ℕ} (hm : 0 < m) (fl : Fin m → ℕ) (acc : Fin m → List Bool)
    (bits : Γ → List Bool) (T : ℕ) (l : List Γ) (hT : l.length ≤ T) (G : List (List Bool) → A) :
    ((segRow sep (List.ofFn fl).reverse (List.ofFn acc).reverse (l.map bits).reverse).map G).sum =
    ∑ X ∈ (Fintype.piFinset fun _ : Fin m => wordsLe Γ T).filter
      (fun X => cat X = l ∧ ∀ b, okFlag (fl b) (decide (X b ≠ [])) = true),
      G (List.ofFn fun b => (X b).flatMap bits ++ (sep ++ acc b)) := by
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h := sum_segL_start sep bits T fl acc l hT [] G
  rw [ofFn_rev, ofFn_rev, segRow]
  simpa only [List.headD_cons, List.tail_cons, List.append_nil] using h

end Nc.Grp
