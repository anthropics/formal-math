/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.SegSum
import Nc.Grp.SumSim

/-!
# Sums over the ways to cut the letters of all tapes
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open Finset

variable {A : Type} [CommRing A]

/-- Functions with values in a finite set. -/
theorem sum_pi_coe {ι β : Type} [Fintype ι] [DecidableEq ι] [DecidableEq β] (s : Finset β) (f : (ι → β) → A) :
    ∑ x ∈ Fintype.piFinset fun _ : ι => s, f x = ∑ x : ι → s, f fun i => (x i : β) := by
  symm
  refine Finset.sum_bij (fun (x : ι → s) _ => fun i => (x i : β)) ?_ ?_ ?_ ?_
  · intro x _
    exact Fintype.mem_piFinset.2 fun i => (x i).2
  · intro x _ y _ h
    funext i
    exact Subtype.ext (congrFun h i)
  · intro y hy
    exact ⟨fun i => ⟨y i, Fintype.mem_piFinset.1 hy i⟩, Finset.mem_univ _, rfl⟩
  · intro x _
    rfl

variable {Γ : Type} [Fintype Γ] [DecidableEq Γ]

/-- Words of length at most `T`, as a type. -/
abbrev Wt (Γ : Type) [Fintype Γ] [DecidableEq Γ] (T : ℕ) := ↥(wordsLe Γ T)

/-- The string of a partner. -/
def joined (bits : Γ → List Bool) (sep : List Bool) {N : ℕ} (X : Fin N → List Γ) : List Bool :=
  (List.ofFn fun i => (X i).flatMap bits ++ sep).flatten

theorem joined_snoc (bits : Γ → List Bool) (sep : List Bool) {N : ℕ} (X : Fin N → List Γ) (y : List Γ) :
    joined bits sep (Fin.snoc X y : Fin (N + 1) → List Γ) = joined bits sep X ++ (y.flatMap bits ++ sep) := by
  simp only [joined, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil]

/-- The condition on the segments of a tape. -/
def CutOk {m : ℕ} (fl : Fin m → ℕ) (l : List Γ) (X : Fin m → List Γ) : Prop :=
  cat X = l ∧ ∀ b, okFlag (fl b) (decide (X b ≠ [])) = true

instance {m : ℕ} (fl : Fin m → ℕ) (l : List Γ) (X : Fin m → List Γ) : Decidable (CutOk fl l X) := by
  unfold CutOk
  infer_instance

/-- One tape. -/
theorem sumL_segOne (sep : List Bool) {m : ℕ} (hm : 0 < m) (fl : Fin m → ℕ) (acc : Fin m → List Bool)
    (bits : Γ → List Bool) (T : ℕ) (l : List Γ) (hT : l.length ≤ T) (G : List (List Bool) → A) :
    sumL (segOne A sep ((List.ofFn fl).reverse, (l.map bits).reverse) (List.ofFn acc).reverse) G =
      ∑ X : Fin m → Wt Γ T, if CutOk fl l (fun b => (X b : List Γ)) then
        G (List.ofFn fun b => (X b : List Γ).flatMap bits ++ (sep ++ acc b)).reverse else 0 := by
  have h := sum_segRow' sep hm fl acc bits T l hT fun out => G out.reverse
  rw [Finset.sum_filter, sum_pi_coe] at h
  rw [sumL, segOne, List.map_map]
  simp only [Function.comp_def, one_mul]
  rw [h]
  refine Finset.sum_congr rfl fun X _ => ?_
  by_cases hX : CutOk fl l (fun b => (X b : List Γ))
  · exact (if_pos hX).trans (if_pos hX).symm
  · exact (if_neg hX).trans (if_neg hX).symm

/-- **All tapes.** -/
theorem sumL_segs (sep : List Bool) {m : ℕ} (hm : 0 < m) (bits : Γ → List Bool) (T : ℕ) {N : ℕ} (fl : Fin N → Fin m → ℕ)
    (l : Fin N → List Γ) (hT : ∀ i, (l i).length ≤ T) (acc : Fin m → List Bool) (G : List (List Bool) → A) :
    sumL (segsL A sep (List.ofFn fun i : Fin N => ((List.ofFn (fl i.rev)).reverse, ((l i.rev).map bits).reverse))
        (List.ofFn acc).reverse) G =
      ∑ X : Fin N → Fin m → Wt Γ T, if ∀ i, CutOk (fl i) (l i) (fun b => (X i b : List Γ)) then
        G (List.ofFn fun b => joined bits sep (fun i => (X i b : List Γ)) ++ acc b).reverse else 0 := by
  induction N generalizing acc with
  | zero =>
    rw [List.ofFn_zero, segsL, foldL, sumL_single, Fintype.sum_unique, if_pos fun i => i.elim0]
    rfl
  | succ N ih =>
    rw [List.ofFn_succ, segsL, foldL, sumL_bindL]
    have e0 : (0 : Fin (N + 1)).rev = Fin.last N := Fin.rev_zero N
    have e1 : (List.ofFn fun i : Fin N => ((List.ofFn (fl i.succ.rev)).reverse, ((l i.succ.rev).map bits).reverse)) =
        List.ofFn fun i : Fin N => ((List.ofFn (fl i.rev.castSucc)).reverse, ((l i.rev.castSucc).map bits).reverse) := by
      congr 1
      funext i
      rw [Fin.rev_succ]
    rw [e0, e1, sumL_segOne sep hm (fl (Fin.last N)) acc bits T (l (Fin.last N)) (hT _)]
    rw [← (Fin.snocEquiv fun _ : Fin (N + 1) => Fin m → Wt Γ T).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun Y _ => ?_
    by_cases hY : CutOk (fl (Fin.last N)) (l (Fin.last N)) (fun b => (Y b : List Γ))
    · rw [if_pos hY]
      have h2 := ih (fun i => fl i.castSucc) (fun i => l i.castSucc) (fun i => hT _)
        (fun b => (Y b : List Γ).flatMap bits ++ (sep ++ acc b))
      rw [segsL] at h2
      rw [h2]
      refine Finset.sum_congr rfl fun X _ => ?_
      have e2 : (Fin.snocEquiv fun _ : Fin (N + 1) => Fin m → Wt Γ T) (Y, X) = Fin.snoc X Y := rfl
      have e3 : (∀ i, CutOk (fl i) (l i) fun b =>
          (((Fin.snocEquiv fun _ : Fin (N + 1) => Fin m → Wt Γ T) (Y, X)) i b : List Γ)) ↔
          ∀ i : Fin N, CutOk (fl i.castSucc) (l i.castSucc) fun b => (X i b : List Γ) := by
        rw [e2]
        constructor
        · intro h i
          have := h i.castSucc
          simpa only [Fin.snoc_castSucc] using this
        · intro h i
          refine Fin.lastCases ?_ (fun i => ?_) i
          · simpa only [Fin.snoc_last] using hY
          · simpa only [Fin.snoc_castSucc] using h i
      have e4 : ∀ b, (fun i => (((Fin.snocEquiv fun _ : Fin (N + 1) => Fin m → Wt Γ T) (Y, X)) i b : List Γ)) =
          (Fin.snoc (fun i => (X i b : List Γ)) (Y b : List Γ) : Fin (N + 1) → List Γ) := by
        intro b
        rw [e2]
        funext i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · rw [Fin.snoc_last, Fin.snoc_last]
        · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      refine if_congr e3.symm ?_ rfl
      congr 2
      congr 1
      funext b
      rw [e4, joined_snoc]
      simp only [List.append_assoc]
    · rw [if_neg hY]
      symm
      refine Finset.sum_eq_zero fun X _ => if_neg fun h => hY ?_
      have := h (Fin.last N)
      have e2 : (Fin.snocEquiv fun _ : Fin (N + 1) => Fin m → Wt Γ T) (Y, X) = Fin.snoc X Y := rfl
      rw [e2] at this
      simpa only [Fin.snoc_last] using this

end Nc.Grp
