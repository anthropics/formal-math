/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.PutSum
import Nc.Grp.GroupProg
import Nc.Grp.SumSim

/-!
# Writing several strings
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

/-- Write the units of several strings. -/
def putsAll (ub : ℕ) : List (List (List Bool) × List Bool) → Tree → Tree
  | [], t => t
  | p :: r, t => putsAll ub r (putAll p.1 (fun i => uwBits (unitsOf ub p.2 i)) t)

theorem putsL_eq {ub : ℕ} (hub : 0 < ub) (P : List (List (List Bool) × List Bool)) (t : Tree) :
    putsL ub (P.map Prod.fst) (P.map fun p => p.2 ++ [true]) t =
      if ∀ p ∈ P, ucount ub p.2 = p.1.length then [putsAll ub P t] else [] := by
  induction P generalizing t with
  | nil => simp [putsL, putsAll]
  | cons p P ih =>
    rw [List.map_cons, List.map_cons, putsL, List.headD_cons, List.tail_cons, putL_eq hub]
    by_cases hp : ucount ub p.2 = p.1.length
    · rw [if_pos hp, List.flatMap_cons, List.flatMap_nil, List.append_nil, ih]
      by_cases hP : ∀ p ∈ P, ucount ub p.2 = p.1.length
      · rw [if_pos hP, if_pos (by
          intro p' hp'
          rcases List.mem_cons.1 hp' with rfl | hp'
          · exact hp
          · exact hP p' hp')]
        rfl
      · rw [if_neg hP, if_neg fun h => hP fun p' hp' => h p' (List.mem_cons_of_mem _ hp')]
    · rw [if_neg hp, if_neg fun h => hp (h p List.mem_cons_self)]
      rfl

theorem tget_putsAll_not {ub : ℕ} {P : List (List (List Bool) × List Bool)} (hP : (P.flatMap Prod.fst).Nodup)
    {k : List Bool} (hk : k ∉ P.flatMap Prod.fst) (t : Tree) : tget k (putsAll ub P t) = tget k t := by
  induction P generalizing t with
  | nil => rfl
  | cons p P ih =>
    rw [List.flatMap_cons, List.nodup_append] at hP
    rw [List.flatMap_cons, List.mem_append, not_or] at hk
    rw [putsAll, ih hP.2.1 hk.2, tget_putAll _ hP.1, if_neg hk.1]

theorem tget_putsAll {ub : ℕ} {P : List (List (List Bool) × List Bool)} (hP : (P.flatMap Prod.fst).Nodup)
    {p : List (List Bool) × List Bool} (hp : p ∈ P) {i : ℕ} {k : List Bool} (hk : p.1[i]? = some k) (t : Tree) :
    tget k (putsAll ub P t) = ofBits (uwBits (unitsOf ub p.2 i)) := by
  induction P generalizing t with
  | nil => simp at hp
  | cons p' P ih =>
    rw [List.flatMap_cons, List.nodup_append] at hP
    rw [putsAll]
    rcases List.mem_cons.1 hp with rfl | hp
    · have hmem : k ∈ p.1 := List.mem_of_getElem? hk
      have hnot : k ∉ P.flatMap Prod.fst := fun h => hP.2.2 k hmem k h rfl
      rw [tget_putsAll_not hP.2.1 hnot, tget_putAll _ hP.1, if_pos hmem]
      congr 3
      obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hk
      exact hP.1.idxOf_getElem i hi
    · exact ih hP.2.1 hp _

theorem TOk.putAll {ub : ℕ} {keys : List (List Bool)} {u : ℕ → List Bool} (hu : ∀ i, (u i).length ≤ ub) {t : Tree}
    (h : TOk ub t) : TOk ub (putAll keys u t) := by
  induction keys generalizing u t with
  | nil => exact h
  | cons k ks ih => exact ih (fun i => hu (i + 1)) (h.tset k _ (hu 0))

theorem length_uwBits_le {ub : ℕ} (w : UW ub) : (uwBits w).length ≤ ub := by
  cases w with
  | none => exact Nat.zero_le _
  | some w => simp [uwBits]

theorem TOk.putsAll {ub : ℕ} {P : List (List (List Bool) × List Bool)} {t : Tree} (h : TOk ub t) :
    TOk ub (Grp.putsAll ub P t) := by
  induction P generalizing t with
  | nil => exact h
  | cons p P ih => exact ih (h.putAll fun i => length_uwBits_le _)

/-- The first numbers. -/
theorem filter_finRange {U c : ℕ} (h : c ≤ U) :
    (List.finRange U).filter (fun k => k.1 < c) = List.ofFn fun i : Fin c => Fin.castLE h i := by
  have h1 : Function.Injective (List.map (Fin.val : Fin U → ℕ)) := List.map_injective_iff.2 Fin.val_injective
  apply h1
  have h2 : ((List.finRange U).filter (fun k => k.1 < c)).map Fin.val = (List.range U).filter (fun k => k < c) := by
    rw [← List.map_coe_finRange_eq_range, List.filter_map]
    rfl
  have h3 : (List.range U).filter (fun k => k < c) = List.range c := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [List.range_add, List.filter_append]
    have e1 : (List.range c).filter (fun k => k < c) = List.range c :=
      List.filter_eq_self.2 fun k hk => by simpa using hk
    have e2 : ((List.range d).map (c + ·)).filter (fun k => k < c) = [] :=
      List.filter_eq_nil_iff.2 fun k hk => by
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hk
        simp
    rw [e1, e2, List.append_nil]
  rw [h2, h3, List.map_ofFn]
  apply List.ext_getElem
  · simp
  · intro i h4 h5
    simp

variable {A : Type} [CommRing A] {θ : List Bool → A}
variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] {c : ℕ}
  {mu : Letter S Unit Γ → Matrix Q Q A} {cb : Option Γ → Fin c → Bool} {kinds : List (Σ L : G.Law A, L.Ro)}

theorem sumL_script_cons (T ub : ℕ) (i : Ins) (l : List Ins) (t : Tree) (Ψ : Tree → A) :
    sumL (scriptSem (S := S) θ mu cb kinds T ub (i :: l) t) Ψ = sumL (insSem (S := S) θ mu cb kinds T ub i t) fun t' =>
      sumL (scriptSem (S := S) θ mu cb kinds T ub l t') Ψ := by
  rw [scriptSem, foldL, sumL_bindL]
  rfl

theorem sumL_script_nil (T ub : ℕ) (t : Tree) (Ψ : Tree → A) :
    sumL (scriptSem (S := S) θ mu cb kinds T ub [] t) Ψ = Ψ t := by
  rw [scriptSem, foldL, sumL_single]

theorem sumL_script_append (T ub : ℕ) (l l' : List Ins) (t : Tree) (Ψ : Tree → A) :
    sumL (scriptSem (S := S) θ mu cb kinds T ub (l ++ l') t) Ψ =
      sumL (scriptSem (S := S) θ mu cb kinds T ub l t) fun t' =>
        sumL (scriptSem (S := S) θ mu cb kinds T ub l' t') Ψ :=
  foldL_append _ _ _ _ _

/-- Several comparisons. -/
theorem sumL_boths {ι : Type} (T ub : ℕ) (ks : List ι) (f g : ι → List Bool) (t : Tree) (Ψ : Tree → A) :
    sumL (scriptSem (S := S) θ mu cb kinds T ub (ks.map fun k => Ins.both (f k) (g k)) t) Ψ =
      if ∀ k ∈ ks, tget (f k) t = tget (g k) t then Ψ t else 0 := by
  induction ks with
  | nil => simp [sumL_script_nil]
  | cons k ks ih =>
    rw [List.map_cons, sumL_script_cons, insSem]
    by_cases h : tget (f k) t = tget (g k) t
    · rw [if_pos h, sumL_single, ih]
      by_cases h' : ∀ k ∈ ks, tget (f k) t = tget (g k) t
      · rw [if_pos h', if_pos (by
          intro k' hk'
          rcases List.mem_cons.1 hk' with rfl | hk'
          · exact h
          · exact h' k' hk')]
      · rw [if_neg h', if_neg fun h1 => h' fun k' hk' => h1 k' (List.mem_cons_of_mem _ hk')]
    · rw [if_neg h, sumL_nil, if_neg fun h1 => h (h1 k List.mem_cons_self)]

end Nc.Grp
