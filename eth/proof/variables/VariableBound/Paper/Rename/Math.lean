/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import MainTheoremFormsStatement
public import VariableBound.Paper.Rename.Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Dedup
import Mathlib.Logic.Equiv.Prod

/-! # Renaming the variables that occur: the mathematics

For a formula φ over x₀ … x_(N−1) in which n variables occur, `ren φ` is φ with every variable
replaced by its position in the list `occL` of the variables that occur: a formula over x₀ …
x_(n−1).
* `toN_ren`: with natural numbers as variables, it is what the program `renL` computes.
* `isKCNF_ren`, `allOccur_ren`, `length_ren`: it is a k-CNF if φ is, all its variables occur, and it
  has as many clauses as φ.
* `numSat_ren`: its number of satisfying assignments is the number of satisfying assignments of φ,
  as assignments of the variables that occur.
* `numSat_eq`: the sentence after Corollary 11, numSat φ = 2^(N−n)·numSatOcc φ. `allOccurStmt`: if
  all variables occur, the two ways of counting agree. -/

public section

namespace VariableBound.Rename

open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Sat3 (CNF)

/-! ### The list of the variables that occur -/

/-- A number is in `occL ψ` if and only if it is the variable of a literal of a clause of ψ. -/
theorem mem_occL {ψ : Fml} {v : ℕ} : v ∈ occL ψ ↔ ∃ C ∈ ψ, ∃ l ∈ C, l.1 = v := by
  simp only [occL, List.mem_dedup, List.mem_flatMap, List.mem_map]

/-- No number is twice in `occL ψ`. -/
theorem nodup_occL (ψ : Fml) : (occL ψ).Nodup := List.nodup_dedup _

variable {N : ℕ} (φ : CNF N)

/-- The variables in the list, for a formula over x₀ … x_(N−1), are those that occur. -/
theorem val_mem_occL {i : Fin N} : i.val ∈ occL (toN φ) ↔ Occurs φ i := by
  rw [mem_occL]
  constructor
  · rintro ⟨C, hC, l, hl, h⟩
    obtain ⟨C', hC', rfl⟩ := List.mem_map.1 hC
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    exact ⟨C', hC', l', hl', Fin.ext h⟩
  · rintro ⟨C, hC, l, hl, h⟩
    exact ⟨_, List.mem_map_of_mem hC, _, List.mem_map_of_mem hl, congrArg Fin.val h⟩

/-- Every number in the list is a variable of φ that occurs. -/
theorem exists_of_mem_occL {v : ℕ} (h : v ∈ occL (toN φ)) : ∃ i : Fin N, i.val = v ∧ Occurs φ i := by
  obtain ⟨C, hC, l, hl, rfl⟩ := mem_occL.1 h
  obtain ⟨C', hC', rfl⟩ := List.mem_map.1 hC
  obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
  exact ⟨l'.1, rfl, C', hC', l', hl', rfl⟩

/-- The position of a variable that occurs. -/
def pos0 (i : {i : Fin N // Occurs φ i}) : Fin (occL (toN φ)).length :=
  ⟨(occL (toN φ)).idxOf i.1.val, List.idxOf_lt_length_iff.2 ((val_mem_occL φ).2 i.2)⟩

/-- The position is a bijection from the variables that occur to the positions of the list. -/
theorem pos0_bijective : Function.Bijective (pos0 φ) := by
  constructor
  · intro i j h
    have h' : (occL (toN φ)).idxOf i.1.val = (occL (toN φ)).idxOf j.1.val := congrArg Fin.val h
    exact Subtype.ext (Fin.ext ((List.idxOf_inj ((val_mem_occL φ).2 i.2)).1 h'))
  · intro j
    obtain ⟨i, hi, ho⟩ := exists_of_mem_occL φ (List.getElem_mem j.2)
    refine ⟨⟨i, ho⟩, Fin.ext ?_⟩
    simp only [pos0, hi]
    exact (nodup_occL _).idxOf_getElem j.1 j.2

/-- The length of the list is the number of variables that occur. -/
theorem length_occL : (occL (toN φ)).length = numOcc φ := by
  rw [numOcc, Nat.card_congr (Equiv.ofBijective _ (pos0_bijective φ)), Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The renaming: a bijection from the variables that occur to 0, …, n − 1. -/
noncomputable def pos : {i : Fin N // Occurs φ i} ≃ Fin (numOcc φ) :=
  (Equiv.ofBijective _ (pos0_bijective φ)).trans (finCongr (length_occL φ))

/-- The new name of a variable is its position in the list. -/
theorem val_pos (i : {i : Fin N // Occurs φ i}) : (pos φ i).val = (occL (toN φ)).idxOf i.1.val := by
  simp [pos, pos0]

/-! ### The renamed formula -/

open Classical in
/-- φ with the variables that occur renamed to 0, …, n − 1. -/
noncomputable def ren : CNF (numOcc φ) :=
  φ.map fun C => C.filterMap fun l => if h : Occurs φ l.1 then some (pos φ ⟨l.1, h⟩, l.2) else none

/-- With natural numbers as variables, the renamed formula is what the program computes. -/
theorem toN_ren : toN (ren φ) = renL (occL (toN φ)) (toN φ) := by
  classical
  simp only [toN, ren, renL, List.map_map]
  refine List.map_congr_left fun C hC => ?_
  simp only [Function.comp_apply, List.map_filterMap, List.map_map]
  rw [← List.filterMap_eq_map]
  refine List.filterMap_congr fun l hl => ?_
  have h : Occurs φ l.1 := ⟨C, hC, l, hl, rfl⟩
  simp [h, val_pos, toN]

/-- The renamed formula has as many clauses as φ. -/
theorem length_ren : (ren φ).length = φ.length := by
  simp [ren]

/-- Putting the old names back: the inverse of the renaming on clauses all of whose variables are in
the list L. -/
theorem map_back {L : List ℕ} {C : List (ℕ × Bool)} (h : ∀ l ∈ C, l.1 ∈ L) :
    (C.map fun l => (L.idxOf l.1, l.2)).map (fun l => (L.getD l.1 0, l.2)) = C := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id C]
  refine List.map_congr_left fun l hl => ?_
  have h1 := List.idxOf_lt_length_iff.2 (h l hl)
  simp [List.getElem?_eq_getElem h1]

/-- If φ is a k-CNF, so is the renamed formula. -/
theorem isKCNF_ren {k : ℕ} (h : SatK.IsKCNF k φ) : SatK.IsKCNF k (ren φ) := by
  constructor
  · intro C' hC'
    have h1 : C'.map (fun l => (l.1.val, l.2)) ∈ toN (ren φ) := List.mem_map_of_mem hC'
    rw [toN_ren] at h1
    obtain ⟨D, hD, hD'⟩ := List.mem_map.1 h1
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hD
    have h2 := congrArg List.length hD'
    simp only [List.length_map] at h2
    rw [← h2]
    exact h.1 C hC
  · have h1 : (toN φ).Nodup := by
      refine List.Nodup.map (List.map_injective_iff.2 fun a b hab => ?_) h.2
      exact Prod.ext (Fin.ext (Prod.ext_iff.1 hab).1) (Prod.ext_iff.1 hab).2
    have h2 : (toN (ren φ)).Nodup := by
      rw [toN_ren]
      refine List.Nodup.map_on (fun C hC D hD hCD => ?_) h1
      rw [← map_back (L := occL (toN φ)) (C := C) fun l hl => mem_occL.2 ⟨C, hC, l, hl, rfl⟩,
        ← map_back (L := occL (toN φ)) (C := D) fun l hl => mem_occL.2 ⟨D, hD, l, hl, rfl⟩, hCD]
    exact List.Nodup.of_map _ h2

/-- An assignment a of x₀ … x_(n−1) satisfies the renamed formula if and only if the assignment «a
at the new name» of the variables that occur satisfies φ. -/
theorem sat_ren_iff (a : Fin (numOcc φ) → Bool) :
    (∀ C ∈ ren φ, ∃ l ∈ C, a l.1 = l.2) ↔ ∀ C ∈ φ, ∃ l ∈ C, ∃ h : Occurs φ l.1, a (pos φ ⟨l.1, h⟩) = l.2 := by
  classical
  simp only [ren, List.forall_mem_map, List.mem_filterMap]
  refine forall₂_congr fun C hC => ?_
  constructor
  · rintro ⟨l', ⟨l, hl, hl'⟩, ha⟩
    have h : Occurs φ l.1 := ⟨C, hC, l, hl, rfl⟩
    rw [dif_pos h, Option.some_inj] at hl'
    subst hl'
    exact ⟨l, hl, h, ha⟩
  · rintro ⟨l, hl, h, ha⟩
    exact ⟨_, ⟨l, hl, dif_pos h⟩, ha⟩

/-- All variables of the renamed formula occur. -/
theorem allOccur_ren : SatM.AllOccur (ren φ) := by
  classical
  intro j
  obtain ⟨C, hC, l, hl, h⟩ := ((pos φ).symm j).2
  have ho : Occurs φ l.1 := ⟨C, hC, l, hl, rfl⟩
  refine ⟨_, List.mem_map_of_mem hC, (pos φ ⟨l.1, ho⟩, l.2), List.mem_filterMap.2 ⟨l, hl, dif_pos ho⟩, ?_⟩
  have : (⟨l.1, ho⟩ : {i : Fin N // Occurs φ i}) = (pos φ).symm j := Subtype.ext h
  simp [this]

/-- The number of satisfying assignments of the renamed formula is the number of satisfying
assignments of φ, as assignments of the variables that occur. -/
theorem numSat_ren : SatK.numSat (ren φ) = numSatOcc φ := by
  rw [SatK.numSat, numSatOcc, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (((Equiv.arrowCongr (pos φ) (Equiv.refl Bool)).symm).subtypeEquiv fun a => ?_)
  rw [sat_ren_iff]
  simp [Equiv.arrowCongr]

/-! ### The sentence after Corollary 11 -/

/-- At most N variables occur in a formula over x₀ … x_(N−1). -/
theorem numOcc_le : numOcc φ ≤ N := by
  have h := Nat.card_le_card_of_injective (Subtype.val : {i : Fin N // Occurs φ i} → Fin N) Subtype.val_injective
  rwa [Nat.card_eq_fintype_card (α := Fin N), Fintype.card_fin] at h

/-- The number of variables that do not occur. -/
theorem card_not_occurs : Nat.card {i : Fin N // ¬ Occurs φ i} = N - numOcc φ := by
  classical
  rw [numOcc, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin]

/-- The sentence after Corollary 11: for a formula on N variables of which n occur, the number of
satisfying assignments of all N variables is 2^(N−n) times the number of satisfying assignments as
assignments of the n variables that occur. -/
theorem numSat_eq : SatK.numSat φ = 2 ^ (N - numOcc φ) * numSatOcc φ := by
  classical
  rw [SatK.numSat, numSatOcc, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, ← card_not_occurs, mul_comm]
  have e1 : {a : Fin N → Bool // ∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2} ≃
      {p : ({i : Fin N // Occurs φ i} → Bool) × ({i : Fin N // ¬ Occurs φ i} → Bool) // ∀ C ∈ φ, ∃ l ∈ C, ∃ h : Occurs φ l.1, p.1 ⟨l.1, h⟩ = l.2} :=
    (Equiv.piEquivPiSubtypeProd (Occurs φ) fun _ => Bool).subtypeEquiv fun a => by
      refine forall₂_congr fun C hC => ⟨?_, ?_⟩
      · rintro ⟨l, hl, h⟩
        exact ⟨l, hl, ⟨C, hC, l, hl, rfl⟩, h⟩
      · rintro ⟨l, hl, _, h⟩
        exact ⟨l, hl, h⟩
  rw [Nat.card_congr (e1.trans (Equiv.prodSubtypeFstEquivSubtypeProd
    (p := fun b : {i : Fin N // Occurs φ i} → Bool => ∀ C ∈ φ, ∃ l ∈ C, ∃ h : Occurs φ l.1, b ⟨l.1, h⟩ = l.2))), Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]

/-- If all variables occur, n is the number of all variables, and the number of satisfying
assignments, as assignments of the variables that occur, is `SatK.numSat`. -/
theorem allOccurStmt : AllOccurStmt := fun n φ h => by
  have h1 : numOcc φ = n := by
    rw [numOcc, Nat.card_congr (Equiv.subtypeUnivEquiv (p := Occurs φ) h), Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨h1, ?_⟩
  rw [numSat_eq φ, h1]
  simp

end VariableBound.Rename
