/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.RunPerm

/-!
# Automata with one input
-/

namespace Nc

open Finset MvPolynomial

set_option linter.unusedSectionVars false

section Rename

variable {S J J' Γ : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  [Fintype J'] [DecidableEq J']

/-- Renaming the inputs. -/
def chEquiv (S : Type) (φ : J ≃ J') : Ch S J ≃ Ch S J' where
  toFun z := match z with
    | .tp s b => .tp s b
    | .inp j => .inp (φ j)
  invFun z := match z with
    | .tp s b => .tp s b
    | .inp j => .inp (φ.symm j)
  left_inv z := by cases z <;> simp
  right_inv z := by cases z <;> simp

/-- Renaming the inputs in letters. -/
def letterEquiv (S Γ : Type) (φ : J ≃ J') : Letter S J Γ ≃ Letter S J' Γ :=
  Equiv.optionCongr (Equiv.prodCongr (chEquiv S φ) (Equiv.refl Γ))

theorem emit_rename (φ : J ≃ J') (o : List (Letter S J Γ)) (z : Ch S J) :
    emit (o.map (letterEquiv S Γ φ)) (chEquiv S φ z) = emit o z := by
  induction o with
  | nil => rfl
  | cons a o ih =>
    rw [List.map_cons, ← List.singleton_append, emit_appendR, ih, ← List.singleton_append (l := o), emit_appendR]
    congr 1
    rcases a with _ | ⟨z', γ⟩
    · rfl
    · have : letterEquiv S Γ φ (some (z', γ)) = some (chEquiv S φ z', γ) := rfl
      rw [this, emit_some, emit_some]
      simp

variable {F : Type*} [CommRing F] {Q : Type} [Fintype Q] [DecidableEq Q]

/-- Renaming the inputs does not change the value. -/
theorem runVal_rename (φ : J ≃ J') (mu : Letter S J' Γ → Matrix Q Q F) (i e : Q) (t : ℕ) (u : J' → List Γ) :
    runVal (fun a => mu (letterEquiv S Γ φ a)) i e t (fun j => u (φ j)) = runVal mu i e t u := by
  unfold runVal
  refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl _) (letterEquiv S Γ φ)) _ _ fun o => ?_
  have hl : List.ofFn (Equiv.arrowCongr (Equiv.refl (Fin t)) (letterEquiv S Γ φ) o) =
      (List.ofFn o).map (letterEquiv S Γ φ) := by
    rw [List.map_ofFn]
    rfl
  have hm : Matched (List.ofFn o) (fun j => u (φ j)) ↔ Matched ((List.ofFn o).map (letterEquiv S Γ φ)) u := by
    unfold Matched
    refine and_congr (forall_congr' fun s => ?_) ?_
    · have h1 := emit_rename φ (List.ofFn o) (.tp s false)
      have h2 := emit_rename φ (List.ofFn o) (.tp s true)
      rw [← h1, ← h2]
      rfl
    · constructor
      · intro h j
        have h1 := emit_rename φ (List.ofFn o) (.inp (φ.symm j))
        have h2 : chEquiv S φ (.inp (φ.symm j)) = .inp j := by simp [chEquiv]
        have h3 := h (φ.symm j)
        rw [h2] at h1
        rw [h1, h3]
        exact congrArg u (φ.apply_symm_apply j)
      · intro h j
        exact (emit_rename φ (List.ofFn o) (.inp j)).symm.trans (h (φ j))
  rw [hl]
  by_cases h : Matched (List.ofFn o) (fun j => u (φ j))
  · rw [if_pos h, if_pos (hm.1 h), List.map_map]
    rfl
  · rw [if_neg h, if_neg fun h' => h (hm.2 h')]

end Rename

variable {F : Type*} [Field F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q]

/-- The one-hot code of a word with an end marker. -/
def code1 (N : ℕ) (u : List Γ) (p : Fin N × Option Γ) : Bool := (u.map some ++ [none])[p.1.1]? = some p.2

end Nc
