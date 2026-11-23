/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.RunPerm

/-!
# Values of automata: names of inputs, change of rings
-/

set_option linter.unusedSectionVars false

namespace Nc

open Finset

variable {A : Type*} [CommRing A] {Γ S Q : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q]

/-- Change of rings. -/
theorem runVal_map {J : Type*} [DecidableEq J] [Fintype J] {K : Type*} [CommRing K] (φ : A →+* K)
    (mu : Letter S J Γ → Matrix Q Q A) (i e : Q) (t : ℕ) (u : J → List Γ) :
    runVal (fun a => (mu a).map φ) i e t u = φ (runVal mu i e t u) := by
  unfold runVal
  rw [map_sum]
  refine sum_congr rfl fun o _ => ?_
  have h : ∀ L : List (Letter S J Γ), (L.map fun a => (mu a).map φ).prod = ((L.map mu).prod).map φ := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih => rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, Matrix.map_mul]
  split_ifs
  · rw [h, Matrix.map_apply]
  · rw [map_zero]

end Nc
