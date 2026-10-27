/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSatStatement

/-! Plain facts on the formulas and on the code `Sat3.enc` of the 3-SAT statement in
`ThreeSatStatement`: an instance of 3-SAT on n variables has at most (2n+1)³
clauses, a clause of at most 3 literals is known by its first 3 slots, and a header 1ⁿ 0 delimits
itself. -/

namespace Sat3

/-- A clause of at most 3 literals is known by its first 3 slots. -/
theorem eq_of_slots {n : ℕ} {C D : List (Lit n)} (hC : C.length ≤ 3) (hD : D.length ≤ 3)
    (h : ∀ j < 3, C[j]? = D[j]?) : C = D :=
  List.ext_getElem? fun j => by
    by_cases hj : j < 3
    · exact h j hj
    · rw [List.getElem?_eq_none (by grind), List.getElem?_eq_none (by grind)]

/-- An instance on n variables has at most (2n+1)³ clauses, so its code is polynomially long. -/
public theorem Is3CNF.length_le {n : ℕ} {φ : CNF n} (h : Is3CNF φ) : φ.length ≤ (2 * n + 1) ^ 3 := by
  have := (h.2.map_on (f := fun C (j : Fin 3) => C[(j : ℕ)]?) fun C hC D hD e =>
    eq_of_slots (h.1 C hC) (h.1 D hD) fun j hj => congrFun e ⟨j, hj⟩).length_le_card
  simpa [mul_comm] using this

/-! ### The header of the code -/

/-- The header 1ⁿ 0 delimits itself. -/
theorem eq_of_header : ∀ {n m : ℕ} {l l' : List Bool},
    List.replicate n true ++ false :: l = List.replicate m true ++ false :: l' → n = m ∧ l = l'
  | 0, 0, _, _, h => by simpa using h
  | 0, _ + 1, _, _, h => by simp [List.replicate_succ] at h
  | _ + 1, 0, _, _, h => by simp [List.replicate_succ] at h
  | n + 1, m + 1, _, _, h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨rfl, rfl⟩ := eq_of_header h
    exact ⟨rfl, rfl⟩

end Sat3
