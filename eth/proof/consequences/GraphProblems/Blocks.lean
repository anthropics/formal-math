/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GraphProblems.Interfaces
public import Mathlib.Algebra.BigOperators.Fin

/-! # Corollary 7: satisfaction of formulas by assignments to all natural numbers

`Sat f φ` says that the assignment f : ℕ → Bool makes a literal of every clause of φ true, and
`sat_append` splits it over the two parts of φ ++ χ. An assignment a to x₀ … xₙ₋₁
is extended by false to all natural numbers (`ext`), and `ext_val` says that this extension agrees
with a on x₀ … xₙ₋₁. -/

public section

namespace GraphProblems

open Groundwork Groundwork.Prog CountKSat Finset

namespace Blocks

/-- f makes a literal of every clause of φ true. -/
@[expose] def Sat (f : ℕ → Bool) (φ : Fml) : Prop := ∀ C ∈ φ, ∃ l ∈ C, f l.1 = l.2

theorem sat_append (f : ℕ → Bool) (φ χ : Fml) : Sat f (φ ++ χ) ↔ Sat f φ ∧ Sat f χ := by
  simp only [Sat, List.mem_append, or_imp, forall_and]

/-! ### Assignments as functions on all natural numbers -/

theorem ext_val {n : ℕ} (a : Fin n → Bool) (k : Fin n) : ext a k = a k := dif_pos k.2

end Blocks

end GraphProblems
