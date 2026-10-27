/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Groundwork.Net.Defs
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-! The double loop over i < i' below g tests the pairs in `pairs (Fin g)`. -/

namespace Groundwork.Prog

open Finset

/-- The double loop over i' > i, as a test on the pairs. -/
public theorem all_pairs_iff (g : ℕ) (p : ℕ → ℕ → Bool) :
    ((List.range g).all fun i => (List.range g).all fun i' => decide (i' ≤ i) || p i i') = true ↔
      ∀ q ∈ pairs (Fin g), p q.1 q.2 = true := by
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq, pairs, mem_filter, mem_univ,
    true_and]
  constructor
  · rintro h ⟨a, b⟩ hab
    exact (h a a.2 b b.2).resolve_left (by have : a.val < b.val := hab; omega)
  · intro h i hi i' hi'
    by_cases hle : i' ≤ i
    · exact Or.inl hle
    · exact Or.inr (h (⟨i, hi⟩, ⟨i', hi'⟩) (show i < i' by omega))

end Groundwork.Prog
