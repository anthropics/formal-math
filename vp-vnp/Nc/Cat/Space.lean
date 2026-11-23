/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cat.Core

/-!
# Formal midpoints

A helper for Proposition prop:space (Paper/Curvature.lean): the terms that name the iterated midpoints.
-/

open Filter Topology Finset

namespace Cat

/-- Formal midpoints. -/
inductive Term (V : Type) : Type
  | of : V → Term V
  | mid : Term V → Term V → Term V

namespace Term

variable {V : Type}

/-- The depth of a term. -/
def depth : Term V → ℕ
  | of _ => 0
  | mid s t => max s.depth t.depth + 1

/-- The first letter of a term. -/
def base : Term V → V
  | of v => v
  | mid s _ => s.base

/-- Where the terms of depth at most `n+1` stand when a new point is added for every pair of terms of depth at most `n`. -/
def place (n : ℕ) (s : Term V) : Term V ⊕ (Term V × Term V) :=
  if s.depth ≤ n then Sum.inl s else
    match s with
    | of v => Sum.inl (of v)
    | Term.mid a b => Sum.inr (a, b)

end Term

end Cat
