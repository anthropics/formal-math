/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Rate.Defs

/-!
# Grid sums and sums of products of wide clauses as projections

A wide clause is a weight that applies when all literals of a list hold. A sum over bits of a product of wide
clauses is a grid sum, so it is a projection of every family that is complete for grid sums. Grid sums are
permanents if 2 ≠ 0.
-/

namespace Nc

open Finset MvPolynomial

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

section Wide

variable {α θ : Type*} [Fintype α] [DecidableEq α] [Fintype θ] [DecidableEq θ]

/-- The sum over the hidden bits `a` of the product over the clauses: a clause contributes its weight when all
its literals hold, and 1 otherwise. -/
def wideSum (lits : θ → List ((ι ⊕ α) × Bool)) (w : θ → F) (x : ι → Bool) : F :=
  ∑ a : α → Bool, ∏ i, if ∀ l ∈ lits i, Sum.elim x a l.1 = l.2 then w i else 1

/-- The extension with weights `X i` (bit 1) and `1 - c * X i` (bit 0). -/
noncomputable def mlExtC (c : F) (f : (ι → Bool) → F) : MvPolynomial ι F :=
  ∑ u : ι → Bool, C (f u) * ∏ i, if u i then X i else 1 - C c * X i

end Wide

section Proj

variable {F ι α θ : Type} [Field F] [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] [Fintype θ]
  [DecidableEq θ] {G : ∀ S, MvPolynomial (Fin S × Fin S) F} {κ : ℕ}

end Proj

end Nc
