/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Boson.Basic
public import ClauseBound.Boson.Scalars
public import ClauseBound.Boson.Defs

/-! # The parts of a monomial of bounded weight

A lemma on the monomials of the polynomial ring in t₁, t₂, … on which the operators a[r] of Appendix
B act: the parts of a monomial of weight at most M lie between 1 and M. -/

public section

namespace ClauseBound.Boson.WickPlus

open Finset

/-- The parts of a monomial of weight at most M lie between 1 and M. -/
theorem toFinset_subset_Icc {τ : Multiset ℕ} (h0 : 0 ∉ τ) {M : ℕ} (hM : τ.sum ≤ M) : τ.toFinset ⊆ Icc 1 M := by
  intro x hx
  have hx' := Multiset.mem_toFinset.1 hx
  have h1 : x ≠ 0 := fun h => h0 (h ▸ hx')
  have h2 : x ≤ τ.sum := Multiset.le_sum_of_mem hx'
  exact mem_Icc.2 ⟨by omega, by omega⟩

end ClauseBound.Boson.WickPlus

namespace ClauseBound.Boson

open Finset WickPlus

end ClauseBound.Boson
