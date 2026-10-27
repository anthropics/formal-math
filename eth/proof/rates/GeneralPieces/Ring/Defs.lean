/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import AppHalfPiecesStatement
public import ClauseBound.Boson.Defs2

/-! # The ring of Appendix B and the matrices of `ClauseBound.Boson.op`: the interface between them

The proof of the bound in m in `ClauseBound.Boson.Defs2` has no ring: an operator is its integer
matrix in the basis of the monomials, indexed by multisets of natural numbers without 0. `StBridge`
says that these
are the matrices of the operators a[r] that `AppHalfPiecesStatement.lean` defines on ℚ[t₁, t₂, …] by
display (47). Nothing is proved here. -/

@[expose] public section

namespace GeneralPieces

open AppHalfPieces

/-- A partition as a multiset of natural numbers. -/
def toN (μ : Ptn) : Multiset ℕ := μ.map fun k : ℕ+ => (k : ℕ)

/-- The parts of a monomial as natural numbers. -/
def toL (a : List ℕ+) : List ℕ := a.map fun k : ℕ+ => (k : ℕ)

/-- The coefficient of t^π in a[r]·t^σ, a the monomial with the parts listed, is the entry (π, σ) of
the matrix `ClauseBound.Boson.op`. -/
def StBridge : Prop := ∀ (a : List ℕ+) (r : ℤ) (π σ : Ptn), coef π (opMon a r (tpow σ)) = (ClauseBound.Boson.op (toL a) r (toN π) (toN σ) : ℚ)

end GeneralPieces
