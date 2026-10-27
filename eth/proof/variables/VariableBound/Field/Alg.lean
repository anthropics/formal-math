/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Field.Defs
public import Mathlib.RingTheory.AdjoinRoot

/-! # What a word of bits stands for

`decR r w` is b_0 + b_1·r + … + b_(n−1)·r^(n−1) for the word w = (b_0, …, b_(n−1)) and an element r
of a commutative ring. With r = X it is a polynomial over the field with two elements (`polyW`);
`modP g` is the polynomial X^s + g, where s is the length of g; `FW g` is the ring of residues
modulo it, and `decW g w` the residue that the word w stands for. -/

@[expose] public section

namespace VariableBound.Fld

open Polynomial

/-- A bit as an element of a ring. -/
def bitR (R : Type) [CommRing R] (b : Bool) : R := if b then 1 else 0

/-- b_0 + b_1·r + … + b_(n−1)·r^(n−1), by Horner's rule. -/
def decR {R : Type} [CommRing R] (r : R) : List Bool → R
  | [] => 0
  | b :: w => bitR R b + r * decR r w

/-- The polynomial over the field with two elements whose coefficients are the bits of w. -/
noncomputable def polyW (w : List Bool) : (ZMod 2)[X] := decR X w

/-- The polynomial X^s + g, where s is the length of g. -/
noncomputable def modP (g : List Bool) : (ZMod 2)[X] := X ^ g.length + polyW g

/-- The ring of residues of polynomials over the field with two elements modulo X^s + g. -/
abbrev FW (g : List Bool) : Type := AdjoinRoot (modP g)

/-- The residue that the word w stands for. -/
noncomputable def decW (g w : List Bool) : FW g := decR (AdjoinRoot.root (modP g)) w

end VariableBound.Fld
