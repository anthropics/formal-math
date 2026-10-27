/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.Top

/-! # Renaming the variables that occur: the program

The n variables that occur are renamed to x₁, …, xₙ, the paper's convention. Here the new names are
0, …, n − 1. This file has the program that does it, as a function from bit strings to bit strings.
Definitions only.
The input is `SatM.enc k φ` for a formula φ over x₀ … x_(N−1). It is decoded (`kOf`, `fmlOf` of
proof/rates/ClauseBound/Alg/Top.lean) to k in unary and the list of clauses with natural numbers as
variables.
`occL` lists the variables that occur, each once, in the order of their last occurrence; `renF`
replaces every variable by its position in that list; `encN` writes the result as a bit string
again, by the formula
of `SatM.enc`. The number N is not used. -/

@[expose] public section

namespace VariableBound.Rename

open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg

/-- The variables that occur in ψ, each once, in the order of their last occurrence. -/
def occL (ψ : Fml) : List ℕ := (ψ.flatMap fun C => C.map fun l => l.1).dedup

/-- ψ with every variable replaced by its position in the list L. -/
def renL (L : List ℕ) (ψ : Fml) : Fml := ψ.map fun C => C.map fun l => (L.idxOf l.1, l.2)

/-- The renamed formula: the number of variables that occur, in unary, and ψ with every variable
replaced by its position in `occL ψ`. -/
def renF (ψ : Fml) : U × Fml := ((occL ψ).map fun _ => (), renL (occL ψ) ψ)

/-- A slot of a clause as a number, as `Sat3.slot`: 0 = no literal, 2i+1 = ¬xᵢ, 2i+2 = xᵢ. -/
def slotN (o : Option (ℕ × Bool)) : ℕ := o.elim 0 fun l => 2 * l.1 + 1 + l.2.toNat

/-- The code of (k, n, ψ), with k and n in unary, by the formula of `SatM.enc`: 1ᵏ 0, then 1ⁿ 0,
then k slots per clause, ⌊log₂ (2n)⌋ + 1 bits per slot, low bit first. -/
def encN (ku : U) (d : U × Fml) : List Bool :=
  ku.map (fun _ => true) ++ false :: (d.1.map (fun _ => true) ++ false :: d.2.flatMap fun C => (List.range ku.length).flatMap fun j =>
    (List.range (Nat.log2 (2 * d.1.length) + 1)).map (slotN C[j]?).testBit)

/-- The front end: from the code of (k, φ) to the code of (k, φ with the variables that occur
renamed to 0, …, n − 1). -/
def renc (x : List Bool) : List Bool := encN (kOf x) (renF (fmlOf x).2)

end VariableBound.Rename
