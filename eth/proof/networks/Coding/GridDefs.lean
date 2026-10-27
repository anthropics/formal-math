/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Coding.Defs
public import Eight.ViaGrouping.LevelDefs

/-! # The row and column networks: settings of g(g² − 1)λ bits, and Lean's g³λ bits as these with padding (definitions and statements only)

Proof of Proposition 3: a setting of row a is the tuple (z_{(a,j)})_{j ∈ [g]} of the settings of its
g grid points; S_a is the set of these tuples, encoded by concatenation in g(g² − 1)λ ≤ P bits,
where P = g³λ. A setting of a grid point w has one string of λ bits for each of the g² − 1 OTHER
grid points.
In the networks on which the machines run (`Eight.ViaGrouping.levelNetP`) a setting of a grid point
has a string of λ bits for EVERY grid point, also for w itself; so a setting of a row has g³λ bits,
and W_a is 0 unless the string at each grid point's own position is 0^λ (`Groundwork.Grid.onGrid`).
`padRow` puts these strings in. This file is about the ENCODING of the settings only. `readThrough`
is Lean's network with its functions W_a, Ψ_{a,a'}, f_{a,a'} read at padded settings; its settings
are ALL strings of g(g² − 1)λ bits. `StGridPadding` says that Lean's network is this one with
padding, in the sense of `Coding.PaddingOf`; what has content in it is that padding is
one-to-one into Lean's settings and that W_a is 0 at every setting of Lean's network that is not a
padded one (the other fields hold by the definition of `readThrough`). So nothing is lost or added
by the strings at the grid points' own positions. The printed statements on W_a and Ψ_{a,a'} (W_a as
the product of the g table entries of row a and of the factors of the straight edges inside row a,
…) are not stated here;
this development has them for settings as functions (`Groundwork.Grid.rowW`, `rowNet`;
proof/networks/Eight/SecLevel_Grid.lean).
This file has no proofs. -/

@[expose] public section

namespace Coding

open Finset Groundwork Groundwork.Prog ClauseBound.Alg Eight.SecNetworks Eight.ViaGrouping

/-- The network N read through a padding: its settings are all strings of len₀ a bits, and every
function is that of N at the padded settings. -/
def readThrough {g : ℕ} (N : Net g) (len₀ : Fin g → ℕ) (pad : Fin g → List Bool → List Bool) : Net g where
  len := len₀
  S a := words (len₀ a)
  W a z := N.W a (pad a z)
  Ψ a b z z' := N.Ψ a b (pad a z) (pad b z')
  c := N.c
  f a b z θ := N.f a b (pad a z) θ

/-- The padding of a setting z of the row (tr = false) or column (tr = true) number a. z is the
concatenation, over the g grid points x of the row, of the g² − 1 strings of λ bits for the other
grid points, in the order of their positions; the result has, for each x, g² strings: 0^λ at the
position of x itself (`nodeG g tr a x`), and the strings of z at the others. -/
def padRow (g : ℕ) (tr : Bool) (lam a : ℕ) (z : List Bool) : List Bool :=
  (List.range g).flatMap fun x => (List.range (g * g)).flatMap fun u =>
    if u = nodeG g tr a x then List.replicate lam false else block lam (if u < nodeG g tr a x then u else u - 1) (block ((g * g - 1) * lam) x z)

/-- **The strings at the grid points' own positions are padding**: Lean's row or column network is
the same network read at settings of g(g² − 1)λ bits, with padding. -/
def StGridPadding : Prop := ∀ (g : ℕ) (tr : Bool) (lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)),
  PaddingOf (readThrough (levelNetP g tr lam y Rm) (fun _ => g * (g ^ 2 - 1) * lam) fun a => padRow g tr lam a.val) (levelNetP g tr lam y Rm) fun a => padRow g tr lam a.val

/-- «g(g² − 1)λ ≤ P». -/
def StGridLength : Prop := ∀ g lam : ℕ, g * (g ^ 2 - 1) * lam ≤ g ^ 3 * lam

end Coding
