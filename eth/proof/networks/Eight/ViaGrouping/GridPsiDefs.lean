/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.ViaGrouping.Defs
public import Eight.SecLevel_GridDefs

/-! # Ψ_{a,a'} in the two networks of Proposition 3, as a program (definitions only)

Definition 2(iii) asks for a procedure that computes the values of Ψ_{a,b}. The row network and the
column network of ι, as Algorithm 1 runs them (`Eight.Level.netOfι`, given by the procedures
`Eight.Level.levelNet`), have procedures for W_a and f_{a,b} only.
This file has a program for Ψ, `gridPsi`. It follows the proof of Proposition 3, paragraph «Two
networks for each ι»: «Ψ_{a,a'} is the product of the factors of the g straight edges between rows a
and a' and of A_{ι(q)}(x_q, y_q, u_q, v_q) over the g(g−1)/2 rectangles q with
these two rows», and the same with rows and columns exchanged. A_i is computed by the program of the
proof of Lemma 2(a) (`Eight.aMul`); ι(q) is the digit of the number y, in base t + 1, at the number
of the rectangle q.
A setting of a row (of a column) is one word of g·g²·λ bits (the paper: g(g² − 1)λ; the λ bits more
per grid point are the dummy string of proof/networks/Eight/SecLevel_Grid.lean);
`ClauseBound.Alg.heG g g λ z i u` is the string which the grid point number i of the row keeps for
the edge to the grid point at the position u, and `ClauseBound.Alg.nodeG g tr b i'` is the position
of the grid point
number i' of the row b (proof/rates/ClauseBound/Alg/Data.lean). tr = false: rows; tr = true:
columns.
The statements `St… : Prop` at the end say that this program computes Ψ of these networks and that
it is polynomial-time. This file has no proofs. -/

@[expose] public section

namespace Eight.ViaGrouping

open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped Eight.SecNetworks Eight.Level

/-- The factor of one rectangle: A_{ι(q)}(x_q, y_q, u_q, v_q) for the rectangle q on the rows a < b
and the columns i < i' (tr = true: on the columns a < b and the rows i < i'). z is the setting of a
and z' that of b. Row-wise x_q, y_q are read from z and
u_q, v_q from z'; column-wise x_q, u_q are read from z and y_q, v_q from z'. -/
def rectPsi (g : ℕ) (tr : Bool) (lam y a b : ℕ) (z z' : List Bool) (i i' : ℕ) : ℤ :=
  aMul (digit (tOf lam) y (rectIxG g tr (tri a b) (tri i i')),
    bif tr then (heG g g lam z i (nodeG g tr b i'), heG g g lam z' i (nodeG g tr a i'), heG g g lam z i' (nodeG g tr b i), heG g g lam z' i' (nodeG g tr a i))
    else (heG g g lam z i (nodeG g tr b i'), heG g g lam z i' (nodeG g tr b i), heG g g lam z' i (nodeG g tr a i'), heG g g lam z' i' (nodeG g tr a i)))

/-- Ψ_{a,b}(z, z') for a < b: 0 unless the two copies of the string agree on each of the g straight
edges between a and b; else the product of the factors of the rectangles. The product runs over all
j = i·g + i' < g², with the factor 1 unless i < i'. -/
def psiLt (g : ℕ) (tr : Bool) (lam y a b : ℕ) (z z' : List Bool) : ℤ :=
  bif (List.range g).all fun i => heG g g lam z i (nodeG g tr b i) == heG g g lam z' i (nodeG g tr a i) then
    prodL (g * g) fun j => if j / g < j % g then rectPsi g tr lam y a b z z' (j / g) (j % g) else 1
  else 0

/-- **Ψ_{a,a'}(z, z')** in the row network (tr = false) or the column network (tr = true) of the
function ι written by y, as a function of the query ((a, a'), (z, z')). For a > a' it is
Ψ_{a',a}(z', z). -/
def gridPsi (g : ℕ) (tr : Bool) (lam y : ℕ) (q : PsiQ) : ℤ :=
  if q.1.1 < q.1.2 then psiLt g tr lam y q.1.1 q.1.2 q.2.1 q.2.2 else psiLt g tr lam y q.1.2 q.1.1 q.2.2 q.2.1

/-! ## Interface statements -/

/-- The program computes Ψ of the network that Algorithm 1 runs, at all settings. -/
def StGridPsi : Prop := ∀ (g : ℕ) (tr : Bool) (lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)), 1 ≤ lam → ∀ a b : Fin (nParts g g tr), a ≠ b →
  ∀ z ∈ (netOfι g tr lam y Rm).S a, ∀ z' ∈ (netOfι g tr lam y Rm).S b, gridPsi g tr lam y ((a.val, b.val), (z, z')) = (netOfι g tr lam y Rm).Ψ a b z z'

/-- The program is polynomial-time, for λ in unary (g and the direction are fixed). -/
def StGridPsiPoly : Prop := ∀ (g : ℕ) (tr : Bool) (C : Type) [Enc C] (lam : C → ℕ), Unary lam → PolyT fun x : (C × ℕ) × PsiQ => gridPsi g tr (lam x.1.1) x.1.2 x.2

end Eight.ViaGrouping
