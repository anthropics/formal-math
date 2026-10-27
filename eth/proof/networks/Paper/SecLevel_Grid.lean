/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Paper.SecNetworks_DefFactor
public import Paper.SecCrossing_Crossing
public import Groundwork.Grid.Size
public import StepMachines.Math.SideNet
public import StepMachines.Prog.GridDefs

/-! # Section 5 of the paper: the g × g grid of the proof of Proposition 3 and its rectangles

The proof of Proposition 3 places the nodes of a (g², λ)-clique on a g × g grid. This file holds the
grid, the set ℛ of its rectangles
and their number (`card_rectangles`, `card_rectangles_le`), and the types of the settings of the
grid points and of the rows.

Here λ is written `lam`, a bit string of length λ has the type `Bits lam` (= `Fin lam → Bool`), and
rows and columns are numbered
by `Fin g` (0, …, g − 1).

The number of rectangles (`rectangles`, `card_rectangles`, `card_rectangles_le`) is used in the
proof of Theorem 2. -/

@[expose] public section

namespace Paper

open Finset Groundwork

variable {g lam : ℕ}

/-! ## The grid and its rectangles -/

/-- A rectangle q of the g × g grid, written ((a, a'), (j, j')): two rows and two columns. The
conditions a < a' and j < j' are
part of `rectangles`. -/
abbrev Rectangle (g : ℕ) : Type := Grid.Rect (Fin g) (Fin g)

/-- The set ℛ of rectangles of the g × g grid (proof of Proposition 3): all choices of two rows a <
a' and two columns j < j',
adjacent or not. -/
def rectangles (g : ℕ) : Finset (Rectangle g) := Grid.Ω (Fin g) (Fin g)

theorem mem_rectangles (q : Rectangle g) : q ∈ rectangles g ↔ q.1.1 < q.1.2 ∧ q.2.1 < q.2.2 := by
  simp [rectangles, Grid.Ω]

/-- The number of rectangles. The paper: «The set ℛ of rectangles has C(g,2)² ≤ g⁴/4 elements.» This
is the equality. Same as in the paper. -/
theorem card_rectangles (g : ℕ) : #(rectangles g) = g.choose 2 ^ 2 :=
  Grid.card_Ω (Fintype.card_fin g) (Fintype.card_fin g)

/-- The inequality of the same sentence: |ℛ| ≤ g⁴/4. Same as in the paper. -/
theorem card_rectangles_le (g : ℕ) : (#(rectangles g) : ℝ) ≤ (g : ℝ) ^ 4 / 4 := by
  have h : 4 * #(rectangles g) ≤ g ^ 4 := Grid.four_mul_card_Ω_le (Fintype.card_fin g) (Fintype.card_fin g)
  have h' : 4 * (#(rectangles g) : ℝ) ≤ (g : ℝ) ^ 4 := by exact_mod_cast h
  linarith

/-- A choice of settings of all grid points: z w w' is the string z_w(w'), the copy that the grid
point w keeps of the string on
the edge {w, w'}. (The entry z w w is not used by the paper.) -/
abbrev Settings (g lam : ℕ) : Type := Grid.Half (Fin g) (Fin g) (Bits lam)

/-! ## The setting of a row -/

/-- A setting of a row (or column): the tuple of the settings of its g grid points. z j w' is the
string that the j-th grid point
of the row keeps for the edge to the grid point w'. -/
abbrev RowSetting (g lam : ℕ) : Type := Grid.RowSt (Fin g) (Fin g) (Bits lam)


section OnPath

open Groundwork.Grid Groundwork.Prog

end OnPath

end Paper
