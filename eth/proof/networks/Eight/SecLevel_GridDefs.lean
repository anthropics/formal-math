/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.SecCrossing_PolyDefs
public import Paper.SecLevel_Grid
public import ClauseBound.Alg.GridNet
public import Mathlib.Data.Sym.Sym2

/-! # Section 5 «One level of the recursion», the mathematics of one level: definitions only

The objects of the proof of Proposition 3 up to display (36), for the functions A_0, …, A_t, t =
⌈λ/3⌉, of Lemma 2 (`Eight.A`): the functions ι : ℛ → {0, …, t}; the term Z_ι of display (34); the
two factorizations of
Lemma 2(b) in the form in which a network of merged rows takes them; the row network and the column
network of ι; a function ι written as a number. Nothing is proved here. The statements are in
proof/networks/Eight/SecLevel_Grid.lean and SecLevel_GridWords.lean.
The grid and its rectangles (`Paper.Rectangle`, `Paper.rectangles`, `Paper.Settings`,
`Paper.RowSetting`) do not depend on the pieces and are taken from
proof/networks/Paper/SecLevel_Grid.lean; the sum over a grid and the network of merged rows, for any
functions at the
rectangles and any factorizations of them, are in proof/networks/Groundwork/ (`Groundwork.Grid.ZG`,
`Groundwork.Grid.rowNet`). λ is written `lam`; a string of λ bits has the type `Bits lam` (=
`Fin lam → Bool`); rows and columns are numbered by `Fin g`. -/

@[expose] public section

namespace Eight

open Finset Groundwork
open Paper (Rectangle rectangles Settings RowSetting)

variable {g lam : ℕ}

/-! ## The expansion (34) -/

/-- The functions ι : ℛ → {0, …, t} of display (34), t = ⌈λ/3⌉. In Lean ι is defined on all ((a,
a'), (j, j')) and is 0 off ℛ. -/
def patterns (g lam : ℕ) : Finset (Rectangle g → ℕ) := Grid.Pat (Fin g) (Fin g) (tOf lam)

/-- The term Z_ι of display (34), for tables W on the grid:
Z_ι = ∑_z ∏_w W_w(z_w) · ∏_{straight edges {w,w'}} [z_w(w') = z_{w'}(w)] · ∏_{q ∈ ℛ} A_{ι(q)}(x_q,
y_q, u_q, v_q). -/
noncomputable def Zι (W : Inst (Fin g × Fin g) (Bits lam)) (ι : Rectangle g → ℕ) : ℤ :=
  Grid.ZG W fun q => A lam (ι q)

/-! ## The two networks of a term Z_ι -/

/-- The first factorization of Lemma 2(b): A_i as a function of (x,y) and (u,v). The index θ is a
word of c_i^row bits, and the two functions are `fTop` and `fBot` of the proof of Lemma 2(b),
row-wise. -/
def rowCut (lam i : ℕ) : Grid.Cut (Bits lam) (List Bool) where
  lab := words (crow lam i)
  top x y θ := fTop (false, i, List.ofFn x, List.ofFn y, θ)
  bot u v θ := fBot (false, i, List.ofFn u, List.ofFn v, θ)
  cap := crow lam i

/-- The second factorization of Lemma 2(b): A_i as a function of (x,u) and (y,v). The index θ is a
word of c_i^col bits, and the two functions are `fTop` and `fBot`, column-wise. -/
def colCut (lam i : ℕ) : Grid.Cut (Bits lam) (List Bool) where
  lab := words (ccol lam i)
  top x u θ := fTop (true, i, List.ofFn x, List.ofFn u, θ)
  bot y v θ := fBot (true, i, List.ofFn y, List.ofFn v, θ)
  cap := ccol lam i

/-- The index θ of the factorization of Ψ_{a,a'}: one string for each of the g straight edges
between the two rows, and one word for each rectangle on the two rows. -/
abbrev RowIndex (g lam : ℕ) : Type := Grid.RowLab (Fin g) (Bits lam) (List Bool)

/-- **The row network of ι** (proof of Proposition 3). Its nodes are the g rows; a setting of row a
is the tuple of the settings of its g grid points.
Different from the paper: a setting of a row has g · g² strings (one of them, for each grid point,
is the dummy of `eqExpansion`), that is g³λ bits, where the paper has g(g² − 1)λ ≤ g³λ. -/
noncomputable def rowNetwork (W : Inst (Fin g × Fin g) (Bits lam)) (ι : Rectangle g → ℕ) :
    Network (Fin g) (RowSetting g lam) (RowIndex g lam) :=
  Grid.rowNet W (fun q => rowCut lam (ι q)) [] lam

/-- **The column network of ι**: «defined in the same way with rows and columns exchanged». In Lean:
the row network of the transposed grid, with the second factorization of Lemma 2(b). -/
noncomputable def colNetwork (W : Inst (Fin g × Fin g) (Bits lam)) (ι : Rectangle g → ℕ) :
    Network (Fin g) (RowSetting g lam) (RowIndex g lam) :=
  Grid.rowNet (Grid.trInst W) (fun q => colCut lam (ι (q.2, q.1))) [] lam

end Eight

namespace Eight.Level

open Groundwork Groundwork.Prog ClauseBound.Alg.GridNet
open Paper (Rectangle)

/-! ## A function ι written as a number -/

/-- The function ι written by the number y: ι(q) is the digit of y in base t + 1 at the number of
the rectangle q. (Defined by the same formula off ℛ.) -/
def digOf (g lam y : ℕ) : Rectangle g → ℕ := fun q => digit (tOf lam) y (ixG g g q)

/-- The same function, made 0 off ℛ, as the functions of display (34) are in Lean. -/
def patOf (g lam y : ℕ) : Rectangle g → ℕ := patG g g (tOf lam) y

end Eight.Level
