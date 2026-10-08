/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Contracts

/-!
# 3SUM from Convolution-3SUM: the loop over the splittings.  Specifications

round handles one splitting `(β, β', v)`: three selections and one call of the recursive procedure.
row runs through `β'` and `v` for a fixed `β`, and grid runs through `β`.  This file fixes their
specifications.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe Finset

/-- What the routines that run through the splittings are given, besides what the routines below
the recursion tree share: the number `Λ` of binary digits, the number `nd` of the distinct values
`D`, their address `val`, the addresses `bt` of the table of digits, `A` of the cells for the three
sets and `cx` of the block of parameters. -/
structure FrontArgs : Type extends Env where
  (Λ nd val bt A cx : ℕ)
  D : List ℤ

/-- The values of the arguments of grid; row and round get them after their own. -/
@[simp] abbrev FrontArgs.vals (a : FrontArgs) (f : ℕ) : List ℤ :=
  [a.nd, a.val, a.bt, a.Λ, a.A, a.n, f, a.cx, a.fr]

/-- What the memory holds while the splittings are run through: the `nd` distinct values `D` at
`val`, the table of their binary digits at `bt`, the block of parameters at `cx`, the primes, the
count table, and `3n` cells from `A` for the three sets of a splitting.  Everything lies below the
free pointer, and the cells from `A` and the count table meet nothing else. -/
structure FrontMem (μ : ℕ → ℤ) (a : FrontArgs) : Prop where
  lenD : a.D.length = a.nd
  nd_le : a.nd ≤ a.n
  nodup : a.D.Nodup
  bdd : Bdd a.V a.D.toFinset
  segVal : Seg μ a.val a.D
  segBt : Seg μ a.bt (bitTable a.V a.Λ a.D)
  ctx : CtxAt μ a.cx a.V a.m a.Λ a.np a.pr a.cnt
  primes : PrimesAt μ a.pr a.np a.m
  zero : ZeroAt μ a.cnt (a.m * a.m)
  belowVal : a.val + a.nd ≤ a.fr
  belowBt : a.bt + a.nd * a.Λ ≤ a.fr
  belowCx : a.cx + 6 ≤ a.fr
  belowPr : a.pr + a.np ≤ a.fr
  belowCnt : a.cnt + a.m * a.m ≤ a.fr
  belowA : a.A + 3 * a.n ≤ a.fr
  apartVal : Apart a.A (3 * a.n) a.val a.nd
  apartBt : Apart a.A (3 * a.n) a.bt (a.nd * a.Λ)
  apartCx : Apart a.A (3 * a.n) a.cx 6
  apartPr : Apart a.A (3 * a.n) a.pr a.np
  apartCnt : Apart a.A (3 * a.n) a.cnt (a.m * a.m)
  cntVal : Apart a.val a.nd a.cnt (a.m * a.m)
  cntCx : Apart a.cx 6 a.cnt (a.m * a.m)
  cntPr : Apart a.pr a.np a.cnt (a.m * a.m)

/-- Some node of the tree of the splitting `(β, β', v)` of the set `S` gives a yes-instance. -/
def SplitYes (m Λ f V : ℕ) (S : Finset ℤ) (β β' : ℕ) (v : Bool) : Prop :=
  TreeYes m Λ f V (splitA V β v S) (splitB V β β' v false S) (splitB V β β' v true S)

/-- Some node of the tree of the splitting `(β, β', v)` of the distinct values gives a
yes-instance. -/
abbrev FrontArgs.Yes (a : FrontArgs) (f β β' : ℕ) (v : Bool) : Prop :=
  SplitYes a.m a.Λ f a.V a.D.toFinset β β' v

/-- The time of the recursive procedure for one three-set input, with `f` levels. -/
def tTree (T : ℕ → ℕ → ℕ) (n V m np f : ℕ) : ℕ := tNodes T n V m np (2 * 3 ^ f)

/-- The time of round. -/
def tRound (T : ℕ → ℕ → ℕ) (n V m np f : ℕ) : ℕ := 3 * tPick n + tTree T n V m np f + 120
/-- The time of row. -/
def tRow (T : ℕ → ℕ → ℕ) (n V m np f Λ : ℕ) : ℕ := Λ * (2 * tRound T n V m np f + 80) + 40
/-- The time of grid. -/
def tGrid (T : ℕ → ℕ → ℕ) (n V m np f Λ : ℕ) : ℕ := Λ * (tRow T n V m np f Λ + 40) + 40

/-- The need of round, row (`extra = 1`) and grid (`extra = 2`): that of the recursive procedure,
and the levels of calls above it. -/
def gridNeed (r : ℕ → ℕ → Need) (n V m f extra : ℕ) : Need :=
  ⟨(nodesNeed r n V m f).word + 4 * V + 16, (nodesNeed r n V m f).cells,
    (nodesNeed r n V m f).depth + 1 + extra⟩

/-- What round (`extra = 0`), row (`extra = 1`) and grid (`extra = 2`) assume besides the memory. -/
structure GridPre (lim : Limits) (r : ℕ → ℕ → Need) (a : FrontArgs) (f extra d : ℕ) : Prop where
  V_pos : 1 ≤ a.V
  m_pos : 1 ≤ a.m
  lam : a.Λ = Lam a.V
  primes : (Nat.primesLE a.m).Nonempty
  ok : (gridNeed r a.n a.V a.m f extra).Ok lim a.fr d

/-- round(β, β', b, nd, val, bt, Λ, A, n, f, cx, fr), with `b` = 1 for `v = true` and 0 for
`v = false`, returns 1 if the splitting gives a yes-instance, and 0 if not.  The three sets are
written to `A`, `A + n`, `A + 2n`. -/
def RoundSpec (lim : Limits) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) : Prop :=
  ∀ (a : FrontArgs) (f β β' : ℕ) (v : Bool) (μ : ℕ → ℤ), FrontMem μ a → β < a.Λ → β' < a.Λ →
    ∀ d, GridPre lim r a f 0 d →
    Meets lim P p d ((β : ℤ) :: β' :: (if v then 1 else 0) :: a.vals f) μ
      (tRound T a.n a.V a.m a.np f) fun res μ' =>
      res = flag (a.Yes f β β' v) ∧ KeptBut μ μ' a.fr a.A (3 * a.n)

/-- row(β, nd, val, bt, Λ, A, n, f, cx, fr) returns a number between 0 and `2Λ` that is positive
exactly if some splitting `(β, β', v)` gives a yes-instance. -/
def RowSpec (lim : Limits) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) : Prop :=
  ∀ (a : FrontArgs) (f β : ℕ) (μ : ℕ → ℤ), FrontMem μ a → β < a.Λ →
    ∀ d, GridPre lim r a f 1 d →
    Meets lim P p d ((β : ℤ) :: a.vals f) μ (tRow T a.n a.V a.m a.np f a.Λ) fun res μ' =>
      0 ≤ res ∧ res ≤ 2 * (a.Λ : ℤ) ∧ (0 < res ↔ ∃ β' < a.Λ, ∃ v, a.Yes f β β' v) ∧
        KeptBut μ μ' a.fr a.A (3 * a.n)

/-- grid(nd, val, bt, Λ, A, n, f, cx, fr) returns 1 if some splitting gives a yes-instance, and 0 if
not. -/
def GridSpec (lim : Limits) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) : Prop :=
  ∀ (a : FrontArgs) (f : ℕ) (μ : ℕ → ℤ), FrontMem μ a → ∀ d, GridPre lim r a f 2 d →
    Meets lim P p d (a.vals f) μ (tGrid T a.n a.V a.m a.np f a.Λ) fun res μ' =>
      res = flag (∃ β < a.Λ, ∃ β' < a.Λ, ∃ v, a.Yes f β β' v) ∧
        KeptBut μ μ' a.fr a.A (3 * a.n)

end Light.Sec3.ChanHe
