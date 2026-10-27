/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.BigOperators.ModEq
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Rat.Star
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.Tactic
public import ParityChecksStatement

/-! # The choice of the checks as a computation: definitions

The clauses are 0, …, m − 1. A check is the list of its clauses. A state of the choice is (Ls, cur,
e): the complete checks, the part of the current check chosen so far, and the number e of
clauses already decided for it. The sums over marked sets are not computed here: they come from two
functions (`orcA`, `orcB`), which are parameters. The four terms of the truncated
potential are written over one common denominator, which does not depend on the decision, so that a
decision compares two integers. Lists, natural numbers and integers only, except for the
translation to the sets of `ParityChecksStatement.lean`. -/

@[expose] public section

namespace ClauseBound.ParityChecks

open Finset _root_.ParityChecks

/-- A check: the list of its clauses. -/
abbrev Chk : Type := List ℕ

/-- The checks as sets. -/
def lam (m : ℕ) (Ls : List Chk) : ℕ → Finset (Fin m) := fun j => univ.filter fun x => x.val ∈ Ls.getD j []

/-- The clauses not yet decided: e, …, m − 1. -/
def Dset (m e : ℕ) : Finset (Fin m) := univ.filter fun x => e ≤ x.val


section Sums
variable {X : Type} [Fintype X] {m : ℕ} (V : X → Finset (Fin m)) (nb r : ℕ)

end Sums

/-! ### The integers that are compared -/

/-- The representative of a modulo 2^β in [−2^{β−1}, 2^{β−1}). -/
def bal (β : ℕ) (a : ℤ) : ℤ := (a + 2 ^ (β - 1)) % 2 ^ β - 2 ^ (β - 1)

/-- The parameters of the choice: (m, nb, r, i₀, β). -/
structure Par where
  m : ℕ
  nb : ℕ
  r : ℕ
  i₀ : ℕ
  β : ℕ

namespace Par
variable (q : Par)

/-- The number of later checks. -/
def k (j : ℕ) : ℕ := q.r - 1 - j

/-- The common denominator of the four terms in a state with j complete checks. -/
def den (j : ℕ) : ℕ := 16 * 8 ^ q.k j * q.nb ^ q.i₀ * q.m * q.r * (q.nb + 1) ^ (q.m + q.r)

/-- A·nb^{i₀} + Σ_{i ≤ i₀} (−2)^i·nb^{i₀−i}·B_i. -/
def numP (A : ℤ) (B : ℕ → ℤ) : ℤ :=
  A * q.nb ^ q.i₀ + ((List.range (q.i₀ + 1)).map fun i => (-2 : ℤ) ^ i * q.nb ^ (q.i₀ - i) * B i).sum

/-- The number of checks among Ls and cur that contain the clause x. -/
def colOf (Ls : List Chk) (cur : Chk) (x : ℕ) : ℕ := (Ls.countP fun L => decide (x ∈ L)) + if x ∈ cur then 1 else 0

/-- I·nb + (number of undecided pairs). -/
def numI (Ls : List Chk) (cur : Chk) (e : ℕ) : ℕ :=
  ((Ls.map List.length).sum + cur.length) * q.nb + ((q.m - e) + q.k Ls.length * q.m)

/-- Σ_{j'} 2^{|Λ_j'|}·nb^{c}·(nb+1)^{m−c}, c the number of clauses decided for check j'. -/
def numR (Ls : List Chk) (cur : Chk) (e : ℕ) : ℕ :=
  (Ls.map fun L => 2 ^ L.length * q.nb ^ q.m).sum + 2 ^ cur.length * q.nb ^ e * (q.nb + 1) ^ (q.m - e) + q.k Ls.length * (q.nb + 1) ^ q.m

/-- Σ_x 2^{col(x)}·nb^{c}·(nb+1)^{r−c}, c the number of checks for which x is decided. -/
def numC (Ls : List Chk) (cur : Chk) (e : ℕ) : ℕ :=
  ((List.range q.m).map fun x =>
    2 ^ colOf Ls cur x * q.nb ^ (Ls.length + if x < e then 1 else 0) * (q.nb + 1) ^ (q.r - (Ls.length + if x < e then 1 else 0))).sum

/-- The numerator of the truncated potential over `den`. -/
def num (A : ℤ) (B : ℕ → ℤ) (Ls : List Chk) (cur : Chk) (e : ℕ) : ℤ :=
  5 ^ q.k Ls.length * q.numP A B * (8 * q.m * q.r * (q.nb + 1) ^ (q.m + q.r) : ℕ) +
    (q.numI Ls cur e * (2 * 8 ^ q.k Ls.length * q.nb ^ q.i₀ * (q.nb + 1) ^ (q.m + q.r)) +
      q.numR Ls cur e * (2 * 8 ^ q.k Ls.length * q.nb ^ q.i₀ * q.m * (q.nb + 1) ^ q.r) +
      q.numC Ls cur e * (2 * 8 ^ q.k Ls.length * q.nb ^ q.i₀ * q.r * (q.nb + 1) ^ q.m) : ℕ)

/-! ### The run -/

variable (orcA : List Chk → ℤ) (orcB : List Chk → Chk → ℕ → ℕ → ℤ)

/-- The numerator in the state (Ls, cur, e), with A and the B_i taken from the two functions and
reduced modulo 2^β. -/
def numO (Ls : List Chk) (cur : Chk) (e : ℕ) : ℤ :=
  q.num (bal q.β (orcA Ls)) (fun i => bal q.β (orcB Ls cur e i)) Ls cur e

/-- One decision: the clause e goes into the current check if that does not give the larger
numerator. -/
def decide1 (Ls : List Chk) (cur : Chk) (e : ℕ) : Chk :=
  if q.numO orcA orcB Ls (cur ++ [e]) (e + 1) ≤ q.numO orcA orcB Ls cur (e + 1) then cur ++ [e] else cur

/-- The first e decisions for one check. -/
def runTo (Ls : List Chk) (e : ℕ) : Chk := (List.range e).foldl (q.decide1 orcA orcB Ls) []

/-- The first j checks. -/
def runChecks (j : ℕ) : List Chk := (List.range j).foldl (fun Ls _ => Ls ++ [q.runTo orcA orcB Ls q.m]) []

/-- All checks. -/
def run : List Chk := q.runChecks orcA orcB q.r

end Par

/-- The bounds that hold in every state that is reached, and with one more pair in every state that
is tried. -/
structure Tent (q : Par) (Λ : ℕ → Finset (Fin q.m)) : Prop where
  inc : ((∑ j' ∈ range q.r, #(Λ j') : ℕ) : ℚ) < 8 * pr q.nb * q.m * q.r + 1
  row : ∀ j' < q.r, (2 : ℚ) ^ #(Λ j') < 2 * (8 * q.r * (1 + pr q.nb) ^ q.m)
  col : ∀ x : Fin q.m, (2 : ℚ) ^ #{j' ∈ range q.r | x ∈ Λ j'} < 2 * (8 * q.m * (1 + pr q.nb) ^ q.r)

/-- What the run needs of the parameters, for a set X of assignments. -/
structure Hyp (q : Par) (cardX : ℕ) (ε : ℚ) : Prop where
  nb_two : 2 ≤ q.nb
  r_pos : 1 ≤ q.r
  m_pos : 1 ≤ q.m
  β_pos : 2 ≤ q.β
  start : (5 / 8 : ℚ) ^ q.r * (cardX * q.m.choose (q.nb + 1) : ℕ) ≤ 1 / 8
  series : ∀ u ≤ q.m, |(1 - 2 * pr q.nb) ^ u - ∑ i ∈ range (q.i₀ + 1), (-2 * pr q.nb) ^ i * (u.choose i : ℚ)| ≤ ε
  drift : ε * (cardX * q.m.choose (q.nb + 1) : ℕ) * (q.m * q.r) < 1 / 4
  small : ∀ i ≤ q.i₀, cardX * q.m.choose (q.nb + 1) * q.m.choose i ≤ 2 ^ (q.β - 2)

end ClauseBound.ParityChecks
