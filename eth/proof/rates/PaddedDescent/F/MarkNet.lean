/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.MarkMath
public import PaddedDescent.F.Data
public import StepMachines.Prog.GridDefs

/-! # Marks and layers, part 2: the network of one profile

Every variable lives at one of g nodes. The clauses are given as a list `Ls` of formulas, the
layers; the layer of a clause is the index of its formula in `Ls` (the paper has no layers:
the network of Step 3 of Appendix D has two kinds of objects instead). The state of a node holds the
values of its variables and one bit, the mark, for every clause that touches the node.
A marked clause must have all its literals false. The nodes that a clause touches form a chain, and
neighbours in the chain compare their marks of the clause, so that only marks are shared
between nodes. A profile prescribes, for every layer, how many marked clauses each node owns and how
many of the marks that two nodes compare are set. Inside a profile the compared marks are
written in a short code (`enc`). The sum of the values of the networks of all admissible profiles is
`trunc`. This file has definitions only. -/

@[expose] public section

namespace PaddedDescent.F.Mark

open Groundwork Groundwork.Prog Groundwork.Prog.Count

/-! ### The network of one profile -/

/-- Variables per node. -/
def qv (g n : ℕ) : ℕ := (n + g - 1) / g

/-- All clauses with the index of their layer. -/
def cls (Ls : List Fml) : List (ℕ × Cl) := (List.range Ls.length).flatMap fun i => (Ls.getD i []).map fun C => (i, C)

def clAt (Ls : List Fml) (e : ℕ) : ℕ × Cl := (cls Ls).getD e (0, [])

/-- Clause e has a literal whose variable lives at node a. -/
def tchB (g n : ℕ) (Ls : List Fml) (a e : ℕ) : Bool := (clAt Ls e).2.any fun l => l.1 / qv g n == a

/-- The clauses that touch a, in order. -/
def tch (g n : ℕ) (Ls : List Fml) (a : ℕ) : List ℕ := (List.range (cls Ls).length).filter (tchB g n Ls a)

/-- a < b are neighbours in the chain of the nodes that e touches. -/
def linkB (g n : ℕ) (Ls : List Fml) (e a b : ℕ) : Bool :=
  decide (a < b) && tchB g n Ls a e && tchB g n Ls b e &&
    (List.range g).all fun c => !(decide (a < c) && decide (c < b) && tchB g n Ls c e)

/-- a is the least node that e touches. -/
def ownB (g n : ℕ) (Ls : List Fml) (e a : ℕ) : Bool :=
  tchB g n Ls a e && (List.range g).all fun c => !(decide (c < a) && tchB g n Ls c e)

/-- The clauses of layer i whose marks the nodes a and b compare, in order. -/
def tst (g n : ℕ) (Ls : List Fml) (a b i : ℕ) : List ℕ :=
  (List.range (cls Ls).length).filter fun e => (clAt Ls e).1 == i && linkB g n Ls e (min a b) (max a b)

/-- The mark that the state word z of node a gives to clause e. -/
def mark (g n : ℕ) (Ls : List Fml) (a : ℕ) (z : List Bool) (e : ℕ) : Bool := z.getD (qv g n + (tch g n Ls a).idxOf e) false

def str (g n : ℕ) (Ls : List Fml) (a b i : ℕ) (z : List Bool) : List Bool := (tst g n Ls a b i).map (mark g n Ls a z)

/-- The block code: blocks of b bits; a block with j ones is written 1^j 0 and then the j positions,
β bits each. -/
def enc (β b : ℕ) (x : List Bool) : List Bool :=
  (List.range ((x.length + b - 1) / b)).flatMap fun o =>
    ((List.range b).filter fun p => x.getD (o * b + p) false).map (fun _ => true) ++
      false :: ((List.range b).filter fun p => x.getD (o * b + p) false).flatMap (toWord β)

/-- The number that the profile y prescribes for the nodes a, b (a = b: owned marks) and the layer
i. -/
def mu (g : ℕ) (Ls : List Fml) (y a b i : ℕ) : ℕ := digit (cls Ls).length y ((min a b * g + max a b) * Ls.length + i)

def mcap (g n β b : ℕ) (Ls : List Fml) (y a a' : ℕ) : ℕ :=
  ((List.range Ls.length).map fun i => mu g Ls y a a' i * (1 + β) + ((tst g n Ls a a' i).length + b - 1) / b).sum

def mlab (g n β b : ℕ) (Ls : List Fml) (a a' : ℕ) (z : List Bool) : List Bool :=
  (List.range Ls.length).flatMap fun i => enc β b (str g n Ls a a' i z)

def mW (g n : ℕ) (Ls : List Fml) (y a : ℕ) (z : List Bool) : ℤ :=
  if ((List.range (qv g n)).all fun r => decide (a * qv g n + r < n) || !(z.getD r false)) &&
      ((tch g n Ls a).all fun e => !(mark g n Ls a z e) ||
        (clAt Ls e).2.all fun l => !(l.1 / qv g n == a) || (z.getD (l.1 % qv g n) false != l.2)) &&
      ((List.range Ls.length).all fun i =>
        ((tch g n Ls a).filter fun e => (clAt Ls e).1 == i && ownB g n Ls e a && mark g n Ls a z e).length == mu g Ls y a a i) &&
      ((List.range g).all fun a' => a' == a || (List.range Ls.length).all fun i => (str g n Ls a a' i z).count true == mu g Ls y a a' i)
  then (-1) ^ ((tch g n Ls a).filter fun e => decide (1 ≤ (clAt Ls e).1) && ownB g n Ls e a && mark g n Ls a z e).length
  else 0

/-- ((g, n, β, b in unary), (layers, profile)). -/
abbrev MCtx := (U × U × U × U) × (List Fml × ℕ)

def markF : FNet MCtx where
  n c a := qv c.1.1.length c.1.2.1.length + (tch c.1.1.length c.1.2.1.length c.2.1 a).length
  cap c a a' := mcap c.1.1.length c.1.2.1.length c.1.2.2.1.length c.1.2.2.2.length c.2.1 c.2.2 a a'
  W x := mW x.1.1.1.length x.1.1.2.1.length x.1.2.1 x.1.2.2 x.2.1 x.2.2
  f x := if mlab x.1.1.1.length x.1.1.2.1.length x.1.1.2.2.1.length x.1.1.2.2.2.length x.1.2.1 x.2.1.1 x.2.1.2 x.2.2.1 == x.2.2.2 then 1 else 0

/-- The network that markF presents. -/
def markN (g : ℕ) (c : MCtx) : Network (Fin g) (List Bool) (List Bool) where
  S a := words (markF.n c a.val)
  W a z := markF.W (c, (a.val, z))
  Θ a b := words (markF.cap c a.val b.val)
  f a b z θ := markF.f (c, ((a.val, b.val), (z, θ)))
  c a b := markF.cap c a.val b.val

/-- The profile y is admissible for the cap w, for clauses of at most k literals. -/
def adm (k g n w : ℕ) (Ls : List Fml) (y : ℕ) : Bool :=
  (List.range Ls.length).all fun i =>
    decide (((List.range g).map fun a => mu g Ls y a a i).sum ≤ w) &&
    decide (((List.range g).map fun a => ((List.range a).map fun a' => mu g Ls y a' a i).sum).sum ≤ (k - 1) * w) &&
    (List.range g).all fun a => (List.range g).all fun a' =>
      if a' < a then digit (cls Ls).length y ((a * g + a') * Ls.length + i) == 0
      else a' == a || decide (mu g Ls y a a' i ≤ (tst g n Ls a a' i).length)

/-! ### Sets of marked clauses -/

/-- The layers are well formed: clauses of 1 to k literals on variables below n. -/
def WfL (k n : ℕ) (Ls : List Fml) : Prop := ∀ L ∈ Ls, ∀ C ∈ L, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n

/-- The indices of the clauses that σ violates. -/
def vset (σ : ℕ → Bool) (Ls : List Fml) : Finset ℕ := (Finset.range (cls Ls).length).filter fun e => vio σ (clAt Ls e).2 = true

/-- The members of P in layer i. -/
def layP (Ls : List Fml) (P : Finset ℕ) (i : ℕ) : Finset ℕ := P.filter fun e => (clAt Ls e).1 = i

/-- The number of members of P in layer i that the node a owns. -/
def oc (g n : ℕ) (Ls : List Fml) (P : Finset ℕ) (a i : ℕ) : ℕ := (P.filter fun e => (clAt Ls e).1 = i ∧ ownB g n Ls e a = true).card

/-- The number of members of P among the clauses of layer i whose marks a and b compare. -/
def pw (g n : ℕ) (Ls : List Fml) (P : Finset ℕ) (a b i : ℕ) : ℕ := (P.filter fun e => e ∈ tst g n Ls a b i).card

/-- The sign of P: the first layer does not count. -/
def sgnP (Ls : List Fml) (P : Finset ℕ) : ℤ := (-1) ^ (P.filter fun e => 1 ≤ (clAt Ls e).1).card

/-- P has the profile y. -/
def Match (g n : ℕ) (Ls : List Fml) (y : ℕ) (P : Finset ℕ) : Prop :=
  ∀ i < Ls.length, ∀ a < g, oc g n Ls P a i = mu g Ls y a a i ∧ ∀ b < g, b ≠ a → pw g n Ls P a b i = mu g Ls y a b i

/-- The number of numbers y that are tried as profiles. -/
def nProf (g M R₁ : ℕ) : ℕ := (M + 1) ^ (g * g * R₁)

end PaddedDescent.F.Mark
