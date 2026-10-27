/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.GridProcedures
public import ExplicitCost.GroupingDefs
public import Tower.Defs

/-! # The solver, and the one machine for all levels

Definitions only; nothing is stated or proved here.

**The text** (Theorem A (b)): «One deterministic algorithm, given ℓ ≥ 0, λ, B ≥ 1 and query access
to tables with |W_w| < 2^B, outputs the value of the (K_ℓ, λ)-clique within
2^{e_ℓK_ℓ²λ}(K_ℓ(λ+B))^{C₀K_ℓ²} operations.» Its proof: «For ℓ = 0, brute force …» «For the step
from ℓ to ℓ + 1 … d^{|ℛ|}Z = Σ_ι Z_ι over the |𝓘|^{|ℛ|} … functions
ι : ℛ → 𝓘, and each Z_ι is the value of the row network and of the column network.» «Case (ii) of
Lemma 8 applies to the network with the smaller total.» «The set 𝓘 and the numbers d, c^row_i,
c^col_i are computed once.» «… finding the numbers c_{a,a'} and the totals of both networks for one
ι; adding one Z_ι; computing d^{|ℛ|} and dividing by it.»

**What is here.** `solver c x₀`: a machine whose input is the context of an instance and which may (1)
call the solver on another context, (2) query the tables of its instance, (3) query the pieces. At ℓ =
0 it is `Printed.bruteMachine (2^x₀)`. At ℓ = ℓ' + 1 it runs, one after the other
(`QueryMachine.bind`; each stage sees the results of all earlier ones):
1. `numbersM x₀`: 2^{3ℓ'+x₀} and K = K_ℓ' in unary (2ℓ' steps); g = g_ℓ' is their product;
2. one query for 𝓘, one for d, one for each c^row_i, one for each c^col_i: 2|𝓘| + 2 queries to the
   pieces;
3. the loop over the numbers y < |𝓘|^{|ℛ|} of the patterns ι. For one y: the direction of the
   network with the smaller total and the input of Definition 2(iii) for it are plain functions of
   what has been computed; `groupingCall` (module `ExplicitCost.GroupingDefs`: the procedure of
   Lemma 8 up to its call) finds the first grouping x, for ζ = 1/2^{ℓ'+5}, and makes ONE call, which
   is passed on as a call of the context (ℓ', L, B') with the parent (K, g, λ, B, the lists, the
   direction, y, x); the result is added;
4. one step: the division by d^{|ℛ|}.
`recursion c x₀` is the tower of `solver c x₀` and `procedure c` (GridProcedures.lean).

«The algorithm uses ℓ, the pieces, the totals U^row, U^col and the constant c (through x₀ and B₁),
but neither ρ nor e_ℓ»: the definitions have the parameters c and x₀ and no ρ. -/

@[expose] public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-- The queries of the solver: a call, a query to the tables of its instance, a query to the pieces. -/
abbrev SolQuery : Type := Ctx ⊕ UpQuery

/-! ### What has been computed before the loop -/

/-- (ℓ, λ, B), with (2^{3ℓ'+x₀}, K) in unary. -/
abbrev Stage₁ : Type := Head × (List Unit × List Unit)
/-- … with the list of 𝓘. -/
abbrev Stage₂ : Type := Stage₁ × List ℤ
/-- … with d. -/
abbrev Stage₃ : Type := Stage₂ × ℤ
/-- … with the numbers c^row_i. -/
abbrev Stage₄ : Type := Stage₃ × List ℕ
/-- … with the numbers c^col_i: all that the loop over the patterns reads. -/
abbrev Ready : Type := Stage₄ × List ℕ

/-- The parts of it: (ℓ, λ, B). -/
def rHead (s : Ready) : Head := s.1.1.1.1.1
/-- K = K_ℓ'. -/
def rK (s : Ready) : ℕ := s.1.1.1.1.2.2.length
/-- g = g_ℓ' = 2^{3ℓ'+x₀}·K. -/
def rG (s : Ready) : ℕ := s.1.1.1.1.2.1.length * s.1.1.1.1.2.2.length
/-- d. -/
def rD (s : Ready) : ℤ := s.1.1.2
/-- The list of 𝓘 and the numbers c^row_i, c^col_i. -/
def rLists (s : Ready) : Lists := (s.1.1.1.2, s.1.2, s.2)

/-- |ℛ|, the number of rectangles of the g × g grid. -/
def rRect (s : Ready) : ℕ := nRectG (rG s) (rG s)

/-- «the |𝓘|^{|ℛ|} functions ι : ℛ → 𝓘». -/
def nPatterns (s : Ready) : ℕ := (rLists s).1.length ^ rRect s

/-! ### One pattern -/

/-- «the network with the smaller total»: the column network if its total is smaller, else the row
network. -/
def direction (v : Ready × ℕ) : Bool :=
  decide (totalG (listsAsPieces (rLists v.1)) (rG v.1) (rG v.1) true 0 (hLam (rHead v.1)) v.2 < totalG (listsAsPieces (rLists v.1)) (rG v.1) (rG v.1) false 0 (hLam (rHead v.1)) v.2)

/-- The parent that is handed to the callee for the pattern y = v.2 and the grouping x. -/
def parentAt (v : Ready × ℕ) (x : ℕ) : Parent :=
  ((v.1.1.1.1.1.2.2, unary (rG v.1)), (rHead v.1).2, rLists v.1, (direction v, v.2, x))

/-- What the search is given: ζ = 2^{−ℓ'−5} as the fraction 1/2^{ℓ'+5} = 1/2^{ℓ+4}, K and g, and the
input of Definition 2(iii) for the network with the smaller total. -/
def searchInput (c : ℕ) (v : Ready × ℕ) : GroupingInput := ((1, 2 ^ (hLev (rHead v.1) + 4)), netData c (parentAt v 0))

/-- The context of the call. The procedure of Lemma 8 names the grouping x and (K, L, B'), L = ⌈(U +
2ζgP)/K²⌉, B' = ⌈2gP/K⌉ + g²B₁ (`callOf`, module `ExplicitCost.GroupingDefs`); the solver calls (ℓ',
L, B') with the parent made from what it holds and x. -/
def child (z : (Ready × ℕ) × CliqueCall) : Ctx := (((rHead z.1.1).1.tail, z.2.2.2.1, z.2.2.2.2), some (parentAt z.1 z.2.1))

/-- Z_ι: **the procedure of Lemma 8 up to the call** (`groupingCall`: «find the first such grouping
among all K^g», then the call), on the network with the smaller total; its call is passed on as a
call of the solver (`QueryMachine.subst`, which lets the call be made from what the solver holds; 2
operations). -/
def patternValue (c : ℕ) : QueryMachine SolQuery Ans (Ready × ℕ) ℤ :=
  QueryMachine.mapIn (fun v : Ready × ℕ => (v, searchInput c v)) (groupingCall.subst (askInt fun z : (Ready × ℕ) × CliqueCall => (Sum.inl (child z) : SolQuery)))

/-! ### The stages -/

/-- The numbers c^row_i (tr = false) or c^col_i (tr = true), one query for each i in the list. -/
def capsLoop {σ : Type} [HasSize σ] (tr : Bool) (lamU : σ → List Unit) (idx : σ → List ℤ) : QueryMachine SolQuery Ans σ (List ℕ) :=
  QueryMachine.foldRange (fun s : σ => (idx s).length) (askInt fun v : σ × ℕ => Sum.inr (Sum.inr (lamU v.1, .inr (.inr (.inl (tr, (idx v.1).getD v.2 0))))))
    (fun acc _ (b : ℤ) => acc ++ [b.toNat]) fun _ => []

/-- «adding one Z_ι», for all ι; then «computing d^{|ℛ|} and dividing by it». -/
def sumAndDivide (c : ℕ) : QueryMachine SolQuery Ans Ready ℤ :=
  QueryMachine.bind (QueryMachine.sumRange nPatterns (patternValue c)) (QueryMachine.lift (Stepped.ofFun fun p : Ready × ℤ => p.2 / (((rD p.1).toNat ^ rRect p.1 : ℕ) : ℤ)))

/-- The solver at a level ℓ = ℓ' + 1. -/
def levelSolver (c x₀ : ℕ) : QueryMachine SolQuery Ans Head ℤ :=
  QueryMachine.bind (QueryMachine.lift (Stepped.mapIn (fun a : Head => a.1.tail) (numbersM x₀)))
    (QueryMachine.bind (askList fun s : Stage₁ => Sum.inr (Sum.inr (s.1.2.1, .inr (.inl ()))))
      (QueryMachine.bind (askInt fun s : Stage₂ => Sum.inr (Sum.inr (s.1.1.2.1, .inl ())))
        (QueryMachine.bind (capsLoop false (fun s : Stage₃ => s.1.1.1.2.1) fun s : Stage₃ => s.1.2)
          (QueryMachine.bind (capsLoop true (fun s : Stage₄ => s.1.1.1.1.2.1) fun s : Stage₄ => s.1.1.2) (sumAndDivide c)))))

/-- The solver at the level 0: «brute force» on K₀ = 2^{x₀} nodes. -/
def baseSolver (x₀ : ℕ) : QueryMachine SolQuery Ans Head ℤ :=
  QueryMachine.mapIn (fun a : Head => a.2) (readAs asInt (QueryMachine.mapAsk (fun q : TableQuery => (Sum.inr (Sum.inl q) : SolQuery)) (bruteMachine (2 ^ x₀))))

/-- **The solver.** Of the context it reads (ℓ, λ, B) only; the parent is for the procedure, and is
not kept in the states of the solver. -/
def solver (c x₀ : ℕ) : QueryMachine SolQuery Ans Ctx Ans :=
  QueryMachine.mapOut (QueryMachine.mapIn Prod.fst (QueryMachine.ite (fun a : Head => a.1.isEmpty) (baseSolver x₀) (levelSolver c x₀))) Sum.inl

/-- **The one machine for all levels**: its input is the context of the outermost instance, (ℓ, λ,
B) in unary; it has query access to the tables of that instance and to the pieces. «The algorithm
uses ℓ, the pieces, the totals U^row, U^col and the constant c (through x₀ and B₁), but neither ρ
nor e_ℓ»: this is visible in the type, since the definition has the parameters c and x₀ and no
others. -/
def recursion (c x₀ : ℕ) : QueryMachine UpQuery Ans Ctx Ans := Tower.tower (solver c x₀) (procedure c)

/-- The same with the pieces computed by their algorithm (`PiecesCounted.withAlgorithm`): a query to
the tables is passed on, a query to the pieces is answered by running Alg. This machine has query
access to the tables alone. -/
def recursionWith (c x₀ : ℕ) (Alg : Stepped PieceQuery Ans) : QueryMachine TableQuery Ans Ctx Ans := PiecesCounted.withAlgorithm (recursion c x₀) Alg

/-- **The algorithm of Theorem A (b)**, in the form in which `CliqueLevels.Solves` speaks of it: the
input is (ℓ, λ, B) in unary, a query to the tables is answered by an integer, the result is an
integer. -/
def cliqueMachine (c x₀ : ℕ) (Alg : Stepped PieceQuery Ans) : QueryMachine TableQuery ℤ Head ℤ :=
  QueryMachine.mapOut (QueryMachine.mapIn (fun h : Head => ((h, none) : Ctx)) (readAs Sum.inl (recursionWith c x₀ Alg))) asInt

end ExplicitCost
