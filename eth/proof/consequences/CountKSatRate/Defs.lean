/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSat.Defs
public import CountKSat.Interfaces
public import PaddedDescent.F.Prog
public import PaddedDescent.Reduce

/-! # Counting satisfying assignments for clauses of width k, with a padded input: definitions

This file holds, for every width k, definitions for counting the satisfying assignments of a formula
written in the input: the depth-first walk `walkS` of the sparsification tree, on the
pairs (formula, side list) of `proof/consequences/CountKSat/Defs.lean`, which adds up the values of
the leaves; the formula `leafM` of a node, built from its formula and its side list;
the number `nK k` of variables written in the input; exhaustive counting `bruteN k` with fuel; the
padding machine `padMW` with a word as result; and a bound `stackLenC` on the length
of the word of a state of the walk. The width k is a constant of the definitions, not a part of the
input.
This file has definitions only. -/

@[expose] public section

namespace CountKSatRate

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F
open WidthK (theta bsum leafC)

/-! ### The walk that adds up -/

/-- One round of the depth-first walk that keeps only the sum of the values of the leaves met so
far. -/
def roundS {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ) : List σ × ℕ → List σ × ℕ
  | ([], c) => ([], c)
  | (s :: r, c) =>
    match step s with
    | none => (r, c + val s)
    | some (l, h) => (l :: h :: r, c)

/-- The depth-first walk of the counting tree for width k, one round for each unit of the pad. -/
def walkS (k : ℕ) (pad : U) (τ : ℕ) (val : CNode → ℕ) (r : CNode) : ℕ :=
  (pad.foldl (fun st _ => cap pad ([], 0) (roundS (stepC (theta τ) k) val st)) (cap pad ([], 0) ([r], 0))).2

/-! ### The functions -/

/-- The side list made short in every variable: the clauses of one literal, each of them once. The
other clauses of a side list are the clauses xᵢ ∨ ¬xᵢ, which are always
true. A count on all n variables, whether they occur or not, does not need them. -/
def sideU (X : PFml) : PFml := (X.filter fun C => C.length == 1).dedup

/-- The formula of a node: its side list made short, followed by its formula. It has the same
satisfying assignments as `leafF x`, and a variable occurs in at most two clauses of its first part. -/
def leafM (x : CNode) : Fml := sideU x.2 ++ x.1

/-- The number of variables written in the bit string x, read as the code of an instance of k-SAT. -/
def nK (k : ℕ) (x : List Bool) : ℕ := (decU k x).1.length

/-- Exhaustive counting with fuel: among the assignments number 0, …, 2^n − 1 (assignment number y
gives the variable i the i-th binary digit of y), cut off at the length of
the pad, how many satisfy the formula written in the bit string. -/
def bruteN (k : ℕ) (p : List Bool × U) : ℕ := ((rng p.2 (2 ^ nK k p.1)).filter fun y => satAt (decU k p.1).2 y).length

/-! ### The padding machine with a word as result -/

/-- The stepped machine: the state is the input with the present pad, or the result. One step
doubles the pad, or, once the pad has length at least 2^(e x), applies B. -/
def padMW (e : List Bool → ℕ) (B : List Bool × List Unit → List Bool) : Stepped (List Bool) (List Bool) where
  σ := (List Bool × List Unit) ⊕ List Bool
  init x := .inl (x, [()])
  step s := s.elim (fun p => bif decide (e p.1 ≤ Nat.log2 p.2.length) then .inr (B p) else .inl (p.1, p.2 ++ p.2))
    fun w => .inr w
  out s := s.elim (fun _ => none) fun w => some w

/-- An upper bound for the length of the word of a state of the walk: at most bsum τ k · n + 1
nodes, each a formula of at most 2^k·m clauses of at most k literals and a side
list of at most 2n clauses of at most 2 literals, all on variables below n; and a number below
2^(n+1). -/
def stackLenC (k τ n m : ℕ) : ℕ :=
  (bsum τ k * n + 1) * (2 ^ k * m * (k * (3 * n + 5) + 10) + 2 * n * (2 * (3 * n + 5) + 10) + 8) + 3 * n + 16

end CountKSatRate
