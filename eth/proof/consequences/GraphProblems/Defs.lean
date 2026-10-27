/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GraphProblemsStatement
public import CountKSat.Defs

/-! # Corollary 7: the programs (definitions only)

How the input word is read, the formulas that express the five problems, the formulas that fix the
number of true variables block by block, and the tree that shortens the long clauses of
Dominating Set. A formula is a `Fml` = list of clauses = list of lists of (variable, wanted value),
with natural numbers as variables, as in the namespace `CountKSat`. -/

@[expose] public section

namespace GraphProblems

open Groundwork Groundwork.Prog CountKSat

/-! ### Reading the input -/

/-- The number of ones at the start of a word. -/
def ones (x : List Bool) : ℕ := (x.takeWhile id).length

/-- The word after its first ones and the zero that ends them. -/
def rest (x : List Bool) : List Bool := (x.dropWhile id).tail

/-- `code G` as (n in unary, adjacency matrix). -/
def read1 (x : List Bool) : List Unit × List Bool := (List.replicate (ones x) (), rest x)

/-- `codeWith G s` as (n in unary, s, adjacency matrix). -/
def read2 (x : List Bool) : List Unit × ℕ × List Bool := (List.replicate (ones x) (), ones (rest x), rest (rest x))

/-- The entry (u, v) of an n × n matrix written row by row. -/
def adjB (n : ℕ) (m : List Bool) (u v : ℕ) : Bool := m.getD (u * n + v) false

/-- All pairs (u, v) with u, v < n. -/
def pairs (n : ℕ) : List (ℕ × ℕ) := List.range n ×ˢ List.range n

/-! ### Counting with a prescribed number of true variables -/

/-- The number of assignments to x₀ … xₙ₋₁ that make a literal of every clause of ψ true and make
exactly s variables true. -/
def cntS (n s : ℕ) (ψ : Fml) : ℕ :=
  (Finset.univ.filter fun a : Fin n → Bool => (∀ C ∈ ψ, ∃ l ∈ C, ext a l.1 = l.2) ∧ (Finset.univ.filter fun i => a i = true).card = s).card

/-! ### The formulas of the problems: the variable x_v says that the vertex v is in the set -/

/-- Independent set: ¬x_u ∨ ¬x_v for every edge. -/
def indepF (n : ℕ) (m : List Bool) : Fml := ((pairs n).filter fun p => adjB n m p.1 p.2).map fun p => [(p.1, false), (p.2, false)]

/-- Clique: ¬x_u ∨ ¬x_v for all u ≠ v that are not adjacent. -/
def cliqueF (n : ℕ) (m : List Bool) : Fml :=
  ((pairs n).filter fun p => p.1 != p.2 && !adjB n m p.1 p.2).map fun p => [(p.1, false), (p.2, false)]

/-- Vertex cover: x_u ∨ x_v for every edge. -/
def coverF (n : ℕ) (m : List Bool) : Fml := ((pairs n).filter fun p => adjB n m p.1 p.2).map fun p => [(p.1, true), (p.2, true)]

/-- The closed neighborhoods, as lists of vertices. -/
def nbhd (n : ℕ) (m : List Bool) : List (List ℕ) := (List.range n).map fun v => v :: (List.range n).filter fun u => u != v && adjB n m v u

/-- A list of variables as a clause of positive literals. -/
def posC (D : List ℕ) : List (ℕ × Bool) := D.map fun u => (u, true)

/-- Dominating set: for every vertex v the clause x_v ∨ ⋁ x_u over the neighbors u of v. Its width
is not bounded. -/
def domF (n : ℕ) (m : List Bool) : Fml := (nbhd n m).map posC

/-- Proper colorings with k colors, on n·k variables: x_{v·k+c} says that the vertex v has the color
c. Every vertex has a color, no vertex has two, and the ends of an edge do not have
the same color. -/
def colorF (k n : ℕ) (m : List Bool) : Fml :=
  ((List.range n).map fun v => (List.range k).map fun c => (v * k + c, true)) ++
  ((List.range n).flatMap fun v => ((pairs k).filter fun q => decide (q.1 < q.2)).map fun q => [(v * k + q.1, false), (v * k + q.2, false)]) ++
  (((pairs n).filter fun p => adjB n m p.1 p.2).flatMap fun p => (List.range k).map fun c => [(p.1 * k + c, false), (p.2 * k + c, false)])

/-! ### Exactly s true variables, block by block

The variables are cut into blocks of b. There are n/b + 1 blocks, so that the b·(n/b + 1) > n
variables of the blocks include x₀ … xₙ₋₁; the others are set to false. A number
y < (b+1)^(n/b+1) is read in base b + 1: its digit i is the number of true variables wanted in block
i. -/

/-- All words of length b. -/
def pats : ℕ → List (List Bool)
  | 0 => [[]]
  | b + 1 => (pats b).flatMap fun p => [false :: p, true :: p]

/-- The number of blocks. -/
def nBlocks (b n : ℕ) : ℕ := n / b + 1

/-- The digit i of y in base b + 1. -/
def digit (b y i : ℕ) : ℕ := y / (b + 1) ^ i % (b + 1)

/-- «Exactly d of the b variables of block i are true»: one clause against every pattern with
another number of ones. -/
def blockCl (b i d : ℕ) : Fml :=
  ((pats b).filter fun p => p.count true != d).map fun p => (List.range b).map fun j => (i * b + j, !(p.getD j false))

/-- ψ, the variables from n on false, and digit i of y true variables in block i; a formula without
satisfying assignment if the digits of y do not add up to s. -/
def blockF (b n s y : ℕ) (ψ : Fml) : Fml :=
  if ((List.range (nBlocks b n)).map (digit b y)).sum = s then
    ψ ++ (((List.range (b * nBlocks b n)).filter fun i => decide (n ≤ i)).map fun i => [(i, false)]) ++
      (List.range (nBlocks b n)).flatMap fun i => blockCl b i (digit b y i)
  else [[]]

/-! ### The tree for Dominating Set (after Calabro, Impagliazzo and Paturi, as in the paper's proof of Corollary 7)

A node holds (n in unary, s), the clauses of positive literals that may still be long, and a formula
that is not touched any more. While some clause C has more than w literals, let H be its first w
variables. Light child: C is replaced by H. Heavy child: the variables of H are false, and are
deleted from all clauses. -/

/-- A node of the tree. -/
abbrev DNode : Type := (List Unit × ℕ) × (List (List ℕ) × Fml)

/-- The two children of a node; none if no clause has more than w literals. -/
def stepD (w : ℕ) (x : DNode) : Option (DNode × DNode) :=
  (x.2.1.find? fun C => decide (w < C.length)).map fun C =>
    ((x.1, (x.2.1.filter fun D => D != C, posC (C.take w) :: x.2.2)),
     (x.1, (x.2.1.map fun D => D.filter fun u => !(C.take w).contains u, ((C.take w).map fun u => [(u, false)]) ++ x.2.2)))

/-- The root: the closed neighborhoods. -/
def rootD (a : List Unit × ℕ × List Bool) : DNode := ((a.1, a.2.1), (nbhd a.1.length a.2.2, []))

/-- What is counted at a node: (n in unary, s, formula). -/
def leafD (x : DNode) : List Unit × ℕ × Fml := (x.1.1, x.1.2, x.2.1.map posC ++ x.2.2)

end GraphProblems
