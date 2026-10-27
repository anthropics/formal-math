/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GraphProblems.Interfaces
public import GraphProblems.SetTM
public import SizeCircuit.Defs
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.VertexCover

/-! # Section 7, proof of Corollary 7: «The cliques of size s are the independent sets of size s of the complement graph, and the vertex covers of size s are the complements of the independent sets of size n − s.» (definitions and statements only)

proof/consequences/GraphProblems/ gives cliques and vertex covers formulas of their own (`cliqueF`,
`coverF`). Here both numbers are obtained, as in the paper, from the ONE formula for independent
sets (`indepF`): for cliques on the matrix of the complement graph, for vertex covers with n − s in
the place of s.
This file has no theorem. -/

@[expose] public section

namespace Complement

open Groundwork Groundwork.Prog CountKSat GraphProblems

/-- «The cliques of size s are the independent sets of size s of the complement graph». -/
def StCliques : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), (∀ S : Finset (Fin n), G.IsNClique s S ↔ Gᶜ.IsNIndepSet s S) ∧ numCliques G s = numIndepSets Gᶜ s

/-- «the vertex covers of size s are the complements of the independent sets of size n − s», for s ≤
n. -/
def StCovers : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n →
  (∀ S : Finset (Fin n), (G.IsVertexCover (S : Set (Fin n)) ∧ S.card = s) ↔ G.IsNIndepSet (n - s) Sᶜ) ∧ numVertexCovers G s = numIndepSets G (n - s)

/-- The adjacency matrix of the complement graph, from that of the graph: the entry (u, v) is 1
exactly if u ≠ v and the old entry is 0. -/
def complMatrix (n : ℕ) (m : List Bool) : List Bool := (pairs n).map fun p => p.1 != p.2 && !adjB n m p.1 p.2

/-- It is the matrix of the complement graph. -/
def StComplMatrix : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)), complMatrix n (matrix G) = matrix Gᶜ

/-- It is computed in polynomial time from (n in unary, matrix). -/
def StComplCert : Prop := PolyT fun a : List Unit × List Bool => complMatrix a.1.length a.2

/-- The reader for cliques: `codeWith G s` as (n in unary, s, formula for independent sets of the
complement graph). -/
def readClique (x : List Bool) : List Unit × ℕ × Fml := ((read2 x).1, (read2 x).2.1, indepF (read2 x).1.length (complMatrix (read2 x).1.length (read2 x).2.2))

/-- The reader for vertex covers: `codeWith G s` as (n in unary, n − s, formula for independent sets
of the graph). -/
def readCover (x : List Bool) : List Unit × ℕ × Fml := ((read2 x).1, (read2 x).1.length - (read2 x).2.1, indepF (read2 x).1.length (read2 x).2.2)

/-- What the two readers hand over counts cliques and vertex covers. -/
def StReaders : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n →
  (readClique (codeWith G s) = (List.replicate n (), s, indepF n (matrix Gᶜ)) ∧ cntS n s (indepF n (matrix Gᶜ)) = numCliques G s) ∧
  (readCover (codeWith G s) = (List.replicate n (), n - s, indepF n (matrix G)) ∧ cntS n (n - s) (indepF n (matrix G)) = numVertexCovers G s)

/-- The two readers are polynomial-time. -/
def StReadersCert : Prop := PolyT readClique ∧ PolyT readCover

/-- **For EVERY machine Z that counts with a prescribed number of true variables** (the body of
`GraphProblems.StSized` at width 2 with the exponent δ): Z after `readClique` returns the number of
cliques of size s, and Z after `readCover` the number of vertex covers of size s, within the same
number of steps. -/
def StCounts : Prop := ∀ (Z : Stepped (List Unit × ℕ × Fml) ℕ) (δ : ℝ) (c : ℕ),
  (∀ (n s : ℕ) (ψ : Fml), s ≤ n → Shaped 2 n ψ → ∃ T : ℕ, Z.Runs (List.replicate n (), s, ψ) T (c * (n + ψ.length + 2) ^ c) (cntS n s ψ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)) →
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n →
    (∃ T : ℕ, (Stepped.mapIn readClique Z).Runs (codeWith G s) T (c * (n + n * n + 2) ^ c) (numCliques G s) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)) ∧
    (∃ T : ℕ, (Stepped.mapIn readCover Z).Runs (codeWith G s) T (c * (n + n * n + 2) ^ c) (numVertexCovers G s) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n))

/-- The formula for independent sets alone: its certificate and its shape. (In
proof/consequences/GraphProblems/ these facts are bundled with those for `cliqueF` and `coverF`;
they are stated apart here, so that the route here does not depend on the two formulas.) -/
def StIndepAlone : Prop := PolyT (fun a : List Unit × List Bool => indepF a.1.length a.2) ∧ ∀ (n : ℕ) (m : List Bool), Shaped 2 n (indepF n m) ∧ (indepF n m).length ≤ n * n

/-- **With the machines named.** From the interface `GraphProblems.StSized`: for every δ > 0 ONE
machine Z, put after the two readers, counts the cliques and the vertex covers of size s ≤ n within
c·2^{δn} steps, with polynomial-time steps. -/
def StFromSized : Prop := StSized → ∀ δ : ℝ, 0 < δ → ∃ Z : Stepped (List Unit × ℕ × Fml) ℕ,
  Nonempty (IsPolyT (Stepped.mapIn readClique Z)) ∧ Nonempty (IsPolyT (Stepped.mapIn readCover Z)) ∧ ∃ c : ℕ,
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n →
    (∃ T : ℕ, (Stepped.mapIn readClique Z).Runs (codeWith G s) T (c * (n + n * n + 2) ^ c) (numCliques G s) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)) ∧
    (∃ T : ℕ, (Stepped.mapIn readCover Z).Runs (codeWith G s) T (c * (n + n * n + 2) ^ c) (numVertexCovers G s) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n))

/-- **The route from end to end, counted in steps.** «Add the clause {¬x_u, ¬x_v} for each edge uv;
Corollary 6 then counts the independent sets of size s. The cliques … the vertex covers …» For every
family of circuits that tests the size, every δ > 0 and EVERY procedure E for #3-SAT whose exponent
δ_E is small enough for the O(n) variables of Γ: the machine that puts Γ beside the formula and then
runs E (`SizeCircuit.sizedBy gates E`),
put after the reader of the formula for independent sets (`GraphProblems.readF indepF`), after
`readClique` and after `readCover`, returns the numbers of independent sets, cliques and vertex
covers of size s ≤ n within c'·2^{δn} steps. -/
def StFromGamma : Prop := ∀ (gates : ℕ → ℕ → List CircuitLowerBound.GateD) (a : ℕ), SizeCircuit.TestsSize gates a →
  ∀ (δ δE : ℝ), 0 < δ → 0 ≤ δE → δE * ((a : ℝ) + 1) ≤ δ →
  ∀ (E : Stepped (List Unit × Fml) (List Bool)) (c : ℕ), Eight.Serves E (max 2 3) δE c →
  ∃ c' : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n →
    (∃ T : ℕ, (Stepped.mapIn (readF indepF) (SizeCircuit.sizedBy gates E)).Runs (codeWith G s) T (c' * (n + n * n + 2) ^ c') (numIndepSets G s) ∧ (T : ℝ) ≤ c' * (2 : ℝ) ^ (δ * n)) ∧
    (∃ T : ℕ, (Stepped.mapIn readClique (SizeCircuit.sizedBy gates E)).Runs (codeWith G s) T (c' * (n + n * n + 2) ^ c') (numCliques G s) ∧ (T : ℝ) ≤ c' * (2 : ℝ) ^ (δ * n)) ∧
    (∃ T : ℕ, (Stepped.mapIn readCover (SizeCircuit.sizedBy gates E)).Runs (codeWith G s) T (c' * (n + n * n + 2) ^ c') (numVertexCovers G s) ∧ (T : ℝ) ≤ c' * (2 : ℝ) ^ (δ * n))

/-- The two clauses of `GraphProblems.CorGraphsCount` and the two of `GraphProblems.CorGraphsDecide`
on cliques and vertex covers, on Mathlib's Turing machines. The counting machines are Z of
`StFromSized` after `readClique` and `readCover`, with the number written by `Nat.bits`; the
deciding machines are the same with «the number is not 0» as the output, which decides by
`GraphProblems.StDecide` («subsets of … cliques, and supersets of vertex covers …, are again such
sets»).
By its statement this shows nothing beyond proof/consequences/GraphProblems/ (which proves it with
formulas of their own); `StCounts`, `StFromSized` and `StFromGamma` name the route by counting. The
route goes from `StFromSized` and `GraphProblems.StDecide` through the host theorem of
proof/consequences/GraphProblems/ (`GraphProblems.tm_of_stepped`), and it uses `StCliques`,
`StCovers`, `StCounts` and `StFromSized`
(proved as `Complement.stCliques`, `stCovers`, `stCounts`, `stFromSized`), not the formulas
`GraphProblems.cliqueF` and `GraphProblems.coverF` of proof/consequences/GraphProblems/. It is the
proof of Corollary 7 by counting (both halves), not the proof of `GraphProblems.CorGraphsDecide`
from 3-SAT in proof/consequences/Sat3Graph/, which uses no counting machine.
(For cliques the formula of proof/consequences/GraphProblems/ and the one here are the same list;
for vertex covers they differ.) -/
def StOnTuringMachines : Prop := StSized → ∀ δ : ℝ, 0 < δ →
  CountsInTime (fun _ G s => numCliques G s) δ ∧ CountsInTime (fun _ G s => numVertexCovers G s) δ ∧
  DecidesInTime (fun n G s => ∃ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) ∧ s ≤ S.card) δ ∧
  DecidesInTime (fun n G s => ∃ S : Finset (Fin n), G.IsVertexCover (S : Set (Fin n)) ∧ S.card ≤ s) δ

end Complement
