/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GraphProblems.Defs
public import ToTuring.PolyT
public import StepMachines.Math.SparsifyTree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Corollary 7: the interface statements, as propositions

The statements that one file needs from another are written here as definitions `St… : Prop`, in the
manner of `proof/consequences/CountKSat/Interfaces.lean`. Nothing is proved and nothing is assumed:
this file has
no theorem. One file proves `theorem … : St…`; a file that needs the statement takes it as a
hypothesis. -/

@[expose] public section

namespace GraphProblems

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat Finset

/-- Every clause of ψ has at most w literals and variables below N. -/
def Shaped (w N : ℕ) (ψ : Fml) : Prop := ∀ C ∈ ψ, C.length ≤ w ∧ ∀ l ∈ C, l.1 < N

/-! ### Reading the input (proof/consequences/GraphProblems/Read.lean) -/

def StRead1 : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)), read1 (code G) = (List.replicate n (), matrix G)

def StRead2 : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), read2 (codeWith G s) = (List.replicate n (), s, matrix G)

def StAdj : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (u v : Fin n), adjB n (matrix G) u v = true ↔ G.Adj u v

def StMatrixLength : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)), (matrix G).length = n * n

/-! ### What the formulas say (proof/consequences/GraphProblems/Sets.lean, Color.lean) -/

def StIndep : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), cntS n s (indepF n (matrix G)) = numIndepSets G s

def StDom : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), cntS n s (domF n (matrix G)) = numDominatingSets G s

def StColor : Prop := ∀ (k n : ℕ) (G : SimpleGraph (Fin n)), cntN (n * k) (colorF k n (matrix G)) = numColorings G k

def StShapeColor : Prop := ∀ (k n : ℕ) (m : List Bool), Shaped (max k 2) (n * k) (colorF k n m)

/-- The decision problems from the numbers: subsets of independent sets and of cliques, and
supersets of vertex covers and of dominating sets, are again such sets. -/
def StDecide : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n →
  ((∃ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) ∧ s ≤ S.card) ↔ numIndepSets G s ≠ 0) ∧
  ((∃ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) ∧ s ≤ S.card) ↔ numCliques G s ≠ 0) ∧
  ((∃ S : Finset (Fin n), G.IsVertexCover (S : Set (Fin n)) ∧ S.card ≤ s) ↔ numVertexCovers G s ≠ 0) ∧
  ((∃ S : Finset (Fin n), IsDominating G S ∧ S.card ≤ s) ↔ numDominatingSets G s ≠ 0)

def StDecideColor : Prop := ∀ (k n : ℕ) (G : SimpleGraph (Fin n)), G.Colorable k ↔ numColorings G k ≠ 0

/-! ### The machine that counts with a prescribed number of true variables (proof/consequences/GraphProblems/Sized.lean) -/

/-- For every width w and every δ > 0 a machine cut into polynomial-time steps returns `cntS n s ψ`
on (n in unary, s, ψ), for s ≤ n and ψ of width at most w with variables below n, within c·2^{δn}
steps and
with states of size polynomial in n and the number of clauses. -/
def StSized : Prop := ∀ (w : ℕ) (δ : ℝ), 0 < δ → ∃ Z : Stepped (List Unit × ℕ × Fml) ℕ, Nonempty (IsPolyT Z) ∧ ∃ c : ℕ,
  ∀ (n s : ℕ) (ψ : Fml), s ≤ n → Shaped w n ψ →
    ∃ T : ℕ, Z.Runs (List.replicate n (), s, ψ) T (c * (n + ψ.length + 2) ^ c) (cntS n s ψ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)

/-! ### The tree for Dominating Set (proof/consequences/GraphProblems/DomTree.lean) -/

/-- `stepD w` (with `rootD`) shortens the clauses of Dominating Set to width w. The tree of depth 2n
has at most 2^{εn} leaves. At a leaf no clause has more than w literals, there are at most 3n
clauses, and
their variables are below n. The numbers `cntS` of the leaves add up to that of `domF`. The stack of
the walk never holds more than 2n + 1 nodes; each holds at most n open clauses of at most n
variables below n, and at most
2n closed clauses of at most w literals with variables below n. -/
def ShortensD (w : ℕ) (ε : ℝ) : Prop := ∀ (n s : ℕ) (m : List Bool),
  ((leaves (stepD w) (2 * n) (rootD (List.replicate n (), s, m))).length : ℝ) ≤ (2 : ℝ) ^ (ε * n) ∧
  (∀ x ∈ leaves (stepD w) (2 * n) (rootD (List.replicate n (), s, m)), stepD w x = none ∧ x.1 = (List.replicate n (), s) ∧
    Shaped w n (leafD x).2.2 ∧ (leafD x).2.2.length ≤ 3 * n) ∧
  cntS n s (domF n m) = ((leaves (stepD w) (2 * n) (rootD (List.replicate n (), s, m))).map fun x => cntS n s (leafD x).2.2).sum ∧
  ∀ i, ((round (stepD w))^[i] ([rootD (List.replicate n (), s, m)], [])).1.length ≤ 2 * n + 1 ∧
    ∀ x ∈ ((round (stepD w))^[i] ([rootD (List.replicate n (), s, m)], [])).1, x.1 = (List.replicate n (), s) ∧
      x.2.1.length ≤ n ∧ (∀ D ∈ x.2.1, D.length ≤ n ∧ ∀ u ∈ D, u < n) ∧ x.2.2.length ≤ 2 * n ∧ Shaped w n x.2.2

/-- For every ε > 0 some width w ≥ 1 works. -/
def StShortens : Prop := ∀ ε : ℝ, 0 < ε → ∃ w : ℕ, 1 ≤ w ∧ ShortensD w ε

/-! ### Certificates (proof/consequences/GraphProblems/Cert.lean) -/

def StCertRead : Prop := PolyT read1 ∧ PolyT read2

/-- The formulas of the problems are computed in polynomial time from (n in unary, matrix). -/
def StCertForm : Prop :=
  PolyT (fun a : List Unit × List Bool => indepF a.1.length a.2) ∧ PolyT (fun a : List Unit × List Bool => cliqueF a.1.length a.2) ∧
  PolyT (fun a : List Unit × List Bool => coverF a.1.length a.2) ∧ ∀ k : ℕ, PolyT (fun a : List Unit × List Bool => colorF k a.1.length a.2)

/-- The formula of a vector of block sizes is computed in polynomial time from ((n in unary, s, ψ),
y). -/
def StCertBlock : Prop := ∀ b : ℕ, PolyT fun p : (List Unit × ℕ × Fml) × ℕ => blockF b p.1.1.length p.1.2.1 p.2 p.1.2.2

def StCertDom : Prop := (∀ w : ℕ, PolyT (stepD w)) ∧ PolyT rootD ∧ PolyT leafD

end GraphProblems
