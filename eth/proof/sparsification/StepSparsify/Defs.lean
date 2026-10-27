/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Defs
public import SparsificationLemma.Cal.Defs
public import UniformInK.Top.Defs

/-! # Step 5 of Appendix D for any thresholds that serve: definitions and statements

Step 5 of Appendix D sparsifies with Calabro's thresholds, and the paper remarks that any
sparsification with few outputs, few occurrences of a variable and no satisfying assignment
shared by two outputs gives the same bound. This file is about one procedure (`stepC`, with its side
list), run with a family of thresholds Θ k s (width k, precision s, with 2^(−s) in the role of ε).
`Serves Θ Lc` says what Step 5 takes from such a family: at most 2^(⌊n/2^s⌋+1) leaves, at most Lc k
s occurrences of a variable at a leaf, the count as the sum over the leaves, and polynomial time.
Calabro's thresholds are such a family (`StServesCal`).
This is a special case of the remark, with fixed constants, not the remark itself.
The counting tree is walked depth first, one round for each unit of a pad (`walkSG`); the clauses
that contain a variable together with its negation are deleted first, as in the paper. Unlike in the
paper, the side list of the walk starts
with the n clauses xᵢ ∨ ¬xᵢ (`rootC`), which the count of a leaf leaves out again (`leafM`); the
outputs are the same (`SparsificationLemma.StOutputsSame`).
Calabro's thresholds are `SparsificationLemma.Cal.thetaC α` with α =
`SparsificationLemma.Cal.alphaC (max k 3) (1/2^s)`. The procedure runs with the width k; only α is
taken for K = max(k, 3), because the
bound on the number of leaves needs x = 32(K−1)²/ε ≥ 128. The paper runs the procedure with the
width max(k, 3), where k is the largest number of literals in a clause. On a k-CNF the two runs
should make the same steps, since no clause has more
than k literals, but this is not proved here.
This file has definitions only; each `St…` here is a proposition, and none is proved in this file. -/

@[expose] public section

namespace StepSparsify

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK SparsificationLemma
open PaddedDescent.F.Mark (occ)

/-! ### What Step 5 takes from the sparsification -/

/-- The family of thresholds Θ k s, with the bound Lc k s on the occurrences of a variable, serves
for Step 5. -/
structure Serves (Θ : ℕ → ℕ → ℕ → ℕ) (Lc : ℕ → ℕ → ℕ) : Prop where
  /-- The tree for width k ≥ 1 and precision s ≥ `s0U k`, of a k-CNF in which no clause contains a
  variable together with its negation: what `UniformInK.StTreeU` says, with 2^(⌊n/2^s⌋+1) for the
  number of leaves and Lc k s for the occurrences. -/
  tree : ∀ (k n s : ℕ), 1 ≤ k → s0U k ≤ s → ∀ ψ : PFml, IsKCNF k n ψ → (∀ C ∈ ψ, ∀ l ∈ C, (l.1, !l.2) ∉ C) →
    (leaves (stepC (Θ k s) k) (bsumU (tauOf s) k * n) (rootC (List.replicate n (), ψ))).length ≤ 2 ^ (n / 2 ^ s + 1) ∧
    (∀ x ∈ leaves (stepC (Θ k s) k) (bsumU (tauOf s) k * n) (rootC (List.replicate n (), ψ)),
      stepC (Θ k s) k x = none ∧ (leafF x).length ≤ (Lc k s + 2) * n ∧
        (∀ C ∈ x.1, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ (∀ v, (occ x.1 v).length ≤ Lc k s) ∧
        ∀ C ∈ x.2, (C ∈ taut n ∨ ∃ l, C = [l]) ∧ ∀ l ∈ C, l.1 < n) ∧
    cntN n ψ = ((leaves (stepC (Θ k s) k) (bsumU (tauOf s) k * n) (rootC (List.replicate n (), ψ))).map fun x => cntN n (leafF x)).sum ∧
    ∀ i, ((round (stepC (Θ k s) k))^[i] ([rootC (List.replicate n (), ψ)], [])).1.length ≤ bsumU (tauOf s) k * n + 1 ∧
      ∀ x ∈ ((round (stepC (Θ k s) k))^[i] ([rootC (List.replicate n (), ψ)], [])).1,
        x.1.length ≤ ψ.length * 2 ^ k ∧ x.2.length ≤ 2 * n ∧ (∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n
  /-- The bound on the occurrences, plus 2, is at most 2^(betaU k s) = 2^(2k(4s+17)). -/
  par : ∀ k s : ℕ, 1 ≤ k → s0U k ≤ s → Lc k s + 2 ≤ 2 ^ betaU k s
  /-- The two children of a node are polynomial-time jointly in k, s and the node, if k, 2^k and s
  are given in unary. -/
  cert : ∀ (α : Type) [Enc α] (k s : α → ℕ) (x : α → CNode), Unary k → (Unary fun a => 2 ^ k a) → Unary s → PolyT x →
    PolyT fun a => stepC (Θ (k a) (s a)) (k a) (x a)

/-! ### The walk -/

/-- The depth-first walk of the counting tree for width k with the thresholds θ, one round for each
unit of the pad. -/
def walkSG (θ : ℕ → ℕ) (k : ℕ) (pad : U) (val : CNode → ℕ) (r : CNode) : ℕ :=
  (pad.foldl (fun st _ => cap pad ([], 0) (roundS (stepC θ k) val st)) (cap pad ([], 0) ([r], 0))).2

section
variable (Θ : ℕ → ℕ → ℕ → ℕ) {Idx : Type} [Enc Idx] (S : Solver Idx)

end

/-! ### The statements -/

/-- If the procedure has stopped at every node that is listed when the paths are cut after d steps,
the pad has at least 2·(number of these nodes) − 1 units and the word of every state of the walk
fits under the pad, then `walkSG` returns the sum of the
values of these nodes. -/
def StWalkSG : Prop := ∀ (θ : ℕ → ℕ) (k : ℕ) (pad : U) (val : CNode → ℕ) (r : CNode) (d : ℕ),
  (∀ x ∈ leaves (stepC θ k) d r, stepC θ k x = none) → 2 * (leaves (stepC θ k) d r).length ≤ pad.length + 1 →
  (∀ i, len ((roundS (stepC θ k) val)^[i] ([r], 0)) ≤ pad.length) →
  walkSG θ k pad val r = ((leaves (stepC θ k) d r).map val).sum

/-- If `val` is right on every node that has the properties of a leaf, and the pad suffices for the
rounds and for the stack, the walk returns the number of satisfying assignments. -/
def StWalkCountG : Prop := ∀ (Θ : ℕ → ℕ → ℕ → ℕ) (Lc : ℕ → ℕ → ℕ), Serves Θ Lc →
  ∀ (k s n : ℕ) (φ : Sat3.CNF n) (pad : U) (val : CNode → ℕ), 1 ≤ k → SatK.IsKCNF k φ → s0U k ≤ s →
  2 * 2 ^ (n / 2 ^ s + 1) ≤ pad.length + 1 → stackLenCU k (tauOf s) n (inLen k n) ≤ pad.length →
  (∀ x : CNode, (leafF x).length ≤ (Lc k s + 2) * n → (∀ C ∈ x.1, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) → (∀ v, (occ x.1 v).length ≤ Lc k s) →
    (∀ C ∈ x.2, (C ∈ taut n ∨ ∃ l, C = [l]) ∧ ∀ l ∈ C, l.1 < n) → val x = cntN n (leafF x)) →
  (bif hasNil (Decode.toN φ) then 0 else walkSG (Θ k s) k pad val (rootC (List.replicate n (), noTaut (Decode.toN φ)))) = SatK.numSat φ

/-- The summing walk is polynomial-time in the pad, jointly in the width k and the precision s, if
k, 2^k and s are given in unary. -/
def StCertWalkSG : Prop := ∀ (Θ : ℕ → ℕ → ℕ → ℕ) (Lc : ℕ → ℕ → ℕ), Serves Θ Lc →
  ∀ (α : Type) [Enc α] (k s : α → ℕ) (pad : α → U) (val : α → CNode → ℕ) (r : α → CNode),
  Unary k → (Unary fun x => 2 ^ k x) → Unary s → PolyT pad → (PolyT fun p : α × CNode => val p.1 p.2) → PolyT r →
  PolyT fun t => walkSG (Θ (k t) (s t)) (k t) (pad t) (val t) (r t)

/-- Deleting the clauses that contain a variable together with its negation is polynomial-time. -/
def StCertNoTaut : Prop := PolyT noTaut

/-! ### Calabro's thresholds -/

/-- Calabro's α for max(k, 3) in the place of k, and ε = 2^(−s). -/
def alphaS (k s : ℕ) : ℕ := Cal.alphaC (max k 3) (1 / 2 ^ s)

/-- Calabro's thresholds with this α. -/
def thCal (k s : ℕ) : ℕ → ℕ := Cal.thetaC (alphaS k s)

/-- Their bound on the occurrences: 2·(θ₀ + … + θ_{k−1}). -/
def lcCal (k s : ℕ) : ℕ := 2 * ∑ j ∈ range k, thCal k s j

/-- α without fractions: with K = max(k, 3), α = 2(K−1)²·2^s·⌈log₂(32(K−1)²·2^s)⌉. -/
def StAlphaS : Prop := ∀ k s : ℕ, alphaS k s = 2 * (max k 3 - 1) ^ 2 * 2 ^ s * Nat.clog 2 (32 * (max k 3 - 1) ^ 2 * 2 ^ s)

/-- Calabro's numbers fit the bounds of the plan, for k ≥ 1 and s ≥ `s0U k`: 1 ≤ α and k² ≤ α; β₁ +
… + β_{k−1} ≤ τ^(2k) for τ = 2^(4s+17); 2·(θ₀ + … + θ_{k−1}) + 2 ≤ 2^(2k(4s+17)). -/
def StCalNumbers : Prop := ∀ k s : ℕ, 1 ≤ k → s0U k ≤ s →
  1 ≤ alphaS k s ∧ k ^ 2 ≤ alphaS k s ∧ ∑ c ∈ range k, Cal.betaC (alphaS k s) c ≤ bsumU (tauOf s) k ∧ lcCal k s + 2 ≤ 2 ^ betaU k s

/-- The tree with Calabro's thresholds has at most 2^(⌊n/2^s⌋+1) leaves, wherever the paths are cut,
as long as D ≥ (β₁ + … + β_{k−1})·n (no path is longer, so the tree is the same for all these D). -/
def StCalLeaves : Prop := ∀ (k n s D : ℕ) (ψ : PFml), 1 ≤ k → (∑ c ∈ range k, Cal.betaC (alphaS k s) c) * n ≤ D → IsKCNF k n ψ →
  (tree (thCal k s) k D ψ).length ≤ 2 ^ (n / 2 ^ s + 1)

/-- Calabro's thresholds are polynomial-time, jointly in k, s and the index, all given in unary. -/
def StCertThCal : Prop := ∀ (α : Type) [Enc α] (k s i : α → ℕ), Unary k → Unary s → Unary i → PolyT fun a => thCal (k a) (s a) (i a)

/-- Calabro's thresholds serve. -/
def StServesCal : Prop := Serves thCal lcCal

end StepSparsify
