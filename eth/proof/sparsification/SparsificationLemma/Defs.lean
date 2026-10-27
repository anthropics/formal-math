/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Spars.Defs
public import UniformInK.Tree.Defs

/-! # Sparsification that preserves the number of satisfying assignments: objects and general statements

The procedure is the one of proof/consequences/CountKSat/Defs.lean (`stepC`): a node is a pair (ψ,
𝒩) of the formula that the branching rule looks at and a side list of clauses that the rule never
looks at.
The rule (`pickK` in proof/sparsification/SparsifyWidthK/DefsProg.lean; `Rule` in
proof/sparsification/SparsifyWidthK/Defs.lean on finite sets) looks for a set H of literals, 1 ≤ |H|
< c ≤ k, that lies in at least θ(c − |H|) clauses of size c; it takes the smallest such c,
then a largest such H. The first child gets the clause H; the second child gets the clauses E ∖ H
for the clauses E of size c that contain H, and on its side list the clause {¬ω} for every ω ∈ H. In
each child the clauses that contain a new clause are deleted (`addP`); since the parent had no
clause that contains another clause, neither has the child.
Here the side list is empty at the start, as in Appendix C, and the output at a leaf is the side
list followed by ψ, with every clause written once (`out`). As a set of clauses this is ψ ∪ 𝒩.
Everything in this file holds for arbitrary thresholds θ, or for all thresholds that satisfy the
four conditions `ThrC`. Two families used here satisfy them: θ 0 = 1, θ i = 4·τ^(2i−1), if 1 ≤ k and
8k ≤ τ
(proof/sparsification/UniformInK/Spars/Defs.lean; proof/sparsification/SparsificationLemma/Geo), and
the thresholds of Calabro's dissertation with any α ≥ 1
(proof/sparsification/SparsificationLemma/Cal).
This file has definitions only. The statements `St…` are propositions; they are proved in other
files. -/

@[expose] public section

namespace SparsificationLemma

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
open PaddedDescent.F.Mark (occ)

/-! ### Formulas and assignments -/

/-- ψ is a k-CNF on the variables x₀, …, xₙ₋₁: every clause is nonempty and has at most k literals. -/
def IsKCNF (k n : ℕ) (ψ : PFml) : Prop := ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n

/-- The assignment b satisfies ψ: it makes a literal of every clause true. -/
def Sat (b : ℕ → Bool) (ψ : PFml) : Prop := ∀ C ∈ ψ, ∃ l ∈ C, b l.1 = l.2

/-- If b satisfies ψ, it satisfies exactly one formula of the list Φ (exactly one position of the
list); otherwise it satisfies none. -/
def ExactlyOne (b : ℕ → Bool) (ψ : PFml) (Φ : List PFml) : Prop :=
  (Sat b ψ → ∃! i : Fin Φ.length, Sat b (Φ.get i)) ∧ (¬ Sat b ψ → ∀ Ψ ∈ Φ, ¬ Sat b Ψ)

/-- The number of clauses of ψ in which the variable v occurs. -/
def occN (ψ : PFml) (v : ℕ) : ℕ := (occ ψ v).length

/-- ψ without the clauses that contain a variable together with its negation. -/
def noTaut (ψ : PFml) : PFml := ψ.filter fun C => !(C.any fun l => C.contains (l.1, !l.2))

/-! ### The tree and the outputs -/

/-- The root: ψ without the clauses that contain another clause (`rootP` also writes every clause
once, with its literals in a fixed order and without repetitions), and the empty side list. -/
def root (ψ : PFml) : CNode := (rootP ψ, [])

/-- The leaves of the tree of the procedure with thresholds θ and width k, from left to right. Every
path is cut after D steps, whether or not the procedure has stopped there; `StGen` says that for D
large enough it has stopped everywhere. -/
def tree (θ : ℕ → ℕ) (k D : ℕ) (ψ : PFml) : List CNode := leaves (stepC θ k) D (root ψ)

/-- The output at a node: the side clauses of one literal and the clauses of the formula, every
clause written once. (`leafM` writes every side clause once; a clause of one literal can also stand
in the formula.) -/
def out (x : CNode) : PFml := (leafM x).dedup

/-- The outputs: at every leaf, the formula together with the side list. -/
def outputs (θ : ℕ → ℕ) (k D : ℕ) (ψ : PFml) : List PFml := (tree θ k D ψ).map out

/-! ### «Exactly one output», and further properties of the tree and the outputs -/

/-- Every assignment that satisfies ψ satisfies exactly one output, and every other assignment
satisfies none. This holds for all thresholds and wherever the paths are cut. -/
def StExactlyOne : Prop := ∀ (θ : ℕ → ℕ) (k D : ℕ) (ψ : PFml) (b : ℕ → Bool), ExactlyOne b ψ (outputs θ k D ψ)

/-- If every assignment satisfies exactly one formula of Φ or none, according to whether it
satisfies ψ, then the number of satisfying assignments of ψ on n variables is the sum of those of
the formulas of Φ. -/
def StCountOfExactlyOne : Prop := ∀ (n : ℕ) (ψ : PFml) (Φ : List PFml), (∀ b, ExactlyOne b ψ Φ) → cntN n ψ = (Φ.map (cntN n)).sum

/-- No choice depends on the side list: the tree that starts with the side list X has the same first
components, and X behind every side list. -/
def StSide : Prop := ∀ (θ : ℕ → ℕ) (k D : ℕ) (r X : PFml),
  leaves (stepC θ k) D (r, X) = (leaves (stepC θ k) D (r, [])).map fun x => (x.1, x.2 ++ X)

/-- The first components of the nodes are the nodes of the unchanged procedure `stepK`. -/
def StUnchanged : Prop := ∀ (θ : ℕ → ℕ) (k D : ℕ) (r X : PFml), (leaves (stepC θ k) D (r, X)).map Prod.fst = leaves (stepK θ k) D r

/-- The outputs are those of the tree of proof/consequences/CountKSat/Defs.lean, whose side list
starts with the n clauses xᵢ ∨ ¬xᵢ. -/
def StOutputsSame : Prop := ∀ (θ : ℕ → ℕ) (k D n : ℕ) (ψ : PFml),
  (leaves (stepC θ k) D (rootC (List.replicate n (), ψ))).map out = outputs θ k D ψ

/-- No output has a clause twice. -/
def StNodup : Prop := ∀ (θ : ℕ → ℕ) (k D : ℕ) (ψ : PFml), ∀ Φ ∈ outputs θ k D ψ, Φ.Nodup

/-- Since every clause has a variable, a k-CNF on n variables in which every variable occurs in at
most Δ clauses has at most Δ·n clauses. -/
def StLenOfOcc : Prop := ∀ (k n Δ : ℕ) (Φ : PFml), IsKCNF k n Φ → (∀ v, occN Φ v ≤ Δ) → Φ.length ≤ Δ * n

/-- Deleting the clauses that contain a variable together with its negation changes neither the
satisfying assignments nor the property of being a k-CNF, and afterwards no clause contains a
variable together with its negation. -/
def StNoTaut : Prop := ∀ ψ : PFml, (∀ b, Sat b (noTaut ψ) ↔ Sat b ψ) ∧ (∀ k n, IsKCNF k n ψ → IsKCNF k n (noTaut ψ)) ∧
  ∀ C ∈ noTaut ψ, ∀ l ∈ C, (l.1, !l.2) ∉ C

/-! ### The conditions on the thresholds, and the counts along a path -/

/-- What the counts need of thresholds θ and numbers β for width k. At most β i · n clauses of size
i < k are added along a path; a step that adds clauses E ∖ H of size r adds at least θ r ≥ τ · β r
of them.
It differs from `UniformInK.ThrU` at size 1 only, where it asks for 2 ≤ β 1: there are only 2n
clauses with one literal. -/
structure ThrC (k τ : ℕ) (θ β : ℕ → ℕ) : Prop where
  pos : ∀ i, 0 < θ i
  one : 2 ≤ β 1
  step : ∀ i, 2 ≤ i → i < k → 4 * θ (i - 1) + ∑ i' ∈ range i, 2 * θ (i - i') * β i' ≤ β i
  mul : ∀ r, τ * β r ≤ θ r

/-- The conditions `ThrU` together with 2 ≤ β 1 imply the conditions `ThrC`. -/
def StThrOfU : Prop := ∀ (k τ : ℕ) (θ β : ℕ → ℕ), 2 ≤ β 1 → ThrU k τ θ β → ThrC k τ θ β

/-- A path has at most (β 0 + … + β (k-1))·n steps, and its steps to a second child use at most
(k−1)·n units, τ each. U is a set of at most 2n literals that contains every clause of φ. -/
def StBoundC : Prop := ∀ (α : Type) [DecidableEq α] (θ β : ℕ → ℕ) (k τ n : ℕ) (φ F : Finset (Finset α)) (U : Finset α) (p t : ℕ),
  ThrC k τ θ β → U.card ≤ 2 * n → (∀ C ∈ φ, C ⊆ U) → NodeU θ k τ φ F p t → p ≤ (∑ i ∈ range k, β i) * n ∧ t ≤ (k - 1) * n

/-- All that the walk of the tree needs to know about the rule on finite sets, for thresholds with
`ThrC`. -/
def StIfaceC : Prop := ∀ (k τ n D : ℕ) (θ β : ℕ → ℕ), ThrC k τ θ β → (∑ i ∈ range k, β i) * n ≤ D →
  Iface θ k D ((k - 1) * n) τ ((2 * ∑ j ∈ range k, θ j) * n) (ProgMain.Ok k n) (fun F₀ F p t => ProgMain.Ok k n F₀ ∧ NodeU θ k τ F₀ F p t)

/-! ### The general theorem -/

/-- The sparsification for thresholds with `ThrC`, τ ≥ 1, and D ≥ (β 0 + … + β (k-1))·n. No path has
more than D steps (the procedure has stopped at every node of `tree`);
there are at most Σ_{j ≤ (k−1)n/τ} C(D, j) outputs; every output is a k-CNF on the same variables,
in which a variable occurs in at most 2·(θ 0 + … + θ (k-1)) + 2 clauses;
the formula at a node that is listed has at most as many clauses as ψ. -/
def StGen : Prop := ∀ (k τ n D : ℕ) (θ β : ℕ → ℕ), 1 ≤ k → 1 ≤ τ → ThrC k τ θ β → (∑ i ∈ range k, β i) * n ≤ D → ∀ ψ : PFml, IsKCNF k n ψ →
  (∀ x ∈ tree θ k D ψ, stepC θ k x = none) ∧
  (outputs θ k D ψ).length ≤ ∑ j ∈ range ((k - 1) * n / τ + 1), D.choose j ∧
  (∀ Φ ∈ outputs θ k D ψ, IsKCNF k n Φ ∧ ∀ v, occN Φ v ≤ 2 * (∑ j ∈ range k, θ j) + 2) ∧
  ∀ x ∈ tree θ k D ψ, x.1.length ≤ ψ.length

/-- What `UniformInK.StTreeU` says of the thresholds `thetaU τ`, for all thresholds with `ThrC` and
k² ≤ τ, with (k−1)·n in place of k·n. The identity of the counts is derived from `StExactlyOne`. -/
def StTreeG : Prop := ∀ (k τ n D : ℕ) (θ β : ℕ → ℕ), 1 ≤ k → k ^ 2 ≤ τ → ThrC k τ θ β → (∑ i ∈ range k, β i) * n ≤ D → ∀ ψ : PFml, IsKCNF k n ψ →
  (leaves (stepC θ k) D (rootC (List.replicate n (), ψ))).length ≤ ∑ j ∈ range ((k - 1) * n / τ + 1), D.choose j ∧
  (∀ x ∈ leaves (stepC θ k) D (rootC (List.replicate n (), ψ)),
    stepC θ k x = none ∧ (leafF x).length ≤ (2 * (∑ j ∈ range k, θ j) + 2) * n ∧
      (∀ C ∈ x.1, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ (∀ v, (occ x.1 v).length ≤ 2 * ∑ j ∈ range k, θ j) ∧
      ∀ C ∈ x.2, (C ∈ taut n ∨ ∃ l, C = [l]) ∧ ∀ l ∈ C, l.1 < n) ∧
  cntN n ψ = ((leaves (stepC θ k) D (rootC (List.replicate n (), ψ))).map fun x => cntN n (leafF x)).sum ∧
  ∀ i, ((round (stepC θ k))^[i] ([rootC (List.replicate n (), ψ)], [])).1.length ≤ D + 1 ∧
    ∀ x ∈ ((round (stepC θ k))^[i] ([rootC (List.replicate n (), ψ)], [])).1,
      x.1.length ≤ ψ.length * 2 ^ k ∧ x.2.length ≤ 2 * n ∧ (∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n

end SparsificationLemma
