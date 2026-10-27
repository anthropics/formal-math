/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.Stepped
public import StepMachines.Prog.Range
public import StepMachines.Prog.Chunks
public import StepMachines.Prog.Brute
public import Groundwork.Net.Net
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The interfaces of the programs in this folder. States and labels are words (List Bool) of
prescribed lengths; the default
word (the label at the node itself, the entries of a tuple off its index set) is []. Lengths are
plain functions of the
context c : C. (For each step to take time polynomial in the input, the context must hold these
lengths in unary; nothing here needs that.)

* an instance of the problem on a clique (K nodes, a λ-bit label on every edge, an integer tensor at
  every node)
given by a procedure that answers queries for tensor entries, and what an evaluator of instances
must do: compute Z in
about 2^{εK²λ} steps (ε = 1/2 is brute force);
* a network (`Network`: nodes with states and integer weights, for every pair of nodes an
  interaction that factors
through labels) given by procedures, and what an evaluator of networks must do: the rebalancing of a
network on g nodes into K groups. -/

namespace Groundwork.Prog

open Finset

/-! ### Instances given by a procedure -/

/-- A query to an instance: the node v and the list (θ_u), u = 0, …, K-1, of the labels of the edges
{v,u} ([] at u = v). -/
public abbrev IQ : Type := ℕ × List (List Bool)

/-- In the context c the procedure R presents the instance Rm on K nodes with ℓ-bit labels: every
well-formed query (a label of
ℓ bits for each other node, [] at the node itself) is answered within t steps and size S, and the
entry of Rm at such a query is
at most 2^B in absolute value. Nothing is asked at other arguments. -/
@[expose] public def ServesInst {C : Type} (R : Stepped (C × IQ) ℤ) (c : C) {K : ℕ} (ℓ B t S : ℕ)
    (Rm : Inst (Fin K) (List Bool)) : Prop :=
  ∀ (v : Fin K) (θ : Fin K → List Bool), (∀ u, u ≠ v → (θ u).length = ℓ) → θ v = [] →
    R.Runs (c, v.1, List.ofFn θ) t S (Rm v θ) ∧ |Rm v θ| ≤ 2 ^ B

/-- An algorithm for instances: from the length function lam and a procedure R (any type of
contexts) a computation
on contexts. -/
public structure Evaluator : Type 2 where
  app : {C : Type} → [HasSize C] → (C → ℕ) → Stepped (C × IQ) ℤ → Stepped C ℤ

/-- E solves the problem on a clique with K nodes with exponent ε: Z within A·2^{εK²λ}·(B+λ)^A·t
steps, in size
S + polynomial (ε = 1/2 is brute force). -/
@[expose] public def Evaluator.Correct (E : Evaluator) (K : ℕ) (ε : ℝ) : Prop :=
  ∃ A : ℕ, ∀ (C : Type) [HasSize C] (lam : C → ℕ) (R : Stepped (C × IQ) ℤ) (c : C) (B t S : ℕ)
    (Rm : Inst (Fin K) (List Bool)), 1 ≤ lam c → 1 ≤ t → ServesInst R c (lam c) B t S Rm →
    ∃ T : ℕ, (E.app lam R).Runs c T (S + A * (size c + B + lam c) ^ A) (Inst.ZW (lam c) [] Rm) ∧
      (T : ℝ) ≤ A * (2 : ℝ) ^ (ε * (K : ℝ) ^ 2 * lam c) * ((B : ℝ) + lam c) ^ A * t

/-! ### Networks given by procedures -/

/-- A query for a weight: (a, z). -/
public abbrev WQ : Type := ℕ × List Bool

/-- A query for a factor: ((a, b), (z, θ)) asks for f_ab(z,θ). -/
public abbrev FQ : Type := (ℕ × ℕ) × (List Bool × List Bool)

/-- A network given by procedures: n c a is the length of the states of a, cap c a b the length of
the labels of {a,b}. -/
public structure PNet (C : Type) : Type 1 where
  n : C → ℕ → ℕ
  cap : C → ℕ → ℕ → ℕ
  W : Stepped (C × WQ) ℤ
  f : Stepped (C × FQ) ℤ

/-- In the context c the procedures present the network N on Fin g; every answer within t steps and
size S. -/
public structure PNet.Presents {C : Type} (Np : PNet C) (c : C) {g : ℕ} (N : Network (Fin g) (List Bool) (List Bool))
    (t S : ℕ) : Prop where
  S_eq : ∀ a : Fin g, N.S a = words (Np.n c a)
  c_eq : ∀ a b : Fin g, a ≠ b → N.c a b = Np.cap c a b
  lab_eq : ∀ a b : Fin g, a ≠ b → N.lab a b = words (Np.cap c a b)
  W_runs : ∀ (a : Fin g) (z : List Bool), z.length = Np.n c a → Np.W.Runs (c, (a.val, z)) t S (N.W a z)
  f_runs : ∀ (a b : Fin g) (z θ : List Bool), a ≠ b → z.length = Np.n c a → θ.length = Np.cap c a b →
    Np.f.Runs (c, ((a.val, b.val), (z, θ))) t S (N.f a b z θ)

/-- An algorithm for networks: from procedures (any type of contexts) a computation on contexts. -/
public structure NetEvaluator : Type 2 where
  app : {C : Type} → [HasSize C] → PNet C → Stepped C ℤ

/-- NE does the rebalancing of a network into K groups: the value of every network on Fin g of size
P (at most 2^P states and at
most P label bits at a node) within A·2^{εU + b·gP/K}·(P+B)^A·t steps; U is the sum of the label
lengths over ordered
pairs. -/
@[expose] public def NetEvaluator.Correct (NE : NetEvaluator) (g K : ℕ) (ε b : ℝ) : Prop :=
  ∃ A : ℕ, ∀ (C : Type) [HasSize C] (Np : PNet C) (c : C) (N : Network (Fin g) (List Bool) (List Bool))
    (P B t S : ℕ), 1 ≤ P → 1 ≤ t → Np.Presents c N t S → N.Sized P B →
    ∃ T : ℕ, (NE.app Np).Runs c T (S + A * (size c + P + B) ^ A) N.value ∧
      (T : ℝ) ≤ A * (2 : ℝ) ^ (ε * (N.U : ℝ) + b * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ A * t

end Groundwork.Prog
