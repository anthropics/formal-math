/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSatStatement
public import CountKSat.Defs
public import SparsifyWidthK.Interfaces
public import WidthK.Decode
public import StepMachines.Prog.Count
public import StepMachines.Prog.Decode
public import StepMachines.Prog.BruteE
public import StepMachines.Prog.NetProg
public import StepMachines.Prog.NetRun
public import StepMachines.Prog.NetVal
public import StepMachines.Math.RebalanceArith
public import StepMachines.Prog.GridLoop
public import StepMachines.Prog.SidePresents
public import StepMachines.Prog.Sat
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import StepMachines.Math.SparsifyCount
public import NetworkStatements
public import Mathlib.Algebra.Polynomial.Coeff
public import ToTuring.PolyT

/-! # The interface statements, as propositions

Every statement that one file needs from another is written here as a definition `St… : Prop`.
Nothing is proved and nothing is assumed: this file has no
theorem. One file proves `theorem … : St…`; a file that needs the statement takes `(h : St…)` as a
hypothesis. -/

@[expose] public section

namespace CountKSat

open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog

/-! ### The input and the output -/

/-- The input as (n in unary, formula). -/
def decU (k : ℕ) (x : List Bool) : List Unit × Fml := (List.replicate (x.takeWhile id).length (), (DecodeK.decK k x).2)

/-- `decU` reads the code of a formula with at most k literals per clause, k ≥ 1. -/
def StDecU : Prop := ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → (∀ C ∈ φ, C.length ≤ k) →
  decU k (SatK.enc k φ) = (List.replicate n (), Decode.toN φ)

/-- `decU` is polynomial-time. -/
def StCertDecU : Prop := ∀ k : ℕ, PolyT (decU k)

/-- The formula read with natural numbers as variables has the same count. -/
def StCntToN : Prop := ∀ (n : ℕ) (φ : Sat3.CNF n), cntN n (Decode.toN φ) = SatK.numSat φ

/-! ### One sparse formula -/

/-- A correct evaluator of networks, run on `satP g k`, returns the value of the network
of φ in at most A·2^{δm} steps, m the number of clauses, and within size A·(size φ)^A. -/
def StCountValue : Prop := ∀ (g K k : ℕ) (δ b : ℝ) (NE : NetEvaluator), 0 < δ → δ ≤ 1 → 1 ≤ k → 0 < g → 0 ≤ b → 8 * b * k / δ ≤ K →
  NE.Correct g K (δ / (8 * k)) b →
  ∃ A : ℕ, ∀ φ : Fml, (∀ C ∈ φ, C.length ≤ k) →
    ∃ T : ℕ, (NE.app (satP g k)).Runs φ T (A * size φ ^ A) (Count.wordNet g k φ).value ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ * φ.length)

/-! ### The tree -/

/-- The satisfying assignments of a node are those of its two children, and no assignment satisfies
both: the counts add up. -/
def StStepCount : Prop := ∀ (θ : ℕ → ℕ) (k n : ℕ) (x l h : CNode), stepC θ k x = some (l, h) →
  cntN n (leafF x) = cntN n (leafF l) + cntN n (leafF h)

/-- The root has the count of the formula. -/
def StRootCount : Prop := ∀ (n : ℕ) (ψ : Fml), cntN n (leafF (rootC (List.replicate n (), ψ))) = cntN n ψ

/-- A quantity that is the sum of its values at the two children, at every node with the invariant
G, is the sum of its values at the leaves. -/
def StSumLeaves : Prop := ∀ (σ : Type) (step : σ → Option (σ × σ)) (G : σ → ℕ → ℕ → Prop) (q : ℕ),
  (∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q)) → ∀ f : σ → ℕ,
  (∀ s p t l h, G s p t → step s = some (l, h) → f s = f l + f h) →
  ∀ (d : ℕ) (s : σ) (p t : ℕ), G s p t → f s = ((leaves step d s).map f).sum

/-- `step` (with `rootC`) sparsifies width k for counting. ψ has variables below n and nonempty
clauses of at most k literals. The tree of depth Dd·n has at most 2^{εn}
leaves. The formula of a leaf has at most Bl·n clauses of at most max k 2 literals, and exactly the
variables below n occur in it. The counts of the leaves add up to the
count of ψ. The stack of the walk never holds more than Dd·n + 1 nodes, each with at most (|ψ| +
n)·Sk clauses. -/
def SparsifiesC (k : ℕ) (ε : ℝ) (step : CNode → Option (CNode × CNode)) (Dd Bl Sk : ℕ) : Prop :=
  ∀ (n : ℕ) (ψ : Fml), (∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) →
    ((leaves step (Dd * n) (rootC (List.replicate n (), ψ))).length : ℝ) ≤ (2 : ℝ) ^ (ε * n) ∧
    (∀ x ∈ leaves step (Dd * n) (rootC (List.replicate n (), ψ)), step x = none ∧ (leafF x).length ≤ Bl * n ∧
      (∀ C ∈ leafF x, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ i < n, ∃ C ∈ leafF x, ∃ l ∈ C, l.1 = i) ∧
    cntN n ψ = ((leaves step (Dd * n) (rootC (List.replicate n (), ψ))).map fun x => cntN n (leafF x)).sum ∧
    ∀ i, ((round step)^[i] ([rootC (List.replicate n (), ψ)], [])).1.length ≤ Dd * n + 1 ∧
      ∀ x ∈ ((round step)^[i] ([rootC (List.replicate n (), ψ)], [])).1, (leafF x).length ≤ (ψ.length + n) * Sk ∧
        ∀ C ∈ leafF x, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n

/-- The sparsification lemma for counting: `stepC` with the thresholds `theta τ` sparsifies width k
for counting, with a tree of depth bsum τ k · n, and at
most 2^{εn} leaves if (k/τ)·log₂(e·τ·bsum τ k) ≤ ε. -/
def StProgC : Prop := ∀ (τ k : ℕ) (ε : ℝ), 1 ≤ τ → ((k : ℝ) / τ) * Real.logb 2 (Real.exp 1 * τ * bsum τ k) ≤ ε →
  SparsifiesC k ε (stepC (theta τ) k) (bsum τ k) (leafC τ k + k * bsum τ k + 1) (2 ^ k + k * bsum τ k + 1)

/-- One step of the counting tree is computed in polynomial time. -/
def StCertStepC : Prop := ∀ (θ : ℕ → ℕ) (k : ℕ), PolyT (stepC θ k)

/-! ### The machine -/

/-- If T takes t steps on each leaf and the sum over the leaves is below 2^B, the summing walk takes
t + 2 steps per leaf and returns that sum. -/
def StWalkSum : Prop := ∀ (α ν : Type) [HasSize ν] (step : ν → Option (ν × ν)) (root : α → ν) (T : Stepped ν ℕ) (d : ℕ) (a : α),
  (∀ x ∈ leaves step d (root a), step x = none) → ∀ (v : ν → ℕ) (t Sm Sx B : ℕ),
  (∀ x ∈ leaves step d (root a), T.Runs x t Sm (v x)) → (∀ i, size ((round step)^[i] ([root a], [])).1 ≤ Sx) →
  ((leaves step d (root a)).map v).sum < 2 ^ B →
  (walkSum step root T).Runs a ((leaves step d (root a)).length * (t + 2)) (Sx + (B + 1 + (Sm + 1)) + 1) ((leaves step d (root a)).map v).sum

/-- The host for a word as output. A stepped computation M from bit strings to bit strings with
polynomial-time init, step and out runs on one multi-stack machine N of
Mathlib with finite alphabets. There is one number q such that, whenever M ends on x with the word w
within T steps and with all states of size at most S, the
machine N started on x halts with output w within q·(T + 1)·(|x| + S + 1)^q steps. -/
def StHostW : Prop := ∀ (M : Stepped (List Bool) (List Bool)) [IsPolyT M],
  ∃ (N : Turing.TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧
    ∀ (x : List Bool) (T S : ℕ) (w : List Bool), M.Runs x T S w →
      Nonempty (Turing.TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun) (some (w.map N.outputAlphabet.invFun))
        (q * (T + 1) * (x.length + S + 1) ^ q))

end CountKSat
