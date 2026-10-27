/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Printed.TiedDefs
public import StepSparsify.Defs

/-! # The sparsification with a family of thresholds, among them those that Step 5 names, and the count of each output by Steps 1 to 4 as printed, in one function: definitions and statements

Two proofs of the bound for all widths k stand side by side. In proof/variables/VariableBound each
sparse formula is counted by `VariableBound.countD`, Steps 1 to 4 of Appendix D as printed, but the
sparsification uses the thresholds θ 0 = 1,
θ i = 4·τ^(2i−1) of proof/sparsification/UniformInK. In proof/sparsification/StepSparsify the
sparsification works with any family Θ of thresholds that serves (`StepSparsify.Serves`), among them
the thresholds of Calabro that Step 5 names (`StepSparsify.thCal`, which serve), after deleting
the clauses that contain a variable together with its negation, but each output is counted by a
variant of Steps 1 to 4 not in the paper. Here `ABDG Θ` sparsifies as
proof/sparsification/StepSparsify does and counts as proof/variables/VariableBound does.

* The thresholds are the only parameter that proof/variables/VariableBound does not have. The walk
  `StepSparsify.walkSG` takes the function that counts a leaf as an argument; it gets
  `VariableBound.valD`, which is `VariableBound.countD` on the formula of the leaf.
* The plan with its tests, the exponent functions `VariableBound.eD` and `VariableBound.eBD`, the
  choice `VariableBound.useMD` between the two algorithms, and the whole arithmetic do not know the
  thresholds. They are those of proof/variables/VariableBound.

**What `AlgDG` says and does not say.** It fixes the function computed on every input, not the steps
of a machine. On the code of a formula, with a pad that is long enough, `ABDG Θ …` has the same
value, the
number of satisfying assignments, for every family Θ that serves. `AlgDG` ties the bounds to this
function: the function and `eBD` are polynomial-time, the function is right when the pad has at
least 2^(`eBD`) units, and a machine that writes a pad of that length and then applies the function
is within the bounds.
**What differs from the printed Steps 5 and 6.**
* The range of k: three computed tests (`VariableBound.planAtD`: s ≥ s0U k, 2^β ≤ n + 1, n ≥
  29·⌈log₂(2·2^β)⌉ + 19), and the test that the computed exponent is at most n, in place of 3 ≤ k ≤
  (log n)^(1/4) and n ≥ n₀, and exhaustive counting where a test fails.
* ε = 2^(−s), a power of two with 2^(−s) ≤ e, in place of a number between e and 2e.
* Δ = 2^β with β = 2k(4s+17), cut off at n + 1, for all outputs, in place of the largest number of
  clauses of the output in which one variable occurs.
* The width is the one declared in the input, cut off as `UniformInK.kcU` says, not the largest
  number of literals in a clause; α alone is taken for max(k, 3).
* The side list of the walk starts with the n clauses xᵢ ∨ ¬xᵢ, which the count of a leaf leaves out
  again (see proof/sparsification/StepSparsify/Defs.lean).
* The cost is counted through a pad: a function that is polynomial-time in the input and a pad of
  2^(exponent) units, run by a padding machine.
This file has definitions only. The statements `St…` are propositions. -/

@[expose] public section

namespace SparsifyThenCount

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN UniformInK VariableBound VariableBound.Decide

/-! ### The functions -/

section
variable (Θ : ℕ → ℕ → ℕ → ℕ) {Idx : Type} [Enc Idx] (S : Solver Idx)

/-- The walk, with the thresholds Θ k s, through the counting tree of the decoded formula d = (n in
unary, clauses) without the clauses that contain a variable together with its negation; every leaf
is counted by `VariableBound.valD`, that is by
Steps 1 to 4; 0 if d has an empty clause. -/
def numDG (k : ℕ) (i : Idx) (s : ℕ) (d : U × Fml) (pad : U) : ℕ :=
  bif hasNil d.2 then 0 else StepSparsify.walkSG (Θ k s) k pad (valD S k pad i d.1.length s) (rootC (d.1, SparsificationLemma.noTaut d.2))

/-- The algorithm for the bound in n: exhaustive counting where `planD` finds no plan, and `numDG`
elsewhere. -/
def ADG (pick : U → U × Idx) (slU : U → U) (p : List Bool × U) : List Bool :=
  outW (fmlOf p.1, bif (planD S pick slU p.1).isNone then bruteU p
    else numDG Θ S (kcU (kU p.1) (nU p.1)) (idxU pick p.1) (precU pick slU p.1) (fmlOf p.1) p.2)

/-- The merged function: the algorithm for the bound in m where `VariableBound.useMD` holds, the
algorithm for the bound in n elsewhere. -/
def ABDG (pick : U → U × Idx) (slU : U → U) (p : List Bool × U) : List Bool :=
  bif useMD S pick slU p.1 then AM S pick p else ADG Θ S pick slU p

end

/-! ### The statements on the parts -/

/-- A number F ≥ 2^(`VariableBound.restD` k K n s) suffices for the rounds of the walk:
2·2^(⌊n/2^s⌋+1) ≤ F + 1. -/
def StRoundsDG : Prop := ∀ k K n s F : ℕ, 2 ^ restD k K n s ≤ F → 2 * 2 ^ (n / 2 ^ s + 1) ≤ F + 1

/-- For thresholds that serve and a polynomial-time solver with a sequence of levels: the algorithm
for the bound in n is right on every k-CNF, for every k ≥ 1 and every n, when the pad has length at
least 2^(`VariableBound.eD` …). -/
def StCorrectDG : Prop := ∀ (Θ : ℕ → ℕ → ℕ → ℕ) (Lc : ℕ → ℕ → ℕ), StepSparsify.Serves Θ Lc →
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (slU : U → U) (k n : ℕ) (φ : Sat3.CNF n),
  1 ≤ k → SatK.IsKCNF k φ → ∀ pad : U, 2 ^ eD S Q.pick slU (SatM.enc k φ) ≤ pad.length →
  ADG Θ S Q.pick slU (SatM.enc k φ, pad) = SatK.binary n (SatK.numSat φ)

/-- For thresholds that serve and a polynomial-time solver with a sequence of levels: the merged
function is right on every k-CNF, for every k ≥ 1 and every n, when the pad has length at least
2^(`VariableBound.eBD` …). -/
def StCorrectBDG : Prop := ∀ (Θ : ℕ → ℕ → ℕ → ℕ) (Lc : ℕ → ℕ → ℕ), StepSparsify.Serves Θ Lc →
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (slU : U → U) (k n : ℕ) (φ : Sat3.CNF n),
  1 ≤ k → SatK.IsKCNF k φ → ∀ pad : U, 2 ^ eBD S Q.pick slU (SatM.enc k φ) ≤ pad.length →
  ABDG Θ S Q.pick slU (SatM.enc k φ, pad) = SatK.binary n (SatK.numSat φ)

/-- For thresholds that serve: the algorithm for the bound in n is polynomial-time, if the solver,
`pick` and `slU` are. -/
def StCertDG : Prop := ∀ (Θ : ℕ → ℕ → ℕ → ℕ) (Lc : ℕ → ℕ → ℕ), StepSparsify.Serves Θ Lc →
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly → ∀ (pick : U → U × Idx) (slU : U → U), PolyT pick → PolyT slU → PolyT (ADG Θ S pick slU)

/-- For thresholds that serve: the merged function and the exponent function `VariableBound.eBD` are
polynomial-time, if the solver, `pick` and `slU` are. -/
def StCertBDG : Prop := ∀ (Θ : ℕ → ℕ → ℕ → ℕ) (Lc : ℕ → ℕ → ℕ), StepSparsify.Serves Θ Lc →
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly → ∀ (pick : U → U × Idx) (slU : U → U), PolyT pick → PolyT slU →
  PolyT (ABDG Θ S pick slU) ∧ PolyT (eBD S pick slU)

/-! ### The merged function as an algorithm -/

/-- The merged function with the thresholds Θ and the exponent function `VariableBound.eBD` are an
algorithm for the rates rn and rm, in the sense of `VariableBound.Decide.Alg`. -/
def AlgDG (Θ : ℕ → ℕ → ℕ → ℕ) {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (slU : U → U) (rn rm : ℕ → ℝ) : Prop :=
  Alg rn rm (ABDG Θ S pick slU) (eBD S pick slU)

/-- For every solver with a sequence of levels, under the hypotheses that `StEndS` fixes: the merged
function with the thresholds Θ and its exponent function are an algorithm for the two rates. -/
def StAlgSG (Θ : ℕ → ℕ → ℕ → ℕ) : Prop := StEndS fun _ _ S pick slU rn rm => AlgDG Θ S pick slU rn rm

end SparsifyThenCount
