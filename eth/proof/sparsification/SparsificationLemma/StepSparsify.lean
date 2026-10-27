/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.StepSparsifyDefs
import SparsificationLemma.Nodes
import SparsificationLemma.One
import SparsificationLemma.Side
import SparsificationLemma.Len
import SparsificationLemma.Cal.Main
import SparsificationLemma.Cal.Alpha
import SparsificationLemma.Cal.Real
import SparsificationLemma.Cal.Beta
import SparsificationLemma.Cal.Facts
import SparsificationLemma.Cal.Thr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Step 5 of Appendix D («sparsification»)

Theorems for some sentences of Step 5 of Appendix D of the paper on the sparsification (the number
of outputs, exactly one output for each satisfying assignment, counting), in the order of the text;
each docstring quotes its sentence.
Where a theorem needs them, k ≥ 3, ε is a rational number in (0,1] and φ is a k-CNF on n variables.
The thresholds are Calabro's (proof/sparsification/SparsificationLemma/Cal/Defs.lean): α =
`alphaC k ε`, θ = `thetaC α`; paths are cut after `depthC α k n` steps.
The procedure runs on φ without the clauses that contain a variable together with its negation
(`noTaut φ`), and `Cal.sparsify` lists the outputs, one for each leaf of its tree of recursive
calls.
**Where Lean differs from the text.** The text has α = 2(k−1)²ε⁻¹·log₂ x with x = 32(k−1)²/ε, a real
number. Thresholds have to be integers, so Lean has α = ⌈2(k−1)²ε⁻¹·⌈log₂ x⌉⌉; all bounds of
the text hold for it. The text cites Calabro's dissertation for the number of leaves and for the
number of occurrences of a literal; the bounds on the number of outputs and on the occurrences of a
variable that rest on these are proved here.
The first sentence, «The change made in Appendix C … uses nothing about clauses of 3 literals», has
no theorem of its own: the statements on the change (`StExactlyOne`, `StSide`, `StUnchanged`;
proof/sparsification/SparsificationLemma/Defs.lean) hold for every width k.
**Not here.** The running time («in time 2^(εn)·n^(O(k))», «the work at a node … is polynomial») is
the subject of proof/sparsification/SparsificationLemma/Mach. The sentences on the choice of ε and
on the total time of Appendix D are not about the sparsification.
Most theorems are corollaries of `sparsABC` (the statement `Cal.SparsABC`). -/

public section

namespace SparsificationLemma.StepSparsify

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate SparsificationLemma.Cal

/-! ### The theorem that most sentences come from -/

/-- The theorem on sparsification with Calabro's thresholds (`Cal.SparsABC`): the outputs are k-CNFs
on the same variables without a repeated clause, there are at most 2^(εn) of them, every satisfying
assignment of φ satisfies exactly one and
no other assignment satisfies any, and in each of them every variable occurs in at most
2·(8k/ε)^(3k) + 2 clauses. -/
theorem sparsABC : SparsABC := Cal.sparsABC stNodup stAlpha stYLe stDegLe

variable {k n : ℕ} {ε : ℚ} {φ : PFml}

/-- α ≥ 1. -/
theorem one_le_alpha (hk : 3 ≤ k) (h0 : 0 < ε) (h1 : ε ≤ 1) : 1 ≤ alphaC k ε := by
  have := (stAlpha k ε hk h0 h1).2.1
  omega

/-! ### The number of outputs -/

/-- «Applied to a k-CNF on n variables and ε ∈ (0,1], the changed algorithm produces at most 2^(εn)
outputs …»; the time is in proof/sparsification/SparsificationLemma/Mach. -/
theorem outputs_le (hk : 3 ≤ k) (h0 : 0 < ε) (h1 : ε ≤ 1) (hφ : IsKCNF k n φ) : ((sparsify k n ε φ).length : ℝ) ≤ (2 : ℝ) ^ ((ε : ℝ) * (n : ℝ)) :=
  (sparsABC k n ε φ hk h0 h1 hφ).2.1

/-! ### The formula at a node -/

/-- «(2n+1)^k ≤ n^(2k)», for n ≥ 3. -/
theorem pow_le (hn : 3 ≤ n) (k : ℕ) : (2 * n + 1) ^ k ≤ n ^ (2 * k) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (by nlinarith) k

/-! ### The outputs -/

/-- «Each satisfying assignment of the input satisfies exactly one output, and no other assignment
satisfies any.» -/
theorem exactly_one (hk : 3 ≤ k) (h0 : 0 < ε) (h1 : ε ≤ 1) (hφ : IsKCNF k n φ) : ∀ b, ExactlyOne b φ (sparsify k n ε φ) :=
  (sparsABC k n ε φ hk h0 h1 hφ).2.2.1

/-! ### Counting -/

/-- «An output without clauses counts 2^n.» -/
theorem count_no_clause (n : ℕ) : cntN n [] = 2 ^ n := cntN_nil n

/-- «Run Steps 2–4 on each of the … outputs and add the results»: the number of satisfying
assignments of φ is the sum of those of the outputs. -/
theorem count_eq_sum (hk : 3 ≤ k) (h0 : 0 < ε) (h1 : ε ≤ 1) (hφ : IsKCNF k n φ) : cntN n φ = ((sparsify k n ε φ).map (cntN n)).sum :=
  stCountOfExactlyOne n φ _ (exactly_one hk h0 h1 hφ)

end SparsificationLemma.StepSparsify
