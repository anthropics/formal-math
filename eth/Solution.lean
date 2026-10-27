/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import MainResults
import CountedRoute.Main
import NamesInOrder.Main
import Wrap.Main

/-! The proofs of the theorems of `Challenge.lean`, the two propositions of `MainResults.lean`, from
Theorem A (b) with its operations counted.
* `mainTheorem` is `CountedRoute.mainTheoremHolds`: the chain in proof/maintheorem/CountedRoute that
  follows the order of the paper's proof, with the differences listed at the head of the index of
  the paper's statements, started from the machine of Theorem A (b) with query access to the tables,
  on the pieces of Appendix B, whose operations and queries are counted
  (`ExplicitCost.cliqueMachine`). Here an operation is one query or one step of the machine; a step
  may be any computation that takes time polynomial in the size of the machine's state, and the
  states are bounded only by the bound on the operations. From the hypothesis of Theorem D (a) on,
  the proofs measure cost as the length of a string of blank symbols that is given with the input as
  a budget of time. The proposition unfolds to `MainTheoremForms.MainTheoremAllOccur` of
  `MainTheoremFormsStatement.lean`, and Lean accepts the term below by unfolding definitions.
* `ethIsFalse` is proved from that proof of the Main Theorem, by two arguments, each proved for
  every machine that has the bound it starts from: `NamesInOrder.generalFormFollowsAsPropositions`
  (a front end that renames the variables that occur gives the form with any names and an added
  polynomial) and `Wrap.countingBoundImpliesFailureOfETH` (a front end, a simulation and a last step
  give one machine that decides 3-SAT within c·2^{δn}
  steps for every δ > 0).
These notions of cost live only inside the proof: the types of the two theorems below count steps of
one of Mathlib's Turing machines, and Lean's kernel checks the proofs against these types, so no
convention inside the proof can weaken what is stated. Inside the proof one operation may cost time
polynomial in the bound on the operations, so in steps of a Turing machine the exponent e_ℓK_ℓ²λ
holds only up to a constant factor, which the O in the conclusion of Theorem D (a) absorbs. In the
term for `ethIsFalse`, `.2.2.1` picks the third of the five statements of
`Wrap.OneMachineEveryDeltaAndETHFails`, `¬ Sat3.ETH_TM`, which unfolds to `MainResults.ETHIsFalse`. -/

/-- The Exponential Time Hypothesis is false; no hypothesis. It is drawn from the Main Theorem as
proved below, by two arguments, each proved for every machine that has the bound it starts from
(`NamesInOrder.generalFormFollowsAsPropositions`, `Wrap.countingBoundImpliesFailureOfETH`). -/
theorem MainResults.ethIsFalse : MainResults.ETHIsFalse := (Wrap.countingBoundImpliesFailureOfETH (NamesInOrder.generalFormFollowsAsPropositions CountedRoute.mainTheoremHolds)).2.2.1

/-- The Main Theorem; no hypothesis. It is `CountedRoute.mainTheoremHolds`, by unfolding
definitions. -/
theorem MainResults.mainTheorem : MainResults.MainTheorem := CountedRoute.mainTheoremHolds
