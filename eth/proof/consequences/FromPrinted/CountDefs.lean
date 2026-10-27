/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SplitCount.Defs
public import Printed.Programs

/-! # Section 7, Corollary 6 (#k-SAT in time O(2^{δn})) along its printed proof, on the machines of proof/threesat/Printed/: the machine and the statements (no proofs)

proof/consequences/SplitCount/Defs.lean states the four steps of the printed proof of Corollary 6.
Most of it has the machine that computes Z as a parameter: `timesFreeAfter Cnt`, `engineBy step D`,
`ComputesZ`, `CountsThree`, `StStepOneFor`, `StStepTwo`, `StStepThree`, `StSuffices`, `StCert`,
`deltaPrime`. Those are used here as they stand. A machine of the main text is named there in
`countThree` (`Eight.ViaGrouping.COUNTp ℓ`), so in `engineSplit`, `ENGINEsplit`, `COUNTsplit` and
the statements on them, and in `StComputesZ`, `StCountIsNetworkMachine`,
`StCountsWithAnyCliqueAlgorithm` (`Eight.ViaGrouping.netAlg`, `Eight.ViaGrouping.CLIQUEp`,
`Paper.CliqueAlgorithm`).
This file states those definitions and statements for another machine, under the same short names,
with `Printed.COUNT ℓ` in the place of `Eight.ViaGrouping.COUNTp ℓ`: COUNT of Algorithm 1 in the
form that the file proof/threesat/Printed/Programs.lean builds, from machines with query access to
the tables of a clique, for which «achievable» is `Printed.Achievable`: Definition 4 in the paper's
unit of cost (a table query costs one operation), with a bound on memory added. Nothing else is
changed, but for two things.
* In the place of «any algorithm E for cliques with `E.Within K (δ'/12)`» stands «any machine M with
  query access to the tables with `Printed.AchievedBy M Cc K (δ'/12)`» (what
  `Printed.Achievable K (δ'/12)` asks of a machine, but for polynomial-time steps), and in the place
  of `(netAlg K g E).app (satProcs g 3)` the machine of the proof of Lemma 1 made from M, with its
  queries answered by the procedures of the network of Φ
  (`Printed.networkOnSteps g (Printed.groupingMachine K g M) (Printed.formulaProcs g 3)`).
* `Printed.COUNT ℓ` begins with line 6 of Algorithm 1, «if m = 0 then return 1», which
  `Eight.ViaGrouping.COUNTp ℓ` does not have: `withFirstLine`, `StFirstLine`.
What differs from the paper is said at the heads of proof/consequences/SplitCount/Defs.lean (the
route of Corollary 6) and of proof/threesat/Printed/Programs.lean and PrintedStatement.lean (the
machines and Definition 4).
This file has no theorem. -/

@[expose] public section

open SplitCount

namespace FromPrinted.SplitCount

open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog Paper CountKSat GraphProblems Eight Eight.ViaGrouping Eight.Width Occ

/-! ### The machine -/

/-- Step 1 with COUNT of Algorithm 1 at level ℓ. -/
def countThree (ℓ : ℕ) : StepMachine (List Unit × Fml) ℕ := timesFreeAfter (Printed.COUNT ℓ)

/-- The procedure with COUNT of Algorithm 1 at level ℓ. -/
def engineSplit (step : CNode → Option (CNode × CNode)) (ℓ : ℕ) : StepMachine (List Unit × Fml) (List Bool) := engineBy step (countThree ℓ)

/-- The procedure at width k, level ℓ, threshold parameter τ of the sparsification. -/
def ENGINEsplit (k ℓ τ : ℕ) : StepMachine (List Unit × Fml) (List Bool) := engineSplit (stepC (WidthK.theta τ) k) ℓ

/-- The machine for #k-SAT: the reader of the input, then the procedure. -/
def COUNTsplit (k ℓ τ : ℕ) : StepMachine (List Bool) (List Bool) := Stepped.mapIn (decU k) (ENGINEsplit k ℓ τ)

/-! ### Step 1 -/

/-- **The proof of Theorem 2, with K and g chosen from δ' as there, computes Z, in the form of
Section 6.** Let 0 < δ' ≤ 1, let K ≥ 2 with K ≥ 72/δ', let M be ANY machine for cliques on K nodes,
with query access to the tables, with `Printed.AchievedBy M Cc K (δ' / 12)` (Definition 4 in the
paper's unit of cost (a table query costs one operation), with a bound on memory added, for (K,
δ'/12) with the constant Cc; «(K, δ'/12) is achievable», `Printed.Achievable`, asks besides that the
steps of M are polynomial time, which this statement does not need), and g = 3K⁸. The algorithm of
the printed proof of Lemma 1 with M, run on the network of Φ on g clusters, computes Z as Section 6
says.
It follows from `Printed.stGroupingTied`, `Printed.onFormula` and `Printed.cost_of_bound`. -/
def StComputesZ : Prop := ∀ (δ' : ℝ), 0 < δ' → δ' ≤ 1 → ∀ (K : ℕ) (M : Printed.CliqueMachine) (Cc : ℕ), 2 ≤ K → 72 / δ' ≤ K → Printed.AchievedBy M Cc K (δ' / 12) →
  ∃ A : ℕ, ComputesZ (Printed.networkOnSteps (3 * K ^ 8) (Printed.groupingMachine K (3 * K ^ 8) M) (Printed.formulaProcs (3 * K ^ 8) 3)) δ' A

/-- Line 6 of Algorithm 1, «if m = 0 then return 1», in front of a machine Cnt. -/
def withFirstLine (Cnt : StepMachine Fml ℤ) : StepMachine Fml ℤ := Stepped.ite (fun Φ : Fml => Φ.isEmpty) (Stepped.const 1) Cnt

/-- **«if m = 0 then return 1».** If Cnt computes Z as Section 6 says, then so does Cnt with line 6
of Algorithm 1 in front of it, with the same exponent. It follows from
`Printed.cost_with_first_line`. -/
def StFirstLine : Prop := ∀ (Cnt : StepMachine Fml ℤ) (δ' : ℝ) (A : ℕ), ComputesZ Cnt δ' A → ∃ A' : ℕ, ComputesZ (withFirstLine Cnt) δ' A'

/-- COUNT of Algorithm 1 at level ℓ is line 6 in front of the machine of `StComputesZ` at K = K_ℓ
and M = CLIQUE(ℓ). (By unfolding definitions.) -/
def StCountIsNetworkMachine : Prop := ∀ ℓ : ℕ, Printed.COUNT ℓ = withFirstLine (Printed.networkOnSteps (3 * levelK ℓ ^ 8) (Printed.groupingMachine (levelK ℓ) (3 * levelK ℓ ^ 8) (Printed.CLIQUE ℓ)) (Printed.formulaProcs (3 * levelK ℓ ^ 8) 3))

/-- **Step 1 for COUNT of Algorithm 1.** Let 0 < δ' ≤ 1. At every level ℓ with K_ℓ ≥ 72/δ' and e_ℓ ≤
δ'/12 (Section 6's constants; the level ℓ stands for Section 6's achievable K), `countThree ℓ` does
what step 1 says. It follows from `StComputesZ` at K = K_ℓ and M = CLIQUE(ℓ)
(`StCountIsNetworkMachine`, `StFirstLine`; `Printed.AchievedBy` holds of CLIQUE(ℓ) for (K_ℓ, e_ℓ),
e_ℓ ≤ δ'/12: `Printed.stClique`) and `StStepOneFor`, so that Section 6's form is on the path. -/
def StStepOne : Prop := ∀ (δ' : ℝ), 0 < δ' → δ' ≤ 1 → ∀ ℓ : ℕ, 72 / δ' ≤ levelK ℓ → Eight.Level.levelE ℓ ≤ δ' / 12 → ∃ A : ℕ, CountsThree (countThree ℓ) δ' A

/-! ### Step 4 and the end -/

/-- **Step 4, with the machine named.** Let k ≥ 1 and δ > 0, let `step` sparsify width k for
counting with ε = δ/3 and leaves of at most Bl·n clauses, and δ' = `deltaPrime δ (max k 3) Bl` (for
the paper's k ≥ 3, max(k, 3) = k). At every level ℓ with K_ℓ ≥ 72/δ' and e_ℓ ≤ δ'/12,
`engineSplit step ℓ` serves as the procedure for #k-SAT with the exponent δ. It follows from
`StStepOne` and `StSuffices`. -/
def StCountsAt : Prop := ∀ (k : ℕ), 1 ≤ k → ∀ δ : ℝ, 0 < δ → ∀ (step : CNode → Option (CNode × CNode)) (Dd Bl Sk : ℕ), SparsifiesPlain k (δ / 3) step Dd Bl Sk →
  ∀ ℓ : ℕ, 72 / deltaPrime δ (max k 3) Bl ≤ levelK ℓ → Eight.Level.levelE ℓ ≤ deltaPrime δ (max k 3) Bl / 12 → ∃ c : ℕ, Serves (engineSplit step ℓ) k δ c

/-- **Corollary 6 for machines cut into steps with Section 6's choice of K**, from end to end: in
the place of a level of Algorithm 1, any K ≥ 2 with K ≥ 72/δ' and any machine M for cliques on K
nodes with `Printed.AchievedBy M Cc K (δ'/12)`, δ' = `deltaPrime δ (max k 3) Bl`. -/
def StCountsWithAnyCliqueAlgorithm : Prop := ∀ (k : ℕ), 1 ≤ k → ∀ δ : ℝ, 0 < δ → ∀ (step : CNode → Option (CNode × CNode)) (Dd Bl Sk : ℕ), SparsifiesPlain k (δ / 3) step Dd Bl Sk →
  ∀ (K : ℕ) (M : Printed.CliqueMachine) (Cc : ℕ), 2 ≤ K → 72 / deltaPrime δ (max k 3) Bl ≤ K → Printed.AchievedBy M Cc K (deltaPrime δ (max k 3) Bl / 12) →
  ∃ c : ℕ, Serves (engineBy step (timesFreeAfter (Printed.networkOnSteps (3 * K ^ 8) (Printed.groupingMachine K (3 * K ^ 8) M) (Printed.formulaProcs (3 * K ^ 8) 3)))) k δ c

/-- **Corollary 6 for machines cut into steps, with the machine named**, in the form in which
Corollary 7 and the circuit lower bound for E^NP (Section 7) take it
(`Eight.ViaGrouping.EngineCounts`; there for every k ≥ 1: below 3 the width reduction changes
nothing). -/
def StEngineCounts : Prop := EngineCounts ENGINEsplit

/-- **#k-SAT with the machine named.** For every k ≥ 1 and δ > 0 there are a level ℓ and a threshold
parameter τ such that `COUNTsplit k ℓ τ` has polynomial-time steps and writes the number of
satisfying assignments of a k-CNF on n variables, in n + 1 bits, within c·2^{δn} steps, on states of
size polynomial in the length of the input. -/
def StCOUNTsplitCounts : Prop := ∀ (k : ℕ), 1 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ ℓ τ : ℕ, PolyTimeSteps (COUNTsplit k ℓ τ) ∧
  ∃ c : ℕ, ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF k φ →
    ∃ T : ℕ, (COUNTsplit k ℓ τ).Runs (SatK.enc k φ) T (c * ((SatK.enc k φ).length + 1) ^ c) (SatK.binary n (SatK.numSat φ)) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)

/-- **Tied to the machine, on Mathlib's Turing machines.** For every k ≥ 1 and δ > 0 there are ℓ, τ
such that (1) `COUNTsplit k ℓ τ` ITSELF has polynomial-time steps and writes the number of
satisfying assignments of a k-CNF on n variables within c·2^{δn} steps, on states of size polynomial
in the length of the input; (2) a Turing machine M with finite alphabets simulates it with
polynomial overhead
(whenever that machine ends on a word x with a word w within T steps on states of size at most S, M
started on x halts with w within q·(T+1)·(|x|+S+1)^q steps); (3) M counts the satisfying assignments
of k-CNFs within ⌊c·2^{δn}⌋ steps. (Without (1), a machine that runs the named machine and another
one side by side would meet (2) and (3).) -/
def StTiedTM : Prop := ∀ (k : ℕ), 1 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ (ℓ τ : ℕ) (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
  PolyTimeSteps (COUNTsplit k ℓ τ) ∧
  (∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF k φ →
    ∃ T : ℕ, (COUNTsplit k ℓ τ).Runs (SatK.enc k φ) T (c * ((SatK.enc k φ).length + 1) ^ c) (SatK.binary n (SatK.numSat φ)) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)) ∧
  (∀ (x w : List Bool) (T S : ℕ), (COUNTsplit k ℓ τ).Runs x T S w →
    Nonempty (Turing.TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun) (some (w.map M.outputAlphabet.invFun)) (q * (T + 1) * (x.length + S + 1) ^ q))) ∧
  SatK.CountsTM k M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊

/-- The end theorem has the statement `PaperSentences.CorCounting` of PaperSentencesStatement.lean.
Both of its halves follow from `StTiedTM`: the second, «#ETH is false», from `StTiedTM` at k = 3 by
the generic `not_CountETH_TM_of` of proof/consequences/CountKSat/EndLemmas.lean.
The end theorem is proved in two pieces:
`FromPrinted.SplitCount.endFrom : StTiedTM → ThreeSatStatement`, which has the tied statement as
HYPOTHESES, and the one-line instance
`FromPrinted.SplitCount.countingCorollary := endFrom stTiedTM`. Every theorem of this development
that the proof of `FromPrinted.SplitCount.endFrom : StTiedTM → ThreeSatStatement` uses says nothing
about a particular machine (such as `not_CountETH_TM_of`); so what the end theorem says about
machines can only come from the hypotheses.
The instance rests on the proofs of `StComputesZ`, `StFirstLine` and `StStepOne` (named
`FromPrinted.SplitCount.stComputesZ`, `stFirstLine`, `stStepOne`) and on the machines
`Printed.COUNT`, `Printed.NETWORK`, `Printed.CLIQUE`, not on the machines of the main text
(`Eight.ViaGrouping.COUNTp`, `Eight.ViaGrouping.CLIQUEp`, `Eight.ViaGrouping.netAlg`) or what is
proved of them. -/
abbrev ThreeSatStatement : Prop := PaperSentences.CorCounting

end FromPrinted.SplitCount
