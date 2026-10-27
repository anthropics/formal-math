/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.Proof
public import Printed.LevelFrom
public import Printed.Grouping
public import Variance.Grouping
public import Exits.End
public import Value.End
public import Suffices.Main
public import Enumerate.Enumeration

/-! # The end statements of proof/threesat/Printed/

The files of this folder prove each step from the steps before it, which are hypotheses (`…_of`,
`…_from`). Five statements come from other folders:
* «a good grouping exists … fix the first good one» (`Eight.ViaGrouping.StSearch`), proved through
  «Var Y_{γ,γ'} ≤ … = 4PU» in proof/networks/Variance (`Variance.stSearch`);
* the search stops at the first good grouping (`Exits.StSearchStops`), proof/threesat/Exits
  (`Exits.stSearchStops`);
* «so the value equals Z» (`Value.StValueEqualsZ`), proof/networks/Value (`Value.stValueEqualsZ`);
* «it suffices …», for deciding (`Suffices.StSuffices`), proof/threesat/Suffices
  (`Suffices.stSuffices`);
* Lemma 4 as an enumeration (`Enumerate.StEnumeration`), proof/threesat/Enumerate
  (`Enumerate.stEnumeration`).
`endStatements_of` has exactly these five as hypotheses. Below they are filled in, and every
statement `St…` of PrintedStatement.lean, Programs.lean and CodingDefs.lean is a closed theorem.
(Some are proved without these hypotheses in other files: `stAskServes`, `stCliqueValue`,
`stToLists` in Coding.lean; `stMono`, `stBrute`, `stHalf`, `stAnswerEachQuery` in Achievable.lean;
`stOnProcedures` in GroupingProcs.lean; `stEntryCost` in GroupingEntry.lean; `stGroupingTiedOf` in
GroupingRun.lean; `stGroupingPoly` in GroupingPoly.lean; `stBothNetworks`, `stLevelPoly` in
LevelFrom.lean.) -/

public section

namespace Printed

/-- All end statements of proof/threesat/Printed/, from the five statements that other folders
prove. -/
theorem endStatements_of (hSearch : Eight.ViaGrouping.StSearch) (hStops : Exits.StSearchStops) (hValue : Value.StValueEqualsZ) (hSuffices : Suffices.StSuffices) (hEnumeration : Enumerate.StEnumeration) : EndStatements :=
  have hG : StGroupingTied := stGroupingTied_of hSearch hStops hValue
  have hC : StClique := stClique_from hG
  have hAlg : StAlgorithm := stAlgorithm_of hSuffices (stCountCost_of hC hG stGroupingPoly stOnProcedures)
  have hDec : StDecides := stDecides_of hAlg hEnumeration
  have hPN : StProofNamed := stProofNamed_of hSuffices hG stGroupingPoly stOnProcedures
  { mono := stMono
    half := stHalf
    answerEachQuery := stAnswerEachQuery
    groupingLemma := groupingLemma_of hG
    levelProposition := levelProposition_from hG
    eStarZero := eStarZero_from hG
    everyEta := stEveryEta_from hG
    clique := hC
    enumeration := hEnumeration
    proofNamed := hPN
    algorithm := hAlg
    decides := hDec
    through_eStar := threeSat_through_eStar_of (stEveryEta_from hG) hEnumeration hPN
    by_algorithm := threeSat_by_algorithm_of hDec }

/-! ## Lemma 1 -/

/-- **Lemma 1 for the algorithm of its proof, from ANY machine that does what Definition 4 asks.** -/
theorem stGroupingTied : StGroupingTied := stGroupingTied_of Variance.stSearch Exits.stSearchStops Value.stValueEqualsZ

/-- **Lemma 1.** -/
theorem groupingLemma : GroupingLemma := groupingLemma_of stGroupingTied

/-! ## Proposition 3 -/

/-- **Proposition 3, first sentence, for the algorithm of its proof, from ANY machine that does what
Definition 4 asks.** -/
theorem stLevelTied : StLevelTied := stLevelTied_from stGroupingTied

/-- **Proposition 3**, first sentence. -/
theorem levelProposition : LevelProposition := levelProposition_of stLevelTied stLevelPoly

/-- **Proposition 3**, second sentence: e* = 0. -/
theorem eStarZero : EStarZero := eStarZero_of levelProposition

/-- «That is, for every η > 0, (K, η) is achievable for infinitely many K.» -/
theorem stEveryEta : StEveryEta := stEveryEta_of eStarZero

/-! ## Section 8 and Section 6 -/

/-- **Section 8: «By brute force and Proposition 3, (K_ℓ, e_ℓ) is achievable for every ℓ»**, by
Clique(ℓ). -/
theorem stClique : StClique := stClique_of stBrute stLevelTied stLevelPoly

/-- **Section 6, «Cost», for Count.** -/
theorem stCountCost : StCountCost := stCountCost_of stClique stGroupingTied stGroupingPoly stOnProcedures

/-- **Algorithm 1 decides 3-SAT, with the constants of its header.** -/
theorem stAlgorithm : StAlgorithm := stAlgorithm_of Suffices.stSuffices stCountCost

/-- **Theorem 2 in its decision form for step machines, with the machine named.** -/
theorem stDecides : StDecides := stDecides_of stAlgorithm Enumerate.stEnumeration

/-- **The proof of Theorem 2 in Section 6, from the printed definition**, for ANY machine that does
what Definition 4 asks for (K, δ'/12). -/
theorem stProofNamed : StProofNamed := stProofNamed_of Suffices.stSuffices stGroupingTied stGroupingPoly stOnProcedures

/-- **Theorem 2 in its decision form**, by the proof of Section 6: through e* = 0 for the printed
Definition 4. -/
theorem threeSat_through_eStar : Sat3.ThmEveryDelta := threeSat_through_eStar_of stEveryEta Enumerate.stEnumeration stProofNamed

/-- **Theorem 2 in its decision form**, by Algorithm 1. -/
theorem threeSat_by_algorithm : Sat3.ThmEveryDelta := threeSat_by_algorithm_of stDecides

/-- The end statements of proof/threesat/Printed/. -/
theorem endStatements : EndStatements where
  mono := stMono
  half := stHalf
  answerEachQuery := stAnswerEachQuery
  groupingLemma := groupingLemma
  levelProposition := levelProposition
  eStarZero := eStarZero
  everyEta := stEveryEta
  clique := stClique
  enumeration := Enumerate.stEnumeration
  proofNamed := stProofNamed
  algorithm := stAlgorithm
  decides := stDecides
  through_eStar := threeSat_through_eStar
  by_algorithm := threeSat_by_algorithm

end Printed
