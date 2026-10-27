/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Exits.AlgDefs
import Exits.Runs
import Exits.Poly
import Exits.Grouping
import Exits.Level
import Exits.Count
import Exits.Decides
import Variance.Grouping
import Value.End
import Enumerate.Enumeration
import Enumerate.Named
import Suffices.Main
import Eight.ViaGrouping.Table

/-! # Lemma 1 → Proposition 3 → Theorem 2 on the deciding form of Algorithm 1: the chain put together

Every theorem of this file is an implication of proof/threesat/Exits/AlgDefs.lean applied to proved
hypotheses; nothing else is proved here. What enters from the other folders:
* `Exits.stFirstUntil`, `Exits.stFoldUntilPoly` (proof/threesat/Exits/Runs.lean, Poly.lean): the
  loop that can be left early, line 10 of Algorithm 1 and the deciding form of lines 1 to 4;
* `Variance.stSearch` (proof/networks/Variance): the paragraph «A good grouping exists», with the
  bound 4PU on the variance of Y_{γ,γ'} summed from the covariances;
* `Value.stValue` (proof/networks/Value): «… so the value equals Z», sentence by sentence;
* `Eight.ViaGrouping.stTable` (proof/networks/Eight/ViaGrouping/Table.lean): «one entry costs …», as
  it stands;
* `Suffices.stSuffices` (proof/threesat/Suffices): «By Lemma 4 with ε = δ/3, … it suffices …», in
  its deciding form;
* Lemma 4 as an enumeration (proof/threesat/Enumerate). The proof of Section 6 takes it as
  `Enumerate.stEnumeration`. The proof by Algorithm 1 takes it from a form of Lemma 4 that speaks of
  a machine which prints the list of formulas, `(Enumerate.stNamedGives Enumerate.stNamed).2`, so
  the formulas that Sat goes through in line 2 are the list that this machine prints. No statement
  of this folder says so; it is visible only in the proof of `Enumerate.stNamedGives`.
The three end theorems `eStar_eq_zero`, `threeSat_through_eStar`, `threeSat_by_algorithm` are also
proved elsewhere in this development; this file proves them through the machines of this folder. -/

public section

namespace Exits

open Paper Eight

/-- **Line 10 of Algorithm 1**: «try all groupings into K_ℓ groups until one is good». The search
halts at the first good grouping. -/
theorem stSearchStops : StSearchStops := stSearchStopsOf stFirstUntil

/-- **Lemma 1 for the algorithm of its proof**, with the search of line 10: «Let (K, e) be
achievable and g = 3K⁸. There is a constant C₁ = C₁(K, e) such that the value of every network on
[g] with parameters P, B, τ and total U is computed within C₁·2^{e(U + gP/K) + 2gP/K}·(P + B)^{C₁}·τ
operations.» -/
theorem stGroupingLemma : StGroupingLemma := stGroupingLemmaOf stSearchStops Variance.stSearch ViaGrouping.stTable Value.stValue

/-- The algorithm of the proof of Lemma 1, with the search of line 10, has polynomial-time steps if
the algorithm for cliques has («… is computed within … operations»: steps are counted, and each
takes polynomial time). -/
theorem stKeeps : StKeeps := stKeepsOf stFoldUntilPoly

/-- **Proposition 3, first sentence, for the named algorithm**: «If (K, e) is achievable and g =
3K⁸, then (g², e') is achievable for e' = (ρ + 2/K)e + 2/K.» -/
theorem stLevelUp : StLevelUp := stLevelUpOf stGroupingLemma stKeeps

/-- **Proposition 3, first sentence**: «If (K, e) is achievable and g = 3K⁸, then (g², e') is
achievable for e' = (ρ + 2/K)e + 2/K.» -/
theorem stLevelAchievable : StLevelAchievable := stLevelAchievableOf stLevelUp

/-- **Proposition 3, second sentence**: «Hence e* = 0.» -/
theorem eStar_eq_zero : eStar = 0 := stEStarOf stLevelAchievable

/-- **Section 8**: «By brute force and Proposition 3, (K_ℓ, e_ℓ) is achievable for every ℓ, …», for
Clique(ℓ). -/
theorem stClique : StClique := stCliqueOf stLevelUp

/-- **Section 6, «Cost», for Count**: «So, with the preparation, Z is computed in time O(2^{δ'm})
plus a polynomial in n». -/
theorem stCountCost : StCountCost := stCountCostOf stGroupingLemma stKeeps stClique

/-- **The deciding form of Algorithm 1 decides 3-SAT, with the constants of its header**: «For
Theorem 2, ε = δ/3, δ' is as in Section 6, and ℓ is the first level with K_ℓ ≥ 72/δ' and e_ℓ ≤
δ'/12.» -/
theorem stAlgorithm : StAlgorithm := stAlgorithmOf Suffices.stSuffices stCountCost

/-- **Theorem 2 in its decision form for step machines, with the machine named**: the machine Sat,
the deciding form of lines 1 to 4 of Algorithm 1, decides 3-SAT on n variables within c·2^{δn}
steps, for a constant c. Line 2: «for each Φ in the list that Lemma 4 computes from φ and ε do»:
Lemma 4 is taken from its form with a machine that prints the list. -/
theorem stDecides : StDecides := stDecidesOf stAlgorithm (Enumerate.stNamedGives Enumerate.stNamed).2

/-- **The proof of Theorem 2 in Section 6, for a named machine**: «Fix such a K ≥ 72/δ' and put g =
3K⁸ … it suffices …», here for deciding whether a 3-CNF Φ with m ≤ Mn clauses is satisfiable, in
time O(2^{δ'm}) plus a polynomial in n. -/
theorem stProofNamed : StProofNamed := stProofNamedOf Suffices.stSuffices stGroupingLemma stKeeps

/-- **Theorem 2 in its decision form, by the proof of Section 6**, through e* = 0: for every δ > 0 a
deterministic algorithm decides 3-SAT on n variables, with any number of clauses, in time O(2^{δn})
(the decision form of Theorem 2, which counts). -/
theorem threeSat_through_eStar : Sat3.ThmEveryDelta := stThroughEStarOf eStar_eq_zero Enumerate.stEnumeration stProofNamed

/-- **Theorem 2 in its decision form, by Algorithm 1**: for every δ > 0 a deterministic algorithm
decides 3-SAT on n variables, with any number of clauses, in time O(2^{δn}) (the decision form of
Theorem 2, which counts). -/
theorem threeSat_by_algorithm : Sat3.ThmEveryDelta := stByAlgorithmOf stDecides

end Exits
