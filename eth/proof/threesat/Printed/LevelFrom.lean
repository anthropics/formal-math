/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.LevelSentences
public import Printed.LevelPoly
public import Printed.GroupingPoly

/-! # Proposition 3 for `Printed.Achievable` (Definition 4 with a bound on the sizes of the states), with the hypotheses filled in

The files LevelNetworks, LevelCost, LevelPoly and LevelSentences of this folder take what other
files prove as hypotheses. Here these are filled in: the coding of the tables
(proof/threesat/Printed/Coding.lean), brute force and the facts on e* (Achievable.lean), Lemma 1 for
networks given by procedures (GroupingProcs.lean), polynomial-time steps of the machine of Lemma 1
(GroupingPoly.lean).
Lemma 1 for the algorithm of its proof (`StGroupingTied`) is the one hypothesis that is left in the
theorems `…_from`. -/

public section

namespace Printed

/-- **«Both networks satisfy Definition 2 with P = g³λ (so gP = N), with B₁ = gB + g²λ + 1 in the
role of B, and with τ = poly(B + λ)».** -/
theorem stBothNetworks : StBothNetworks := stBothNetworks_of stAskServes

/-- The machine of Proposition 3 has polynomial-time steps, because the machine of Lemma 1 has
(`stGroupingPoly`). -/
theorem stLevelPoly : StLevelPoly := stLevelPoly_of stGroupingPoly

/-- Proposition 3, first sentence, for the algorithm of its proof, from Lemma 1 for the algorithm of
its proof. -/
theorem stLevelTied_from (hG : StGroupingTied) : StLevelTied := stLevelTied_of stAskServes stCliqueValue hG stOnProcedures

/-- Proposition 3, first sentence. -/
theorem levelProposition_from (hG : StGroupingTied) : LevelProposition := levelProposition_of (stLevelTied_from hG) stLevelPoly

/-- Proposition 3, second sentence. -/
theorem eStarZero_from (hG : StGroupingTied) : EStarZero := eStarZero_of (levelProposition_from hG)

/-- «For every η > 0, (K, η) is achievable for infinitely many K.» -/
theorem stEveryEta_from (hG : StGroupingTied) : StEveryEta := stEveryEta_of (eStarZero_from hG)

/-- «By brute force and Proposition 3, (K_ℓ, e_ℓ) is achievable for every ℓ», by Clique(ℓ). -/
theorem stClique_from (hG : StGroupingTied) : StClique := stClique_of stBrute (stLevelTied_from hG) stLevelPoly

end Printed
