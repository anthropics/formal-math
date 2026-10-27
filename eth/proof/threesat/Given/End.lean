/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Given.Level
import Mathlib.Tactic

/-! # The way from `IsGivenNetwork` to Theorem 2

Every statement here is a statement of the namespace `Printed` (PrintedStatement.lean,
proof/threesat/Printed/Programs.lean), unchanged. Only the proofs differ: wherever the proofs there
say that a network satisfies Definition 2, or apply Lemma 1 to it, the proofs here use
`stGridGiven`, `stFormulaGiven` and `stOnGiven`.
The steps that do not look at a network are used as they stand, from their hypotheses:
`Printed.levelProposition_of`, `eStarZero_of`, `stEveryEta_of`, `stClique_of`, `cost_of_bound`,
`cost_with_first_line`, `firstLine_poly`, `decidesSparse_of_cost`, `stAlgorithm_of`, `stDecides_of`,
`threeSat_through_eStar_of`, `threeSat_by_algorithm_of`; so are Lemma 1 for the algorithm of its
proof (`Printed.stGroupingTied`, `stGroupingPoly`), which speaks of every network and is given none,
and the statements of other folders.
That these proofs run through `IsGivenNetwork` cannot be read off the statements; it shows in what
they depend on. -/

public section

namespace Given

open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed

/-! ## Proposition 3 -/

/-- **Proposition 3**, first sentence. -/
theorem levelProposition : LevelProposition := levelProposition_of stLevelTied stLevelPoly

/-- **Proposition 3**, second sentence: e* = 0. -/
theorem eStarZero : EStarZero := eStarZero_of levelProposition

/-- «That is, for every η > 0, (K, η) is achievable for infinitely many K.» -/
theorem stEveryEta : StEveryEta := stEveryEta_of eStarZero

/-- **Section 8: «By brute force and Proposition 3, (K_ℓ, e_ℓ) is achievable for every ℓ»**, by
Clique(ℓ). -/
theorem stClique : StClique := stClique_of stBrute stLevelTied stLevelPoly

/-! ## Section 6 -/

/-- **Lemma 1, applied to the network of Φ.** If NM does what Lemma 1 says for (K, e) on networks on
[g], then NM, with its queries answered by the procedures of the network of Φ, returns the value Z
of that network within C·2^{eU + (e+2)·gP/K}·(P + 1)^C steps: B = 1 and τ = 1. The bounds are
written as in `Eight.ViaGrouping.Correct.onFormula`; C = 3C₁ + 5 (the 3 is that of `StOnGiven`).
With it, in one conclusion: the machine has polynomial-time steps if NM has. The text is that of
`Printed.onFormula`, with `stFormulaGiven` and `stOnGiven` (read by `onSteps`) in the places of
`Printed.formula_isNetwork` and `Printed.stOnProcedures`. -/
theorem onFormula {NM : NetMachine} {C₁ g K : ℕ} {e : ℝ} (hg : 0 < g) (k : ℕ) (h : ComputesNetworks NM C₁ g K e) :
    (NM.PolyTimeSteps → Nonempty (IsPolyT (networkOnSteps g NM (formulaProcs g k)))) ∧ ∃ C : ℕ, ∀ Φ : Fml, ∃ T : ℕ,
      (networkOnSteps g NM (formulaProcs g k)).Runs Φ T (size Φ + 2 * g + 6 * (mu g Φ * k) + 10 + C * (size Φ + satPf g k Φ + 1) ^ C) (wordNet g k Φ).value ∧
      (T : ℝ) ≤ C * (2 : ℝ) ^ (e * ((wordNet g k Φ).U : ℝ) + (e + 2) * ((g : ℝ) * (satPf g k Φ : ℝ)) / K) * ((satPf g k Φ : ℝ) + 1) ^ C := by
  refine ⟨(onSteps h (stFormulaGiven g hg k [])).1, 3 * C₁ + 5, fun Φ => ?_⟩
  obtain ⟨_, hv, hU⟩ := satNet_isNetworkP hg k Φ
  obtain ⟨T, hrun, hT⟩ := (onSteps h (stFormulaGiven g hg k Φ)).2
  rw [hv] at hrun
  rw [hU, Nat.cast_one, mul_one] at hT
  refine ⟨T, hrun.mono le_rfl ?_, hT.trans ?_⟩
  · have := size_under (size Φ) (satPf g k Φ) C₁
    omega
  · have he : e * ((wordNet g k Φ).U : ℝ) + (e + 2) * ((g : ℝ) * (satPf g k Φ : ℝ)) / K = e * (((wordNet g k Φ).U : ℝ) + (g : ℝ) * (satPf g k Φ : ℝ) / K) + 2 * ((g : ℝ) * (satPf g k Φ : ℝ)) / K := by ring
    rw [he]
    have hY : (1 : ℝ) ≤ (satPf g k Φ : ℝ) + 1 := by linarith [(Nat.cast_nonneg (satPf g k Φ) : (0 : ℝ) ≤ _)]
    have h2 : ((satPf g k Φ : ℝ) + 1) ^ C₁ ≤ ((satPf g k Φ : ℝ) + 1) ^ (3 * C₁ + 5) := pow_le_pow_right₀ hY (by omega)
    have h3 : 3 * (C₁ : ℝ) ≤ ((3 * C₁ + 5 : ℕ) : ℝ) := by push_cast; linarith
    calc 3 * ((C₁ : ℝ) * (2 : ℝ) ^ (e * (((wordNet g k Φ).U : ℝ) + (g : ℝ) * (satPf g k Φ : ℝ) / K) + 2 * ((g : ℝ) * (satPf g k Φ : ℝ)) / K) * ((satPf g k Φ : ℝ) + 1) ^ C₁)
        = 3 * (C₁ : ℝ) * (2 : ℝ) ^ (e * (((wordNet g k Φ).U : ℝ) + (g : ℝ) * (satPf g k Φ : ℝ) / K) + 2 * ((g : ℝ) * (satPf g k Φ : ℝ)) / K) * ((satPf g k Φ : ℝ) + 1) ^ C₁ := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right h3 (by positivity)) h2 (by positivity) (by positivity)

/-- **Section 6, «Cost», for Count.** The text is that of `Printed.stCountCost_of`, with `onFormula`
of this file. -/
theorem stCountCost : StCountCost := by
  intro δ' ℓ hδ' h1 hK hE
  obtain ⟨hp, Cc, hA⟩ := stClique ℓ
  have hK2 : 2 ≤ levelK ℓ := (by norm_num : 2 ≤ 64).trans (levelK_ge ℓ)
  obtain ⟨C₁, hC₁⟩ := stGroupingTied (levelK ℓ) (δ' / 12) (CLIQUE ℓ) Cc hK2 (by positivity) (hA.mono hE)
  have hC₁' : ComputesNetworks (NETWORK ℓ) C₁ (levelG ℓ) (levelK ℓ) (δ' / 12) := hC₁
  have hg : 0 < levelG ℓ := Nat.mul_pos (by norm_num) (pow_pos (by omega) 8)
  obtain ⟨hpoly, hbound⟩ := onFormula hg 3 hC₁'
  obtain ⟨A, hA'⟩ := cost_of_bound hδ' h1 hg hK hbound
  exact ⟨firstLine_poly (hpoly (stGroupingPoly _ _ _ hp)), A + 4, cost_with_first_line hA'⟩

/-- **Algorithm 1 decides 3-SAT, with the constants of its header.** -/
theorem stAlgorithm : StAlgorithm := stAlgorithm_of Suffices.stSuffices stCountCost

/-- **Theorem 2 in its decision form for step machines, with the machine named.** -/
theorem stDecides : StDecides := stDecides_of stAlgorithm Enumerate.stEnumeration

/-- **The proof of Theorem 2 in Section 6**, for any machine that does what `Printed.AchievedBy`
asks for (K, δ'/12). The text is that of `Printed.stProofNamed_of`, with `onFormula` of this file.
(The τ here is a threshold of the sparsification used for Lemma 4, not the price of a query in
Definition 2(iii).) -/
theorem stProofNamed : StProofNamed := by
  intro δ Mc τ K M Cc hδ hδ1 hM hEn hK hp hA
  have hM' : (1 : ℝ) ≤ Mc := by exact_mod_cast hM
  -- «Let … δ' = δ/(3M) ≤ 1/3.»
  have hδ' : 0 < δ / (3 * (Mc : ℝ)) := div_pos hδ (by linarith)
  have h3 := Eight.delta'_le hδ1 hM'
  have hK2 := Eight.two_le_of_le hδ' h3 hK
  -- Lemma 1 for (K, δ'/12)
  obtain ⟨C₁, hC₁⟩ := stGroupingTied K _ M Cc hK2 (by positivity) hA
  have hg : 0 < 3 * K ^ 8 := Nat.mul_pos (by norm_num) (pow_pos (by omega) 8)
  -- the network of Φ and the paragraph «Cost»
  obtain ⟨hpoly, hbound⟩ := onFormula hg 3 hC₁
  obtain ⟨A, hA'⟩ := cost_of_bound hδ' (by linarith) hg hK hbound
  -- «By Lemma 4 with ε = δ/3, it suffices …», «so the total time is O(2^{δn})»
  have hs := Suffices.stSuffices δ Mc τ hδ hM hEn
  exact ⟨hs.1 _ (hpoly (stGroupingPoly _ _ _ hp)), hs.2 _ A (decidesSparse_of_cost hA')⟩

/-! ## Theorem 2 -/

/-- **Theorem 2 in its decision form**, by the proof of Section 6: through e* = 0 (`Printed.eStar`). -/
theorem threeSat_through_eStar : Sat3.ThmEveryDelta := threeSat_through_eStar_of stEveryEta Enumerate.stEnumeration stProofNamed

/-- **Theorem 2 in its decision form**, by Algorithm 1. -/
theorem threeSat_by_algorithm : Sat3.ThmEveryDelta := threeSat_by_algorithm_of stDecides

/-- The end statements of the namespace `Printed`, each field that rests on a network filled by the
corresponding theorem of this file. The fields `mono`, `half`, `answerEachQuery`, `groupingLemma`
and `enumeration` are given no network and are those of `Printed` and `Enumerate`. -/
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

end Given
