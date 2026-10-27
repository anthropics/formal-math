/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PrintedOrder.Defs
import SplitSat.Main
import SplitSat.Procedure
import SplitSat.Simulate
import WidthK.Top.EndLemmas
import Mathlib.Tactic

/-! # Section 7, Corollary 5 through the implication

«Theorem 2 gives s_3=0, which is the negation of ETH. By a theorem of Impagliazzo, Paturi and Zane
[…], which rests on their Sparsification Lemma, s_3 = 0 implies s_k = 0 for every k ≥ 3» (proof of
Corollary 5)
* `stThreeSatFamily`: `SplitSat.stCore3` gives, for each exponent δ₃ > 0, a level ℓ and a threshold
  parameter τ; choosing them gives a family of procedures for 3-SAT.
* `hostedFrom`: from the implication for machines cut into steps (`SplitSat.StImplication`, a
  hypothesis), taken at δ/2, and the host theorem (`SplitSat.exists_simulates`,
  `decidesTM_of_simulates`): k-SAT on Turing machines from ANY family of procedures for 3-SAT.
  `stHosted`: the same on `SplitSat.stImplication`.
* `endThroughImplication`: Corollary 5 from the family, `StHosted` and `SplitSat.StTiedThreeTM`,
  which are hypotheses; `eth_and_seth_false`: on their proofs.
The implication is for machines cut into polynomial-time steps, not for arbitrary algorithms. -/

public section

namespace PrintedOrder

open Groundwork Groundwork.Prog Paper Eight.ViaGrouping SplitSat
open scoped NNReal ENNReal

/-- **«Theorem 2 gives s_3=0», for machines cut into steps**: there is a family of procedures for
3-SAT, one for each exponent δ₃ > 0, each with polynomial-time steps, and each member is the machine
of Theorem 2 in its decision form without the part that reads the input, at some level ℓ and
threshold parameter τ. From `SplitSat.stCore3`, by choice. -/
theorem stThreeSatFamily : StThreeSatFamily := by
  have h := SplitSat.stCore3
  refine ⟨fun δ => if hδ : 0 < δ then core3 (Classical.choose (h δ hδ)) (Classical.choose (Classical.choose_spec (h δ hδ))) else core3 0 0,
    fun δ hδ => ?_, fun δ hδ => ⟨_, _, dif_pos hδ⟩⟩
  simp only [dif_pos hδ]
  exact Classical.choose_spec (Classical.choose_spec (h δ hδ))

/-- **k-SAT on Turing machines from any family of procedures for 3-SAT**, from the implication for
machines cut into steps, which is a hypothesis. The implication is taken at δ/2; a Turing machine
simulates the machine that it gives, with polynomial overhead. -/
theorem hostedFrom : SplitSat.StImplication → StHosted := fun hI Ds hDs k hk δ hδ => by
  obtain ⟨τ, δ₃, h0, hp, c, hd⟩ := hI Ds hDs k hk (δ / 2) (by positivity)
  obtain ⟨M, q, hfin, hs⟩ := exists_simulates _ hp
  obtain ⟨C, hcC, hTM⟩ := decidesTM_of_simulates hδ hs hd
  exact ⟨τ, δ₃, M, C, q, h0, hfin, hp, decides_mono (by linarith) hcC hd, hs, hTM⟩

/-- **k-SAT on Turing machines from any family of procedures for 3-SAT, through the implication**:
`hostedFrom` on `SplitSat.stImplication`. -/
theorem stHosted : StHosted := hostedFrom SplitSat.stImplication

/-- **Corollary 5 in the order of its printed proof**, from three statements taken as hypotheses:
«s_k = 0 for every k ≥ 3. Hence s_∞ = 0, and both ETH and SETH are false.» At k = 3 the Turing
machine is that of `SplitSat.StTiedThreeTM` («Theorem 2 gives s_3=0»); at k > 3 the family of
`StThreeSatFamily` is handed to `StHosted`; then the general `SatK.sTM_eq_zero_of`. -/
theorem endThroughImplication : StThreeSatFamily → StHosted → SplitSat.StTiedThreeTM → SplitSat.ThreeSatStatement := fun hF hH hT3 => by
  obtain ⟨Ds, hDs, -⟩ := hF
  have hs : ∀ k : ℕ, 3 ≤ k → SatK.sTM k = 0 := fun k hk => SatK.sTM_eq_zero_of fun δ hδ => by
    rcases Nat.eq_or_lt_of_le hk with rfl | -
    · obtain ⟨_, _, M, c, _, hfin, -, -, -, h⟩ := hT3 (δ : ℝ) hδ
      exact ⟨M, c, hfin, h⟩
    · obtain ⟨_, _, M, c, _, -, hfin, -, -, -, h⟩ := hH Ds hDs k hk (δ : ℝ) hδ
      exact ⟨M, c, hfin, h⟩
  have hInf : PaperSentences.sInfty = 0 := by
    unfold PaperSentences.sInfty
    simp only [ENNReal.iSup_eq_zero]
    exact hs
  refine ⟨hs, hInf, fun h => ?_, fun h => ?_⟩
  · have := h 3 le_rfl
    rw [hs 3 le_rfl] at this
    exact lt_irrefl _ this
  · have h' : PaperSentences.sInfty = 1 := h
    rw [hInf] at h'
    exact zero_ne_one h'

/-- **Corollary 5**, in the wording of PaperSentencesStatement.lean: `endThroughImplication` on
`stThreeSatFamily`, `stHosted` and `SplitSat.stTiedThreeTM`. For k > 3 the way is: Theorem 2 gives
the family, the implication gives the machine for k-SAT, a Turing machine simulates it. -/
theorem eth_and_seth_false : EthAndSethAgain := endThroughImplication stThreeSatFamily stHosted SplitSat.stTiedThreeTM

end PrintedOrder
