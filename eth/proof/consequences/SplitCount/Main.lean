/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SplitCount.Defs
import SplitCount.StepOne
import SplitCount.Tree
import SplitCount.Suffices
import SplitCount.Cert
import SplitCount.Host
import CountKSat.Host
import CountKSat.InOut
import CountKSat.Poly
import CountKSat.EndLemmas
import Eight.ViaGrouping.Alg
import Eight.SecPseudocode_Levels
import WidthK.Decode
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! # Corollary 6: the choice of δ', and the corollary from the tied statement

«The constants in O(n) depend on k and ε, so choosing ε = δ/3 first and then δ' small enough gives
time O(2^{δn}).»
* `deltaPrime_facts`: δ' = `deltaPrime δ w Bl` is positive, at most 1, and small enough.
* `stCountsAt`: `stStepOne`, for a level ℓ of Algorithm 1, put into «this suffices» (`stSuffices`).
* `endFrom`: Corollary 6 in the wording of PaperSentencesStatement.lean, both halves from the tied
  statement `StTiedTM`, which is taken as a hypothesis. -/

public section

namespace SplitCount

open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
open scoped NNReal

/-- «then δ' small enough»: for δ > 0 and w ≥ 3, δ' = `deltaPrime δ w Bl` is positive, at most 1,
and δ'·(1 + 3(w − 3))·(Bl + 1) ≤ δ/3. -/
theorem deltaPrime_facts {δ : ℝ} (hδ : 0 < δ) {w : ℕ} (hw : 3 ≤ w) (Bl : ℕ) :
    0 < deltaPrime δ w Bl ∧ deltaPrime δ w Bl ≤ 1 ∧ deltaPrime δ w Bl * ((1 + 3 * ((w : ℝ) - 3)) * ((Bl : ℝ) + 1)) ≤ δ / 3 := by
  have hw' : (3 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hB0 : (0 : ℝ) ≤ (Bl : ℝ) := Nat.cast_nonneg Bl
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (1 + 3 * ((w : ℝ) - 3)) * ((Bl : ℝ) + 1) := ⟨_, rfl⟩
  have hX0 : 0 < X := by rw [hX]; exact mul_pos (by linarith) (by linarith)
  unfold deltaPrime
  rw [← hX]
  refine ⟨lt_min (by positivity) one_pos, min_le_right _ _, ?_⟩
  calc min (δ / (3 * X)) 1 * X ≤ δ / (3 * X) * X := mul_le_mul_of_nonneg_right (min_le_left _ _) hX0.le
    _ = δ / 3 := by field_simp

/-- **The choice of δ', with the machine named.** Under the hypotheses of `StCountsAt`,
`engineSplit step ℓ` serves as the procedure for #k-SAT with the exponent δ. -/
theorem stCountsAt : StCountsAt := by
  intro k hk δ hδ step Dd Bl Sk hsp ℓ hK hE
  obtain ⟨h0, h1, h2⟩ := deltaPrime_facts hδ (le_max_right k 3) Bl
  obtain ⟨A, hA⟩ := stStepOne _ h0 h1 ℓ hK hE
  exact stSuffices k hk δ hδ step Dd Bl Sk hsp (countThree ℓ) _ A h0.le h2 hA

/-- **Corollary 6**: «For every k ≥ 3 and δ > 0 there is a deterministic algorithm that computes the
number of satisfying assignments of a k-CNF on n variables in time O(2^{δn}). For k = 3 this says
that the counting version #ETH of ETH is false.»
The statement is `PaperSentences.CorCounting` of PaperSentencesStatement.lean, for Turing machines.
Here it is drawn from the tied statement `StTiedTM` as a hypothesis: both halves take the Turing
machine of that statement, which simulates `COUNTsplit k ℓ τ`; the second half at k = 3, by
`CountKSat.EndLemmas.not_CountETH_TM_of`. -/
theorem endFrom (h : StTiedTM) : ThreeSatStatement := by
  refine ⟨fun k hk δ hδ => ?_, EndLemmas.not_CountETH_TM_of fun δ hδ => ?_⟩
  · obtain ⟨ℓ, τ, M, c, q, hfin, -, -, -, hM⟩ := h k (by omega) δ hδ
    exact ⟨c, M, _, hfin, hM, fun n _ => Nat.floor_le (by positivity)⟩
  · obtain ⟨ℓ, τ, M, c, q, hfin, -, -, -, hM⟩ := h 3 (by norm_num) (δ : ℝ) (NNReal.coe_pos.2 hδ)
    exact ⟨M, c, hfin, hM⟩

end SplitCount
