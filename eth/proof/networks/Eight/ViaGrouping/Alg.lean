/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.ViaGrouping.AlgDefs
public import Eight.ViaGrouping.LemGrouping
public import Eight.ViaGrouping.LevelEnd
public import Eight.ViaGrouping.GridPsi
public import Eight.ViaGrouping.Count

/-! # Algorithm 1 (Section 8) and Section 6 «Cost», on the algorithm of the printed proof of Lemma 1

Here the algorithm of Section 8 is put on top of `netAlg`
(proof/networks/Eight/ViaGrouping/Defs.lean), the algorithm of the printed proof of Lemma 1:

* CLIQUE(ℓ) meets the bound of «achievable» for (K_ℓ, e_ℓ), by brute force at level 0 and by Lemma 1
  and one level in each step (`CLIQUEp_within`, `CLIQUEp_polyTimeSteps`); the steps of NETWORK(ℓ)
  are polynomial time (`NETWORKp_keeps`);
* at a level with K_ℓ ≥ 72/δ' and e_ℓ ≤ δ'/12, COUNT counts the satisfying assignments within
  A·2^{δ'm} steps (`COUNTp_cost`, Section 6 «Cost»);
* from any sparsification with the property `Eight.SufficesSparse`, Algorithm 1 decides 3-SAT within
  c·2^{δn} steps (`algPseudocode_of`).

Used from the other files of this folder: Lemma 1 for the algorithm of its proof (`stLemGrouping`,
`stKeeps`; proof/networks/Eight/ViaGrouping/LemGrouping.lean, Keeps.lean), one level
(`levelAlgP_gridPsi_correct`, `levelAlgP_gridPsi_keeps`; LevelEnd.lean), the network of Φ
(`count_cost_of`,
`satProcs_keepsP`; Count.lean, SatPsi.lean), the program for Ψ in the two networks of a level
(`stGridPsi`, `stGridPsiPoly`; GridPsi.lean). No theorem of this file has a hypothesis of the form
`St…`.
Lemma 4 enters at one place only: through the property `Eight.SufficesSparse` of a constant M and a
construction S (proof/networks/Eight/SecProof_Proof.lean). `algPseudocode_of` holds for every M and
S with that property.
The numbers e_ℓ (`Eight.Level.levelE`) are those of proof/networks/Eight/Level/Defs.lean; they do
not depend on any algorithm. -/

public section

namespace Eight.ViaGrouping

open Groundwork Groundwork.Prog Paper Eight.SecNetworks Eight.Level

/-! ## Section 8: what CLIQUE and NETWORK do, and how long they take -/

/-- K_ℓ ≥ 2. -/
theorem two_le_levelK (ℓ : ℕ) : 2 ≤ levelK ℓ := le_trans (by norm_num) (levelK_ge ℓ)

/-- g_ℓ ≥ 1. -/
theorem zero_lt_levelG (ℓ : ℕ) : 0 < levelG ℓ := by
  have := levelK_ge ℓ
  unfold levelG
  positivity

/-- The steps of CLIQUE(ℓ) are polynomial time. -/
theorem CLIQUEp_polyTimeSteps (ℓ : ℕ) : (CLIQUEp ℓ).PolyTimeSteps := by
  induction ℓ with
  | zero => exact bruteE_keeps _
  | succ ℓ ih => exact levelAlgP_gridPsi_keeps stGridPsiPoly _ (ViaGrouping.stKeeps (levelK ℓ) _ _ ih)

/-- CLIQUE(ℓ) returns the value of every (K_ℓ, λ)-clique within C · 2^{e_ℓ K_ℓ² λ} (B + λ)^C steps,
times the cost of a query, with the e_ℓ of Section 8 for ρ = 11/12. The numbers are those of the
paper. Level 0 is brute force; the step from ℓ to ℓ + 1 is Lemma 1 for
the algorithm of its proof, then one level. -/
theorem CLIQUEp_within (ℓ : ℕ) : (CLIQUEp ℓ).Within (levelK ℓ) (Level.levelE ℓ) := by
  induction ℓ with
  | zero => exact bruteE_correct _
  | succ ℓ ih =>
    have hK : 2 ≤ levelK ℓ := two_le_levelK ℓ
    have hg : levelK ℓ ≤ levelG ℓ := by
      have : levelK ℓ ≤ levelK ℓ ^ 8 := Nat.le_self_pow (by norm_num) _
      unfold levelG
      omega
    have h := levelAlgP_gridPsi_correct stGridPsi hK hg (Level.levelE_nonneg ℓ) (stLemGrouping (levelK ℓ) (Level.levelE ℓ) (CLIQUEp ℓ) hK (Level.levelE_nonneg ℓ) ih)
    rw [levelK_succ]
    exact h

/-- The steps of NETWORK(ℓ) are polynomial time, whenever those of the procedures of the network are
and P is given in unary. -/
theorem NETWORKp_keeps (ℓ : ℕ) : AlgKeeps (NETWORKp ℓ) := ViaGrouping.stKeeps (levelK ℓ) (levelG ℓ) _ (CLIQUEp_polyTimeSteps ℓ)

/-! ## Algorithm 1 decides 3-SAT, and Theorem 2 -/

/-- The steps of COUNT, at the level ℓ, are polynomial time. -/
theorem COUNTp_polyTimeSteps (ℓ : ℕ) : PolyTimeSteps (COUNTp ℓ) := NETWORKp_keeps ℓ Formula _ (satProcs_keepsP _ _)

/-- **Section 6, «Cost», for COUNT of Algorithm 1.** Let 0 < δ' ≤ 1. At every level ℓ with K_ℓ ≥
72/δ' and e_ℓ ≤ δ'/12, COUNT(Φ) returns the number of assignments of the variables occurring in Φ
that satisfy Φ within A·2^{δ'm} steps, on states of polynomial size. -/
theorem COUNTp_cost {δ' : ℝ} (hδ' : 0 < δ') (hδ'1 : δ' ≤ 1) {ℓ : ℕ} (hK : 72 / δ' ≤ levelK ℓ) (hE : Level.levelE ℓ ≤ δ' / 12) :
    ∃ A : ℕ, ∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) → ∃ T : ℕ, (COUNTp ℓ).Runs Φ T (A * size Φ ^ A) (numSat Φ) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length) :=
  ViaGrouping.count_cost_of hδ' hδ'1 (zero_lt_levelG ℓ) hK
    (stLemGrouping (levelK ℓ) (δ' / 12) (CLIQUEp ℓ) (two_le_levelK ℓ) (by positivity) ((CLIQUEp_within ℓ).mono hE))

/-- **The deciding form of procedure #Sat of Algorithm 1, from any sparsification.** Let δ > 0, and
let the constant M ≥ 1 and the construction S have the property that it suffices to decide whether a
3-CNF Φ with m clauses is satisfiable, in time O(2^{δ'm}) (`Eight.SufficesSparse δ M S`). Let
δ' = min(δ/(3M), 1). At every level ℓ with K_ℓ ≥ 72/δ' and e_ℓ ≤ δ'/12, the machine S(COUNT) decides
3-SAT within c·2^{δn} steps. Lemma 4 is used only through that property. Only steps are counted
here. That they take polynomial time: `COUNTp_polyTimeSteps` and the first part of
`Eight.SufficesSparse`. -/
theorem algPseudocode_of {δ M : ℝ} (hδ : 0 < δ) (hM : 1 ≤ M) {S : StepMachine Formula ℤ → StepMachine (List Bool) Bool} (hS : SufficesSparse δ M S) {ℓ : ℕ}
    (hK : 72 / min (δ / (3 * M)) 1 ≤ levelK ℓ) (hE : Level.levelE ℓ ≤ min (δ / (3 * M)) 1 / 12) : Paper.DecidesInSteps (S (COUNTp ℓ)) δ := by
  have hδ' : 0 < min (δ / (3 * M)) 1 := lt_min (by positivity) one_pos
  obtain ⟨A, hA⟩ := COUNTp_cost hδ' (min_le_right _ _) hK hE
  refine hS.2 _ A fun Φ hΦ => ?_
  obtain ⟨T, hrun, hT⟩ := hA Φ hΦ
  -- «Φ is satisfiable if and only if Z > 0»
  refine ⟨T, _, hrun, by rw [Nat.cast_pos]; exact numSat_pos_iff Φ, hT.trans ?_⟩
  gcongr
  · norm_num
  · exact min_le_left _ _

end Eight.ViaGrouping
