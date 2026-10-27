/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PrintedOrder.Defs
import PrintedOrder.AddUp
import SplitCount.Main
import SplitCount.Tree
import SplitCount.Cert
import SplitCount.Host
import SparsifyWidthK.Thresholds
import CountKSat.ProgC
import CountKSat.StepCount
import CountKSat.Walk
import CountKSat.Host
import CountKSat.InOut
import CountKSat.Poly
import CountKSat.EndLemmas
import Eight.ViaGrouping.Alg
import Eight.SecPseudocode_Levels
import WidthK.Decode
import Mathlib.Tactic

/-! # Section 7, Corollary 6: the count is the sum of the counts of the outputs of the sparsification, because no two of them share a satisfying assignment, as in the paper's proof

* `boundsFrom`, `stBounds`: the bounds on the tree (number of leaves, clauses of a leaf, stack),
  without the sum. They come from `CountKSat.stProgC` as in proof/consequences/SplitCount/; that
  theorem has three hypotheses: the sum at one step, which gets `StStepAdds`, and
  proof/consequences/CountKSat/'s own `CountKSat.stRootCount` and `CountKSat.stSumLeaves`. Its sum
  over the leaves is dropped.
* `stepTwoFrom`: step 2 of the proof (`SplitCount.StStepTwo`) from `StTreeAddsUp` and `StBounds`,
  which are hypotheses. `StBounds` has no sum, so the sum over the leaves in the result can only be
  that of `StTreeAddsUp`.
* `engineCountsFrom`, `countsFrom`, `tiedFrom`: the last steps of
  proof/consequences/SplitCount/Main.lean, repeated with step 2 as a hypothesis.
* `countingCorollary`: `SplitCount.endFrom` on them. -/

public section

namespace PrintedOrder

open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ SplitCount
open scoped NNReal

/-- **The bounds on the tree, without the sum**, from the sum at one step (`StStepAdds`), which is a
hypothesis: for every k and ε > 0 some threshold parameter τ gives a tree with at most 2^{εn}
leaves, O(n) clauses in each leaf and a short stack. The thresholds are those of
`WidthK.stExistsTau`; the bounds are those of `CountKSat.stProgC`, which gets the hypothesis for the
sum at one step and proof/consequences/CountKSat/'s own `stRootCount` and `stSumLeaves`;
`SplitCount.sparsifiesPlain_of` carries them to the tree whose side list starts empty; its sum over
the leaves is dropped. -/
theorem boundsFrom : StStepAdds → StBounds := fun hS k _ hε => by
  obtain ⟨τ, -, h4, hτ⟩ := WidthK.stExistsTau k 0 _ hε
  have hsp := sparsifiesPlain_of (stProgC hS stRootCount stSumLeaves τ k _ (by omega) hτ)
  refine ⟨τ, WidthK.bsum τ k, WidthK.leafC τ k + k * WidthK.bsum τ k + 1, 2 ^ k + k * WidthK.bsum τ k + 1, fun n ψ hψ => ?_⟩
  obtain ⟨t1, t2, -, t4⟩ := hsp n ψ hψ
  exact ⟨t1, t2, t4⟩

/-- **The bounds on the tree, without the sum**: `boundsFrom` on `stStepAdds`. -/
theorem stBounds : StBounds := boundsFrom stStepAdds

/-- **Step 2 of the proof of Corollary 6**, from two statements taken as hypotheses: the numbers of
the leaves add up to that of the given formula (`StTreeAddsUp`), and the bounds on the tree
(`StBounds`, which has no sum). The proof only puts the pieces together: the sum is that of
`StTreeAddsUp` at the depth Dd·n. -/
theorem stepTwoFrom : StTreeAddsUp → StBounds → SplitCount.StStepTwo := fun hT hB k ε hε => by
  obtain ⟨τ, Dd, Bl, Sk, h⟩ := hB k ε hε
  refine ⟨τ, Dd, Bl, Sk, fun n ψ hψ => ?_⟩
  obtain ⟨t1, t2, t4⟩ := h n ψ hψ
  exact ⟨t1, t2, hT _ k _ n ψ, t4⟩

/-- `SplitCount.StEngineCounts` with step 2 as a hypothesis: for every k ≥ 1 and δ > 0 there are ℓ
and τ such that `ENGINEsplit k ℓ τ` has polynomial-time steps and serves as the procedure for #k-SAT
with the exponent δ. -/
theorem engineCountsFrom (h2 : SplitCount.StStepTwo) : StEngineCounts := by
  intro k hk δ hδ
  obtain ⟨τ, Dd, Bl, Sk, hsp⟩ := h2 k (δ / 3) (by positivity)
  obtain ⟨h0, -, -⟩ := deltaPrime_facts hδ (le_max_right k 3) Bl
  obtain ⟨ℓ, a1, a2⟩ := Level.exists_level (η := deltaPrime δ (max k 3) Bl / 12) (by positivity) ⌈72 / deltaPrime δ (max k 3) Bl⌉₊
  exact ⟨ℓ, τ, SplitCount.stCert.2 _ _ (Poly.certStepC _ k) (SplitCount.stCert.1 _ (COUNTp_polyTimeSteps ℓ)),
    stCountsAt k hk δ hδ _ Dd Bl Sk hsp ℓ ((Nat.le_ceil _).trans (by exact_mod_cast a1)) a2⟩

/-- `SplitCount.StCOUNTsplitCounts` with step 2 as a hypothesis: for every k ≥ 1 and δ > 0 there are
ℓ and τ such that `COUNTsplit k ℓ τ` has polynomial-time steps and writes the number of satisfying
assignments of a k-CNF on n variables, in n + 1 bits, within c·2^{δn} steps. -/
theorem countsFrom (h2 : SplitCount.StStepTwo) : StCOUNTsplitCounts := by
  intro k hk δ hδ
  obtain ⟨ℓ, τ, ⟨hI⟩, c, hS⟩ := engineCountsFrom h2 k hk δ hδ
  refine ⟨ℓ, τ, ?_, c, fun n φ h3 => ?_⟩
  · have := hI
    exact ⟨IsPolyT.mapIn (M := ENGINEsplit k ℓ τ) (stCertDecU k)⟩
  · have hc : ∀ C ∈ Decode.toN φ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := by
      intro C hC
      obtain ⟨⟨D, hD, hl⟩, h⟩ := Decode.mem_toN hC
      exact ⟨hl ▸ h3.1 D hD, h⟩
    have hnd : (Decode.toN φ).Nodup := by
      refine List.Nodup.map (List.map_injective_iff.2 fun a b hab => ?_) h3.2
      exact Prod.ext (Fin.ext (Prod.ext_iff.1 hab).1) (Prod.ext_iff.1 hab).2
    obtain ⟨T, r, hT⟩ := hS n (Decode.toN φ) hc hnd
    rw [stCntToN] at r
    refine ⟨T, (Stepped.mapIn_runs (by rw [stDecU k n φ hk h3.1]; exact r)).mono le_rfl ?_, hT⟩
    have hlen := DecodeK.length_enc k φ
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) c)

/-- **The tied statement of proof/consequences/SplitCount/ with step 2 as a hypothesis**: for every
k ≥ 1 and δ > 0 there are ℓ, τ, a Turing machine M with finite alphabets and numbers c, q such that
`COUNTsplit k ℓ τ` has polynomial-time steps and counts within c·2^{δn} steps, M simulates it with
polynomial overhead, and M counts the satisfying assignments of k-CNFs within ⌊c·2^{δn}⌋ steps. -/
theorem tiedFrom : SplitCount.StStepTwo → SplitCount.StTiedTM := by
  intro h2 k hk δ hδ
  obtain ⟨ℓ, τ, ⟨hI⟩, c₁, h⟩ := countsFrom h2 k hk (δ / 2) (by positivity)
  have := hI
  obtain ⟨N', q, hfin, hP⟩ := stHostW (COUNTsplit k ℓ τ)
  have hP' : ∀ (x w : List Bool) (T S : ℕ), (COUNTsplit k ℓ τ).Runs x T S w →
      Nonempty (Turing.TM2OutputsInTime N'.tm (x.map N'.inputAlphabet.invFun) (some (w.map N'.outputAlphabet.invFun)) (q * (T + 1) * (x.length + S + 1) ^ q)) :=
    fun x w T S r => hP x T S w r
  obtain ⟨C, hC⟩ := counts_of_simulation hδ (COUNTsplit k ℓ τ) N' q hP' c₁ _ _ (fun n φ h => DecodeK.length_enc_succ_le h) h
  refine ⟨ℓ, τ, N', max c₁ C, q, hfin, ⟨hI⟩, fun n φ h3 => ?_, hP', ?_⟩
  · obtain ⟨T, r, hT⟩ := h n φ h3
    refine ⟨T, r.mono le_rfl (Nat.mul_le_mul (le_max_left _ _) (Nat.pow_le_pow_right (by omega) (le_max_left _ _))), hT.trans ?_⟩
    have hn0 : (0 : ℝ) ≤ δ * n := by positivity
    exact mul_le_mul (by exact_mod_cast le_max_left c₁ C) (Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)) (by positivity) (by positivity)
  · exact EndLemmas.CountsTM.mono hC fun n => Nat.floor_le_floor (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right c₁ C) (by positivity))

/-- **Corollary 6**, in the wording of PaperSentencesStatement.lean: `SplitCount.endFrom` on
`tiedFrom`, `stepTwoFrom`, `stTreeAddsUp` and `stBounds`. The sum over the outputs of the
sparsification comes from «no two of which share a satisfying assignment». -/
theorem countingCorollary : CountingAgain := SplitCount.endFrom (tiedFrom (stepTwoFrom stTreeAddsUp stBounds))

end PrintedOrder
