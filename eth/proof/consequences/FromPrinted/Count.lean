/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FromPrinted.CountDefs
import Printed.End
import SplitCount.StepOne
import SplitCount.Main
import SplitCount.Tree
import SplitCount.Suffices
import SplitCount.Cert
import SplitCount.Host
import CountKSat.Host
import CountKSat.InOut
import CountKSat.Poly
import CountKSat.EndLemmas
import Eight.SecPseudocode_Levels
import WidthK.Decode
import Mathlib.Tactic

/-! # Proof of Corollary 6 on the machines of proof/threesat/Printed/

The statements are those of proof/consequences/FromPrinted/CountDefs.lean. What
proof/consequences/SplitCount/ proves for every machine is used as it stands:
`SplitCount.stStepOneFor` («Φ has Z·2^{n'} satisfying assignments»), `SplitCount.stStepTwo`,
`SplitCount.stSuffices` («By the work of Dell et al. … this case suffices»; the reduction to 3-CNFs
lies inside it), `SplitCount.stCert`, `SplitCount.deltaPrime_facts`,
`SplitCount.counts_of_simulation`. What names a machine is proved here:
* `stComputesZ`: the proof of Theorem 2 computes Z: Lemma 1 for the algorithm of its printed proof,
  from any machine with `Printed.AchievedBy` (`Printed.stGroupingTied`), applied to the network of Φ
  (`Printed.onFormula`, `Printed.stOnProcedures`), and «Cost» of Section 6
  (`Printed.cost_of_bound`).
* `stFirstLine`, `stCountIsNetworkMachine`, `stStepOne`: COUNT of Algorithm 1 at level ℓ is line 6
  in front of that machine at K = K_ℓ with CLIQUE(ℓ) (`Printed.stClique`).
* `COUNT_polyTimeSteps`: the steps of COUNT are polynomial time at every level.
* `stCountsAt`, `stCountsWithAnyCliqueAlgorithm`, `stEngineCounts`, `stCOUNTsplitCounts`,
  `stTiedTM`, `endFrom`, `countingCorollary`: as in proof/consequences/SplitCount/Main.lean. -/

public section

open SplitCount

namespace FromPrinted.SplitCount

open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
open scoped NNReal

/-- **The proof of Theorem 2, with K and g chosen from δ' as there, computes Z.** For 0 < δ' ≤ 1, K
≥ 2 with K ≥ 72/δ', g = 3K⁸ and any machine M for cliques on K nodes with
`Printed.AchievedBy M Cc K (δ'/12)`, the algorithm of the printed proof of Lemma 1 with M, run on
the network of Φ on g clusters, computes Z as Section 6 says. -/
theorem stComputesZ : StComputesZ := by
  intro δ' h0 h1 K M Cc hK2 hK hM
  have hg : 0 < 3 * K ^ 8 := by
    have : 0 < K := by omega
    positivity
  obtain ⟨C₁, hC₁⟩ := Printed.stGroupingTied K (δ' / 12) M Cc hK2 (by positivity) hM
  exact Printed.cost_of_bound h0 h1 hg hK (Printed.onFormula Printed.stOnProcedures hg 3 hC₁)

/-- **«if m = 0 then return 1».** If a machine computes Z as Section 6 says, with the exponent δ'
and the constant A, then so does that machine with line 6 of Algorithm 1 in front of it, with the
same exponent and some constant A' (the proof takes A' = A + 4). -/
theorem stFirstLine : StFirstLine := fun _ _ A h => ⟨A + 4, Printed.cost_with_first_line h⟩

/-- COUNT of Algorithm 1 at level ℓ is line 6 in front of the machine of `StComputesZ` at K = K_ℓ
and M = CLIQUE(ℓ): g_ℓ = 3K_ℓ⁸ by definition. -/
theorem stCountIsNetworkMachine : StCountIsNetworkMachine := fun _ => rfl

/-- **The count of a 3-CNF by COUNT of Algorithm 1.** For 0 < δ' ≤ 1 and every level ℓ with K_ℓ ≥
72/δ' and e_ℓ ≤ δ'/12, `countThree ℓ` computes the number Z·2^{n'} of the proof of Corollary 6, in
the form that `SplitCount.stStepOneFor` states. -/
theorem stStepOne : StStepOne := by
  intro δ' h0 h1 ℓ hK hE
  obtain ⟨-, Cc, hC⟩ := Printed.stClique ℓ
  obtain ⟨A, hA⟩ := stComputesZ δ' h0 h1 (levelK ℓ) (Printed.CLIQUE ℓ) Cc ((by norm_num : 2 ≤ 64).trans (levelK_ge ℓ)) hK (hC.mono hE)
  obtain ⟨A', hA'⟩ := stFirstLine _ δ' A hA
  rw [← stCountIsNetworkMachine ℓ] at hA'
  exact stStepOneFor (Printed.COUNT ℓ) δ' A' h0.le hA'

/-- The steps of COUNT of Algorithm 1 are polynomial time, at every level ℓ: those of CLIQUE(ℓ) are
(`Printed.stClique`), so those of the machine of Lemma 1 made from it (`Printed.stGroupingPoly`), so
those of that machine on the network of Φ (`Printed.onFormula_poly`), and line 6 keeps this
(`Printed.firstLine_poly`). -/
theorem COUNT_polyTimeSteps (ℓ : ℕ) : PolyTimeSteps (Printed.COUNT ℓ) :=
  Printed.firstLine_poly (Printed.onFormula_poly _ 3 _ (Printed.stGroupingPoly _ _ _ (Printed.stClique ℓ).1))

/-- **The proof of Corollary 6 at a level of Algorithm 1, with the machine named.** Under the
hypotheses of `StCountsAt`, `engineSplit step ℓ` serves as the procedure for #k-SAT with the
exponent δ. -/
theorem stCountsAt : StCountsAt := by
  intro k hk δ hδ step Dd Bl Sk hsp ℓ hK hE
  obtain ⟨h0, h1, h2⟩ := deltaPrime_facts hδ (le_max_right k 3) Bl
  obtain ⟨A, hA⟩ := stStepOne _ h0 h1 ℓ hK hE
  exact stSuffices k hk δ hδ step Dd Bl Sk hsp (countThree ℓ) _ A h0.le h2 hA

/-- **The same with Section 6's choice of K**: any K ≥ 2 with K ≥ 72/δ' and any machine M for
cliques on K nodes with `Printed.AchievedBy M Cc K (δ'/12)`, in the place of a level of Algorithm 1. -/
theorem stCountsWithAnyCliqueAlgorithm : StCountsWithAnyCliqueAlgorithm := by
  intro k hk δ hδ step Dd Bl Sk hsp K M Cc hK2 hK hM
  obtain ⟨h0, h1, h2⟩ := deltaPrime_facts hδ (le_max_right k 3) Bl
  obtain ⟨A, hA⟩ := stComputesZ _ h0 h1 K M Cc hK2 hK hM
  obtain ⟨A', hA'⟩ := stStepOneFor _ _ A h0.le hA
  exact stSuffices k hk δ hδ step Dd Bl Sk hsp _ _ A' h0.le h2 hA'

/-- **Corollary 6 for machines cut into steps, with the machine named**: for every k ≥ 1 and δ > 0
there are ℓ and τ such that `ENGINEsplit k ℓ τ` has polynomial-time steps and serves as the
procedure for #k-SAT with the exponent δ. -/
theorem stEngineCounts : StEngineCounts := by
  intro k hk δ hδ
  -- «choosing ε = δ/3 first»
  obtain ⟨τ, Dd, Bl, Sk, hsp⟩ := stStepTwo k (δ / 3) (by positivity)
  -- «and then applying Theorem 2 with a small enough value in place of δ»
  obtain ⟨h0, -, -⟩ := deltaPrime_facts hδ (le_max_right k 3) Bl
  obtain ⟨ℓ, a1, a2⟩ := Level.exists_level (η := deltaPrime δ (max k 3) Bl / 12) (by positivity) ⌈72 / deltaPrime δ (max k 3) Bl⌉₊
  exact ⟨ℓ, τ, stCert.2 _ _ (Poly.certStepC _ k) (stCert.1 _ (COUNT_polyTimeSteps ℓ)),
    stCountsAt k hk δ hδ _ Dd Bl Sk hsp ℓ ((Nat.le_ceil _).trans (by exact_mod_cast a1)) a2⟩

/-- **#k-SAT with the machine named.** For every k ≥ 1 and δ > 0 there are ℓ and τ such that
`COUNTsplit k ℓ τ` has polynomial-time steps and writes the number of satisfying assignments of a
k-CNF on n variables, in n + 1 bits, within c·2^{δn} steps, on states of size at most c·(length of
the input + 1)^c. -/
theorem stCOUNTsplitCounts : StCOUNTsplitCounts := by
  intro k hk δ hδ
  obtain ⟨ℓ, τ, ⟨hI⟩, c, hS⟩ := stEngineCounts k hk δ hδ
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

/-- **Tied to the machine, on Mathlib's Turing machines.** For every k ≥ 1 and δ > 0 there are ℓ, τ,
a Turing machine M with finite alphabets and numbers c, q such that `COUNTsplit k ℓ τ` has
polynomial-time steps and writes the number of satisfying assignments of a k-CNF on n variables
within c·2^{δn} steps on states of size at most c·(length + 1)^c;
M simulates it with the overhead q·(T+1)·(|x|+S+1)^q; and M counts the satisfying assignments of
k-CNFs within ⌊c·2^{δn}⌋ steps. -/
theorem stTiedTM : StTiedTM := by
  intro k hk δ hδ
  obtain ⟨ℓ, τ, ⟨hI⟩, c₁, h⟩ := stCOUNTsplitCounts k hk (δ / 2) (by positivity)
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

/-- **Corollary 6**, in the wording of PaperSentencesStatement.lean: `endFrom` on the proof
`stTiedTM` of the tied statement. -/
theorem countingCorollary : ThreeSatStatement := endFrom stTiedTM

end FromPrinted.SplitCount
