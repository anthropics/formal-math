/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FromPrinted.SatDefs
import FromPrinted.Core
import Printed.End
import SplitSat.Simulate
import SplitSat.Main
import WidthK.Top.EndLemmas
import Mathlib.Tactic

/-! # Section 7, Corollary 5 along the reduction that its printed proof cites, on the machine `Printed.SAT`, which decides with Algorithm 1

The proof in the paper: «… Theorem 2 gives s_3 = 0, which is the negation of ETH; … By a theorem of
Impagliazzo, Paturi and Zane, which rests on their Sparsification Lemma, s_3 = 0 implies s_k = 0 for
every k ≥ 3; the reduction (sparsify, then split every long clause into clauses of 3 literals with
new variables) uses no randomness … Hence s_∞ = lim_k s_k = 0 ≠ 1.»
The reduction and what is proved of it for every procedure D for 3-SAT are those of
proof/consequences/SplitSat/ (`SplitSat.exists_parameters`, which rests on `SplitSat.stSparsifyK`,
`stReduce`, `stReduceCert`); they are used as they stand.
* `stSATsplit`, `stTiedTM`: the reduction run on the machine of Theorem 2 in its decision form, and
  a Turing machine of Mathlib that simulates it.
* `stTiedThreeTM`: «Theorem 2 gives s_3 = 0», tied to the machine of Theorem 2 in its decision form,
  from `Printed.stDecides`.
* `endFrom`, `eth_and_seth_false`: Corollary 5, first with the two tied statements as hypotheses,
  then applied to their proofs. s_3 = 0 is taken from `StTiedThreeTM`, and s_k = 0 for k > 3 from
  `StTiedTM`; then the general `SatK.sTM_eq_zero_of`.
What is different from the paper is listed at the head of proof/consequences/SplitSat/Defs.lean. -/

public section

section

open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight.ViaGrouping SplitSat
open scoped NNReal ENNReal

namespace FromPrinted.SplitSat

/-- **k-SAT with the machine named**: for every k ≥ 3 and δ > 0 there are τ, ℓ₃, τ₃ such that
`SATsplit k τ ℓ₃ τ₃`, the reduction run on the machine of Theorem 2 in its decision form without its
reader, has polynomial-time steps and decides k-SAT with the exponent δ. This is the statement
`FromPrinted.SplitSat.StSATsplit`. -/
theorem stSATsplit : StSATsplit := fun k hk δ hδ => by
  obtain ⟨τ, δ₃, h0, h⟩ := exists_parameters k hk δ hδ
  obtain ⟨ℓ₃, τ₃, hp, c, hD⟩ := stCore3 δ₃ h0
  exact ⟨τ, ℓ₃, τ₃, h (core3 ℓ₃ τ₃) c hp hD⟩

/-- **Tied to the machine, on Mathlib's Turing machines**: for every k ≥ 3 and δ > 0 there are τ,
ℓ₃, τ₃ such that `SATsplit k τ ℓ₃ τ₃` itself has polynomial-time steps and decides k-SAT with the
exponent δ, a Turing machine M with finite alphabets simulates it with polynomial overhead, and M
decides k-SAT within ⌊c·2^{δn}⌋ steps. This is the statement `FromPrinted.SplitSat.StTiedTM`. In the
proof the named machine has the exponent δ/2. -/
theorem stTiedTM : StTiedTM := fun k hk δ hδ => by
  obtain ⟨τ, ℓ₃, τ₃, hp, c, hd⟩ := stSATsplit k hk (δ / 2) (by positivity)
  obtain ⟨M, q, hfin, hs⟩ := exists_simulates _ hp
  obtain ⟨C, hcC, hTM⟩ := decidesTM_of_simulates hδ hs hd
  exact ⟨τ, ℓ₃, τ₃, M, C, q, hfin, hp, decides_mono (by linarith) hcC hd, hs, hTM⟩

/-- **«Theorem 2 gives s_3 = 0», tied to the machine of Theorem 2 in its decision form**: for every
δ > 0 there are ℓ, τ such that `Printed.SAT ℓ τ` itself has polynomial-time steps and decides 3-SAT
with the exponent δ, a Turing machine M with finite alphabets simulates it with polynomial overhead,
and M decides 3-SAT within ⌊c·2^{δn}⌋ steps. This is the statement
`FromPrinted.SplitSat.StTiedThreeTM`; ℓ and τ are those that `Printed.stDecides` gives for δ/2. -/
theorem stTiedThreeTM : StTiedThreeTM := fun δ hδ => by
  obtain ⟨ℓ, τ, hp, c, hd⟩ := Printed.stDecides (δ / 2) (by positivity)
  have hd' : Decides (Printed.SAT ℓ τ) 3 (δ / 2) c := hd
  obtain ⟨M, q, hfin, hs⟩ := exists_simulates _ hp
  obtain ⟨C, hcC, hTM⟩ := decidesTM_of_simulates hδ hs hd'
  exact ⟨ℓ, τ, M, C, q, hfin, hp, decides_mono (by linarith) hcC hd', hs, hTM⟩

/-- **Corollary 5 from the two tied statements**, which are hypotheses here: «s_k = 0 for every k ≥ 3.
Hence s_∞ = 0, and both ETH and SETH are false.» At k = 3 the Turing machine is that of
`StTiedThreeTM` («Theorem 2 gives s_3 = 0»), at k > 3 that of `StTiedTM` (the reduction); then the
general `SatK.sTM_eq_zero_of`. Nothing else is known of the machines. -/
theorem endFrom : StTiedTM → StTiedThreeTM → ThreeSatStatement := fun hT hT3 => by
  -- «s_k = 0 for every k ≥ 3»
  have hs : ∀ k : ℕ, 3 ≤ k → SatK.sTM k = 0 := fun k hk => SatK.sTM_eq_zero_of fun δ hδ => by
    rcases Nat.eq_or_lt_of_le hk with rfl | -
    · obtain ⟨_, _, M, c, _, hfin, -, -, -, h⟩ := hT3 (δ : ℝ) hδ
      exact ⟨M, c, hfin, h⟩
    · obtain ⟨_, _, _, M, c, _, hfin, -, -, -, h⟩ := hT k hk (δ : ℝ) hδ
      exact ⟨M, c, hfin, h⟩
  -- «Hence s_∞ = lim_k s_k = 0 ≠ 1»; here s_∞ is the supremum of the s_k, k ≥ 3, as in Definition
  -- 6, and all of them are 0.
  have hInf : PaperSentences.sInfty = 0 := by
    unfold PaperSentences.sInfty
    simp only [ENNReal.iSup_eq_zero]
    exact hs
  refine ⟨hs, hInf, fun h => ?_, fun h => ?_⟩
  · -- «Theorem 2 gives s_3 = 0, which is the negation of ETH»
    have := h 3 le_rfl
    rw [hs 3 le_rfl] at this
    exact lt_irrefl _ this
  · -- SETH is the statement s_∞ = 1, and 0 ≠ 1.
    have h' : PaperSentences.sInfty = 1 := h
    rw [hInf] at h'
    exact zero_ne_one h'

/-- **Corollary 5**: «s_k = 0 for every k ≥ 3. Hence s_∞ = 0, and both ETH and SETH are false.» The
statement is `PaperSentences.CorEth` of PaperSentencesStatement.lean. It is `endFrom` applied to
`stTiedTM` (the cited reduction of k-SAT to 3-SAT) and `stTiedThreeTM` (Theorem 2). -/
theorem eth_and_seth_false : ThreeSatStatement := endFrom stTiedTM stTiedThreeTM

end FromPrinted.SplitSat

end
