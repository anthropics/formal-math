/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SplitSat.Defs
import SplitSat.Cert
import SplitSat.Reader
import SplitSat.Procedure
import SplitSat.Simulate
import SparsificationLemma.TreeWalk.Walk
import ThreeSatPrinted.ThmEveryDelta
import WidthK.Top.EndLemmas
import Mathlib.Tactic

/-! # Section 7, Corollary 5 along the reduction that its printed proof cites, for machines cut into steps

The printed proof: «Theorem 2 gives s_3 = 0, which is the negation of ETH … By a theorem of
Impagliazzo, Paturi and Zane, which rests on their Sparsification Lemma, s_3 = 0 implies s_k = 0 for
every k ≥ 3; the reduction (sparsify, then split every long clause into clauses of 3 literals with
new variables) uses no randomness … Hence s_∞ = lim_k s_k = 0 ≠ 1.»
* `stSparsifyK`: «sparsify», from `SparsificationLemma.TreeWalk.lemSparsification_walk_k`.
* `exists_parameters`: for k ≥ 3 and δ > 0, a threshold parameter τ and an exponent δ₃ > 0 such that
  the reduction with parameter τ, run on any procedure with polynomial-time steps that decides 3-SAT
  with the exponent δ₃, has polynomial-time steps and decides k-SAT with the exponent δ. Here δ₃ =
  (δ/3)/(1 + (k−3)·B), where B·n bounds the clauses of a leaf.
* `stImplication`: «s_3 = 0 implies s_k = 0 for every k ≥ 3», for machines cut into steps.
* `stSATsplit`, `stTiedTM`: the reduction run on the machine of Theorem 2 in its decision form, and
  a Turing machine of Mathlib that simulates it.
* `stTiedThreeTM`: «Theorem 2 gives s_3 = 0», tied to the machine of Theorem 2 in its decision form,
  from `ThreeSatPrinted.algPseudocode_decides_viaC`.
* `endFrom`, `eth_and_seth_false`: Corollary 5, first with the two tied statements as hypotheses,
  then applied to their proofs. s_3 = 0 is taken from `StTiedThreeTM`, and s_k = 0 for k > 3 from
  `StTiedTM`; then the general `SatK.sTM_eq_zero_of`.
What is different from the paper is listed at the head of proof/consequences/SplitSat/Defs.lean. -/

public section

namespace SplitSat

open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight.ViaGrouping
open scoped NNReal ENNReal

/-- «sparsify»: for every k ≥ 3 and ε > 0 some threshold parameter τ makes the tree of the procedure
behind the Lean form of Lemma 4, run at width k, sparsify width k with at most 2^{εn} leaves. This
is the statement `SplitSat.StSparsifyK`, taken from
`SparsificationLemma.TreeWalk.lemSparsification_walk_k`. -/
theorem stSparsifyK : StSparsifyK := fun k hk ε hε => by
  obtain ⟨τ, -, h, -⟩ := SparsificationLemma.TreeWalk.lemSparsification_walk_k (k := k) (by omega) hε
  exact ⟨τ, _, _, _, h⟩

/-- For every k ≥ 3 and δ > 0 there are a threshold parameter τ and an exponent δ₃ > 0 such that,
for every procedure D with polynomial-time steps that decides 3-SAT with the exponent δ₃,
`REDUCE k τ D` has polynomial-time steps and decides k-SAT with the exponent δ. -/
theorem exists_parameters (k : ℕ) (hk : 3 ≤ k) (δ : ℝ) (hδ : 0 < δ) : ∃ (τ : ℕ) (δ₃ : ℝ), 0 < δ₃ ∧
    ∀ (D : StepMachine (List Unit × Fml) Bool) (c : ℕ), PolyTimeSteps D → Decides3 D δ₃ c →
      PolyTimeSteps (REDUCE k τ D) ∧ ∃ c' : ℕ, Decides (REDUCE k τ D) k δ c' := by
  obtain ⟨τ, Dd, B, Sk, hsp⟩ := stSparsifyK k hk (δ / 3) (by positivity)
  have hk3 : (0 : ℝ) ≤ (k : ℝ) - 3 := by
    have : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hpos : (0 : ℝ) < 1 + ((k : ℝ) - 3) * B := by
    have := mul_nonneg hk3 (Nat.cast_nonneg (α := ℝ) B)
    linarith
  have h0 : 0 < δ / 3 / (1 + ((k : ℝ) - 3) * B) := div_pos (by positivity) hpos
  exact ⟨τ, δ / 3 / (1 + ((k : ℝ) - 3) * B), h0, fun D c hp hD =>
    ⟨stReduceCert k τ D hp, stReduce k hk δ hδ τ Dd B Sk hsp D _ c h0.le (le_of_eq (div_mul_cancel₀ _ hpos.ne')) hD⟩⟩

/-- **«s_3 = 0 implies s_k = 0 for every k ≥ 3», for machines cut into steps**: for every family Ds
of procedures for 3-SAT, one for each exponent δ₃ > 0, and for every k ≥ 3 and δ > 0, the reduction
run on one member of that family has polynomial-time steps and decides k-SAT with the exponent δ.
This is the statement `SplitSat.StImplication`. -/
theorem stImplication : StImplication := fun Ds hDs k hk δ hδ => by
  obtain ⟨τ, δ₃, h0, h⟩ := exists_parameters k hk δ hδ
  obtain ⟨hp, c, hD⟩ := hDs δ₃ h0
  exact ⟨τ, δ₃, h0, h (Ds δ₃) c hp hD⟩

/-- **k-SAT with the machine named**: for every k ≥ 3 and δ > 0 there are τ, ℓ₃, τ₃ such that
`SATsplit k τ ℓ₃ τ₃`, the reduction run on the machine of Theorem 2 in its decision form without its
reader, has polynomial-time steps and decides k-SAT with the exponent δ. This is the statement
`SplitSat.StSATsplit`. -/
theorem stSATsplit : StSATsplit := fun k hk δ hδ => by
  obtain ⟨τ, δ₃, h0, h⟩ := exists_parameters k hk δ hδ
  obtain ⟨ℓ₃, τ₃, hp, c, hD⟩ := stCore3 δ₃ h0
  exact ⟨τ, ℓ₃, τ₃, h (core3 ℓ₃ τ₃) c hp hD⟩

/-- **Tied to the machine, on Mathlib's Turing machines**: for every k ≥ 3 and δ > 0 there are τ,
ℓ₃, τ₃ such that `SATsplit k τ ℓ₃ τ₃` itself has polynomial-time steps and decides k-SAT with the
exponent δ, a Turing machine M with finite alphabets simulates it with polynomial overhead, and M
decides k-SAT within ⌊c·2^{δn}⌋ steps. This is the statement `SplitSat.StTiedTM`. In the proof the
named machine has the exponent δ/2. -/
theorem stTiedTM : StTiedTM := fun k hk δ hδ => by
  obtain ⟨τ, ℓ₃, τ₃, hp, c, hd⟩ := stSATsplit k hk (δ / 2) (by positivity)
  obtain ⟨M, q, hfin, hs⟩ := exists_simulates _ hp
  obtain ⟨C, hcC, hTM⟩ := decidesTM_of_simulates hδ hs hd
  exact ⟨τ, ℓ₃, τ₃, M, C, q, hfin, hp, decides_mono (by linarith) hcC hd, hs, hTM⟩

/-- **«Theorem 2 gives s_3 = 0», tied to the machine of Theorem 2 in its decision form**: for every
δ > 0 there are ℓ, τ such that `ThreeSatPrinted.SATCp ℓ τ` itself has polynomial-time steps and
decides 3-SAT with the exponent δ, a Turing machine M with finite alphabets simulates it with
polynomial overhead, and M decides 3-SAT within ⌊c·2^{δn}⌋ steps. This is the statement
`SplitSat.StTiedThreeTM`; ℓ and τ are those that `ThreeSatPrinted.algPseudocode_decides_viaC` gives
for δ/2. -/
theorem stTiedThreeTM : StTiedThreeTM := fun δ hδ => by
  obtain ⟨ℓ, τ, -, hp, c, hd⟩ := ThreeSatPrinted.algPseudocode_decides_viaC (δ := δ / 2) (by positivity)
  have hd' : Decides (ThreeSatPrinted.SATCp ℓ τ) 3 (δ / 2) c := hd
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

end SplitSat
