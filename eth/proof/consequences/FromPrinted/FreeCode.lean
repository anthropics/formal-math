/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FromPrinted.SatDefs
import FromPrinted.Core
import FreeCode.Reader
import FreeCode.ReaderCert
import FreeCode.Random
import FreeCode.Tied
import FreeCode.Main
import SplitSat.Walk
import SplitSat.Cert
import SplitSat.Main
import SparsifyWidthK.Poly.Sparsify
import Mathlib.Tactic

/-! # Corollary 5 with an input code of the formulas that does not depend on k (read by the reader `readFree`), tied to the machine `Printed.SAT`, which decides with Algorithm 1

The proof in the paper: «Theorem 2 gives s_3 = 0 … s_3 = 0 implies s_k = 0 for every k ≥ 3; the
reduction (sparsify, then split every long clause into clauses of 3 literals with new variables) …».
What proof/consequences/FreeCode/ proves for every procedure D (`FreeCode.tied_of_decidesW`: D
behind the reader `readFree`, and a Turing machine that simulates it) is used as it stands.
* `stTiedThree` (= `FromPrinted.FreeCode.StTiedThree`): D = `core3 ℓ τ`, the machine of Theorem 2 in
  its decision form without its own reader, by `FromPrinted.SplitSat.stCore3`.
* `stTied` (= `FromPrinted.FreeCode.StTied`): D = the reduction on `core3`, by
  `SplitSat.stSparsifyK`, `FromPrinted.SplitSat.stCore3` and `SplitSat.stReduceCore`.
* `allZeroFrom`, `allZero`: Corollary 5, first with the two tied statements as hypotheses, then
  applied to their proofs: s_3 = 0 from `StTiedThree` (Theorem 2), s_k = 0 for k > 3 from `StTied`
  (the reduction).
* `allZeroRandomized`: from `SatFree.randomnessHelps` and `allZero`. -/

public section

section

open Groundwork Groundwork.Prog WidthK.Prog UniformInK Paper FreeCode SatFree
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement stSATsplit stTiedTM stTiedThreeTM endFrom eth_and_seth_false
open FromPrinted.SplitSat
open scoped NNReal ENNReal

namespace FromPrinted.FreeCode

/-- **«Theorem 2 gives s_3 = 0»**, for the code that does not depend on k, tied to the machine of
Theorem 2 in its decision form behind the reader: for every δ > 0 there are a polynomial-time reader
of the code, ℓ and τ such that `core3 ℓ τ` behind the reader itself has polynomial-time steps and
decides 3-SAT with the exponent δ, a Turing machine with finite alphabets simulates it with
polynomial overhead, and that Turing machine decides 3-SAT within ⌊c·2^{δn}⌋ steps. This is the
statement `FromPrinted.FreeCode.StTiedThree`. In the proof the named machine has the exponent δ/2. -/
theorem stTiedThree : StTiedThree := fun δ hδ => by
  obtain ⟨ℓ, τ, hp, c₀, hD⟩ := stCore3 (δ / 2) (by positivity)
  obtain ⟨M, c, q, h⟩ := tied_of_decidesW hδ hp hD
  exact ⟨readFree, ℓ, τ, M, c, q, readFree_polyT, reads_readFree, h⟩

/-- **Corollary 5, tied to the reduction**, for the code that does not depend on k: for every k ≥ 3
and δ > 0 there are a polynomial-time reader of the code, τ, ℓ₃ and τ₃ such that the reduction
(sparsify at width k with the threshold parameter τ, split every long clause, ask `core3 ℓ₃ τ₃`)
behind the reader itself has polynomial-time steps and decides k-SAT with the exponent δ, a Turing
machine with finite alphabets simulates it with polynomial overhead, and that Turing machine decides
k-SAT within ⌊c·2^{δn}⌋ steps. This is the statement `FromPrinted.FreeCode.StTied`. With ε = (δ/2)/3
the tree at width k has at most 2^{εn} leaves of at most B·n clauses; the machine of Theorem 2 in
its decision form is taken with the exponent δ₃ = ε/(1 + (k−3)·B). In the proof the named machine
has the exponent δ/2. -/
theorem stTied : StTied := fun k hk δ hδ => by
  have hδ2 : 0 < δ / 2 := by positivity
  obtain ⟨τ, Dd, B, Sk, hsp⟩ := stSparsifyK k hk (δ / 2 / 3) (by positivity)
  have hk3 : (0 : ℝ) ≤ (k : ℝ) - 3 := by
    have : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hpos : (0 : ℝ) < 1 + ((k : ℝ) - 3) * B := by
    have := mul_nonneg hk3 (Nat.cast_nonneg (α := ℝ) B)
    linarith
  have h0 : 0 < δ / 2 / 3 / (1 + ((k : ℝ) - 3) * B) := div_pos (by positivity) hpos
  obtain ⟨ℓ₃, τ₃, hp, c₃, hD⟩ := stCore3 _ h0
  obtain ⟨c₀, hR⟩ := stReduceCore k hk (δ / 2) hδ2 τ Dd B Sk hsp (core3 ℓ₃ τ₃) _ c₃ h0.le (le_of_eq (div_mul_cancel₀ _ hpos.ne')) hD
  obtain ⟨M, c, q, h⟩ := tied_of_decidesW hδ (reduceCore_polyTimeSteps (certStep (thetaU τ) k) hp) hR
  exact ⟨readFree, τ, ℓ₃, τ₃, M, c, q, readFree_polyT, reads_readFree, h⟩

/-- **Corollary 5 from the two tied statements**, which are hypotheses here: «s_k = 0 for every k ≥ 3.
Hence s_∞ = 0, and both ETH and SETH are false», for the numbers s_k defined with the code that does
not depend on k. At k = 3 the Turing machine is that of `StTiedThree` («Theorem 2 gives s_3 = 0»),
at k > 3 that of `StTied` (the reduction); then the general `SatFree.s_eq_zero_of`. Nothing else is
known of the machines. -/
theorem allZeroFrom : StTiedThree → StTied → SatFree.AllZero := fun hT3 hT => by
  -- «s_k = 0 for every k ≥ 3»
  have hs : ∀ k : ℕ, 3 ≤ k → s k = 0 := fun k hk => s_eq_zero_of fun δ hδ => by
    rcases Nat.eq_or_lt_of_le hk with rfl | -
    · obtain ⟨_, _, _, M, c, _, -, -, hfin, -, -, -, h⟩ := hT3 (δ : ℝ) hδ
      exact ⟨M, c, hfin, h⟩
    · obtain ⟨_, _, _, _, M, c, _, -, -, hfin, -, -, -, h⟩ := hT k hk (δ : ℝ) hδ
      exact ⟨M, c, hfin, h⟩
  -- «Hence s_∞ = 0»: s_∞ is the supremum of the s_k, k ≥ 3.
  have hInf : sInfty = 0 := by
    unfold sInfty
    simp only [ENNReal.iSup_eq_zero]
    exact hs
  refine ⟨hs, hInf, fun h => ?_, fun h => ?_⟩
  · -- «Theorem 2 gives s_3 = 0, which is the negation of ETH»
    have := h 3 le_rfl
    rw [hs 3 le_rfl] at this
    exact lt_irrefl _ this
  · -- SETH is the statement s_∞ = 1, and 0 ≠ 1.
    have h' : sInfty = 1 := h
    rw [hInf] at h'
    exact zero_ne_one h'

/-- **Corollary 5**: «s_k = 0 for every k ≥ 3. Hence s_∞ = 0, and both ETH and SETH are false», for
the numbers s_k defined with the code that does not depend on k. It is `allZeroFrom` applied to
`stTiedThree` (Theorem 2) and `stTied` (the reduction). -/
theorem allZero : AllZero := allZeroFrom stTiedThree stTied

/-- «and Corollary 5 holds under each of these conventions»: with randomized algorithms with error
at most p, for every p ≥ 0, s_k = 0 for every k ≥ 3. -/
theorem allZeroRandomized : AllZeroRandomized := fun p hp k hk =>
  le_antisymm ((randomnessHelps p hp k).trans (le_of_eq (allZero.1 k hk))) bot_le

end FromPrinted.FreeCode

end
