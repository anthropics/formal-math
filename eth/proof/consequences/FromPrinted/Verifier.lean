/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FromPrinted.SatDefs
import FromPrinted.Core
import FromPrinted.SplitSat
import Eight.ViaGrouping.CorNSETH
import CountKSat.InOut
import WidthK.Decode

/-! # The sentence on NSETH after Corollary 5: the machines, on `Printed.SAT`, the deciding form of Algorithm 1

«a k-DNF is a tautology exactly if its negation, a k-CNF, is unsatisfiable, and a deterministic
algorithm is in particular a nondeterministic one»
* `stVerifier`: for k ≥ 3 the machine for k-SAT is `FromPrinted.SplitSat.SATsplit`
  (`FromPrinted.SplitSat.stSATsplit`), the reduction to 3-SAT run on the machine of Theorem 2 in its
  decision form; the verifier made from it has polynomial-time steps
  (`Eight.ViaGrouping.verifier_polyTimeSteps`) and returns, on every witness and the code of a k-DNF
  ψ, the bit that says whether ψ is a tautology (`Eight.ViaGrouping.verifier_recognizes`).
* `stSmallWidths`: for 1 ≤ k ≤ 3 the machine is the reader for width k followed by the machine of
  Theorem 2 in its decision form without its reader (`FromPrinted.SplitSat.stCore3`): a k-CNF with k
  ≤ 3 is a 3-CNF.
* `nsethFrom`, `nsethFalse`: «NSETH … is false as well», by `Eight.ViaGrouping.not_NSETH_TM_of`,
  first from the two statements as hypotheses, then on their proofs. -/

public section

section

open Groundwork Groundwork.Prog CountKSat Paper Eight Eight.ViaGrouping
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement
open FromPrinted.SplitSat

namespace FromPrinted.Consequences

/-- **The verifier for tautologies, with the machine named**: for every k ≥ 3 and δ > 0 there are τ,
ℓ₃, τ₃, c such that `SATsplit k τ ℓ₃ τ₃` has polynomial-time steps and decides k-SAT with the
exponent δ and the constant c, and the verifier made from it has polynomial-time steps and, on every
witness w and the code of a k-DNF ψ on n variables, ends within c·2^{δn} steps, on states of size at
most c·(length of the code + 1)^c, with the bit that says whether ψ is a tautology. -/
theorem stVerifier : StVerifier := by
  intro k hk δ hδ
  obtain ⟨τ, ℓ₃, τ₃, hp, c, hc⟩ := stSATsplit k hk δ hδ
  exact ⟨τ, ℓ₃, τ₃, c, hp, hc, verifier_polyTimeSteps hp, verifier_recognizes hc⟩

/-- For 1 ≤ k ≤ 3 and δ > 0 there are ℓ, τ, c such that `SATsmall k ℓ τ` has polynomial-time steps
and decides k-SAT with the exponent δ and the constant c. -/
theorem stSmallWidths : StSmallWidths := by
  intro k hk hk3 δ hδ
  obtain ⟨ℓ, τ, ⟨hI⟩, c, hc⟩ := stCore3 δ hδ
  refine ⟨ℓ, τ, c, ⟨IsPolyT.mapIn (M := core3 ℓ τ) (stCertDecU k)⟩, fun n φ h3 => ?_⟩
  have hw : ∀ C ∈ Decode.toN φ, C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n := by
    intro C hC
    obtain ⟨⟨D, hD, hl⟩, h⟩ := Decode.mem_toN hC
    exact ⟨hl ▸ (h3.1 D hD).trans hk3, h⟩
  have hnd : (Decode.toN φ).Nodup := by
    refine List.Nodup.map (List.map_injective_iff.2 fun a b hab => ?_) h3.2
    exact Prod.ext (Fin.ext (Prod.ext_iff.1 hab).1) (Prod.ext_iff.1 hab).2
  obtain ⟨T, b, r, hb, hT⟩ := hc n (Decode.toN φ) hw hnd
  refine ⟨T, b, (Stepped.mapIn_runs (by rw [stDecU k n φ hk h3.1]; exact r)).mono le_rfl ?_, hb.trans (Decode.satN_toN φ), hT⟩
  have hlen := DecodeK.length_enc k φ
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) c)

/-- **«NSETH … is false as well»** (the sentence after Corollary 5), for Turing machines and
nondeterministic time in verifier form (`Eight.NSETH_TM`), from the two statements that name the
machines, as hypotheses: the machine for k-SAT is that of `StSmallWidths` for k ≤ 3 and that of
`StVerifier` for k > 3. -/
theorem nsethFrom (hV : StVerifier) (hS : StSmallWidths) : NsethFalse := by
  refine not_NSETH_TM_of fun k hk δ hδ => ?_
  by_cases h3 : k ≤ 3
  · obtain ⟨ℓ, τ, c, hp, hc⟩ := hS k hk h3 δ hδ
    exact ⟨_, hp, c, hc⟩
  · obtain ⟨τ, ℓ₃, τ₃, c, hp, hc, -, -⟩ := hV k (by omega) δ hδ
    exact ⟨_, hp, c, hc⟩

/-- **«NSETH … is false as well»**: `nsethFrom` on the proofs `stVerifier` and `stSmallWidths`. -/
theorem nsethFalse : NsethFalse := nsethFrom stVerifier stSmallWidths

end FromPrinted.Consequences

end
