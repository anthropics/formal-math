/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SizeCircuit.CircuitDefs
import SizeCircuit.Circuit
import SizeCircuit.Cert
import SizeCircuit.Sized
import SizeCircuit.SizedCert
import Mathlib.Tactic

/-! # Section 7, proof of Corollary 7: the interface of proof/consequences/GraphProblems/ through Γ

Proofs of `StSizeGates` (CircuitDefs.lean) and of `StCircuitExists`, `StSizedFromEngine`,
`StSizedFromEngines` and `StSizedViaGamma` (Defs.lean). The paper: «All these formulas have O(n)
variables, so Corollary 6, applied with a small enough value in place of δ, gives time O(2^{δn}).»
Here the small enough value is δ/(a+1), where the circuit has at most a·(n+1) gates. -/

public section

namespace SizeCircuit

open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound Eight

/-- **`StSizeGates`.** The circuits `sizeGates n s` test the size with at most 6·(n+1) gates and are
computed in polynomial time. -/
theorem stSizeGates : StSizeGates := ⟨6, testsSize_sizeGates, certGates_sizeGates⟩

/-- **`StCircuitExists`.** There is a family of circuits that tests the size with O(n) gates and is
computed in polynomial time: `sizeGates`. -/
theorem stCircuitExists : StCircuitExists := ⟨sizeGates, 6, testsSize_sizeGates, certGates_sizeGates⟩

/-- **`StSizedFromEngine`.** From Corollary 6 for machines cut into steps: for every family of
circuits that tests the size and is computed in polynomial time, every width w and every δ > 0,
there are a procedure E with polynomial-time steps, an exponent δ_E ≥ 0 with δ_E·(a+1) ≤ δ and a
constant c such that E serves as the procedure for #max(w,3)-SAT with δ_E and c, and
`sizedBy gates E` has polynomial-time steps and does what `GraphProblems.StSized` asks. (The proof
takes δ_E = δ/(a+1).) -/
theorem stSizedFromEngine : StSizedFromEngine := by
  intro hEng gates a hT hC w δ hδ
  have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hd : 0 < δ / ((a : ℝ) + 1) := div_pos hδ ha
  have hle : δ / ((a : ℝ) + 1) * ((a : ℝ) + 1) ≤ δ := le_of_eq (div_mul_cancel₀ δ ha.ne')
  obtain ⟨E, hE, c, hc⟩ := hEng (max w 3) (le_max_of_le_right (by norm_num)) (δ / ((a : ℝ) + 1)) hd
  exact ⟨E, _, c, hE, hd.le, hle, hc, stSizedCert gates hC E hE, stSizedBy gates a hT w δ _ hδ hd.le hle E c hc⟩

/-- **`StSizedFromEngines`.** For every family En k ℓ τ of procedures of which Corollary 6 for
machines cut into steps holds, every family of circuits that tests the size and is computed in
polynomial time, every width w and every δ > 0: for some ℓ and τ the machine
`sizedBy gates (En (max w 3) ℓ τ)` has polynomial-time steps and does what `GraphProblems.StSized`
asks. -/
theorem stSizedFromEngines : StSizedFromEngines := by
  intro En hEn gates a hT hC w δ hδ
  have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hd : 0 < δ / ((a : ℝ) + 1) := div_pos hδ ha
  have hle : δ / ((a : ℝ) + 1) * ((a : ℝ) + 1) ≤ δ := le_of_eq (div_mul_cancel₀ δ ha.ne')
  obtain ⟨ℓ, τ, hP, c, hc⟩ := hEn (max w 3) (le_max_of_le_right (by norm_num)) (δ / ((a : ℝ) + 1)) hd
  exact ⟨ℓ, τ, stSizedCert gates hC _ hP, stSizedBy gates a hT w δ _ hδ hd.le hle _ c hc⟩

/-- **`StSizedViaGamma`.** With the circuits `sizeGates`: from Corollary 6 for machines cut into
steps, the interface `GraphProblems.StSized` of proof/consequences/GraphProblems/; the machine is
`sizedBy sizeGates E`. -/
theorem stSizedViaGamma : StSizedViaGamma := by
  intro hEng w δ hδ
  obtain ⟨E, -, -, -, -, -, -, hP, c', h⟩ := stSizedFromEngine hEng sizeGates 6 testsSize_sizeGates certGates_sizeGates w δ hδ
  exact ⟨sizedBy sizeGates E, hP, c', h⟩

end SizeCircuit
