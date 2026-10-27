/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.Level.End
public import Eight.SecProof_Network
public import CountKSat.Value
import all StepMachines.Prog.Count

/-! # Lemmas for the section «Proof of Theorem 2» (Section 6 of the paper)

The file is named after its counterpart proof/networks/Paper/SecProof_Proof.lean. It holds one
definition and three small lemmas for the proof of Theorem 2.

What that proof takes from Lemma 4: the deciding form of the step «it suffices to compute the number
of satisfying assignments of a 3-CNF Φ on n variables with m ≤ Mn clauses, in time O(2^{δ'm})», with
Lemma 4 in its form for deciding, is the statement `SufficesSparse δ M S`, a property of a constant
M and of a construction S of machines.
For the paragraph «Constants and reduction»: δ' = δ/(3M) ≤ 1/3 for δ ≤ 1 and M ≥ 1, and a K ≥ 72/δ'
is at least 2. Finally, a machine that decides 3-SAT within c·2^{δn} steps does so for every larger
δ. -/

public section

namespace Eight

open Groundwork Groundwork.Prog Paper

/-! ## What the proof of Theorem 2 takes from Lemma 4 -/

/-- The deciding form, as used for Theorem 2 in its decision form, of «it suffices to compute the
number of satisfying assignments of a 3-CNF Φ on n variables with m ≤ Mn clauses, in time
O(2^{δ'm})», δ' = δ/(3M), as a property of the constant M and of a construction S of machines:
whenever the step machine `Mc` returns, for every formula Φ
with m clauses of at most 3 literals, within A·2^{δ'm} steps an integer that is positive exactly if
Φ is satisfiable, the machine `S Mc` decides 3-SAT on n variables within c·2^{δn} steps; and the
steps of `S Mc` are polynomial time if those of `Mc` are.
Different from the paper: `Mc` is asked to work for every m, not only for m ≤ Mn; there is no «plus
a polynomial in n»: steps are counted, and a step may take time polynomial in the size of Φ; the
states of `Mc` must have polynomial size. -/
@[expose] def SufficesSparse (δ M : ℝ) (S : StepMachine Formula ℤ → StepMachine (List Bool) Bool) : Prop :=
  (∀ Mc : StepMachine Formula ℤ, PolyTimeSteps Mc → PolyTimeSteps (S Mc)) ∧
  ∀ (Mc : StepMachine Formula ℤ) (A : ℕ),
    (∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) →
      ∃ (T : ℕ) (v : ℤ), Mc.Runs Φ T (A * size Φ ^ A) v ∧ (0 < v ↔ Φ.Sat) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ / (3 * M) * Φ.length)) →
    Paper.DecidesInSteps (S Mc) δ

/-! ## Lemmas for the proof of Theorem 2 -/

/-- «Let … δ' = δ/(3M) ≤ 1/3», for δ ≤ 1 and M ≥ 1. -/
theorem delta'_le {δ M : ℝ} (hδ1 : δ ≤ 1) (hM : 1 ≤ M) : δ / (3 * M) ≤ 1 / 3 := by
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- A number K ≥ 72/δ' with δ' ≤ 1/3 is at least 2 (even at least 216), as the definition of
«achievable» in the paper asks. -/
theorem two_le_of_le {δ' : ℝ} {K : ℕ} (hδ' : 0 < δ') (h3 : δ' ≤ 1 / 3) (hK : 72 / δ' ≤ K) : 2 ≤ K := by
  have h1 : (2 : ℝ) ≤ 72 / δ' := by rw [le_div_iff₀ hδ']; linarith
  exact_mod_cast h1.trans hK

/-- A machine that decides 3-SAT within c·2^{δn} steps does so within c·2^{δ₁n} steps for every δ₁ ≥
δ. -/
theorem decidesInSteps_mono {Ms : StepMachine (List Bool) Bool} {δ δ₁ : ℝ} (h : Paper.DecidesInSteps Ms δ) (hle : δ ≤ δ₁) : Paper.DecidesInSteps Ms δ₁ := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun n φ hφ => ?_⟩
  obtain ⟨T, b, h1, h2, h3⟩ := hc n φ hφ
  refine ⟨T, b, h1, h2, h3.trans ?_⟩
  gcongr
  norm_num

end Eight
