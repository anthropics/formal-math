/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Exits.AlgDefs
import Eight.ViaGrouping.Count
import Eight.SecLevel_EStar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Algorithm 1 decides 3-SAT, and the two proofs of Theorem 2: the implications

Proof of Theorem 2, «Constants and reduction»: «We may assume δ ≤ 1. Let M = M(δ/3) and δ' = δ/(3M)
≤ 1/3. Since e* = 0 < δ'/12 and achievability is monotone in e (Definition 4), (K, δ'/12) is
achievable for infinitely many K. Fix such a K ≥ 72/δ' and put g = 3K⁸ … By Lemma 4 with ε = δ/3, …
it suffices to compute the number of satisfying assignments of a 3-CNF Φ on n variables with m ≤ Mn
clauses, in time O(2^{δ'm}) plus a polynomial in n.» This file uses the reduction for deciding: it
suffices to decide whether such a Φ is satisfiable within that time.
Header of Algorithm 1: «For Theorem 2, ε = δ/3, δ' is as in Section 6, and ℓ is the first level with
K_ℓ ≥ 72/δ' and e_ℓ ≤ δ'/12.»
This file proves five implications of proof/threesat/Exits/AlgDefs.lean, each from its hypotheses.
* `stAlgorithmOf`: Algorithm 1 with the constants of its header, from «it suffices», read for
  deciding, and «Cost» for Count.
* `stProofNamedOf`: the proof of Section 6 for a named machine, from «it suffices», Lemma 1 for the
  algorithm of its proof and its polynomial-time steps; the paragraph «Cost» is generic in the
  algorithm for networks (`Eight.ViaGrouping.count_cost_pos_of`).
* `stDecidesOf`: Theorem 2 for step machines with the machine named, from Algorithm 1 and Lemma 4 as
  an enumeration; «We may assume δ ≤ 1»: the machine for min(δ, 1) serves.
* `stThroughEStarOf`: Theorem 2 by the proof of Section 6.
* `stByAlgorithmOf`: Theorem 2 by Algorithm 1.
`decidesSparse_of` is a step inside the proofs of the first two, not a statement of AlgDefs.lean.
In the last two the bound in steps is taken at δ/2, and the polynomial cost of a step is paid at the
end (`Paper.steps_to_time`); the paper counts operations. -/

public section

namespace Exits

open Groundwork Groundwork.Prog Groundwork.Stepped Paper Eight Eight.SecNetworks Eight.ViaGrouping Suffices Enumerate

/-- A machine that decides every 3-CNF with m clauses within A·2^{δ'm} steps does what the reduction
of the proof of Theorem 2, read for deciding, asks (to decide whether a 3-CNF Φ with m ≤ Mn clauses
is satisfiable, in time O(2^{δ'm}) plus a polynomial in n): the sentence asks for less. -/
theorem decidesSparse_of {δ' : ℝ} {M : ℕ} {Mc : StepMachine Formula ℤ} {A : ℕ}
    (h : ∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) → ∃ (T : ℕ) (v : ℤ), Mc.Runs Φ T (A * size Φ ^ A) v ∧ (0 < v ↔ Φ.Sat) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length)) :
    DecidesSparse δ' M Mc A := by
  intro n Φ hΦ _
  obtain ⟨T, v, hrun, hv, hT⟩ := h Φ fun C hC => (hΦ C hC).2.1
  refine ⟨T, v, hrun.mono le_rfl (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_add_right _ _) _)), hv, hT.trans ?_⟩
  have : (0 : ℝ) ≤ A * ((n : ℝ) + 1) ^ A := by positivity
  linarith

/-- **Algorithm 1 decides 3-SAT, with the constants of its header**: «For Theorem 2, ε = δ/3, δ' is
as in Section 6, and ℓ is the first level with K_ℓ ≥ 72/δ' and e_ℓ ≤ δ'/12.» From «it suffices»,
read for deciding, and «Cost» for Count; Φ is satisfiable if and only if Z > 0. -/
theorem stAlgorithmOf : StAlgorithmOf := by
  intro hS hC δ M τ hδ' hδ hδ1 hM hEn
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  obtain ⟨hK, hE⟩ := Level.firstLevel_spec hδ'
  have h3 := delta'_le hδ1 hMR
  obtain ⟨hp, A, hA⟩ := hC (δ / (3 * (M : ℝ))) (Level.firstLevel hδ') hδ' (by linarith) hK hE
  obtain ⟨s1, s2⟩ := hS δ M τ hδ hM hEn
  refine ⟨s1 _ hp, s2 _ A (decidesSparse_of fun Φ hΦ => ?_)⟩
  obtain ⟨T, hrun, hT⟩ := hA Φ hΦ
  exact ⟨T, _, hrun, by rw [Nat.cast_pos]; exact numSat_pos_iff Φ, hT⟩

/-- **The proof of Theorem 2 in Section 6, for a named machine**: «Fix such a K ≥ 72/δ' and put g =
3K⁸ … By Lemma 4 with ε = δ/3, … it suffices to compute the number of satisfying assignments of a
3-CNF Φ on n variables with m ≤ Mn clauses, in time O(2^{δ'm}) plus a polynomial in n.» From «it
suffices», read for deciding, Lemma 1 for the algorithm of its proof, and its polynomial-time steps. -/
theorem stProofNamedOf : StProofNamedOf := by
  intro hS hL hKp δ M τ K E hδ hδ1 hM hEn hK hEk hE
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hδ' : 0 < δ / (3 * (M : ℝ)) := by positivity
  have h3 := delta'_le hδ1 hMR
  have hK2 := two_le_of_le hδ' h3 hK
  -- Lemma 1 for (K, δ'/12), and the paragraph «Cost»
  obtain ⟨A, hA⟩ := ViaGrouping.count_cost_pos_of hδ' (by linarith) (by positivity) hK (hL K _ E hK2 (by positivity) hE)
  obtain ⟨s1, s2⟩ := hS δ M τ hδ hM hEn
  exact ⟨s1 _ (count_isPolyT (hKp K _ E hEk) _ 3), s2 _ A (decidesSparse_of hA)⟩

/-- **Theorem 2 in its decision form for step machines, with the machine named.** From Algorithm 1
with the constants of its header and Lemma 4 as an enumeration. «We may assume δ ≤ 1»: the machine
for min(δ, 1) serves. «Let M = M(δ/3)». -/
theorem stDecidesOf : StDecidesOf := by
  intro hA hEn δ hδ
  have hδ₀ : 0 < min δ 1 := lt_min hδ one_pos
  obtain ⟨M, τ, hM, hE⟩ := hEn (min δ 1 / 3) (by positivity)
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hδ' : 0 < min δ 1 / (3 * (M : ℝ)) := by positivity
  obtain ⟨h1, h2⟩ := hA (min δ 1) M τ hδ' hδ₀ (min_le_right _ _) hM hE
  exact ⟨Level.firstLevel hδ', τ, h1, decidesInSteps_mono h2 (min_le_left _ _)⟩

/-- **Theorem 2 in its decision form by the proof of Section 6**, sentence by sentence (the comments
quote the paper), from e* = 0, Lemma 4 as an enumeration, and the proof for a named machine. -/
theorem stThroughEStarOf : StThroughEStarOf := by
  intro h0 hEn hP δ hδ
  -- «We may assume δ ≤ 1.» (The bound in steps is taken at δ/2.)
  have hd : 0 < min (δ / 2) 1 := lt_min (by positivity) one_pos
  -- «Let M = M(δ/3) and δ' = δ/(3M) ≤ 1/3.» (with min(δ/2, 1) in the place of δ)
  obtain ⟨M, τ, hM, hE⟩ := hEn (min (δ / 2) 1 / 3) (by positivity)
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hδ' : 0 < min (δ / 2) 1 / (3 * (M : ℝ)) := by positivity
  -- «Since e* = 0 < δ'/12 and achievability is monotone in e (Definition 4), (K, δ'/12) is
  -- achievable for infinitely many K. Fix such a K ≥ 72/δ' and put g = 3K⁸; …»
  have hstar : eStar < min (δ / 2) 1 / (3 * (M : ℝ)) / 12 := by rw [h0]; positivity
  obtain ⟨K, hK, E, hEk, hEw⟩ := achievable_of_eStar_lt hstar ⌈72 / (min (δ / 2) 1 / (3 * (M : ℝ)))⌉₊
  have hKδ : 72 / (min (δ / 2) 1 / (3 * (M : ℝ))) ≤ K := (Nat.le_ceil _).trans (by exact_mod_cast hK)
  -- «By Lemma 4 with ε = δ/3, it suffices …», the network of Φ, «Cost», «so the total time is
  -- O(2^{δn})»
  obtain ⟨p1, p2⟩ := hP (min (δ / 2) 1) M τ K E hd (min_le_right _ _) hM hE hKδ hEk hEw
  exact steps_to_time hδ _ p1 (decidesInSteps_mono p2 (min_le_left _ _))

/-- **Theorem 2 in its decision form by Algorithm 1**: «For every δ > 0 there is a deterministic
algorithm that computes the number of satisfying assignments of a 3-CNF on n variables, with any
number of clauses, in time O(2^{δn}).» Here in the deciding form. A Turing machine of Mathlib
simulates Sat(ℓ, τ), for the ℓ and τ that belong to δ/2. -/
theorem stByAlgorithmOf : StByAlgorithmOf := by
  intro h δ hδ
  obtain ⟨ℓ, τ, h1, h2⟩ := h (δ / 2) (by positivity)
  exact steps_to_time hδ _ h1 h2

end Exits
