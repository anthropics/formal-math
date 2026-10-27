/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.Count
import Mathlib.Tactic

/-! # The proof of Theorem 2 in Section 6, and Algorithm 1, from `Printed.Achievable` (Definition 4 with a bound on the sizes of the states)

Section 6, «Constants and reduction» and «Cost». What is taken as a hypothesis in each theorem is
named in its statement: «it suffices …» in its deciding form (`Suffices.StSuffices`) and Lemma 4 as
an enumeration (`Enumerate.StEnumeration`), which are proved in proof/threesat/Suffices/ and
proof/threesat/Enumerate/; Lemma 1 for the algorithm of its proof (`StGroupingTied`,
`StGroupingPoly`, `StOnProcedures`) and «(K_ℓ, e_ℓ) is achievable» (`StClique`), which are proved in
this folder.
* `stProofNamed_of`: the proof of Section 6 for ANY machine that does what Definition 4 asks for (K,
  δ'/12);
* `stAlgorithm_of`: Sat(ℓ, τ) decides 3-SAT within c·2^{δn} steps, ℓ the first level with K_ℓ ≥
  72/δ' and e_ℓ ≤ δ'/12 (the header of Algorithm 1); `stDecides_of`: the same for every δ > 0;
* `threeSat_through_eStar_of`, `threeSat_by_algorithm_of`: Theorem 2 for Turing machines of Mathlib,
  in the two ways. -/

public section

namespace Printed

open Groundwork Groundwork.Prog Eight Eight.SecNetworks Paper QueryMachines

/-- Since Φ is satisfiable if and only if Z > 0: a machine that counts within A·2^{δ'm} steps does
what the deciding form of the paper's reduction asks: decide whether a 3-CNF Φ with m ≤ Mn clauses
is satisfiable, in time O(2^{δ'm}) plus a polynomial in n. -/
theorem decidesSparse_of_cost {δ' : ℝ} {M A : ℕ} {Mc : StepMachine Formula ℤ}
    (h : ∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) → ∃ T : ℕ, Mc.Runs Φ T (A * size Φ ^ A) (numSat Φ) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length)) :
    Suffices.DecidesSparse δ' M Mc A := by
  intro n Φ hΦ _
  obtain ⟨T, hr, hT⟩ := h Φ fun C hC => (hΦ C hC).2.1
  exact ⟨T, _, hr.mono le_rfl (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_add_right _ _) _)), by rw [Nat.cast_pos]; exact Eight.numSat_pos_iff Φ,
    hT.trans (le_add_of_nonneg_right (by positivity))⟩

/-- **The proof of Theorem 2 in Section 6, from the printed definition.** Let 0 < δ ≤ 1, M = M(δ/3)
and τ the constant and the parameter of Lemma 4, δ' = δ/(3M) ≤ 1/3, K ≥ 72/δ', g = 3K⁸. For any
machine that does what Definition 4 asks for (K, δ'/12): Lemma 1 for the algorithm of its proof; the
network of Φ and «Cost»; «it suffices …». -/
theorem stProofNamed_of (hS : Suffices.StSuffices) (hG : StGroupingTied) (hGp : StGroupingPoly) (hOn : StOnProcedures) : StProofNamed := by
  intro δ Mc τ K M Cc hδ hδ1 hM hEn hK hp hA
  have hM' : (1 : ℝ) ≤ Mc := by exact_mod_cast hM
  -- «Let … δ' = δ/(3M) ≤ 1/3.»
  have hδ' : 0 < δ / (3 * (Mc : ℝ)) := div_pos hδ (by linarith)
  have h3 := Eight.delta'_le hδ1 hM'
  have hK2 := Eight.two_le_of_le hδ' h3 hK
  -- Lemma 1 for (K, δ'/12)
  obtain ⟨C₁, hC₁⟩ := hG K _ M Cc hK2 (by positivity) hA
  have hg : 0 < 3 * K ^ 8 := Nat.mul_pos (by norm_num) (pow_pos (by omega) 8)
  -- the network of Φ and the paragraph «Cost»
  obtain ⟨A, hA'⟩ := cost_of_bound hδ' (by linarith) hg hK (onFormula hOn hg 3 hC₁)
  -- «By Lemma 4 with ε = δ/3, it suffices …», «so the total time is O(2^{δn})»
  have hs := hS δ Mc τ hδ hM hEn
  exact ⟨hs.1 _ (onFormula_poly _ 3 _ (hGp _ _ _ hp)), hs.2 _ A (decidesSparse_of_cost hA')⟩

/-- **Algorithm 1 decides 3-SAT, with the constants of its header**: ε = δ/3, M and τ from Lemma 4,
δ' = δ/(3M), and ℓ the first level with K_ℓ ≥ 72/δ' and e_ℓ ≤ δ'/12. From «it suffices …» in its
deciding form and «Cost» for Count. -/
theorem stAlgorithm_of (hS : Suffices.StSuffices) (hCC : StCountCost) : StAlgorithm := by
  intro δ Mc τ hδ' hδ hδ1 hM hE
  have hM' : (1 : ℝ) ≤ Mc := by exact_mod_cast hM
  have h3 := Eight.delta'_le hδ1 hM'
  obtain ⟨hK, hLe⟩ := Eight.Level.firstLevel_spec hδ'
  obtain ⟨hp, A, hA⟩ := hCC _ (Eight.Level.firstLevel hδ') hδ' (by linarith) hK hLe
  have hs := hS δ Mc τ hδ hM hE
  exact ⟨hs.1 _ hp, hs.2 _ A (decidesSparse_of_cost hA)⟩

/-- **Theorem 2 in its decision form for step machines, with the machine named.** «We may assume δ ≤
1»: the machine for min(δ, 1) serves. From Algorithm 1 with the constants of its header and Lemma 4. -/
theorem stDecides_of (hAlg : StAlgorithm) (hEn : Enumerate.StEnumeration) : StDecides := by
  intro δ hδ
  have hδ₀ : 0 < min δ 1 := lt_min hδ one_pos
  obtain ⟨M, τ, hM, hE⟩ := hEn (min δ 1 / 3) (by linarith)
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hδ' : 0 < min δ 1 / (3 * (M : ℝ)) := div_pos hδ₀ (by linarith)
  obtain ⟨hp, hd⟩ := hAlg (min δ 1) M τ hδ' hδ₀ (min_le_right _ _) hM hE
  exact ⟨_, τ, hp, Eight.decidesInSteps_mono hd (min_le_left _ _)⟩

/-- **Theorem 2 in its decision form by the proof of Section 6**: «Since e* = 0 < δ'/12 and
achievability is monotone in e (Definition 4), (K, δ'/12) is achievable for infinitely many K. Fix
such a K ≥ 72/δ'». The bound in steps is proved for δ/2, and the polynomial cost of a step is paid
at the end (`Paper.steps_to_time`). -/
theorem threeSat_through_eStar_of (hEta : StEveryEta) (hEn : Enumerate.StEnumeration) (hPN : StProofNamed) : Sat3.ThmEveryDelta := by
  intro δ hδ
  have hδ₀ : 0 < min (δ / 2) 1 := lt_min (by linarith) one_pos
  obtain ⟨M, τ, hM, hE⟩ := hEn (min (δ / 2) 1 / 3) (by linarith)
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hδ' : 0 < min (δ / 2) 1 / (3 * (M : ℝ)) := div_pos hδ₀ (by linarith)
  obtain ⟨K, hK, _, _, Mq, Cc, hp, hA⟩ := hEta (min (δ / 2) 1 / (3 * (M : ℝ)) / 12) (by linarith) ⌈72 / (min (δ / 2) 1 / (3 * (M : ℝ)))⌉₊
  have hKδ : 72 / (min (δ / 2) 1 / (3 * (M : ℝ))) ≤ K := (Nat.le_ceil _).trans (by exact_mod_cast hK)
  obtain ⟨h1, h2⟩ := hPN (min (δ / 2) 1) M τ K Mq Cc hδ₀ (min_le_right _ _) hM hE hKδ hp hA
  exact steps_to_time hδ _ h1 (Eight.decidesInSteps_mono h2 (min_le_left _ _))

/-- **Theorem 2 in its decision form by Algorithm 1**: a Turing machine of Mathlib simulates Sat(ℓ,
τ). -/
theorem threeSat_by_algorithm_of (h : StDecides) : Sat3.ThmEveryDelta := fun δ hδ =>
  have ⟨_, _, hp, hd⟩ := h (δ / 2) (by linarith)
  steps_to_time hδ _ hp hd

end Printed
