/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SplitCount.Defs
import SplitCount.Sizes
import Occ.Main
import Eight.ViaGrouping.Count
import Eight.ViaGrouping.LemGrouping
import Eight.ViaGrouping.Alg
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! # Proof of Corollary 6 at k = 3 (here called step 1): Theorem 2 counts

For every δ' > 0, the proof of Theorem 2 (Section 6), with K and g chosen from δ' as there (we may
assume δ' ≤ 1), computes Z, and hence the number Z·2^{n'} of satisfying assignments of a 3-CNF with
m ≥ 1 clauses in which n' of the n variables do not occur, in time O(2^{δ'm}) plus a polynomial in
n; with no clauses the number is 2^n.
* `stStepOneFor`: the number Z·2^{n'} of satisfying assignments, for every machine that computes Z:
  one more step, which multiplies by 2^{n'} (`Occ.timesFree`); that the product is the number of
  satisfying assignments is `Occ.stCountOcc`.
* `stComputesZ`: the proof of Theorem 2 computes Z: Lemma 1 for the algorithm of its printed proof
  (`Eight.ViaGrouping.stLemGrouping`) and «Cost» of Section 6 (`Eight.ViaGrouping.count_cost_of`).
* `stCountIsNetworkMachine`, `stStepOne`: COUNT of Algorithm 1 at level ℓ is that machine at K = K_ℓ
  with CLIQUE(ℓ). -/

public section

namespace SplitCount

open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ

/-- **Step 1: from Z to the number Z·2^{n'} of satisfying assignments.** If Cnt computes Z as
Section 6 says, with the exponent δ' ≥ 0 and the constant A, then `timesFreeAfter Cnt` does what
step 1 says, with the same exponent and some constant A'. -/
theorem stStepOneFor : StStepOneFor := by
  intro Cnt δ' A hδ' hC
  refine ⟨6 + 1 + A * 1 ^ A + 1 * A, fun n Φ h3 hb => ?_⟩
  obtain ⟨T, r, hT⟩ := hC Φ h3
  obtain ⟨a, ha⟩ : ∃ a : List Unit × Fml, a = (List.replicate n (), Φ) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = n + size Φ + 1 := ⟨_, rfl⟩
  rw [← ha, ← hs]
  -- «Z·2^{n'}» is the number of satisfying assignments
  have hv : timesFree (a, ((Eight.numSat Φ : ℕ) : ℤ)) = cntN n Φ := by
    rw [ha, stCountOcc n Φ hb]
    simp [timesFree]
  have r1 : (Stepped.mapIn Prod.snd Cnt).Runs a T (A * size Φ ^ A) ((Eight.numSat Φ : ℕ) : ℤ) := Stepped.mapIn_runs (by rw [ha]; exact r)
  have r2 := Stepped.ofFun_runs timesFree (a, ((Eight.numSat Φ : ℕ) : ℤ))
  rw [hv] at r2
  have hc2 : cntN n Φ < 2 ^ (n + 1) := (cntN_le n Φ).trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hz2 : Eight.numSat Φ < 2 ^ (n + 1) := by
    refine lt_of_le_of_lt ?_ hc2
    rw [stCountOcc n Φ hb]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have s1 : size a ≤ 2 * s := by
    have := size_unary n
    rw [ha, size_prod]
    show size (List.replicate n ()) + size Φ ≤ _
    omega
  have s2 : size (cntN n Φ) ≤ s + 1 := by have := size_nat_le hc2; omega
  have s3 : size ((Eight.numSat Φ : ℕ) : ℤ) ≤ s + 1 := by
    have := size_nat_le hz2
    rw [size_nat] at this
    rw [size_int, Int.natAbs_natCast]
    omega
  have s4 : A * size Φ ^ A ≤ A * (1 * s ^ 1) ^ A := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by rw [one_mul, pow_one]; omega) A)
  refine ⟨T + 1 + 1, (Stepped.bind_runs r1 r2).mono le_rfl (poly_le (by omega) ?_), ?_⟩
  · have sp : size (a, ((Eight.numSat Φ : ℕ) : ℤ)) = size a + size ((Eight.numSat Φ : ℕ) : ℤ) := size_prod _
    rw [sp, pow_one]
    rw [pow_one] at s4
    omega
  · have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ' * Φ.length) := Real.one_le_rpow one_le_two (by positivity)
    have hcA : (A : ℝ) + 2 ≤ ((6 + 1 + A * 1 ^ A + 1 * A : ℕ) : ℝ) := by
      have : A + 2 ≤ 6 + 1 + A * 1 ^ A + 1 * A := by rw [one_pow]; omega
      exact_mod_cast this
    calc ((T + 1 + 1 : ℕ) : ℝ) = (T : ℝ) + 2 := by push_cast; ring
      _ ≤ (A : ℝ) * (2 : ℝ) ^ (δ' * Φ.length) + 2 * (2 : ℝ) ^ (δ' * Φ.length) := by linarith
      _ = ((A : ℝ) + 2) * (2 : ℝ) ^ (δ' * Φ.length) := by ring
      _ ≤ ((6 + 1 + A * 1 ^ A + 1 * A : ℕ) : ℝ) * (2 : ℝ) ^ (δ' * Φ.length) := mul_le_mul_of_nonneg_right hcA (by positivity)

/-- **The proof of Theorem 2, with K and g chosen from δ' as there, computes Z.** For 0 < δ' ≤ 1, K
≥ 2 with K ≥ 72/δ', g = 3K⁸ and any algorithm E for cliques on K nodes with the exponent δ'/12, the
algorithm of the printed proof of Lemma 1 with E, run on the network of Φ on g clusters, computes Z
as Section 6 says. -/
theorem stComputesZ : StComputesZ := by
  intro δ' h0 h1 K E hK2 hK hE
  have hg : 0 < 3 * K ^ 8 := by
    have : 0 < K := by omega
    positivity
  exact ViaGrouping.count_cost_of h0 h1 hg hK (ViaGrouping.stLemGrouping K (δ' / 12) E hK2 (by positivity) hE)

/-- COUNT of Algorithm 1 at level ℓ is the machine of `StComputesZ` at K = K_ℓ and E = CLIQUE(ℓ):
g_ℓ = 3K_ℓ⁸ by definition. -/
theorem stCountIsNetworkMachine : StCountIsNetworkMachine := fun _ => rfl

/-- **Step 1 for COUNT of Algorithm 1.** For 0 < δ' ≤ 1 and every level ℓ with K_ℓ ≥ 72/δ' and e_ℓ ≤
δ'/12, `countThree ℓ` does what step 1 says. -/
theorem stStepOne : StStepOne := by
  intro δ' h0 h1 ℓ hK hE
  obtain ⟨A, hA⟩ := stComputesZ δ' h0 h1 (levelK ℓ) (CLIQUEp ℓ) (two_le_levelK ℓ) hK ((CLIQUEp_within ℓ).mono hE)
  rw [← stCountIsNetworkMachine ℓ] at hA
  exact stStepOneFor (COUNTp ℓ) δ' A h0.le hA

end SplitCount
