/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.LevelCost
public import Eight.SecPseudocode_Levels
import Mathlib.Tactic

/-! # Proposition 3 from the printed Definition 4

Proposition 3: «If (K, e) is achievable and g = 3K⁸, then (g², e') is achievable for e' = (ρ + 2/K)e +
2/K. Hence e* = 0.» «Achievable» is `Printed.Achievable`: a table query costs one operation.
The first sentence is `StLevelTied` (the bound, for the algorithm of the proof) together with
`StLevelPoly` (polynomial-time steps). The second sentence follows the last paragraph of the printed
proof sentence by sentence, as proof/networks/Eight/SecLevel_EStar.lean does for «achievable» as
defined in the namespace `Paper`.
Then Section 8: «By brute force and Proposition 3, (K_ℓ, e_ℓ) is achievable for every ℓ», by
Clique(ℓ). The statements about the algorithm (`StLevelTied`, `StLevelPoly`, `StBrute`) are
hypotheses of the theorems `…_of` here; the facts on e* and «if (K, e) is achievable, so is (K, e₁)
for every e₁ ≥ e» are those of proof/threesat/Printed/Achievable.lean. -/

public section

namespace Printed

open Eight Paper QueryMachines

/-- **Proposition 3**, first sentence, from the two statements about the algorithm of its proof. -/
theorem levelProposition_of (hT : StLevelTied) (hP : StLevelPoly) : LevelProposition := by
  intro K e hA
  obtain ⟨hK, h0, M, Cc, hp, hM⟩ := hA
  obtain ⟨Cc', h⟩ := hT K e M Cc hK h0 hM
  refine ⟨?_, ?_, levelMachine K (3 * K ^ 8) M, Cc', hP K (3 * K ^ 8) M hp, h⟩
  · have h1 : 1 ≤ K ^ 8 := Nat.one_le_pow _ _ (by omega)
    have h2 : 3 * K ^ 8 ≤ (3 * K ^ 8) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  · have hρ : (0 : ℝ) < rho := by unfold rho; norm_num
    positivity

/-- «Let e > e*; then (K, e) is achievable for infinitely many K. Let e'' > ρe. For all large K we
have (ρ + 2/K)e + 2/K ≤ e'', so (9K¹⁶, e'') is achievable for infinitely many K, and therefore e* ≤
e''.» «Large» is K ≥ (2e + 2)/(e'' − ρe); 9K¹⁶ is written (3K⁸)². -/
theorem eStar_le_of (hP3 : LevelProposition) {e e'' : ℝ} (he : eStar < e) (he'' : rho * e < e'') : eStar ≤ e'' := by
  have hs0 := eStar_nonneg
  have h0 : 0 ≤ e := by linarith
  have hd : 0 < e'' - rho * e := by linarith
  refine eStar_le fun K₀ => ?_
  obtain ⟨K, hK, hA⟩ := achievable_of_eStar_lt he (max K₀ (max 2 ⌈(2 * e + 2) / (e'' - rho * e)⌉₊))
  have hK0 : K₀ ≤ K := (le_max_left _ _).trans hK
  have hK2 : 2 ≤ K := ((le_max_left _ _).trans (le_max_right _ _)).trans hK
  have hKd : (2 * e + 2) / (e'' - rho * e) ≤ K :=
    (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans (le_max_right _ _)).trans hK)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hsmall : (2 * e + 2) / (K : ℝ) ≤ e'' - rho * e := by
    rw [div_le_iff₀ hd] at hKd
    rw [div_le_iff₀ hKpos]
    linarith
  have hexp : (rho + 2 / K) * e + 2 / K ≤ e'' := by
    have : (rho + 2 / K) * e + 2 / K = rho * e + (2 * e + 2) / (K : ℝ) := by ring
    linarith
  refine ⟨(3 * K ^ 8) ^ 2, ?_, stMono _ _ _ (hP3 K e hA) hexp⟩
  have h1 : K ≤ K ^ 8 := Nat.le_self_pow (by norm_num) K
  have h2 : 3 * K ^ 8 ≤ (3 * K ^ 8) ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

/-- «Letting e'' → ρe and e → e* gives e* ≤ ρe*.» Here: for every η > 0, take e = e* + η/2 and e'' =
ρe + η/2, which is at most ρe* + η. -/
theorem eStar_le_rho_mul_of (hP3 : LevelProposition) : eStar ≤ rho * eStar := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  have h1 : eStar ≤ rho * (eStar + η / 2) + η / 2 := eStar_le_of hP3 (e := eStar + η / 2) (by linarith) (by linarith)
  have h2 : rho * (η / 2) ≤ 1 * (η / 2) := mul_le_mul_of_nonneg_right (by unfold rho; norm_num) (by linarith)
  linarith

/-- **Proposition 3**, second sentence: e* = 0. «Since 0 ≤ e* ≤ 1/2 and ρ < 1, e* = 0.» (e* ≤ 1/2 is
not needed.) -/
theorem eStarZero_of (hP3 : LevelProposition) : EStarZero := by
  have h1 := eStar_le_rho_mul_of hP3
  have h2 := eStar_nonneg
  have h3 : rho < 1 := by unfold rho; norm_num
  unfold EStarZero
  nlinarith

/-- The last sentence of the proof of Proposition 3: «That is, for every η > 0, (K, η) is achievable
for infinitely many K.» -/
theorem stEveryEta_of (h : EStarZero) : StEveryEta := fun η hη K₀ =>
  achievable_of_eStar_lt (by rw [show eStar = 0 from h]; exact hη) K₀

/-- **Section 8: «By brute force and Proposition 3, (K_ℓ, e_ℓ) is achievable for every ℓ»**, by
Clique(ℓ). -/
theorem stClique_of (hB : StBrute) (hT : StLevelTied) (hP : StLevelPoly) : StClique := by
  intro ℓ
  induction ℓ with
  | zero => exact hB (levelK 0) (le_trans (by norm_num) (levelK_ge 0))
  | succ ℓ ih =>
    obtain ⟨hp, Cc, hM⟩ := ih
    obtain ⟨Cc', h⟩ := hT (levelK ℓ) (Level.levelE ℓ) (CLIQUE ℓ) Cc (le_trans (by norm_num) (levelK_ge ℓ)) (Level.levelE_nonneg ℓ) hM
    have e1 : levelK (ℓ + 1) = (3 * levelK ℓ ^ 8) ^ 2 := by
      simp only [levelK]
      ring
    refine ⟨hP _ _ _ hp, Cc', ?_⟩
    rw [e1]
    exact h

end Printed
