/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Exits.AlgDefs
import Eight.ViaGrouping.LevelEnd
import Eight.ViaGrouping.GridPsi
import Eight.SecLevel_EStar
import Eight.SecPseudocode_Levels
import ToTuring.Poly.Brute
import Mathlib.Tactic.Ring

/-! # Proposition 3, «Hence e* = 0», and the levels of Section 8, on the algorithm for networks of this folder

Proposition 3: «If (K, e) is achievable and g = 3K⁸, then (g², e') is achievable for e' = (ρ + 2/K)e +
2/K. Hence e* = 0.» Section 8: «By brute force and Proposition 3, (K_ℓ, e_ℓ) is achievable for every
ℓ, …».
This file proves four implications of proof/threesat/Exits/AlgDefs.lean, each from its hypotheses.
* `stLevelUpOf`: Proposition 3, first sentence, for the named algorithm `levelUp K E`, from Lemma 1
  for `Exits.netAlg` and its polynomial-time steps. What one level does with an algorithm for
  networks is generic in that algorithm: `Eight.ViaGrouping.levelAlgP_gridPsi_correct`,
  `levelAlgP_gridPsi_keeps` (proof/networks/Eight/ViaGrouping/LevelEnd.lean).
* `stLevelAchievableOf`: the first sentence as printed, from the form for the named algorithm.
* `stEStarOf`: «Hence e* = 0», by the last paragraph of the printed proof (`Eight.eStar_eq_zero_of`,
  proof/networks/Eight/SecLevel_EStar.lean).
* `stCliqueOf`: Clique(ℓ) has polynomial-time steps and meets the bound of «achievable» for (K_ℓ,
  e_ℓ): level 0 is brute force, and the step from ℓ to ℓ + 1 is the hypothesis at K = K_ℓ, e = e_ℓ. -/

public section

namespace Exits

open Groundwork Groundwork.Prog Paper Eight Eight.SecNetworks Eight.ViaGrouping

/-- K_ℓ ≥ 2 (Section 8: «K₀ = 64 … K_{ℓ+1} = g_ℓ² = 9K_ℓ¹⁶»). -/
theorem two_le_levelK (ℓ : ℕ) : 2 ≤ levelK ℓ := le_trans (by norm_num) (levelK_ge ℓ)

/-- g_ℓ ≥ 1 (Section 8: «g_ℓ = 3K_ℓ⁸»). -/
theorem zero_lt_levelG (ℓ : ℕ) : 0 < levelG ℓ := Nat.mul_pos (by norm_num) (Nat.pow_pos (lt_of_lt_of_le (by norm_num) (levelK_ge ℓ)))

/-- **Proposition 3, first sentence, for the named algorithm**: «If (K, e) is achievable and g =
3K⁸, then (g², e') is achievable for e' = (ρ + 2/K)e + 2/K.» From Lemma 1 for the algorithm of its
proof: «Apply Lemma 1 to the network with the smaller total.» g² is written 9K¹⁶. -/
theorem stLevelUpOf : StLevelUpOf := by
  intro hL hKp K e E hK h0 hk hc
  have hg : K ≤ 3 * K ^ 8 := by
    have : K ≤ K ^ 8 := Nat.le_self_pow (by norm_num) K
    omega
  -- «Apply Lemma 1 to the network with the smaller total.»
  have h2 := levelAlgP_gridPsi_correct stGridPsi hK hg h0 (hL K e E hK h0 hc)
  have e1 : 3 * K ^ 8 * (3 * K ^ 8) = 9 * K ^ 16 := by ring
  rw [e1] at h2
  exact ⟨levelAlgP_gridPsi_keeps stGridPsiPoly _ (hKp K _ E hk), h2⟩

/-- **Proposition 3, first sentence**: «If (K, e) is achievable and g = 3K⁸, then (g², e') is
achievable for e' = (ρ + 2/K)e + 2/K.» From the form for the named algorithm. -/
theorem stLevelAchievableOf : StLevelAchievableOf := fun h K e hK h0 ⟨E, hk, hc⟩ => ⟨levelUp K E, (h K e E hK h0 hk hc).1, (h K e E hK h0 hk hc).2⟩

/-- **Proposition 3, second sentence**: «Hence e* = 0.» From the first sentence, by the last
paragraph of the printed proof. -/
theorem stEStarOf : StEStarOf := fun h => eStar_eq_zero_of fun {K e} hK h0 hA => h K e hK h0 hA

/-- **Section 8**: «By brute force and Proposition 3, (K_ℓ, e_ℓ) is achievable for every ℓ, …», for
Clique(ℓ). -/
theorem stCliqueOf : StCliqueOf := by
  intro h ℓ
  induction ℓ with
  | zero => exact ⟨bruteE_keeps _, bruteE_correct _⟩
  | succ ℓ ih => exact h (levelK ℓ) (Level.levelE ℓ) (CLIQUE ℓ) (two_le_levelK ℓ) (Level.levelE_nonneg ℓ) ih.1 ih.2

end Exits
