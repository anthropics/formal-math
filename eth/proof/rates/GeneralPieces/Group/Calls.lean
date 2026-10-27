/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Group.Lemma

/-! # The lemma on groupings with explicit cost: two sizes

`groupingSizes`: the last sentence of the proof of Lemma 8, the lemma on groupings with explicit
cost, «K ≤ g in both cases and L ≤ gP + 1». -/

public section

namespace GeneralPieces

open Finset Groundwork Groundwork.Prog PaddedDescent.F AppRunningTime

/-- «K ≤ g in both cases and L ≤ gP + 1». (L ≤ gP holds too, because U ≤ gP, ζ ≤ 1 and K² ≥ 4, but
is not needed and not proved here.) -/
theorem groupingSizes : GroupingSizes := by
  intro K g ζ P c hK hg hζ0 hζ1 hP hrow hcase
  constructor
  · rcases hcase with ⟨rfl, -⟩ | ⟨hd, -⟩
    · calc K ≤ K ^ 8 := Nat.le_self_pow (by norm_num) K
        _ ≤ 3 * K ^ 8 := by omega
    · exact Nat.le_of_dvd (by omega) hd
  · have hU : ∑ a, ∑ b ∈ univ.erase a, c a b ≤ g * P := by
      have := Finset.sum_le_card_nsmul (univ : Finset (Fin g)) (fun a => ∑ b ∈ univ.erase a, c a b) P fun a _ => hrow a
      simpa using this
    have hU' : ((∑ a, ∑ b ∈ univ.erase a, c a b : ℕ) : ℝ) ≤ (g : ℝ) * P := by exact_mod_cast hU
    have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
    have hK2 : (4 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    have hgP : (0 : ℝ) ≤ (g : ℝ) * P := by positivity
    have hz : 2 * ζ * g * P ≤ 2 * ((g : ℝ) * P) := by nlinarith
    unfold Lof
    rw [Nat.ceil_le, div_le_iff₀ (by linarith)]
    have h4 : ((g : ℝ) * P + 1) * 4 ≤ ((g : ℝ) * P + 1) * (K : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hK2 (by linarith)
    push_cast at hU' ⊢
    linarith

end GeneralPieces
