/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.Level.Defs
public import Eight.SecPseudocode_Levels
public import Eight.SecProof_Network

/-! # The choice of the level in the header of Algorithm 1, for the pieces of Lemma 2 from the eight-square identity

Algorithm 1 of Section 8 of the paper, for the pieces of Lemma 2 from the eight-square identity.
Procedure CLIQUE of Algorithm 1 is defined in proof/networks/Eight/Level/Defs.lean as
`Eight.Level.levelAlg`, the algorithm for one level that works with the functions A_0, …, A_t, t =
⌈λ/3⌉, of
`EightSquareStatement.lean` and ends with the division by 2^{t|ℛ|}: lines 16 and 19 of Algorithm 1
read «for each function ι : ℛ → {0, …, ⌈λ/3⌉}» and «return sum / 2^{⌈λ/3⌉|ℛ|}».
This file holds the choice of the level as in the header of Algorithm 1: the first ℓ with K_ℓ ≥
72/δ' and e_ℓ ≤ δ'/12, for the e_ℓ of Section 8 with ρ = 11/12 (`Eight.Level.levelE`):
`exists_first`, `firstLevel`, `firstLevel_spec`. -/

@[expose] public section

namespace Eight.Level

open Groundwork Groundwork.Prog Paper

/-! ## The choice of the level -/

/-- Some level has K_ℓ ≥ 72/δ' and e_ℓ ≤ δ'/12. -/
theorem exists_first {δ' : ℝ} (hδ' : 0 < δ') : ∃ ℓ, 72 / δ' ≤ levelK ℓ ∧ Eight.Level.levelE ℓ ≤ δ' / 12 := by
  obtain ⟨ℓ, h1, h2⟩ := Eight.Level.exists_level (η := δ' / 12) (by positivity) ⌈72 / δ'⌉₊
  exact ⟨ℓ, (Nat.le_ceil _).trans (by exact_mod_cast h1), h2⟩

open Classical in
/-- Header of Algorithm 1: «ℓ is the first level with K_ℓ ≥ 72/δ' and e_ℓ ≤ δ'/12». Same as in the
paper. -/
noncomputable def firstLevel {δ' : ℝ} (hδ' : 0 < δ') : ℕ := Nat.find (exists_first hδ')

/-- The first level is such a level. -/
theorem firstLevel_spec {δ' : ℝ} (hδ' : 0 < δ') : 72 / δ' ≤ levelK (firstLevel hδ') ∧ Eight.Level.levelE (firstLevel hδ') ≤ δ' / 12 := by
  classical
  exact Nat.find_spec (exists_first hδ')


section

variable (hL : StLevel) (hLK : StLevelKeeps)

end

end Eight.Level
