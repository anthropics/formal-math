/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cut.Codes
import Nc.Cut.Groups
import Nc.Cut.StartB

/-!
# Exactness of a whole cut

The value of an automaton is the sum, over the states between the blocks, the row data, the numbers of units, the
outcomes of the moves, and the contents of the units shared by different groups, of the products of the values of
the groups.
-/

set_option linter.unusedSectionVars false

namespace Nc.Cut

open Finset

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A K U0 E U1 : ℕ}

section Groups

variable {AA UU W G : Type*} [Fintype AA] [DecidableEq AA] [Fintype UU] [DecidableEq UU]
  [Fintype W] [DecidableEq W] [Fintype G] [DecidableEq G]

/-- If the tables vanish unless all units held are present, the contents of shared units are present. -/
theorem groupVal_ne_none {h0 h1 : UU → AA} {e : W} {Seen Cur : Finset UU} (hCur : Cur ⊆ Seen) {grp : AA → G}
    {φ : AA → (UU → W) → F} {g : G} {b : UU → W}
    (hφ : ∀ a y, φ a y ≠ 0 → ∀ id ∈ Seen, Holds h0 h1 a id → y id ≠ e)
    (h : groupVal h0 h1 e Seen Cur grp φ g b ≠ 0) {id : UU} (hid : id ∈ Cur)
    (hg : (grp (h0 id) = g ∧ grp (h1 id) ≠ g) ∨ (grp (h0 id) ≠ g ∧ grp (h1 id) = g)) : b id ≠ e := by
  classical
  rw [groupVal] at h
  obtain ⟨y, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at h with hc
  swap
  · exact absurd rfl h
  have h2 : ∀ a, grp a = g → φ a (y a) ≠ 0 := fun a ha h0 =>
    h (Finset.prod_eq_zero (Finset.mem_filter.2 ⟨Finset.mem_univ a, ha⟩) h0)
  rcases hg with ⟨g1, g2⟩ | ⟨g1, g2⟩
  · rw [← hc.fst id hid g1 g2]
    exact hφ _ _ (h2 _ g1) id (hCur hid) (Or.inl rfl)
  · rw [← hc.snd id hid g1 g2]
    exact hφ _ _ (h2 _ g2) id (hCur hid) (Or.inr rfl)

end Groups

end Nc.Cut
