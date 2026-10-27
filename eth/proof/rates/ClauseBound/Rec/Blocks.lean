/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Rec.Defs

/-! # The blocks of positions

The positions 0, …, n − 1 are cut into δ = ⌈n/h⌉ blocks; position k lies in block k / h. This file
has the elementary facts on this cut that the lemma on the
recombined pieces uses:

* the arithmetic of δ and of the blocks: δ ≤ n ≤ hδ, the block k / h of a position is one of the δ
  blocks, and every block has at most h positions;
* a label is the family of its parts in the blocks (`split`), and block b has 4^{n_b} labels. -/

public section

namespace ClauseBound.Rec

open Finset Polynomial Pieces

variable {n h : ℕ}

/-! ### The number of blocks and their sizes -/

/-- There are at most n blocks. -/
theorem nblk_le (n : ℕ) (hh : 1 ≤ h) : nblk n h ≤ n := by
  unfold nblk
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  have : n ≤ h * n := Nat.le_mul_of_pos_left n hh
  omega

/-- The blocks have room for all positions. -/
theorem le_mul_nblk (n : ℕ) (hh : 1 ≤ h) : n ≤ h * nblk n h := by
  unfold nblk
  have h1 := Nat.div_add_mod (n + h - 1) h
  have h2 := Nat.mod_lt (n + h - 1) hh
  omega

/-- The block of a position is one of the blocks. -/
theorem div_lt_nblk (hh : 1 ≤ h) (k : Fin n) : k.val / h < nblk n h := by
  rw [Nat.div_lt_iff_lt_mul hh]
  have h1 := le_mul_nblk n hh
  have h2 := k.isLt
  rw [Nat.mul_comm] at h1
  omega

/-- A block has at most h positions. -/
theorem card_blk_le (hh : 1 ≤ h) (b : ℕ) : #(blk n h b) ≤ h := by
  have h1 : #(blk n h b) ≤ #(Ico (b * h) (b * h + h)) := by
    refine card_le_card_of_injOn (fun k => k.val) ?_ (fun _ _ _ _ e => Fin.ext e)
    intro k hk
    have hk' : k.val / h = b := by simpa [blk] using hk
    have h3 := Nat.div_add_mod k.val h
    have h4 := Nat.mod_lt k.val hh
    rw [hk', Nat.mul_comm] at h3
    simp only [coe_Ico, Set.mem_Ico]
    omega
  simpa using h1

/-! ### A label and its parts in the blocks -/

/-- The value of a family of labels on blocks at a position does not depend on how the block of the
position is written. -/
private theorem family_congr (F : ∀ b : Fin (nblk n h), BLab n h b) (k : Fin n) {b b' : Fin (nblk n h)} (hk : k.val / h = b.val)
    (hk' : k.val / h = b'.val) : F b ⟨k, hk⟩ = F b' ⟨k, hk'⟩ := by
  obtain rfl : b = b' := Fin.ext (hk.symm.trans hk')
  rfl

/-- A label is the family of its parts in the blocks. -/
noncomputable def split (hh : 1 ≤ h) : Lab n ≃ ∀ b : Fin (nblk n h), BLab n h b where
  toFun β _ k := β k.1
  invFun F k := F ⟨k.val / h, div_lt_nblk hh k⟩ ⟨k, rfl⟩
  left_inv _ := rfl
  right_inv F := by
    funext b k
    exact family_congr F k.1 rfl k.2

/-- The part of β in block b has the entries of β. -/
theorem split_apply (hh : 1 ≤ h) (β : Lab n) (b : Fin (nblk n h)) (k : {k : Fin n // k.val / h = b.val}) :
    split hh β b k = β k.1 := by
  unfold split
  rfl

/-- Block b has 4^{n_b} labels. -/
theorem card_BLab (b : Fin (nblk n h)) : Fintype.card (BLab n h b) = 4 ^ #(blk n h b.val) := by
  rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_bool, Fintype.card_subtype]
  rfl

end ClauseBound.Rec
