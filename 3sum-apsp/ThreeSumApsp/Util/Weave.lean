/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Digits

/-!
# Interleaving two strings of digits along a mask

A mask is a list of truth values, one for each level.  `weaveList mask outer inner` runs through the
levels and takes the next digit of `inner` at a level with the entry `true` and the next digit of
`outer` at a level with the entry `false`.  A program that forms the number with these digits by
Horner's rule needs one pass over the mask and two pointers: at level `ℓ` the pointer into `inner`
has passed as many digits as there are entries `true` among the first `ℓ` entries of the mask, and
the pointer into `outer` as many as there are entries `false` (`getD_weaveList`).
-/

@[expose] public section

namespace ThreeSumApsp

/-- Two lists of digits interleaved along a mask: at a level with the entry `true` stands the next
digit of `inner`, at a level with the entry `false` the next digit of `outer`.  A missing digit
counts as 0. -/
def weaveList : List Bool → List ℕ → List ℕ → List ℕ
  | [], _, _ => []
  | true :: mask, outer, inner => inner.headD 0 :: weaveList mask outer inner.tail
  | false :: mask, outer, inner => outer.headD 0 :: weaveList mask outer.tail inner

/-- `weaveList` has one digit for each level. -/
@[simp] theorem length_weaveList (mask : List Bool) (outer inner : List ℕ) :
    (weaveList mask outer inner).length = mask.length := by
  induction mask generalizing outer inner with
  | nil => simp [weaveList]
  | cons x mask ih => cases x <;> simp [weaveList, ih]

/-- The digit of `weaveList` at level `ℓ`: the next unused digit of `inner` or of `outer`. -/
theorem getD_weaveList (mask : List Bool) (outer inner : List ℕ) (ℓ : ℕ) :
    (weaveList mask outer inner).getD ℓ 0 =
      if ℓ < mask.length then
        if mask.getD ℓ false then inner.getD ((mask.take ℓ).count true) 0
        else outer.getD ((mask.take ℓ).count false) 0
      else 0 := by
  induction mask generalizing outer inner ℓ with
  | nil => simp [weaveList]
  | cons x mask ih =>
    cases ℓ with
    | zero =>
      cases x
      · cases outer <;> simp [weaveList]
      · cases inner <;> simp [weaveList]
    | succ ℓ =>
      cases x
      · cases outer with
        | nil => simpa [weaveList] using ih [] inner ℓ
        | cons o outer => simpa [weaveList] using ih outer inner ℓ
      · cases inner with
        | nil => simpa [weaveList] using ih outer [] ℓ
        | cons i inner => simpa [weaveList] using ih outer inner ℓ

/-- If the digits of both lists are below a positive number `b`, so are the interleaved digits. -/
theorem lt_of_mem_weaveList {b : ℕ} (hb : 0 < b) {mask : List Bool} {outer inner : List ℕ}
    (houter : ∀ d ∈ outer, d < b) (hinner : ∀ d ∈ inner, d < b) :
    ∀ d ∈ weaveList mask outer inner, d < b := by
  intro d hd
  obtain ⟨ℓ, hℓ, rfl⟩ := List.getElem_of_mem hd
  rw [← List.getD_eq_getElem _ 0 hℓ, getD_weaveList]
  split_ifs
  · exact List.getD_of_forall_mem (p := (· < b)) hb hinner _
  · exact List.getD_of_forall_mem (p := (· < b)) hb houter _
  · exact hb

end ThreeSumApsp
