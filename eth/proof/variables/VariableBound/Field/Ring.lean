/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Field.Alg
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-! # The programs compute in the ring

R is a commutative ring in which 2 = 0, r an element of R, and g a word of s bits with r^s =
`decR r g`; so r is a root of X^s + g. For words of s bits, `xorW` is the sum, `mulX g` the product
with r,
`mulW g` the product and `powW g` the power of what the words stand for (`decR r`), and all of them
give words of s bits (`powW g` only for s ≥ 1). -/

public section

namespace VariableBound.Fld

variable {R : Type} [CommRing R]

/-! ### Lengths -/

/-- The sum is as long as the shorter word. -/
theorem length_xorW (x y : List Bool) : (xorW x y).length = min x.length y.length := by simp [xorW]

/-- The word 0 is as long as g. -/
theorem length_zeroW (g : List Bool) : (zeroW g).length = g.length := by simp [zeroW]

/-- The word 1 is as long as g, if g is not empty. -/
theorem length_oneW {g : List Bool} (hg : 1 ≤ g.length) : (oneW g).length = g.length := by
  simp only [oneW, List.length_cons, List.length_map, List.length_tail]; omega

/-- X·w is as long as g, if w is. -/
theorem length_mulX {g w : List Bool} (hw : w.length = g.length) : (mulX g w).length = g.length := by
  unfold mulX
  split <;> simp [length_xorW, hw]

/-- x·y is as long as g, if x is. -/
theorem length_mulW {g x : List Bool} (hx : x.length = g.length) (y : List Bool) : (mulW g x y).length = g.length := by
  induction y with
  | nil => exact length_zeroW g
  | cons b y ih =>
    have h : mulW g x (b :: y) = if b then xorW x (mulX g (mulW g x y)) else mulX g (mulW g x y) := rfl
    rw [h]
    split
    · rw [length_xorW, length_mulX ih, hx, min_self]
    · exact length_mulX ih

/-- One more factor. -/
theorem powW_succ (g u : List Bool) (e : ℕ) : powW g u (e + 1) = mulW g (powW g u e) u := by
  simp [powW, List.range_succ]

/-- u^e is as long as g, if g is not empty. -/
theorem length_powW {g : List Bool} (hg : 1 ≤ g.length) (u : List Bool) (e : ℕ) : (powW g u e).length = g.length := by
  induction e with
  | zero => exact length_oneW hg
  | succ e ih => rw [powW_succ]; exact length_mulW ih u

/-! ### Values -/

/-- In a ring with 2 = 0, the exclusive or of two bits is their sum. -/
theorem bitR_xor (h2 : (2 : R) = 0) (a b : Bool) : bitR R (xor a b) = bitR R a + bitR R b := by
  cases a <;> cases b <;> simp [bitR]
  linear_combination -h2

/-- In a ring with 2 = 0, `xorW` is the sum, for words of the same length. -/
theorem decR_xorW (h2 : (2 : R) = 0) (r : R) : ∀ x y : List Bool, x.length = y.length → decR r (xorW x y) = decR r x + decR r y
  | [], [], _ => by simp [xorW, decR]
  | a :: x, b :: y, h => by
    have ih := decR_xorW h2 r x y (by simpa using h)
    have e : xorW (a :: x) (b :: y) = xor a b :: xorW x y := rfl
    rw [e, decR, decR, decR, ih, bitR_xor h2]
    ring

/-- The word 0 stands for 0. -/
theorem decR_zeroW (r : R) (g : List Bool) : decR r (zeroW g) = 0 := by
  induction g with
  | nil => rfl
  | cons b g ih =>
    have e : zeroW (b :: g) = false :: zeroW g := rfl
    rw [e, decR, ih]; simp [bitR]

/-- The word 1 stands for 1. -/
theorem decR_oneW (r : R) (g : List Bool) : decR r (oneW g) = 1 := by
  have e : oneW g = true :: zeroW g.tail := rfl
  rw [e, decR, decR_zeroW]; simp [bitR]

/-- A bit at the upper end of a word w of n bits adds that bit times r^n. -/
theorem decR_concat (r : R) (w : List Bool) (b : Bool) : decR r (w ++ [b]) = decR r w + bitR R b * r ^ w.length := by
  induction w with
  | nil => simp [decR]
  | cons a w ih =>
    rw [List.cons_append, decR, decR, ih, List.length_cons]
    ring

/-- In a ring with 2 = 0 and for r^s = `decR r g` (r a root of X^s + g), `mulX g` is the product
with r, for a word w of s bits, s the length of g. -/
theorem decR_mulX (h2 : (2 : R) = 0) {r : R} {g : List Bool} (hr : r ^ g.length = decR r g) {w : List Bool} (hw : w.length = g.length) :
    decR r (mulX g w) = r * decR r w := by
  rcases List.eq_nil_or_concat' w with rfl | ⟨L, b, rfl⟩
  · simp [mulX, decR]
  · have hL : L.length + 1 = g.length := by simpa using hw
    have e : mulX g (L ++ [b]) = if b then xorW (false :: L) g else false :: L := by
      simp [mulX]
    rw [e, decR_concat]
    cases b
    · simp [decR, bitR]
    · rw [if_pos rfl, decR_xorW h2 r _ _ (by simpa using hL), ← hr, ← hL, decR]
      simp only [bitR]
      simp
      ring

/-- In a ring with 2 = 0 and for r^s = `decR r g` (r a root of X^s + g), `mulW g` is the product,
for a word x of s bits, s the length of g, and any word y. -/
theorem decR_mulW (h2 : (2 : R) = 0) {r : R} {g : List Bool} (hr : r ^ g.length = decR r g) {x : List Bool} (hx : x.length = g.length) (y : List Bool) :
    decR r (mulW g x y) = decR r x * decR r y := by
  induction y with
  | nil =>
    have e : mulW g x [] = zeroW g := rfl
    rw [e, decR_zeroW, decR, mul_zero]
  | cons b y ih =>
    have h : mulW g x (b :: y) = if b then xorW x (mulX g (mulW g x y)) else mulX g (mulW g x y) := rfl
    have hl := length_mulW hx y
    rw [h, decR]
    cases b
    · rw [if_neg (by simp), decR_mulX h2 hr hl, ih]; simp only [bitR]; simp; ring
    · rw [if_pos rfl, decR_xorW h2 r _ _ (by rw [length_mulX hl, hx]), decR_mulX h2 hr hl, ih]; simp only [bitR]; simp; ring

/-- In a ring with 2 = 0 and for r^s = `decR r g` (r a root of X^s + g), `powW g` is the power, for
s ≥ 1 the length of g and any word u. -/
theorem decR_powW (h2 : (2 : R) = 0) {r : R} {g : List Bool} (hr : r ^ g.length = decR r g) (hg : 1 ≤ g.length) (u : List Bool) (e : ℕ) :
    decR r (powW g u e) = decR r u ^ e := by
  induction e with
  | zero =>
    have e0 : powW g u 0 = oneW g := rfl
    rw [e0, decR_oneW, pow_zero]
  | succ e ih => rw [powW_succ, decR_mulW h2 hr (length_powW hg u e), ih, pow_succ]

end VariableBound.Fld
