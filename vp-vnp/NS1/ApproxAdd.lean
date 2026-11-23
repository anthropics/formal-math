/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Postpone

/-!
# The counter of exponents

A program that adds two numbers of the same number of binary digits, modulo that power of 2, and is plain.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- Two of three bits are 1. -/
def maj (a b c : Bool) : Bool := (a && b) || (c && (a || b))

/-- The digits of a sum, with a carry; the last carry is dropped. -/
def addc : Bool → List Bool → List Bool → List Bool
  | c, a :: x, b :: y => xor a (xor b c) :: addc (maj a b c) x y
  | _, _, _ => []

theorem length_addc (c : Bool) {x y : List Bool} (h : x.length = y.length) : (addc c x y).length = x.length := by
  induction x generalizing c y with
  | nil => simp [addc]
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp [addc, ih _ h]

/-- **Paper: proof of Proposition prop:approx-acc, the counter adds.** The program's sum is the sum modulo 2 ^ length. -/
theorem val_addc (c : Bool) {x y : List Bool} (h : x.length = y.length) :
    KT.val (addc c x y) = ((if c then 1 else 0) + KT.val x + KT.val y) % 2 ^ x.length := by
  induction x generalizing c y with
  | nil => simp [addc, KT.val, Nat.mod_one]
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [addc, KT.val, ih _ h, List.length_cons, pow_succ']
      have key : ((if c then 1 else 0) + ((if a then 1 else 0) + 2 * KT.val x) + ((if b then 1 else 0) + 2 * KT.val y)) / 2 =
          (if maj a b c then 1 else 0) + KT.val x + KT.val y := by
        cases a <;> cases b <;> cases c <;> simp [maj] <;> omega
      rw [Nat.mod_mul, key]
      congr 1
      cases a <;> cases b <;> cases c <;> simp <;> omega

/-- Write a digit and go on with a carry. -/
def addBr (s c : Bool) : Fm := .cons (.quote (bit s)) (.run (.hd .id) (.cons (.hd .id)
  (.cons (.quote (bit c)) (.cons (.tl (.hd (.tl (.tl .id)))) (.tl (.tl (.tl (.tl .id))))))))

/-- Add; the argument is (this program, (carry, (number, number))). -/
def AD : Fm := .ite (.hd (.tl (.tl .id)))
  (.ite (.hd (.hd (.tl (.tl .id))))
    (.ite (.hd (.tl (.tl (.tl .id)))) (.ite (.hd (.tl .id)) (addBr true true) (addBr false true))
      (.ite (.hd (.tl .id)) (addBr false true) (addBr true false)))
    (.ite (.hd (.tl (.tl (.tl .id)))) (.ite (.hd (.tl .id)) (addBr false true) (addBr true false))
      (.ite (.hd (.tl .id)) (addBr true false) (addBr false false))))
  (.quote .nil)

theorem addBr_dt {s c' c : Bool} {a b : Bool} {x y : List Bool} {o : Tree} {k : ℕ}
    (h : Dt θ AD (.cons AD.code (.cons (bit c') (.cons (ofBits x) (ofBits y)))) o k) :
    Dt θ (addBr s c') (.cons AD.code (.cons (bit c) (.cons (ofBits (a :: x)) (ofBits (b :: y)))))
      (.cons (bit s) o) (k + 21) := by
  have h' : Dt θ (Fm.ofTree AD.code) (.cons AD.code (.cons (bit c') (.cons (ofBits x) (ofBits y)))) o k := by
    rwa [Fm.ofTree_code]
  have := Dt.cons (Dt.quote (θ := θ) (bit s) (.cons AD.code (.cons (bit c) (.cons (ofBits (a :: x)) (ofBits (b :: y))))))
    (Dt.run (Dt.hd (Dt.id _)) (Dt.cons (Dt.hd (Dt.id _)) (Dt.cons (Dt.quote (bit c') _)
      (Dt.cons (Dt.tl (Dt.hd (Dt.tl (Dt.tl (Dt.id _))))) (Dt.tl (Dt.tl (Dt.tl (Dt.tl (Dt.id _)))))))) h')
  simp only [ofBits] at this ⊢
  convert this using 1
  · rfl
  · omega

theorem AD_dt (c : Bool) {x y : List Bool} (h : x.length = y.length) :
    ∃ k ≤ 60 * x.length + 20,
      Dt θ AD (.cons AD.code (.cons (bit c) (.cons (ofBits x) (ofBits y)))) (ofBits (addc c x y)) k := by
  induction x generalizing c y with
  | nil =>
    obtain rfl : y = [] := List.length_eq_zero_iff.1 h.symm
    exact ⟨_, by norm_num, Dt.ite_false (Dt.hd (Dt.tl (Dt.tl (Dt.id _)))) (Dt.quote _ _)⟩
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      obtain ⟨k, hk, hd⟩ := ih (maj a b c) h
      have hbr := addBr_dt (θ := θ) (s := xor a (xor b c)) (c := c) (a := a) (b := b) hd
      have h0 : Dt θ (.hd (.tl (.tl .id))) (.cons AD.code (.cons (bit c) (.cons (ofBits (a :: x)) (ofBits (b :: y)))))
          (ofBits (a :: x)) 4 := Dt.hd (Dt.tl (Dt.tl (Dt.id _)))
      have h1 := Dt.hd h0
      have h2 : Dt θ (.hd (.tl (.tl (.tl .id)))) (.cons AD.code (.cons (bit c) (.cons (ofBits (a :: x)) (ofBits (b :: y)))))
          (bit b) 5 := Dt.hd (Dt.tl (Dt.tl (Dt.tl (Dt.id _))))
      have h3 : Dt θ (.hd (.tl .id)) (.cons AD.code (.cons (bit c) (.cons (ofBits (a :: x)) (ofBits (b :: y)))))
          (bit c) 3 := Dt.hd (Dt.tl (Dt.id _))
      have one_ne : bit true ≠ .nil := by simp [bit, one]
      refine ⟨_, ?_, Dt.ite_true h0 (by simp [ofBits]) (j := 5 + 1 + (5 + 1 + (3 + 1 + (k + 21)))) ?_⟩
      · simp only [List.length_cons]
        omega
      · cases a <;> cases b <;> cases c <;>
          simp only [maj, Bool.and_self, Bool.and_true, Bool.and_false, Bool.or_self,
            Bool.or_true, Bool.or_false, Bool.xor_false, Bool.xor_true, Bool.not_true,
            Bool.not_false, addc, ofBits] at hbr ⊢
        · exact Dt.ite_false h1 (Dt.ite_false h2 (Dt.ite_false h3 hbr))
        · exact Dt.ite_false h1 (Dt.ite_false h2 (Dt.ite_true h3 one_ne hbr))
        · exact Dt.ite_false h1 (Dt.ite_true h2 one_ne (Dt.ite_false h3 hbr))
        · exact Dt.ite_false h1 (Dt.ite_true h2 one_ne (Dt.ite_true h3 one_ne hbr))
        · exact Dt.ite_true h1 one_ne (Dt.ite_false h2 (Dt.ite_false h3 hbr))
        · exact Dt.ite_true h1 one_ne (Dt.ite_false h2 (Dt.ite_true h3 one_ne hbr))
        · exact Dt.ite_true h1 one_ne (Dt.ite_true h2 one_ne (Dt.ite_false h3 hbr))
        · exact Dt.ite_true h1 one_ne (Dt.ite_true h2 one_ne (Dt.ite_true h3 one_ne hbr))

end NS1
