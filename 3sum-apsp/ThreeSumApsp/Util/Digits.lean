/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.List
public import Mathlib.Data.List.OfFn
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic.Ring

/-!
# Strings of digits as numbers

The paper indexes its arrays by strings (Section 2.3.1).  A program indexes them by numbers: the
string `d₁ d₂ ⋯ d_n` of digits in base `b` is coded by the number `d₁ b^{n-1} + ⋯ + d_n`.  The first
digit (the paper's level 1) is the most significant one, so the strings that begin with a given
digit have consecutive codes, and a slice of an array is a contiguous part of it.

* `code` is the number of a string, `digit` reads one digit of a number, `digitList` all of them,
  and `ofDigitList` is Horner's rule.
* `code` and `digit` undo each other (`digit_code`, `code_digit`), so the strings of length `n`
  correspond to the numbers below `b^n` (`codeEquiv`).
* For lists of digits, `digitList` undoes `ofDigitList` (`digitList_ofDigitList`). A list of `n`
  digits has a value below `b^n` (`ofDigitList_lt`), which determines it (`eq_of_ofDigitList_eq`).
  One more digit at the end is one more step of Horner's rule (`ofDigitList_append_singleton`,
  `ofDigitList_take_succ`).
* For an alphabet `α` whose letters are numbered by `e : α ≃ Fin b`, `codeStr e` and `decodeStr e`
  go from strings over `α` to numbers and back, so these strings, too, correspond to the numbers
  below `b^n` (`strEquiv`).  `digitsStr e` is the list of the digits of such a string; Horner's rule
  computes the code from it (`ofDigitList_digitsStr`).

Mathlib's `Nat.ofDigits` and `finFunctionFinEquiv` put the least significant digit first, so they
would make a slice a scattered part of an array; this is why the codes are defined here.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## Strings of numbers below `b` -/

/-- The number with the digits `d 0, d 1, …, d (n-1)` in base `b`, most significant digit first. -/
def code (b : ℕ) : {n : ℕ} → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, d => d 0 * b ^ n + code b (Fin.tail d)

/-- The digit number `ℓ` (counted from 0, most significant first) of the `n`-digit number `c` in
base `b`. -/
def digit (b n c ℓ : ℕ) : ℕ := c / b ^ (n - 1 - ℓ) % b

/-- The `n` digits of `c` in base `b`, most significant first, as a list. -/
def digitList (b n c : ℕ) : List ℕ := (List.range n).map (digit b n c)

/-- Horner's rule: the number with the given list of digits, most significant first. -/
def ofDigitList (b : ℕ) (l : List ℕ) : ℕ := l.foldl (fun acc x => acc * b + x) 0

/-- The code of the digit `s` followed by the string `d`. -/
theorem code_cons (b : ℕ) {n : ℕ} (s : ℕ) (d : Fin n → ℕ) :
    code b (Fin.cons s d : Fin (n + 1) → ℕ) = s * b ^ n + code b d := by
  rw [code, Fin.cons_zero, Fin.tail_cons]

/-- Horner's rule, started with `acc`, shifts `acc` by `n` digits and adds the code. -/
private theorem foldl_ofFn (b : ℕ) {n : ℕ} (d : Fin n → ℕ) (acc : ℕ) :
    (List.ofFn d).foldl (fun acc x => acc * b + x) acc = acc * b ^ n + code b d := by
  induction n generalizing acc with
  | zero => simp [code]
  | succ n ih =>
    rw [List.ofFn_succ, List.foldl_cons, ih, code, pow_succ, Fin.tail_def]
    ring

/-- The code is computed by Horner's rule, with one multiplication by `b` and one addition for each
digit. -/
theorem code_eq_ofDigitList (b : ℕ) {n : ℕ} (d : Fin n → ℕ) :
    code b d = ofDigitList b (List.ofFn d) := by
  rw [ofDigitList, foldl_ofFn, Nat.zero_mul, Nat.zero_add]

/-- An `n`-digit number is less than `b^n`. -/
theorem code_lt {b n : ℕ} {d : Fin n → ℕ} (hd : ∀ ℓ, d ℓ < b) : code b d < b ^ n := by
  induction n with
  | zero => simp [code]
  | succ n ih =>
    have hrest : code b (Fin.tail d) < b ^ n := ih fun ℓ => hd _
    have hfirst : d 0 * b ^ n + b ^ n ≤ b * b ^ n := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ (hd 0)
    rw [code, pow_succ']
    omega

/-- The first digit and the rest, by division. -/
theorem code_div_mod {b n : ℕ} {d : Fin (n + 1) → ℕ} (hd : ∀ ℓ, d ℓ < b) :
    code b d / b ^ n = d 0 ∧ code b d % b ^ n = code b (Fin.tail d) := by
  have hrest : code b (Fin.tail d) < b ^ n := code_lt fun ℓ => hd _
  have hpos : 0 < b ^ n := Nat.zero_lt_of_lt hrest
  rw [code, Nat.add_comm]
  exact ⟨by rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hrest, Nat.zero_add],
    by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrest]⟩

/-- The digits after the first one are the digits of the remainder modulo `b^n`. -/
theorem digit_succ (b n c k : ℕ) (hk : k < n) :
    digit b (n + 1) c (k + 1) = digit b n (c % b ^ n) k := by
  obtain ⟨e, rfl⟩ : ∃ e, n = e + (k + 1) := ⟨n - (k + 1), by omega⟩
  rw [digit, digit, show e + (k + 1) + 1 - 1 - (k + 1) = e by omega,
    show e + (k + 1) - 1 - k = e by omega, pow_add, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (dvd_pow_self b k.succ_ne_zero)]

/-- The digits of the code are the digits. -/
theorem digit_code {b n : ℕ} {d : Fin n → ℕ} (hd : ∀ ℓ, d ℓ < b) (ℓ : Fin n) :
    digit b n (code b d) ℓ = d ℓ := by
  induction n with
  | zero => exact ℓ.elim0
  | succ n ih =>
    obtain ⟨hdiv, hmod⟩ := code_div_mod hd
    refine Fin.cases ?_ (fun k => ?_) ℓ
    · rw [digit, Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel, hdiv, Nat.mod_eq_of_lt (hd 0)]
    · rw [Fin.val_succ, digit_succ b n _ k k.isLt, hmod]
      exact ih (d := Fin.tail d) (fun ℓ => hd _) k

/-- A digit is less than the base. -/
theorem digit_lt {b : ℕ} (hb : 0 < b) (n c ℓ : ℕ) : digit b n c ℓ < b :=
  Nat.mod_lt _ hb

/-- A number below `b^n` is the code of its digits. -/
theorem code_digit {b n c : ℕ} (hc : c < b ^ n) : code b (fun ℓ : Fin n => digit b n c ℓ) = c := by
  induction n generalizing c with
  | zero =>
    rw [pow_zero, Nat.lt_one_iff] at hc
    rw [hc, code]
  | succ n ih =>
    rw [pow_succ'] at hc
    have hpos : 0 < b ^ n := Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt hc)
    have hfirst : digit b (n + 1) c 0 = c / b ^ n := by
      rw [digit, Nat.sub_zero, Nat.add_sub_cancel]
      exact Nat.mod_eq_of_lt ((Nat.div_lt_iff_lt_mul hpos).mpr hc)
    have hrest : (Fin.tail fun ℓ : Fin (n + 1) => digit b (n + 1) c ℓ)
        = fun ℓ : Fin n => digit b n (c % b ^ n) ℓ :=
      funext fun k => digit_succ b n c k k.isLt
    rw [code, hrest, ih (Nat.mod_lt _ hpos), Fin.val_zero, hfirst]
    exact Nat.div_add_mod' c (b ^ n)

/-- Different strings have different codes. -/
theorem eq_of_code_eq {b n : ℕ} {d d' : Fin n → ℕ} (hd : ∀ ℓ, d ℓ < b) (hd' : ∀ ℓ, d' ℓ < b)
    (h : code b d = code b d') : d = d' := by
  funext ℓ
  rw [← digit_code hd ℓ, ← digit_code hd' ℓ, h]

/-- If some number is below `b^n` and `n` is not 0, the base is not 0. -/
theorem pos_of_lt_pow {b n c : ℕ} (hc : c < b ^ n) (hn : n ≠ 0) : 0 < b := by
  refine Nat.pos_of_ne_zero fun hb => ?_
  rw [hb, zero_pow hn] at hc
  exact Nat.not_lt_zero _ hc

/-- The strings of `n` digits in base `b` correspond to the numbers below `b^n`. -/
def codeEquiv (b n : ℕ) : (Fin n → Fin b) ≃ Fin (b ^ n) where
  toFun d := ⟨code b fun ℓ => (d ℓ : ℕ), code_lt fun ℓ => (d ℓ).isLt⟩
  invFun c := fun ℓ =>
    ⟨digit b n c ℓ, digit_lt (pos_of_lt_pow c.isLt (Nat.ne_zero_of_lt ℓ.isLt)) n c ℓ⟩
  left_inv d := funext fun ℓ => Fin.ext (digit_code (fun ℓ => (d ℓ).isLt) ℓ)
  right_inv c := Fin.ext (code_digit c.isLt)

/-! ## Lists of digits -/

/-- The list of the `n` digits of a number has `n` entries. -/
@[simp]
theorem length_digitList (b n c : ℕ) : (digitList b n c).length = n := by
  simp [digitList]

/-- Entry `i` of the list of digits is digit `i`. -/
@[simp]
theorem getElem_digitList (b n c : ℕ) {i : ℕ} (hi : i < (digitList b n c).length) :
    (digitList b n c)[i] = digit b n c i := by
  simp [digitList]

/-- The digits are below the base. -/
theorem lt_of_mem_digitList {b : ℕ} (hb : 0 < b) {n c x : ℕ} (hx : x ∈ digitList b n c) :
    x < b := by
  obtain ⟨ℓ, -, rfl⟩ := List.mem_map.1 hx
  exact digit_lt hb n c ℓ

/-- The list of digits of a code. -/
theorem digitList_code {b n : ℕ} {d : Fin n → ℕ} (hd : ∀ ℓ, d ℓ < b) :
    digitList b n (code b d) = List.ofFn d := by
  refine List.ext_getElem (by simp) fun i hi _ => ?_
  simpa using digit_code hd ⟨i, by simpa using hi⟩

/-- The empty list of digits has the value `0`. -/
@[simp]
theorem ofDigitList_nil (b : ℕ) : ofDigitList b [] = 0 :=
  rfl

/-- One more digit at the end multiplies the value by `b` and adds the digit. -/
theorem ofDigitList_append_singleton (b : ℕ) (l : List ℕ) (x : ℕ) :
    ofDigitList b (l ++ [x]) = ofDigitList b l * b + x := by
  simp [ofDigitList]

/-- The value of the first `i + 1` digits, from the value of the first `i` digits. -/
theorem ofDigitList_take_succ (b : ℕ) (l : List ℕ) {i : ℕ} (hi : i < l.length) :
    ofDigitList b (l.take (i + 1)) = ofDigitList b (l.take i) * b + l.getD i 0 := by
  rw [List.take_succ_getD l hi 0, ofDigitList_append_singleton]

/-- The value of a list of digits is the code of the list, read as a string. -/
theorem ofDigitList_eq_code (b : ℕ) (l : List ℕ) :
    ofDigitList b l = code b fun ℓ : Fin l.length => l[(ℓ : ℕ)] := by
  rw [code_eq_ofDigitList, List.ofFn_getElem]

/-- A number with `n` digits below `b` is below `b^n`. -/
theorem ofDigitList_lt {b : ℕ} (l : List ℕ) (hd : ∀ d ∈ l, d < b) :
    ofDigitList b l < b ^ l.length := by
  rw [ofDigitList_eq_code]
  exact code_lt fun ℓ => hd _ (List.getElem_mem ℓ.isLt)

/-- The digits of the value of a list of digits below `b` are the list. -/
theorem digitList_ofDigitList {b : ℕ} (l : List ℕ) (hd : ∀ d ∈ l, d < b) :
    digitList b l.length (ofDigitList b l) = l := by
  rw [ofDigitList_eq_code, digitList_code fun ℓ => hd _ (List.getElem_mem ℓ.isLt),
    List.ofFn_getElem]

/-- Two lists of the same length of digits below `b` with the same value are equal. -/
theorem eq_of_ofDigitList_eq {b : ℕ} (l l' : List ℕ) (hlen : l.length = l'.length)
    (hl : ∀ d ∈ l, d < b) (hl' : ∀ d ∈ l', d < b) (hval : ofDigitList b l = ofDigitList b l') :
    l = l' := by
  rw [← digitList_ofDigitList l hl, ← digitList_ofDigitList l' hl', hlen, hval]

/-! ## Strings over a numbered alphabet -/

variable {α : Type} {b : ℕ} (e : α ≃ Fin b)

/-- Strings over an alphabet `α` whose letters are numbered by `e : α ≃ Fin b`: the code of a
string. -/
def codeStr {n : ℕ} (u : Fin n → α) : ℕ := code b fun ℓ => (e (u ℓ) : ℕ)

/-- The string with a given code. -/
def decodeStr [NeZero b] (n c : ℕ) : Fin n → α :=
  fun ℓ => e.symm ⟨digit b n c ℓ, digit_lt (NeZero.pos b) n c ℓ⟩

/-- The code of the letter `s` followed by the string `u'`. -/
theorem codeStr_cons {n : ℕ} (s : α) (u' : Fin n → α) :
    codeStr e (Fin.cons s u' : Fin (n + 1) → α) = e s * b ^ n + codeStr e u' := by
  rw [codeStr, codeStr, ← code_cons]
  congr 1
  funext ℓ
  refine Fin.cases ?_ (fun k => ?_) ℓ <;> simp

/-- The code of a string of length `n` is less than `b^n`. -/
theorem codeStr_lt {n : ℕ} (u : Fin n → α) : codeStr e u < b ^ n :=
  code_lt fun ℓ => (e (u ℓ)).isLt

/-- Decoding undoes coding. -/
@[simp]
theorem decodeStr_codeStr [NeZero b] {n : ℕ} (u : Fin n → α) :
    decodeStr e n (codeStr e u) = u := by
  funext ℓ
  have hdigit := digit_code (d := fun ℓ => (e (u ℓ) : ℕ)) (fun ℓ => (e (u ℓ)).isLt) ℓ
  simp only [decodeStr, codeStr, hdigit, Fin.eta, Equiv.symm_apply_apply]

/-- Coding undoes decoding, for a number below `b^n`. -/
theorem codeStr_decodeStr [NeZero b] {n c : ℕ} (hc : c < b ^ n) :
    codeStr e (decodeStr e n c) = c := by
  simp only [codeStr, decodeStr, Equiv.apply_symm_apply]
  exact code_digit hc

/-- Different strings have different codes. -/
theorem codeStr_injective (n : ℕ) : Function.Injective (codeStr e : (Fin n → α) → ℕ) := by
  intro u u' h
  have hdigits := eq_of_code_eq (fun ℓ => (e (u ℓ)).isLt) (fun ℓ => (e (u' ℓ)).isLt) h
  exact funext fun ℓ => e.injective (Fin.ext (congrFun hdigits ℓ))

/-- The list of digits of the code of a string. -/
@[simp]
theorem digitList_codeStr {n : ℕ} (u : Fin n → α) :
    digitList b n (codeStr e u) = List.ofFn fun ℓ => (e (u ℓ) : ℕ) :=
  digitList_code fun ℓ => (e (u ℓ)).isLt

/-- The string with the code `s · b^n + c` is the letter with the digit `s` followed by the string
with the code `c`. -/
theorem decodeStr_cons [NeZero b] {n : ℕ} (s : α) {c : ℕ} (hc : c < b ^ n) :
    decodeStr e (n + 1) (e s * b ^ n + c) = Fin.cons s (decodeStr e n c) := by
  rw [← decodeStr_codeStr e (Fin.cons s (decodeStr e n c)), codeStr_cons,
    codeStr_decodeStr e hc]

/-- The strings of length `n` over `α` correspond to the numbers below `b^n`. -/
def strEquiv (n : ℕ) : (Fin n → α) ≃ Fin (b ^ n) :=
  (Equiv.arrowCongr (Equiv.refl _) e).trans (codeEquiv b n)

/-! ## The list of the digits of a string -/

/-- The digits of a string over an alphabet with numbered symbols, level 1 first. -/
def digitsStr {α : Type} {b : ℕ} (e : α ≃ Fin b) {n : ℕ} (u : Fin n → α) : List ℕ :=
  List.ofFn fun ℓ => (e (u ℓ) : ℕ)

section

variable {α : Type} {b : ℕ} (e : α ≃ Fin b) {n : ℕ}

theorem length_digitsStr (u : Fin n → α) : (digitsStr e u).length = n := List.length_ofFn

theorem digitsStr_lt (u : Fin n → α) : ∀ d ∈ digitsStr e u, d < b := by
  intro d hd
  obtain ⟨ℓ, rfl⟩ := List.mem_ofFn.mp hd
  exact (e _).isLt

theorem digitsStr_injective : Function.Injective (digitsStr e : (Fin n → α) → List ℕ) :=
  fun _ _ h => funext fun ℓ => e.injective (Fin.ext (congrFun (List.ofFn_injective h) ℓ))

/-- Every list of n digits below b is the list of digits of a string. -/
theorem exists_digitsStr (l : List ℕ) (hl : l.length = n) (hd : ∀ d ∈ l, d < b) :
    ∃ u : Fin n → α, digitsStr e u = l := by
  subst hl
  refine ⟨fun ℓ => e.symm ⟨l[ℓ], hd _ (List.getElem_mem _)⟩, ?_⟩
  simp only [digitsStr, Equiv.apply_symm_apply]
  exact List.ofFn_getElem

/-- The digit at a level. -/
theorem getD_digitsStr (u : Fin n → α) (ℓ : Fin n) : (digitsStr e u).getD ℓ 0 = e (u ℓ) := by
  simp [digitsStr, List.getD_eq_getElem?_getD]

/-- A list with n members and the right digit at every level is the list of digits of the
string. -/
theorem digitsStr_eq_of_getD (u : Fin n → α) {l : List ℕ} (hl : l.length = n)
    (h : ∀ ℓ : Fin n, l.getD ℓ 0 = e (u ℓ)) : digitsStr e u = l := by
  refine List.ext_getElem (by rw [length_digitsStr, hl]) fun i hi _ => ?_
  rw [length_digitsStr] at hi
  rw [← List.getD_eq_getElem l 0, h ⟨i, hi⟩]
  simp only [digitsStr, List.getElem_ofFn]

/-- A statement on all positions of a digit a ≠ 0 is a statement on levels (beyond the end of the
list `getD` gives 0, so a position of the digit a is a level). -/
theorem forall_getD_digitsStr (u : Fin n → α) {a : ℕ} (ha : a ≠ 0) (P : ℕ → Prop) :
    (∀ j, (digitsStr e u).getD j 0 = a → P j) ↔ ∀ ℓ : Fin n, (e (u ℓ) : ℕ) = a → P ℓ := by
  refine ⟨fun h ℓ hℓ => h ℓ ((getD_digitsStr e u ℓ).trans hℓ), fun h j hj => ?_⟩
  have hjn : j < n := by
    by_contra hc
    rw [List.getD_eq_default _ _ (by rw [length_digitsStr]; omega)] at hj
    exact ha hj.symm
  exact h ⟨j, hjn⟩ ((getD_digitsStr e u ⟨j, hjn⟩).symm.trans hj)

/-- The code is computed from the digits by Horner's rule. -/
theorem ofDigitList_digitsStr (u : Fin n → α) : ofDigitList b (digitsStr e u) = codeStr e u :=
  (code_eq_ofDigitList b fun ℓ => (e (u ℓ) : ℕ)).symm

end

end ThreeSumApsp
