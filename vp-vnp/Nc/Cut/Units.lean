/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Units

A bit string is cut into units of `ub` bits: a 1 and then zeros are appended. The string can be recovered from
the units.
-/

set_option linter.unusedSectionVars false

namespace Nc

variable (ub : ℕ)

/-- The content of a unit: absent, or `ub` bits. -/
abbrev UW := Option (Fin ub → Bool)

/-- The number of units of a string. -/
def ucount (L : List Bool) : ℕ := L.length / ub + 1

/-- The `k`-th unit of a string. -/
def uword (L : List Bool) (k : ℕ) : Fin ub → Bool := fun b => (L ++ [true]).getD (k * ub + b) false

/-- All units of a string. -/
def unitsOf (L : List Bool) (k : ℕ) : UW ub := if k < ucount ub L then some (uword ub L k) else none

variable {ub}

theorem unitsOf_inj (hub : 0 < ub) {L L' : List Bool} (h : ∀ k, unitsOf ub L k = unitsOf ub L' k) : L = L' := by
  have hc : ucount ub L = ucount ub L' := by
    rcases lt_trichotomy (ucount ub L) (ucount ub L') with hlt | heq | hlt
    · have := h (ucount ub L)
      simp [unitsOf, hlt] at this
    · exact heq
    · have := h (ucount ub L')
      simp [unitsOf, hlt] at this
  have hp : ∀ i, i < ucount ub L * ub → (L ++ [true]).getD i false = (L' ++ [true]).getD i false := by
    intro i hi
    have hk : i / ub < ucount ub L := (Nat.div_lt_iff_lt_mul hub).2 hi
    have := h (i / ub)
    simp only [unitsOf, if_pos hk, if_pos (hc ▸ hk), Option.some.injEq] at this
    have h2 := congrFun this ⟨i % ub, Nat.mod_lt _ hub⟩
    simp only [uword, Nat.div_add_mod'] at h2
    exact h2
  have hl : ∀ L : List Bool, L.length < ucount ub L * ub := by
    intro L
    have := Nat.div_add_mod L.length ub
    have h3 := Nat.mod_lt L.length hub
    simp only [ucount, add_mul, one_mul]
    rw [mul_comm] at this
    omega
  have hlen : L.length = L'.length := by
    rcases lt_trichotomy L.length L'.length with hlt | heq | hlt
    · exfalso
      have := hp L'.length (hc ▸ hl L')
      rw [List.getD_eq_default _ _ (by simp; omega)] at this
      simp at this
    · exact heq
    · exfalso
      have := hp L.length (hl L)
      rw [List.getD_eq_default (L' ++ [true]) _ (by simp; omega)] at this
      simp at this
  apply List.ext_getElem hlen
  intro i h1 h2
  have := hp i (h1.trans (hl L))
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)] at this
  rwa [List.getElem_append_left h1, List.getElem_append_left h2] at this

theorem unitsOf_eq_none {L : List Bool} {k : ℕ} : unitsOf ub L k = none ↔ ucount ub L ≤ k := by
  simp [unitsOf]

section Segments

variable {Γ : Type*} {c : ℕ}

/-- The bits of a word. -/
def bitsOf (cb : Γ → Fin c → Bool) (X : List Γ) : List Bool := X.flatMap fun a => List.ofFn (cb a)

theorem length_bitsOf (cb : Γ → Fin c → Bool) (X : List Γ) : (bitsOf cb X).length = X.length * c := by
  induction X with
  | nil => simp [bitsOf]
  | cons a X ih =>
    simp only [bitsOf, List.flatMap_cons, List.length_append, List.length_ofFn, List.length_cons] at *
    rw [ih]; ring

theorem bitsOf_inj {cb : Γ → Fin c → Bool} (hcb : Function.Injective cb) (hc : 0 < c) {X X' : List Γ}
    (h : bitsOf cb X = bitsOf cb X') : X = X' := by
  induction X generalizing X' with
  | nil =>
    cases X' with
    | nil => rfl
    | cons a X' =>
      have := congrArg List.length h
      rw [length_bitsOf, length_bitsOf] at this
      simp only [List.length_nil, List.length_cons, zero_mul] at this
      have : 0 < (X'.length + 1) * c := Nat.mul_pos (by omega) hc
      omega
  | cons a X ih =>
    cases X' with
    | nil =>
      have := congrArg List.length h
      rw [length_bitsOf, length_bitsOf] at this
      simp only [List.length_nil, List.length_cons, zero_mul] at this
      have : 0 < (X.length + 1) * c := Nat.mul_pos (by omega) hc
      omega
    | cons a' X' =>
      simp only [bitsOf, List.flatMap_cons] at h
      obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
      have e1 : a = a' := hcb (List.ofFn_injective h1)
      rw [e1, ih h2]

end Segments

end Nc
