/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Lib.Int
public import ToTuring.Lib.List3
public import ToTuring.Lib.List2
public import ToTuring.Lib.Unary
public import ToTuring.Lib.Nat2
public import ToTuring.Lib.Nat1b

/-! # Loops cut off by a pad

`U` is a number in unary; the pad is a `U`. Every enumeration of exponentially many things runs over
`rng pad q` (or `sumF q pad`), that is over 0, …, min q (length of the pad) − 1; every loop whose
state could grow puts `cap pad d` around
the state after each round. So all functions built this way are polynomial-time in (pad, arguments)
without any side condition, and the
mathematics is only needed to show that, for a long enough pad, no cut-off is active (`rng_eq`,
`sumF_eq`, `cap_eq`). -/

@[expose] public section

namespace PaddedDescent.F

open Groundwork

/-- A number in unary. -/
abbrev U := List Unit

/-- 0, …, q − 1, cut off at the length of the pad. -/
def rng (pad : U) (q : ℕ) : List ℕ := List.range (min q pad.length)

/-- Σ_{y < N} f y, cut off at the length of the pad. -/
def sumF (N : ℕ) (pad : U) (f : ℕ → ℤ) : ℤ :=
  (List.range (min N pad.length)).foldl (fun acc y => acc + f y) 0

/-- ∏_{y < n} f y (n is small: no cut-off). -/
def prodL (n : ℕ) (f : ℕ → ℤ) : ℤ := (List.range n).foldl (fun acc y => acc * f y) 1

/-- x if its word is no longer than the pad, else d. -/
def cap {γ : Type} [Enc γ] (pad : U) (d x : γ) : γ := if len x ≤ pad.length then x else d

/-- The length of the word of a value can be computed in polynomial time. -/
class Meas (α : Type) [Enc α] : Prop where
  poly : PolyT (fun x : α => len x)

theorem rng_eq {pad : U} {q : ℕ} (h : q ≤ pad.length) : rng pad q = List.range q := by
  rw [rng, min_eq_left h]

theorem sumF_eq {N : ℕ} {pad : U} (h : N ≤ pad.length) (f : ℕ → ℤ) :
    sumF N pad f = ∑ y ∈ Finset.range N, f y := by
  unfold sumF
  rw [min_eq_left h]
  clear h
  induction N with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih]

theorem prodL_eq (n : ℕ) (f : ℕ → ℤ) : prodL n f = ∏ y ∈ Finset.range n, f y := by
  unfold prodL
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.prod_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih]

theorem cap_eq {γ : Type} [Enc γ] {pad : U} {d x : γ} (h : len x ≤ pad.length) : cap pad d x = x := if_pos h

theorem len_cap_le {γ : Type} [Enc γ] (pad : U) (d x : γ) : len (cap pad d x) ≤ pad.length + len d := by
  unfold cap; split_ifs <;> omega

end PaddedDescent.F
