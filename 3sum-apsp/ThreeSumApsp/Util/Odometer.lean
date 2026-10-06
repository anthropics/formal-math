/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Index
public import Mathlib.Data.List.Range

/-!
# Counting in base `b` without division: an odometer

The word RAM has no division.  A program that runs through all strings of `n` digits, for instance
through all choices of one vertex in each part of a graph (Corollary 39), keeps the digits of a
number that grows by 1.  `incDigits` is the step, and it counts: it takes the digits of `c` to the
digits of `c + 1` (`incDigits_digitsLE`).
-/

@[expose] public section

namespace ThreeSumApsp

/-- Add 1 to a number given by its digits in base `b`, least significant digit first (an odometer);
a carry out of the most significant digit is dropped. -/
def incDigits (b : ℕ) : List ℕ → List ℕ
  | [] => []
  | d :: l => if d + 1 < b then (d + 1) :: l else 0 :: incDigits b l

/-- The `n` digits of `c` in base `b`, least significant first, which is the order in which an
odometer runs through them. -/
def digitsLE (b n c : ℕ) : List ℕ := (List.range n).map fun k => c / b ^ k % b

/-- There are `n` digits. -/
@[simp] theorem length_digitsLE (b n c : ℕ) : (digitsLE b n c).length = n := by
  simp [digitsLE]

/-- The digits in base `b` are below `b`. -/
theorem lt_of_mem_digitsLE {b : ℕ} (hb : 0 < b) {n c x : ℕ} (hx : x ∈ digitsLE b n c) : x < b := by
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
  exact Nat.mod_lt _ hb

/-- The least significant digit, and the digits of the quotient by `b`. -/
private theorem digitsLE_succ (b n c : ℕ) :
    digitsLE b (n + 1) c = c % b :: digitsLE b n (c / b) := by
  unfold digitsLE
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp [Function.comp_def, Nat.pow_succ', Nat.div_div_eq_div_mul]

/-- The odometer counts: adding 1 to the `n` digits of `c` gives the `n` digits of `c + 1`. -/
theorem incDigits_digitsLE {b : ℕ} (hb : 0 < b) (n c : ℕ) :
    incDigits b (digitsLE b n c) = digitsLE b n (c + 1) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    have hdigit : c % b < b := Nat.mod_lt c hb
    rw [digitsLE_succ, digitsLE_succ, incDigits]
    split_ifs with hlt
    · -- No carry: the least significant digit grows by 1, and the quotient by `b` stays.
      obtain ⟨hdiv, hmod⟩ := Nat.succ_div_mod_of_lt hlt
      rw [hdiv, hmod]
    · -- A carry: the least significant digit becomes 0, and the quotient by `b` grows by 1.
      obtain ⟨hdiv, hmod⟩ := Nat.succ_div_mod_of_eq (show c % b + 1 = b by omega)
      rw [hdiv, hmod, ih]

end ThreeSumApsp
