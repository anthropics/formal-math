/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.Spec
public import StepMachines.Prog.Comb

/-! Lemmas on the sizes of lists of booleans and of natural numbers (bookkeeping with no counterpart
in the paper), and a lemma that writes a map over `List.range` as `List.ofFn`. -/

@[expose] public section

namespace Groundwork.Prog

open Finset Stepped

theorem size_bools (w : List Bool) : size w = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [size_list, List.map_cons, List.sum_cons, size_bool, List.length_cons] at ih ⊢; omega

theorem size_nat_le (n : ℕ) : size n ≤ n + 1 := by
  rw [size_nat]
  exact Nat.succ_le_succ (Nat.size_le.2 Nat.lt_two_pow_self)

theorem size_nat_mono {m n : ℕ} (h : m ≤ n) : size m ≤ size n := by
  rw [size_nat, size_nat]
  exact Nat.succ_le_succ (Nat.size_le_size h)

theorem size_two_pow (k : ℕ) : size (2 ^ k) = k + 2 := by
  rw [size_nat, Nat.size_pow]

theorem map_range_eq_ofFn {α : Type} (n : ℕ) (f : ℕ → α) : (List.range n).map f = List.ofFn fun u : Fin n => f u := by
  apply List.ext_getElem <;> simp

end Groundwork.Prog
