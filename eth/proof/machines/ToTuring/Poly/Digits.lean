/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Lib.Unary
public import StepMachines.Prog.GridDefs

/-! Polynomial time for the patterns ι of one level of the recursion (ι(q) is the digit number q of
a number in base λ+1) and for
the lengths of the bit strings that encode the labels of the grouping step (`tb`, `capW`); and
`sum_range_eq_list`, which turns a sum
over `Finset.range` into the sum of a list. -/

@[expose] public section

namespace Groundwork

variable {α : Type} [Enc α]

/-- A sum over `Finset.range` as the sum of a list, the form in which it is polynomial-time. -/
theorem sum_range_eq_list (R : ℕ) (f : ℕ → ℕ) : ∑ q ∈ Finset.range R, f q = ((List.range R).map f).sum := by
  induction R with
  | zero => simp
  | succ R ih => simp [Finset.sum_range_succ, List.range_succ, ih]

/-- The digit number q of y in base n + 1. -/
@[fun_prop] theorem digit_polyT {n y q : α → ℕ} (h1 : PolyT n) (h2 : PolyT y) (h3 : PolyT q) :
    PolyT fun x => Prog.digit (n x) (y x) (q x) := by
  unfold Prog.digit; fun_prop

theorem tb_polyT {f : α → ℕ} (hf : Unary f) : PolyT fun a => Prog.tb (f a) := by
  have := PolyT.pow_unary (b := fun _ : α => 3) (by fun_prop) hf
  unfold Prog.tb; fun_prop

theorem tb_unary {f : α → ℕ} (hf : Unary f) : Unary fun a => Prog.tb (f a) :=
  (((Unary.const 2).mul hf).add (Unary.const 1)).of_le (tb_polyT hf) fun _ => Prog.tb_le _

theorem capW_unary {n c : α → ℕ} (hn : Unary n) (hc : Unary c) : Unary fun a => Prog.capW (n a) (c a) :=
  hn.add (tb_unary hc)

/-- The length of the bit string of a label when the bound c on the number of symbols is a number in
binary that is at most
the length n, which is given in unary. -/
theorem capW_polyT {n c : α → ℕ} (hn : Unary n) (hc : PolyT c) (h : ∀ a, c a ≤ n a) :
    PolyT fun a => Prog.capW (n a) (c a) :=
  (capW_unary hn (hn.of_le hc h)).poly

end Groundwork
