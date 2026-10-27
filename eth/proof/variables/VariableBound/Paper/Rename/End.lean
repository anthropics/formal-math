/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Top.Defs
public import VariableBound.Paper.Rename.Math
import VariableBound.Paper.Rename.Time
import UniformInK.Top.End

/-! # The last step that turns a counting machine into a deciding one

`anyBit` maps a word of bits to the word of one bit that says whether some bit of the word is 1. It
is polynomial-time, and on a number c < 2^(n+1) written in n + 1 bits it says whether c ≠ 0;
so applied to the number of satisfying assignments, written in binary, it gives the bit that says
whether the formula is satisfiable. -/

public section

namespace VariableBound.Rename

open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg MainTheoremForms
open Sat3 (CNF)

/-! ### The last step for deciding -/

/-- The word of one bit that says whether some bit of w is 1. -/
@[expose] def anyBit (w : List Bool) : List Bool := [w.any id]

/-- `anyBit` is polynomial-time. -/
theorem anyBit_polyT : PolyT anyBit := by
  unfold anyBit
  fun_prop

/-- On a number c < 2^(n+1) written in n + 1 bits, `anyBit` says whether c ≠ 0. -/
theorem anyBit_binary {n c : ℕ} (h : c < 2 ^ (n + 1)) : anyBit (SatK.binary n c) = [decide (c ≠ 0)] := by
  rw [anyBit, SatK.binary]
  congr 1
  rw [Bool.eq_iff_iff]
  simp only [List.any_map, List.any_eq_true, List.mem_range, Function.comp_apply, id, decide_eq_true_eq]
  constructor
  · rintro ⟨i, _, hi⟩ rfl
    simp at hi
  · intro hc
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hc
    refine ⟨i, ?_, hi⟩
    by_contra hlt
    have := Nat.testBit_lt_two_pow (h.trans_le (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hlt)))
    simp [this] at hi

end VariableBound.Rename
