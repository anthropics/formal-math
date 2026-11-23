/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Tensors

/-!
# The values of a spectral point at wires

The parts of Lemma lem:exponents (`Paper/Tensors.lean`) in the form in which the development cites them, and what follows
at once for tensors whose legs are moved.
-/

set_option linter.unusedSectionVars false

namespace Ov

open Finset

namespace Spec

open Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (F : Spec K I)

/-- φ(⟨n⟩_P) = n^g with g = log₂ φ(⟨2⟩_P), wherever the legs are. -/
theorem unit_eq [Nonempty I] (π : J → I) {n : ℕ} (hn : 1 ≤ n) :
    F.F (Ten.push π (unit K J n)) = (n : ℝ) ^ Real.logb 2 (F.F (Ten.push π (unit K J 2))) :=
  (Paper.lem_exponents_power F π).2 n hn

/-- φ(⟨n⟩_pq) = n^(d_φ(p,q)). -/
theorem wire_eq (p q : I) {n : ℕ} (hn : 1 ≤ n) : F.F (wire K n p q) = (n : ℝ) ^ F.e p q :=
  Paper.lem_exponents_wire F p q hn

/-- φ(⟨2⟩_pq) = 2^(d_φ(p,q)). -/
theorem wire_two (p q : I) : F.F (wire K 2 p q) = 2 ^ F.e p q := Paper.lem_exponents_wire_two F p q

/-- φ(⟨n⟩_pq) ≤ n^(d_φ(p,q)), also for n = 0. -/
theorem wire_le (p q : I) (n : ℕ) : F.F (wire K n p q) ≤ (n : ℝ) ^ F.e p q := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : F.F (wire K 0 p q) ≤ (0 : ℕ) := F.unit_le ![p, q] 0
    exact this.trans (by exact_mod_cast Real.rpow_nonneg le_rfl _)
  · exact (F.wire_eq p q hn).le

/-- Distances are not negative. -/
theorem e_nonneg (p q : I) : 0 ≤ F.e p q := (Paper.lem_exponents_unit_interval F p q).1

/-- Distances are at most 1. -/
theorem e_le_one (p q : I) : F.e p q ≤ 1 := (Paper.lem_exponents_unit_interval F p q).2

/-- The distance from a party to itself is 0. -/
theorem e_self (p : I) : F.e p p = 0 := Paper.lem_exponents_self F p

/-- Distances are symmetric. -/
theorem e_comm (p q : I) : F.e p q = F.e q p := Paper.lem_exponents_symm F p q

/-- A tensor with all its legs at one party costs at most 1. -/
theorem push_const_le (q : I) (t : Ten K J) : F.F (Ten.push (fun _ => q) t) ≤ 1 := by
  rw [← F.one]
  exact F.mono (Restr.push_const q t)

/-- Moving legs: if the leg j moves from π' j to π j, the value grows at most by the values of wires
between π j and π' j that have the dimensions of the legs. -/
theorem push_le_move (π π' : J → I) (t : Ten K J) :
    F.F (Ten.push π t) ≤
      (∏ j, (Fintype.card (t.ι j) : ℝ) ^ F.e (π j) (π' j)) * F.F (Ten.push π' t) := by
  refine (F.le_mul (Restr.move π π' t)).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (F.nonneg _)
  rw [F.prod]
  exact Finset.prod_le_prod (fun _ _ => F.nonneg _) fun j _ => F.wire_le _ _ _

/-- The distances of a pull-back. -/
theorem pull_e (π : J → I) (p q : J) : (F.pull π).e p q = F.e (π p) (π q) := by
  rw [e, e, pull_F]
  congr 1
  refine F.congr ((Equi.push_push π ![p, q] (unit K (Fin 2) 2)).trans ?_)
  have : π ∘ ![p, q] = ![π p, π q] := by funext i; fin_cases i <;> rfl
  rw [this]
  exact Equi.refl _

end Spec

end Ov
