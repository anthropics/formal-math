/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Tower.Defs
import Mathlib.Tactic.Ring

/-! # The recursion `cost`

It is monotone in the cost of a query if the costs of the solver and of the procedure are
(`costMono`); for costs of the shape own + calls·tc + queries·tq and own' + q'·t it is written out
for these shapes (`costShape`), and queries that cost x times as much make the whole cost at most x
times as much (`costSlowDown`). -/

public section

namespace QueryMachines.Tower

/-- Dearer queries make the tower dearer, if they make the solver and the procedure dearer. -/
theorem costMono {TS : ℕ → ℕ → ℕ → ℕ} {TI : ℕ → ℕ → ℕ} (hS : ∀ l tc tc' tq tq', tc ≤ tc' → tq ≤ tq' → TS l tc tq ≤ TS l tc' tq') (hI : ∀ l t t', t ≤ t' → TI l t ≤ TI l t') :
    ∀ l t t', t ≤ t' → cost TS TI l t ≤ cost TS TI l t'
  | 0, _, _, h => hS 0 _ _ _ _ le_rfl h
  | l + 1, _, _, h => hS _ _ _ _ _ (Nat.add_le_add_right (costMono hS hI l _ _ (Nat.add_le_add_right (hI l _ _ h) 2)) 2) h

/-- The shape of the solver's cost is monotone in the two prices. -/
theorem shapeS_mono (own calls qs : ℕ → ℕ) (l tc tc' tq tq' : ℕ) (h1 : tc ≤ tc') (h2 : tq ≤ tq') : shapeS own calls qs l tc tq ≤ shapeS own calls qs l tc' tq' :=
  Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left _ h1) _) (Nat.mul_le_mul_left _ h2)

/-- The shape of the procedure's cost is monotone in the price. -/
theorem shapeI_mono (own' q' : ℕ → ℕ) (l t t' : ℕ) (h : t ≤ t') : shapeI own' q' l t ≤ shapeI own' q' l t' := Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _

/-- The recursion written out for these shapes. -/
theorem costShape : CostShape := fun _ _ _ _ _ _ _ => rfl

/-- For these shapes, queries that cost x times as much make the whole cost at most x times as much. -/
theorem costSlowDown : CostSlowDown := by
  intro own calls qs own' q' l x y hx
  induction l generalizing y with
  | zero =>
    show own 0 + calls 0 * 0 + qs 0 * (x * y) ≤ x * (own 0 + calls 0 * 0 + qs 0 * y)
    have e : x * (own 0 + calls 0 * 0 + qs 0 * y) = x * own 0 + qs 0 * (x * y) := by ring
    have h1 : own 0 ≤ x * own 0 := Nat.le_mul_of_pos_left _ hx
    rw [e]; omega
  | succ l ih =>
    rw [costShape, costShape]
    have e1 : x * (own' l + q' l * y + 2) = x * own' l + q' l * (x * y) + 2 * x := by ring
    have h0 : own' l ≤ x * own' l := Nat.le_mul_of_pos_left _ hx
    have hD := (costMono (shapeS_mono own calls qs) (shapeI_mono own' q') l (own' l + q' l * (x * y) + 2) (x * (own' l + q' l * y + 2)) (by rw [e1]; omega)).trans (ih _)
    generalize cost (shapeS own calls qs) (shapeI own' q') l (own' l + q' l * (x * y) + 2) = D at hD ⊢
    generalize cost (shapeS own calls qs) (shapeI own' q') l (own' l + q' l * y + 2) = C at hD ⊢
    have e : x * (own (l + 1) + calls (l + 1) * (C + 2) + qs (l + 1) * y) = x * own (l + 1) + calls (l + 1) * (x * C + 2 * x) + qs (l + 1) * (x * y) := by ring
    have h1 : own (l + 1) ≤ x * own (l + 1) := Nat.le_mul_of_pos_left _ hx
    have h2 : calls (l + 1) * (D + 2) ≤ calls (l + 1) * (x * C + 2 * x) := Nat.mul_le_mul_left _ (by omega)
    rw [e]; omega

end QueryMachines.Tower
