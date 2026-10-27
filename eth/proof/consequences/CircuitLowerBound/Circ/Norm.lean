/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.InterfacesPolyT
import Mathlib.Tactic

/-! # Every circuit can be written as data in which a gate reads inputs and earlier gates only

A gate that names a wire that does not exist yet reads 0 there. Such a gate is replaced by a gate
that reads the wire 0 and ignores it: the function of the gate gets the value 0 built in. All wires
keep their values (`Norm.wires_norm`), so the circuit computes the same function with the same
number of gates (`stNorm`). The auxiliary statements are in the namespace `CircuitLowerBound.Norm`. -/

public section

namespace CircuitLowerBound

open ENP Groundwork

namespace Norm

/-- The function of the gate G when there are n wires: an input that names a wire that does not
exist is read as 0. -/
def op' (n : ℕ) (G : Gate) (x y : Bool) : Bool := G.op (decide (G.in₁ < n) && x) (decide (G.in₂ < n) && y)

/-- The gate G as data, when there are n wires. -/
def ng (n : ℕ) (G : Gate) : GateD :=
  ((op' n G false false, op' n G false true, op' n G true false, op' n G true true), if G.in₁ < n then G.in₁ else 0, if G.in₂ < n then G.in₂ else 0)

/-- The circuit as data, when there are n wires before its first gate. -/
def norm : ℕ → Circuit → List GateD
  | _, [] => []
  | n, G :: C => ng n G :: norm (n + 1) C

theorem toGate_op (n : ℕ) (G : Gate) (x y : Bool) : (ng n G).toGate.op x y = op' n G x y := by
  cases x <;> cases y <;> rfl

theorem length_norm (C : Circuit) (n : ℕ) : (norm n C).length = C.length := by
  induction C generalizing n with
  | nil => rfl
  | cons G C ih => simp [norm, ih]

/-- The gate `ng w.length G` has the value of G. -/
theorem value_ng (w : List Bool) (G : Gate) :
    (ng w.length G).toGate.op (w.getD (ng w.length G).toGate.in₁ false) (w.getD (ng w.length G).toGate.in₂ false)
      = G.op (w.getD G.in₁ false) (w.getD G.in₂ false) := by
  rw [toGate_op]
  change op' w.length G (w.getD (if G.in₁ < w.length then G.in₁ else 0) false) (w.getD (if G.in₂ < w.length then G.in₂ else 0) false) = _
  unfold op'
  by_cases h1 : G.in₁ < w.length <;> by_cases h2 : G.in₂ < w.length <;>
    simp [h1, h2]

/-- All wires keep their values. -/
theorem wires_norm (C : Circuit) (w : List Bool) : wires w (toC (norm w.length C)) = wires w C := by
  induction C generalizing w with
  | nil => rfl
  | cons G C ih =>
    have h := ih (w ++ [G.op (w.getD G.in₁ false) (w.getD G.in₂ false)])
    rw [List.length_append, List.length_singleton] at h
    change wires (w ++ [(ng w.length G).toGate.op (w.getD (ng w.length G).toGate.in₁ false) (w.getD (ng w.length G).toGate.in₂ false)])
      (toC (norm (w.length + 1) C)) = wires (w ++ [G.op (w.getD G.in₁ false) (w.getD G.in₂ false)]) C
    rw [value_ng, h]

/-- Every gate reads earlier wires only. -/
theorem wf_norm (C : Circuit) (n : ℕ) (hn : 1 ≤ n) : WF n (norm n C) := by
  induction C generalizing n with
  | nil => intro t h; simp [norm] at h
  | cons G C ih =>
    intro t h
    cases t with
    | zero =>
      change (if G.in₁ < n then G.in₁ else 0) < n + 0 ∧ (if G.in₂ < n then G.in₂ else 0) < n + 0
      constructor <;> split_ifs <;> omega
    | succ t =>
      have h' : t < (norm (n + 1) C).length := by simpa [norm] using h
      have := ih (n + 1) (by omega) t h'
      change (norm (n + 1) C)[t].2.1 < n + (t + 1) ∧ (norm (n + 1) C)[t].2.2 < n + (t + 1)
      omega

end Norm

open CircuitLowerBound.Norm

/-- Every circuit on m ≥ 1 input bits can be written as data in which every gate reads inputs and
earlier gates only, with the same number of gates. -/
theorem stNorm : StNorm := by
  intro m C hm
  refine ⟨norm m C, wf_norm C m hm, length_norm C m, fun x hx => ?_⟩
  unfold eval
  rw [← hx, wires_norm]

end CircuitLowerBound
