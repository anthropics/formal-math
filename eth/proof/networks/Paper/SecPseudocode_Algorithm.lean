/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Paper.SecProof_Proof
public import StepMachines.Prog.BruteE
public import StepMachines.Prog.NetProg
public import StepMachines.Prog.NetRun
public import StepMachines.Prog.NetVal
public import StepMachines.Math.RebalanceArith
public import StepMachines.Prog.GridLoop
public import StepMachines.Prog.SidePresents
public import StepMachines.Prog.Sat
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import StepMachines.Math.SparsifyCount
public import NetworkStatements
public import Mathlib.Algebra.Polynomial.Coeff
public import ToTuring.Poly.Spec
public import ToTuring.Poly.Brute
public import ToTuring.Poly.NetFun
public import ToTuring.Poly.Basic
public import ToTuring.Poly.Range
public import ToTuring.Poly.Comb
public import ToTuring.Poly.GridSide
public import ToTuring.Poly.Count
public import ToTuring.Poly.Sat

/-! # Section 8 of the paper: the numbers K_ℓ and g_ℓ of display (38)

This file defines the numbers K_ℓ and g_ℓ = 3 K_ℓ⁸ of display (38), which set the levels of
Algorithm 1 of the paper, and proves simple facts about them:
K_{ℓ+1} = g_ℓ², K_ℓ ≥ 64, K_ℓ < K_{ℓ+1}, and ℓ < K_ℓ, so that K_ℓ grows without bound. -/

@[expose] public section

namespace Paper

open Groundwork Groundwork.Prog

/-! ## The levels: display (38) -/

/-- K_ℓ of display (38): K₀ = 64 and K_{ℓ+1} = 9 K_ℓ¹⁶. Same as in the paper. -/
def levelK : ℕ → ℕ
  | 0 => 64
  | ℓ + 1 => 9 * levelK ℓ ^ 16

/-- g_ℓ = 3 K_ℓ⁸ of display (38). Same as in the paper. -/
def levelG (ℓ : ℕ) : ℕ := 3 * levelK ℓ ^ 8

/-- K_{ℓ+1} = g_ℓ² (display (38)). -/
theorem levelK_succ (ℓ : ℕ) : levelK (ℓ + 1) = levelG ℓ * levelG ℓ := by
  simp only [levelK, levelG]
  ring

theorem levelK_ge (ℓ : ℕ) : 64 ≤ levelK ℓ := by
  induction ℓ with
  | zero => exact le_rfl
  | succ ℓ ih =>
    have h : levelK ℓ ≤ levelK ℓ ^ 16 := Nat.le_self_pow (by norm_num) _
    simp only [levelK]
    omega

theorem levelK_lt_succ (ℓ : ℕ) : levelK ℓ < levelK (ℓ + 1) := by
  have h : levelK ℓ ≤ levelK ℓ ^ 16 := Nat.le_self_pow (by norm_num) _
  have h64 := levelK_ge ℓ
  simp only [levelK]
  omega

/-- K_ℓ grows without bound. -/
theorem lt_levelK (ℓ : ℕ) : ℓ < levelK ℓ := by
  induction ℓ with
  | zero => norm_num [levelK]
  | succ ℓ ih => exact lt_of_le_of_lt ih (levelK_lt_succ ℓ)

end Paper
