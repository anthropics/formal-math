/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Prog
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

/-! # The numbers at the top of the descent

A network on g nodes with at most Ub shared bits in all and size P is rebalanced to an instance on K
nodes. This file bounds from above the label length `lamG` of that
instance and the exponents of the enumerations which the rebalancing makes, as inequalities between
natural numbers. No programs occur here. -/

@[expose] public section

namespace PaddedDescent.F.Arith

open PaddedDescent PaddedDescent.F

variable {K g Ub P X : ℕ}

/-- K³·lamG ≤ K³ + K·Ub + g·P. -/
theorem lamG_mul_le (K g Ub P : ℕ) : lamG K g Ub P * K ^ 3 ≤ K ^ 3 + K * Ub + g * P :=
  Nat.div_mul_le_self _ _

/-- With Q = K²·lamG: 4·Q ≤ 4·K² + 4·Ub + X, if 4·g·P ≤ K·X. -/
theorem four_sq_mul_lamG_le (hK : 0 < K) (hP : 4 * (g * P) ≤ K * X) :
    4 * (K ^ 2 * lamG K g Ub P) ≤ 4 * K ^ 2 + 4 * Ub + X := by
  have h := lamG_mul_le K g Ub P
  have key : K * (4 * (K ^ 2 * lamG K g Ub P)) ≤ K * (4 * K ^ 2 + 4 * Ub + X) := by nlinarith
  exact Nat.le_of_mul_le_mul_left key hK

/-- The states of a class at the top: the exponent is at most X. -/
theorem mul_div_le (hK : 0 < K) (hP : 4 * (g * P) ≤ K * X) : P * (2 * g / K) ≤ X := by
  have m1 : 2 * g / K * K ≤ 2 * g := Nat.div_mul_le_self _ _
  have h1 : K * (P * (2 * g / K)) ≤ 2 * (g * P) := by
    calc K * (P * (2 * g / K)) = P * (2 * g / K * K) := by ring
      _ ≤ P * (2 * g) := Nat.mul_le_mul_left _ m1
      _ = 2 * (g * P) := by ring
  exact Nat.le_of_mul_le_mul_left (by omega : K * (P * (2 * g / K)) ≤ K * X) hK

/-- The labels inside a class at the top: the exponent is at most X. -/
theorem size_le (hg : 0 < g) (hKg : K ≤ g) (hP : 4 * (g * P) ≤ K * X) : P ≤ X := by
  have h1 : K * X ≤ g * X := Nat.mul_le_mul_right _ hKg
  exact Nat.le_of_mul_le_mul_left (by omega : g * P ≤ g * X) hg

/-- The index of a table at the top: the exponent is at most K + 2·X + r, if Ub ≤ K·X + r. -/
theorem mul_lamG_le {r : ℕ} (hK : 0 < K) (hP : 4 * (g * P) ≤ K * X) (hU : Ub ≤ K * X + r) :
    (K - 1) * lamG K g Ub P ≤ K + 2 * X + r := by
  have h1 := four_sq_mul_lamG_le (Ub := Ub) hK hP
  have h2 : X ≤ K * X := Nat.le_mul_of_pos_left _ hK
  have h3 : r ≤ K * r := Nat.le_mul_of_pos_left _ hK
  have key : K * (K * lamG K g Ub P) ≤ K * (K + 2 * X + r) := by nlinarith
  exact le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) (Nat.le_of_mul_le_mul_left key hK)

/-- The arithmetic of `inv_top` with plain variables (A = 8963^t, B = 10000^t, q = K²·lamG, v =
u·2^s·X). -/
theorem inv_top_aux {A B q Z v X : ℕ} (h3 : A * (2 * v) ≤ B * X) (h4 : A * X ≤ B * X) (h5 : 4 * q ≤ 4 * Z + 4 * v + X) :
    A * q ≤ B * X + A * Z := by
  have h6 := Nat.mul_le_mul_left A h5
  nlinarith

/-- The bound 8963^t·(K²·lamG) ≤ 10000^t·X + 8963^t·Z for the instance at the top of the descent: if
Ub ≤ u·n + r, n ≤ 2^s·X and t levels make up for the factor 2·u·2^s. -/
theorem inv_top {t Z u r n s : ℕ} (hK : 0 < K) (hP : 4 * (g * P) ≤ K * X) (hU : Ub ≤ u * n + r) (hn : n ≤ 2 ^ s * X)
    (ht : 8963 ^ t * (2 * u * 2 ^ s) ≤ 10000 ^ t) (hZ : K ^ 2 + r ≤ Z) :
    8963 ^ t * (K ^ 2 * lamG K g Ub P) ≤ 10000 ^ t * X + 8963 ^ t * Z := by
  have h1 := four_sq_mul_lamG_le (Ub := Ub) hK hP
  have hab : 8963 ^ t ≤ 10000 ^ t := Nat.pow_le_pow_left (by norm_num) t
  have h2 : u * n ≤ u * 2 ^ s * X := by
    calc u * n ≤ u * (2 ^ s * X) := Nat.mul_le_mul_left _ hn
      _ = u * 2 ^ s * X := by ring
  have h3 : 8963 ^ t * (2 * (u * 2 ^ s * X)) ≤ 10000 ^ t * X := by
    calc 8963 ^ t * (2 * (u * 2 ^ s * X)) = 8963 ^ t * (2 * u * 2 ^ s) * X := by ring
      _ ≤ 10000 ^ t * X := Nat.mul_le_mul_right _ ht
  have h4 : 8963 ^ t * X ≤ 10000 ^ t * X := Nat.mul_le_mul_right _ hab
  have h5 : 4 * (K ^ 2 * lamG K g Ub P) ≤ 4 * Z + 4 * (u * 2 ^ s * X) + X := by omega
  exact inv_top_aux h3 h4 h5

end PaddedDescent.F.Arith
