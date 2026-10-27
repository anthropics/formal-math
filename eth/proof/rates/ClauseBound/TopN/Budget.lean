/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.TopN.Defs
import PaddedDescent.F.ArithWalk
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Products and sums below powers of two, and the parameters for width k

`mul_le_pow`, `add_le_pow`: products and sums of numbers below powers of two. `stParN : StParN`: 2^β
bounds the number of clauses per variable of a leaf (`leafC_le`),
and the number of layers is large enough (`last_le`). Statements about natural numbers. -/

namespace ClauseBound.TopN

open PaddedDescent PaddedDescent.F CountKSatRate
open WidthK (theta bsum leafC)

/-- A product of numbers below powers of two. -/
public theorem mul_le_pow {x y p q : ℕ} (hx : x ≤ 2 ^ p) (hy : y ≤ 2 ^ q) : x * y ≤ 2 ^ (p + q) := by
  rw [pow_add]; exact Nat.mul_le_mul hx hy

/-- A sum of two numbers below powers of two. -/
public theorem add_le_pow {x y p q r : ℕ} (hx : x ≤ 2 ^ p) (hy : y ≤ 2 ^ q) (hp : p < r) (hq : q < r) : x + y ≤ 2 ^ r := by
  obtain ⟨u, rfl⟩ : ∃ u, r = u + 1 := ⟨r - 1, by omega⟩
  have h1 : 2 ^ p ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ q ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega

/-- leafC τ k + 2 ≤ 2^β. -/
theorem leafC_le (k s : ℕ) : leafC (tauOf s) k + 2 ≤ 2 ^ betaN k s := by
  have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  obtain ⟨E, hE⟩ : ∃ E, E = (4 * s + 17) * 2 ^ k := ⟨_, rfl⟩
  have hE1 : 1 ≤ 2 ^ E := Nat.one_le_two_pow
  have h2 : E + k + 1 ≤ betaN k s := by
    have e1 : (4 * s + 17) * (2 ^ (k + 1) + 1) = 2 * E + (4 * s + 17) := by rw [hE, pow_succ]; ring
    unfold betaN
    omega
  calc leafC (tauOf s) k + 2 ≤ 2 * (k * 2 ^ E) + 2 * 2 ^ E := Nat.add_le_add (hE ▸ leafC_tauOf_le k s) (by omega)
    _ = 2 * ((k + 1) * 2 ^ E) := by ring
    _ ≤ 2 * (2 ^ k * 2 ^ E) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hk)
    _ = 2 ^ (E + k + 1) := by rw [pow_add, pow_add]; ring
    _ ≤ 2 ^ betaN k s := Nat.pow_le_pow_right (by norm_num) h2

/-- After 2β + 4 divisions, each of which keeps at most two thirds of the clauses, fewer than n + 2
of 2^β·n clauses are left. -/
theorem last_le (β : ℕ) {n : ℕ} (hn : 6 ≤ n) : 2 ^ (2 * β + 4) * (2 ^ β * n) + 5 * 3 ^ (2 * β + 4) ≤ 3 ^ (2 * β + 4) * (n + 2) := by
  obtain ⟨h, hh⟩ : ∃ h, h = β + 2 := ⟨_, rfl⟩
  have e : 2 * β + 4 = 2 * h := by omega
  have e2 : (2 : ℕ) ^ (2 * h) = 4 ^ h := by rw [pow_mul]; norm_num
  have e3 : (3 : ℕ) ^ (2 * h) = 9 ^ h := by rw [pow_mul]; norm_num
  have h2 : 2 * 2 ^ β ≤ 2 ^ h := by rw [hh, pow_add]; omega
  have h3 : 4 ^ h * 2 ^ h ≤ 9 ^ h := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by norm_num) h
  have h4 : 2 * (4 ^ h * 2 ^ β) ≤ 9 ^ h := by
    calc 2 * (4 ^ h * 2 ^ β) = 4 ^ h * (2 * 2 ^ β) := by ring
      _ ≤ 4 ^ h * 2 ^ h := Nat.mul_le_mul_left _ h2
      _ ≤ 9 ^ h := h3
  rw [e, e2, e3]
  obtain ⟨A, hA⟩ : ∃ A, A = 9 ^ h := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = 4 ^ h * 2 ^ β := ⟨_, rfl⟩
  have e4 : 4 ^ h * (2 ^ β * n) = D * n := by rw [hD]; ring
  rw [e4, ← hA]
  rw [← hD, ← hA] at h4
  nlinarith

/-- The parameters are large enough for width k. -/
public theorem stParN : StParN := fun k _ s => ⟨leafC_le k s, fun hn => last_le (betaN k s) hn⟩

end ClauseBound.TopN
