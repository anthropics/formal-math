/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.TopDefs
import PaddedDescent.F.ArithWalk
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # What a pad of length 2^(restO …) suffices for

`stBudgetO : StBudgetO`: the list of profiles, the lists of the checks, the rounds of the walk
through the counting tree and its stack. Statements about natural numbers; every factor is
bounded by a power of two, and each of the four summands of `restO` pays for one of the four
budgets. The last two budgets and their proofs are those of
proof/rates/ClauseBound/TopN/Budget.lean. -/

namespace ClauseBound.ParityChecks.BudgetOL

open PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.TopN ClauseBound.ParityChecks
open WidthK (bsum)

/-- A product of numbers below powers of two. -/
theorem mul_le_pow {x y p q : ℕ} (hx : x ≤ 2 ^ p) (hy : y ≤ 2 ^ q) : x * y ≤ 2 ^ (p + q) := by
  rw [pow_add]; exact Nat.mul_le_mul hx hy

/-- A sum of two numbers below powers of two. -/
theorem add_le_pow {x y p q r : ℕ} (hx : x ≤ 2 ^ p) (hy : y ≤ 2 ^ q) (hp : p < r) (hq : q < r) : x + y ≤ 2 ^ r := by
  obtain ⟨u, rfl⟩ : ∃ u, r = u + 1 := ⟨r - 1, by omega⟩
  have h1 : 2 ^ p ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ q ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega

/-- n + 1 ≤ 2^(size n). -/
theorem succ_le_size (n : ℕ) : n + 1 ≤ 2 ^ Nat.size n := Nat.lt_size_self n

/-- The word of a clause: k·(3n+5) + 10 ≤ 2^(k + size n + 4). -/
theorem clause_le (k n : ℕ) : k * (3 * n + 5) + 10 ≤ 2 ^ (k + Nat.size n + 4) := by
  have h1 := succ_le_size n
  have h2 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have h3 : (k + 1) * (n + 1) ≤ 2 ^ k * 2 ^ Nat.size n := Nat.mul_le_mul h2 h1
  have h4 : k * (3 * n + 5) + 10 ≤ 16 * ((k + 1) * (n + 1)) := by nlinarith
  calc k * (3 * n + 5) + 10 ≤ 16 * (2 ^ k * 2 ^ Nat.size n) := h4.trans (Nat.mul_le_mul_left _ h3)
    _ = 2 ^ (k + Nat.size n + 4) := by rw [pow_add, pow_add]; ring

/-- bsum τ k ≤ 2^β. -/
theorem bsum_le (k s : ℕ) : bsum (tauOf s) k ≤ 2 ^ betaN k s := by
  refine (bsum_tauOf_le k s).trans (Nat.pow_le_pow_right (by norm_num) ?_)
  have e : (4 * s + 17) * (2 ^ (k + 1) + 1) = (4 * s + 17) * 2 ^ (k + 1) + (4 * s + 17) := by ring
  unfold betaN
  omega

/-- The length of the code of an instance: inLen k n ≤ 2^(3k + 1 + (k+1)·size n). -/
theorem inLen_le (k n : ℕ) : inLen k n ≤ 2 ^ (3 * k + 1 + (k + 1) * Nat.size n) := by
  have h1 := succ_le_size n
  have h2 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have h3 : k * 2 ^ k + 1 ≤ 2 ^ (k + k) := by
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    calc k * 2 ^ k + 1 ≤ (k + 1) * 2 ^ k := by nlinarith
      _ ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul_right _ h2
      _ = 2 ^ (k + k) := (pow_add _ _ _).symm
  have h4 : n + 2 ≤ 2 ^ (Nat.size n + 1) := by rw [pow_succ]; omega
  have h5 : (n + 2) ^ (k + 1) ≤ 2 ^ ((Nat.size n + 1) * (k + 1)) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left h4 _
  unfold inLen
  refine (mul_le_pow h3 h5).trans (Nat.pow_le_pow_right (by norm_num) (le_of_eq ?_))
  ring

/-- The list of profiles: (M + 1)^(g·g·3) ≤ 2^(g·g·3·size M). -/
theorem nProf_le (g M : ℕ) : Mark.nProf g M 3 ≤ 2 ^ (g * g * 3 * Nat.size M) := by
  unfold Mark.nProf
  calc (M + 1) ^ (g * g * 3) ≤ (2 ^ Nat.size M) ^ (g * g * 3) := Nat.pow_le_pow_left (succ_le_size M) _
    _ = 2 ^ (g * g * 3 * Nat.size M) := by rw [← pow_mul, Nat.mul_comm (Nat.size M)]

/-- The lists of the checks: 8(6n+1)(m+1)(size m + 2) + 8 ≤ 2^(3·size m + 3·size n + 12). -/
theorem checks_le (n m : ℕ) : 8 * (6 * n + 1) * (m + 1) * (Nat.size m + 2) + 8 ≤ 2 ^ (3 * Nat.size m + 3 * Nat.size n + 12) := by
  obtain ⟨a, ha⟩ : ∃ a, a = Nat.size m := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = Nat.size n := ⟨_, rfl⟩
  rw [← ha, ← hz]
  have h1 : m + 1 ≤ 2 ^ a := ha ▸ succ_le_size m
  have h2 : n + 1 ≤ 2 ^ z := hz ▸ succ_le_size n
  have h3 : 8 * (6 * n + 1) ≤ 2 ^ (z + 6) := by rw [pow_add]; omega
  have h4 : a + 2 ≤ 2 ^ (a + 1) := by
    have : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self
    rw [pow_succ]
    omega
  have h5 : 8 * (6 * n + 1) * (m + 1) * (a + 2) ≤ 2 ^ (z + 6 + a + (a + 1)) := mul_le_pow (mul_le_pow h3 h1) h4
  exact add_le_pow h5 (by norm_num : 8 ≤ 2 ^ 3) (by omega) (by omega)

/-- The stack of the walk. -/
theorem stack_le {k : ℕ} (hk : 1 ≤ k) (n s : ℕ) : stackLenC k (tauOf s) n (inLen k n) ≤ 2 ^ (betaN k s + 5 * k + 10 + (k + 3) * Nat.size n) := by
  obtain ⟨β, hβ⟩ : ∃ β, β = betaN k s := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = Nat.size n := ⟨_, rfl⟩
  obtain ⟨kz, hkz⟩ : ∃ kz, kz = k * z := ⟨_, rfl⟩
  have hn1 : n + 1 ≤ 2 ^ z := hz ▸ succ_le_size n
  have hcl : k * (3 * n + 5) + 10 ≤ 2 ^ (k + z + 4) := hz ▸ clause_le k n
  have hB1 : 1 ≤ 2 ^ β := Nat.one_le_two_pow
  have he : betaN k s + 5 * k + 10 + (k + 3) * Nat.size n = β + 5 * k + 10 + (kz + 3 * z) := by
    rw [← hβ, ← hz, hkz]
    ring
  rw [he]
  unfold stackLenC
  have b1 : bsum (tauOf s) k * n + 1 ≤ 2 ^ (β + z) := by
    have hb : bsum (tauOf s) k ≤ 2 ^ β := hβ ▸ bsum_le k s
    calc bsum (tauOf s) k * n + 1 ≤ 2 ^ β * n + 1 := Nat.add_le_add_right (Nat.mul_le_mul_right _ hb) _
      _ ≤ 2 ^ β * (n + 1) := by nlinarith
      _ ≤ 2 ^ β * 2 ^ z := Nat.mul_le_mul_left _ hn1
      _ = 2 ^ (β + z) := (pow_add _ _ _).symm
  have hin : inLen k n ≤ 2 ^ (3 * k + 1 + (kz + z)) := by
    have h := inLen_le k n
    rw [← hz, show (k + 1) * z = k * z + z by ring, ← hkz] at h
    exact h
  have b2 : 2 ^ k * inLen k n * (k * (3 * n + 5) + 10) ≤ 2 ^ (k + (3 * k + 1 + (kz + z)) + (k + z + 4)) :=
    mul_le_pow (mul_le_pow le_rfl hin) hcl
  have b3 : 2 * n * (2 * (3 * n + 5) + 10) + 8 ≤ 2 ^ (z + z + 6) := by
    have h1 : (n + 1) * (n + 1) ≤ 2 ^ z * 2 ^ z := Nat.mul_le_mul hn1 hn1
    have h2 : 2 * n * (2 * (3 * n + 5) + 10) + 8 ≤ 64 * ((n + 1) * (n + 1)) := by nlinarith
    calc 2 * n * (2 * (3 * n + 5) + 10) + 8 ≤ 64 * (2 ^ z * 2 ^ z) := h2.trans (Nat.mul_le_mul_left _ h1)
      _ = 2 ^ (z + z + 6) := by rw [pow_add, pow_add]; ring
  have b4 : 2 ^ k * inLen k n * (k * (3 * n + 5) + 10) + (2 * n * (2 * (3 * n + 5) + 10) + 8) ≤ 2 ^ (5 * k + 6 + kz + 2 * z) :=
    add_le_pow b2 b3 (by omega) (by omega)
  have b5 : (bsum (tauOf s) k * n + 1) * (2 ^ k * inLen k n * (k * (3 * n + 5) + 10) + 2 * n * (2 * (3 * n + 5) + 10) + 8) ≤
      2 ^ (β + z + (5 * k + 6 + kz + 2 * z)) := by
    rw [Nat.add_assoc (2 ^ k * inLen k n * (k * (3 * n + 5) + 10))]
    exact mul_le_pow b1 b4
  have b6 : 3 * n + 16 ≤ 2 ^ (z + 4) := by rw [pow_add]; omega
  have b7 := add_le_pow (r := β + 5 * k + 10 + (kz + 3 * z)) b5 b6 (by omega) (by omega)
  rw [Nat.add_assoc]
  exact b7

/-- Each of four summands is at most the sum. -/
theorem le_four (a b c d : ℕ) : a ≤ a + b + c + d ∧ b ≤ a + b + c + d ∧ c ≤ a + b + c + d ∧ d ≤ a + b + c + d := by omega

/-- The four budgets. -/
public theorem stBudgetO : StBudgetO := by
  intro k K n s F hk hs hF
  have up : ∀ {x t : ℕ}, x ≤ 2 ^ t → t ≤ restO k K n s → x ≤ F := fun h1 h2 => h1.trans ((Nat.pow_le_pow_right (by norm_num) h2).trans hF)
  refine ⟨up (nProf_le _ _) (le_four _ _ _ _).1, up (checks_le _ _) (le_four _ _ _ _).2.1, ?_, up (stack_le hk n s) (le_four _ _ _ _).2.2.2⟩
  have h1 := Arith.sum_choose_le_two_pow hs n
  have h2 : 2 ^ (n / 2 ^ s + 1 + 1) ≤ F := up le_rfl (le_four _ _ _ _).2.2.1
  rw [pow_succ] at h2
  omega

end ClauseBound.ParityChecks.BudgetOL
