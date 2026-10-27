/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Sat3Graph.Defs
import SplitSat.Leaf
import SizeCircuit.General
import GraphProblems.Engine
import Mathlib.Tactic

/-! # Splitting long clauses into clauses of 3 literals with new variables

General facts used by the proofs of the statements of proof/consequences/Sat3Graph/Defs.lean.
* `splitN_spec`: for a formula x with variables below n, the formula with its long clauses split is
  a 3-CNF on n + `numFresh x` variables, no clause twice, and it is satisfiable exactly if x is.
  This is the argument of `SplitSat.stLeaf` without its bound on the number of clauses.
* The number of new variables `numFresh`: it adds up over `++`, is 0 at width 3 (from
  `Eight.Width.numFresh_le`: at most (w − 3)·(number of clauses) at width w), and striking out
  repeated clauses does not make it larger.
* `sat_iff_cntN`: a formula with variables below N is satisfiable exactly if its number of
  satisfying assignments on N variables is not 0. `cntN_of_dedup`: striking out repeated clauses
  does not change that number.
* `exists_bounds`: if the 3-CNF has N ≤ A·(n+1) variables and δ₃·A ≤ δ, then c·2^{δ₃N} steps are at
  most c'·2^{δn} steps, and states of size c·(N+2)^c have size at most c'·(n+2)^{c'}. -/

public section

namespace Sat3Graph

open Groundwork Groundwork.Prog CountKSat GraphProblems Eight.Width

/-- For a formula x with variables below n: the formula with its long clauses split has at most 3
literals per clause, variables below n + (number of new variables), no clause twice, and is
satisfiable exactly if x is. -/
theorem splitN_spec {n : ℕ} {x : Fml} (hx : ∀ C ∈ x, ∀ l ∈ C, l.1 < n) :
    (∀ C ∈ splitN n x, C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n + numFresh x) ∧ (splitN n x).Nodup ∧ ((splitN n x).Sat ↔ x.Sat) := by
  obtain ⟨φ, rfl⟩ := exists_toN hx
  rw [← toN_widthReduce, numFresh_toN]
  obtain ⟨h3, -, -⟩ := stWidth n φ
  refine ⟨fun C hC => ?_, SplitSat.nodup_toN h3.2,
    (Decode.satN_toN _).trans ((SplitSat.satisfiable_widthReduce φ).trans (Decode.satN_toN φ).symm)⟩
  obtain ⟨⟨C', hC', hl'⟩, h⟩ := Decode.mem_toN hC
  exact ⟨hl' ▸ h3.1 C' hC', h⟩

/-- The numbers of new variables of two formulas add up. -/
theorem numFresh_append (x y : Fml) : numFresh (x ++ y) = numFresh x + numFresh y := by
  simp only [numFresh, List.map_append, List.sum_append]

/-- At width 3 there is no new variable. -/
theorem numFresh_eq_zero {x : Fml} (h : ∀ C ∈ x, C.length ≤ 3) : numFresh x = 0 := by
  have := Eight.Width.numFresh_le 3 x h
  simpa using this

/-- Striking out repeated clauses does not make the number of new variables larger. -/
theorem numFresh_dedup_le : ∀ x : Fml, numFresh x.dedup ≤ numFresh x
  | [] => le_rfl
  | C :: x => by
    have ih := numFresh_dedup_le x
    by_cases h : C ∈ x
    · rw [List.dedup_cons_of_mem h, numFresh_cons]
      omega
    · rw [List.dedup_cons_of_notMem h, numFresh_cons, numFresh_cons]
      omega

/-- A formula with variables below N is satisfiable exactly if its number of satisfying assignments
on N variables is not 0. -/
theorem sat_iff_cntN {N : ℕ} {x : Fml} (hx : ∀ C ∈ x, ∀ l ∈ C, l.1 < N) : x.Sat ↔ cntN N x ≠ 0 := by
  unfold cntN
  rw [← Nat.pos_iff_ne_zero, Finset.card_pos, Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun i => a i.1, Finset.mem_univ _, ?_⟩
    exact (SizeCircuit.holds_congr (a := ext fun i : Fin N => a i.1) (a' := a) fun C hC l hl => by
      rw [SizeCircuit.ext_of_lt _ (hx C hC l hl)]).2 ha
  · rintro ⟨b, -, hb⟩
    exact ⟨ext b, hb⟩

/-- Striking out repeated clauses does not change the number of satisfying assignments. -/
theorem cntN_of_dedup (N : ℕ) (ψ : Fml) : cntN N ψ.dedup = cntN N ψ := by
  unfold cntN
  exact congrArg Finset.card (Finset.filter_congr fun a _ => by simp only [List.mem_dedup])

/-- **The arithmetic of all bounds.** Let δ₃ ≥ 0 and δ₃·A ≤ δ. There is c' such that, whenever N ≤
A·(n+1) and T ≤ c·2^{δ₃N}: c·(N+2)^c ≤ c'·(n+2)^{c'} and T ≤ c'·2^{δn}. -/
theorem exists_bounds (A c : ℕ) {δ δ₃ : ℝ} (h0 : 0 ≤ δ₃) (hle : δ₃ * (A : ℝ) ≤ δ) : ∃ c' : ℕ, ∀ n N T : ℕ, N ≤ A * (n + 1) →
    (T : ℝ) ≤ c * (2 : ℝ) ^ (δ₃ * N) → c * (N + 2) ^ c ≤ c' * (n + 2) ^ c' ∧ (T : ℝ) ≤ c' * (2 : ℝ) ^ (δ * n) := by
  obtain ⟨c₁, hc₁⟩ := exists_nat_ge ((c : ℝ) * (2 : ℝ) ^ δ)
  obtain ⟨C', hC'⟩ : ∃ C', C' = c₁ + c * (A + 2) ^ c + c := ⟨_, rfl⟩
  have k1 : c₁ ≤ C' := by rw [hC', Nat.add_assoc]; exact Nat.le_add_right _ _
  have k2 : c * (A + 2) ^ c ≤ C' := by rw [hC']; exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  have k3 : c ≤ C' := by rw [hC']; exact Nat.le_add_left _ _
  refine ⟨C', fun n N T hN hT => ⟨?_, ?_⟩⟩
  · obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
    rw [← hX]
    have hX1 : 1 ≤ X := by omega
    have h3 : N + 2 ≤ (A + 2) * X := by
      have e1 : A * (n + 1) ≤ A * X := Nat.mul_le_mul_left _ (by omega)
      have e2 : (A + 2) * X = A * X + 2 * X := by ring
      omega
    calc c * (N + 2) ^ c ≤ c * ((A + 2) * X) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 _)
      _ = c * (A + 2) ^ c * X ^ c := by rw [Nat.mul_pow, Nat.mul_assoc]
      _ ≤ C' * X ^ C' := Nat.mul_le_mul k2 (Nat.pow_le_pow_right hX1 k3)
  · have hN' : (N : ℝ) ≤ (A : ℝ) * ((n : ℝ) + 1) := by exact_mod_cast hN
    have h1 : δ₃ * N ≤ δ * n + δ := by
      calc δ₃ * N ≤ δ₃ * ((A : ℝ) * ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_left hN' h0
        _ = δ₃ * (A : ℝ) * ((n : ℝ) + 1) := by ring
        _ ≤ δ * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_right hle (by positivity)
        _ = δ * n + δ := by ring
    have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (δ * n) := by positivity
    calc (T : ℝ) ≤ c * (2 : ℝ) ^ (δ₃ * N) := hT
      _ ≤ c * (2 : ℝ) ^ (δ * n + δ) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two h1) (Nat.cast_nonneg c)
      _ = c * (2 : ℝ) ^ δ * (2 : ℝ) ^ (δ * n) := by
        rw [Real.rpow_add two_pos]
        ring
      _ ≤ c₁ * (2 : ℝ) ^ (δ * n) := mul_le_mul_of_nonneg_right hc₁ hp
      _ ≤ C' * (2 : ℝ) ^ (δ * n) := mul_le_mul_of_nonneg_right (Nat.cast_le.2 k1) hp

end Sat3Graph
