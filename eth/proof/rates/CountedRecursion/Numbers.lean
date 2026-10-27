/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.AnswersDefs
public import ToTuring.Poly.Range
public import ToTuring.Poly.Comb
public import ToTuring.Lib.Unary
import Mathlib.Tactic

/-! # The numbers of a level, written in unary by a loop

`numbersM x₀` has ℓ rounds; a round costs two steps (one of the body, which does nothing, and one of
the loop) and replaces (2^{3j+x₀}, K_j) by (2^{3(j+1)+x₀}, K_{j+1}). So it returns (2^{3ℓ+x₀}, K_ℓ)
after 2ℓ steps (`numbersRun`). Its states hold ℓ in unary twice, a counter, and the pair:
at most 6ℓ + 8 + 2·2^{3ℓ+x₀} + 2K_ℓ ≤ 18·g_ℓ. A round is polynomial-time in the pair
(`numbersPoly`). -/

public section

namespace ExplicitCost

open Groundwork QueryMachines Printed

/-- The length of a number in unary. -/
theorem length_unary' (n : ℕ) : (unary n).length = n := List.length_replicate

/-- The size of a number in unary. -/
theorem size_unary' (n : ℕ) : size (unary n) = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [unary, List.replicate_succ, size_list, List.map_cons, List.sum_cons, size_unit] at ih ⊢
    omega

/-- After k rounds the pair is (2^{3k+x₀}, K_k). -/
theorem numbers_fold (x₀ k : ℕ) : (List.range k).foldl (fun acc _ => numbersStep acc) (unary (2 ^ x₀), unary (2 ^ x₀)) = (unary (2 ^ (3 * k + x₀)), unary (Levels.Gen.K x₀ k)) := by
  induction k with
  | zero => simp [Levels.Gen.K]
  | succ k ih =>
    rw [Stepped.foldl_range_succ, ih]
    have e : 8 * 2 ^ (3 * k + x₀) = 2 ^ (3 * (k + 1) + x₀) := by
      rw [show 3 * (k + 1) + x₀ = (3 * k + x₀) + 3 by ring, pow_add]
      ring
    simp only [numbersStep, length_unary', e, Levels.Gen.K]

/-- K_ℓ ≥ 1. -/
theorem K_pos (x₀ l : ℕ) : 1 ≤ Levels.Gen.K x₀ l := by
  induction l with
  | zero => exact Nat.one_le_two_pow
  | succ l ih => exact Nat.pow_pos (Nat.mul_pos (Nat.pow_pos (by norm_num)) ih)

/-- K_ℓ ≤ K_{ℓ+1}. -/
theorem K_le_succ (x₀ l : ℕ) : Levels.Gen.K x₀ l ≤ Levels.Gen.K x₀ (l + 1) := by
  have h1 : 1 ≤ 2 ^ (3 * l + x₀) := Nat.one_le_two_pow
  have h2 : Levels.Gen.K x₀ l ≤ 2 ^ (3 * l + x₀) * Levels.Gen.K x₀ l := Nat.le_mul_of_pos_left _ h1
  exact h2.trans (Nat.le_self_pow (by norm_num) _)

/-- K_ℓ grows with ℓ. -/
theorem K_mono (x₀ : ℕ) {k l : ℕ} (h : k ≤ l) : Levels.Gen.K x₀ k ≤ Levels.Gen.K x₀ l := monotone_nat_of_le_succ (K_le_succ x₀) h

/-- `NumbersRun`, with C = 18. -/
theorem numbersRun : NumbersRun := by
  refine ⟨18, fun x₀ l => ?_⟩
  have hp : ∀ k ≤ l, 2 ^ (3 * k + x₀) ≤ 2 ^ (3 * l + x₀) := fun k hk => Nat.pow_le_pow_right (by norm_num) (by omega)
  have r := Stepped.foldRange_runs (N := fun l : List Unit => l.length) (M := (Stepped.const () : Stepped (List Unit × ℕ) Unit)) (g := fun acc _ (_ : Unit) => numbersStep acc)
    (c₀ := fun _ => (unary (2 ^ x₀), unary (2 ^ x₀))) (a := unary l) (fun _ => 1) (fun _ => ()) (2 * 2 ^ (3 * l + x₀) + 2 * Levels.Gen.K x₀ l + 2) (3 * l + 3)
    (fun y hy => (Stepped.const_runs () (unary l, y)).mono le_rfl (by
      rw [length_unary'] at hy
      have := Nat.size_le.2 (Nat.lt_two_pow_self (n := y))
      simp only [size_prod, size_unary', size_nat, size_unit]
      omega))
    (fun k hk => by
      rw [length_unary'] at hk
      have h1 := hp k hk
      have h2 := K_mono x₀ hk
      rw [numbers_fold]
      simp only [size_prod, size_unary']
      omega)
  rw [numbers_fold] at r
  simp only [length_unary'] at r
  refine Stepped.Runs.mono r (by simp [Finset.sum_const, Nat.mul_comm]) ?_
  have h1 := Nat.size_le.2 (Nat.lt_two_pow_self (n := l))
  have h2 : l < 2 ^ (3 * l + x₀) := (Nat.lt_two_pow_self (n := l)).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h3 := K_pos x₀ l
  have h4 : 2 ^ (3 * l + x₀) ≤ Levels.Gen.g x₀ l := Nat.le_mul_of_pos_right _ h3
  have h5 : Levels.Gen.K x₀ l ≤ Levels.Gen.g x₀ l := Nat.le_mul_of_pos_left _ (by omega)
  simp only [size_unary', size_nat]
  omega

/-- One round is polynomial-time in the pair. -/
theorem numbersStep_polyT : PolyT numbersStep := by
  have u1 : Unary fun acc : List Unit × List Unit => acc.1.length := Unary.of_length (by fun_prop)
  have u2 : Unary fun acc : List Unit × List Unit => acc.2.length := Unary.of_length (by fun_prop)
  have h1 : Unary fun acc : List Unit × List Unit => 8 * acc.1.length := (Unary.const 8).mul u1
  have h2 : Unary fun acc : List Unit × List Unit => (acc.1.length * acc.2.length) * (acc.1.length * acc.2.length) := (u1.mul u2).mul (u1.mul u2)
  exact (PolyT.prodMk h1 h2).congr fun acc => by simp only [numbersStep, unary, sq]

/-- `NumbersPoly`. -/
theorem numbersPoly : NumbersPoly := fun x₀ => by
  have : IsPolyT (Stepped.const () : Stepped (List Unit × ℕ) Unit) := IsPolyT.const ()
  exact ⟨IsPolyT.foldRange (by fun_prop) (PolyT.comp numbersStep_polyT (by fun_prop)) (by fun_prop)⟩

end ExplicitCost
