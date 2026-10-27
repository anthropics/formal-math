/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.CliqueReads
public import CountedRecursion.Brute
import Mathlib.Tactic

/-! # The solver at the level 0

Proof of Theorem A (b): for ℓ = 0, brute force sums 2^{λK₀(K₀−1)/2} ≤ 2^{e₀K₀²λ} terms, each at a
cost of at most (K₀(λ+B))^{C₅}. At ℓ = 0 the solver is brute force on K₀ = 2^{x₀} nodes, with its
queries written as queries of the solver and its answers read as integers. The count is
`brute_within`;
the constructions around it (`mapAsk`, `readAs`, `mapIn`, `ite`, `mapOut`) take no step and together
make the states larger by 1 (only `ite` adds to the size). The states have size at most 3X² + 13X +
22 ≤ X⁶ for X = K₀(λ + B) ≥ 2: C₅ = 6, one constant for all x₀ (`solverBase`). -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines Printed

/-- A list of n units has size 2n + 1. -/
theorem size_listUnit (l : List Unit) : size l = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [size_list, List.map_cons, List.sum_cons, size_unit, List.length_cons] at ih ⊢
    omega

/-- The tables read back from the answers of `W`, `readTables (answersOf K lam W)`, give the same
oracle `tables K lam` as `W` itself. -/
theorem tables_readTables (K lam : ℕ) (W : ℕ → List Bool → ℤ) : tables K lam (readTables (answersOf K lam W)) = tables K lam W := by
  funext q
  by_cases h : q.1 < K ∧ q.2.length = (K - 1) * lam
  · exact (if_pos h).trans ((congrArg some (readTables_setting W h.1 h.2)).trans (if_pos h).symm)
  · exact (if_neg h).trans (if_neg h).symm

/-- The bound on the states: 3X² + 13X + 22 ≤ X⁶ for X = K(λ + B). -/
theorem base_room_le {K lam B : ℕ} (hK : 1 ≤ K) (hl : 1 ≤ lam) (hB : 1 ≤ B) :
    3 * (2 * lam + 1 + (2 * B + 1)) + 3 * (K * (K - 1) / 2 * lam) + 2 * (B * K) + 2 * size K + K * (2 * lam + 2) + B + 13 + 1 ≤ (K * (lam + B)) ^ 6 := by
  obtain ⟨X, hX⟩ : ∃ X, X = K * (lam + B) := ⟨_, rfl⟩
  rw [← hX]
  have e1 : X = K * lam + K * B := by rw [hX, Nat.mul_add]
  have a1 : lam ≤ K * lam := Nat.le_mul_of_pos_left _ hK
  have a2 : B ≤ K * B := Nat.le_mul_of_pos_left _ hK
  have a3 : K ≤ K * B := Nat.le_mul_of_pos_right _ hB
  have a4 : K * (K - 1) / 2 * lam ≤ X * X := by
    have b1 : K * (K - 1) / 2 ≤ K * K := (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    calc K * (K - 1) / 2 * lam ≤ K * K * lam := Nat.mul_le_mul_right _ b1
      _ = K * (K * lam) := Nat.mul_assoc _ _ _
      _ ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
  have a5 : size K ≤ K + 1 := by
    have := Nat.size_le.2 (Nat.lt_two_pow_self (n := K))
    rw [size_nat]
    omega
  have a6 : K * (2 * lam + 2) = 2 * (K * lam) + 2 * K := by ring
  have a7 : B * K = K * B := Nat.mul_comm _ _
  have h2 : 2 ≤ X := by omega
  have a8 : 2 * X ≤ X * X := Nat.mul_le_mul_right _ h2
  have a9 : 16 * (X * X) ≤ X ^ 6 := by
    have : 2 ^ 4 ≤ X ^ 4 := Nat.pow_le_pow_left h2 4
    calc 16 * (X * X) = 2 ^ 4 * (X * X) := by norm_num
      _ ≤ X ^ 4 * (X * X) := Nat.mul_le_mul_right _ this
      _ = X ^ 6 := by ring
  rw [a6, a7]
  omega

/-- `SolverBase`, with C₅ = 6. -/
theorem solverBase : SolverBase := by
  refine ⟨6, fun D c x₀ Bound gl a f hF h0 tc tq => ?_⟩
  obtain ⟨hl, hB, W, hW, hf⟩ := hF
  have hK : Levels.Gen.K x₀ (cLev a) = 2 ^ x₀ := by rw [h0]; rfl
  rw [hK] at hW hf
  subst hf
  change (solver c x₀).Within _ _ a _ _ (Sum.inl (clique (Levels.Gen.K x₀ (cLev a)) (cLam a) fun w => readTables (answersOf (2 ^ x₀) (cLam a) W) w.val).value)
  rw [hK]
  -- brute force, for the tables read back from the oracle
  have b := brute_within (2 ^ x₀) a.1.2 (readTables (answersOf (2 ^ x₀) (cLam a) W)) (fun w hw z hz => by
    rw [readTables_setting (lam := cLam a) W hw (mem_words.1 hz)]
    exact hW w hw z hz) tq
  have eT : tables (2 ^ x₀) a.1.2.1.length (readTables (answersOf (2 ^ x₀) (cLam a) W)) = tables (2 ^ x₀) (cLam a) W := tables_readTables _ _ _
  rw [eT] at b
  -- the oracle of the solver, at a query to the tables, read as an integer
  have eO : (fun q : TableQuery => ((spec D c x₀ Bound).oracle gl a (answersOf (2 ^ x₀) (cLam a) W) (Sum.inr (Sum.inl q))).map asInt) = tables (2 ^ x₀) (cLam a) W := funext fun q => by
    change ((tables (2 ^ x₀) (cLam a) W q).map Sum.inl).map asInt = _
    cases tables (2 ^ x₀) (cLam a) W q <;> rfl
  have hE : (fun h : Head => h.1.isEmpty) a.1 = true := by
    have : a.1.1.length = 0 := h0
    change a.1.1.isEmpty = true
    rw [List.isEmpty_iff, ← List.length_eq_zero_iff]
    exact this
  have r : (solver c x₀).Within ((spec D c x₀ Bound).oracle gl a (answersOf (2 ^ x₀) (cLam a) W)) (solPrices c tc tq) a _ _ _ :=
    mapOut_within (mapIn_within (ite_within_true hE (mapIn_within (readAs_within (O := fun x => ((spec D c x₀ Bound).oracle gl a (answersOf (2 ^ x₀) (cLam a) W) x).map asInt) (fun _ => rfl)
      (mapAsk_within (h := fun q : TableQuery => (Sum.inr (Sum.inl q) : SolQuery)) (w := solPrices c tc tq) (by rw [eO]; exact b))))))
  refine r.mono le_rfl ?_
  have hs : size a.1.2 = 2 * cLam a + 1 + (2 * cB a + 1) := by
    rw [size_prod, size_listUnit, size_listUnit]
    rfl
  rw [hs]
  exact base_room_le Nat.one_le_two_pow hl hB

end ExplicitCost
