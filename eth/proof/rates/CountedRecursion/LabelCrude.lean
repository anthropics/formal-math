/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.CaseTwo
import ClauseBound.Gen.Rate
import Mathlib.Tactic

/-! # «Crude bounds give L ≤ N + 1»

Proof of Theorem A (b), the step from ℓ to ℓ + 1: crude bounds give L ≤ N + 1, B' ≤ N + g²B₁, g(P +
B₁) ≤ Ξ^{c+4} and K(L + B') ≤ Ξ^{c+5}. The statement `CrudeBounds` takes the first of the four as a
hypothesis. Here it is proved (`LabelCrude`) for the lemma's L = ⌈(U + 2ζgP)/K²⌉ and the total U of
either network of a pattern; `ProcedureCostFrom` takes it as a premise: the cost of an entry
(`EntryCostExplicit`) asks L ≤ 2gP for the L of a call, and L ≤ N + 1 = gP + 1 ≤ 2gP. For the bounds
on λ used along the recursion, the same inequality is part of `ChainLabel`, from which `ChainBase`
gets K(L + B') ≤ Ξ^{c+5}.
* `total_le`: U ≤ N, since there are at most g² ordered pairs of nodes and c_{a,a'} ≤ g²λ.
* `label_le_of`: L ≤ N + 1 whenever U ≤ N; `label_le_net`, `labelCrude : LabelCrude`: so for either
  network of a pattern. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-- U ≤ N = g⁴λ, for either network of a pattern. -/
theorem total_le {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) (g : ℕ) {lam : ℕ} (hlam : 1 ≤ lam) (y : ℕ) (tr : Bool) (W : ℕ → List Bool → ℤ) :
    (patternNet D c g tr lam y W).U ≤ g ^ 4 * lam := by
  unfold Net.U
  calc ∑ a, ∑ b ∈ univ.erase a, (patternNet D c g tr lam y W).c a b ≤ ∑ a : Fin (nParts g g tr), ∑ _b ∈ univ.erase a, g ^ 2 * lam :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => shared_le hS g hlam y tr W a b
    _ ≤ ∑ _a : Fin (nParts g g tr), g * (g ^ 2 * lam) := Finset.sum_le_sum fun a _ => by
        rw [Finset.sum_const, smul_eq_mul]
        refine Nat.mul_le_mul_right _ ((Finset.card_erase_le).trans (le_of_eq ?_))
        rw [Finset.card_univ, Fintype.card_fin, nParts_self]
    _ = g ^ 4 * lam := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin, nParts_self]
        ring

/-- «L ≤ N + 1», for every U ≤ N. -/
theorem label_le_of (x₀ l lam U : ℕ) (hx : 18 ≤ x₀) (hU : U ≤ Levels.Gen.g x₀ l ^ 4 * lam) :
    AppRunningTime.Lof (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) ((1 : ℝ) / (2 ^ (l + 5) : ℕ)) (Levels.Gen.g x₀ l ^ 3 * lam) U ≤ Levels.Gen.g x₀ l ^ 4 * lam + 1 := by
  have hK : (2 : ℝ) ≤ Levels.Gen.K x₀ l := by
    have := ClauseBound.Gen.Rate.big_le_K hx l
    exact_mod_cast (by omega : 2 ≤ Levels.Gen.K x₀ l)
  have hK2 : (2 : ℝ) ≤ (Levels.Gen.K x₀ l : ℝ) ^ 2 := by nlinarith
  have hz : Levels.Gen.zeta l ≤ 1 / 2 := by
    unfold Levels.Gen.zeta
    have h2 : (2 : ℝ) ≤ 2 ^ (l + 5) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one _).symm
        _ ≤ 2 ^ (l + 5) := pow_le_pow_right₀ (by norm_num) (by omega)
    exact one_div_le_one_div_of_le (by norm_num) h2
  have hUr : (U : ℝ) ≤ (Levels.Gen.g x₀ l : ℝ) ^ 4 * lam := by exact_mod_cast hU
  have hN : (0 : ℝ) ≤ (Levels.Gen.g x₀ l : ℝ) ^ 4 * lam := by positivity
  have h1 := label_first x₀ l lam U
  have h2 : 2 * Levels.Gen.zeta l * ((Levels.Gen.g x₀ l : ℝ) ^ 4 * lam) ≤ (Levels.Gen.g x₀ l : ℝ) ^ 4 * lam := by nlinarith
  have h3 : (Levels.Gen.K x₀ l : ℝ) ^ 2 * AppRunningTime.Lof (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) ((1 : ℝ) / (2 ^ (l + 5) : ℕ)) (Levels.Gen.g x₀ l ^ 3 * lam) U ≤
      (Levels.Gen.K x₀ l : ℝ) ^ 2 * ((Levels.Gen.g x₀ l : ℝ) ^ 4 * lam + 1) := by nlinarith
  have h4 := le_of_mul_le_mul_left h3 (by linarith)
  exact_mod_cast h4

/-- **«Crude bounds give L ≤ N + 1»**, for the lemma's L and either network of a pattern. -/
theorem label_le_net {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) (l : ℕ) {lam : ℕ} (hlam : 1 ≤ lam) (y : ℕ) (tr : Bool) (W : ℕ → List Bool → ℤ) :
    AppRunningTime.Lof (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) ((1 : ℝ) / (2 ^ (l + 5) : ℕ)) (Levels.Gen.g x₀ l ^ 3 * lam) (patternNet D c (Levels.Gen.g x₀ l) tr lam y W).U ≤ Levels.Gen.g x₀ l ^ 4 * lam + 1 :=
  label_le_of x₀ l lam _ hS.x₀_ge (total_le hS _ hlam y tr W)

/-- `label_le_net`, in the form of the statement `LabelCrude`. -/
theorem labelCrude : LabelCrude := fun _ _ _ _ hS l _ y tr W hlam => label_le_net hS l hlam y tr W

end ExplicitCost
