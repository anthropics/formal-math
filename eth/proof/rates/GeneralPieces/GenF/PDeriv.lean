/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.GenF.Taylor
public import Mathlib.RingTheory.MvPowerSeries.Derivative

/-! # The derivatives with respect to the variables x_i of the two exponentials

∂/∂x_i e^w = (∂w/∂x_i)·e^w (`pderiv_expW`). For 𝒪 = Σ_v x_v·O_v: ∂/∂x_i ∘ 𝒪 = 𝒪 ∘ ∂/∂x_i + O_i
(`pderiv_opX`), hence, if the O_v commute, ∂/∂x_i (e^𝒪 f) = e^𝒪 (∂f/∂x_i) + e^𝒪 (O_i f)
(`pderiv_expOp`, `pderiv_expD`). -/

@[expose] public section

namespace GeneralPieces.GenF

open Finset MvPowerSeries

variable {X A : Type} [CommRing A] [Algebra ℚ A]

theorem degree_add_single (α : X →₀ ℕ) (i : X) : (α + Finsupp.single i 1).degree = α.degree + 1 := by
  rw [map_add, Finsupp.degree_single]

theorem inv_factorial_succ_mul (n : ℕ) : (((n + 1).factorial : ℚ)⁻¹) * ((n + 1 : ℕ) : ℚ) = ((n.factorial : ℚ)⁻¹) := by
  have h1 : (n.factorial : ℚ) ≠ 0 := by positivity
  rw [Nat.factorial_succ]
  push_cast
  have h2 : ((n : ℚ) + 1) ≠ 0 := by positivity
  field_simp

/-- ∂/∂x_i Σ_{n ≤ N} wⁿ/n! = (∂w/∂x_i)·Σ_{n < N} wⁿ/n!. -/
theorem pderiv_expN (i : X) (N : ℕ) (w : MvPowerSeries X A) : pderiv A i (expN (N + 1) w) = pderiv A i w * expN N w := by
  unfold expN
  rw [sum_range_succ', map_add, map_sum, mul_sum]
  have h0 : pderiv A i (((Nat.factorial 0 : ℚ)⁻¹) • w ^ 0) = 0 := by rw [map_rat_smul, pow_zero, pderiv_one, smul_zero]
  rw [h0, add_zero]
  refine sum_congr rfl fun n _ => ?_
  rw [map_rat_smul, Derivation.leibniz_pow, Nat.add_sub_cancel, smul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_factorial_succ_mul,
    mul_smul_comm, mul_comm]

/-- ∂/∂x_i e^w = (∂w/∂x_i)·e^w. -/
theorem pderiv_expW (i : X) {w : MvPowerSeries X A} (hw : constantCoeff w = 0) : pderiv A i (expW w) = pderiv A i w * expW w := by
  ext α
  rw [coeff_pderiv, coeff_expW hw (N := α.degree + 1 + 1) (by rw [degree_add_single]; omega), ← coeff_pderiv, pderiv_expN]
  exact coeff_mul_congr (fun _ _ => rfl) fun β hβ => (coeff_expW hw (by omega)).symm

/-- ∂/∂x_i commutes with a linear map that is applied to every coefficient. -/
theorem pderiv_mapE (D : A →ₗ[ℚ] A) (i : X) (f : MvPowerSeries X A) : pderiv A i (mapE D f) = mapE D (pderiv A i f) := by
  ext α
  rw [coeff_pderiv, coeff_mapE, coeff_mapE, coeff_pderiv]
  have h : ∀ c : A, c * ((α i : A) + 1) = (α i + 1) • c := fun c => by rw [nsmul_eq_mul]; push_cast; ring
  rw [h, h, map_nsmul]

/-- ∂/∂x_i ∘ 𝒪 = 𝒪 ∘ ∂/∂x_i + O_i. -/
theorem pderiv_opX (O : X → A →ₗ[ℚ] A) (i : X) (f : MvPowerSeries X A) : pderiv A i (opX O f) = opX O (pderiv A i f) + mapE (O i) f := by
  classical
  ext α
  have hs1 : (α + Finsupp.single i 1).support ⊆ insert i α.support := by
    refine Finsupp.support_add.trans (union_subset (subset_insert _ _) ?_)
    exact Finsupp.support_single_subset.trans (singleton_subset_iff.2 (mem_insert_self _ _))
  have h : ∀ v, pderiv A i (MvPowerSeries.X v * mapE (O v) f) = MvPowerSeries.X v * mapE (O v) (pderiv A i f) + if v = i then mapE (O v) f else 0 := fun v => by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, pderiv_mapE]
    split_ifs with hv
    · rw [hv, pderiv_X_self, mul_one]
    · rw [pderiv_X_of_ne hv, mul_zero]
  rw [coeff_pderiv, coeff_opX_eq O f hs1, ← coeff_pderiv, map_sum]
  simp only [h]
  rw [sum_add_distrib, sum_ite_eq' _ i, if_pos (mem_insert_self _ _), map_add, map_add, ← coeff_opX_eq O _ (subset_insert _ _)]

/-- O_i, applied to every coefficient, commutes with 𝒪 if the O_v commute. -/
theorem mapE_opX {O : X → A →ₗ[ℚ] A} (hc : ∀ v v' a, O v (O v' a) = O v' (O v a)) (i : X) (f : MvPowerSeries X A) : mapE (O i) (opX O f) = opX O (mapE (O i) f) := by
  ext α
  rw [coeff_mapE, coeff_opX, coeff_opX, map_sum]
  exact sum_congr rfl fun v _ => by rw [hc, coeff_mapE]

theorem mapE_iterate {O : X → A →ₗ[ℚ] A} (hc : ∀ v v' a, O v (O v' a) = O v' (O v a)) (i : X) (n : ℕ) (f : MvPowerSeries X A) :
    mapE (O i) ((opX O)^[n] f) = (opX O)^[n] (mapE (O i) f) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', mapE_opX hc, ih]

/-- ∂/∂x_i 𝒪^{n+1} f = 𝒪^{n+1} ∂f/∂x_i + (n+1)·𝒪ⁿ O_i f. -/
theorem pderiv_iterate {O : X → A →ₗ[ℚ] A} (hc : ∀ v v' a, O v (O v' a) = O v' (O v a)) (i : X) (n : ℕ) (f : MvPowerSeries X A) :
    pderiv A i ((opX O)^[n + 1] f) = (opX O)^[n + 1] (pderiv A i f) + (n + 1) • (opX O)^[n] (mapE (O i) f) := by
  induction n with
  | zero =>
    rw [zero_add, one_smul]
    exact pderiv_opX O i f
  | succ n ih =>
    rw [Function.iterate_succ_apply', pderiv_opX, ih, map_add, map_nsmul, mapE_iterate hc, ← Function.iterate_succ_apply' (opX O), ← Function.iterate_succ_apply' (opX O),
      add_assoc, ← succ_nsmul]

theorem pderiv_opN {O : X → A →ₗ[ℚ] A} (hc : ∀ v v' a, O v (O v' a) = O v' (O v a)) (i : X) (N : ℕ) (f : MvPowerSeries X A) :
    pderiv A i (opN O (N + 1) f) = opN O (N + 1) (pderiv A i f) + opN O N (mapE (O i) f) := by
  unfold opN
  rw [sum_range_succ', sum_range_succ' (fun n => ((n.factorial : ℚ)⁻¹) • (opX O)^[n] (pderiv A i f)), map_add, map_sum, add_right_comm, ← sum_add_distrib]
  congr 1
  · refine sum_congr rfl fun n _ => ?_
    rw [map_rat_smul, pderiv_iterate hc, smul_add, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_factorial_succ_mul]
  · rw [map_rat_smul]
    rfl

/-- ∂/∂x_i (e^𝒪 f) = e^𝒪 (∂f/∂x_i) + e^𝒪 (O_i f), if the O_v commute. -/
theorem pderiv_expOp {O : X → A →ₗ[ℚ] A} (hc : ∀ v v' a, O v (O v' a) = O v' (O v a)) (i : X) (f : MvPowerSeries X A) :
    pderiv A i (expOp O f) = expOp O (pderiv A i f) + expOp O (mapE (O i) f) := by
  ext α
  rw [coeff_pderiv, coeff_expOp O f (N := α.degree + 1 + 1) (by rw [degree_add_single]; omega), ← coeff_pderiv, pderiv_opN hc, map_add, map_add,
    ← coeff_expOp O _ (by omega), ← coeff_expOp O _ (by omega)]

/-- The same for commuting derivations. -/
theorem pderiv_expD {D : X → Derivation ℚ A A} (hc : ∀ i j a, D i (D j a) = D j (D i a)) (i : X) (w : MvPowerSeries X A) :
    pderiv A i (expD D w) = expD D (pderiv A i w) + expD D (mapD (D i) w) :=
  pderiv_expOp (O := fun i => (D i).toLinearMap) hc i w

end GeneralPieces.GenF
