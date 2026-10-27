/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.GenF.Coeff

/-! # Coefficients of a power series as derivatives at 0

α! times the coefficient of x^α in F is the constant term of the derivative of F with respect to the
variables of x^α, one after the other (`borel_zero`). Here the coefficients of the products of
exponentials in the proof of
Lemma 9 (Appendix B) are identified this way, by their differential equations in the variables x_n,
x'_n; the paper instead expands the exponentials and compares coefficients. -/

@[expose] public section

namespace GeneralPieces.GenF

open Finset MvPowerSeries

variable {Y R : Type} [CommRing R]

/-- The exponent of the monomial ∏_{i ∈ L} x_i. -/
noncomputable def expo (L : List Y) : Y →₀ ℕ := (L.map fun i => Finsupp.single i 1).sum

theorem expo_nil : expo ([] : List Y) = 0 := rfl

theorem expo_cons (i : Y) (L : List Y) : expo (i :: L) = Finsupp.single i 1 + expo L := by simp [expo]

theorem expo_append (L L' : List Y) : expo (L ++ L') = expo L + expo L' := by simp [expo]

/-- The derivatives with respect to the variables of the list, the first of the list first. -/
noncomputable def pdL : List Y → MvPowerSeries Y R → MvPowerSeries Y R
  | [], F => F
  | i :: L, F => pdL L (pderiv R i F)

theorem pdL_nil (F : MvPowerSeries Y R) : pdL [] F = F := rfl

theorem pdL_cons (i : Y) (L : List Y) (F : MvPowerSeries Y R) : pdL (i :: L) F = pdL L (pderiv R i F) := rfl

theorem pdL_append (L L' : List Y) (F : MvPowerSeries Y R) : pdL (L ++ L') F = pdL L' (pdL L F) := by
  induction L generalizing F with
  | nil => rfl
  | cons i L ih => rw [List.cons_append, pdL_cons, pdL_cons, ih]

theorem pdL_add (L : List Y) (F G : MvPowerSeries Y R) : pdL L (F + G) = pdL L F + pdL L G := by
  induction L generalizing F G with
  | nil => rfl
  | cons i L ih => rw [pdL_cons, pdL_cons, pdL_cons, map_add, ih]

theorem pdL_zero (L : List Y) : pdL L (0 : MvPowerSeries Y R) = 0 := by
  induction L with
  | nil => rfl
  | cons i L ih => rw [pdL_cons, map_zero, ih]

theorem pdL_sum {ι : Type} (L : List Y) (s : Finset ι) (F : ι → MvPowerSeries Y R) : pdL L (∑ j ∈ s, F j) = ∑ j ∈ s, pdL L (F j) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty, sum_empty, pdL_zero]
  | insert j s hj ih => rw [sum_insert hj, sum_insert hj, pdL_add, ih]

theorem pderiv_C_mul (i : Y) (c : R) (F : MvPowerSeries Y R) : pderiv R i (C c * F) = C c * pderiv R i F := by
  rw [Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul]

theorem pdL_C_mul (L : List Y) (c : R) (F : MvPowerSeries Y R) : pdL L (C c * F) = C c * pdL L F := by
  induction L generalizing F with
  | nil => rfl
  | cons i L ih => rw [pdL_cons, pdL_cons, pderiv_C_mul, ih]

/-- Two derivatives commute. -/
theorem pderiv_pderiv (i j : Y) (F : MvPowerSeries Y R) : pderiv R i (pderiv R j F) = pderiv R j (pderiv R i F) := by
  by_cases h : i = j
  · rw [h]
  · ext α
    rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv, add_right_comm, Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm h),
      Finsupp.single_eq_of_ne h, add_zero, add_zero]
    ring

theorem pderiv_pdL (i : Y) (L : List Y) (F : MvPowerSeries Y R) : pderiv R i (pdL L F) = pdL L (pderiv R i F) := by
  induction L generalizing F with
  | nil => rfl
  | cons j L ih => rw [pdL_cons, pdL_cons, ih, pderiv_pderiv]

variable [Algebra ℚ R]

/-- (β + e_i)!·(the coefficient of x^β·x_i in F) = β!·(the coefficient of x^β in ∂F/∂x_i). -/
theorem borel_step (β : Y →₀ ℕ) (i : Y) (F : MvPowerSeries Y R) :
    fac (β + Finsupp.single i 1) • coeff (β + Finsupp.single i 1) F = fac β • coeff β (pderiv R i F) := by
  rw [coeff_pderiv, mul_natCast_succ, fac_add_single, smul_smul, mul_comm]

theorem borel (L : List Y) : ∀ (β : Y →₀ ℕ) (F : MvPowerSeries Y R), fac (β + expo L) • coeff (β + expo L) F = fac β • coeff β (pdL L F) := by
  induction L with
  | nil => intro β F; rw [expo_nil, add_zero, pdL_nil]
  | cons i L ih =>
    intro β F
    rw [expo_cons, add_left_comm, add_comm (Finsupp.single i 1), borel_step, ih, pdL_cons]

/-- α! times the coefficient of x^α = ∏_{i ∈ L} x_i in F is the constant term of the derivative of F
with respect to the variables of L. -/
theorem borel_zero (L : List Y) (F : MvPowerSeries Y R) : fac (expo L) • coeff (expo L) F = constantCoeff (pdL L F) := by
  have h := borel L 0 F
  rwa [zero_add, fac_zero, one_smul, coeff_zero_eq_constantCoeff_apply] at h

end GeneralPieces.GenF
