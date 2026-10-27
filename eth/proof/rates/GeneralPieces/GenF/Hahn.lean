/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Module.Rat

/-! # A derivation applied to every coefficient of a Hahn series

"e^{A⁻} is the ring homomorphism …, applied to the coefficient of each power of ω₂" (Appendix B): a
derivation d of a commutative ℚ-algebra A, applied to every coefficient of a series in the powers of
one more
variable with coefficients in A, is a derivation of the ring of these series (`hder`); and commuting
derivations give commuting derivations (`hder_comm`). -/

@[expose] public section

namespace GeneralPieces.GenF

open Finset HahnSeries

variable {A : Type} [CommRing A] [Algebra ℚ A]

/-- d applied to every coefficient, as a linear map. -/
noncomputable def hmap (d : Derivation ℚ A A) : HahnSeries ℤ A →ₗ[ℚ] HahnSeries ℤ A where
  toFun f := f.map d
  map_add' f g := by
    ext y
    simp
  map_smul' q f := by
    ext y
    simp

theorem coeff_hmap (d : Derivation ℚ A A) (f : HahnSeries ℤ A) (y : ℤ) : (hmap d f).coeff y = d (f.coeff y) := rfl

theorem support_hmap (d : Derivation ℚ A A) (f : HahnSeries ℤ A) : (hmap d f).support ⊆ f.support := fun y hy => by
  rw [mem_support] at hy ⊢
  intro h
  exact hy (by rw [coeff_hmap, h, map_zero])

/-- d applied to every coefficient, as a derivation. -/
noncomputable def hder (d : Derivation ℚ A A) : Derivation ℚ (HahnSeries ℤ A) (HahnSeries ℤ A) :=
  Derivation.mk' (hmap d) fun f g => by
    ext y
    rw [coeff_hmap, smul_eq_mul, smul_eq_mul, coeff_add, mul_comm g, coeff_mul, coeff_mul_right' g.isPWO_support (support_hmap d g),
      coeff_mul_left' f.isPWO_support (support_hmap d f), map_sum, ← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, coeff_hmap, coeff_hmap, mul_comm (g.coeff p.2)]

theorem coeff_hder (d : Derivation ℚ A A) (f : HahnSeries ℤ A) (y : ℤ) : (hder d f).coeff y = d (f.coeff y) := rfl

/-- Commuting derivations give commuting derivations. -/
theorem hder_comm {d d' : Derivation ℚ A A} (h : ∀ a, d (d' a) = d' (d a)) (f : HahnSeries ℤ A) : hder d (hder d' f) = hder d' (hder d f) := by
  ext y
  rw [coeff_hder, coeff_hder, coeff_hder, coeff_hder, h]

/-- On a series with one term. -/
theorem hder_single (d : Derivation ℚ A A) (y : ℤ) (a : A) : hder d (single y a) = single y (d a) := by
  ext z
  rw [coeff_hder]
  by_cases h : z = y
  · rw [h, coeff_single_same, coeff_single_same]
  · rw [coeff_single_of_ne h, coeff_single_of_ne h, map_zero]

/-- On a constant series. -/
theorem hder_C (d : Derivation ℚ A A) (a : A) : hder d (HahnSeries.C a) = HahnSeries.C (d a) := hder_single d 0 a

end GeneralPieces.GenF
