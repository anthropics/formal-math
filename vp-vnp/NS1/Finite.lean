/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# A field that is finitely generated as a ring is finite
-/

namespace NS1

theorem isJacobsonRing_int : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases h : P = ⊥
  · subst h
    rw [eq_bot_iff]
    intro x hx
    have h1 := Ideal.mem_jacobson_bot.1 hx x
    rcases Int.isUnit_iff.1 h1 with h2 | h2
    · have : x * x = 0 := by omega
      exact mul_self_eq_zero.1 this
    · nlinarith [mul_self_nonneg x]
  · have : P.IsMaximal := hP.isMaximal h
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem finite_of_finiteType_int (E : Type) [Field E] (h : (Int.castRingHom E).FiniteType) : Finite E := by
  have := isJacobsonRing_int
  have : Algebra.FiniteType ℤ E := by
    rw [← RingHom.finiteType_algebraMap, algebraMap_int_eq]
    exact h
  have hfin : Module.Finite ℤ E := finite_of_finite_type_of_isJacobsonRing ℤ E
  obtain ⟨p, hp⟩ := CharP.exists E
  rcases CharP.char_is_prime_or_zero E p with hprime | h0
  · have : Fact p.Prime := ⟨hprime⟩
    let _ := ZMod.algebra E p
    have : Module.Finite (ZMod p) E := Module.Finite.of_restrictScalars_finite ℤ (ZMod p) E
    exact Module.finite_of_finite (ZMod p)
  · exfalso
    subst h0
    have : CharZero E := CharP.charP_to_charZero E
    have hinj : Function.Injective (algebraMap ℤ E) := by
      rw [algebraMap_int_eq]
      exact Int.cast_injective
    have hint : Algebra.IsIntegral ℤ E := inferInstance
    exact Int.not_isField (isField_of_isIntegral_of_isField hinj (Field.toIsField E))

end NS1
