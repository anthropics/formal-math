/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Rate.Defs
import Nc.Final.CClasses
import Nc.Rate.Truncate

/-!
# Substitution into approximate circuits
-/

namespace Nc

open Finset MvPolynomial

variable {F X Y : Type*} [Field F]

/-- An affine substitution keeps approximation; the number of gates grows by a factor
at most 5. -/
theorem Approximates.aeval {f : MvPolynomial X F} {s : ℕ} (h : Approximates f s) (M : X → MvPolynomial Y F)
    (hM : ∀ q, IsAffine (M q)) : Approximates (MvPolynomial.aeval M f) (5 * s) := by
  obtain ⟨p, hp, hpf⟩ := h
  refine ⟨MvPolynomial.aeval (fun q => MvPolynomial.map (HahnSeries.C : F →+* LaurentSeries F) (M q)) p,
    hp.aeval _ fun q => ?_, fun d i hi => ?_⟩
  · rcases hM q with ⟨b, hb⟩ | ⟨j, a, b, hb⟩
    · exact Or.inl ⟨HahnSeries.C b, by rw [hb, map_C]⟩
    · exact Or.inr ⟨j, HahnSeries.C a, HahnSeries.C b, by rw [hb, map_add, map_mul, map_C, map_C, map_X]⟩
  · classical
    have hsub : f.support ⊆ p.support := fun b hb => by
      rw [mem_support_iff] at hb ⊢
      intro h0
      have h1 := hpf b 0 le_rfl
      rw [h0, if_pos rfl] at h1
      exact hb (h1.symm.trans (by simp))
    have e1 : coeff d (MvPolynomial.aeval (fun q => MvPolynomial.map (HahnSeries.C : F →+* LaurentSeries F) (M q)) p) =
        ∑ b ∈ p.support, coeff b p * HahnSeries.C (coeff d (MvPolynomial.aeval M (monomial b (1 : F)))) := by
      conv_lhs => rw [p.as_sum, map_sum, coeff_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← mul_one (coeff b p), ← C_mul_monomial, map_mul, aeval_C, MvPolynomial.algebraMap_eq, coeff_C_mul, mul_one]
      congr 1
      rw [← coeff_map, aeval_monomial, aeval_monomial, map_one, map_one, one_mul, one_mul, map_finsuppProd]
      simp only [map_pow]
    have e2 : coeff d (MvPolynomial.aeval M f) =
        ∑ b ∈ p.support, coeff b f * coeff d (MvPolynomial.aeval M (monomial b (1 : F))) := by
      conv_lhs => rw [f.as_sum, map_sum, coeff_sum]
      rw [Finset.sum_subset hsub (fun b _ hb => by rw [notMem_support_iff.1 hb, monomial_zero, map_zero, coeff_zero])]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← mul_one (coeff b f), ← C_mul_monomial, map_mul, aeval_C, MvPolynomial.algebraMap_eq, coeff_C_mul, mul_one]
    have e3 : ∀ (a : LaurentSeries F) (r : F), (a * HahnSeries.C r).coeff i = a.coeff i * r := by
      intro a r
      rw [mul_comm, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, mul_comm]
    rw [e1, HahnSeries.coeff_sum]
    simp only [e3, hpf _ i hi]
    by_cases h0 : i = 0
    · simp only [if_pos h0, e2]
    · simp [h0]

end Nc
