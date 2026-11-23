/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Acc.ApproxMain
import Nc.End.PermThm

/-!
# Affine substitutions preserve approximation
-/

set_option linter.unusedSectionVars false

namespace Nc

open MvPolynomial

variable {F X Y : Type} [Field F]

theorem OrdGe.map_C (g : MvPolynomial Y F) : OrdGe 0 (MvPolynomial.map (HahnSeries.C : F →+* LaurentSeries F) g) := by
  intro d i hi
  rw [coeff_map, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by omega)]

theorem OrdGe.C_of_coeff {n : ℤ} {a : LaurentSeries F} (h : ∀ i < n, a.coeff i = 0) :
    OrdGe n (MvPolynomial.C a : MvPolynomial Y (LaurentSeries F)) := by
  classical
  intro d i hi
  rw [coeff_C]
  split_ifs
  · exact h i hi
  · rfl

theorem IsAffine.map_series {g : MvPolynomial Y F} (h : IsAffine g) :
    IsAffine (MvPolynomial.map (HahnSeries.C : F →+* LaurentSeries F) g) := by
  rcases h with ⟨b, rfl⟩ | ⟨i, a, b, rfl⟩
  · exact Or.inl ⟨_, map_C _ _⟩
  · exact Or.inr ⟨i, HahnSeries.C a, HahnSeries.C b, by simp⟩

/-- **Substitution.** An affine substitution with entries free of ε preserves
approximation, with five times as many gates. -/
theorem Approximates.substitute_affine {f : MvPolynomial X F} {s : ℕ} (h : Approximates f s)
    (Mat : X → MvPolynomial Y F) (hMat : ∀ q, IsAffine (Mat q)) : Approximates (aeval Mat f) (5 * s) := by
  obtain ⟨p, hp, hpf⟩ := h
  obtain ⟨φ, hφ⟩ : ∃ φ : F →+* LaurentSeries F, φ = HahnSeries.C := ⟨_, rfl⟩
  obtain ⟨Mat', hMat'⟩ : ∃ Mat', Mat' = fun q => MvPolynomial.map φ (Mat q) := ⟨_, rfl⟩
  refine ⟨aeval Mat' p, hp.aeval Mat' fun q => by rw [hMat', hφ]; exact (hMat q).map_series, ?_⟩
  have hr : OrdGe 1 (p - MvPolynomial.map φ f) := by
    intro d i hi
    rw [coeff_sub, coeff_map, HahnSeries.coeff_sub, hpf d i (by omega), hφ, HahnSeries.C_apply,
      HahnSeries.coeff_single]
    by_cases h : i = 0 <;> simp [h]
  have hmap : aeval Mat' (MvPolynomial.map φ f) = MvPolynomial.map φ (aeval Mat f) := by
    rw [hMat']
    exact (map_bind₁ φ Mat f).symm
  obtain ⟨r, hrdef⟩ : ∃ r, r = p - MvPolynomial.map φ f := ⟨_, rfl⟩
  rw [← hrdef] at hr
  have hs : OrdGe 1 (aeval Mat' r) := by
    rw [r.as_sum, map_sum]
    refine Finset.sum_induction _ (OrdGe 1) (fun u v hu hv => hu.add hv) (OrdGe.zero 1) fun d _ => ?_
    rw [aeval_monomial, algebraMap_eq]
    have e : (d.prod fun q k => Mat' q ^ k) = MvPolynomial.map φ (d.prod fun q k => Mat q ^ k) := by
      rw [map_finsuppProd, hMat']
      simp only [map_pow]
    rw [e, hφ]
    simpa using (OrdGe.C_of_coeff fun i hi => hr d i hi).mul (OrdGe.map_C (d.prod fun q k => Mat q ^ k))
  intro d i hi
  have e : aeval Mat' p = aeval Mat' r + MvPolynomial.map φ (aeval Mat f) := by
    rw [← hmap, ← map_add, hrdef, sub_add_cancel]
  rw [e, coeff_add, HahnSeries.coeff_add, hs d i (by omega), zero_add, coeff_map, hφ, HahnSeries.C_apply,
    HahnSeries.coeff_single]
  congr

end Nc
