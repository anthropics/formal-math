/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec2.Lemma6

/-!
# The monomials of Schönhage's identity

Two sentences of the paper about the monomials of `G + E`. No later file uses this one: the Lean
proof of `lemma_9` computes the values of `gamma` that it needs from the definition (`gamma_z0`,
`gamma_x_y_z`).

* Section 2.2, the first observation after Lemma 6: a monomial of `G` is a `p_ij q_ij z₀` or an
  `x_i y_j z_ij` (`monomials_G`), and a monomial of `E` has an outer output variable together with
  an inner left or right variable (`monomials_E`).
* Section 2.3.2: the `γ(s, t, z)` of equation (3) is the coefficient of the monomial `s t z` on the
  left-hand side of the identity and so, by Lemma 6, in `G + E` (`gamma_eq_coeff`).

Both rest on the expansion of a product of three linear forms, one in the left, one in the right and
one in the output variables, into the monomials `s t z` (`formL_mul_formR_mul_formO`). Distinct
triples give distinct monomials (`monomialSTZ_inj`), so the coefficient of `s t z` in such a product
is the product of the three coefficients (`coeff_monomialSTZ_forms`).
-/

@[expose] public section

open Finset MvPolynomial

namespace ThreeSumApsp

/-! ### Products of three linear forms -/

/-- The monomial `s t z` (Section 2.3.2), as an exponent vector. -/
noncomputable def monomialSTZ (s : LeftVar) (t : RightVar) (z : OutVar) : Var →₀ ℕ :=
  Finsupp.single (Sum.inl s) 1 + Finsupp.single (Sum.inr (Sum.inl t)) 1
    + Finsupp.single (Sum.inr (Sum.inr z)) 1

/-- The product of a left, a right and an output variable is the monomial `s t z`. -/
theorem polyL_mul_polyR_mul_polyO (s : LeftVar) (t : RightVar) (z : OutVar) :
    polyL s * polyR t * polyO z = monomial (monomialSTZ s t z) 1 := by
  simp [polyL, polyR, polyO, monomialSTZ, X, monomial_mul]

/-- The product of three linear forms, one in the left, one in the right and one in the output
variables, expanded into the monomials `s t z`. -/
theorem formL_mul_formR_mul_formO (f : LeftVar → ℤ) (g : RightVar → ℤ) (h : OutVar → ℤ) :
    formL f * formR g * formO h
      = ∑ s, ∑ t, ∑ z, monomial (monomialSTZ s t z) (f s * g t * h z) := by
  have hmono : ∀ s t z, monomial (monomialSTZ s t z) (f s * g t * h z)
      = C (f s) * polyL s * (C (g t) * polyR t) * (C (h z) * polyO z) := fun s t z => by
    rw [← mul_one (f s * g t * h z), ← C_mul_monomial, ← polyL_mul_polyR_mul_polyO, C_mul, C_mul]
    ring
  simp only [hmono, ← mul_sum, ← sum_mul, formL, formR, formO]

/-- Distinct triples of variables give distinct monomials `s t z`. -/
theorem monomialSTZ_inj {s s' : LeftVar} {t t' : RightVar} {z z' : OutVar} :
    monomialSTZ s' t' z' = monomialSTZ s t z ↔ s' = s ∧ t' = t ∧ z' = z := by
  refine ⟨fun h => ⟨?_, ?_, ?_⟩, by rintro ⟨rfl, rfl, rfl⟩; rfl⟩
  · simpa [monomialSTZ, Finsupp.single_apply] using DFunLike.congr_fun h (.inl s)
  · simpa [monomialSTZ, Finsupp.single_apply] using DFunLike.congr_fun h (.inr (.inl t))
  · simpa [monomialSTZ, Finsupp.single_apply] using DFunLike.congr_fun h (.inr (.inr z))

/-- The coefficient of the monomial `s t z` in a product of three linear forms, one in the left, one
in the right and one in the output variables, is the product of the three coefficients. -/
theorem coeff_monomialSTZ_forms (f : LeftVar → ℤ) (g : RightVar → ℤ) (h : OutVar → ℤ)
    (s : LeftVar) (t : RightVar) (z : OutVar) :
    coeff (monomialSTZ s t z) (formL f * formR g * formO h) = f s * g t * h z := by
  simp [formL_mul_formR_mul_formO, coeff_sum, coeff_monomial, monomialSTZ_inj, ite_and]

/-! ### The coefficients `γ` -/

/-- After equation (3): `γ(s, t, z)` is "the coefficient of the monomial stz on the
left-hand side of the identity." -/
theorem gamma_eq_coeff_sum (s : LeftVar) (t : RightVar) (z : OutVar) :
    gamma s t z
      = coeff (monomialSTZ s t z) (∑ lam, formL (phi lam) * formR (psi lam) * formO (chi lam)) := by
  simp only [coeff_sum, coeff_monomialSTZ_forms, chi_eq_ite, gamma, sum_filter]
  exact sum_congr rfl fun lam _ => by split_ifs <;> simp

/-- Section 2.3.2: "By Lemma 6, it is also the coefficient of stz in G + E". -/
theorem gamma_eq_coeff (s : LeftVar) (t : RightVar) (z : OutVar) :
    gamma s t z = coeff (monomialSTZ s t z) (G + E) := by
  rw [gamma_eq_coeff_sum, lemma_6]

/-! ### The monomials of `G` and of `E` -/

/-- A monomial of a sum is a monomial of one of the summands. -/
private theorem exists_mem_support_of_sum {ι : Type*} {f : ι → TriPoly} {I : Finset ι}
    {μ : Var →₀ ℕ} (hμ : μ ∈ (∑ i ∈ I, f i).support) : ∃ i, μ ∈ (f i).support :=
  (mem_biUnion.mp (support_sum hμ)).imp fun _ h => h.2

/-- Every monomial of a product `f g z` of a left form, a right form and an output variable is
`s t z` for a variable `s` of `f` and a variable `t` of `g`. -/
private theorem exists_of_mem_support_form_mul {f : LeftVar → ℤ} {g : RightVar → ℤ} {z : OutVar}
    {μ : Var →₀ ℕ} (hμ : μ ∈ (formL f * formR g * polyO z).support) :
    ∃ s t, f s ≠ 0 ∧ g t ≠ 0 ∧ μ = monomialSTZ s t z := by
  rw [← formO_single, formL_mul_formR_mul_formO] at hμ
  obtain ⟨s, -, hμ⟩ := mem_biUnion.mp (support_sum hμ)
  obtain ⟨t, -, hμ⟩ := mem_biUnion.mp (support_sum hμ)
  obtain ⟨z', -, hμ⟩ := mem_biUnion.mp (support_sum hμ)
  obtain rfl := mem_singleton.mp (support_monomial_subset hμ)
  have hcoeff : f s * g t * (Pi.single z 1 : OutVar → ℤ) z' ≠ 0 := by
    simpa [mem_support_iff] using hμ
  obtain rfl : z' = z := by
    by_contra hne
    exact hcoeff (by rw [Pi.single_eq_of_ne hne, mul_zero])
  exact ⟨s, t, left_ne_zero_of_mul (left_ne_zero_of_mul hcoeff),
    right_ne_zero_of_mul (left_ne_zero_of_mul hcoeff), rfl⟩

/-- Every variable of an entry of `p̂` is inner. -/
private theorem isInner_of_pHat_ne_zero {i j : Fin 3} {s : LeftVar} (h : pHat i j s ≠ 0) :
    s.IsInner := by
  cases s with
  | p a b => trivial
  | x a => exact absurd (by fin_cases i <;> fin_cases j <;> simp [pHat, pForm]) h

/-- Every variable of an entry of `q̂` is inner. -/
private theorem isInner_of_qHat_ne_zero {i j : Fin 3} {t : RightVar} (h : qHat i j t ≠ 0) :
    t.IsInner := by
  cases t with
  | q a b => trivial
  | y a => exact absurd (by fin_cases i <;> fin_cases j <;> simp [qHat, qForm]) h

/-- Section 2.2, first observation: "every monomial of G consists only of inner variables (p_ij q_ij
z₀) or only of outer variables (x_i y_j z_ij)." -/
theorem monomials_G (μ : Var →₀ ℕ) (hμ : μ ∈ G.support) :
    (∃ i j, μ = monomialSTZ (.p i j) (.q i j) .z0)
      ∨ (∃ i j, μ = monomialSTZ (.x i) (.y j) (.z i j)) := by
  simp only [G, sum_mul] at hμ
  rcases mem_union.mp (support_add hμ) with h | h
  all_goals
    obtain ⟨i, h⟩ := exists_mem_support_of_sum h
    obtain ⟨j, h⟩ := exists_mem_support_of_sum h
    rw [polyL_mul_polyR_mul_polyO] at h
    have hμ_eq := mem_singleton.mp (support_monomial_subset h)
  · exact .inr ⟨i, j, hμ_eq⟩
  · exact .inl ⟨i, j, hμ_eq⟩

/-- Section 2.2, first observation: "every monomial of E has an outer output variable together with
an inner left or right variable." -/
theorem monomials_E (μ : Var →₀ ℕ) (hμ : μ ∈ E.support) :
    ∃ s t i j, (s.IsInner ∨ t.IsInner) ∧ μ = monomialSTZ s t (.z i j) := by
  obtain ⟨i, -, h⟩ := mem_biUnion.mp (support_sum hμ)
  obtain ⟨j, h⟩ := exists_mem_support_of_sum h
  -- The three summands `x_i q̂_ij z_ij`, `p̂_ij y_j z_ij` and `p̂_ij q̂_ij z_ij`, in this order.
  rw [add_mul, add_mul, ← formL_single, ← formR_single] at h
  rcases mem_union.mp (support_add h) with h | h
  · rcases mem_union.mp (support_add h) with h | h
    · obtain ⟨s, t, -, ht, rfl⟩ := exists_of_mem_support_form_mul h
      exact ⟨s, t, i, j, .inr (isInner_of_qHat_ne_zero ht), rfl⟩
    · obtain ⟨s, t, hs, -, rfl⟩ := exists_of_mem_support_form_mul h
      exact ⟨s, t, i, j, .inl (isInner_of_pHat_ne_zero hs), rfl⟩
  · obtain ⟨s, t, hs, -, rfl⟩ := exists_of_mem_support_form_mul h
    exact ⟨s, t, i, j, .inl (isInner_of_pHat_ne_zero hs), rfl⟩

end ThreeSumApsp
