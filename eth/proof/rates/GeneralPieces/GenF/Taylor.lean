/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.GenF.Exp
public import Mathlib.Algebra.MvPolynomial.Derivation

/-! # The exponential of Σ_v x_v·O_v for operators O_v, and Taylor's formula

Let A be a commutative ℚ-algebra, X a set of variables and O_v (v ∈ X) ℚ-linear maps A → A. The
operator 𝒪 = Σ_v x_v·O_v acts on the power series in the variables X over A (`opX`): O_v is applied
to
every coefficient, and the result is multiplied by x_v. It raises the degree in the x_v by one, so
e^𝒪 = Σ_n 𝒪ⁿ/n! (`expOp`) is a finite sum in every coefficient. If the O_v are derivations, 𝒪 is a
derivation (`opX_mul`), so e^𝒪 is a ring homomorphism by Leibniz's rule (`expOp_mul`, `expOpHom`),
which commutes with the exponential of power series (`expOp_expW`). Taylor's formula, of the kind
used in the proof
of Lemma 9 (Appendix B): if 𝒪(𝒪 f) = 0, then e^𝒪 f = f + 𝒪 f (`expOp_of_sq_zero`); for e^{Σ x_i D_i}
with derivations D_i this is `expD_of_sq_zero`. -/

@[expose] public section

namespace GeneralPieces.GenF

open Finset MvPowerSeries

variable {X A : Type} [CommRing A] [Algebra ℚ A]

/-! ### Series without monomials of low degree -/

/-- f has no monomials of degree less than d. -/
def Low (d : ℕ) (f : MvPowerSeries X A) : Prop := ∀ β : X →₀ ℕ, β.degree < d → coeff β f = 0

omit [Algebra ℚ A] in
theorem Low.mul {i j : ℕ} {f g : MvPowerSeries X A} (hf : Low i f) (hg : Low j g) : Low (i + j) (f * g) := fun α h => by
  classical
  rw [coeff_mul]
  refine sum_eq_zero fun p hp => ?_
  have h' := congrArg Finsupp.degree (mem_antidiagonal.1 hp)
  rw [map_add] at h'
  by_cases h1 : p.1.degree < i
  · rw [hf p.1 h1, zero_mul]
  · rw [hg p.2 (by omega), mul_zero]

theorem sub_single_add {β : X →₀ ℕ} {v : X} (hv : v ∈ β.support) : β - Finsupp.single v 1 + Finsupp.single v 1 = β :=
  tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hv)))

theorem degree_sub_single {β : X →₀ ℕ} {v : X} (hv : v ∈ β.support) : (β - Finsupp.single v 1).degree + 1 = β.degree := by
  have h := congrArg Finsupp.degree (sub_single_add hv)
  rwa [map_add, Finsupp.degree_single] at h

/-! ### The operator 𝒪 = Σ_v x_v·O_v -/

/-- A linear map applied to every coefficient. -/
noncomputable def mapE (D : A →ₗ[ℚ] A) : MvPowerSeries X A →ₗ[ℚ] MvPowerSeries X A where
  toFun f := fun α => D (coeff α f)
  map_add' f g := by
    ext α
    show D (coeff α (f + g)) = D (coeff α f) + D (coeff α g)
    rw [map_add, map_add]
  map_smul' q f := by
    ext α
    show D (coeff α (q • f)) = q • D (coeff α f)
    rw [coeff_rat_smul, map_smul]

theorem coeff_mapE (D : A →ₗ[ℚ] A) (f : MvPowerSeries X A) (α : X →₀ ℕ) : coeff α (mapE D f) = D (coeff α f) := rfl

/-- 𝒪 = Σ_v x_v·O_v: the coefficient of α in 𝒪 f is Σ_v O_v(the coefficient of α − e_v in f), over
the variables v that occur in α. -/
noncomputable def opX (O : X → A →ₗ[ℚ] A) : MvPowerSeries X A →ₗ[ℚ] MvPowerSeries X A where
  toFun f := fun α => ∑ v ∈ α.support, O v (coeff (α - Finsupp.single v 1) f)
  map_add' f g := by
    ext α
    show ∑ v ∈ α.support, O v (coeff (α - Finsupp.single v 1) (f + g)) =
      ∑ v ∈ α.support, O v (coeff (α - Finsupp.single v 1) f) + ∑ v ∈ α.support, O v (coeff (α - Finsupp.single v 1) g)
    rw [← sum_add_distrib]
    exact sum_congr rfl fun v _ => by rw [map_add, map_add]
  map_smul' q f := by
    ext α
    show ∑ v ∈ α.support, O v (coeff (α - Finsupp.single v 1) (q • f)) = q • ∑ v ∈ α.support, O v (coeff (α - Finsupp.single v 1) f)
    rw [smul_sum]
    exact sum_congr rfl fun v _ => by rw [coeff_rat_smul, map_smul]

theorem coeff_opX (O : X → A →ₗ[ℚ] A) (f : MvPowerSeries X A) (α : X →₀ ℕ) :
    coeff α (opX O f) = ∑ v ∈ α.support, O v (coeff (α - Finsupp.single v 1) f) := rfl

/-- 𝒪 raises the degree by one. -/
theorem Low.opX {d : ℕ} {f : MvPowerSeries X A} (hf : Low d f) (O : X → A →ₗ[ℚ] A) : Low (d + 1) (GenF.opX O f) := fun β h => by
  rw [coeff_opX]
  refine sum_eq_zero fun v hv => ?_
  have := degree_sub_single hv
  rw [hf _ (by omega), map_zero]

theorem Low.iterate {d : ℕ} {f : MvPowerSeries X A} (hf : Low d f) (O : X → A →ₗ[ℚ] A) (n : ℕ) : Low (d + n) ((GenF.opX O)^[n] f) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.opX O

omit [Algebra ℚ A] in
theorem low_zero (f : MvPowerSeries X A) : Low 0 f := fun _ h => absurd h (Nat.not_lt_zero _)

/-- 𝒪ⁿ f has no monomials of degree less than n. -/
theorem coeff_iterate_eq_zero (O : X → A →ₗ[ℚ] A) (f : MvPowerSeries X A) {α : X →₀ ℕ} {n : ℕ} (h : α.degree < n) : coeff α ((opX O)^[n] f) = 0 :=
  (low_zero f).iterate O n α (by omega)

/-- In the coefficient of α, 𝒪 is the finite sum Σ_{v ∈ s} x_v·O_v, for every finite set s that
contains the variables of α. -/
theorem coeff_opX_eq (O : X → A →ₗ[ℚ] A) (f : MvPowerSeries X A) {α : X →₀ ℕ} {s : Finset X} (hs : α.support ⊆ s) :
    coeff α (opX O f) = coeff α (∑ v ∈ s, MvPowerSeries.X v * mapE (O v) f) := by
  classical
  have h : ∀ v, coeff α (MvPowerSeries.X v * mapE (O v) f) = if v ∈ α.support then O v (coeff (α - Finsupp.single v 1) f) else 0 := fun v => by
    rw [X_def, coeff_monomial_mul, one_mul, coeff_mapE]
    refine if_congr ?_ rfl rfl
    rw [Finsupp.single_le_iff, Finsupp.mem_support_iff, Nat.one_le_iff_ne_zero]
  rw [coeff_opX, map_sum]
  simp only [h]
  rw [sum_ite_mem, inter_eq_right.2 hs]

/-! ### Derivations -/

/-- The product rule. -/
def IsDer {B : Type} [CommRing B] [Algebra ℚ B] (D : B →ₗ[ℚ] B) : Prop := ∀ a b, D (a * b) = a * D b + D a * b

/-- A derivation applied to every coefficient is a derivation. -/
theorem mapE_mul {D : A →ₗ[ℚ] A} (hD : IsDer D) : IsDer (mapE (X := X) D) := fun f g => by
  classical
  ext α
  rw [coeff_mapE, map_add, coeff_mul, coeff_mul, coeff_mul, map_sum, ← sum_add_distrib]
  exact sum_congr rfl fun p _ => by rw [hD, coeff_mapE, coeff_mapE]

/-- 𝒪 is a derivation if the O_v are. -/
theorem opX_mul {O : X → A →ₗ[ℚ] A} (hO : ∀ v, IsDer (O v)) : IsDer (opX O) := fun f g => by
  classical
  ext α
  have h1 : ∑ v ∈ α.support, MvPowerSeries.X v * mapE (O v) (f * g) =
      f * ∑ v ∈ α.support, MvPowerSeries.X v * mapE (O v) g + (∑ v ∈ α.support, MvPowerSeries.X v * mapE (O v) f) * g := by
    rw [mul_sum, sum_mul, ← sum_add_distrib]
    exact sum_congr rfl fun v _ => by rw [mapE_mul (hO v)]; ring
  have hsub : ∀ p ∈ antidiagonal α, p.1.support ⊆ α.support ∧ p.2.support ⊆ α.support := fun p hp => by
    have h := mem_antidiagonal.1 hp
    exact ⟨Finsupp.support_mono (h ▸ le_self_add), Finsupp.support_mono (h ▸ le_add_self)⟩
  rw [coeff_opX_eq O (f * g) (Subset.refl _), h1, map_add, map_add, coeff_mul, coeff_mul, coeff_mul, coeff_mul]
  congr 1
  · exact sum_congr rfl fun p hp => by rw [coeff_opX_eq O g (hsub p hp).2]
  · exact sum_congr rfl fun p hp => by rw [coeff_opX_eq O f (hsub p hp).1]

/-- Leibniz's rule for the n-th power of a derivation. -/
theorem iterate_mul {B : Type} [CommRing B] [Algebra ℚ B] {D : B →ₗ[ℚ] B} (hD : IsDer D) (n : ℕ) (a b : B) :
    D^[n] (a * b) = ∑ p ∈ antidiagonal n, n.choose p.1 • (D^[p.1] a * D^[p.2] b) := by
  have hD' : ∀ a b, D (a * b) = a * D b + D a * b := hD
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul (M := B) (fun i j => D^[i] a * D^[j] b) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul, hD', smul_add, sum_add_distrib, add_right_inj]
    refine sum_congr rfl fun ⟨i, j⟩ hij => ?_
    rw [n.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm]

/-- The same, divided by n!. -/
theorem iterate_mul_div {B : Type} [CommRing B] [Algebra ℚ B] {D : B →ₗ[ℚ] B} (hD : IsDer D) (n : ℕ) (a b : B) :
    ((n.factorial : ℚ)⁻¹) • D^[n] (a * b) = ∑ p ∈ antidiagonal n, ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) • (D^[p.1] a * D^[p.2] b) := by
  rw [iterate_mul hD, smul_sum]
  refine sum_congr rfl fun p hp => ?_
  have hn := mem_antidiagonal.1 hp
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  have h := Nat.add_choose_mul_factorial_mul_factorial p.1 p.2
  rw [hn, ← Nat.choose_symm_of_eq_add hn.symm] at h
  have h' : ((n.choose p.1 : ℕ) : ℚ) * p.1.factorial * p.2.factorial = n.factorial := by exact_mod_cast h
  have h1 : (p.1.factorial : ℚ) ≠ 0 := by positivity
  have h2 : (p.2.factorial : ℚ) ≠ 0 := by positivity
  have h3 : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  linarith

/-! ### The exponential e^𝒪 -/

/-- Σ_{n < N} 𝒪ⁿ f/n!. -/
noncomputable def opN (O : X → A →ₗ[ℚ] A) (N : ℕ) (f : MvPowerSeries X A) : MvPowerSeries X A := ∑ n ∈ range N, ((n.factorial : ℚ)⁻¹) • (opX O)^[n] f

/-- e^𝒪 f = Σ_n 𝒪ⁿ f/n!: the coefficient of a monomial of degree d is taken from the sum over n ≤ d. -/
noncomputable def expOp (O : X → A →ₗ[ℚ] A) (f : MvPowerSeries X A) : MvPowerSeries X A := fun α => coeff α (opN O (α.degree + 1) f)

theorem coeff_expOp_def (O : X → A →ₗ[ℚ] A) (f : MvPowerSeries X A) (α : X →₀ ℕ) : coeff α (expOp O f) = coeff α (opN O (α.degree + 1) f) := rfl

/-- More terms of the sum do not change the coefficient. -/
theorem coeff_expOp (O : X → A →ₗ[ℚ] A) (f : MvPowerSeries X A) {α : X →₀ ℕ} {N : ℕ} (h : α.degree < N) : coeff α (expOp O f) = coeff α (opN O N f) := by
  rw [coeff_expOp_def]
  unfold opN
  rw [map_sum, map_sum]
  refine sum_subset (range_subset_range.2 (by omega)) fun n _ hn => ?_
  rw [coeff_rat_smul, coeff_iterate_eq_zero O f (by simpa using hn), smul_zero]

theorem iterate_add (O : X → A →ₗ[ℚ] A) (n : ℕ) (f g : MvPowerSeries X A) : (opX O)^[n] (f + g) = (opX O)^[n] f + (opX O)^[n] g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_add]

theorem iterate_smul (O : X → A →ₗ[ℚ] A) (n : ℕ) (q : ℚ) (f : MvPowerSeries X A) : (opX O)^[n] (q • f) = q • (opX O)^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_smul]

theorem opN_add (O : X → A →ₗ[ℚ] A) (N : ℕ) (f g : MvPowerSeries X A) : opN O N (f + g) = opN O N f + opN O N g := by
  unfold opN
  rw [← sum_add_distrib]
  exact sum_congr rfl fun n _ => by rw [iterate_add, smul_add]

theorem expOp_add (O : X → A →ₗ[ℚ] A) (f g : MvPowerSeries X A) : expOp O (f + g) = expOp O f + expOp O g := by
  ext α
  rw [map_add, coeff_expOp_def, coeff_expOp_def, coeff_expOp_def, opN_add, map_add]

theorem expOp_smul (O : X → A →ₗ[ℚ] A) (q : ℚ) (f : MvPowerSeries X A) : expOp O (q • f) = q • expOp O f := by
  ext α
  rw [coeff_rat_smul, coeff_expOp_def, coeff_expOp_def]
  unfold opN
  rw [← coeff_rat_smul, smul_sum]
  congr 1
  exact sum_congr rfl fun n _ => by rw [iterate_smul, smul_comm]

theorem expOp_zero (O : X → A →ₗ[ℚ] A) : expOp O 0 = 0 := by
  have := expOp_smul O 0 0
  simpa using this

/-- e^𝒪 is multiplicative if the O_v are derivations. -/
theorem expOp_mul {O : X → A →ₗ[ℚ] A} (hO : ∀ v, IsDer (O v)) (f g : MvPowerSeries X A) : expOp O (f * g) = expOp O f * expOp O g := by
  ext α
  rw [coeff_mul_congr (f' := opN O (α.degree + 1) f) (g' := opN O (α.degree + 1) g) (fun β hβ => coeff_expOp O f (by omega)) fun β hβ => coeff_expOp O g (by omega),
    coeff_expOp_def]
  unfold opN
  rw [sum_mul_sum, map_sum, map_sum]
  simp only [iterate_mul_div (opX_mul hO), map_sum, smul_mul_smul_comm]
  refine sum_triangle (α.degree + 1) (fun i j => coeff α (((i.factorial : ℚ)⁻¹ * (j.factorial : ℚ)⁻¹) • ((opX O)^[i] f * (opX O)^[j] g))) fun i j hij => ?_
  have h := ((low_zero f).iterate O i).mul ((low_zero g).iterate O j) α (by omega)
  rw [coeff_rat_smul, h, smul_zero]

/-- If 𝒪(𝒪 f) = 0, then e^𝒪 f = f + 𝒪 f. -/
theorem expOp_of_sq_zero (O : X → A →ₗ[ℚ] A) {f : MvPowerSeries X A} (h : opX O (opX O f) = 0) : expOp O f = f + opX O f := by
  ext α
  rw [coeff_expOp O f (N := α.degree + 2) (by omega)]
  unfold opN
  have hz : ∀ n, (opX O)^[n + 2] f = 0 := fun n => by
    induction n with
    | zero => exact h
    | succ n ih => rw [Function.iterate_succ_apply', ih, map_zero]
  rw [sum_range_succ', sum_range_succ', sum_eq_zero fun n _ => by rw [hz, smul_zero]]
  simp [add_comm]

/-- If 𝒪 f = 0, then e^𝒪 f = f. -/
theorem expOp_of_zero (O : X → A →ₗ[ℚ] A) {f : MvPowerSeries X A} (h : opX O f = 0) : expOp O f = f := by
  rw [expOp_of_sq_zero O (by rw [h, map_zero]), h, add_zero]

theorem IsDer.one {B : Type} [CommRing B] [Algebra ℚ B] {D : B →ₗ[ℚ] B} (hD : IsDer D) : D 1 = 0 := by
  have h := hD 1 1
  rw [mul_one, one_mul, mul_one] at h
  exact left_eq_add.1 h

theorem expOp_one {O : X → A →ₗ[ℚ] A} (hO : ∀ v, IsDer (O v)) : expOp O 1 = 1 := expOp_of_zero O (opX_mul hO).one

/-- e^𝒪 as a ring homomorphism. -/
noncomputable def expOpHom (O : X → A →ₗ[ℚ] A) (hO : ∀ v, IsDer (O v)) : MvPowerSeries X A →+* MvPowerSeries X A where
  toFun := expOp O
  map_one' := expOp_one hO
  map_mul' := expOp_mul hO
  map_zero' := expOp_zero O
  map_add' := expOp_add O

/-- The coefficient of α in e^𝒪 f depends only on the coefficients of f at the monomials of degree
at most that of α. -/
theorem coeff_expOp_congr (O : X → A →ₗ[ℚ] A) (α : X →₀ ℕ) (f g : MvPowerSeries X A) (h : ∀ β : X →₀ ℕ, β.degree ≤ α.degree → coeff β f = coeff β g) :
    coeff α (expOp O f) = coeff α (expOp O g) := by
  have hl : Low (α.degree + 1) (f - g) := fun β hβ => by rw [map_sub, h β (by omega), sub_self]
  have h0 : coeff α (expOp O (f - g)) = 0 := by
    rw [coeff_expOp_def]
    unfold opN
    rw [map_sum]
    exact sum_eq_zero fun n _ => by rw [coeff_rat_smul, hl.iterate O n α (by omega), smul_zero]
  have h1 : f = (f - g) + g := (sub_add_cancel f g).symm
  rw [h1, expOp_add, map_add, h0, zero_add]

/-- e^𝒪 commutes with the exponential of power series. -/
theorem expOp_expW {O : X → A →ₗ[ℚ] A} (hO : ∀ v, IsDer (O v)) {w : MvPowerSeries X A} (hw : constantCoeff w = 0) : expOp O (expW w) = expW (expOp O w) :=
  hom_expW (expOpHom O hO) (coeff_expOp_congr O) hw

/-- e^𝒪 does not change the constant term. -/
theorem constantCoeff_expOp (O : X → A →ₗ[ℚ] A) (f : MvPowerSeries X A) : constantCoeff (expOp O f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_expOp_def]
  simp [opN]

/-! ### The series Σ_v x_v·b_v -/

/-- Σ_v x_v·b_v: the coefficient of x_v is b_v, all other coefficients are 0. -/
noncomputable def lin (b : X → A) : MvPowerSeries X A := fun α => if α.degree = 1 then ∑ v ∈ α.support, b v else 0

omit [Algebra ℚ A] in
theorem coeff_lin (b : X → A) (α : X →₀ ℕ) : coeff α (lin b) = if α.degree = 1 then ∑ v ∈ α.support, b v else 0 := rfl

omit [Algebra ℚ A] in
theorem constantCoeff_lin (b : X → A) : constantCoeff (lin b) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_lin, map_zero, if_neg zero_ne_one]

/-! ### The same for derivations -/

theorem isDer_derivation (d : Derivation ℚ A A) : IsDer d.toLinearMap := fun a b => by
  show d (a * b) = a * d b + d a * b
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_comm b]

/-- A derivation applied to every coefficient. -/
noncomputable def mapD (d : Derivation ℚ A A) : MvPowerSeries X A →ₗ[ℚ] MvPowerSeries X A := mapE d.toLinearMap

theorem coeff_mapD (d : Derivation ℚ A A) (f : MvPowerSeries X A) (α : X →₀ ℕ) : coeff α (mapD d f) = d (coeff α f) := rfl

/-- Σ_i x_i·D_i. -/
noncomputable def dsum (D : X → Derivation ℚ A A) : MvPowerSeries X A →ₗ[ℚ] MvPowerSeries X A := opX fun i => (D i).toLinearMap

theorem coeff_dsum (D : X → Derivation ℚ A A) (f : MvPowerSeries X A) (α : X →₀ ℕ) :
    coeff α (dsum D f) = ∑ i ∈ α.support, D i (coeff (α - Finsupp.single i 1) f) := rfl

/-- e^{Σ_i x_i·D_i}, a ring homomorphism. -/
noncomputable def expD (D : X → Derivation ℚ A A) : MvPowerSeries X A →+* MvPowerSeries X A :=
  expOpHom (fun i => (D i).toLinearMap) fun i => isDer_derivation (D i)

/-- e^{Σ x_i D_i} fixes the series on whose coefficients all D_i vanish. -/
theorem expD_of_zero (D : X → Derivation ℚ A A) {w : MvPowerSeries X A} (h : ∀ i α, D i (coeff α w) = 0) : expD D w = w := by
  refine expOp_of_zero _ ?_
  ext α
  rw [coeff_opX, map_zero]
  exact sum_eq_zero fun i _ => h i _

/-- Taylor's formula: e^{Σ x_i D_i} w = w + Σ_i x_i·D_i w, if all D_i D_j vanish on the coefficients
of w. -/
theorem expD_of_sq_zero (D : X → Derivation ℚ A A) {w : MvPowerSeries X A} (h : ∀ i j α, D i (D j (coeff α w)) = 0) : expD D w = w + dsum D w := by
  refine expOp_of_sq_zero _ ?_
  ext α
  rw [coeff_opX, map_zero]
  refine sum_eq_zero fun i _ => ?_
  rw [coeff_opX, map_sum]
  exact sum_eq_zero fun j _ => h i j _

/-- e^{Σ x_i D_i} commutes with the exponential of power series. -/
theorem expD_expW (D : X → Derivation ℚ A A) {w : MvPowerSeries X A} (hw : constantCoeff w = 0) : expD D (expW w) = expW (expD D w) :=
  expOp_expW (fun i => isDer_derivation (D i)) hw

theorem constantCoeff_expD (D : X → Derivation ℚ A A) (f : MvPowerSeries X A) : constantCoeff (expD D f) = constantCoeff f := constantCoeff_expOp _ f

end GeneralPieces.GenF
