/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-! # The exponential of a formal power series without constant term

"Exponentials of these are formal power series in the x_n, x'_n" (Appendix B, the paragraph on
generating functions). For a commutative ℚ-algebra R and a set X of variables, `expW w` is
Σ_n wⁿ/n! for a power series w in the variables X over R without constant term: the coefficient of a
monomial of degree d is that of the finite sum over n ≤ d. Proved here: the constant term of e^w is
1,
e^{a+b} = e^a·e^b, a ring homomorphism applied to the coefficients commutes with the exponential,
and: if the coefficient of every monomial α in w is a rational number times ε^{wt α}, for an
additive weight wt, then so it is
in e^w, with a rational number that does not depend on ε or on R (`coeff_expW_of_weight`). -/

@[expose] public section

namespace GeneralPieces.GenF

open Finset MvPowerSeries

variable {X R : Type} [CommRing R] [Algebra ℚ R]

/-! ### A sum over a triangle and over a square -/

/-- If F i j = 0 for i + j ≥ N, the sum of F over i + j < N is the sum over i, j < N. -/
theorem sum_triangle {M : Type} [AddCommMonoid M] (N : ℕ) (F : ℕ → ℕ → M) (h : ∀ i j, N ≤ i + j → F i j = 0) :
    ∑ n ∈ range N, ∑ p ∈ antidiagonal n, F p.1 p.2 = ∑ i ∈ range N, ∑ j ∈ range N, F i j := by
  rw [← sum_product' (range N) (range N) F]
  have h1 : ∑ p ∈ range N ×ˢ range N, F p.1 p.2 = ∑ p ∈ (range N ×ˢ range N) with p.1 + p.2 < N, F p.1 p.2 := by
    rw [sum_filter]
    refine sum_congr rfl fun p _ => ?_
    split_ifs with hp
    · rfl
    · exact h p.1 p.2 (by omega)
  rw [h1, ← sum_fiberwise_of_maps_to (t := range N) (g := fun p : ℕ × ℕ => p.1 + p.2) fun p hp => mem_range.2 (mem_filter.1 hp).2]
  refine sum_congr rfl fun n hn => sum_congr ?_ fun _ _ => rfl
  have hn' := mem_range.1 hn
  ext p
  simp only [mem_antidiagonal, mem_filter, mem_product, mem_range]
  omega

/-! ### The definition -/

/-- Σ_{n < N} wⁿ/n!. -/
noncomputable def expN (N : ℕ) (w : MvPowerSeries X R) : MvPowerSeries X R := ∑ n ∈ range N, ((n.factorial : ℚ)⁻¹) • w ^ n

/-- e^w = Σ_n wⁿ/n!, for w without constant term: the coefficient of a monomial of degree d is taken
from the sum over n ≤ d. -/
noncomputable def expW (w : MvPowerSeries X R) : MvPowerSeries X R := fun α => coeff α (expN (α.degree + 1) w)

theorem coeff_expW_def (w : MvPowerSeries X R) (α : X →₀ ℕ) : coeff α (expW w) = coeff α (expN (α.degree + 1) w) := rfl

theorem coeff_rat_smul (α : X →₀ ℕ) (q : ℚ) (f : MvPowerSeries X R) : coeff α (q • f) = q • coeff α f := map_rat_smul (coeff α) q f

omit [Algebra ℚ R] in
/-- wⁿ has no monomials of degree less than n. -/
theorem coeff_pow_eq_zero {w : MvPowerSeries X R} (hw : constantCoeff w = 0) {α : X →₀ ℕ} {n : ℕ} (h : α.degree < n) : coeff α (w ^ n) = 0 :=
  coeff_eq_zero_of_constantCoeff_nilpotent (m := 1) (by rw [pow_one, hw]) (by omega)

/-- More terms of the sum do not change the coefficient. -/
theorem coeff_expW {w : MvPowerSeries X R} (hw : constantCoeff w = 0) {α : X →₀ ℕ} {N : ℕ} (h : α.degree < N) : coeff α (expW w) = coeff α (expN N w) := by
  rw [coeff_expW_def]
  unfold expN
  rw [map_sum, map_sum]
  refine sum_subset (range_subset_range.2 (by omega)) fun n _ hn => ?_
  rw [coeff_rat_smul, coeff_pow_eq_zero hw (by simpa using hn), smul_zero]

omit [Algebra ℚ R] in
/-- The coefficient of α in a product depends only on the coefficients of the monomials of degree at
most that of α. -/
theorem coeff_mul_congr {f f' g g' : MvPowerSeries X R} {α : X →₀ ℕ} (hf : ∀ β : X →₀ ℕ, β.degree ≤ α.degree → coeff β f = coeff β f')
    (hg : ∀ β : X →₀ ℕ, β.degree ≤ α.degree → coeff β g = coeff β g') : coeff α (f * g) = coeff α (f' * g') := by
  classical
  rw [coeff_mul, coeff_mul]
  refine sum_congr rfl fun p hp => ?_
  have h := congrArg Finsupp.degree (mem_antidiagonal.1 hp)
  rw [map_add] at h
  rw [hf p.1 (by omega), hg p.2 (by omega)]

omit [Algebra ℚ R] in
/-- a^i·b^j has no monomials of degree less than i + j. -/
theorem coeff_pow_mul_pow_eq_zero {a b : MvPowerSeries X R} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) {α : X →₀ ℕ} {i j : ℕ}
    (h : α.degree < i + j) : coeff α (a ^ i * b ^ j) = 0 := by
  classical
  rw [coeff_mul]
  refine sum_eq_zero fun p hp => ?_
  have h' := congrArg Finsupp.degree (mem_antidiagonal.1 hp)
  rw [map_add] at h'
  by_cases h1 : p.1.degree < i
  · rw [coeff_pow_eq_zero ha h1, zero_mul]
  · rw [coeff_pow_eq_zero hb (by omega : p.2.degree < j), mul_zero]

/-! ### The rules -/

/-- The constant term of e^w is 1. -/
theorem constantCoeff_expW (w : MvPowerSeries X R) : constantCoeff (expW w) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_expW_def]
  simp [expN]

/-- (a+b)ⁿ/n! = Σ_{i+j=n} (a^i/i!)·(b^j/j!). -/
theorem add_pow_div (a b : MvPowerSeries X R) (n : ℕ) :
    ((n.factorial : ℚ)⁻¹) • (a + b) ^ n = ∑ p ∈ antidiagonal n, ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) • (a ^ p.1 * b ^ p.2) := by
  rw [(Commute.all a b).add_pow', smul_sum]
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

/-- e^{a+b} = e^a·e^b. -/
theorem expW_add {a b : MvPowerSeries X R} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) : expW (a + b) = expW a * expW b := by
  ext α
  have hab : constantCoeff (a + b) = 0 := by rw [map_add, ha, hb, add_zero]
  rw [coeff_mul_congr (f' := expN (α.degree + 1) a) (g' := expN (α.degree + 1) b) (fun β hβ => coeff_expW ha (by omega)) fun β hβ => coeff_expW hb (by omega),
    coeff_expW_def]
  unfold expN
  rw [sum_mul_sum, map_sum, map_sum]
  simp only [add_pow_div, map_sum, smul_mul_smul_comm]
  refine sum_triangle (α.degree + 1) (fun i j => coeff α (((i.factorial : ℚ)⁻¹ * (j.factorial : ℚ)⁻¹) • (a ^ i * b ^ j))) fun i j hij => ?_
  rw [coeff_rat_smul, coeff_pow_mul_pow_eq_zero ha hb (by omega), smul_zero]

/-- A ring homomorphism between rings of power series commutes with the finite sums. -/
theorem map_expN {Y R' : Type} [CommRing R'] [Algebra ℚ R'] (Φ : MvPowerSeries X R →+* MvPowerSeries Y R') (N : ℕ) (w : MvPowerSeries X R) :
    Φ (expN N w) = expN N (Φ w) := by
  unfold expN
  rw [map_sum]
  exact sum_congr rfl fun n _ => by rw [map_rat_smul, map_pow]

/-- A ring homomorphism applied to the coefficients commutes with the exponential. -/
theorem map_expW {R' : Type} [CommRing R'] [Algebra ℚ R'] (φ : R →+* R') (w : MvPowerSeries X R) : map φ (expW w) = expW (map φ w) := by
  ext α
  rw [coeff_map, coeff_expW_def, coeff_expW_def, ← map_expN, coeff_map]

/-- A ring homomorphism Φ of the ring of power series commutes with the exponential, if the
coefficient of α in Φ f depends only on the coefficients of f at the monomials of degree at most
that of α. -/
theorem hom_expW (Φ : MvPowerSeries X R →+* MvPowerSeries X R)
    (hΦ : ∀ (α : X →₀ ℕ) (f g : MvPowerSeries X R), (∀ β : X →₀ ℕ, β.degree ≤ α.degree → coeff β f = coeff β g) → coeff α (Φ f) = coeff α (Φ g))
    {w : MvPowerSeries X R} (hw : constantCoeff w = 0) : Φ (expW w) = expW (Φ w) := by
  ext α
  rw [hΦ α (expW w) (expN (α.degree + 1) w) fun β hβ => coeff_expW hw (by omega), map_expN, coeff_expW_def]

/-! ### Coefficients that are numbers times powers of one element -/

/-- The coefficient of every monomial α of a power series over ℚ is multiplied by ε^{wt α}. -/
noncomputable def twF (wt : (X →₀ ℕ) →+ ℕ) (ε : R) (f : MvPowerSeries X ℚ) : MvPowerSeries X R := fun α => algebraMap ℚ R (coeff α f) * ε ^ wt α

theorem coeff_twF (wt : (X →₀ ℕ) →+ ℕ) (ε : R) (f : MvPowerSeries X ℚ) (α : X →₀ ℕ) : coeff α (twF wt ε f) = algebraMap ℚ R (coeff α f) * ε ^ wt α := rfl

/-- This is a ring homomorphism, because the weight is additive. -/
noncomputable def tw (wt : (X →₀ ℕ) →+ ℕ) (ε : R) : MvPowerSeries X ℚ →+* MvPowerSeries X R where
  toFun := twF wt ε
  map_one' := by
    classical
    ext α
    rw [coeff_twF, coeff_one, coeff_one]
    split_ifs with h
    · rw [h, map_zero, pow_zero, map_one, mul_one]
    · rw [map_zero, zero_mul]
  map_mul' f g := by
    classical
    ext α
    rw [coeff_twF, coeff_mul, coeff_mul, map_sum, sum_mul]
    refine sum_congr rfl fun p hp => ?_
    rw [coeff_twF, coeff_twF, ← mem_antidiagonal.1 hp, map_add, pow_add, map_mul]
    ring
  map_zero' := by
    ext α
    rw [coeff_twF, map_zero, map_zero, map_zero, zero_mul]
  map_add' f g := by
    ext α
    rw [coeff_twF, map_add, map_add, map_add, add_mul, coeff_twF, coeff_twF]

theorem coeff_tw (wt : (X →₀ ℕ) →+ ℕ) (ε : R) (f : MvPowerSeries X ℚ) (α : X →₀ ℕ) : coeff α (tw wt ε f) = algebraMap ℚ R (coeff α f) * ε ^ wt α := rfl

theorem expW_tw (wt : (X →₀ ℕ) →+ ℕ) (ε : R) (q : MvPowerSeries X ℚ) : expW (tw wt ε q) = tw wt ε (expW q) := by
  ext α
  rw [coeff_expW_def, ← map_expN, coeff_tw, coeff_tw, coeff_expW_def]

/-- If the coefficient of every monomial α in w is q_α·ε^{wt α} with a rational number q_α, then its
coefficient in e^w is (the coefficient of α in e^q)·ε^{wt α}: the number is the same for every ε and
every R. -/
theorem coeff_expW_of_weight (wt : (X →₀ ℕ) →+ ℕ) (ε : R) (q : MvPowerSeries X ℚ) {w : MvPowerSeries X R}
    (hw : ∀ α, coeff α w = algebraMap ℚ R (coeff α q) * ε ^ wt α) (α : X →₀ ℕ) : coeff α (expW w) = algebraMap ℚ R (coeff α (expW q)) * ε ^ wt α := by
  have h : w = tw wt ε q := by ext β; rw [hw, coeff_tw]
  rw [h, expW_tw, coeff_tw]

end GeneralPieces.GenF
