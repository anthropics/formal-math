/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.GenF.Products
public import GeneralPieces.GenF.Bra
public import GeneralPieces.GenF.Borel
public import ClauseBound.Boson.Basic

/-! # The lemma on the operators Q_s: f₊ = ⟨Y(a, ω₁)·Y(b, ω₂)⟩ is μ!·ν! times the coefficient of x^μ·x'^ν in ⟨e^{A⁺}e^{A⁻}·e^{B⁺}e^{B⁻}⟩

The paper (proof of Lemma 9): "Expanding the exponentials gives e^{A⁺}e^{A⁻} = Σ_μ x^μ·Y(t^μ,
ω₁)/μ!, and likewise e^{B⁺}e^{B⁻} = Σ_ν x'^ν·Y(t^ν, ω₂)/ν!", and "let f₊ = ⟨Y(a, ω₁)·Y(b, ω₂)⟩".
Here the two expansions are hypotheses, in the
form of the interface statements below: `StY1`, `StY1'` for the family that is applied first,
`StY2`, `StXo` for the other. What is proved is their composition: the product of the two operators
is the sum over the
monomials t^τ in between (`map_eq_fP`), "by (O1)" only the τ of one weight contribute to the
coefficient of each power of the outer variable, and this sum is the entry of the product a[r]∘b[−r]
of matrices.
The result is the interface statement `StY` (`stY_of`), for both readings. -/

public section

namespace GeneralPieces.GenF

open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset

/-- The expansion of e^{B⁺}e^{B⁻}: ν! times the coefficient of x'^ν in e^{B⁺}e^{B⁻}·t^σ' has at t^τ
the coefficient ⟨τ|Y(t^ν, v)|σ'⟩ = ⟨τ|t^ν[r]|σ'⟩·v^{r−|ν|} with r = |τ| − |σ'|. -/
@[expose] def StY1 : Prop := ∀ (rd : Bool) (b : List ℕ), Pos b → ∀ τ σ' : Multiset ℕ,
  bra τ (fac (aL (xo rd) b) • MvPowerSeries.coeff (aL (xo rd) b) (expW (Bp rd) * ket rd σ')) =
    ((op b ((τ.sum : ℤ) - σ'.sum) τ σ' : ℤ) : ℚ) • mo 0 ((τ.sum : ℤ) - σ'.sum - b.sum)

/-- The variables of the inner family do not occur in e^{B⁺}e^{B⁻}·t^σ'. -/
@[expose] def StY1' : Prop := ∀ (rd : Bool) (n : ℕ) (σ' : Multiset ℕ), MvPowerSeries.pderiv Tv (xi rd n) (expW (Bp rd) * ket rd σ') = 0

/-- t₀ does not occur: the entries of t^ν[r] in the rows of the monomials with t₀ vanish. -/
@[expose] def StOp0 : Prop := ∀ (b : List ℕ) (r : ℤ) (τ σ : Multiset ℕ), 0 ∈ τ → 0 ∉ σ → op b r τ σ = 0

/-- The expansion of e^{A⁺}e^{A⁻}: μ! times the coefficient of x^μ in ⟨t^σ|e^{A⁺}e^{A⁻}·w⟩, written
as a derivative at 0, is a linear form applied to w, and on t^τ the form is
⟨σ|Y(t^μ, u)|τ⟩ = ⟨σ|t^μ[r]|τ⟩·u^{r−|μ|} with r = |σ| − |τ|. Here w is free of the variables of the
inner family. -/
@[expose] def StY2 : Prop := ∀ (rd : Bool) (E : ℕ) (a : List ℕ) (σ : Multiset ℕ), Pos a → σ.sum ≤ E → ∃ ℓ : Vu →ₗ[Lu] Lu,
  (∀ τ : Multiset ℕ, ℓ (MvPolynomial.monomial (Multiset.toFinsupp τ) 1) = C ((op a ((σ.sum : ℤ) - τ.sum) σ τ : ℤ) : ℚ) * T ((σ.sum : ℤ) - τ.sum - a.sum)) ∧
    ∀ w : W, (∀ n, MvPowerSeries.pderiv Tv (xi rd n) w = 0) →
      MvPowerSeries.constantCoeff (pdL (a.map (xi rd)) (braW σ (expW (Ap rd E) * Phi rd w))) = (MvPowerSeries.constantCoeff w).map ℓ

/-- The derivatives with respect to the variables of the outer family pass through
⟨t^σ|e^{A⁺}e^{A⁻}·⟩. -/
@[expose] def StXo : Prop := ∀ (rd : Bool) (E : ℕ) (σ : Multiset ℕ) (b : List ℕ) (w : W),
  pdL (b.map (xo rd)) (braW σ (expW (Ap rd E) * Phi rd w)) = braW σ (expW (Ap rd E) * Phi rd (pdL (b.map (xo rd)) w))

/-- A linear form on the polynomials in the t_k is determined by its values on the monomials. -/
theorem form_eq_sum (ℓ : Vu →ₗ[Lu] Lu) (p : Vu) : ℓ p = ∑ m ∈ p.support, MvPolynomial.coeff m p * ℓ (MvPolynomial.monomial m 1) := by
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
  rw [map_sum]
  refine sum_congr rfl fun m _ => ?_
  have e : MvPolynomial.monomial m (MvPolynomial.coeff m p) = MvPolynomial.coeff m p • MvPolynomial.monomial m (1 : Lu) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, smul_eq_mul]

/-- ⟨Y(a, u)·Y(b, v)⟩ = Σ_r ⟨a[r]∘b[−r]⟩·u^{r−h'}·v^{−r−h}: if g has the coefficients ⟨τ|Y(b, v)|σ'⟩
and the form ℓ has the values ⟨σ|Y(a, u)|τ⟩, then ℓ applied to g is f₊. -/
theorem map_eq_fP (h0 : StOp0) {a b : List ℕ} {σ σ' : Multiset ℕ} (hσ' : 0 ∉ σ') (hw : σ.sum = σ'.sum) (ℓ : Vu →ₗ[Lu] Lu)
    (hℓ : ∀ τ : Multiset ℕ, ℓ (MvPolynomial.monomial (Multiset.toFinsupp τ) 1) = C ((op a ((σ.sum : ℤ) - τ.sum) σ τ : ℤ) : ℚ) * T ((σ.sum : ℤ) - τ.sum - a.sum))
    (g : Tv) (hg : ∀ τ : Multiset ℕ, bra τ g = ((op b ((τ.sum : ℤ) - σ'.sum) τ σ' : ℤ) : ℚ) • mo 0 ((τ.sum : ℤ) - σ'.sum - b.sum)) :
    g.map ℓ = fP a b σ σ' := by
  classical
  ext y : 2
  change ℓ (g.coeff y) = _
  have hc : ∀ τ : Multiset ℕ, MvPolynomial.coeff (Multiset.toFinsupp τ) (g.coeff y) =
      if y = (τ.sum : ℤ) - σ'.sum - b.sum then C ((op b ((τ.sum : ℤ) - σ'.sum) τ σ' : ℤ) : ℚ) else 0 := fun τ => by
    rw [← coeff_bra, hg, coeff_smul_mo, T_zero, mul_one]
  have hw' : (σ.sum : ℤ) = σ'.sum := by exact_mod_cast hw
  have key : ℓ (g.coeff y) = C ((mul2 a (-y - b.sum) b (y + b.sum) σ σ' : ℤ) : ℚ) * T (-((a.sum : ℤ) + b.sum) - y) := by
    have e1 : ∑ m ∈ (g.coeff y).support, MvPolynomial.coeff m (g.coeff y) * ℓ (MvPolynomial.monomial m 1) =
        ∑ τ ∈ (g.coeff y).support.image Finsupp.toMultiset,
          MvPolynomial.coeff (Multiset.toFinsupp τ) (g.coeff y) * ℓ (MvPolynomial.monomial (Multiset.toFinsupp τ) 1) := by
      rw [sum_image fun m _ m' _ h => by
        have h' := congrArg Multiset.toFinsupp h
        rwa [Finsupp.toMultiset_toFinsupp, Finsupp.toMultiset_toFinsupp] at h']
      exact sum_congr rfl fun m _ => by rw [Finsupp.toMultiset_toFinsupp]
    rw [form_eq_sum, e1, mul2, Int.cast_sum, map_sum, sum_mul]
    refine sum_congr_of_eq_on_inter (fun τ _ h2 => ?_) (fun τ h1 h2 => ?_) fun τ _ h2 => ?_
    · rw [hc]
      split_ifs with hy
      · have h3 : 0 ∈ τ := by
          by_contra h3
          exact h2 (mem_Pz.2 ⟨by omega, h3⟩)
        rw [h0 b _ τ σ' h3 hσ', Int.cast_zero, map_zero, zero_mul]
      · rw [zero_mul]
    · have h3 := (mem_Pz.1 h1).1
      have h4 : MvPolynomial.coeff (Multiset.toFinsupp τ) (g.coeff y) = 0 := by
        by_contra h4
        exact h2 (mem_image.2 ⟨Multiset.toFinsupp τ, MvPolynomial.mem_support_iff.2 h4, Multiset.toFinsupp_toMultiset τ⟩)
      rw [hc, if_pos (by omega), show (τ.sum : ℤ) - σ'.sum = y + b.sum by omega] at h4
      rw [Int.cast_mul, map_mul, h4, mul_zero, zero_mul]
    · have h3 := (mem_Pz.1 h2).1
      rw [hc, if_pos (by omega), hℓ, show (τ.sum : ℤ) - σ'.sum = y + b.sum by omega, show (σ.sum : ℤ) - τ.sum = -y - b.sum by omega,
        show -y - (b.sum : ℤ) - a.sum = -((a.sum : ℤ) + b.sum) - y by ring, Int.cast_mul, map_mul]
      ring
  rw [key, fP, Series.diag, HahnSeries.coeff_ofSuppBddBelow]
  split_ifs with hy
  · rfl
  · rw [mul2_eq_zero a b _ σ (by omega), Int.cast_zero, map_zero, zero_mul]

theorem aL_eq_expo (ι : ℕ → X) (a : List ℕ) : aL ι a = expo (a.map ι) := by
  rw [aL, expo, List.map_map]
  rfl

/-- μ!·ν! times the coefficient of x^μ·x'^ν in ⟨e^{A⁺}e^{A⁻}·e^{B⁺}e^{B⁻}⟩ is f₊ = ⟨Y(a, u)·Y(b,
v)⟩, from the expansions of the two pairs of exponentials. -/
theorem stY_of (h1 : StY1) (h1' : StY1') (h0 : StOp0) (h2 : StY2) (hxo : StXo) : StY := by
  intro rd E a b σ σ' ha hb _ hσ' hw hE
  obtain ⟨ℓ, hℓ, hform⟩ := h2 rd E a σ ha hE
  have hfree : ∀ n, MvPowerSeries.pderiv Tv (xi rd n) (pdL (b.map (xo rd)) (expW (Bp rd) * ket rd σ')) = 0 := fun n =>
    (pderiv_pdL (R := Tv) (xi rd n) (b.map (xo rd)) (expW (Bp rd) * ket rd σ')).trans (by rw [h1' rd n σ']; exact pdL_zero (R := Tv) _)
  have e : aL (xi rd) a + aL (xo rd) b = expo (b.map (xo rd) ++ a.map (xi rd)) := by
    rw [expo_append, aL_eq_expo, aL_eq_expo, add_comm]
  have hb0 := borel_zero (R := Tv) (b.map (xo rd)) (expW (Bp rd) * ket rd σ')
  rw [e, borel_zero, pdL_append, plusSide, hxo, hform _ hfree, ← hb0, ← aL_eq_expo]
  exact map_eq_fP h0 hσ' hw ℓ hℓ _ (h1 rd b hb · σ')

end GeneralPieces.GenF
