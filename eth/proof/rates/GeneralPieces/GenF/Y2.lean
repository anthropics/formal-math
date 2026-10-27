/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.GenF.DDComm
public import GeneralPieces.GenF.Borel
public import ClauseBound.Boson.Basic

/-! # The lemma on the operators Q_s, paragraph "Generating functions": e^{A⁺}·e^{A⁻} = Σ_μ x^μ·Y(t^μ, ω₁)/μ!

"Expanding the exponentials gives e^{A⁺}e^{A⁻} = Σ_μ x^μ Y(t^μ, ω₁)/μ!." Here the coefficients are
not found by expanding, but from the differential equations in the variables x_n: the derivative of
⟨e^{A⁺}·e^{A⁻}·w⟩ with respect to x_n is ⟨J_n^+·e^{A⁺}e^{A⁻}·w⟩ + ⟨e^{A⁺}e^{A⁻}·J_n^-·w⟩
(`pderiv_GG_xi`), and this is the recursion (O2), Y(t_n·a') = J_n^+·Y(a') + Y(a')·J_n^-.
`y0 a σ` is the linear form p ↦ ⟨t^σ| Y(a, u) p⟩ on the polynomials in the t_k, defined by this
recursion; on a monomial t^τ it is the entry (σ, τ) of the matrix of a[r], r = |σ| − |τ|, times
u^{r−|a|} (`y0_monomial`).
`Y2`: μ! times the coefficient of x^μ in ⟨e^{A⁺}e^{A⁻}·w⟩ is `y0` applied to w. -/

public section

namespace GeneralPieces.GenF

open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset

/-! ### The linear form ⟨t^σ| Y(a, u) · ⟩ -/

/-- p ↦ ⟨t^σ| Y(a, u) p⟩, by the recursion Y(t_n·a') = J_n^+(u)·Y(a') + Y(a')·J_n^-(u). -/
@[expose] noncomputable def y0 : List ℕ → Multiset ℕ → (Vu →ₗ[Lu] Lu)
  | [], σ => MvPolynomial.lcoeff Lu (Multiset.toFinsupp σ)
  | n :: a, σ => ∑ l ∈ σ.toFinset, (C (bet n l : ℚ) * T ((l : ℤ) - n)) • y0 a (σ.erase l) + (y0 a σ).comp (JmU n).toLinearMap

theorem y0_nil (σ : Multiset ℕ) (p : Vu) : y0 [] σ p = MvPolynomial.coeff (Multiset.toFinsupp σ) p := rfl

theorem y0_cons (n : ℕ) (a : List ℕ) (σ : Multiset ℕ) (p : Vu) :
    y0 (n :: a) σ p = ∑ l ∈ σ.toFinset, (C (bet n l : ℚ) * T ((l : ℤ) - n)) * y0 a (σ.erase l) p + y0 a σ (JmU n p) := by
  show (∑ l ∈ σ.toFinset, (C (bet n l : ℚ) * T ((l : ℤ) - n)) • y0 a (σ.erase l) + (y0 a σ).comp (JmU n).toLinearMap) p = _
  rw [LinearMap.add_apply, LinearMap.sum_apply]
  rfl

/-- J_n^-(u) on a monomial. -/
theorem JmU_monomial (n : ℕ) (τ : Multiset ℕ) : JmU n (MvPolynomial.monomial (Multiset.toFinsupp τ) 1) =
    ∑ k ∈ τ.toFinset, ((τ.count k : Lu) * (C ((k : ℚ) * (bet n (-(k : ℤ)) : ℚ)) * T (-(k : ℤ) - n))) • MvPolynomial.monomial (Multiset.toFinsupp (τ.erase k)) (1 : Lu) := by
  rw [JmU, MvPolynomial.mkDerivation_monomial, one_smul, Finsupp.sum, Multiset.toFinsupp_support]
  refine sum_congr rfl fun k _ => ?_
  rw [Multiset.toFinsupp_apply, smul_eq_mul, toFinsupp_erase, MvPolynomial.C_apply, MvPolynomial.monomial_mul, add_zero, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem CT_mul (q q' : ℚ) (x x' : ℤ) : (C q * T x : Lu) * (C q' * T x') = C (q * q') * T (x + x') := by
  rw [T_add, map_mul]
  ring

/-- On the monomial t^τ: the entry (σ, τ) of the matrix of a[r], r = |σ| − |τ|, times u^{r−|a|}. -/
theorem y0_monomial (a : List ℕ) : ∀ σ τ : Multiset ℕ, y0 a σ (MvPolynomial.monomial (Multiset.toFinsupp τ) 1) =
    C ((op a ((σ.sum : ℤ) - τ.sum) σ τ : ℤ) : ℚ) * T ((σ.sum : ℤ) - τ.sum - a.sum) := by
  induction a with
  | nil =>
    intro σ τ
    rw [y0_nil, MvPolynomial.coeff_monomial]
    by_cases h : σ = τ
    · subst h
      simp [op, one]
    · have h0 : op [] ((σ.sum : ℤ) - τ.sum) σ τ = 0 := by
        unfold op
        split_ifs <;> simp [one, h]
      rw [if_neg fun h' => h (Multiset.toFinsupp.injective h').symm, h0]
      simp
  | cons n a ih =>
    intro σ τ
    rw [y0_cons, JmU_monomial, map_sum]
    show _ = C ((nop n (op a) ((σ.sum : ℤ) - τ.sum) σ τ : ℤ) : ℚ) * _
    unfold nop
    rw [Int.cast_add, Int.cast_sum, Int.cast_sum, map_add, map_sum, map_sum, add_mul, sum_mul, sum_mul]
    have hs : (((n :: a).sum : ℕ) : ℤ) = (n : ℤ) + a.sum := by rw [List.sum_cons, Nat.cast_add]
    congr 1
    · refine sum_congr rfl fun l hl => ?_
      have hl' := Multiset.mem_toFinset.1 hl
      have e : (l : ℤ) - n + ((σ.sum : ℤ) - τ.sum - l - a.sum) = (σ.sum : ℤ) - τ.sum - ((n :: a).sum : ℕ) := by rw [hs]; ring
      rw [ih, Basic.sum_erase_cast hl', CT_mul, cre, if_pos hl', show (σ.sum : ℤ) - l - τ.sum = (σ.sum : ℤ) - τ.sum - l by ring, e, Int.cast_mul]
    · refine sum_congr rfl fun k hk => ?_
      have hk' := Multiset.mem_toFinset.1 hk
      have e : -(k : ℤ) - n + ((σ.sum : ℤ) - τ.sum + k - a.sum) = (σ.sum : ℤ) - τ.sum - ((n :: a).sum : ℕ) := by rw [hs]; ring
      have e2 : ((τ.count k : ℕ) : Lu) = C ((τ.count k : ℕ) : ℚ) := (map_natCast (C : ℚ →+* Lu) _).symm
      rw [map_smul, ih, Basic.sum_erase_cast hk', smul_eq_mul, e2, ← mul_assoc (C _) (C _) (T _), ← map_mul, CT_mul, ann,
        show (σ.sum : ℤ) - ((τ.sum : ℤ) - k) = (σ.sum : ℤ) - τ.sum + k by ring, e]
      congr 2
      push_cast
      ring

/-! ### The differential equations of ⟨e^{A⁺}·e^{A⁻}·w⟩ -/

/-- ⟨e^{A⁺}·e^{A⁻}·w⟩: the coefficient of t^σ in e^{A⁺}·e^{A⁻}·w. -/
@[expose] noncomputable def GG (rd : Bool) (E : ℕ) (σ : Multiset ℕ) (w : W) : PS := braW σ (expW (Ap rd E) * Phi rd w)

theorem mapD_zero (w : W) : mapD (0 : Derivation ℚ Tv Tv) w = 0 := by
  ext α : 1
  show (0 : Derivation ℚ Tv Tv) (MvPowerSeries.coeff α w) = 0
  rfl

theorem pderiv_prod (rd : Bool) (E : ℕ) (i : X) (w : W) : MvPowerSeries.pderiv Tv i (expW (Ap rd E) * Phi rd w) =
    MvPowerSeries.C (sel rd (fun n => HahnSeries.C (JpU E n)) 0 i) * (expW (Ap rd E) * Phi rd w) +
      expW (Ap rd E) * (Phi rd (MvPowerSeries.pderiv Tv i w) + Phi rd (mapD (DD rd i) w)) := by
  have h1 : MvPowerSeries.pderiv Tv i (expW (Ap rd E)) = MvPowerSeries.C (sel rd (fun n => HahnSeries.C (JpU E n)) 0 i) * expW (Ap rd E) := by
    rw [pderiv_expW (A := Tv) i (w := Ap rd E) (constantCoeff_lin _), Ap, pderiv_lin (A := Tv) _ i]
  have h2 : MvPowerSeries.pderiv Tv i (Phi rd w) = Phi rd (MvPowerSeries.pderiv Tv i w) + Phi rd (mapD (DD rd i) w) := pderiv_expD (DD_comm rd) i w
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, h1, h2]
  ring

/-- The derivative with respect to a variable of the outer family falls on w. -/
theorem pderiv_GG_xo (rd : Bool) (E : ℕ) (σ : Multiset ℕ) (n : ℕ) (w : W) :
    MvPowerSeries.pderiv S (xo rd n) (GG rd E σ w) = GG rd E σ (MvPowerSeries.pderiv Tv (xo rd n) w) := by
  have h : (sel rd (fun n => (HahnSeries.C (JpU E n) : Tv)) 0 (xo rd n) : Tv) = 0 := by
    rw [sel_xo']
    unfold z0
    split_ifs <;> rfl
  rw [GG, pderiv_braW, pderiv_prod, h, DD_xo, mapD_zero, map_zero, map_zero, zero_mul, zero_add, add_zero]
  rfl

/-- The derivative with respect to the variable x_n of the inner family: ⟨J_n^+·e^{A⁺}e^{A⁻}·w⟩ +
⟨e^{A⁺}e^{A⁻}·J_n^-·w⟩, if w does not depend on x_n. -/
theorem pderiv_GG_xi (rd : Bool) {E : ℕ} {σ : Multiset ℕ} (hσ : σ.sum ≤ E) {n : ℕ} (hn : 1 ≤ n) {w : W} (hw : MvPowerSeries.pderiv Tv (xi rd n) w = 0) :
    MvPowerSeries.pderiv S (xi rd n) (GG rd E σ w) =
      ∑ l ∈ σ.toFinset, MvPowerSeries.C ((bet n l : ℚ) • mo ((l : ℤ) - n) 0) * GG rd E (σ.erase l) w + GG rd E σ (mapD (JmT n) w) := by
  rw [GG, pderiv_braW, pderiv_prod, sel_xi rd _ _ hn, DD_xi rd hn, hw, map_zero, zero_add, braW_add, braW_C_JpU_mul hσ]
  rfl

theorem constantCoeff_GG (rd : Bool) (E : ℕ) (σ : Multiset ℕ) (w : W) : MvPowerSeries.constantCoeff (GG rd E σ w) = bra σ (MvPowerSeries.constantCoeff w) := by
  rw [GG, constantCoeff_braW, map_mul, constantCoeff_expW (Ap rd E), one_mul, Phi, constantCoeff_expD (DD rd) w]

theorem pdL_GG_xo (rd : Bool) (E : ℕ) (σ : Multiset ℕ) (b : List ℕ) : ∀ w : W, pdL (b.map (xo rd)) (GG rd E σ w) = GG rd E σ (pdL (b.map (xo rd)) w) := by
  induction b with
  | nil => intro w; rfl
  | cons n b ih => intro w; rw [List.map_cons, pdL_cons, pdL_cons, pderiv_GG_xo, ih]

theorem sum_erase_le_sum (σ : Multiset ℕ) (l : ℕ) : (σ.erase l).sum ≤ σ.sum := by
  by_cases h : l ∈ σ
  · have := Multiset.sum_erase h
    omega
  · rw [Multiset.erase_of_notMem h]

theorem coeff_smul_mo_mul (q : ℚ) (x : ℤ) (f : S) (y : ℤ) : ((q • mo x 0) * f).coeff y = (C q * T x) * f.coeff y := by
  rw [smul_mul_assoc, HahnSeries.coeff_smul, mo, HahnSeries.coeff_single_zero_mul, Algebra.smul_def, mul_assoc]
  rfl

/-- "e^{A⁺}e^{A⁻} = Σ_μ x^μ·Y(t^μ, ω₁)/μ!": the derivative of ⟨e^{A⁺}e^{A⁻}·w⟩ with respect to the
variables x_n, n in a, has the constant term ⟨t^σ| Y(a, u) w₀⟩, w₀ the constant term of w, if w does
not
depend on the variables of the inner family. By `borel_zero` this is μ! times the coefficient of
x^μ. -/
theorem Y2 (rd : Bool) (E : ℕ) (a : List ℕ) : Pos a → ∀ (σ : Multiset ℕ) (w : W), σ.sum ≤ E → (∀ n, MvPowerSeries.pderiv Tv (xi rd n) w = 0) →
    MvPowerSeries.constantCoeff (pdL (a.map (xi rd)) (GG rd E σ w)) = (MvPowerSeries.constantCoeff w).map (y0 a σ) := by
  induction a with
  | nil =>
    intro _ σ w _ _
    rw [List.map_nil, pdL_nil, constantCoeff_GG]
    rfl
  | cons n a ih =>
    intro ha σ w hσ hw
    have ha' : Pos a := fun m hm => ha m (List.mem_cons_of_mem _ hm)
    have hw' : ∀ m, MvPowerSeries.pderiv Tv (xi rd m) (mapD (JmT n) w) = 0 := fun m => by
      rw [mapD, pderiv_mapE (A := Tv) (JmT n).toLinearMap (xi rd m) w, hw m, map_zero]
    rw [List.map_cons, pdL_cons, pderiv_GG_xi rd hσ (ha n List.mem_cons_self) (hw n), pdL_add, pdL_sum, map_add, map_sum, ih ha' σ _ hσ hw',
      sum_congr rfl fun l _ => by rw [pdL_C_mul, map_mul, MvPowerSeries.constantCoeff_C, ih ha' (σ.erase l) w ((sum_erase_le_sum σ l).trans hσ) hw]]
    ext y : 2
    rw [HahnSeries.coeff_add, HahnSeries.coeff_sum]
    simp only [coeff_smul_mo_mul]
    show _ = y0 (n :: a) σ ((MvPowerSeries.constantCoeff w).coeff y)
    rw [y0_cons]
    rfl

end GeneralPieces.GenF
