/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.GenF.DDComm
public import GeneralPieces.GenF.NormalL

/-! # Lemma 9 (Appendix B), proof, paragraph "One Laurent polynomial": the differential equation of ⟨𝒩⟩

𝒩 = e^{A⁺}·e^{B⁺}·e^{A⁻}·e^{B⁻} is the product defined in the paragraph "Generating functions" of
that proof. Here ⟨𝒩⟩ (`normal`) is differentiated with respect to each of the variables x_n, x'_n
(`pderiv_normal`, `stNeq`).
"Multiplications commute with each other, and so do differentiations": so the derivative with
respect to the inner variable x_n brings down the factor J_n^+(u) on the left and J_n^-(u) on the
right, and
the derivative with respect to the outer variable brings down J_n^+(v) and J_n^-(v). On the left,
the coefficient of t^σ in t_l·w is the coefficient of t^{σ−l} in w (`braW_C_sel_mul`);
on the right, e^{A⁻}·e^{B⁻}·t^σ' is the product, over the parts k of σ', of t_k plus a linear form
in the x_n, x'_n without any t (`Phi` is a ring homomorphism, `ket` is a product), so the derivative
replaces each factor in turn
by the coefficient of the variable in that linear form (`der_factor`, `pderiv_Phi_ket`). The result:
the derivative of ⟨𝒩⟩ for (σ, σ') is a combination of the ⟨𝒩⟩ for (σ − l, σ') and (σ, σ' − k) whose
coefficients are numbers times powers of u, or of v. The statements of the paper on the coefficients
of ⟨𝒩⟩ are derived from this equation (in the form `StNeq`); the paper reads them off 𝒩 directly,
without a differential equation. -/

public section

namespace GeneralPieces.GenF

open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial

/-! ### The product rule, for any ring of coefficients -/

/-- The product rule for a product over a multiset. -/
theorem der_multiset_prod {B ι : Type} [CommRing B] [DecidableEq ι] (d : B →+ B) (hd : ∀ a b, d (a * b) = a * d b + d a * b) (s : Multiset ι) (f : ι → B) :
    d (s.map f).prod = ∑ k ∈ s.toFinset, s.count k • (d (f k) * ((s.erase k).map f).prod) := by
  rw [← Finset.sum_multiset_map_count]
  induction s using Multiset.induction_on with
  | empty =>
    have h1 : d 1 = 0 := by
      have := hd 1 1
      simpa using this
    simpa using h1
  | cons k s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, hd, ih, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head, add_comm, ← Multiset.sum_map_mul_left]
    congr 1
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun j hj => ?_)
    rw [Multiset.erase_cons_tail_of_mem hj, Multiset.map_cons, Multiset.prod_cons]
    ring

section Generic

variable {Y A : Type} [CommRing A] [Algebra ℚ A]

theorem Normal.mapD_C (d : Derivation ℚ A A) (a : A) : mapD (X := Y) d (MvPowerSeries.C a) = MvPowerSeries.C (d a) := by
  classical
  ext1 α
  rw [coeff_mapD, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
  split_ifs
  · rfl
  · exact map_zero d

theorem Normal.pderiv_rat_smul (i : Y) (q : ℚ) (f : MvPowerSeries Y A) : MvPowerSeries.pderiv A i (q • f) = q • MvPowerSeries.pderiv A i f :=
  map_rat_smul (MvPowerSeries.pderiv A i).toLinearMap q f

theorem Normal.C_rat_smul (q : ℚ) (a : A) : MvPowerSeries.C (σ := Y) (q • a) = q • MvPowerSeries.C (σ := Y) a :=
  map_rat_smul (MvPowerSeries.C (σ := Y) (R := A)) q a

/-- ∂/∂x_i of e^𝒪 applied to a product: if ∂f_k/∂x_i + O_i f_k = g_k and e^𝒪 fixes g_k, each factor
in turn is replaced by g_k. -/
theorem pderiv_expD_prod {D : Y → Derivation ℚ A A} (hc : ∀ i j a, D i (D j a) = D j (D i a)) (i : Y) {ι : Type} [DecidableEq ι] (s : Multiset ι)
    (f g : ι → MvPowerSeries Y A) (hf : ∀ k, MvPowerSeries.pderiv A i (f k) + mapD (D i) (f k) = g k) (hg : ∀ k, expD D (g k) = g k) :
    MvPowerSeries.pderiv A i (expD D (s.map f).prod) = ∑ k ∈ s.toFinset, s.count k • (g k * expD D ((s.erase k).map f).prod) := by
  have h1 := der_multiset_prod ((MvPowerSeries.pderiv A i : MvPowerSeries Y A →ₗ[A] MvPowerSeries Y A).toAddMonoidHom)
    (fun a b => by
      show MvPowerSeries.pderiv A i (a * b) = a * MvPowerSeries.pderiv A i b + MvPowerSeries.pderiv A i a * b
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_comm b]) s f
  have h2 := der_multiset_prod ((mapD (X := Y) (D i)).toAddMonoidHom) (fun a b => mapE_mul (isDer_derivation (D i)) a b) s f
  have h1' : MvPowerSeries.pderiv A i (s.map f).prod = ∑ k ∈ s.toFinset, s.count k • (MvPowerSeries.pderiv A i (f k) * ((s.erase k).map f).prod) := h1
  have h2' : mapD (D i) (s.map f).prod = ∑ k ∈ s.toFinset, s.count k • (mapD (D i) (f k) * ((s.erase k).map f).prod) := h2
  rw [pderiv_expD hc, ← map_add, h1', h2', ← Finset.sum_add_distrib, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← nsmul_add, ← add_mul, hf, map_nsmul, map_mul, hg]

/-- ∂/∂x_i of e^a·e^b·c. -/
theorem pderiv_three (i : Y) {a b : MvPowerSeries Y A} (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) (c : MvPowerSeries Y A) :
    MvPowerSeries.pderiv A i (expW a * (expW b * c)) =
      (MvPowerSeries.pderiv A i a + MvPowerSeries.pderiv A i b) * (expW a * (expW b * c)) + expW a * (expW b * MvPowerSeries.pderiv A i c) := by
  rw [Derivation.leibniz, Derivation.leibniz, pderiv_expW i ha, pderiv_expW i hb]
  simp only [smul_eq_mul]
  ring

end Generic

/-! ### The operators in A⁻ on the series without any t_k and on the t_k -/

/-- J_n^-(u) vanishes on the constant polynomials. -/
theorem Normal.JmT_emb (n : ℕ) (s : S) : JmT n (emb s) = 0 := by
  refine HahnSeries.ext (funext fun y => ?_)
  rw [JmT, coeff_hder]
  exact MvPolynomial.derivation_C (JmU n) (s.coeff y)

theorem Normal.DD_emb (rd : Bool) (i : X) (s : S) : DD rd i (emb s) = 0 := by
  rcases DD_eq rd i with h | ⟨n, h⟩
  · rw [h]
    rfl
  · rw [h, Normal.JmT_emb]

theorem Normal.sel_add {R : Type} [AddZeroClass R] (rd : Bool) (f g : ℕ → R) (i : X) : sel rd f 0 i + sel rd 0 g i = sel rd f g i := by
  cases rd <;> rcases i with n | n <;> by_cases hn : n = 0 <;> simp [sel, z0, hn]

theorem Normal.mapD_embW (rd : Bool) (i : X) (e : PS) : mapD (DD rd i) (embW e) = 0 := by
  ext1 α
  refine (coeff_mapD (DD rd i) (embW e) α).trans ?_
  rw [embW, MvPowerSeries.coeff_map, Normal.DD_emb, map_zero]

/-- e^{A⁻} fixes the series without any t_k. -/
theorem Phi_embW (rd : Bool) (e : PS) : Phi rd (embW e) = embW e := by
  rw [Phi, expD_of_zero (X := X) (A := Tv) (DD rd)]
  intro i α
  rw [embW, MvPowerSeries.coeff_map, Normal.DD_emb]

theorem Normal.emb_rat_smul (q : ℚ) (s : S) : emb (q • s) = q • emb s := by
  refine HahnSeries.ext (funext fun y => ?_)
  show MvPolynomial.C (q • s.coeff y) = q • MvPolynomial.C (s.coeff y)
  exact map_rat_smul (MvPolynomial.C : Lu →+* Vu) q _

theorem Normal.emb_smul_mo (q : ℚ) (x : ℤ) : emb (q • mo x 0) = HahnSeries.C (MvPolynomial.C (C q * T x)) := by
  refine HahnSeries.ext (funext fun y => ?_)
  show MvPolynomial.C (q • (mo x 0).coeff y) = _
  rw [mo, HahnSeries.C_apply]
  by_cases h : y = 0
  · rw [h, HahnSeries.coeff_single_same, HahnSeries.coeff_single_same, LaurentPolynomial.smul_eq_C_mul]
  · rw [HahnSeries.coeff_single_of_ne h, HahnSeries.coeff_single_of_ne h, smul_zero, map_zero]

/-- J_n^-(u) maps t_k to k·C(−k−1, n−1)·u^{−k−n}. -/
theorem JmT_tT (n k : ℕ) : JmT n (tT k) = emb ((k : ℚ) • ((bet n (-(k : ℤ)) : ℚ) • mo (-(k : ℤ) - n) 0)) := by
  rw [smul_smul, Normal.emb_smul_mo, JmT, tT, hder_C]
  congr 1
  exact MvPolynomial.mkDerivation_X _ _ _

/-- The operator beside x_i in A⁻ maps t_k to k times the coefficient of x_i in 𝖠_k. -/
theorem DD_tT (rd : Bool) (i : X) (k : ℕ) : DD rd i (tT k) = emb ((k : ℚ) • sel rd (fun n => (bet n (-(k : ℤ)) : ℚ) • mo (-(k : ℤ) - n) 0) 0 i) := by
  rw [DD, map_sel (fun d : Derivation ℚ Tv Tv => d (tT k)) rfl, map_sel (fun s : S => emb ((k : ℚ) • s)) (by simp)]
  congr 1
  · funext n
    exact JmT_tT n k
  · funext n
    simp

/-! ### The right side: e^{A⁻}·e^{B⁻}·t^σ' -/

/-- ∂/∂x_i + (the operator beside x_i in A⁻), on a factor t_k + k·(the coefficient of ∇_k in B⁻) of
e^{B⁻}·t^σ'. -/
theorem der_factor (rd : Bool) (i : X) (k : ℕ) :
    MvPowerSeries.pderiv Tv i (MvPowerSeries.C (tT k) + (k : ℚ) • embW (sfB' rd k)) + mapD (DD rd i) (MvPowerSeries.C (tT k) + (k : ℚ) • embW (sfB' rd k)) =
      embW (MvPowerSeries.C ((k : ℚ) • cS rd i (-(k : ℤ)))) := by
  have h1 : MvPowerSeries.pderiv Tv i (MvPowerSeries.C (tT k) + (k : ℚ) • embW (sfB' rd k)) =
      embW (MvPowerSeries.C ((k : ℚ) • sel rd 0 (fun n => (bet n (-(k : ℤ)) : ℚ) • mo 0 (-(k : ℤ) - n)) i)) := by
    rw [map_add, MvPowerSeries.pderiv_C, zero_add, Normal.pderiv_rat_smul (Y := X) (A := Tv), sfB', embW, map_lin (Y := X) (A := S) (A' := Tv),
      pderiv_lin (X := X) (A := Tv), MvPowerSeries.map_C, Normal.emb_rat_smul, Normal.C_rat_smul (Y := X) (A := Tv)]
  have h2 : mapD (DD rd i) (MvPowerSeries.C (tT k) + (k : ℚ) • embW (sfB' rd k)) =
      embW (MvPowerSeries.C ((k : ℚ) • sel rd (fun n => (bet n (-(k : ℤ)) : ℚ) • mo (-(k : ℤ) - n) 0) 0 i)) := by
    rw [map_add, map_smul, Normal.mapD_embW, smul_zero, add_zero, embW, MvPowerSeries.map_C, ← DD_tT, Normal.mapD_C (Y := X) (A := Tv)]
  rw [h1, h2, ← map_add, ← map_add, ← smul_add, add_comm, Normal.sel_add, cS]

/-- ∂/∂x_i of e^{A⁻}·e^{B⁻}·t^σ': each factor t_k of t^σ' in turn is replaced by k·C(−k−1,
n−1)·u^{−k−n}, or ·v^{−k−n}. -/
theorem pderiv_Phi_ket (rd : Bool) (i : X) (σ' : Multiset ℕ) :
    MvPowerSeries.pderiv Tv i (Phi rd (ket rd σ')) =
      ∑ k ∈ σ'.toFinset, σ'.count k • (embW (MvPowerSeries.C ((k : ℚ) • cS rd i (-(k : ℤ)))) * Phi rd (ket rd (σ'.erase k))) := by
  unfold ket
  rw [Phi, pderiv_expD_prod (Y := X) (A := Tv) (D := DD rd) (g := fun k : ℕ => embW (MvPowerSeries.C ((k : ℚ) • cS rd i (-(k : ℤ)))))]
  · exact DD_comm rd
  · exact der_factor rd i
  · intro k
    rw [← Phi, Phi_embW]

/-! ### The left side: e^{A⁺}·e^{B⁺}, and the equation -/

/-- The coefficient of t^σ in (the series beside x_i in A⁺ + B⁺)·w: each factor t_l of t^σ in turn
is taken away, with the coefficient C(l−1, n−1)·u^{l−n}, or ·v^{l−n}. -/
theorem braW_C_sel_mul (rd : Bool) {E : ℕ} {σ : Multiset ℕ} (hσ : σ.sum ≤ E) (i : X) (w : W) :
    braW σ (MvPowerSeries.C (sel rd (fun n => HahnSeries.C (JpU E n)) JpV i) * w) = ∑ l ∈ σ.toFinset, MvPowerSeries.C (cS rd i (l : ℤ)) * braW (σ.erase l) w := by
  rcases xi_or_xo rd i with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · by_cases hn : n = 0
    · subst hn
      simp only [cS, sel_xi_zero]
      simp [braW_zero]
    · simp only [cS, sel_xi rd _ _ (show 1 ≤ n by omega)]
      exact braW_C_JpU_mul hσ n w
  · by_cases hn : n = 0
    · subst hn
      simp only [cS, sel_xo_zero]
      simp [braW_zero]
    · simp only [cS, sel_xo rd _ _ (show 1 ≤ n by omega)]
      exact braW_C_JpV_mul σ n w

/-- The differential equation of ⟨𝒩⟩ in every variable x_i, for |σ| ≤ E: one term for every
different part l of σ, from A⁺ or B⁺, and one for every different part k of σ', from A⁻ or B⁻. -/
theorem pderiv_normal (rd : Bool) {E : ℕ} {σ : Multiset ℕ} (hσ : σ.sum ≤ E) (σ' : Multiset ℕ) (i : X) :
    MvPowerSeries.pderiv S i (normal rd E σ σ') =
      ∑ l ∈ σ.toFinset, MvPowerSeries.C (cS rd i (l : ℤ)) * normal rd E (σ.erase l) σ' +
        ∑ k ∈ σ'.toFinset, MvPowerSeries.C (((k : ℚ) * σ'.count k) • cS rd i (-(k : ℤ))) * normal rd E σ (σ'.erase k) := by
  have hp : MvPowerSeries.pderiv Tv i (Ap rd E) + MvPowerSeries.pderiv Tv i (Bp rd) = MvPowerSeries.C (sel rd (fun n => HahnSeries.C (JpU E n)) JpV i) := by
    rw [Ap, Bp, pderiv_lin (X := X) (A := Tv), pderiv_lin (X := X) (A := Tv), ← map_add, Normal.sel_add]
  rw [normal, pderiv_braW, pderiv_three (Y := X) (A := Tv) i (by rw [Ap, constantCoeff_lin (X := X) (A := Tv)]) (by rw [Bp, constantCoeff_lin (X := X) (A := Tv)]), hp,
    pderiv_Phi_ket, braW_add, braW_C_sel_mul rd hσ, Finset.mul_sum, Finset.mul_sum, braW_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, mul_smul_comm, ← Nat.cast_smul_eq_nsmul ℚ, braW_smul, mul_left_comm (expW (Bp rd)), mul_left_comm (expW (Ap rd E)), braW_embW_mul,
    mul_comm (k : ℚ), ← smul_smul, Normal.C_rat_smul (Y := X) (A := S) (σ'.count k : ℚ), smul_mul_assoc, normal]

/-- The differential equation of ⟨𝒩⟩, as the statement from which the coefficients of ⟨𝒩⟩ are read
off. -/
theorem stNeq : StNeq := fun rd _ _ σ' i h => pderiv_normal rd h σ' i

end GeneralPieces.GenF
