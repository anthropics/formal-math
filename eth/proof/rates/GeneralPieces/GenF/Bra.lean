/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.GenF.Defs
public import GeneralPieces.GenF.Coeff

/-! # The lemma on the operators Q_s, paragraph "Generating functions": elementary rules

Rules for the definitions of `Defs.lean` that the other files of this paragraph use: the two
families of variables (`sel`, `xi`, `xo`), linear and bilinear forms in the variables (`lin`,
`bil`), and
the coefficient of t^σ (`bra` on the series in v, `braW` on the power series in the x_n, x'_n). The
main rule is `bra_lin_mul`: if every coefficient of g is a linear form in the t_l, the coefficient
of t^σ
in g·f is the sum over the different parts l of σ of the coefficient of t_l in g times the
coefficient of t^{σ − l} in f. It is applied to t_k, to J_n^+(v) and to the part of J_n^+(u) with l
≤ E.
Nothing here is a sentence of the paper. -/

public section

namespace GeneralPieces.GenF

open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial

/-! ### The two families of variables -/

section Sel
variable {R : Type} [Zero R]

theorem sel_xi (rd : Bool) (f g : ℕ → R) {n : ℕ} (hn : 1 ≤ n) : sel rd f g (xi rd n) = f n := by
  have h : n ≠ 0 := by omega
  cases rd <;> simp [sel, xi, z0, h]

theorem sel_xo (rd : Bool) (f g : ℕ → R) {n : ℕ} (hn : 1 ≤ n) : sel rd f g (xo rd n) = g n := by
  have h : n ≠ 0 := by omega
  cases rd <;> simp [sel, xo, z0, h]

theorem sel_xi_zero (rd : Bool) (f g : ℕ → R) : sel rd f g (xi rd 0) = 0 := by
  cases rd <;> simp [sel, xi, z0]

theorem sel_xo_zero (rd : Bool) (f g : ℕ → R) : sel rd f g (xo rd 0) = 0 := by
  cases rd <;> simp [sel, xo, z0]

/-- On the inner family, with the value 0 at the index 0. -/
theorem sel_xi' (rd : Bool) (f g : ℕ → R) (n : ℕ) : sel rd f g (xi rd n) = z0 f n := by
  cases rd <;> simp [sel, xi]

/-- On the outer family, with the value 0 at the index 0. -/
theorem sel_xo' (rd : Bool) (f g : ℕ → R) (n : ℕ) : sel rd f g (xo rd n) = z0 g n := by
  cases rd <;> simp [sel, xo]

theorem sel_zero_xi (rd : Bool) (g : ℕ → R) (n : ℕ) : sel rd 0 g (xi rd n) = 0 := by
  rw [sel_xi']
  simp [z0]

end Sel

/-- Every variable belongs to the inner or to the outer family. -/
theorem xi_or_xo (rd : Bool) (x : X) : (∃ n, x = xi rd n) ∨ ∃ n, x = xo rd n := by
  cases rd <;> rcases x with n | n <;> simp [xi, xo]

/-- A map φ with φ 0 = 0 may be applied to the values. -/
theorem map_sel {R R' : Type} [Zero R] [Zero R'] (φ : R → R') (h0 : φ 0 = 0) (rd : Bool) (f g : ℕ → R) (x : X) :
    φ (sel rd f g x) = sel rd (fun n => φ (f n)) (fun n => φ (g n)) x := by
  cases rd <;> rcases x with n | n <;> by_cases hn : n = 0 <;> simp [sel, z0, hn, h0]

/-! ### Linear forms in the variables -/

section Lin
variable {Y A : Type} [CommRing A]

theorem map_lin {A' : Type} [CommRing A'] (φ : A →+* A') (c : Y → A) : MvPowerSeries.map φ (lin c) = lin fun i => φ (c i) := by
  ext α
  rw [MvPowerSeries.coeff_map, coeff_lin, coeff_lin]
  split_ifs
  · rw [map_sum]
  · rw [map_zero]

end Lin

section Bil
variable {R : Type}

/-! ### Bilinear forms in the variables -/

theorem coeff_bil [Semiring R] (q : X → X → R) (α : X →₀ ℕ) :
    MvPowerSeries.coeff α (bil q) = if α.degree = 2 then ∑ i ∈ α.support, ∑ i' ∈ α.support, q i i' else 0 := rfl

theorem coeff_bil_of_degree_ne [Semiring R] (q : X → X → R) {α : X →₀ ℕ} (h : α.degree ≠ 2) : MvPowerSeries.coeff α (bil q) = 0 := by
  rw [coeff_bil, if_neg h]

theorem constantCoeff_bil [Semiring R] (q : X → X → R) : MvPowerSeries.constantCoeff (bil q) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_bil_of_degree_ne q (by simp)

end Bil

/-! ### The coefficient of t^σ in a series in v -/

theorem coeff_bra (σ : Multiset ℕ) (f : Tv) (y : ℤ) : (bra σ f).coeff y = MvPolynomial.coeff (Multiset.toFinsupp σ) (f.coeff y) := rfl

theorem coeff_emb (s : S) (y : ℤ) : (emb s).coeff y = MvPolynomial.C (s.coeff y) := rfl

theorem support_bra (σ : Multiset ℕ) (f : Tv) : (bra σ f).support ⊆ f.support := fun y hy h => hy (by rw [coeff_bra, h, MvPolynomial.coeff_zero])

theorem support_emb (s : S) : (emb s).support ⊆ s.support := fun y hy h => hy (by rw [coeff_emb, h, map_zero])

theorem bra_zero (σ : Multiset ℕ) : bra σ 0 = 0 := by
  ext y : 2
  rw [coeff_bra, HahnSeries.coeff_zero, HahnSeries.coeff_zero, MvPolynomial.coeff_zero]

theorem bra_add (σ : Multiset ℕ) (f g : Tv) : bra σ (f + g) = bra σ f + bra σ g := by
  ext y : 2
  rw [HahnSeries.coeff_add, coeff_bra, coeff_bra, coeff_bra, HahnSeries.coeff_add, MvPolynomial.coeff_add]

/-- `bra σ` as an additive map. -/
@[expose] noncomputable def braH (σ : Multiset ℕ) : Tv →+ S where
  toFun := bra σ
  map_zero' := bra_zero σ
  map_add' := bra_add σ

theorem bra_sum {ι : Type} (σ : Multiset ℕ) (s : Finset ι) (F : ι → Tv) : bra σ (∑ i ∈ s, F i) = ∑ i ∈ s, bra σ (F i) := map_sum (braH σ) F s

/-- The coefficients of a product, as a sum over any two sets that contain the supports. -/
theorem coeff_mul_big {R : Type} [CommRing R] (f g : HahnSeries ℤ R) {A B : Set ℤ} (hA : A.IsPWO) (hB : B.IsPWO) (hf : f.support ⊆ A) (hg : g.support ⊆ B) (y : ℤ) :
    (f * g).coeff y = ∑ ij ∈ Finset.antidiagonal hA hB y, f.coeff ij.1 * g.coeff ij.2 := by
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_subset (fun ij h => ?_) fun ij h hn => ?_
  · rw [Finset.mem_antidiagonal] at h ⊢
    exact ⟨hf h.1, hg h.2.1, h.2.2⟩
  · by_contra hne
    refine hn ?_
    rw [Finset.mem_antidiagonal]
    exact ⟨left_ne_zero_of_mul hne, right_ne_zero_of_mul hne, (Finset.mem_antidiagonal.1 h).2.2⟩

/-- Series without the t_k may be taken out. -/
theorem bra_emb_mul (σ : Multiset ℕ) (s : S) (f : Tv) : bra σ (emb s * f) = s * bra σ f := by
  ext y : 2
  rw [coeff_bra, coeff_mul_big (emb s) f s.isPWO_support f.isPWO_support (support_emb s) subset_rfl,
    coeff_mul_big s (bra σ f) s.isPWO_support f.isPWO_support subset_rfl (support_bra σ f), MvPolynomial.coeff_sum]
  exact Finset.sum_congr rfl fun ij _ => by rw [coeff_emb, MvPolynomial.coeff_C_mul, coeff_bra]

theorem bra_emb (σ : Multiset ℕ) (s : S) : bra σ (emb s) = if σ = 0 then s else 0 := by
  classical
  ext y : 2
  rw [coeff_bra, coeff_emb, MvPolynomial.coeff_C]
  by_cases h : σ = 0
  · rw [if_pos h, h, map_zero, if_pos rfl]
  · rw [if_neg h, if_neg, HahnSeries.coeff_zero]
    intro h0
    exact h (Multiset.toFinsupp.injective (by rw [← h0, map_zero]))

theorem bra_one (σ : Multiset ℕ) : bra σ 1 = if σ = 0 then 1 else 0 := by
  rw [← map_one emb, bra_emb]

theorem toFinsupp_erase (σ : Multiset ℕ) (l : ℕ) : Multiset.toFinsupp (σ.erase l) = Multiset.toFinsupp σ - Finsupp.single l 1 := by
  ext x
  rw [Finsupp.coe_tsub, Pi.sub_apply, Multiset.toFinsupp_apply, Multiset.toFinsupp_apply]
  by_cases h : x = l
  · subst h
    rw [Multiset.count_erase_self, Finsupp.single_eq_same]
  · rw [Multiset.count_erase_of_ne h, Finsupp.single_eq_of_ne h, Nat.sub_zero]

/-- An exponent of degree 1 is that of a variable. -/
theorem eq_single_of_degree {Y : Type} {m : Y →₀ ℕ} (h : m.degree = 1) : ∃ l, m = Finsupp.single l 1 := by
  have hm : m ≠ 0 := fun h0 => by rw [h0, map_zero] at h; exact absurd h (by norm_num)
  obtain ⟨l, hl⟩ := Finsupp.support_nonempty_iff.2 hm
  have h1 := degree_sub_single hl
  have h2 : m - Finsupp.single l 1 = 0 := (Finsupp.degree_eq_zero_iff _).1 (by omega)
  refine ⟨l, ?_⟩
  have h3 := sub_single_add hl
  rw [h2, zero_add] at h3
  exact h3.symm

/-- The coefficients of p·q for a linear form p in the t_l. -/
theorem coeff_linear_mul {p : Vu} (hp : ∀ m, MvPolynomial.coeff m p ≠ 0 → m.degree = 1) (q : Vu) (m : ℕ →₀ ℕ) :
    MvPolynomial.coeff m (p * q) = ∑ l ∈ m.support, MvPolynomial.coeff (Finsupp.single l 1) p * MvPolynomial.coeff (m - Finsupp.single l 1) q := by
  classical
  rw [MvPolynomial.coeff_mul]
  have hinj : Set.InjOn (fun l : ℕ => ((Finsupp.single l 1 : ℕ →₀ ℕ), m - Finsupp.single l 1)) m.support := fun a _ b _ hab => by
    have := congrArg Prod.fst hab
    exact (Finsupp.single_left_injective one_ne_zero) this
  rw [← Finset.sum_image (f := fun x : (ℕ →₀ ℕ) × (ℕ →₀ ℕ) => MvPolynomial.coeff x.1 p * MvPolynomial.coeff x.2 q) hinj]
  symm
  refine Finset.sum_subset (fun x hx => ?_) fun x hx hn => ?_
  · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal, add_comm]
    exact sub_single_add hl
  · by_contra hne
    obtain ⟨l, hl⟩ := eq_single_of_degree (hp x.1 (left_ne_zero_of_mul hne))
    have hsum : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    refine hn (Finset.mem_image.2 ⟨l, ?_, ?_⟩)
    · rw [Finsupp.mem_support_iff, ← hsum, hl]
      simp
    · refine Prod.ext hl.symm ?_
      rw [← hsum, hl]
      simp

/-- Every coefficient of g is a linear form in the t_l. -/
@[expose] def Lin1 (g : Tv) : Prop := ∀ (y : ℤ) (m : ℕ →₀ ℕ), MvPolynomial.coeff m (g.coeff y) ≠ 0 → m.degree = 1

/-- If every coefficient of g is a linear form in the t_l, the coefficient of t^σ in g·f is the sum
over the different parts l of σ of the coefficient of t_l in g times the coefficient of
t^{σ − l} in f. -/
theorem bra_lin_mul {g : Tv} (hg : Lin1 g) (σ : Multiset ℕ) (f : Tv) : bra σ (g * f) = ∑ l ∈ σ.toFinset, bra {l} g * bra (σ.erase l) f := by
  ext y : 2
  rw [coeff_bra, HahnSeries.coeff_mul, MvPolynomial.coeff_sum, HahnSeries.coeff_sum]
  simp only [coeff_mul_big _ _ g.isPWO_support f.isPWO_support (support_bra _ g) (support_bra _ f), coeff_linear_mul (hg _), Multiset.toFinsupp_support]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun ij _ => ?_
  rw [coeff_bra, coeff_bra, Multiset.toFinsupp_singleton, toFinsupp_erase]

/-! ### The three linear forms: t_k, J_n^+(v), and the part of J_n^+(u) with l ≤ E -/

theorem coeff_single_X (l k : ℕ) : MvPolynomial.coeff (Finsupp.single l 1) (MvPolynomial.X k : Vu) = if l = k then 1 else 0 := by
  classical
  rw [MvPolynomial.coeff_X]
  by_cases h : l = k
  · rw [if_pos h, h, if_pos rfl]
  · rw [if_neg h, if_neg fun e => h (Finsupp.single_left_injective one_ne_zero e).symm]

/-- c·t_k is a linear form. -/
theorem degree_of_coeff_C_mul_X {c : Lu} {k : ℕ} {m : ℕ →₀ ℕ} (h : MvPolynomial.coeff m (MvPolynomial.C c * MvPolynomial.X k : Vu) ≠ 0) : m.degree = 1 := by
  classical
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X] at h
  by_cases e : Finsupp.single k 1 = m
  · rw [← e, Finsupp.degree_single]
  · rw [if_neg e, mul_zero] at h
    exact absurd rfl h

theorem lin1_tT (k : ℕ) : Lin1 (tT k) := fun y m h => by
  unfold tT at h
  rw [HahnSeries.C_apply, HahnSeries.coeff_single] at h
  split_ifs at h
  · refine degree_of_coeff_C_mul_X (c := 1) (k := k) ?_
    rwa [map_one, one_mul]
  · exact absurd (MvPolynomial.coeff_zero m) h

theorem bra_single_tT (l k : ℕ) : bra {l} (tT k) = if l = k then 1 else 0 := by
  ext y : 2
  unfold tT
  rw [coeff_bra, HahnSeries.C_apply, HahnSeries.coeff_single, Multiset.toFinsupp_singleton]
  by_cases hy : y = 0
  · rw [if_pos hy, coeff_single_X, hy]
    split_ifs <;> simp
  · rw [if_neg hy, MvPolynomial.coeff_zero]
    split_ifs
    · rw [HahnSeries.coeff_one, if_neg hy]
    · rfl

/-- The coefficient of t^σ in t_k·f. -/
theorem bra_tT_mul (σ : Multiset ℕ) (k : ℕ) (f : Tv) : bra σ (tT k * f) = if k ∈ σ then bra (σ.erase k) f else 0 := by
  rw [bra_lin_mul (lin1_tT k)]
  simp only [bra_single_tT, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Multiset.mem_toFinset]

/-- C(l−1, n−1) = 0 for l < n. -/
theorem bet_eq_zero_of_lt {n l : ℕ} (h : l < n) : bet n (l : ℤ) = 0 := by
  unfold bet
  split_ifs with h0
  · rfl
  · exact ClauseBound.Boson.Scalars.choose_eq_zero (by omega) (by omega)

theorem coeff_JpV (n : ℕ) (y : ℤ) : (JpV n).coeff y = if 0 ≤ y then MvPolynomial.C (C (bet n (y + n) : ℚ)) * MvPolynomial.X (y + n).toNat else 0 := rfl

theorem lin1_JpV (n : ℕ) : Lin1 (JpV n) := fun y m h => by
  rw [coeff_JpV] at h
  split_ifs at h
  · exact degree_of_coeff_C_mul_X h
  · exact absurd (MvPolynomial.coeff_zero m) h

/-- q·u^x·v^y, coefficient by coefficient in v. -/
theorem coeff_smul_mo (q : ℚ) (x y y' : ℤ) : (q • mo x y).coeff y' = if y' = y then C q * T x else 0 := by
  unfold mo
  rw [HahnSeries.coeff_smul, HahnSeries.coeff_single]
  split_ifs
  · rw [← LaurentPolynomial.smul_eq_C_mul]
  · rw [smul_zero]

/-- The coefficient of t_l in J_n^+(v) is C(l−1, n−1)·v^{l−n}. -/
theorem bra_single_JpV (l n : ℕ) : bra {l} (JpV n) = (bet n l : ℚ) • mo 0 ((l : ℤ) - n) := by
  ext y : 2
  rw [coeff_bra, coeff_JpV, coeff_smul_mo, Multiset.toFinsupp_singleton, T_zero, mul_one]
  by_cases hy : 0 ≤ y
  · rw [if_pos hy, MvPolynomial.coeff_C_mul, coeff_single_X]
    by_cases e : l = (y + n).toNat
    · rw [if_pos e, if_pos (by omega), mul_one, show y + (n : ℤ) = (l : ℤ) by omega]
    · rw [if_neg e, if_neg (by omega), mul_zero]
  · rw [if_neg hy, MvPolynomial.coeff_zero]
    split_ifs with e
    · rw [bet_eq_zero_of_lt (by omega)]
      simp
    · rfl

/-- The coefficient of t^σ in J_n^+(v)·f. -/
theorem bra_JpV_mul (σ : Multiset ℕ) (n : ℕ) (f : Tv) :
    bra σ (JpV n * f) = ∑ l ∈ σ.toFinset, ((bet n l : ℚ) • mo 0 ((l : ℤ) - n)) * bra (σ.erase l) f := by
  rw [bra_lin_mul (lin1_JpV n)]
  simp only [bra_single_JpV]

theorem lin1_JpU (E n : ℕ) : Lin1 (HahnSeries.C (JpU E n)) := fun y m h => by
  rw [HahnSeries.C_apply, HahnSeries.coeff_single] at h
  split_ifs at h
  · unfold JpU at h
    rw [MvPolynomial.coeff_sum] at h
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact degree_of_coeff_C_mul_X hl
  · exact absurd (MvPolynomial.coeff_zero m) h

/-- The coefficient of t_l in the part of J_n^+(u) with l ≤ E is C(l−1, n−1)·u^{l−n} for l ≤ E. -/
theorem bra_single_JpU {E l : ℕ} (hl : l ≤ E) (n : ℕ) : bra {l} (HahnSeries.C (JpU E n)) = (bet n l : ℚ) • mo ((l : ℤ) - n) 0 := by
  ext y : 2
  rw [coeff_bra, HahnSeries.C_apply, HahnSeries.coeff_single, coeff_smul_mo, Multiset.toFinsupp_singleton]
  by_cases hy : y = 0
  · rw [if_pos hy, if_pos hy]
    unfold JpU
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_C_mul, coeff_single_X, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · rfl
    · have h0 : l = 0 := by
        by_contra hne
        exact hm (Finset.mem_Icc.2 ⟨by omega, hl⟩)
      rw [h0]
      simp [bet]
  · rw [if_neg hy, if_neg hy, MvPolynomial.coeff_zero]

/-- The coefficient of t^σ in the monomial t^σ'. -/
theorem bra_prod_tT (σ σ' : Multiset ℕ) : bra σ ((σ'.map tT).prod) = if σ = σ' then 1 else 0 := by
  induction σ' using Multiset.induction_on generalizing σ with
  | empty => rw [Multiset.map_zero, Multiset.prod_zero, bra_one]
  | cons k σ' ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, bra_tT_mul]
    by_cases hk : k ∈ σ
    · rw [if_pos hk, ih]
      by_cases e : σ.erase k = σ'
      · rw [if_pos e, if_pos (by rw [← e, Multiset.cons_erase hk])]
      · rw [if_neg e, if_neg fun e' => e (by rw [e', Multiset.erase_cons_head])]
    · rw [if_neg hk, if_neg fun e' => hk (by rw [e']; exact Multiset.mem_cons_self k σ')]

/-! ### The coefficient of t^σ in a power series in the x_n, x'_n -/

theorem coeff_braW (σ : Multiset ℕ) (w : W) (α : X →₀ ℕ) : MvPowerSeries.coeff α (braW σ w) = bra σ (MvPowerSeries.coeff α w) := rfl

theorem constantCoeff_braW (σ : Multiset ℕ) (w : W) : MvPowerSeries.constantCoeff (braW σ w) = bra σ (MvPowerSeries.constantCoeff w) := rfl

theorem braW_zero (σ : Multiset ℕ) : braW σ 0 = 0 := by
  ext α : 1
  rw [coeff_braW, map_zero, map_zero, bra_zero]

theorem braW_add (σ : Multiset ℕ) (w w' : W) : braW σ (w + w') = braW σ w + braW σ w' := by
  ext α : 1
  rw [coeff_braW, map_add, map_add, bra_add, coeff_braW, coeff_braW]

/-- `braW σ` as an additive map. -/
@[expose] noncomputable def braWH (σ : Multiset ℕ) : W →+ PS where
  toFun := braW σ
  map_zero' := braW_zero σ
  map_add' := braW_add σ

theorem braW_sum {ι : Type} (σ : Multiset ℕ) (s : Finset ι) (F : ι → W) : braW σ (∑ i ∈ s, F i) = ∑ i ∈ s, braW σ (F i) := map_sum (braWH σ) F s

theorem braW_smul (σ : Multiset ℕ) (q : ℚ) (w : W) : braW σ (q • w) = q • braW σ w := map_rat_smul (braWH σ) q w

/-- Power series without the t_k may be taken out. -/
theorem braW_embW_mul (σ : Multiset ℕ) (e : PS) (w : W) : braW σ (embW e * w) = e * braW σ w := by
  classical
  ext α : 1
  rw [coeff_braW, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, bra_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [embW, MvPowerSeries.coeff_map, bra_emb_mul, coeff_braW]

/-- Taking the coefficient of t^σ commutes with ∂/∂x_i. -/
theorem pderiv_braW (σ : Multiset ℕ) (i : X) (w : W) : MvPowerSeries.pderiv S i (braW σ w) = braW σ (MvPowerSeries.pderiv Tv i w) := by
  ext α : 1
  rw [MvPowerSeries.coeff_pderiv, coeff_braW, coeff_braW, MvPowerSeries.coeff_pderiv]
  have e : ((α i : Tv) + 1) = emb ((α i : S) + 1) := by rw [map_add, map_natCast, map_one]
  rw [e, mul_comm _ (emb _), bra_emb_mul, mul_comm]

/-- The rule `bra_lin_mul` for power series. -/
theorem braW_C_lin_mul {g : Tv} (hg : Lin1 g) (σ : Multiset ℕ) (w : W) :
    braW σ (MvPowerSeries.C g * w) = ∑ l ∈ σ.toFinset, MvPowerSeries.C (bra {l} g) * braW (σ.erase l) w := by
  ext α : 1
  rw [coeff_braW, MvPowerSeries.coeff_C_mul, bra_lin_mul hg, map_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [MvPowerSeries.coeff_C_mul, coeff_braW]

theorem braW_C_JpV_mul (σ : Multiset ℕ) (n : ℕ) (w : W) :
    braW σ (MvPowerSeries.C (JpV n) * w) = ∑ l ∈ σ.toFinset, MvPowerSeries.C ((bet n l : ℚ) • mo 0 ((l : ℤ) - n)) * braW (σ.erase l) w := by
  rw [braW_C_lin_mul (lin1_JpV n)]
  simp only [bra_single_JpV]

theorem braW_C_JpU_mul {σ : Multiset ℕ} {E : ℕ} (h : σ.sum ≤ E) (n : ℕ) (w : W) :
    braW σ (MvPowerSeries.C (HahnSeries.C (JpU E n)) * w) = ∑ l ∈ σ.toFinset, MvPowerSeries.C ((bet n l : ℚ) • mo ((l : ℤ) - n) 0) * braW (σ.erase l) w := by
  rw [braW_C_lin_mul (lin1_JpU E n)]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [bra_single_JpU ((Multiset.single_le_sum (fun _ _ => Nat.zero_le _) l (Multiset.mem_toFinset.1 hl)).trans h)]

end GeneralPieces.GenF
