/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Ring.LemmaQ

/-! # The pieces with ρ = 1/√2: the steps of the proof that are statements about the ring

`GeneralPieces.pieceFacts` derives `AppHalfPieces.PieceFacts`, field by field along the sentences of
the proof of the theorem on the pieces (Appendix B), from the lemma on the operators Q_s and the
lemma on the dual
families: a^μ is a combination of monomials of weight at most h; Σ_s A_s = h!·[x = v]·[y = u]; the
displays (54) and (55), by expanding a^⟨i⟩[s−h+i]t^{μ(y)} ∈ V_{s+i} (after the factors have been
exchanged) and b[h−s−i]t^{μ(y)} ∈ V_{2h−s−i} in monomials; all factors are integers by (O1); both
numbers of terms are at least 1.
The two lemmas (`GeneralPieces.lemmaQ`, `GeneralPieces.Dual.lemmaDual`), the facts on a[r] that come
with display (47) (`GeneralPieces.opFacts`), the property (O1) (`GeneralPieces.o1`) and the fact
that h!/z_μ is an integer
(`GeneralPieces.Dual.zDvd`) are hypotheses; `proof/rates/GeneralPieces/Main.lean` feeds them in.
Claim (b) of the lemma on the Q_s, which the paper quotes
for the sum, is not needed there: the index set {−2h, …, 2h} is exactly the range |s| ≤ E + h of
claim (c) for E = h. -/

public section

namespace GeneralPieces.Pcs

open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ

/-! ### Combinations of monomials of weight at most h -/

/-- Every monomial of a has weight at most h. -/
@[expose] def Le (h : ℕ) (a : V) : Prop := ∀ π, coef π a ≠ 0 → wt π ≤ h

theorem wtLe_of_le {h : ℕ} {a : V} (ha : Le h a) : WtLe h a := by
  unfold WtLe
  refine ext_coef fun π => ?_
  rw [coef_sum]
  simp only [coef_part]
  rw [sum_ite_eq]
  split_ifs with hm
  · rfl
  · by_contra hne
    exact hm (mem_range.2 (by have := ha π hne; omega))

theorem Le.add {h : ℕ} {a a' : V} (ha : Le h a) (ha' : Le h a') : Le h (a + a') := fun π hπ => by
  by_cases h1 : coef π a = 0
  · exact ha' π (by rwa [coef_add, h1, zero_add] at hπ)
  · exact ha π h1

theorem Le.smul {h : ℕ} {a : V} (ha : Le h a) (q : ℚ) : Le h (q • a) := fun π hπ => ha π (by rw [coef_smul] at hπ; exact right_ne_zero_of_mul hπ)

theorem Le.zero (h : ℕ) : Le h 0 := fun π hπ => absurd (coef_zero π) hπ

theorem Le.sum {ι : Type} {h : ℕ} (s : Finset ι) {F : ι → V} (hF : ∀ i ∈ s, Le h (F i)) : Le h (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Le.zero h
  | insert x s hx ih =>
    rw [sum_insert hx]
    exact (hF x (mem_insert_self _ _)).add (ih fun i hi => hF i (mem_insert_of_mem hi))

theorem le_tpow {h : ℕ} {μ : Ptn} (hμ : wt μ ≤ h) : Le h (tpow μ) := fun π hπ => by
  rw [coef_tpow] at hπ
  by_cases e : π = μ
  · rw [e]; exact hμ
  · rw [if_neg e] at hπ; exact absurd rfl hπ

theorem tpow_mul (μ ν : Ptn) : tpow μ * tpow ν = tpow (μ + ν) := by
  unfold tpow
  rw [monomial_mul, map_add, one_mul]

theorem wt_add (μ ν : Ptn) : wt (μ + ν) = wt μ + wt ν := by
  unfold wt
  rw [Multiset.map_add, Multiset.sum_add]

theorem Le.mul {h h' : ℕ} {a a' : V} (ha : Le h a) (ha' : Le h' a') : Le (h + h') (a * a') := by
  rw [eq_sum_of_subset a (ptnsLe h) fun μ hμ => (mem_ptnsLe h μ).2 (ha μ hμ), eq_sum_of_subset a' (ptnsLe h') fun μ hμ => (mem_ptnsLe h' μ).2 (ha' μ hμ), sum_mul_sum]
  refine Le.sum _ fun μ hμ => Le.sum _ fun ν hν => ?_
  rw [smul_mul_smul_comm, tpow_mul]
  refine (le_tpow ?_).smul _
  rw [wt_add]
  exact Nat.add_le_add ((mem_ptnsLe h μ).1 hμ) ((mem_ptnsLe h' ν).1 hν)

theorem X_eq_tpow (k : ℕ+) : (X k : V) = tpow {k} := by
  unfold tpow
  rw [Multiset.toFinsupp_singleton]
  rfl

theorem one_eq_tpow : (1 : V) = tpow 0 := by
  unfold tpow
  rw [map_zero]
  rfl

theorem wt_singleton (k : ℕ+) : wt {k} = k := by simp [wt]

theorem wt_cons (n : ℕ+) (μ : Ptn) : wt (n ::ₘ μ) = n + wt μ := by simp [wt]

/-- Every monomial of y_n has weight at most n. -/
theorem le_y (n : ℕ+) : Le n (y n) := by
  unfold y
  refine Le.sum _ fun j hj => Le.smul ?_ _
  rw [X_eq_tpow]
  refine le_tpow ?_
  rw [wt_singleton, PNat.toPNat'_coe (by have := (mem_Icc.1 hj).1; omega)]
  exact (mem_Icc.1 hj).2

theorem aFam_zero : aFam 0 = 1 := by simp [aFam]

theorem aFam_cons (n : ℕ+) (μ : Ptn) : aFam (n ::ₘ μ) = ((-1 : ℚ) ^ ((n : ℕ) - 1) • y n) * aFam μ := by
  unfold aFam
  rw [Multiset.map_cons, Multiset.prod_cons]

/-- "Here a^μ is a combination of monomials of weight at most h." -/
theorem le_aFam (μ : Ptn) : Le (wt μ) (aFam μ) := by
  induction μ using Multiset.induction_on with
  | empty =>
    rw [aFam_zero, one_eq_tpow]
    exact le_tpow le_rfl
  | cons n μ ih =>
    rw [aFam_cons, wt_cons]
    exact ((le_y n).smul _).mul ih

/-! ### Polynomials with integer coefficients -/

theorem isInt_add {f g : V} (hf : IsInt f) (hg : IsInt g) : IsInt (f + g) := fun m => by
  obtain ⟨z, hz⟩ := hf m
  obtain ⟨w, hw⟩ := hg m
  exact ⟨z + w, by rw [coeff_add, hz, hw]; push_cast; rfl⟩

theorem isInt_zero : IsInt (0 : V) := fun m => ⟨0, by simp⟩

theorem isInt_sum {ι : Type} (s : Finset ι) {F : ι → V} (hF : ∀ i ∈ s, IsInt (F i)) : IsInt (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact isInt_zero
  | insert x s hx ih =>
    rw [sum_insert hx]
    exact isInt_add (hF x (mem_insert_self _ _)) (ih fun i hi => hF i (mem_insert_of_mem hi))

theorem isInt_smul {f : V} (hf : IsInt f) (z : ℤ) : IsInt ((z : ℚ) • f) := fun m => by
  obtain ⟨w, hw⟩ := hf m
  exact ⟨z * w, by rw [coeff_smul, hw, smul_eq_mul]; push_cast; rfl⟩

theorem isInt_mul {f g : V} (hf : IsInt f) (hg : IsInt g) : IsInt (f * g) := fun m => by
  classical
  choose zf hzf using hf
  choose zg hzg using hg
  refine ⟨∑ x ∈ antidiagonal m, zf x.1 * zg x.2, ?_⟩
  rw [coeff_mul]
  push_cast
  exact sum_congr rfl fun x _ => by rw [hzf, hzg]

theorem isInt_tpow (μ : Ptn) : IsInt (tpow μ) := fun m => by
  classical
  unfold tpow
  rw [coeff_monomial]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

theorem isInt_y (n : ℕ+) : IsInt (y n) := by
  unfold y
  refine isInt_sum _ fun j _ => ?_
  have := isInt_smul (isInt_tpow {j.toPNat'}) ((n : ℕ).choose j : ℤ)
  rwa [Int.cast_natCast, ← X_eq_tpow] at this

theorem isInt_aFam (μ : Ptn) : IsInt (aFam μ) := by
  induction μ using Multiset.induction_on with
  | empty =>
    rw [aFam_zero, one_eq_tpow]
    exact isInt_tpow 0
  | cons n μ ih =>
    rw [aFam_cons]
    have := isInt_smul (isInt_y n) ((-1) ^ ((n : ℕ) - 1))
    push_cast at this
    exact isInt_mul this ih

theorem isInt_part {a : V} (ha : IsInt a) (h' : ℕ) : IsInt (part h' a) := fun m => by
  classical
  unfold part
  rw [coeff_weightedHomogeneousComponent]
  split_ifs
  · exact ha m
  · exact ⟨0, by simp⟩

theorem isInt_angle {a : V} (ha : IsInt a) (h i : ℕ) : IsInt (angle h i a) := by
  unfold angle
  refine isInt_sum _ fun h' _ => ?_
  have := isInt_smul (isInt_part ha h') ((h' + h).choose i : ℤ)
  rwa [Int.cast_natCast] at this

/-- b^ν has integer coefficients, because h!/z_ν is an integer. -/
theorem isInt_bFam (hZ : ZDvd) (ν : Ptn) : IsInt (bFam ν) := by
  unfold bFam
  have h0 : (zz ν : ℚ) ≠ 0 := by
    have : zz ν ≠ 0 := by
      unfold zz
      exact Finset.prod_ne_zero_iff.2 fun k _ => Nat.mul_ne_zero (pow_ne_zero _ k.pos.ne') (Nat.factorial_ne_zero _)
    exact_mod_cast this
  have := isInt_smul (isInt_tpow ν) (((wt ν).factorial / zz ν : ℕ) : ℤ)
  rwa [Int.cast_natCast, Nat.cast_div (hZ ν) h0] at this

/-! ### Expanding in monomials -/

theorem bFam_mem (ν : Ptn) : bFam ν ∈ VE (wt ν : ℤ) := Submodule.smul_mem _ _ (tpow_mem_VE ν)

/-- "Expanding these polynomials in monomials t^σ": if f ∈ V_E, then b[r']f ∈ V_{E+r'} by (O1), and
the coefficient of t^π in a[r]b[r']f is the sum over |σ| = E + r' of the coefficient of t^π in
a[r]t^σ times the coefficient of t^σ in b[r']f. -/
theorem coef_comp_gen (hOp : OpFacts) (h1 : O1) (a b : V) (r r' : ℤ) {E : ℤ} {f : V} (hf : f ∈ VE E) (π : Ptn) :
    coef π (op a r (op b r' f)) = ∑ σ ∈ ptnsZ (E + r'), coef π (op a r (tpow σ)) * coef σ (op b r' f) := by
  have hg := h1.maps b r' E f hf
  conv_lhs => rw [eq_sum_ptnsZ hg, op_sum_right hOp, coef_sum]
  exact sum_congr rfl fun σ _ => by rw [coef_smul, mul_comm]

theorem one_le_p (n : ℕ) : 1 ≤ Partitions.p n := Fintype.card_pos

theorem one_le_pZ {m : ℤ} (hm : 0 ≤ m) : 1 ≤ pZ m := by
  rw [pZ, if_pos hm]
  exact one_le_p _

end GeneralPieces.Pcs

namespace GeneralPieces

open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ GeneralPieces.Pcs

/-- The steps of the proof of the theorem on the pieces with ρ = 1/√2 that are statements about the
ring, from the two lemmas and the other hypotheses named at the head. -/
theorem pieceFacts (hQ : LemmaQ) (hD : LemmaDual) (hOp : OpFacts) (h1 : O1) (hZ : ZDvd) : PieceFacts where
  wtLe h μ hμ := by
    rw [← hμ]
    exact wtLe_of_le (le_aFam μ)
  sum h ξ η υ ν hh hξ hη hυ hν := by
    have ha : WtLe h (aFam ξ) := by rw [← hξ]; exact wtLe_of_le (le_aFam ξ)
    have hb : bFam ν ∈ VE h := by rw [← hν]; exact bFam_mem ν
    have hf : tpow η ∈ VE h := by rw [← hη]; exact tpow_mem_VE η
    have e := hQ.c h (aFam ξ) (bFam ν) hh hb ha h (tpow η) hf
    have e2 : pairing h (aFam ξ) (bFam ν) = if ξ = ν then (h.factorial : ℚ) else 0 := by
      rw [pairing, hD h ξ ν hξ hν, coeff_C, if_pos rfl]
    rw [show (2 * h : ℤ) = (h : ℤ) + h by ring, ← coef_sum, e, e2, coef_smul, coef_tpow]
    by_cases h3 : ξ = ν <;> by_cases h4 : η = υ <;> simp [h3, h4, eq_comm]
  row h ξ η υ ν s hh hξ hη hυ hν := by
    have ha : WtLe h (aFam ξ) := by rw [← hξ]; exact wtLe_of_le (le_aFam ξ)
    have hb : bFam ν ∈ VE h := by rw [← hν]; exact bFam_mem ν
    have hf : tpow η ∈ VE h := by rw [← hη]; exact tpow_mem_VE η
    rw [hQ.a h (aFam ξ) (bFam ν) hh hb ha h (tpow η) hf s, Q', coef_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [coef_smul, coef_comp_gen hOp h1 _ _ _ _ hf, mul_sum, show (h : ℤ) + (s - h + i) = s + i by ring]
    exact sum_congr rfl fun σ _ => by ring
  col h ξ η υ ν s hh hξ hη hυ hν := by
    have hf : tpow η ∈ VE h := by rw [← hη]; exact tpow_mem_VE η
    rw [Q, coef_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [coef_smul, coef_comp_gen hOp h1 _ _ _ _ hf, mul_sum, show (h : ℤ) + (h - s - i) = 2 * h - s - i by ring]
    exact sum_congr rfl fun σ _ => by ring
  int_a h i ξ σ r := h1.int _ r _ (isInt_angle (isInt_aFam ξ) h i) (isInt_tpow σ)
  int_b ν σ r := h1.int _ r _ (isInt_bFam hZ ν) (isInt_tpow σ)
  terms h s hs := by
    have h2 := abs_le.1 hs
    constructor
    · unfold Rrow
      exact (one_le_pZ (m := s + (2 * h : ℕ)) (by push_cast; omega)).trans
        (single_le_sum (f := fun i : ℕ => pZ (s + i)) (fun _ _ => Nat.zero_le _) (mem_range.2 (by omega)))
    · unfold Rcol
      exact (one_le_pZ (m := 2 * h - s - (0 : ℕ)) (by push_cast; omega)).trans
        (single_le_sum (f := fun i : ℕ => pZ (2 * h - s - i)) (fun _ _ => Nat.zero_le _) (mem_range.2 (by omega)))

end GeneralPieces
