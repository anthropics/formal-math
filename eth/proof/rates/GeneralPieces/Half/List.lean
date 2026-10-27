/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Ring.Op
public import ClauseBound.Boson.HalfList

/-! # The pieces with ρ = 1/√2: from the ring of Appendix B to the matrices that the programs compute

The programs write a partition as a list of natural numbers and compute entries of integer matrices:
`ClauseBound.Boson.topK` carries a^μ and `ClauseBound.Boson.botK` carries b^ν. This file shows that
these entries
are the factors in displays (54) and (55) of the proof of the theorem on pieces with ρ = 1/√2
(`topK_eq`, `botK_eq`), so that the integer function `ClauseBound.Boson.ApcL` is the piece A_s of
the appendix
(`ApcL_eq_piece`). Then the sum of the pieces and display (54) for the matrices are read off the
statements about the ring, `AppHalfPieces.PieceFacts`, which is a hypothesis here (`sum_ApcL`,
`ApcL_row_eq`).
Display (55) for the matrices is the definition of `ApcL` with the matrix product written as a sum
over σ (`ClauseBound.Boson.ApcL_col_eq`). -/

public section

namespace GeneralPieces

open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

/-! ### Lists of natural numbers as partitions -/

/-- A list of natural numbers as a list of positive integers. -/
@[expose] def toPNats (L : List ℕ) : List ℕ+ := L.map Nat.toPNat'

/-- The partition whose parts are listed. -/
@[expose] def ptn (L : List ℕ) : Ptn := (toPNats L : Multiset ℕ+)

namespace Half

theorem toL_toPNats {L : List ℕ} (hL : ClauseBound.Boson.Pos L) : toL (toPNats L) = L := by
  unfold toL toPNats
  rw [List.map_map]
  conv_rhs => rw [← List.map_id L]
  exact List.map_congr_left fun k hk => PNat.toPNat'_coe (hL k hk)

theorem toN_ptn {L : List ℕ} (hL : ClauseBound.Boson.Pos L) : toN (ptn L) = (L : Multiset ℕ) := by
  have h : toN (ptn L) = ((toL (toPNats L) : List ℕ) : Multiset ℕ) := rfl
  rw [h, toL_toPNats hL]

theorem wt_ptn {L : List ℕ} (hL : ClauseBound.Boson.Pos L) : wt (ptn L) = L.sum := by
  rw [← sum_toN, toN_ptn hL, Multiset.sum_coe]

theorem ptn_cons (n : ℕ) (L : List ℕ) : ptn (n :: L) = n.toPNat' ::ₘ ptn L := rfl

theorem tpow_ptn_cons (n : ℕ) (L : List ℕ) : tpow (ptn (n :: L)) = X n.toPNat' * tpow (ptn L) := by
  rw [ptn_cons, X_mul_tpow]

/-- z_μ is the same number for the partition and for its multiset of natural numbers. -/
theorem zz_eq (μ : Ptn) : AppHalfPieces.zz μ = ClauseBound.Boson.zz (toN μ) := by
  unfold AppHalfPieces.zz ClauseBound.Boson.zz
  have h : (toN μ).toFinset = μ.toFinset.image fun k : ℕ+ => (k : ℕ) := Multiset.toFinset_map _ _
  rw [h, Finset.prod_image fun a _ b _ e => PNat.coe_injective e]
  exact Finset.prod_congr rfl fun k _ => by rw [count_toN]

/-! ### The factor that carries b^ν -/

/-- The entry (π, σ) of the matrix (h!/z_ν)·t^ν[r] is the coefficient of t^π in b^ν[r]·t^σ. -/
theorem botK_eq {L : List ℕ} {h : ℕ} (hL : ClauseBound.Boson.Pos L) (hs : L.sum = h) (r : ℤ) (π σ : Ptn) :
    ((ClauseBound.Boson.botK L h r (toN π) (toN σ) : ℤ) : ℚ) = coef π (op (bFam (ptn L)) r (tpow σ)) := by
  have hd : ClauseBound.Boson.zz (L : Multiset ℕ) ∣ h.factorial :=
    ClauseBound.Boson.zz_dvd_factorial (⟨(L : Multiset ℕ), fun hi => hL _ (Multiset.mem_coe.1 hi), by rw [Multiset.sum_coe]; exact hs⟩ : Nat.Partition h)
  have h0 : ((ClauseBound.Boson.zz (L : Multiset ℕ) : ℕ) : ℚ) ≠ 0 := by
    intro h0
    have h1 : ClauseBound.Boson.zz (L : Multiset ℕ) = 0 := by exact_mod_cast h0
    rw [h1] at hd
    exact (Nat.factorial_pos h).ne' (Nat.eq_zero_of_zero_dvd hd)
  rw [bFam, op_smul_left, coef_smul, wt_ptn hL, hs, zz_eq, toN_ptn hL]
  have h2 : op (tpow (ptn L)) r (tpow σ) = opMon (toPNats L) r (tpow σ) := op_tpow (toPNats L) r (tpow σ)
  rw [h2, stBridge, toL_toPNats hL, ClauseBound.Boson.botK, Int.cast_mul, Int.cast_natCast, Nat.cast_div hd h0]

/-! ### The factor that carries a^μ -/

/-- A combination of monomials, given as a list, as a polynomial; the coefficient of a term is given
by k. -/
@[expose] noncomputable def polyK (k : ℤ × List ℕ → ℚ) (A : ClauseBound.Boson.FA) : V := (A.map fun c => k c • tpow (ptn c.2)).sum

/-- A combination of monomials, given as a list, as a polynomial. -/
@[expose] noncomputable def polyOf (A : ClauseBound.Boson.FA) : V := polyK (fun c => (c.1 : ℚ)) A

theorem polyK_nil (k : ℤ × List ℕ → ℚ) : polyK k [] = 0 := rfl

theorem polyK_cons (k : ℤ × List ℕ → ℚ) (c : ℤ × List ℕ) (A : ClauseBound.Boson.FA) : polyK k (c :: A) = k c • tpow (ptn c.2) + polyK k A := by
  simp [polyK]

theorem polyK_append (k : ℤ × List ℕ → ℚ) (A B : ClauseBound.Boson.FA) : polyK k (A ++ B) = polyK k A + polyK k B := by
  simp [polyK]

/-- One term c·t_j times a combination. -/
theorem polyOf_map_cons (c : ℤ) (j : ℕ) (A : ClauseBound.Boson.FA) :
    polyOf (A.map fun cL => (c * cL.1, j :: cL.2)) = ((c : ℚ) • X j.toPNat') * polyOf A := by
  induction A with
  | nil => simp [polyOf, polyK]
  | cons a A ih =>
    simp only [polyOf] at ih ⊢
    rw [List.map_cons, polyK_cons, polyK_cons, mul_add, ih, tpow_ptn_cons]
    congr 1
    push_cast
    rw [smul_mul_smul_comm]

/-- A combination of variables times a combination of monomials, multiplied out. -/
theorem polyOf_flatMap (Y : List (ℤ × ℕ)) (A : ClauseBound.Boson.FA) :
    polyOf (Y.flatMap fun cj => A.map fun cL => (cj.1 * cL.1, cj.2 :: cL.2)) = (Y.map fun cj => (cj.1 : ℚ) • (X cj.2.toPNat' : V)).sum * polyOf A := by
  induction Y with
  | nil => simp [polyOf, polyK]
  | cons a Y ih =>
    have h := polyOf_map_cons a.1 a.2 A
    simp only [polyOf] at ih h ⊢
    rw [List.flatMap_cons, polyK_append, List.map_cons, List.sum_cons, add_mul, ih, h]

/-- A sum over 1, …, n as the sum of a list. -/
theorem sum_Icc_eq_list (f : ℕ → V) (n : ℕ) : ∑ j ∈ Icc 1 n, f j = ((List.range n).map fun i => f (i + 1)).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, List.range_succ, List.map_append, List.sum_append]; simp

/-- The list of the terms of (−1)^{n−1}·y_n. -/
theorem sum_yl {n : ℕ} (hn : 1 ≤ n) :
    ((ClauseBound.Boson.yl n).map fun cj => (cj.1 : ℚ) • (X cj.2.toPNat' : V)).sum = (-1 : ℚ) ^ (((n.toPNat' : ℕ+) : ℕ) - 1) • y n.toPNat' := by
  have h : ((n.toPNat' : ℕ+) : ℕ) = n := PNat.toPNat'_coe hn
  rw [y, h, sum_Icc_eq_list, ClauseBound.Boson.yl, List.map_map, List.smul_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp]
  push_cast
  rw [mul_smul]

/-- a^μ, multiplied out. -/
theorem aFam_eq {L : List ℕ} (hL : ClauseBound.Boson.Pos L) : AppHalfPieces.aFam (ptn L) = polyOf (ClauseBound.Boson.aFam L) := by
  induction L with
  | nil => simp [AppHalfPieces.aFam, ptn, toPNats, polyOf, polyK, ClauseBound.Boson.aFam, tpow]
  | cons n L ih =>
    rw [ClauseBound.Boson.aFam, polyOf_flatMap, sum_yl (hL n List.mem_cons_self), ← ih fun m hm => hL m (List.mem_cons_of_mem _ hm), ptn_cons, AppHalfPieces.aFam,
      Multiset.map_cons, Multiset.prod_cons, AppHalfPieces.aFam]

/-- The part of weight h' of a monomial. -/
theorem part_tpow (h' : ℕ) (μ : Ptn) : part h' (tpow μ) = if h' = wt μ then tpow μ else 0 := by
  have h : tpow μ ∈ weightedHomogeneousSubmodule ℚ wgt (wt μ) := by
    have := tpow_mem_VE μ
    rwa [VE_natCast] at this
  exact weightedHomogeneousComponent_of_mem h

theorem angle_add (h i : ℕ) (a b : V) : angle h i (a + b) = angle h i a + angle h i b := by
  simp only [angle, part, map_add, smul_add, Finset.sum_add_distrib]

theorem angle_zero (h i : ℕ) : angle h i 0 = 0 := by
  simp [angle, part]

/-- (q·t^μ)^⟨i⟩ = C(|μ| + h, i)·q·t^μ for |μ| ≤ h. -/
theorem angle_smul_tpow (h i : ℕ) (q : ℚ) {μ : Ptn} (hμ : wt μ ≤ h) : angle h i (q • tpow μ) = (q * ((wt μ + h).choose i : ℚ)) • tpow μ := by
  unfold angle
  rw [Finset.sum_eq_single_of_mem (wt μ) (Finset.mem_range.2 (by omega))]
  · rw [part, map_smul, ← part, part_tpow, if_pos rfl, smul_smul, mul_comm]
  · intro h' _ hne
    rw [part, map_smul, ← part, part_tpow, if_neg hne, smul_zero, smul_zero]

/-- a^⟨i⟩ for a combination of monomials of weight at most h. -/
theorem angle_polyOf {A : ClauseBound.Boson.FA} {h : ℕ} (hA : A.Ok h) (i : ℕ) :
    angle h i (polyOf A) = polyK (fun c => (c.1 : ℚ) * ((c.2.sum + h).choose i : ℚ)) A := by
  induction A with
  | nil => exact angle_zero h i
  | cons c A ih =>
    have hc := hA c List.mem_cons_self
    simp only [polyOf] at ih ⊢
    rw [polyK_cons, polyK_cons, angle_add, angle_smul_tpow h i _ (by rw [wt_ptn hc.1]; exact hc.2), wt_ptn hc.1,
      ih fun c' hc' => hA c' (List.mem_cons_of_mem _ hc')]

/-- The coefficient of t^π in a[r]·t^σ for a combination a of monomials: the same combination of the
entries of the matrices. -/
theorem coef_op_polyK (k : ℤ × List ℕ → ℚ) {A : ClauseBound.Boson.FA} (hA : ∀ c ∈ A, ClauseBound.Boson.Pos c.2) (r : ℤ) (π σ : Ptn) :
    coef π (op (polyK k A) r (tpow σ)) = (A.map fun c => k c * ((ClauseBound.Boson.op c.2 r (toN π) (toN σ) : ℤ) : ℚ)).sum := by
  induction A with
  | nil =>
    have h : op (0 : V) r (tpow σ) = 0 := map_zero (opLeft r (tpow σ))
    rw [polyK_nil, h]
    simp [coef]
  | cons c A ih =>
    have h2 : op (tpow (ptn c.2)) r (tpow σ) = opMon (toPNats c.2) r (tpow σ) := op_tpow (toPNats c.2) r (tpow σ)
    have h3 : ∀ f g : V, coef π (f + g) = coef π f + coef π g := fun f g => coeff_add _ f g
    rw [polyK_cons, op_add_left, h3, op_smul_left, coef_smul, h2, stBridge, toL_toPNats (hA c List.mem_cons_self), List.map_cons, List.sum_cons,
      ih fun c' hc' => hA c' (List.mem_cons_of_mem _ hc')]

/-- The entry (π, σ) of the matrix that carries a^μ is (−1)^i times the coefficient of t^π in
(a^μ)^⟨i⟩[r]·t^σ. -/
theorem topK_eq {L : List ℕ} {h : ℕ} (hL : ClauseBound.Boson.Pos L) (hs : L.sum = h) (i : ℕ) (r : ℤ) (π σ : Ptn) :
    ((ClauseBound.Boson.topK L h i r (toN π) (toN σ) : ℤ) : ℚ) = (-1) ^ i * coef π (op (angle h i (AppHalfPieces.aFam (ptn L))) r (tpow σ)) := by
  have hA : (ClauseBound.Boson.aFam L).Ok h := by
    have := ClauseBound.Boson.aFam_ok hL
    rwa [hs] at this
  rw [aFam_eq hL, angle_polyOf hA, coef_op_polyK _ (fun c hc => (hA c hc).1), ClauseBound.Boson.topK]
  push_cast
  congr 1
  induction ClauseBound.Boson.aFam L with
  | nil => simp
  | cons c A ih => simp only [List.map_cons, List.sum_cons]; push_cast; rw [ih]

end Half

open Half

/-! ### The pieces -/

section

variable {lam h : ℕ} {ℓ : Pieces.Bits lam → List ℕ}

/-- The integer function that the programs factorize is the piece A_s of the appendix, for μ(x) the
partition listed in ℓ(x). By display (55). -/
theorem ApcL_eq_piece (hPF : PieceFacts) (hℓ : ∀ x, ClauseBound.Boson.Pos (ℓ x) ∧ (ℓ x).sum = h) (hh : 1 ≤ h) (s : ℤ) (x y u v : Pieces.Bits lam) :
    ((ClauseBound.Boson.ApcL ℓ h s x y u v : ℤ) : ℚ) = piece h (fun x => ptn (ℓ x)) s x y u v := by
  have hw : ∀ x, wt (ptn (ℓ x)) = h := fun x => by rw [wt_ptn (hℓ x).1, (hℓ x).2]
  rw [piece, hPF.col h _ _ _ _ s hh (hw x) (hw y) (hw u) (hw v), ClauseBound.Boson.ApcL_col_eq hℓ]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_Pz]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← toN_ptn (hℓ u).1, ← toN_ptn (hℓ y).1, topK_eq (hℓ x).1 (hℓ x).2, botK_eq (hℓ v).1 (hℓ v).2]

/-- Σ_s A_s = h!·[x = v][y = u], from the statement about the ring. -/
theorem sum_ApcL (hPF : PieceFacts) (hℓ : ∀ x, ClauseBound.Boson.Pos (ℓ x) ∧ (ℓ x).sum = h) (hinj : ∀ x v, (ℓ x : Multiset ℕ) = ℓ v → x = v) (hh : 1 ≤ h)
    (x y u v : Pieces.Bits lam) :
    ∑ s ∈ Icc (-(2 * h : ℤ)) (2 * h), ClauseBound.Boson.ApcL ℓ h s x y u v = h.factorial * Pieces.cross x y u v := by
  have hw : ∀ x, wt (ptn (ℓ x)) = h := fun x => by rw [wt_ptn (hℓ x).1, (hℓ x).2]
  have hi : ∀ x v, ptn (ℓ x) = ptn (ℓ v) ↔ x = v := fun x v =>
    ⟨fun e => hinj x v (by rw [← toN_ptn (hℓ x).1, ← toN_ptn (hℓ v).1, e]), fun e => by rw [e]⟩
  have h1 := hPF.sum h _ _ _ _ hh (hw x) (hw y) (hw u) (hw v)
  have h2 : ((∑ s ∈ Icc (-(2 * h : ℤ)) (2 * h), ClauseBound.Boson.ApcL ℓ h s x y u v : ℤ) : ℚ) = ((h.factorial * Pieces.cross x y u v : ℤ) : ℚ) := by
    push_cast
    rw [Finset.sum_congr rfl fun s _ => ApcL_eq_piece hPF hℓ hh s x y u v]
    unfold piece
    rw [h1, Pieces.cross]
    simp only [hi]
    split_ifs <;> simp
  exact_mod_cast h2

/-- Display (54) for the matrices, from the statement about the ring. -/
theorem ApcL_row_eq (hPF : PieceFacts) (hℓ : ∀ x, ClauseBound.Boson.Pos (ℓ x) ∧ (ℓ x).sum = h) (hh : 1 ≤ h) (s : ℤ) (x y u v : Pieces.Bits lam) :
    ClauseBound.Boson.ApcL ℓ h s x y u v = ∑ i ∈ range (2 * h + 1), ∑ τ ∈ ClauseBound.Boson.Pz (s + i),
      ClauseBound.Boson.topK (ℓ x) h i (s - h + i) τ (ℓ y : Multiset ℕ) * ClauseBound.Boson.botK (ℓ v) h (h - s - i) (ℓ u : Multiset ℕ) τ := by
  have hw : ∀ x, wt (ptn (ℓ x)) = h := fun x => by rw [wt_ptn (hℓ x).1, (hℓ x).2]
  have h2 : ((ClauseBound.Boson.ApcL ℓ h s x y u v : ℤ) : ℚ) = ((∑ i ∈ range (2 * h + 1), ∑ τ ∈ ClauseBound.Boson.Pz (s + i),
      ClauseBound.Boson.topK (ℓ x) h i (s - h + i) τ (ℓ y : Multiset ℕ) * ClauseBound.Boson.botK (ℓ v) h (h - s - i) (ℓ u : Multiset ℕ) τ : ℤ) : ℚ) := by
    rw [ApcL_eq_piece hPF hℓ hh, piece, hPF.row h _ _ _ _ s hh (hw x) (hw y) (hw u) (hw v)]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_Pz]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← toN_ptn (hℓ u).1, ← toN_ptn (hℓ y).1, topK_eq (hℓ x).1 (hℓ x).2, botK_eq (hℓ v).1 (hℓ v).2]
  exact_mod_cast h2

end

end GeneralPieces
