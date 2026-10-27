/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Ring.Bits
public import ClauseBound.Boson.Final

/-! # The theorem on the pieces with ρ = 1/√2, without the running time, from the statements about the ring

The proof of that theorem in Appendix B, from its first sentence to the sentence that Definition 7
holds with ρ = 1/√2 if c is large enough. The pieces are
A_s(x,y,u,v) = the coefficient of t^{μ(u)} in Q_s(a^{μ(x)}, b^{μ(v)})·t^{μ(y)}, with h the least
integer ≥ 2 with p(h) ≥ 2^λ and μ(x) the partition of h with number x in the lexicographic list.
Their sum, the two displays (54) and (55) and the integrality of the factors are taken from
`AppHalfPieces.PieceFacts`, which is a hypothesis here. From these: the pieces are integers
(`piece_row`);
they add up to h!·[x = v][y = u] (`sum_A`); numbering the pairs (i, σ) of (54) and of (55) gives
factorizations through ⌈log R^row_s⌉ and ⌈log R^col_s⌉ bits (`row_A`, `col_A`);
the number of terms of (55) is R^col_s (`card_terms_col`); all partitions in (55) are listed
(`wt_le_col`), and A_s is a sum of at most Δ products of two factors
(`Rcol_le_Delta`, `abs_piece_le`), so it is 2^{O(h²)} in absolute value (`bound_lt_big`,
`abs_A_lt`).
The sizes of the factors are those of `GeneralPieces.Sizes`; the bound on c^row_s + c^col_s, h =
O(λ²) and log Δ = O(λ) are those of `GeneralPieces.Bits`, with display (46) in the form proved in
`ClauseBound.Part.exists_bounds`, with B·log E in place of log E.
The choice of c and the lemma that a sum of R products factors through ⌈log R⌉ bits are those of
proof/rates/ClauseBound/Boson/Final.lean and proof/rates/ClauseBound/Boson/Half.lean; their
exponents 16h² + 4h and 17h² + h, which
are larger than 12h² + 3h and 13h², are used as bounds for the two factors. -/

public section

namespace GeneralPieces.ThmHalfPieces

open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex

/-! ### The factors as integers -/

/-- A coefficient of an integer polynomial, as an integer. -/
theorem cast_num_coef {f : V} (hf : IsInt f) (μ : Ptn) : (((coef μ f).num : ℤ) : ℚ) = coef μ f := by
  obtain ⟨z, hz⟩ := hf (Multiset.toFinsupp μ)
  unfold coef
  rw [hz, Rat.num_intCast]

/-- The first factor of a term of (54) or (55), with the sign: (−1)^i times the coefficient of
t^{σ'} in a^⟨i⟩[r]·t^σ, for a = a^ξ. -/
@[expose] noncomputable def fa (h i : ℕ) (r : ℤ) (ξ σ' σ : Ptn) : ℤ := (-1) ^ i * (coef σ' (op (angle h i (aFam ξ)) r (tpow σ))).num

/-- The second factor: the coefficient of t^{σ'} in b[r]·t^σ, for b = b^ν. -/
@[expose] noncomputable def fb (r : ℤ) (ν σ' σ : Ptn) : ℤ := (coef σ' (op (bFam ν) r (tpow σ))).num

/-- The family of the appendix: d = h!, I = {−2h, …, 2h}, the pieces A_s, c^row_s = ⌈log R^row_s⌉,
c^col_s = ⌈log R^col_s⌉. A_s is written as the numerator of the coefficient that defines it, which
is an
integer (`cast_A`). -/
@[expose] noncomputable def fam {lam : ℕ} (h : ℕ) (mu : Pieces.Bits lam → Ptn) : Pieces.Family lam where
  d := h.factorial
  I := Icc (-(2 * h : ℤ)) (2 * h)
  A := fun s x y u v => (piece h mu s x y u v).num
  crow := fun s => Nat.clog 2 (Rrow h s)
  ccol := fun s => Nat.clog 2 (Rcol h s)

theorem three_le_eL (h : ℕ) : 3 * h + 12 * h ^ 2 ≤ ClauseBound.Boson.Half.eL h := by
  unfold ClauseBound.Boson.Half.eL
  nlinarith

theorem sq_le_eR (h : ℕ) : h * h + 12 * h ^ 2 ≤ ClauseBound.Boson.Half.eR h := by
  unfold ClauseBound.Boson.Half.eR
  nlinarith

/-- The first factor is small at listed partitions. -/
theorem abs_fa_le (hP : PieceFacts) {h : ℕ} (hh : 1 ≤ h) (i : ℕ) {ξ : Ptn} (hξ : wt ξ = h) (r : ℤ) {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h) (h2 : wt σ ≤ 4 * h) :
    |fa h i r ξ σ' σ| ≤ 2 ^ ClauseBound.Boson.Half.eL h := by
  have a1 := abs_factor_a_le hh i hξ r h1 h2
  rw [← cast_num_coef (hP.int_a h i ξ σ r) σ', ← pow_add] at a1
  have a2 : |(coef σ' (op (angle h i (aFam ξ)) r (tpow σ))).num| ≤ 2 ^ (3 * h + 12 * h ^ 2) := by exact_mod_cast a1
  rw [fa, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact a2.trans (pow_le_pow_right₀ (by norm_num) (three_le_eL h))

/-- The second factor is small at listed partitions. -/
theorem abs_fb_le (hP : PieceFacts) {h : ℕ} (hh : 1 ≤ h) {ν : Ptn} (hν : wt ν = h) (r : ℤ) {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h) (h2 : wt σ ≤ 4 * h) :
    |fb r ν σ' σ| ≤ 2 ^ ClauseBound.Boson.Half.eR h := by
  have a1 := abs_factor_b_le hh hν r h1 h2
  rw [← cast_num_coef (hP.int_b ν σ r) σ'] at a1
  have a2 : |(coef σ' (op (bFam ν) r (tpow σ))).num| ≤ (h.factorial : ℤ) * 2 ^ (12 * h ^ 2) := by exact_mod_cast a1
  have a3 : h.factorial ≤ 2 ^ (h * h) := (Nat.factorial_le_pow h).trans (by
    rw [pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le h)
  have a4 : (h.factorial : ℤ) ≤ 2 ^ (h * h) := by exact_mod_cast a3
  calc |fb r ν σ' σ| ≤ (h.factorial : ℤ) * 2 ^ (12 * h ^ 2) := a2
    _ ≤ 2 ^ (h * h) * 2 ^ (12 * h ^ 2) := mul_le_mul_of_nonneg_right a4 (by positivity)
    _ = 2 ^ (h * h + 12 * h ^ 2) := (pow_add _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (sq_le_eR h)

/-! ### The pieces -/

section

variable {lam h : ℕ} {mu : Pieces.Bits lam → Ptn}

/-- Display (54) with integer factors. In particular the pieces are integers. -/
theorem piece_row (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) (s : ℤ) (x y u v : Pieces.Bits lam) :
    piece h mu s x y u v = ((∑ i ∈ range (2 * h + 1), ∑ σ ∈ ptnsZ (s + i),
      fa h i (s - h + i) (mu x) σ (mu y) * fb (h - s - i) (mu v) (mu u) σ : ℤ) : ℚ) := by
  unfold piece
  rw [hP.row h _ _ _ _ s hh (IsMu.wt hmu x) (IsMu.wt hmu y) (IsMu.wt hmu u) (IsMu.wt hmu v)]
  push_cast
  refine sum_congr rfl fun i _ => sum_congr rfl fun σ _ => ?_
  rw [fa, fb]
  push_cast
  rw [cast_num_coef (hP.int_a _ _ _ _ _), cast_num_coef (hP.int_b _ _ _)]

/-- Display (55) with integer factors. -/
theorem piece_col (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) (s : ℤ) (x y u v : Pieces.Bits lam) :
    piece h mu s x y u v = ((∑ i ∈ range (2 * h + 1), ∑ σ ∈ ptnsZ (2 * h - s - i),
      fa h i (s - h + i) (mu x) (mu u) σ * fb (h - s - i) (mu v) σ (mu y) : ℤ) : ℚ) := by
  unfold piece
  rw [hP.col h _ _ _ _ s hh (IsMu.wt hmu x) (IsMu.wt hmu y) (IsMu.wt hmu u) (IsMu.wt hmu v)]
  push_cast
  refine sum_congr rfl fun i _ => sum_congr rfl fun σ _ => ?_
  rw [fa, fb]
  push_cast
  rw [cast_num_coef (hP.int_a _ _ _ _ _), cast_num_coef (hP.int_b _ _ _)]

/-- The integer A_s is the coefficient that defines the piece. -/
theorem cast_A (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) (s : ℤ) (x y u v : Pieces.Bits lam) :
    ((fam h mu).A s x y u v : ℚ) = piece h mu s x y u v := by
  change (((piece h mu s x y u v).num : ℤ) : ℚ) = _
  rw [piece_row hP hmu hh, Rat.num_intCast]

/-- Display (54) for the integers A_s, with the sum over the monomials of the matrices. -/
theorem A_row (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) (s : ℤ) (x y u v : Pieces.Bits lam) :
    (fam h mu).A s x y u v = ∑ i ∈ range (2 * h + 1), ∑ τ ∈ ClauseBound.Boson.Pz (s + i),
      fa h i (s - h + i) (mu x) (τ.map Nat.toPNat') (mu y) * fb (h - s - i) (mu v) (mu u) (τ.map Nat.toPNat') := by
  change (piece h mu s x y u v).num = _
  rw [piece_row hP hmu hh, Rat.num_intCast]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_Pz]
  exact sum_congr rfl fun σ _ => by rw [map_toPNat'_toN]

/-- Display (55) for the integers A_s, with the sum over the monomials of the matrices. -/
theorem A_col (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) (s : ℤ) (x y u v : Pieces.Bits lam) :
    (fam h mu).A s x y u v = ∑ i ∈ range (2 * h + 1), ∑ τ ∈ ClauseBound.Boson.Pz (2 * h - s - i),
      fa h i (s - h + i) (mu x) (mu u) (τ.map Nat.toPNat') * fb (h - s - i) (mu v) (τ.map Nat.toPNat') (mu y) := by
  change (piece h mu s x y u v).num = _
  rw [piece_col hP hmu hh, Rat.num_intCast]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_Pz]
  exact sum_congr rfl fun σ _ => by rw [map_toPNat'_toN]

/-- Σ_s A_s = h!·[x = v][y = u]. -/
theorem sum_A (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) (x y u v : Pieces.Bits lam) :
    ∑ s ∈ (fam h mu).I, (fam h mu).A s x y u v = (fam h mu).d * Pieces.cross x y u v := by
  have e : ((∑ s ∈ (fam h mu).I, (fam h mu).A s x y u v : ℤ) : ℚ) = (((fam h mu).d * Pieces.cross x y u v : ℤ) : ℚ) := by
    push_cast
    simp_rw [cast_A hP hmu hh]
    have h1 := hP.sum h (mu x) (mu y) (mu u) (mu v) hh (IsMu.wt hmu x) (IsMu.wt hmu y) (IsMu.wt hmu u) (IsMu.wt hmu v)
    change ∑ s ∈ Icc (-(2 * h : ℤ)) (2 * h), coef (mu u) (Q h s (aFam (mu x)) (bFam (mu v)) (tpow (mu y))) = ((h.factorial : ℤ) : ℚ) * _
    rw [h1, Pieces.cross]
    have h2 : (mu x = mu v ∧ mu y = mu u) ↔ (x = v ∧ y = u) := by rw [(IsMu.injective hmu).eq_iff, (IsMu.injective hmu).eq_iff]
    by_cases h3 : x = v ∧ y = u
    · rw [if_pos (h2.2 h3), if_pos h3]
      push_cast
      ring
    · rw [if_neg (fun h4 => h3 (h2.1 h4)), if_neg h3]
      push_cast
      ring
  exact_mod_cast e

/-- The weight of a monomial of the matrices, as a partition. -/
theorem wt_map {m : ℤ} {τ : Multiset ℕ} (hτ : τ ∈ ClauseBound.Boson.Pz m) : (wt (τ.map Nat.toPNat') : ℤ) = m := by
  rw [Pz_eq] at hτ
  obtain ⟨σ, hσ, rfl⟩ := mem_image.1 hτ
  rw [map_toPNat'_toN]
  exact (mem_ptnsZ m σ).1 hσ

/-- Numbering the pairs (i, σ) of (54), here in some order that is not specified, gives a
factorization through ⌈log R^row_s⌉ bits: the first function depends on (x,y), the second on (u,v). -/
theorem row_A (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) :
    Pieces.FactorsThrough (Pieces.rowwise ((fam h mu).A s)) ((fam h mu).crow s) (2 ^ ClauseBound.Boson.big h) :=
  ClauseBound.Boson.Half.factors (h := h) (Pieces.rowwise ((fam h mu).A s)) (fun i => s + i)
    (fun i τ z => fa h i (s - h + i) (mu z.1) (τ.map Nat.toPNat') (mu z.2))
    (fun i τ z' => fb (h - s - i) (mu z'.2) (mu z'.1) (τ.map Nat.toPNat'))
    (fun z z' => A_row hP hmu hh s z.1 z.2 z'.1 z'.2)
    (fun i hi τ hτ z => abs_fa_le hP hh i (IsMu.wt hmu z.1) _
      (by have := wt_map hτ; have := abs_le.1 hs; have := mem_range.1 hi; omega) (by rw [IsMu.wt hmu]; omega))
    (fun i hi τ hτ z' => abs_fb_le hP hh (IsMu.wt hmu z'.2) _ (by rw [IsMu.wt hmu]; omega)
      (by have := wt_map hτ; have := abs_le.1 hs; have := mem_range.1 hi; omega))

/-- Numbering the pairs (i, σ) of (55), here in some order that is not specified, gives a
factorization through ⌈log R^col_s⌉ bits: the first function depends on (x,u), the second on (y,v). -/
theorem col_A (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) :
    Pieces.FactorsThrough (Pieces.colwise ((fam h mu).A s)) ((fam h mu).ccol s) (2 ^ ClauseBound.Boson.big h) :=
  ClauseBound.Boson.Half.factors (h := h) (Pieces.colwise ((fam h mu).A s)) (fun i => 2 * h - s - i)
    (fun i τ z => fa h i (s - h + i) (mu z.1) (mu z.2) (τ.map Nat.toPNat'))
    (fun i τ z' => fb (h - s - i) (mu z'.2) (τ.map Nat.toPNat') (mu z'.1))
    (fun z z' => A_col hP hmu hh s z.1 z'.1 z.2 z'.2)
    (fun i _ τ hτ z => abs_fa_le hP hh i (IsMu.wt hmu z.1) _ (by rw [IsMu.wt hmu]; omega)
      (by have := wt_map hτ; have := abs_le.1 hs; omega))
    (fun i _ τ hτ z' => abs_fb_le hP hh (IsMu.wt hmu z'.2) _
      (by have := wt_map hτ; have := abs_le.1 hs; omega) (by rw [IsMu.wt hmu]; omega))

/-- All partitions in (55) are among the listed ones. -/
theorem wt_le_col {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) {i : ℕ} {σ : Ptn} (hσ : σ ∈ ptnsZ (2 * h - s - i)) : wt σ ≤ 4 * h := by
  have := (mem_ptnsZ _ σ).1 hσ
  have := abs_le.1 hs
  omega

/-- The sum (55) has at most Δ terms. -/
theorem Rcol_le_Delta {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) : Rcol h s ≤ Delta h :=
  ClauseBound.Boson.Half.sum_pz_le (fun i => 2 * h - s - i) (fun i j hij => by omega) (fun i _ => by have := abs_le.1 hs; omega)

theorem card_ptnsZ (m : ℤ) : #(ptnsZ m) = pZ m := by
  unfold ptnsZ pZ
  split_ifs
  · exact card_ptns _
  · exact card_empty

/-- The number of terms of (55) is R^col_s. -/
theorem card_terms_col (h : ℕ) (s : ℤ) : ∑ i ∈ range (2 * h + 1), #(ptnsZ (2 * h - s - i)) = Rcol h s :=
  sum_congr rfl fun _ _ => card_ptnsZ _

/-- A_s is a sum of at most Δ products of two factors: |A_s| ≤ Δ·(2^{3h}·2^{12h²})·(h!·2^{12h²}),
which is 2^{O(h²)}. -/
theorem abs_piece_le (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) (x y u v : Pieces.Bits lam) :
    |piece h mu s x y u v| ≤ Delta h * ((2 ^ (3 * h) * 2 ^ (12 * h ^ 2)) * (h.factorial * 2 ^ (12 * h ^ 2))) := by
  have hw : ∀ z, wt (mu z) ≤ 4 * h := fun z => by rw [IsMu.wt hmu]; omega
  unfold piece
  rw [hP.col h _ _ _ _ s hh (IsMu.wt hmu x) (IsMu.wt hmu y) (IsMu.wt hmu u) (IsMu.wt hmu v)]
  generalize hK : ((2 : ℚ) ^ (3 * h) * 2 ^ (12 * h ^ 2)) * (h.factorial * 2 ^ (12 * h ^ 2)) = K
  have hK0 : 0 ≤ K := by rw [← hK]; positivity
  have h1 : ∀ i ∈ range (2 * h + 1), ∀ σ ∈ ptnsZ (2 * h - s - i),
      |(-1 : ℚ) ^ i * coef (mu u) (op (angle h i (aFam (mu x))) (s - h + i) (tpow σ)) * coef σ (op (bFam (mu v)) (h - s - i) (tpow (mu y)))| ≤ K := by
    intro i _ σ hσ
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, ← hK]
    exact mul_le_mul (abs_factor_a_le hh i (IsMu.wt hmu x) _ (hw u) (wt_le_col hs hσ)) (abs_factor_b_le hh (IsMu.wt hmu v) _ (wt_le_col hs hσ) (hw y))
      (abs_nonneg _) (by positivity)
  calc _ ≤ ∑ i ∈ range (2 * h + 1), ∑ σ ∈ ptnsZ (2 * h - s - i), K :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun σ hσ => h1 i hi σ hσ))
    _ = (Rcol h s : ℚ) * K := by
        simp_rw [sum_const, nsmul_eq_mul]
        rw [← sum_mul, ← Nat.cast_sum, card_terms_col]
    _ ≤ Delta h * K := mul_le_mul_of_nonneg_right (by exact_mod_cast Rcol_le_Delta hs) hK0

/-- Δ·(2^{3h}·2^{12h²})·(h!·2^{12h²}) is below 2^{40(h+1)² + ⌈log Δ⌉}, the bound from which c is
chosen. -/
theorem bound_lt_big (h : ℕ) : Delta h * ((2 ^ (3 * h) * 2 ^ (12 * h ^ 2)) * (h.factorial * 2 ^ (12 * h ^ 2))) < 2 ^ ClauseBound.Boson.big h := by
  have a1 : Delta h ≤ 2 ^ Nat.clog 2 (Delta h) := Nat.le_pow_clog (by norm_num) _
  have a2 : h.factorial ≤ 2 ^ (h * h) := (Nat.factorial_le_pow h).trans (by
    rw [pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le h)
  have a3 : 3 * h + 12 * h ^ 2 + (h * h + 12 * h ^ 2) < 40 * (h + 1) ^ 2 := by nlinarith
  have a4 : ClauseBound.Boson.big h = 40 * (h + 1) ^ 2 + Nat.clog 2 (Delta h) := rfl
  calc _ ≤ 2 ^ Nat.clog 2 (Delta h) * ((2 ^ (3 * h) * 2 ^ (12 * h ^ 2)) * (2 ^ (h * h) * 2 ^ (12 * h ^ 2))) :=
        Nat.mul_le_mul a1 (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ a2))
    _ = 2 ^ (Nat.clog 2 (Delta h) + (3 * h + 12 * h ^ 2 + (h * h + 12 * h ^ 2))) := by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    _ < 2 ^ ClauseBound.Boson.big h := Nat.pow_lt_pow_right (by norm_num) (by rw [a4]; linarith)

/-- Hence all values of the pieces are 2^{O(h²)} in absolute value: below the bound from which c is
chosen. -/
theorem abs_A_lt (hP : PieceFacts) (hmu : IsMu lam h mu) (hh : 1 ≤ h) {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) (x y u v : Pieces.Bits lam) :
    |(fam h mu).A s x y u v| < 2 ^ ClauseBound.Boson.big h := by
  have h1 := abs_piece_le hP hmu hh hs x y u v
  rw [← cast_A hP hmu hh] at h1
  have h2 : |(fam h mu).A s x y u v| ≤ ((Delta h * ((2 ^ (3 * h) * 2 ^ (12 * h ^ 2)) * (h.factorial * 2 ^ (12 * h ^ 2))) : ℕ) : ℤ) := by exact_mod_cast h1
  exact h2.trans_lt (by exact_mod_cast bound_lt_big h)

end

end GeneralPieces.ThmHalfPieces

namespace GeneralPieces

open AppHalfPieces Finset GeneralPieces.ThmHalfPieces ClauseBound.Boson.Final

/-- The theorem on the pieces with ρ = 1/√2, with the construction of its proof and without the
running time, from the statements about the ring. -/
theorem thmHalfPiecesPure (hP : AppHalfPieces.PieceFacts) : AppHalfPieces.ThmHalfPiecesPure := by
  obtain ⟨B, C, hB⟩ := ClauseBound.Part.exists_bounds
  obtain ⟨c₁, hbits⟩ := Bits.exists_bits_le hB
  obtain ⟨c₀, hh0⟩ := Bits.exists_hOf_le hB
  obtain ⟨c₂, hall⟩ := Bits.exists_Delta_le hB
  refine ⟨c₁ + 4 + (40 * (c₀ + 1) ^ 2 + c₂), fun lam hl => ?_⟩
  have hbig := big_le (c₁ := c₁) hl (hh0 lam hl) (hall lam hl)
  generalize hc : c₁ + 4 + (40 * (c₀ + 1) ^ 2 + c₂) = c at hbig ⊢
  have hc1 : c₁ ≤ c := by omega
  have hbits := hbits lam hl
  have h2 := (hOfSpec lam).1
  have hp := (hOfSpec lam).2.1
  generalize AppHalfPieces.hOf lam = h at *
  have hh : 1 ≤ h := by omega
  obtain ⟨mu, hmu, -⟩ := Lex.existsUnique_isMu hp
  have hpow : (2 : ℤ) ^ ClauseBound.Boson.big h ≤ 2 ^ (2 * lam) ^ c := pow_le_pow_right₀ (by norm_num) hbig
  have hI : ∀ i ∈ (fam h mu).I, |i| ≤ 2 * (h : ℤ) := fun i hi => by
    obtain ⟨a, b⟩ := mem_Icc.1 hi
    exact abs_le.2 ⟨a, b⟩
  refine ⟨mu, fam h mu, hmu, ?_, rfl, rfl, cast_A hP hmu hh, fun _ => rfl, fun _ => rfl⟩
  exact
    { d_pos := by
        change (1 : ℤ) ≤ (h.factorial : ℤ)
        exact_mod_cast h.factorial_pos
      sum_eq := sum_A hP hmu hh
      row := fun i hi => factorsThrough_mono (row_A hP hmu hh (hI i hi)) hpow
      col := fun i hi => factorsThrough_mono (col_A hP hmu hh (hI i hi)) hpow
      caps := fun i hi => by
        have hL : 0 ≤ Real.logb 2 (2 * (lam : ℝ)) := Real.logb_nonneg one_lt_two (by
          have : (1 : ℝ) ≤ lam := by exact_mod_cast hl
          linarith)
        have hcc : (c₁ : ℝ) * Real.logb 2 (2 * (lam : ℝ)) ≤ (c : ℝ) * Real.logb 2 (2 * (lam : ℝ)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hc1) hL
        exact (hbits i (hI i hi)).trans (by linarith)
      card_I := by
        change #(Icc (-(2 * h : ℤ)) (2 * h)) ≤ _
        rw [Int.card_Icc]
        have := four_mul_add_one_le_big h
        omega
      abs_d := by
        change (h.factorial : ℤ) < _
        exact lt_of_lt_of_le (by exact_mod_cast factorial_lt_two_pow_big h) hpow
      abs_I := fun i hi => by
        have h1 : 2 * h < 2 ^ ClauseBound.Boson.big h :=
          (Nat.lt_two_pow_self (n := 2 * h)).trans_le (Nat.pow_le_pow_right (by norm_num) (by have := four_mul_add_one_le_big h; omega))
        have h3 : (2 * (h : ℤ)) < 2 ^ ClauseBound.Boson.big h := by exact_mod_cast h1
        exact ((hI i hi).trans_lt h3).trans_le hpow
      abs_A := fun i hi x y u v => (abs_A_lt hP hmu hh (hI i hi) x y u v).trans_le hpow }

end GeneralPieces
