/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements

/-!
# Corollary 40: the hinted Mv conjectures

Conjectures 5.2 and 5.7 of [vdBNS19] fail for `0 < τ < 1/18` (Phase 2 in `O(n^{2-0.063τ})` time,
Phase 3 in `O(n^{1+0.437τ})`) and Conjecture 5.12 for `0 < τ₁ < τ₂/18`, because the data structure
of Corollary 26 answers the last phase by queries; with smaller savings they fail up to `ε*`.
Running times are not defined here.  This file proves the parts of the proof that are not running
times.
* "We compute over ℤ with 0/1 matrices; a Boolean entry is 1 exactly when the corresponding integer
  entry is positive" (`boolMul_eq_true_iff_pos`).  So the outputs of the first two problems are
  signs of entries of an integer product `XY` (`vHintedOutput_eq_true_iff`,
  `MvHintedOutput_eq_true_iff`).  For Conjecture 5.12 the product is cut into blocks of rows
  (`mul_apply_eq_blockOfRows_mul`).
* "In each case the phases beat the conjectured bounds": running times with exponents below all the
  bounds of a conjecture refute it (`not_conjecture52_of_achieves`,
  `not_conjecture57_of_achieves`, `not_conjecture512_of_achieves`).
* The variant with a sparse matrix as the hint (Section 5.4) is again a product with a small inner
  dimension (`boolMul_boolMul_eq_boolMul_submatrix`).

Nothing else rests on `mul_apply_eq_blockOfRows_mul` and `boolMul_boolMul_eq_boolMul_submatrix`.
-/

public section

namespace ThreeSumApsp

open Finset HintedMv

namespace Corollary40

/-! ### Boolean products from integer products -/

/-- An entry of a Boolean product is true exactly if some term of it is. -/
theorem boolMul_eq_true {l m r : ℕ} (M : Matrix (Fin l) (Fin m) Bool)
    (V : Matrix (Fin m) (Fin r) Bool) (i : Fin l) (j : Fin r) :
    boolMul M V i j = true ↔ ∃ k, M i k = true ∧ V k j = true := by
  simp only [boolMul, decide_eq_true_eq]

/-- An entry of the 0/1 matrix of a Boolean matrix is 1 exactly if the Boolean entry is true. -/
theorem toInt_eq_one_iff {l m : ℕ} (M : Matrix (Fin l) (Fin m) Bool) (i : Fin l) (j : Fin m) :
    toInt M i j = 1 ↔ M i j = true := by
  cases h : M i j <;> simp [toInt, h]

/-- The entries of a 0/1 matrix are not negative. -/
theorem toInt_nonneg {l m : ℕ} (M : Matrix (Fin l) (Fin m) Bool) (i : Fin l) (j : Fin m) :
    0 ≤ toInt M i j := by
  cases h : M i j <;> simp [toInt, h]

/-- The entries of a 0/1 matrix are at most 1 in absolute value. -/
theorem abs_toInt_le {l m : ℕ} (M : Matrix (Fin l) (Fin m) Bool) (i : Fin l) (j : Fin m) :
    |toInt M i j| ≤ 1 := by
  cases h : M i j <;> simp [toInt, h]

/-- A term of a product of 0/1 matrices is 0 or 1, and it is 1 exactly if both entries are true. -/
private theorem toInt_mul_toInt {l m r : ℕ} (M : Matrix (Fin l) (Fin m) Bool)
    (V : Matrix (Fin m) (Fin r) Bool) (i : Fin l) (j : Fin r) (k : Fin m) :
    0 ≤ toInt M i k * toInt V k j ∧
      (0 < toInt M i k * toInt V k j ↔ M i k = true ∧ V k j = true) := by
  cases hM : M i k <;> cases hV : V k j <;> simp [toInt, hM, hV]

/-- Proof of Corollary 40: "We compute over ℤ with 0/1 matrices; a Boolean entry is 1 exactly when
the corresponding integer entry is positive." -/
theorem boolMul_eq_true_iff_pos {l m r : ℕ} (M : Matrix (Fin l) (Fin m) Bool)
    (V : Matrix (Fin m) (Fin r) Bool) (i : Fin l) (j : Fin r) :
    boolMul M V i j = true ↔ 0 < (toInt M * toInt V) i j := by
  rw [boolMul_eq_true, Matrix.mul_apply,
    sum_pos_iff_of_nonneg fun k _ => (toInt_mul_toInt M V i j k).1]
  simp only [mem_univ, true_and, (toInt_mul_toInt M V i j _).2]

/-- Proof of Corollary 40, paragraph "Conjecture 5.2 of [vdBNS19]": "we preprocess X := M and Y := V
...  In Phase 3, the n entries of column i of MV are n queries". -/
theorem vHintedOutput_eq_true_iff {n t : ℕ} (M : Matrix (Fin n) (Fin t) Bool)
    (V : Matrix (Fin t) (Fin n) Bool) (i r : Fin n) :
    vHintedOutput M V i r = true ↔ 0 < (toInt M * toInt V) r i :=
  boolMul_eq_true_iff_pos M V r i

/-- Proof of Corollary 40, paragraph "Conjecture 5.7 of [vdBNS19]": "The proof is the same, with
X := N_{[n],I} and Y := V, which are both known in Phase 2 (X may have repeated columns, which do
not affect the argument)." -/
theorem MvHintedOutput_eq_true_iff {n t : ℕ} (N : Matrix (Fin n) (Fin n) Bool)
    (V : Matrix (Fin t) (Fin n) Bool) (I : Fin t → Fin n) (j r : Fin n) :
    MvHintedOutput N V I j r = true ↔ 0 < (toInt (N.submatrix id I) * toInt V) r j :=
  boolMul_eq_true_iff_pos (N.submatrix id I) V r j

/-- Proof of Corollary 40, paragraph "Conjecture 5.12 of [vdBNS19]": "Cut the n rows of U into n/t₂
blocks of t₂ rows, and preprocess each of the n/t₂ products of a block with Y, which are products of
a t₂ × t₁ matrix by a t₁ × t₂ matrix". Here n = b * t₂.  Every entry of XY is an entry of one of
these products. -/
theorem mul_apply_eq_blockOfRows_mul {b t₁ t₂ : ℕ} (X : Matrix (Fin (b * t₂)) (Fin t₁) ℤ)
    (Y : Matrix (Fin t₁) (Fin t₂) ℤ) (p : Fin b) (i l : Fin t₂) :
    (X * Y) (finProdFinEquiv (p, i)) l = (blockOfRows X p * Y) i l :=
  rfl

end Corollary40

/-! ### From the running times to "the conjecture fails"

Running times are not defined in this file.  See `Conjecture52` for the meaning of `Achieves`;
`hmono` says that an algorithm that meets a time bound meets every larger one. -/

/-- Corollary 40: "In each case the phases beat the conjectured bounds".  An algorithm whose
exponents `a₂`, `a₃` are below the bounds `ω` and `1 + τ` of Conjecture 5.2 refutes it: `ε` is the
smaller margin.  In Corollary 40, `a₂` is `2 - 0.063τ` or `2 - γτ`, which is below `ω` "whatever the
value of ω, since ω(1,1,τ) = ω(1,τ,1) ≥ 2", and `a₃` is `1 + 0.437τ` or `1 + τ/2`. -/
theorem not_conjecture52_of_achieves {Achieves : ℝ → ℝ → Prop}
    (hmono : ∀ ⦃a₂ a₃ a₂' a₃'⦄, Achieves a₂ a₃ → a₂ ≤ a₂' → a₃ ≤ a₃' → Achieves a₂' a₃')
    {ω τ a₂ a₃ : ℝ} (h₂ : a₂ < ω) (h₃ : a₃ < 1 + τ) (h : Achieves a₂ a₃) :
    ¬ Conjecture52 Achieves ω τ := by
  obtain ⟨ε, hε, hε₂, hε₃⟩ : ∃ ε > 0, ε ≤ ω - a₂ ∧ ε ≤ 1 + τ - a₃ :=
    ⟨min (ω - a₂) (1 + τ - a₃), lt_min (sub_pos.2 h₂) (sub_pos.2 h₃), min_le_left _ _,
      min_le_right _ _⟩
  exact fun hc => hc ε hε (hmono h (by linarith) (by linarith))

/-- Corollary 40: "In each case the phases beat the conjectured bounds".  Conjecture 5.7 has the two
bounds of Conjecture 5.2 for another problem, so `not_conjecture52_of_achieves` applies. -/
theorem not_conjecture57_of_achieves {Achieves : ℝ → ℝ → Prop}
    (hmono : ∀ ⦃a₂ a₃ a₂' a₃'⦄, Achieves a₂ a₃ → a₂ ≤ a₂' → a₃ ≤ a₃' → Achieves a₂' a₃')
    {ω τ a₂ a₃ : ℝ} (h₂ : a₂ < ω) (h₃ : a₃ < 1 + τ) (h : Achieves a₂ a₃) :
    ¬ Conjecture57 Achieves ω τ :=
  not_conjecture52_of_achieves hmono h₂ h₃ h

/-- Corollary 40: "In each case the phases beat the conjectured bounds", for the three bounds `ω₂`,
`ω₃`, `τ₁ + τ₂` of Conjecture 5.12.  In Corollary 40, Phase 2 only stores `I`, so `a₂ = τ₁`, and `τ₁
< ω(1,τ₁,1)` has to hold as well.  It does, since `τ₁ < 1` (Section 5.4) and `ω(1,τ₁,1) ≥ 2`. The
other two exponents are `1 + τ₂ - 0.063τ₁` or `1 + τ₂ - γτ₁`, below `ω(τ₂,τ₁,1) ≥ 1 + τ₂`, and `τ₂ +
0.437τ₁` or `τ₂ + τ₁/2`. -/
theorem not_conjecture512_of_achieves {Achieves : ℝ → ℝ → ℝ → Prop}
    (hmono : ∀ ⦃a₂ a₃ a₄ a₂' a₃' a₄'⦄, Achieves a₂ a₃ a₄ → a₂ ≤ a₂' → a₃ ≤ a₃' → a₄ ≤ a₄' →
      Achieves a₂' a₃' a₄')
    {ω₂ ω₃ τ₁ τ₂ a₂ a₃ a₄ : ℝ} (h₂ : a₂ < ω₂) (h₃ : a₃ < ω₃) (h₄ : a₄ < τ₁ + τ₂)
    (h : Achieves a₂ a₃ a₄) : ¬ Conjecture512 Achieves ω₂ ω₃ τ₁ τ₂ := by
  obtain ⟨ε, hε, hε₂, hε₃, hε₄⟩ : ∃ ε > 0, ε ≤ ω₂ - a₂ ∧ ε ≤ ω₃ - a₃ ∧ ε ≤ τ₁ + τ₂ - a₄ :=
    ⟨min (ω₂ - a₂) (min (ω₃ - a₃) (τ₁ + τ₂ - a₄)),
      lt_min (sub_pos.2 h₂) (lt_min (sub_pos.2 h₃) (sub_pos.2 h₄)), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  exact fun hc => hc ε hε (hmono h (by linarith) (by linarith) (by linarith))

/-! ### The discussion after Corollary 40 -/

/-- Section 5.4, on the variant of Conjecture 5.7 in [vdBSZ24] "in which Phase 2 gives a matrix with
at most n^τ nonzero entries instead of the vector I.  Our proof applies to this variant as well,
since after Phase 2 the product again has inner dimension at most n^τ".  In that variant M, P, V are
n × n Boolean matrices and the output is a column of M P V.  If the nonzero entries of P are at the
t positions (a_k, b_k), then M P V is the product of the n × t matrix of the columns a_k of M and
the t × n matrix of the rows b_k of V. -/
theorem boolMul_boolMul_eq_boolMul_submatrix {n t : ℕ} (M P V : Matrix (Fin n) (Fin n) Bool)
    (a b : Fin t → Fin n) (hP : ∀ i j, P i j = true ↔ ∃ k, a k = i ∧ b k = j) :
    boolMul (boolMul M P) V = boolMul (M.submatrix id a) (V.submatrix b id) := by
  funext i j
  rw [Bool.eq_iff_iff]
  simp only [Corollary40.boolMul_eq_true, Matrix.submatrix_apply, id_eq]
  constructor
  · rintro ⟨l, ⟨k', hM, hPk⟩, hV⟩
    obtain ⟨k, rfl, rfl⟩ := (hP k' l).mp hPk
    exact ⟨k, hM, hV⟩
  · rintro ⟨k, hM, hV⟩
    exact ⟨b k, ⟨a k, hM, (hP _ _).mpr ⟨k, rfl, rfl⟩⟩, hV⟩

end ThreeSumApsp
