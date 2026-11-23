/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cross.Split

/-!
# States, and the terms of the expansion of `det [[X, AΛB],[B'ΛA', Y]]`

The definitions for the step "The coefficients" of the proof of Proposition prop:identity; the step itself is in
Paper/Identity.lean (Paper.prop_identity_schur to Paper.prop_identity_near). In the paper's letters `X = M₁`, `Y = M₂`, `A = F`,
`A' = F′`, `B = G`, `B' = −G′` and `Λ = D`.
-/

set_option linter.unusedSectionVars false

namespace Nc.Cross

open Matrix Finset

/-- The energy `∑ (2i+1)` of a set. -/
def en (S : Finset ℕ) : ℕ := ∑ i ∈ S, (2 * i + 1)

/-- The states of energy at most `E`. -/
def pairs (E : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((range E).powerset ×ˢ (range E).powerset).filter
    fun s => s.1.card = s.2.card ∧ en s.1 + en s.2 ≤ E

theorem lt_of_mem_en {S : Finset ℕ} {E i : ℕ} (h : en S ≤ E) (hi : i ∈ S) : i < E := by
  have : 2 * i + 1 ≤ en S := Finset.single_le_sum (f := fun i => 2 * i + 1) (fun _ _ => Nat.zero_le _) hi
  omega

theorem mem_pairs {E : ℕ} {s : Finset ℕ × Finset ℕ} :
    s ∈ pairs E ↔ s.1.card = s.2.card ∧ en s.1 + en s.2 ≤ E := by
  unfold pairs
  rw [mem_filter, mem_product, mem_powerset, mem_powerset]
  refine ⟨fun h => h.2, fun h => ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, h⟩⟩
  · exact mem_range.2 (lt_of_mem_en (by omega) hi)
  · exact mem_range.2 (lt_of_mem_en (by omega) hi)

section

variable {p q ρ : Type*} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q] [Fintype ρ] [DecidableEq ρ]
variable {R : Type*} [CommRing R]

/-- The upper rows `(X, 0, A, 0)` and `(0, Y, 0, B')` of the big matrix. -/
def topRows (X : Matrix p p R) (A : Matrix p ρ R) (Y : Matrix q q R) (B' : Matrix q ρ R) :
    p ⊕ q → (p ⊕ q) ⊕ (ρ ⊕ ρ) → R :=
  fun i => Sum.elim (fromBlocks X 0 0 Y i) (fromBlocks A 0 0 B' i)

/-- The parts `(0, −B, 0, 0)` and `(−A', 0, 0, 0)` of the lower rows, without the factors from `Λ`. -/
def lowRows (A' : Matrix ρ p R) (B : Matrix ρ q R) : ρ ⊕ ρ → (p ⊕ q) ⊕ (ρ ⊕ ρ) → R :=
  fun r => Sum.elim (-(fromBlocks 0 B A' 0 : Matrix (ρ ⊕ ρ) (p ⊕ q) R) r) 0

/-- The parts of the lower rows with the entry 1. -/
def unitRows : ρ ⊕ ρ → (p ⊕ q) ⊕ (ρ ⊕ ρ) → R :=
  fun r => Sum.elim 0 ((1 : Matrix (ρ ⊕ ρ) (ρ ⊕ ρ) R) r)

/-- The matrix of the term of `T`: in the lower rows in `T` the first part is taken, in the others the entry 1. -/
def termMat (T : Finset (ρ ⊕ ρ)) (X : Matrix p p R) (A : Matrix p ρ R) (A' : Matrix ρ p R)
    (Y : Matrix q q R) (B : Matrix ρ q R) (B' : Matrix q ρ R) :
    Matrix ((p ⊕ q) ⊕ (ρ ⊕ ρ)) ((p ⊕ q) ⊕ (ρ ⊕ ρ)) R :=
  of (Sum.elim (topRows X A Y B') (T.piecewise (lowRows A' B) unitRows))

/-- Columns of the first group. -/
def cgrp : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop
  | Sum.inl (Sum.inl _) => True
  | Sum.inl (Sum.inr _) => False
  | Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inr _) => False

/-- Rows of the first group. -/
def rgrp (T : Finset (ρ ⊕ ρ)) : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop
  | Sum.inl (Sum.inl _) => True
  | Sum.inl (Sum.inr _) => False
  | Sum.inr (Sum.inl r) => Sum.inl r ∉ T
  | Sum.inr (Sum.inr r) => Sum.inr r ∈ T

instance : DecidablePred (cgrp : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop) := fun i =>
  match i with
  | Sum.inl (Sum.inl _) => isTrue trivial
  | Sum.inl (Sum.inr _) => isFalse id
  | Sum.inr (Sum.inl _) => isTrue trivial
  | Sum.inr (Sum.inr _) => isFalse id

instance (T : Finset (ρ ⊕ ρ)) : DecidablePred (rgrp T : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop) := fun i =>
  match i with
  | Sum.inl (Sum.inl _) => isTrue trivial
  | Sum.inl (Sum.inr _) => isFalse id
  | Sum.inr (Sum.inl r) => inferInstanceAs (Decidable (Sum.inl r ∉ T))
  | Sum.inr (Sum.inr r) => inferInstanceAs (Decidable (Sum.inr r ∈ T))

/-- The matrix of a term falls into two blocks: one made of `X, A, A'` and one made of `Y, B, B'`. -/
theorem termMat_eq_glue (T : Finset (ρ ⊕ ρ)) (X : Matrix p p R) (A : Matrix p ρ R) (A' : Matrix ρ p R)
    (Y : Matrix q q R) (B : Matrix ρ q R) (B' : Matrix q ρ R) :
    termMat T X A A' Y B B' =
      glueMat (rgrp T) cgrp (termMat T X A A' 0 0 0) (termMat T 0 0 0 Y B B') := by
  ext i j
  rcases i with (i | i) | (i | i)
  · rcases j with (j | j) | (j | j) <;> simp [termMat, glueMat, rgrp, cgrp, topRows]
  · rcases j with (j | j) | (j | j) <;> simp [termMat, glueMat, rgrp, cgrp, topRows]
  · by_cases hi : Sum.inl i ∈ T <;> rcases j with (j | j) | (j | j) <;>
      simp [termMat, glueMat, rgrp, cgrp, lowRows, unitRows, hi]
  · by_cases hi : Sum.inr i ∈ T <;> rcases j with (j | j) | (j | j) <;>
      simp [termMat, glueMat, rgrp, cgrp, lowRows, unitRows, hi]

theorem card_cgrp : (univ.filter (cgrp : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop)).card =
    Fintype.card p + Fintype.card ρ := by
  have h : univ.filter (cgrp : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop) =
      disjSum (disjSum univ ∅) (disjSum univ ∅) := by
    ext i
    rcases i with (i | i) | (i | i) <;> simp [cgrp]
  rw [h]
  simp [Finset.card_univ]

theorem card_rgrp (T : Finset (ρ ⊕ ρ)) :
    (univ.filter (rgrp T : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop)).card + T.toLeft.card =
    Fintype.card p + Fintype.card ρ + T.toRight.card := by
  have h : univ.filter (rgrp T : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop) =
      disjSum (disjSum univ ∅) (disjSum T.toLeftᶜ T.toRight) := by
    ext i
    rcases i with (i | i) | (i | i) <;> simp [rgrp]
  rw [h]
  have := Finset.card_add_card_compl T.toLeft
  simp only [card_disjSum, Finset.card_univ, card_empty]
  omega

end

section coeff

open Polynomial

/-- The paper's `E(T)`, for `T = (T₁, T₂)`. -/
def enT {K : ℕ} (T : Finset (Fin K ⊕ Fin K)) : ℕ :=
  ∑ r ∈ T, Sum.elim (fun r : Fin K => 2 * (r : ℕ) + 1) (fun r : Fin K => 2 * (r : ℕ) + 1) r

/-- The `T` with `|T₁| = |T₂|` and `E(T) ≤ N`: the terms that contribute to the coefficient of `x^N`. -/
def goodT (K N : ℕ) : Finset (Finset (Fin K ⊕ Fin K)) :=
  univ.filter fun T => T.toLeft.card = T.toRight.card ∧ enT T ≤ N

end coeff

end Nc.Cross
