/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec5.Corollary40

/-!
# The output of uMv-hinted uMv, in terms of integer matrix products

Proof of Corollary 40: "We compute over ℤ with 0/1 matrices; a Boolean entry is 1 exactly when the
corresponding integer entry is positive."  A data structure for thin matrix products returns entries
of integer products.  The output `(U N_{I,J} V)_{i,j}` of uMv-hinted uMv is true exactly if, for
some `ℓ` with `V[ℓ, j] = 1`, the entry `(i, ℓ)` of the integer product `U N_{I,J}` is not 0
(`uMvHintedOutput_eq`).

The paper cuts "the n rows of U into n/t₂ blocks of t₂ rows".  `rowsFrom X s t` is the block of the
`t` rows of `X` from the row `s` on; the entries of its product with `Y` are entries of `X Y`
(`rowsFrom_mul`).  The data structure asks for a bound on the entries of its inputs;
`Corollary40.abs_toInt_le` and `abs_rowsFrom_le` give it.
-/

@[expose] public section

namespace ThreeSumApsp.Spec.Sec5

open HintedMv

/-! ## 0/1 matrices -/

section
variable {p q r : ℕ} (M : Matrix (Fin p) (Fin q) Bool) (V : Matrix (Fin q) (Fin r) Bool)

/-- An entry of a Boolean product is true exactly if the entry of the integer product is not 0. -/
private theorem boolMul_eq_true_iff_ne_zero (i : Fin p) (j : Fin r) :
    boolMul M V i j = true ↔ (toInt M * toInt V) i j ≠ 0 := by
  have hnonneg : 0 ≤ (toInt M * toInt V) i j := by
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (Corollary40.toInt_nonneg M i k)
      (Corollary40.toInt_nonneg V k j)
  rw [Corollary40.boolMul_eq_true_iff_pos]
  omega

end

/-! ## The output of uMv-hinted uMv -/

/-- "In Phase 4, (U N_{I,J} V)_{i,j} = ∑_{ℓ=1}^{t₂} (U N_{I,J})_{i,ℓ} V_{ℓ,j} is a sum of at most t₂
entries of XY".  The output is true exactly if for some `ℓ` with `V[ℓ, j] = 1` the entry `(i, ℓ)` of
`U N_{I,J}` is not 0. -/
theorem uMvHintedOutput_eq {n t₁ t₂ : ℕ} (U : Matrix (Fin n) (Fin t₁) Bool)
    (N : Matrix (Fin n) (Fin n) Bool) (V : Matrix (Fin t₂) (Fin n) Bool) (I : Fin t₁ → Fin n)
    (J : Fin t₂ → Fin n) (i j : Fin n) :
    uMvHintedOutput U N V I J i j
      = decide (∃ ℓ : Fin t₂, toInt V ℓ j = 1 ∧ (toInt U * (toInt N).submatrix I J) i ℓ ≠ 0) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, uMvHintedOutput, Corollary40.boolMul_eq_true]
  refine exists_congr fun ℓ => ?_
  rw [boolMul_eq_true_iff_ne_zero, Corollary40.toInt_eq_one_iff]
  -- The 0/1 matrix of `N_{I,J}` is the submatrix of the 0/1 matrix of `N`, by definition.
  exact and_comm

/-! ## Blocks of rows -/

section
variable {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℤ) (s t : ℕ) (h : s + t ≤ n)

/-- The `t` rows of a matrix from the row `s` on. -/
def rowsFrom : Matrix (Fin t) (Fin k) ℤ :=
  fun a b => X ⟨s + a.val, by have := a.isLt; omega⟩ b

/-- An entry of the product of a block of rows with `Y` is an entry of `XY`. -/
theorem rowsFrom_mul {r : ℕ} (Y : Matrix (Fin k) (Fin r) ℤ) (a : Fin t) (ℓ : Fin r) :
    (rowsFrom X s t h * Y) a ℓ = (X * Y) ⟨s + a.val, by have := a.isLt; omega⟩ ℓ := by
  simp only [Matrix.mul_apply, rowsFrom]

end

/-- A bound on the entries of a matrix bounds the entries of a block of its rows. -/
theorem abs_rowsFrom_le {n k : ℕ} {X : Matrix (Fin n) (Fin k) ℤ} {B : ℤ} (hX : ∀ i j, |X i j| ≤ B)
    (s t : ℕ) (h : s + t ≤ n) (a : Fin t) (b : Fin k) : |rowsFrom X s t h a b| ≤ B :=
  hX _ _

end ThreeSumApsp.Spec.Sec5
