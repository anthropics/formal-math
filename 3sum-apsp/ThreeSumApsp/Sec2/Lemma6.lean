/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Ring

/-!
# Lemma 6: Schönhage's identity

Sections 2.1 and 2.2. After Strassen's identity (equation (1)), which the paper
recalls, this file treats Schönhage's. It has ten terms `λ`, each the product of a linear form `φ_λ`
in the seven left variables, a linear form `ψ_λ` in the seven right variables and a linear form
`χ_λ` in the ten output variables. Lemma 6 says that `∑_λ φ_λ ψ_λ χ_λ = G + E`, an identity of
polynomials in the 24 variables: `G` holds the outer product and the inner product that are wanted,
and `E` is an error.

* A linear form is the vector of its coefficients. `formL`, `formR` and `formO` turn it into a
  polynomial, and they are linear (`formL_eq_linearCombination` and its two companions).
* The proof of `lemma_6` is the paper's. The coefficient of `z_ij` comes only from the term `P_ij`.
  In the coefficient of `z₀` the products `x_i y_j` cancel, the cross terms vanish because the
  columns of `p̂` and the rows of `q̂` sum to zero (`pHat_column_sum`, `qHat_row_sum`), and what
  remains is the inner product (`sum_pHat_mul_qHat`).
* Second observation after the lemma: every term contributes to `z₀`, and only `P_ij` contributes to
  `z_ij` (`Term.contributes_z0`, `Term.contributes_z_iff`).

The later files on Section 2 use the second observation and the coefficients of the forms; none of
their proofs uses `lemma_6`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-- Equation (1) and the display after it: Strassen's seven products give the product of
two 2 × 2 matrices.  The entries may be blocks, so they are taken in a ring that need not be
commutative. -/
theorem eq_1 {R : Type} [Ring R] (a11 a12 a21 a22 b11 b12 b21 b22 : R) :
    !![a11, a12; a21, a22] * !![b11, b12; b21, b22] =
      !![(a11 + a22) * (b11 + b22) + a22 * (b21 - b11) - (a11 + a12) * b22
            + (a12 - a22) * (b21 + b22),
         a11 * (b12 - b22) + (a11 + a12) * b22;
         (a21 + a22) * b11 + a22 * (b21 - b11),
         (a11 + a22) * (b11 + b22) - (a21 + a22) * b11 + a11 * (b12 - b22)
            + (a21 - a11) * (b11 + b12)] := by
  simp only [Matrix.mul_fin_two, EmbeddingLike.apply_eq_iff_eq, Matrix.vecCons_inj, and_true]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> noncomm_ring

/-! ### The alphabets -/

/-- The left variables, listed: `x i` is `.inl i`, and `p i j` is `.inr (i, j)`. -/
def LeftVar.equiv : LeftVar ≃ Fin 3 ⊕ Fin 2 × Fin 2 where
  toFun
    | .x i => .inl i
    | .p i j => .inr (i, j)
  invFun
    | .inl i => .x i
    | .inr (i, j) => .p i j
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with _ | ⟨_, _⟩ <;> rfl

/-- The right variables, listed: `y j` is `.inl j`, and `q i j` is `.inr (i, j)`. -/
def RightVar.equiv : RightVar ≃ Fin 3 ⊕ Fin 2 × Fin 2 where
  toFun
    | .y j => .inl j
    | .q i j => .inr (i, j)
  invFun
    | .inl j => .y j
    | .inr (i, j) => .q i j
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with _ | ⟨_, _⟩ <;> rfl

/-- The terms, listed: `P i j` is `some (i, j)`, and `P0` is `none`. -/
def Term.equiv : Term ≃ Option (Fin 3 × Fin 3) where
  toFun
    | .P i j => some (i, j)
    | .P0 => none
  invFun
    | some (i, j) => .P i j
    | none => .P0
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with _ | ⟨_, _⟩ <;> rfl

/-- Section 2.2: there are "seven left variables". -/
theorem card_leftVar : Fintype.card LeftVar = 7 := by
  simp [Fintype.card_congr LeftVar.equiv]

/-- Section 2.2: there are "seven right variables". -/
theorem card_rightVar : Fintype.card RightVar = 7 := by
  simp [Fintype.card_congr RightVar.equiv]

/-- Section 2.2: "Schönhage's identity has ten terms". -/
theorem card_term : Fintype.card Term = 10 := by
  simp [Fintype.card_congr Term.equiv]

/-- A sum over the ten terms, split into the `P_ij` and `P₀`. -/
private theorem sum_term {A : Type*} [AddCommMonoid A] (f : Term → A) :
    ∑ lam, f lam = ∑ i, ∑ j, f (.P i j) + f .P0 := by
  rw [← Term.equiv.symm.sum_comp f, Fintype.sum_option, Fintype.sum_prod_type, add_comm]
  rfl

/-! ### Linear forms as polynomials -/

/-- `formL` is the linear map that sends the form consisting of the single variable `s` to the
polynomial `s`. -/
theorem formL_eq_linearCombination (f : LeftVar → ℤ) :
    formL f = Fintype.linearCombination ℤ polyL f := by
  simp only [formL, Fintype.linearCombination_apply, MvPolynomial.smul_eq_C_mul]

/-- `formR` is the linear map that sends the form consisting of the single variable `t` to the
polynomial `t`. -/
theorem formR_eq_linearCombination (f : RightVar → ℤ) :
    formR f = Fintype.linearCombination ℤ polyR f := by
  simp only [formR, Fintype.linearCombination_apply, MvPolynomial.smul_eq_C_mul]

/-- `formO` is the linear map that sends the form consisting of the single variable `z` to the
polynomial `z`. -/
theorem formO_eq_linearCombination (f : OutVar → ℤ) :
    formO f = Fintype.linearCombination ℤ polyO f := by
  simp only [formO, Fintype.linearCombination_apply, MvPolynomial.smul_eq_C_mul]

/-- The form consisting of a single left variable is that variable. -/
theorem formL_single (s : LeftVar) : formL (Pi.single s 1) = polyL s := by
  simp [formL_eq_linearCombination]

/-- The form consisting of a single right variable is that variable. -/
theorem formR_single (t : RightVar) : formR (Pi.single t 1) = polyR t := by
  simp [formR_eq_linearCombination]

/-- The form consisting of a single output variable is that variable. -/
theorem formO_single (z : OutVar) : formO (Pi.single z 1) = polyO z := by
  simp [formO_eq_linearCombination]

/-- Section 2.2, the display of the linear forms: `φ_{P_ij} = x_i + p̂_ij`. -/
theorem formL_phi_P (i j : Fin 3) : formL (phi (.P i j)) = polyL (.x i) + formL (pHat i j) := by
  simp [phi, xForm, formL_eq_linearCombination]

/-- Section 2.2, the display of the linear forms: `ψ_{P_ij} = y_j + q̂_ij`. -/
theorem formR_psi_P (i j : Fin 3) : formR (psi (.P i j)) = polyR (.y j) + formR (qHat i j) := by
  simp [psi, yForm, formR_eq_linearCombination]

/-- Section 2.2, the display of the linear forms: `χ_{P_ij} = z_ij + z₀`. -/
theorem formO_chi_P (i j : Fin 3) : formO (chi (.P i j)) = polyO (.z i j) + polyO .z0 := by
  simp [chi, zForm, z0Form, formO_eq_linearCombination]

/-- Section 2.2, the display of the linear forms: `φ_{P₀} = -(x₁ + x₂ + x₃)`. -/
theorem formL_phi_P0 : formL (phi .P0) = -(polyL (.x 0) + polyL (.x 1) + polyL (.x 2)) := by
  simp [phi, xForm, formL_eq_linearCombination]

/-- Section 2.2, the display of the linear forms: `ψ_{P₀} = y₁ + y₂ + y₃`. -/
theorem formR_psi_P0 : formR (psi .P0) = polyR (.y 0) + polyR (.y 1) + polyR (.y 2) := by
  simp [psi, yForm, formR_eq_linearCombination]

/-- Section 2.2, the display of the linear forms: `χ_{P₀} = z₀`. -/
theorem formO_chi_P0 : formO (chi .P0) = polyO .z0 :=
  formO_single .z0

/-! ### Lemma 6 -/

/-- Section 2.2: "every column of p̂ […] sums to zero". -/
theorem pHat_column_sum (j : Fin 3) : ∑ i, pHat i j = 0 := by
  fin_cases j <;> simp [Fin.sum_univ_three, pHat]

/-- Section 2.2: "every row of q̂ sums to zero". -/
theorem qHat_row_sum (i : Fin 3) : ∑ j, qHat i j = 0 := by
  fin_cases i <;> simp [Fin.sum_univ_three, qHat]

/-- Section 2.2: "Notice that ∑_{i,j=1}^{3} p̂_ij q̂_ij = ∑_{i,j=1}^{2} p_ij q_ij is the desired
inner product." -/
theorem sum_pHat_mul_qHat :
    ∑ i : Fin 3, ∑ j : Fin 3, formL (pHat i j) * formR (qHat i j)
      = ∑ i : Fin 2, ∑ j : Fin 2, polyL (.p i j) * polyR (.q i j) := by
  simp [Fin.sum_univ_three, Fin.sum_univ_two, pHat, qHat, pForm, qForm,
    formL_eq_linearCombination, formR_eq_linearCombination]

/-- **Lemma 6**.  "Summing over the ten terms, ∑_λ φ_λ ψ_λ χ_λ = G + E, where E :=
∑_{i,j=1}^{3} (x_i q̂_ij + p̂_ij y_j + p̂_ij q̂_ij) z_ij."  An identity of polynomials with integer
coefficients in the 24 variables. -/
theorem lemma_6 : ∑ lam, formL (phi lam) * formR (psi lam) * formO (chi lam) = G + E := by
  -- The column sums of p̂ and the row sums of q̂, as identities of polynomials.
  have hcol : ∀ j, ∑ i, formL (pHat i j) = 0 := fun j => by
    simp only [formL_eq_linearCombination, ← map_sum, pHat_column_sum, map_zero]
  have hrow : ∀ i, ∑ j, formR (qHat i j) = 0 := fun i => by
    simp only [formR_eq_linearCombination, ← map_sum, qHat_row_sum, map_zero]
  simp only [Fin.sum_univ_three] at hcol hrow
  -- Write out the ten terms, and write the inner product in G as ∑ p̂_ij q̂_ij.
  simp only [sum_term, formL_phi_P, formR_psi_P, formO_chi_P, formL_phi_P0, formR_psi_P0,
    formO_chi_P0, G, E, ← sum_pHat_mul_qHat, Fin.sum_univ_three]
  -- The coefficients of the z_ij agree term by term.  In the coefficient of z₀ the products x_i y_j
  -- cancel, and the cross terms are ∑_i x_i ∑_j q̂_ij + ∑_j y_j ∑_i p̂_ij = 0.
  linear_combination polyO .z0 * (polyL (.x 0) * hrow 0 + polyL (.x 1) * hrow 1
    + polyL (.x 2) * hrow 2 + polyR (.y 0) * hcol 0 + polyR (.y 1) * hcol 1 + polyR (.y 2) * hcol 2)

/-! ### Which terms contribute to which output variables -/

/-- Section 2.2, second observation: "every term contributes to z₀". -/
@[simp]
theorem Term.contributes_z0 (lam : Term) : lam.Contributes .z0 := by
  cases lam <;> simp [Term.Contributes, chi, zForm, z0Form]

/-- Section 2.2, second observation: "only P_ij contributes to z_ij". -/
@[simp]
theorem Term.contributes_z_iff (lam : Term) (i j : Fin 3) :
    lam.Contributes (.z i j) ↔ lam = .P i j := by
  cases lam <;> simp [Term.Contributes, chi, zForm, z0Form, Pi.single_apply, eq_comm]

/-- The second observation in one statement: a term contributes to `z` if and only if `z` is inner,
that is `z₀`, or the term is `z.privateTerm`, which is `P_ij` for `z = z_ij`. (This is the term that
the private leaf of Section 2.4.3 has at a level with the variable `z`.) -/
theorem Term.contributes_iff (lam : Term) (z : OutVar) :
    lam.Contributes z ↔ z.IsInner ∨ lam = z.privateTerm := by
  decide +revert

/-- A sum over the terms contributing to `z` has the one summand `P_ij` for `z = z_ij`, and runs
over all terms for `z = z₀`. This is how step (4) of the recursions assembles the slice at `z`. -/
theorem Term.sum_contributes {A : Type*} [AddCommMonoid A] (c : Term → A) (z : OutVar) :
    ∑ lam : Term with lam.Contributes z, c lam
      = match z with
        | .z i j => c (.P i j)
        | .z0 => ∑ lam, c lam := by
  cases z with
  | z i j => simp [filter_eq']
  | z0 => simp

/-- Section 2.2: "the χ_λ forms are all sums of output variables (without any minus signs or other
coefficients)". -/
theorem chi_eq_ite (lam : Term) (z : OutVar) :
    chi lam z = if lam.Contributes z then 1 else 0 := by
  decide +revert

end ThreeSumApsp
