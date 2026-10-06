/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec2.Lemma6

/-!
# Strings, vertices and the coefficients of the encoding

Section 2.3.1. The recursion `Full` works on arrays indexed by strings of variables. This file has
the counts that the later cost estimates use: `7^L` left strings and `7^L` right strings of length
`L`, `10^k` vertices at depth `k` of the recursion tree, and coefficients `φ_λ(s)` and `ψ_λ(t)` in
`{0, ±1}`. The first three follow from the sizes of the alphabets; the last is a finite check. So is
the sentence that each form has at most three nonzero coefficients (`card_support_phi_le`,
`card_support_psi_le`), which no later proof uses. The example in the caption of Figure 3 is
`figure_3`.
-/

public section

open Finset

namespace ThreeSumApsp

/-- Section 2.3.1: an array on the left strings of length `L` "has 7^L entries in total". -/
theorem card_leftStr (L : ℕ) : Fintype.card (LeftStr L) = 7 ^ L := by
  rw [Fintype.card_fun, card_leftVar, Fintype.card_fin]

/-- Section 2.3.1: an array on the right strings of length `L` has `7^L` entries. -/
theorem card_rightStr (L : ℕ) : Fintype.card (RightStr L) = 7 ^ L := by
  rw [Fintype.card_fun, card_rightVar, Fintype.card_fin]

/-- Section 2.3.1: "At depth k there are 10^k vertices"; in particular there are `10^L` leaves. -/
theorem card_vertex (k : ℕ) : Fintype.card (Vertex k) = 10 ^ k := by
  rw [Fintype.card_fun, card_term, Fintype.card_fin]

/-- Section 2.3.1: "φ_λ(s) ∈ {0, ±1}". -/
theorem abs_phi_le_one (lam : Term) (s : LeftVar) : |phi lam s| ≤ 1 := by
  decide +revert

/-- Section 2.3.1: `ψ_λ(t) ∈ {0, ±1}`. -/
theorem abs_psi_le_one (lam : Term) (t : RightVar) : |psi lam t| ≤ 1 := by
  decide +revert

/-- Section 2.3.1: "for each term λ, at most three of the seven values φ_λ(s) are nonzero". -/
theorem card_support_phi_le (lam : Term) : (univ.filter fun s => phi lam s ≠ 0).card ≤ 3 := by
  decide +revert

/-- Section 2.3.1: "and similarly for the seven values ψ_λ(t)". -/
theorem card_support_psi_le (lam : Term) : (univ.filter fun t => psi lam t ≠ 0).card ≤ 3 := by
  decide +revert

/-- A sum over the seven left variables, split into the `x` and the `p`. -/
private theorem sum_leftVar {A : Type*} [AddCommMonoid A] (f : LeftVar → A) :
    ∑ s, f s = ∑ i, f (.x i) + ∑ i, ∑ j, f (.p i j) := by
  rw [← LeftVar.equiv.symm.sum_comp f, Fintype.sum_sum_type, Fintype.sum_prod_type]
  rfl

/-- Figure 3: "For instance, A_{P₃₁} = a_{x₃} - a_{p₁₁} - a_{p₂₁} and
A_{P₀} = -a_{x₁} - a_{x₂} - a_{x₃}."  (Indices are counted from 0 in Lean.) -/
theorem figure_3 {L : ℕ} (a : LeftStr (L + 1) → ℤ) (u' : LeftStr L) :
    encodeStepL (.P 2 0) a u' = sliceAt a (.x 2) u' - sliceAt a (.p 0 0) u' - sliceAt a (.p 1 0) u'
      ∧ encodeStepL .P0 a u'
        = -sliceAt a (.x 0) u' - sliceAt a (.x 1) u' - sliceAt a (.x 2) u' := by
  constructor
  · simp [encodeStepL, sum_leftVar, phi, pHat, xForm, pForm, Fin.sum_univ_two, Pi.single_apply,
      sub_eq_add_neg, add_assoc]
  · simp [encodeStepL, sum_leftVar, phi, xForm, Fin.sum_univ_three, Pi.single_apply,
      sub_eq_add_neg]

end ThreeSumApsp
