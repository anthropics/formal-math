/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.GenF.Products
public import GeneralPieces.GenF.Bra
public import Mathlib.RingTheory.Derivation.Lie

/-! # Lemma 9 (the operators Q_s), proof, paragraph "Generating functions": differentiations commute with each other

The derivations J_n^-(ω_1) of the paper (written J_n^-(u) here, with u in the place of ω_1) of the
polynomials in the t_k commute, because they map every t_k to a constant; so do the operators that
stand beside the variables in A⁻. -/

public section

namespace GeneralPieces.GenF

open GeneralPieces.Series ClauseBound.Boson

/-- J_n^-(u) and J_m^-(u) commute. -/
theorem JmU_comm (n m : ℕ) (p : Vu) : JmU n (JmU m p) = JmU m (JmU n p) := by
  have h : ⁅JmU n, JmU m⁆ = 0 := MvPolynomial.derivation_ext fun k => by
    rw [Derivation.commutator_apply, JmU, JmU, MvPolynomial.mkDerivation_X, MvPolynomial.mkDerivation_X, MvPolynomial.derivation_C, MvPolynomial.derivation_C, sub_zero]
    rfl
  have h' := congrArg (fun D : Derivation Lu Vu Vu => D p) h
  simp only [Derivation.commutator_apply] at h'
  exact sub_eq_zero.1 h'

theorem JmT_comm (n m : ℕ) (f : Tv) : JmT n (JmT m f) = JmT m (JmT n f) := hder_comm (fun a => JmU_comm n m a) f

theorem DD_xi (rd : Bool) {n : ℕ} (hn : 1 ≤ n) : DD rd (xi rd n) = JmT n := sel_xi rd JmT 0 hn

theorem DD_xo (rd : Bool) (n : ℕ) : DD rd (xo rd n) = 0 := by
  rw [DD, sel_xo']
  unfold z0
  split_ifs <;> rfl

theorem DD_eq (rd : Bool) (i : X) : DD rd i = 0 ∨ ∃ n, DD rd i = JmT n := by
  rcases xi_or_xo rd i with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · by_cases hn : n = 0
    · subst hn
      exact Or.inl (sel_xi_zero rd JmT 0)
    · exact Or.inr ⟨n, DD_xi rd (by omega)⟩
  · exact Or.inl (DD_xo rd n)

/-- The operators that stand beside the variables in A⁻ commute. -/
theorem DD_comm (rd : Bool) (i j : X) (a : Tv) : DD rd i (DD rd j a) = DD rd j (DD rd i a) := by
  rcases DD_eq rd i with hi | ⟨n, hi⟩ <;> rcases DD_eq rd j with hj | ⟨m, hj⟩ <;> rw [hi, hj]
  · simp
  · simp
  · exact JmT_comm n m a

end GeneralPieces.GenF
