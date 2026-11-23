/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.LowDegree

/-!
# A polynomial along a line

The parts of positive degree of the gates of a circuit, along a line, are power series that satisfy quadratic
equations; `W` sums the coefficients of products of them.
-/

set_option linter.unusedSectionVars false

namespace Nc.Acc

open Finset

variable {F : Type*} [CommRing F] {σ : Type*} {s : ℕ}

/-- `p` along the line through 0 and `u`. -/
noncomputable def line (u : σ → F) : MvPolynomial σ F →ₐ[F] Polynomial F :=
  MvPolynomial.aeval fun l => Polynomial.C (u l) * Polynomial.X

theorem line_coeff_zero (u : σ → F) (p : MvPolynomial σ F) :
    (line u p).coeff 0 = MvPolynomial.constantCoeff p := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have : ((Polynomial.evalRingHom (0 : F)).comp (line u).toRingHom) =
      (MvPolynomial.constantCoeff : MvPolynomial σ F →+* F) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [line]
    · intro i; simp [line]
  exact DFunLike.congr_fun this p

theorem eval_one_line (u : σ → F) (p : MvPolynomial σ F) :
    (line u p).eval 1 = MvPolynomial.eval u p := by
  have : ((Polynomial.evalRingHom (1 : F)).comp (line u).toRingHom) =
      (MvPolynomial.eval u : MvPolynomial σ F →+* F) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [line]
    · intro i; simp [line]
  exact DFunLike.congr_fun this p

/-- The inner part of a product. -/
theorem coeff_mul_succ (a b : Polynomial F) (m : ℕ) :
    (a * b).coeff (m + 1) = a.coeff 0 * b.coeff (m + 1) + b.coeff 0 * a.coeff (m + 1) +
      ∑ j ∈ range m, a.coeff (j + 1) * b.coeff (m - j) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_succ']
  simp only [Nat.sub_zero, Nat.sub_self, Nat.add_sub_add_right]
  ring

end Nc.Acc
