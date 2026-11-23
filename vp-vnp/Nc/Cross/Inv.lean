/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cross.Psi

/-!
# Inversion `x ↦ 1/x` exchanges `b` and `d`: the multipliers

Definitions for the step "Reflection" of the proof of Proposition prop:identity (Paper/Identity.lean).
-/

set_option linter.unusedSimpArgs false

namespace Nc.Cross

open Matrix Finset

section inv

variable {R : Type*} [CommRing R] {μ ν : ℕ}

/-- The exchange of the sites `b` and `d`. -/
def exch (μ ν : ℕ) : (Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν) ≃ (Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν) where
  toFun
    | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inr (Sum.inr i) => Sum.inl (Sum.inr i)
  invFun
    | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inr (Sum.inr i) => Sum.inl (Sum.inr i)
  left_inv := by rintro ((i | i) | (i | i)) <;> rfl
  right_inv := by rintro ((i | i) | (i | i)) <;> rfl

/-- The multipliers of the rows (columns) of the matrix at `1/x`: `x^(2i+1)` at `a, c`, `(y−1)y^i` at `d` and `y^(i+1)` at `b`,
with `y = x²`. -/
def scal (x : R) (fa : Fin μ → ℕ) (fb : Fin ν → ℕ) (fc : Fin μ → ℕ) (fd : Fin ν → ℕ) :
    (Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν) → R :=
  Sum.elim (Sum.elim (fun i => x ^ (2 * fa i + 1)) fun i => (x ^ 2 - 1) * (x ^ 2) ^ fd i)
    (Sum.elim (fun i => x ^ (2 * fc i + 1)) fun i => (x ^ 2) ^ (fb i + 1))

/-- The multipliers on the other side: `1 − y` at the new site `d`. -/
def scal' (x : R) : (Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν) → R :=
  Sum.elim (Sum.elim (fun _ => 1) fun _ => 1) (Sum.elim (fun _ => 1) fun _ => 1 - x ^ 2)

/-- The energy of a word. -/
def enW (s : Wd μ) : ℕ := ∑ i, (2 * s.1 i + 1) + ∑ i, (2 * s.2 i + 1)

theorem prod_scal (x : R) (fa : Fin μ → ℕ) (fb : Fin ν → ℕ) (fc : Fin μ → ℕ) (fd : Fin ν → ℕ) :
    ∏ i, scal x fa fb fc fd i = (x ^ 2 - 1) ^ ν *
      x ^ ((∑ i, (2 * fa i + 1)) + (∑ i, (2 * fc i + 1)) + (∑ i, 2 * fd i) + ∑ i, (2 * fb i + 2)) := by
  simp only [scal, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  have e : ∀ i, 2 * (fb i + 1) = 2 * fb i + 2 := fun i => by ring
  simp only [e, pow_add]
  ring

theorem prod_scal' (x : R) :
    ∏ i, (scal' x : (Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν) → R) i = (1 - x ^ 2) ^ ν := by
  simp [scal', Fintype.prod_sum_type]

end inv

end Nc.Cross
