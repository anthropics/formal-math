/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import EightSquareStatement
import Mathlib.Tactic

/-! # The functions R and C of four blocks

This file proves, for the functions R and C of four blocks of Section 4 of the paper, the closed
forms R = [x ⊕ y = v ⊕ u]σ(x,y)σ(v,u) and C = [x ⊕ u = v ⊕ y]σ(x,u)σ(v,y), the identity R + C = 2[x =
v][y = u] along the paragraph that begins with «Indeed»,
that R has values in {−1, 0, 1}, and the bounds |R|, |C|, |ψ_k| ≤ 1. The sign rule σ(p,q)σ(p',q') +
σ(p,q')σ(p',q) = 0 (`Eight.Signs`) is a hypothesis `hS` wherever the paper uses it; it is proved in
`SecCrossing_Identity.lean`. -/

public section

namespace Eight

open Finset

/-! ## Signs and ⊕ -/

/-- σ(p,q) is 1 or −1. -/
theorem sigma_eq_or (p q : Block) : sigma p q = 1 ∨ sigma p q = -1 := neg_one_pow_eq_or ℤ _

/-- σ(p,q)² = 1. -/
theorem sigma_mul_self (p q : Block) : sigma p q * sigma p q = 1 := by
  rcases sigma_eq_or p q with h | h <;> rw [h] <;> norm_num

/-- A product of two signs is 1 or −1. -/
theorem sigma_mul_eq_or (p q p' q' : Block) : sigma p q * sigma p' q' = 1 ∨ sigma p q * sigma p' q' = -1 := by
  rcases sigma_eq_or p q with h | h <;> rcases sigma_eq_or p' q' with h' | h' <;> rw [h, h'] <;> norm_num

/-- «Both brackets say x ⊕ y ⊕ u ⊕ v = 000»: x ⊕ y = v ⊕ u says this. -/
theorem bxor_eq_iff_zero (x y u v : Block) : bxor x y = bxor v u ↔ bxor (bxor x y) (bxor u v) = (false, false, false) := by
  obtain ⟨x1, x2, x3⟩ := x; obtain ⟨y1, y2, y3⟩ := y; obtain ⟨u1, u2, u3⟩ := u; obtain ⟨v1, v2, v3⟩ := v
  have h : ∀ a b c d : Bool, (a ^^ b) = (d ^^ c) ↔ ((a ^^ b) ^^ (c ^^ d)) = false := by decide
  simp only [bxor, Prod.mk.injEq, h]

/-- «Both brackets say x ⊕ y ⊕ u ⊕ v = 000»: x ⊕ u = v ⊕ y says this too. -/
theorem bxor_eq_iff_zero' (x y u v : Block) : bxor x u = bxor v y ↔ bxor (bxor x y) (bxor u v) = (false, false, false) := by
  obtain ⟨x1, x2, x3⟩ := x; obtain ⟨y1, y2, y3⟩ := y; obtain ⟨u1, u2, u3⟩ := u; obtain ⟨v1, v2, v3⟩ := v
  have h : ∀ a b c d : Bool, (a ^^ c) = (d ^^ b) ↔ ((a ^^ b) ^^ (c ^^ d)) = false := by decide
  simp only [bxor, Prod.mk.injEq, h]

/-- The two brackets say the same. -/
theorem bxor_eq_swap (x y u v : Block) : bxor x y = bxor v u ↔ bxor x u = bxor v y :=
  (bxor_eq_iff_zero x y u v).trans (bxor_eq_iff_zero' x y u v).symm

/-- «If it holds and y = u, then x = v»: x ⊕ y = v ⊕ y only if x = v. -/
theorem bxor_right_cancel {x v y : Block} (h : bxor x y = bxor v y) : x = v := by
  obtain ⟨x1, x2, x3⟩ := x; obtain ⟨y1, y2, y3⟩ := y; obtain ⟨v1, v2, v3⟩ := v
  have hb : ∀ a b c : Bool, (a ^^ b) = (c ^^ b) → a = c := by decide
  simp only [bxor, Prod.mk.injEq] at h ⊢
  exact ⟨hb _ _ _ h.1, hb _ _ _ h.2.1, hb _ _ _ h.2.2⟩

/-! ## R and C in closed form -/

/-- Σ_k ψ_k(p,q)·ψ_k(p',q') = [p ⊕ q = p' ⊕ q']·σ(p,q)·σ(p',q'): only k = p ⊕ q contributes. -/
theorem sum_psi_mul (p q p' q' : Block) : ∑ k, psi k p q * psi k p' q' = if bxor p q = bxor p' q' then sigma p q * sigma p' q' else 0 := by
  rw [Finset.sum_eq_single (bxor p q)]
  · by_cases h : bxor p q = bxor p' q'
    · simp [psi, h]
    · simp [psi, h, Ne.symm h]
  · intro k _ hk
    simp [psi, Ne.symm hk]
  · simp

/-- «Indeed, R = [x ⊕ y = v ⊕ u]σ(x,y)σ(v,u)». -/
theorem Rb_eq (x y u v : Block) : Rb x y u v = if bxor x y = bxor v u then sigma x y * sigma v u else 0 := sum_psi_mul x y v u

/-- «and C = [x ⊕ u = v ⊕ y]σ(x,u)σ(v,y)». -/
theorem Cb_eq (x y u v : Block) : Cb x y u v = if bxor x u = bxor v y then sigma x u * sigma v y else 0 := sum_psi_mul x u v y

/-- C is R with y and u exchanged; this holds by the definitions. The paper uses it in the words
«column-wise the roles of R and C are exchanged». -/
theorem Cb_eq_Rb (x y u v : Block) : Cb x y u v = Rb x u y v := rfl

/-! ## The three cases of the paragraph «Indeed» -/

/-- «If this fails, all three functions are 0»: R. -/
theorem Rb_of_ne {x y u v : Block} (h : bxor x y ≠ bxor v u) : Rb x y u v = 0 := by rw [Rb_eq, if_neg h]

/-- «If this fails, all three functions are 0»: C. -/
theorem Cb_of_ne {x y u v : Block} (h : bxor x y ≠ bxor v u) : Cb x y u v = 0 := by
  rw [Cb_eq, if_neg fun h' => h ((bxor_eq_swap x y u v).2 h')]

/-- «If this fails, all three functions are 0»: [x = v][y = u]. -/
theorem not_cross_of_ne {x y u v : Block} (h : bxor x y ≠ bxor v u) : ¬(x = v ∧ y = u) := fun ⟨h1, h2⟩ => h (by rw [h1, h2])

/-- «If it holds and y = u, then x = v and R = C = σ(x,y)² = 1»: here with x = v and y = u put in. -/
theorem Rb_diag (x y : Block) : Rb x y y x = 1 := by rw [Rb_eq, if_pos rfl, sigma_mul_self]

/-- «R = C = σ(x,y)² = 1»: C. -/
theorem Cb_diag (x y : Block) : Cb x y y x = 1 := Rb_diag x y

/-- If x ⊕ y = v ⊕ u, then R is 1 or −1. -/
theorem Rb_of_eq {x y u v : Block} (h : bxor x y = bxor v u) : Rb x y u v = 1 ∨ Rb x y u v = -1 := by
  rw [Rb_eq, if_pos h]; exact sigma_mul_eq_or _ _ _ _

/-- «If it holds and y ≠ u, then R + C = 0 by the sign rule with (p,q,p',q') = (x,y,v,u)». -/
theorem Rb_add_Cb_of_ne (hS : Signs) {x y u v : Block} (h : bxor x y = bxor v u) (hyu : y ≠ u) : Rb x y u v + Cb x y u v = 0 := by
  rw [Rb_eq, Cb_eq, if_pos h, if_pos ((bxor_eq_swap x y u v).1 h)]
  exact hS x y v u h hyu

/-- **R + C = 2[x = v][y = u]**, by the three cases of the paragraph «Indeed» of the paper. -/
theorem Rb_add_Cb (hS : Signs) (x y u v : Block) : Rb x y u v + Cb x y u v = 2 * if x = v ∧ y = u then 1 else 0 := by
  by_cases h : bxor x y = bxor v u
  · by_cases hyu : y = u
    · subst hyu
      obtain rfl : x = v := bxor_right_cancel h
      rw [Rb_diag, Cb_diag]; simp
    · rw [Rb_add_Cb_of_ne hS h hyu, if_neg fun h' => hyu h'.2]; rfl
  · rw [Rb_of_ne h, Cb_of_ne h, if_neg (not_cross_of_ne h)]; rfl

/-! ## The values of R and C -/

/-- «Both have values in {−1, 0, 1}»: R. This does not need the sign rule. -/
theorem Rb_val (x y u v : Block) : Rb x y u v = -1 ∨ Rb x y u v = 0 ∨ Rb x y u v = 1 := by
  by_cases h : bxor x y = bxor v u
  · rcases Rb_of_eq h with h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  · exact Or.inr (Or.inl (Rb_of_ne h))

/-- |R| ≤ 1. -/
theorem abs_Rb_le (x y u v : Block) : |Rb x y u v| ≤ 1 := by
  rcases Rb_val x y u v with h | h | h <;> rw [h] <;> norm_num

/-- |C| ≤ 1. -/
theorem abs_Cb_le (x y u v : Block) : |Cb x y u v| ≤ 1 := abs_Rb_le x u y v

/-! ## The bound on ψ -/

/-- |ψ_k(p,q)| ≤ 1. -/
theorem abs_psi_le (k p q : Block) : |psi k p q| ≤ 1 := by
  unfold psi
  split_ifs
  · rcases sigma_eq_or p q with h | h <;> rw [h] <;> norm_num
  · norm_num

end Eight
