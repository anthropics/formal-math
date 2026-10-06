/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec2.Lemma6

/-!
# Lemmas 7 and 8: what `Full` computes

Section 2.3.2. Lemma 7: at the leaf `τ`, `Full(a, b)` multiplies `Φ_τ(a)` by
`Ψ_τ(b)`, and it returns `Mult(a, b)`, whose entry at `w` is the sum of these products over the
leaves contributing to `w` (equation (2)). Lemma 8:
`Mult(a, b)[w] = ∑_{u,v} γ(u₁, v₁, w₁) ⋯ γ(u_L, v_L, w_L) a[u] b[v]`, with the `γ` of equation (3).

* `Φ_τ` and `Ψ_τ` are the same expression for two families of linear forms (`encodeWith`), so what
  holds for both is proved once.
* Lemma 7 is proved by induction on `L`, as in the paper. Step (2) is the encoding:
  `Φ_{λτ'}(a) = Φ_{τ'}(A_λ)` and `Ψ_{λτ'}(b) = Ψ_{τ'}(B_λ)` (`Phi_cons`, `Psi_cons`). Step (4) is
  the decoding: the leaves contributing to `z w'` are the `λτ'` with `λ` contributing to `z` and
  `τ'` to `w'` (`Leaf.contributes_succ`), so `Full` and `Mult` both satisfy
  `c[z w'] = ∑_{λ contributing to z} C_λ[w']` (`Full_succ`, `Mult_succ`).
* Lemma 8: the leaves contributing to `w` choose a term contributing to `w_ℓ` independently at each
  level `ℓ` (`Leaf.filter_contributes_eq_piFinset`), so the sum over these leaves of a product over
  the levels is a product of sums (`prod_gamma_eq_sum_contributes`).
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### Which leaves contribute to an output string -/

/-- In the proof of Lemma 7: "the leaves contributing to zw' are the λτ' with λ
contributing to z and τ' contributing to w'".  Here `λ = τ 0`, `τ' = Fin.tail τ`, `z = w 0` and
`w' = Fin.tail w`. -/
theorem Leaf.contributes_succ {L : ℕ} {τ : Leaf (L + 1)} {w : OutStr (L + 1)} :
    Leaf.Contributes τ w
      ↔ (τ 0).Contributes (w 0) ∧ Leaf.Contributes (Fin.tail τ) (Fin.tail w) := by
  simp only [Leaf.Contributes, Fin.forall_fin_succ, Fin.tail]

/-- A sum over the strings of length `L + 1` is a sum over the first variable `s` and the rest `u'`
of the string `s u'`. -/
private theorem sum_strings_succ {α : Type*} [Fintype α] {L : ℕ} (f : (Fin (L + 1) → α) → ℤ) :
    ∑ u, f u = ∑ s, ∑ u', f (Fin.cons s u') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => α) _ _ fun _ => rfl).symm

/-- A sum over the leaves contributing to `w`, split by the first term of the leaf. -/
theorem Leaf.sum_contributes_succ {L : ℕ} (w : OutStr (L + 1)) (f : Leaf (L + 1) → ℤ) :
    ∑ τ : Leaf (L + 1) with Leaf.Contributes τ w, f τ
      = ∑ lam : Term with lam.Contributes (w 0),
          ∑ τ' : Leaf L with Leaf.Contributes τ' (Fin.tail w), f (Fin.cons lam τ') := by
  simp only [sum_filter, sum_strings_succ, Leaf.contributes_succ, Fin.cons_zero,
    Fin.tail_cons]
  refine sum_congr rfl fun lam _ => ?_
  by_cases h : lam.Contributes (w 0) <;> simp [h]

/-- In the proof of Lemma 8: the leaves contributing to `w` "are the leaves whose term at
level ℓ contributes to w_ℓ, independently for each ℓ". -/
theorem Leaf.filter_contributes_eq_piFinset {L : ℕ} (w : OutStr L) :
    (univ.filter fun τ : Leaf L => Leaf.Contributes τ w)
      = Fintype.piFinset fun ℓ => univ.filter fun lam : Term => lam.Contributes (w ℓ) := by
  ext τ
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  rfl

/-- Membership in `Leaves(U)`. -/
@[simp]
theorem mem_Leaves {L : ℕ} {U : Finset (OutStr L)} {τ : Leaf L} :
    τ ∈ Leaves U ↔ ∃ w ∈ U, Leaf.Contributes τ w := by
  simp [Leaves]

/-! ### The two encodings at once -/

section encodeWith

variable {α : Type} [Fintype α] (c : Term → α → ℤ) {L : ℕ}

/-- The number `∑_u a[u] ∏_ℓ c_{τ_ℓ}(u_ℓ)`, for an array `a` on the strings over a finite alphabet
and the coefficients `c` of a family of linear forms, one for each term. By definition it is
`Φ_τ(a)` for `c = φ` and `Ψ_τ(b)` for `c = ψ`. -/
def encodeWith (τ : Leaf L) (a : (Fin L → α) → ℤ) : ℤ := ∑ u, a u * ∏ ℓ, c (τ ℓ) (u ℓ)

/-- For `L = 0` the only string is empty, and so are the products over the levels. -/
theorem encodeWith_zero (τ : Leaf 0) (a : (Fin 0 → α) → ℤ) : encodeWith c τ a = a Fin.elim0 := by
  simp [encodeWith, Subsingleton.elim (default : Fin 0 → α) Fin.elim0]

/-- The number at the leaf `λτ'` for `a` is the number at the leaf `τ'` for `∑_s c_λ(s) a_s`. -/
theorem encodeWith_cons (lam : Term) (τ' : Leaf L) (a : (Fin (L + 1) → α) → ℤ) :
    encodeWith c (Fin.cons lam τ' : Leaf (L + 1)) a
      = encodeWith c τ' fun u' => ∑ s, c lam s * sliceAt a s u' := by
  simp only [encodeWith, sum_strings_succ, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    sliceAt, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun u' _ => sum_congr rfl fun s _ => by ring

end encodeWith

/-! ### Lemma 7 -/

/-- In the proof of Lemma 7: "for every leaf λτ' we have
Φ_{λτ'}(a) = ∑_s φ_λ(s) Φ_{τ'}(a_s) = Φ_{τ'}(A_λ)". -/
theorem Phi_cons {L : ℕ} (lam : Term) (τ' : Leaf L) (a : LeftStr (L + 1) → ℤ) :
    Phi (Fin.cons lam τ' : Leaf (L + 1)) a = Phi τ' (encodeStepL lam a) :=
  encodeWith_cons phi lam τ' a

/-- In the proof of Lemma 7: "and similarly Ψ_{λτ'}(b) = Ψ_{τ'}(B_λ)". -/
theorem Psi_cons {L : ℕ} (lam : Term) (τ' : Leaf L) (b : RightStr (L + 1) → ℤ) :
    Psi (Fin.cons lam τ' : Leaf (L + 1)) b = Psi τ' (encodeStepR lam b) :=
  encodeWith_cons psi lam τ' b

/-- "For L = 0, the only leaf is the empty string τ, and Φ_τ(a) = a […], as the products over the
levels are empty" (proof of Lemma 7). -/
private theorem Phi_zero (τ : Leaf 0) (a : LeftStr 0 → ℤ) : Phi τ a = a Fin.elim0 :=
  encodeWith_zero phi τ a

/-- "and Ψ_τ(b) = b" (proof of Lemma 7). -/
private theorem Psi_zero (τ : Leaf 0) (b : RightStr 0 → ℤ) : Psi τ b = b Fin.elim0 :=
  encodeWith_zero psi τ b

/-- **Lemma 7**, first half.  "At the leaf τ, Full(a, b) multiplies Φ_τ(a) by Ψ_τ(b)". -/
theorem Lemma7.multiplied_at_leaf {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (τ : Leaf L) :
    Full.multipliedAt L a b τ = (Phi τ a, Psi τ b) := by
  induction L with
  | zero =>
    rw [Phi_zero, Psi_zero]
    rfl
  | succ L ih =>
    -- The leaf `τ` is `λ τ'` with `λ = τ 0` and `τ' = Fin.tail τ`. By steps (2) and (3) it is the
    -- leaf `τ'` of `Full(A_λ, B_λ)`.
    have hstep : Full.multipliedAt (L + 1) a b τ
        = Full.multipliedAt L (encodeStepL (τ 0) a) (encodeStepR (τ 0) b) (Fin.tail τ) := rfl
    rw [hstep, ih, ← Phi_cons, ← Psi_cons, Fin.cons_self_tail]

/-- Step (4) of `Full`, as it is read in the proof of Lemma 7:
`c[z w'] = ∑_{λ contributing to z} C_λ[w']`. -/
theorem Full_succ {L : ℕ} (a : LeftStr (L + 1) → ℤ) (b : RightStr (L + 1) → ℤ)
    (w : OutStr (L + 1)) :
    Full (L + 1) a b w = ∑ lam : Term with lam.Contributes (w 0),
      Full L (encodeStepL lam a) (encodeStepR lam b) (Fin.tail w) := by
  rw [Term.sum_contributes]
  rfl

/-- In the proof of Lemma 7:
`Mult(a, b)[z w'] = ∑_{λ contributing to z} Mult(A_λ, B_λ)[w']`. -/
theorem Mult_succ {L : ℕ} (a : LeftStr (L + 1) → ℤ) (b : RightStr (L + 1) → ℤ)
    (w : OutStr (L + 1)) :
    Mult a b w = ∑ lam : Term with lam.Contributes (w 0),
      Mult (encodeStepL lam a) (encodeStepR lam b) (Fin.tail w) := by
  simp only [Mult, Leaf.sum_contributes_succ, Phi_cons, Psi_cons]

/-- **Lemma 7**, second half.  "and it returns Mult(a, b)." -/
theorem Lemma7.returns_Mult {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) :
    Full L a b = Mult a b := by
  induction L with
  | zero =>
    funext w
    simp [Full, Full.run, Mult, Leaf.Contributes, Phi_zero, Psi_zero]
  | succ L ih =>
    funext w
    simp only [Full_succ, Mult_succ, ih]

/-- **Lemma 7**.  "At the leaf τ, Full(a, b) multiplies Φ_τ(a) by Ψ_τ(b), and it returns
Mult(a, b)." -/
theorem lemma_7 {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) :
    (∀ τ : Leaf L, Full.multipliedAt L a b τ = (Phi τ a, Psi τ b)) ∧ Full L a b = Mult a b :=
  ⟨Lemma7.multiplied_at_leaf a b, Lemma7.returns_Mult a b⟩

/-! ### Lemma 8 -/

/-- The display in the proof of Lemma 8: the sum, over the leaves `τ` contributing
to `w`, of `∏_ℓ φ_{τ_ℓ}(u_ℓ) ψ_{τ_ℓ}(v_ℓ)` "is the product of sums ∏_ℓ ∑_{τ_ℓ contributing to w_ℓ}
φ_{τ_ℓ}(u_ℓ) ψ_{τ_ℓ}(v_ℓ) = ∏_ℓ γ(u_ℓ, v_ℓ, w_ℓ) by (3)". -/
theorem prod_gamma_eq_sum_contributes {L : ℕ} (u : LeftStr L) (v : RightStr L) (w : OutStr L) :
    ∏ ℓ, gamma (u ℓ) (v ℓ) (w ℓ)
      = ∑ τ : Leaf L with Leaf.Contributes τ w, (∏ ℓ, phi (τ ℓ) (u ℓ)) * ∏ ℓ, psi (τ ℓ) (v ℓ) := by
  simp only [gamma]
  rw [prod_univ_sum, Leaf.filter_contributes_eq_piFinset]
  exact sum_congr rfl fun τ _ => prod_mul_distrib

/-- **Lemma 8**.  "For all arrays a, b and every output string w,
Mult(a, b)[w] = ∑_{u,v} γ(u₁, v₁, w₁) γ(u₂, v₂, w₂) ⋯ γ(u_L, v_L, w_L) a[u] b[v],
the sum over all left strings u and right strings v." -/
theorem lemma_8 {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (w : OutStr L) :
    Mult a b w = ∑ u, ∑ v, (∏ ℓ, gamma (u ℓ) (v ℓ) (w ℓ)) * a u * b v := by
  -- "the coefficient of a[u] b[v] in (2) is ∑_τ ∏_ℓ φ_{τ_ℓ}(u_ℓ) ψ_{τ_ℓ}(v_ℓ), summed over the
  -- leaves τ contributing to w": expand `Φ_τ(a) Ψ_τ(b)` and sum over `τ` last.
  simp only [Mult, Phi, Psi, sum_mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [prod_gamma_eq_sum_contributes, sum_mul, sum_mul]
  exact sum_congr rfl fun τ _ => by ring

end ThreeSumApsp
