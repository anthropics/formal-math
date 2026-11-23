/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.RunSum

/-!
# The sum over runs with finite domains: literals, counts
-/

set_option linter.unusedSectionVars false

namespace Nc

open Finset MvPolynomial

section Degree

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

end Degree

section Count

theorem card_ChN (S : Type) [Fintype S] (n : ℕ) : Fintype.card (Ch S (Fin n)) = 2 * Fintype.card S + n := by
  have e : Ch S (Fin n) ≃ (S × Bool) ⊕ Fin n :=
    { toFun := fun z => match z with
        | .tp s b => .inl (s, b)
        | .inp j => .inr j
      invFun := fun y => match y with
        | .inl (s, b) => .tp s b
        | .inr j => .inp j
      left_inv := fun z => by cases z <;> rfl
      right_inv := fun y => by rcases y with ⟨s, b⟩ | j <;> rfl }
  rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  omega

variable {Γ S Q : Type} [Fintype Γ] [Fintype S] [Fintype Q] {n t M N B : ℕ}

theorem card_letter_le (hΓ : Fintype.card Γ ≤ B) (hS : Fintype.card S ≤ B) (hn : n ≤ B) (hB : 1 ≤ B) :
    Fintype.card (Letter S (Fin n) Γ) ≤ 4 * B ^ 2 := by
  rw [Fintype.card_option, Fintype.card_prod, card_ChN]
  calc (2 * Fintype.card S + n) * Fintype.card Γ + 1 ≤ (2 * B + B) * B + 1 * 1 := by gcongr
    _ ≤ (2 * B + B) * B + B * B := by gcongr
    _ = 4 * B ^ 2 := by ring

theorem card_RD_le (hS : Fintype.card S ≤ B) (hn : n ≤ B) (ht : t + 1 ≤ B) (hM : M ≤ B) (hB : 1 ≤ B) :
    Fintype.card (RD S n t M) ≤ 6 * B ^ 2 := by
  have ht' : t ≤ B := by omega
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_ChN]
  calc t + (t + 1 + ((2 * Fintype.card S + n) * (t + 1) + Fintype.card S * M))
      ≤ B * 1 + (B * 1 + ((2 * B + B) * B + B * B)) := by
        rw [mul_one]; gcongr
    _ ≤ B * B + (B * B + ((2 * B + B) * B + B * B)) := by gcongr
    _ = 6 * B ^ 2 := by ring

theorem card_RE_le [DecidableEq Γ] [DecidableEq S] [DecidableEq Q] (hΓ : Fintype.card Γ + 1 ≤ B)
    (hS : Fintype.card S ≤ B) (hQ : Fintype.card Q ≤ B) (hn : n ≤ B) (ht : t + 1 ≤ B) (hM : M ≤ B) (hB : 1 ≤ B) :
    Fintype.card (Σ d, RE Γ S Q n t M d) ≤ 9 * B ^ 3 := by
  have ht' : t ≤ B := by omega
  have hL := card_letter_le (Γ := Γ) (S := S) (n := n) (by omega) hS hn hB
  have h : Fintype.card (Σ d, RE Γ S Q n t M d) = t * Fintype.card (Letter S (Fin n) Γ) +
      ((t + 1) * Fintype.card Q + (((2 * Fintype.card S + n) * (t + 1)) * M +
        (Fintype.card S * M) * (Fintype.card Γ + 1))) := by
    rw [Fintype.card_sigma, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    have e1 : ∀ τ : Fin t, Fintype.card (RE Γ S Q n t M (.inl τ)) = Fintype.card (Letter S (Fin n) Γ) :=
      fun _ => rfl
    have e2 : ∀ τ : Fin (t + 1), Fintype.card (RE Γ S Q n t M (.inr (.inl τ))) = Fintype.card Q := fun _ => rfl
    have e3 : ∀ z, Fintype.card (RE Γ S Q n t M (.inr (.inr (.inl z)))) = M := fun _ => Fintype.card_fin M
    have e4 : ∀ z, Fintype.card (RE Γ S Q n t M (.inr (.inr (.inr z)))) = Fintype.card Γ + 1 :=
      fun _ => Fintype.card_option
    simp only [e1, e2, e3, e4, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin,
      Fintype.card_prod, card_ChN]
  rw [h]
  calc _ ≤ B * (4 * B ^ 2) + (B * B * 1 + (((2 * B + B) * B) * B + (B * B) * B)) := by
        rw [mul_one]; gcongr
    _ ≤ B * (4 * B ^ 2) + (B * B * B + (((2 * B + B) * B) * B + (B * B) * B)) := by gcongr
    _ = 9 * B ^ 3 := by ring

theorem card_RS_le (hΓ : Fintype.card Γ + 1 ≤ B) (hS : Fintype.card S ≤ B) (hQ : Fintype.card Q ≤ B)
    (hn : n ≤ B) (ht : t ≤ B) (hB : 1 ≤ B) : Fintype.card (RS Γ S Q n t) ≤ 4 * B ^ 5 := by
  have hL := card_letter_le (Γ := Γ) (S := S) (n := n) (by omega) hS hn hB
  simp only [Fintype.card_prod, Fintype.card_fin]
  calc _ ≤ B * (4 * B ^ 2 * (B * B)) := by gcongr
    _ = 4 * B ^ 5 := by ring

theorem card_RH_le (hΓ : Fintype.card Γ + 1 ≤ B) (hS : Fintype.card S ≤ B)
    (hn : n ≤ B) (ht : t ≤ B) (hM : M ≤ B) (hB : 1 ≤ B) : Fintype.card (RH Γ S n t M) ≤ 25 * B ^ 5 := by
  have hL := card_letter_le (Γ := Γ) (S := S) (n := n) (by omega) hS hn hB
  have hΓ' : Fintype.card Γ ≤ B := by omega
  have h (k : ℕ) (hk : k ≤ 5) : B ^ k ≤ B ^ 5 := Nat.pow_le_pow_right hB hk
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  have h4 := h 4 (by omega)
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  rw [card_ChN]
  calc _ ≤ 2 + ((2 * B + B) + ((2 * B + B) * (B * (B * (4 * B ^ 2))) + (B * (B * B) +
        (B * (2 * (B * (B * B))) + (B * (2 * (B * B)) + (B * (B * (B * B)) + B * B)))))) := by gcongr
    _ = 2 * B ^ 0 + 3 * B ^ 1 + 12 * B ^ 5 + 3 * B ^ 3 + 3 * B ^ 4 + B ^ 2 := by ring
    _ ≤ 25 * B ^ 5 := by omega

end Count

section Main

variable {F : Type*} [Field F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q]

/-- The total length of the words with their separators. -/
theorem length_wordOf_ofFn {n : ℕ} (u : Fin n → List Γ) :
    (wordOf (List.ofFn u)).length = (∑ j, (u j).length) + n := by
  rw [length_wordOf, List.map_ofFn, List.sum_ofFn, List.length_ofFn]
  rfl

end Main

end Nc
