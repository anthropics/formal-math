/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.GridDefs

/-! A bound on the value of a network (Definition 2 of the paper): |Z| ≤ 2^{|J|(P+B) + |J|²B} for a
network on the nodes J with at most
2^P states a node and all weights and interactions at most 2^B in absolute value. -/

@[expose] public section

namespace Groundwork.Prog

open Finset Stepped

/-! ### The value of a network is small -/

/-- A network on the nodes J with at most 2^P states a node and all weights W and interactions Ψ at
most 2^B in absolute
value (part of `Sized P B`) has a value Z with |Z| ≤ 2^{|J|(P+B) + |J|²B}. -/
theorem abs_value_le {J σ τ : Type} [Fintype J] [LinearOrder J] (N : Network J σ τ) {P B : ℕ}
    (h : N.Sized P B) : |N.value| ≤ 2 ^ (Fintype.card J * (P + B) + Fintype.card J * Fintype.card J * B) := by
  unfold Network.value
  have hW : ∀ z : J → σ, |∏ a, N.W a (z a)| ≤ (2 ^ B) ^ Fintype.card J := by
    intro z
    rw [Finset.abs_prod]
    calc _ ≤ ∏ _a : J, (2 : ℤ) ^ B := Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun a _ => h.abs_W a _
      _ = _ := by rw [Finset.prod_const, card_univ]
  have hcard : #(pairs J) ≤ Fintype.card J * Fintype.card J := by
    refine (Finset.card_le_univ _).trans ?_
    rw [Fintype.card_prod]
  have hΨ : ∀ z : J → σ, |∏ p ∈ pairs J, N.Ψ p.1 p.2 (z p.1) (z p.2)| ≤ (2 ^ B) ^ (Fintype.card J * Fintype.card J) := by
    intro z
    rw [Finset.abs_prod]
    calc _ ≤ ∏ _p ∈ pairs J, (2 : ℤ) ^ B := Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun p hp =>
          h.abs_Ψ _ _ _ _ (ne_of_lt (by simpa [pairs] using hp))
      _ = ((2 : ℤ) ^ B) ^ #(pairs J) := by rw [Finset.prod_const]
      _ ≤ _ := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hcard
  have hS : (#(Fintype.piFinset N.S) : ℤ) ≤ (2 ^ P) ^ Fintype.card J := by
    rw [Fintype.card_piFinset]
    have : ∏ a, #(N.S a) ≤ ∏ _a : J, 2 ^ P := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun a _ => h.card_S a
    rw [Finset.prod_const, card_univ] at this
    exact_mod_cast this
  calc _ ≤ ∑ z ∈ Fintype.piFinset N.S, |(∏ a, N.W a (z a)) * ∏ p ∈ pairs J, N.Ψ p.1 p.2 (z p.1) (z p.2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z ∈ Fintype.piFinset N.S,
          ((2 : ℤ) ^ B) ^ Fintype.card J * ((2 : ℤ) ^ B) ^ (Fintype.card J * Fintype.card J) := by
        refine Finset.sum_le_sum fun z _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hW z) (hΨ z) (abs_nonneg _) (by positivity)
    _ = (#(Fintype.piFinset N.S) : ℤ)
          * (((2 : ℤ) ^ B) ^ Fintype.card J * ((2 : ℤ) ^ B) ^ (Fintype.card J * Fintype.card J)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 ^ P) ^ Fintype.card J
          * (((2 : ℤ) ^ B) ^ Fintype.card J * ((2 : ℤ) ^ B) ^ (Fintype.card J * Fintype.card J)) :=
        mul_le_mul_of_nonneg_right hS (by positivity)
    _ = _ := by
        rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
        congr 1
        ring


section

variable {C : Type}

end

end Groundwork.Prog
