/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Groundwork.Grid.Grid

/-! One level of the recursion, with all rows merged (the row network in the proof of Proposition 3):
for any factorisation of the functions at the rectangles, the row
network has the value ZG. -/

@[expose] public section

namespace Groundwork.Grid

open Finset

variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]

/-- Regrouping the half-edges by the row of their source. -/
theorem ZG_eq_rows (R : Inst (ρ × γ) α) (G : Rect ρ γ → α → α → α → α → ℤ) :
    ZG R G = ∑ z : ρ → RowSt ρ γ α, (∏ a, rowW R a (z a)) * ∏ p ∈ pairs ρ, rowΨ G p.1 p.2 (z p.1) (z p.2) := by
  unfold ZG
  refine Fintype.sum_equiv (Equiv.curry ρ γ _) _ _ fun ℓ => ?_
  simp only [rowW, rowΨ, Equiv.curry_apply, Function.curry, prod_mul_distrib, Fintype.prod_prod_type, prod_Ω_rows, app,
    Prod.mk.eta]
  rw [Finset.prod_comm (s := univ) (t := pairs ρ)]
  ring

/-- An equality factors through the common value; for a family. -/
theorem prod_eq_factorised {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β] (x y : ι → β) :
    (∏ i, if x i = y i then (1 : ℤ) else 0) =
      ∑ θ : ι → β, (∏ i, if x i = θ i then 1 else 0) * ∏ i, if y i = θ i then 1 else 0 := by
  simp only [← prod_mul_distrib]
  rw [← Fintype.piFinset_univ]
  exact (prod_congr rfl fun i _ => (sum_mul_eq (fun t => if x i = t then 1 else 0) (y i)).symm).trans
    (Finset.prod_univ_sum (fun _ => univ) fun i t => (if x i = t then (1 : ℤ) else 0) * if y i = t then 1 else 0)

omit [Fintype ρ] [LinearOrder ρ] in
/-- The interaction of two rows is factorised by rowTop and rowBot over rowΘ. -/
theorem rowΨ_eq {G : Rect ρ γ → α → α → α → α → ℤ} {C : Rect ρ γ → Cut α τ} (h : ∀ ω, (C ω).Factors (G ω)) (t₀ : τ)
    (a b : ρ) (z z' : RowSt ρ γ α) :
    rowΨ G a b z z' = ∑ θ ∈ rowΘ C t₀ a b, rowTop C a b z θ * rowBot C a b z' θ := by
  have h' : ∀ ω x y u v, G ω x y u v = ∑ θ ∈ (C ω).lab, (C ω).top x y θ * (C ω).bot u v θ := h
  unfold rowΨ rowΘ rowTop rowBot
  rw [prod_eq_factorised]
  simp only [h']
  rw [prod_factorised _ _ t₀]
  rw [Finset.sum_product, Finset.sum_mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-- The interaction of the row network is rowΨ. -/
theorem rowNet_Ψ {G : Rect ρ γ → α → α → α → α → ℤ} {C : Rect ρ γ → Cut α τ} (h : ∀ ω, (C ω).Factors (G ω))
    (R : Inst (ρ × γ) α) (t₀ : τ) (L : ℕ) {a b : ρ} (hab : a < b) (z z' : RowSt ρ γ α) :
    (rowNet R C t₀ L).Ψ a b z z' = rowΨ G a b z z' := by
  rw [rowΨ_eq h t₀]
  simp [Network.Ψ, Network.lab, rowNet, min_eq_left hab.le, max_eq_right hab.le, hab, not_lt.2 hab.le]

/-- The row network has the value ZG. -/
theorem value_rowNet {G : Rect ρ γ → α → α → α → α → ℤ} {C : Rect ρ γ → Cut α τ} (h : ∀ ω, (C ω).Factors (G ω))
    (R : Inst (ρ × γ) α) (t₀ : τ) (L : ℕ) : (rowNet R C t₀ L).value = ZG R G := by
  rw [ZG_eq_rows]
  unfold Network.value
  have hS : Fintype.piFinset (rowNet R C t₀ L).S = univ := by simp [rowNet]
  rw [hS]
  refine sum_congr rfl fun z _ => congrArg₂ (· * ·) rfl (prod_congr rfl fun p hp => ?_)
  exact rowNet_Ψ h R t₀ L (by simpa [pairs] using hp) _ _

end Groundwork.Grid
