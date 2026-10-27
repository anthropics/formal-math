/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Groundwork.Grid.Expand

/-! # The expansion over patterns, for any family of pieces

`Groundwork.Grid.Expand` expands the sum over the grid with one fixed family of pieces A_0, …, A_n,
which add up to the function X = [x = v][y = u] of a rectangle. Here the pieces are any functions
A_i, i ∈ I, that add up to d·X for an integer d. `ZG_cross_mul_eq_sum` is the identity d^|R| Z = Σ_ι
Z_ι of the proof of Theorem A on the grid (there R is the set of rectangles, here `Ω ρ γ`, and ι is
here `f`),
`Z_mul_eq_sum` the same for an instance carried to the grid, and `value_rowNet_tr` says that the row
network of the transposed grid, which is the column network,
has the value of the grid that was transposed. -/

public section

namespace ClauseBound.Grid

open Finset Groundwork Groundwork.Grid

variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
/-- The rectangles, as the subset of all ω that lie in Ω. -/
theorem filter_mem_Ω : (univ.filter fun ω => ω ∈ Ω ρ γ) = Ω ρ γ := by
  ext ω; simp

/-- If the pieces A_i, i ∈ I, add up to d·X, then d^|Ω| times the sum over the grid with X at every
rectangle is the sum, over all ways f to choose a piece for every
rectangle, of the sum over the grid with the piece A_{f ω} at the rectangle ω. -/
theorem ZG_cross_mul_eq_sum {κ : Type} [DecidableEq κ] (R : Inst (ρ × γ) α) (I : Finset κ) (i₀ : κ)
    (A : κ → α → α → α → α → ℤ) (d : ℤ) (h : ∀ x y u v, ∑ i ∈ I, A i x y u v = d * Cross.X x y u v) :
    d ^ #(Ω ρ γ) * ZG R (fun _ => Cross.X) = ∑ f ∈ tuples (fun ω => ω ∈ Ω ρ γ) (fun _ => I) i₀, ZG R fun ω => A (f ω) := by
  unfold ZG
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [← mul_sum, ← mul_sum]
  have h1 := sum_tuples_prod (fun ω => ω ∈ Ω ρ γ) (fun _ => I) i₀ fun ω i => app (A i) ℓ ω
  rw [filter_mem_Ω] at h1
  have h2 : ∏ ω ∈ Ω ρ γ, ∑ i ∈ I, app (A i) ℓ ω = d ^ #(Ω ρ γ) * ∏ ω ∈ Ω ρ γ, app Cross.X ℓ ω := by
    rw [← prod_const, ← prod_mul_distrib]
    exact prod_congr rfl fun ω _ => h _ _ _ _
  rw [h1, h2]
  ring

/-- For an instance on any node set J that is laid out on the grid by a bijection e: d^|Ω| times its
value is the sum over all choices of pieces. -/
theorem Z_mul_eq_sum {J κ : Type} [Fintype J] [LinearOrder J] [DecidableEq κ] (R : Inst J α) (d₀ : α) (e : J ≃ ρ × γ)
    (I : Finset κ) (i₀ : κ) (A : κ → α → α → α → α → ℤ) (d : ℤ) (h : ∀ x y u v, ∑ i ∈ I, A i x y u v = d * Cross.X x y u v) :
    d ^ #(Ω ρ γ) * R.Z d₀ = ∑ f ∈ tuples (fun ω => ω ∈ Ω ρ γ) (fun _ => I) i₀, ZG (onGrid R d₀ e) fun ω => A (f ω) := by
  rw [Z_eq_ZG_X R d₀ e]
  exact ZG_cross_mul_eq_sum _ I i₀ A d h

/-- The column network: if the cuts factor the functions of the transposed grid, the row network of
the transposed grid has the value of the grid itself. -/
theorem value_rowNet_tr {G : Rect ρ γ → α → α → α → α → ℤ} {C : Rect γ ρ → Cut α τ} (h : ∀ ω, (C ω).Factors (trG G ω))
    (R : Inst (ρ × γ) α) (t₀ : τ) (L : ℕ) : (rowNet (trInst R) C t₀ L).value = ZG R G := by
  rw [← ZG_tr]
  exact value_rowNet h (trInst R) t₀ L

end ClauseBound.Grid
