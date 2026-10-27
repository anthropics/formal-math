/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Groundwork.Grid.RowNet
public import Groundwork.Cross.Bit

/-! One level of the recursion, as identities: transposing the grid, which exchanges rows and
columns, does not change the sum;
and the value with the crossing on every rectangle is the sum over ι of the terms Z_ι. -/

@[expose] public section

namespace Groundwork.Grid

open Finset

variable {ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ]

/-- Transposing a half-edge labelling: the coordinates of both nodes are exchanged. -/
def trHalf (ρ γ α : Type) : Half ρ γ α ≃ Half γ ρ α where
  toFun ℓ w w' := ℓ w.swap w'.swap
  invFun ℓ w w' := ℓ w.swap w'.swap
  left_inv _ := rfl
  right_inv _ := rfl

/-- The rectangles, as the subset of all ω that lie in Ω. -/
private theorem filter_mem_Ω : (univ.filter fun ω => ω ∈ Ω ρ γ) = Ω ρ γ := by
  ext ω; simp

/-- Transposing the grid does not change the sum. -/
theorem ZG_tr [Fintype α] [DecidableEq α] (R : Inst (ρ × γ) α) (G : Rect ρ γ → α → α → α → α → ℤ) :
    ZG (trInst R) (trG G) = ZG R G := by
  unfold ZG
  refine (Fintype.sum_equiv (trHalf ρ γ α) _ _ fun ℓ => ?_).symm
  have h1 : ∏ w, trInst R w (trHalf ρ γ α ℓ w) = ∏ w, R w (ℓ w) :=
    (Fintype.prod_equiv (Equiv.prodComm ρ γ) _ _ fun _ => rfl).symm
  have h2 : ∏ ω ∈ Ω γ ρ, app (trG G ω) (trHalf ρ γ α ℓ) ω = ∏ ω ∈ Ω ρ γ, app (G ω) ℓ ω :=
    (prod_equiv (Equiv.prodComm (ρ × ρ) (γ × γ)) (fun ω => by simp [Ω, and_comm]) fun _ _ => rfl).symm
  rw [h1, h2]
  congr 2
  exact mul_comm _ _

/-- The value with the crossing `Cross.X` on every rectangle is the sum over ι of the terms Z_ι. -/
theorem ZG_cross_eq_sum {n : ℕ} (R : Inst (ρ × γ) (Bits n)) :
    ZG R (fun _ => Cross.X) = ∑ ι ∈ Pat ρ γ n, ZG R fun ω => A n (ι ω) := by
  unfold ZG
  rw [sum_comm]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [← mul_sum, ← mul_sum]
  congr 2
  have h := sum_tuples_prod (fun ω => ω ∈ Ω ρ γ) (fun _ => range (n + 1)) 0 fun ω i => app (A n i) ℓ ω
  rw [filter_mem_Ω] at h
  rw [Pat, h]
  exact prod_congr rfl fun ω _ => (sum_A _ _ _ _).symm

end Groundwork.Grid
