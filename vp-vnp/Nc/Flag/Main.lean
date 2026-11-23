/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Flag.Avg
import Nc.Flag.Num
import Nc.Cat.Prod

/-!
# Translations of maps of a group into a metric space; what is used of prices
-/

open Finset Matrix

namespace Nc.Flag

open Cat

/-! ### Maps of a group into a complete CAT(0) space -/

section Maps
variable {G : Type} [Group G] [Fintype G] {Y : Type} [MetricSpace Y]

/-- Translations of maps. -/
def transAct (G Y : Type) [Group G] [Fintype G] [MetricSpace Y] :
    IsoAct G (PiLp 2 fun _ : G => Y) where
  act g z := WithLp.toLp 2 fun k => z (g⁻¹ * k)
  one' z := by
    ext k
    simp
  mul' g h z := by
    ext k
    simp [mul_assoc]
  iso' g z z' := by
    have h1 : dist (WithLp.toLp 2 fun k => z (g⁻¹ * k) : PiLp 2 fun _ : G => Y)
        (WithLp.toLp 2 fun k => z' (g⁻¹ * k)) ^ 2 = dist z z' ^ 2 := by
      rw [piLp_dist_sq, piLp_dist_sq]
      exact Equiv.sum_comp (Equiv.mulLeft g⁻¹) (fun k => dist (z k) (z' k) ^ 2)
    exact (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1 h1

theorem transAct_dist (z : PiLp 2 fun _ : G => Y) (g : G) :
    dist z ((transAct G Y).act g z) ^ 2 = ∑ k, dist (z (g * k)) (z k) ^ 2 := by
  rw [piLp_dist_sq, ← Equiv.sum_comp (Equiv.mulLeft g)]
  refine sum_congr rfl fun k _ => ?_
  show dist (z (g * k)) (z (g⁻¹ * (g * k))) ^ 2 = _
  rw [inv_mul_cancel_left]

end Maps

/-! ### Prices -/

variable {Pr : ∀ V : Type, (V → V → ℝ) → Prop}

end Nc.Flag
