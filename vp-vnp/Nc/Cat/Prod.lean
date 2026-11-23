/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cat.Core

/-!
# The metric of a finite ℓ²-product
-/

namespace Cat

variable {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MetricSpace (X i)]

theorem piLp_dist_sq (f g : PiLp 2 X) : dist f g ^ 2 = ∑ i, dist (f i) (g i) ^ 2 := by
  rw [PiLp.dist_eq_sum (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

end Cat
