/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Flag.Rank

/-!
# The choice of the size of the windows
-/

open Finset Filter Topology

namespace Nc.Flag

theorem exists_log_large {ρ ε : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) (hε : 0 < ε) :
    ∃ L0 : ℕ, ∀ L ≥ L0, ((L : ℝ) + 1) ^ 4 * ρ ^ L ≤ ε := by
  have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one 4 (r := ρ) (by rw [abs_of_pos h0]; exact h1)
  have h2 := (h.eventually (gt_mem_nhds (show (0 : ℝ) < ε * ρ by positivity)))
  obtain ⟨N, hN⟩ := eventually_atTop.1 h2
  refine ⟨N, fun L hL => ?_⟩
  have h3 := hN (L + 1) (by omega)
  push_cast at h3
  have h4 : ((L : ℝ) + 1) ^ 4 * ρ ^ L * ρ < ε * ρ := by
    calc _ = ((L : ℝ) + 1) ^ 4 * ρ ^ (L + 1) := by rw [pow_succ]; ring
      _ < _ := h3
  exact (lt_of_mul_lt_mul_right h4 h0.le).le

end Nc.Flag
