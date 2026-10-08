/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Asymptotics.Powers
public import Mathlib.Data.Finset.Card

/-!
# Two counting facts for the lower bounds

* Fewer than `n` cells miss one of `n` consecutive cells (`exists_offset_notMem`).
* A time bound `C (n^a (log n)^e + 1)` with `a < 1` is far below `n` for some `n`
  (`exists_sublinear_bound_lt`).
-/

public section

namespace ThreeSumApsp.WordRam

/-- Fewer than `n` cells miss one of the `n` cells from `a` on. -/
theorem exists_offset_notMem {S : Finset ℤ} {n : ℕ} (hS : S.card < n) (a : ℤ) :
    ∃ r < n, a + (r : ℤ) ∉ S := by
  obtain ⟨b, hb, hnot⟩ : ∃ b ∈ (Finset.range n).image (fun r : ℕ => a + (r : ℤ)), b ∉ S := by
    refine Finset.exists_mem_notMem_of_card_lt_card ?_
    rwa [Finset.card_image_of_injective _ (fun p q hpq => by simpa using hpq), Finset.card_range]
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hb
  exact ⟨r, Finset.mem_range.1 hr, hnot⟩

/-- For `a < 1`, `C (n^a (log n)^e + 1)` is far below `n` for some `n`. -/
theorem exists_sublinear_bound_lt {a : ℝ} (ha : a < 1) (e : ℕ) (C : ℝ) : ∃ n : ℕ, 3 ≤ n ∧
    2 * (C * ((n : ℝ) ^ a * Real.log n ^ e + 1)) + 2 < (n : ℝ) := by
  have hmain := eventually_mul_rpow_mul_log_pow_le (4 * C) ha e
  have hconst : ∀ᶠ n : ℕ in Filter.atTop, 4 * C + 5 ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  obtain ⟨n, hmain, hconst, hn⟩ :=
    (hmain.and (hconst.and (Filter.eventually_ge_atTop 3))).exists
  rw [Real.rpow_one] at hmain
  -- `2 C X ≤ n / 2` and `2 C + 2 < n / 2`, where `X = n^a (log n)^e`
  exact ⟨n, hn, by linarith⟩

end ThreeSumApsp.WordRam
