/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/PairCeiling/Grid.lean — closed forms of E = ∫₀ˣ D at the grid points (consumed by Bridge.lean):
  Efun s N (m/N) = Σ_{i<m} ( Csum s i / N − (((i+1)/N)³ − (i/N)³)/6 ),   m ≤ N.
-/
import Zeta23.PairCeiling.Stability

open scoped BigOperators Interval
open MeasureTheory Set intervalIntegral

noncomputable section

namespace Zeta23
namespace PairCeiling

variable {s : ℕ → ℝ} {N : ℕ}

/-- a.e. on a cell, D is the polynomial C_i − t²/2. -/
lemma Dfun_ae_cell (hN : 0 < N) {i : ℕ} (hi : i < N) :
    ∀ᵐ t ∂volume, t ∈ Ι ((i:ℝ)/N) ((i+1:ℝ)/N) → Dfun s N t = Csum s i - t ^ 2 / 2 := by
  filter_upwards [Cstep_ae_cell (s := s) hN hi] with t ht hmem
  simp [Dfun, ht hmem]

/-- the cell integral of D. -/
lemma integral_Dfun_cell (hN : 0 < N) {i : ℕ} (hi : i < N) :
    ∫ t in ((i:ℝ)/N)..((i+1:ℝ)/N), Dfun s N t
      = Csum s i / N - ((((i:ℝ)+1)/N) ^ 3 - ((i:ℝ)/N) ^ 3) / 6 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [intervalIntegral.integral_congr_ae (Dfun_ae_cell (s := s) hN hi)]
  rw [intervalIntegral.integral_sub _root_.intervalIntegrable_const
        (((by fun_prop : Continuous fun t : ℝ => t ^ 2 / 2)).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_const, smul_eq_mul]
  have h2 : ∫ t in ((i:ℝ)/N)..((i+1:ℝ)/N), t ^ 2 / 2
      = ((((i:ℝ)+1)/N) ^ 3 - ((i:ℝ)/N) ^ 3) / 6 := by
    rw [intervalIntegral.integral_div, integral_pow]
    push_cast
    ring
  rw [h2]
  field_simp
  ring

/-- **E at the grid points.** -/
theorem Efun_grid (hN : 0 < N) {m : ℕ} (hm : m ≤ N) :
    Efun s N ((m:ℝ)/N) = ∑ i ∈ Finset.range m, (Csum s i / N - ((((i:ℝ)+1)/N) ^ 3 - ((i:ℝ)/N) ^ 3) / 6) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold Efun
  have hint : ∀ k < m, IntervalIntegrable (Dfun s N) volume ((fun i : ℕ => (i:ℝ)/N) k) ((fun i : ℕ => (i:ℝ)/N) (k+1)) := by
    intro k hk
    have hk' : k < N := lt_of_lt_of_le hk hm
    refine (intervalIntegrable_Dfun (s := s) hN).mono_set ?_
    rw [uIcc_of_le zero_le_one]
    simpa [Nat.cast_succ] using cell_subset hN hk'
  have key := intervalIntegral.sum_integral_adjacent_intervals hint
  simp only [Nat.cast_zero, zero_div] at key
  rw [← key]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < N := lt_of_lt_of_le (Finset.mem_range.mp hi) hm
  simpa [Nat.cast_succ] using integral_Dfun_cell (s := s) hN hi'

/-- D at the grid points (right value): D(m/N) = C_m − (m/N)²/2, m ≤ N. -/
theorem Dfun_grid (hN : 0 < N) {m : ℕ} (hm : m ≤ N) :
    Dfun s N ((m:ℝ)/N) = Csum s m - ((m:ℝ)/N) ^ 2 / 2 := by
  rcases Nat.lt_or_ge m N with h | h
  · simp [Dfun, Cstep_eq_Csum_of_mem hN (Nat.succ_le_of_lt h) ⟨le_rfl, by
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      gcongr; linarith⟩]
  · have : m = N := le_antisymm hm h
    subst this
    have hNr : (0 : ℝ) < (m:ℕ) := by exact_mod_cast hN
    simp [Dfun, div_self hNr.ne', Cstep_one hN]

end PairCeiling
end Zeta23

end
