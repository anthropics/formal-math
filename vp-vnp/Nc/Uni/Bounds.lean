/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Uni.Exist
import Nc.Uni.LenU
import Nc.Uni.TopU
import Nc.Tape.ProgRun

/-!
# The universal automaton: bounds for the time
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc.Uni

open Finset NS1

section General

variable {A : Type} [CommRing A] {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K] {P : Mach A M K}

theorem tU_mono {b T T' L L' : ℕ} (hT : T ≤ T') (hL : L ≤ L') : tU b T L ≤ tU b T' L' := by
  unfold tU
  gcongr

end General

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

/-- The number of steps. -/
def stepsU (supp : Finset (List Bool)) (τ s : ℕ) : ℕ := 3 * s + (40 + 2 * Lm supp) * τ + 10

theorem tU_le (b T L : ℕ) : tU b T L ≤ (50 + b) * ((T + 1) * (L + 1) ^ 2) := by
  obtain ⟨t, rfl⟩ : ∃ t, T = t := ⟨T, rfl⟩
  have h1 : T ≤ T + 1 := Nat.le_succ _
  have h2 : L + 4 ≤ 4 * (L + 1) := by omega
  have h3 : L + 2 ≤ 2 * (L + 1) := by omega
  have h4 : L + 3 ≤ 3 * (L + 1) := by omega
  have h5 : 2 * T + 1 ≤ 2 * (T + 1) := by omega
  have hl : 1 ≤ L + 1 := by omega
  have ht : 1 ≤ T + 1 := by omega
  unfold tU
  generalize T + 1 = t at *
  generalize L + 1 = l at *
  calc 5 * (t * l) + t + t * l + T * l + T * (L + 4) +
        ((L + 2) * ((2 * T + 1) * (L + 4) + 1) + (l * ((2 * T + 1) * (L + 4)) + b * l) + 2 * ((2 * T + 1) * (L + 3)))
      ≤ 5 * (t * l) + t + t * l + t * l + t * (4 * l) +
        (2 * l * (2 * t * (4 * l) + 1) + (l * (2 * t * (4 * l)) + b * l) + 2 * (2 * t * (3 * l))) := by gcongr
    _ = 24 * (t * l ^ 2) + 23 * (t * l) + t + 2 * l + b * l := by ring
    _ ≤ 24 * (t * l ^ 2) + 23 * (t * l ^ 2) + t * l ^ 2 + 2 * (t * l ^ 2) + b * (t * l ^ 2) := by
        have a1 : l ≤ l ^ 2 := by nlinarith
        have a2 : t * l ≤ t * l ^ 2 := Nat.mul_le_mul_left _ a1
        have a3 : t ≤ t * l ^ 2 := by nlinarith
        have a4 : l ≤ t * l ^ 2 := by nlinarith
        gcongr
    _ = (50 + b) * (t * l ^ 2) := by ring

theorem size_le_lg (n : ℕ) : Nat.size n ≤ lg n := by
  rw [Nat.size_le, lg]
  exact Nat.lt_pow_succ_log_self (by norm_num) n

theorem size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

end Nc.Uni
