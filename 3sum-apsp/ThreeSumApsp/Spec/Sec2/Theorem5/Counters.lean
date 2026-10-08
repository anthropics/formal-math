/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Index

/-!
# Quotients and remainders by counters

The word RAM has no division.  A program that runs through the rows `I = 0, 1, …, N - 1` of a matrix
can still know, for each row, its band, its block within the band and its offset within the block
(Section 2.3.4), that is `I / (K₀ N₀)`, `I / N₀ % K₀` and `I % N₀`: it keeps three counters and
steps them (`stepCtr`, `ctrAt_succ`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-- The band of a row, its block within the band, and its offset within the block. -/
structure Ctr where
  /-- The band of the row. -/
  band : ℕ
  /-- The block of the row within its band. -/
  block : ℕ
  /-- The offset of the row within its block. -/
  off : ℕ

/-- The band, block and offset of row `I`, for bands of `k₀` blocks of `n₀` rows. -/
def ctrAt (k₀ n₀ I : ℕ) : Ctr := ⟨I / (k₀ * n₀), I / n₀ % k₀, I % n₀⟩

/-- From the band, block and offset of a row to those of the next row: comparisons and additions of
1 only. -/
def stepCtr (k₀ n₀ : ℕ) (s : Ctr) : Ctr :=
  if s.off + 1 < n₀ then { s with off := s.off + 1 }
  else if s.block + 1 < k₀ then { s with block := s.block + 1, off := 0 }
  else ⟨s.band + 1, 0, 0⟩

/-- Stepping the counters of row `I` gives the counters of row `I + 1`. -/
theorem ctrAt_succ {k₀ n₀ : ℕ} (hk : 0 < k₀) (hn : 0 < n₀) (I : ℕ) :
    ctrAt k₀ n₀ (I + 1) = stepCtr k₀ n₀ (ctrAt k₀ n₀ I) := by
  have hoff_lt : I % n₀ < n₀ := Nat.mod_lt I hn
  have hblock_lt : I / n₀ % k₀ < k₀ := Nat.mod_lt _ hk
  simp only [ctrAt, stepCtr, Nat.mul_comm k₀ n₀, ← Nat.div_div_eq_div_mul]
  split_ifs with hoff hlt
  · -- The next row of the same block.
    obtain ⟨hdiv, hmod⟩ := Nat.succ_div_mod_of_lt hoff
    rw [hdiv, hmod]
  · -- The first row of the next block of the same band.
    obtain ⟨hdiv, hmod⟩ := Nat.succ_div_mod_of_eq (show I % n₀ + 1 = n₀ by omega)
    obtain ⟨hband, hblock⟩ := Nat.succ_div_mod_of_lt hlt
    rw [hdiv, hmod, hband, hblock]
  · -- The first row of the first block of the next band.
    obtain ⟨hdiv, hmod⟩ := Nat.succ_div_mod_of_eq (show I % n₀ + 1 = n₀ by omega)
    obtain ⟨hband, hblock⟩ := Nat.succ_div_mod_of_eq (show I / n₀ % k₀ + 1 = k₀ by omega)
    rw [hdiv, hmod, hband, hblock]

end ThreeSumApsp.Spec
