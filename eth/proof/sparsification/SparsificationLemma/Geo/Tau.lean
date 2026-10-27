/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Geo.Defs
import SparsificationLemma.Geo.Thr
import SparsificationLemma.One
import SparsificationLemma.Side
import SparsificationLemma.Gen
import UniformInK.Spars.Thresholds
import SparsifyWidthK.Thresholds

/-! # The sparsification theorem for the geometric thresholds, for any τ ≥ 8k that is large enough for ε

`stThmTau` puts together the general theorem `SparsificationLemma.stGen` for the thresholds
`thetaU τ`, «exactly one output» (`SparsificationLemma.stExactlyOne`), the bound on the occurrences
(`stDegGeo`) and the estimate
`WidthK.Thresholds.sum_choose_le_two_rpow` of a sum of binomial coefficients. The general theorem
counts at most (k−1)·n/τ steps of the second kind on a path; here k·n/τ is enough. -/

public section

namespace SparsificationLemma.Geo

open Finset Groundwork Groundwork.Sparsify CountKSat UniformInK

/-- k ≤ τ^(2k), if 2 ≤ τ. -/
theorem le_bsumU {k τ : ℕ} (hτ : 2 ≤ τ) : k ≤ bsumU τ k := by
  unfold bsumU
  calc k ≤ 2 * k := by omega
    _ ≤ 2 ^ (2 * k) := Nat.lt_two_pow_self.le
    _ ≤ τ ^ (2 * k) := Nat.pow_le_pow_left hτ _

/-- The theorem for any τ ≥ 8k with (k/τ)·log₂(e·τ·τ^(2k)) ≤ ε. -/
theorem stThmTau : StThmTau := by
  intro k n τ ε φ hk hτ hε hφ
  have hτ2 : 2 ≤ τ := by omega
  obtain ⟨g1, g2, g3, -⟩ := stGen stSide k τ n (bsumU τ k * n) (thetaU τ) (betaSU τ) hk (by omega) (stThrGeo k τ hk hτ)
    (Nat.mul_le_mul_right _ (stBetaSumU τ k hτ2)) φ hφ
  refine ⟨g1, fun Φ hΦ => ⟨(g3 Φ hΦ).1, stNodup _ _ _ _ Φ hΦ⟩, ?_, fun b => stExactlyOne _ _ _ _ b, fun Φ hΦ v => ((g3 Φ hΦ).2 v).trans (stDegGeo k τ hk (by omega))⟩
  have h1 : ∑ j ∈ range ((k - 1) * n / τ + 1), (bsumU τ k * n).choose j ≤ ∑ j ∈ range (k * n / τ + 1), (bsumU τ k * n).choose j :=
    sum_le_sum_of_subset (range_mono (Nat.succ_le_succ (Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.sub_le k 1)))))
  calc ((outTau k n τ φ).length : ℝ) ≤ ((∑ j ∈ range (k * n / τ + 1), (bsumU τ k * n).choose j : ℕ) : ℝ) := by exact_mod_cast g2.trans h1
    _ ≤ (2 : ℝ) ^ (ε * (n : ℝ)) := WidthK.Thresholds.sum_choose_le_two_rpow (by omega) (le_bsumU hτ2) hε n

end SparsificationLemma.Geo
