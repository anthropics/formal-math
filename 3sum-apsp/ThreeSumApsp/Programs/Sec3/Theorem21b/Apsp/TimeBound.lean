/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.LightModel
public import ThreeSumApsp.Programs.Sec3.Theorem21b.Apsp.Host

/-!
# APSP from the (min,+)-product: the claim

The running time of the host (`apTime`, `isHost_ap`) in the form of the claim
`ApspFromMinPlus`: `⌈log₂ n⌉ + 1` times the sum of the time of a (min,+)-product of
matrices whose entries are bounded by `3nu` and of `O(n² (1 + log(nu)))` (for Theorem 21(b)).
-/

public section

namespace Light.Sec3

open ThreeSumApsp

/-- APSP from the (min,+)-product, for programs of the light language. -/
theorem claim_apspFromMinPlus : Claim.ApspFromMinPlus lightModel := by
  refine ⟨3, 135, by norm_num, fun T hT => isHost_ap.solvedIn hT fun Tn hTn n U u hn hU hu => ?_⟩
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hτ : (Tn n (3 * (n * U)) : ℝ) ≤ T n (3 * ((n : ℝ) * u)) := by
    refine hTn n (3 * (n * U)) _ hn (by have := Nat.mul_pos hn hU; omega) ?_
    push_cast
    have : (n : ℝ) * U ≤ n * u := mul_le_mul_of_nonneg_left hu (by positivity)
    linarith
  have hlog : 0 ≤ logU (3 * ((n : ℝ) * u)) :=
    Real.log_nonneg (le_trans (by norm_num) (le_max_right _ _))
  have hτ0 : 0 ≤ T n (3 * ((n : ℝ) * u)) := le_trans (by positivity) hτ
  have hc0 : (0 : ℝ) ≤ (Nat.clog 2 n : ℝ) := by positivity
  have hns : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hs1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hsℓ : 0 ≤ (n : ℝ) ^ 2 * logU (3 * ((n : ℝ) * u)) := by positivity
  simp only [apTime]
  push_cast
  rw [← sq (n : ℝ)]
  -- `t ≤ τ` are the time of the solver and its bound, `ℓ = log (3nu)`, `c` is the number of rounds
  -- and `s = n²`
  generalize (Tn n (3 * (n * U)) : ℝ) = t at hτ ⊢
  generalize T n (3 * ((n : ℝ) * u)) = τ at hτ hτ0 ⊢
  generalize logU (3 * ((n : ℝ) * u)) = ℓ at hsℓ ⊢
  generalize (Nat.clog 2 n : ℝ) = c at hc0 ⊢
  generalize (n : ℝ) ^ 2 = s at hns hs1 hsℓ ⊢
  have hround : t + 23 * s + 29 ≤ τ + 135 * (s * (1 + ℓ)) := by linarith
  have hends : 53 * s + 17 * n + 65 ≤ τ + 135 * (s * (1 + ℓ)) := by linarith
  calc c * (t + 23 * s + 29) + 53 * s + 17 * n + 65
      ≤ c * (τ + 135 * (s * (1 + ℓ))) + (τ + 135 * (s * (1 + ℓ))) := by
        linarith [mul_le_mul_of_nonneg_left hround hc0]
    _ = (c + 1) * (τ + 135 * (s * (1 + ℓ))) := by ring

end Light.Sec3
