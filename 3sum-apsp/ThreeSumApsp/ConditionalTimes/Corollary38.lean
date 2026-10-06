/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.ConditionalTimes.SmallFacts
public import ThreeSumApsp.Sec5.Corollary38

/-!
# Corollary 38 from Lemma 37 and Corollary 26

Lemma 37 turns the comparison counts into the wanted entries of one thin matrix product, and
Corollary 26 computes these.

1. For large `n` the parameters `s` and `D*` are admissible: `s ≥ 1`, `D'' ≤ D*`, `(D*)^18 ≤ n`
   (`Corollary38.exists_regime` and the lemmas on `Corollary38.Regime`).
2. The time of Corollary 26 and the time of Lemma 37, as `Claim.Lemma_37` has it, are together at
   most a constant times the bound of the corollary (`corollary_38_bound`).
-/

public section

open ThreeSumApsp.ConditionalTimes

namespace ThreeSumApsp

open ComparisonCounts

/-- The deduction of **Corollary 38** from Lemma 37 and Corollary 26: "Apply Lemma 37 with s :=
⌈n^{1-1/440}/d⌉ [...] and pad the product to the inner dimension D* [...] and Corollary 26 with N :=
n and D := D* computes (XY)[r,c] for all (r,c) ∈ P". `blockLen n d` is this s, and `Dstar n d` is D*
= ⌈3d²n^{1/440}⌉. -/
theorem conditional_corollary_38 (M : TimeModel) (h26 : Claim.Corollary_26_wanted M)
    (h37 : Claim.Lemma_37 M ComparisonCounts.blockLen ComparisonCounts.Dstar) :
    Claim.Corollary_38 M := by
  -- The entries of the two matrices are at most `d ≤ n`, so the exponent `c` of Corollary 26 is 1.
  obtain ⟨C₁, T, hT, hproduct⟩ := h26 1
  obtain ⟨C₀, htransfer⟩ := h37
  obtain ⟨T', hT', hbuild⟩ := htransfer T hT
  obtain ⟨n₁, hregime⟩ := Corollary38.exists_regime
  obtain ⟨K, n₂, hbound⟩ := corollary_38_bound
  refine ⟨(|C₁| + |C₀|) * K, max n₁ n₂, T', hT', fun n d p hn hd hdn => ?_⟩
  -- Step 1: the parameters. `1 ≤ d ≤ D'' ≤ D*`.
  have hreg := hregime n d (le_of_max_le_left hn) hd hdn
  have hDstar : 1 ≤ Dstar n d :=
    (hd.trans (Nat.le_add_left _ _)).trans (Corollary38.D''_le_Dstar hreg)
  have hdn1 : (d : ℝ) ≤ (n : ℝ) ^ (1 : ℝ) := by
    simpa only [Real.rpow_one] using (Nat.cast_le (α := ℝ)).2 hreg.d_le_n
  -- Step 2: the time of Corollary 26 and the time of Lemma 37.
  have hproduct0 := productBound_nonneg n (Dstar n d) p
  have hbuild0 := buildBound_nonneg n d p
  calc T' n d p ≤ T n (Dstar n d) p d + C₀ * buildBound n d p :=
        hbuild n d p hreg.one_le_n hd hreg.d_le_n (Corollary38.one_le_blockLen hreg)
          (Corollary38.D''_le_Dstar hreg)
    _ ≤ |C₁| * productBound n (Dstar n d) p + |C₀| * buildBound n d p :=
        add_le_add (le_abs_mul_of_le_mul (hproduct n _ p d hDstar
          (Corollary38.Dstar_pow_le hreg) hdn1) hproduct0) (le_abs_mul_of_le_mul le_rfl hbuild0)
    _ ≤ (|C₁| + |C₀|) * (productBound n (Dstar n d) p + buildBound n d p) := by
        -- the right side has two further terms, which are not negative
        linarith [mul_nonneg (abs_nonneg C₁) hbuild0, mul_nonneg (abs_nonneg C₀) hproduct0]
    _ ≤ (|C₁| + |C₀|) * (K * countBound n d p) :=
        mul_le_mul_of_nonneg_left (hbound n d p (le_of_max_le_right hn) hd hdn) (by positivity)
    _ = (|C₁| + |C₀|) * K * countBound n d p := (mul_assoc _ _ _).symm

end ThreeSumApsp
