/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FixedWidthSteps.Absorb
public import UniformInK.Top.Time

/-! # The main statement, from its four premises

Fix k, and let w ≤ max(k, 3) be the width that the algorithm takes. If the test is true, the «In
particular» of Theorem D (a) bounds the time of M on the rewritten code by 2^{C₁·w²·E(n)}, E(n) =
n·log log n/(log n)^α. If the test is false, n is one of finitely many
(`ConditionsHoldEventually` at max(k, 3)), and the time 2^{cn}·n^{ck} of trying all assignments is
within the bound by `SmallCasesAreWithinTheBound`. In both cases the overhead q·(t + |x| + 1)^q of
the machine that chooses is absorbed (`absorb`), because the code has
length below (n + 2)^{5k}. The step from w to max(k, 3) is made in the constant: C₁·w² ≤ C₁·max(k, 3)²,
and `two_rpow_mono` raises the constant in the exponent. -/

public section

namespace FixedWidthSteps

open Turing Groundwork ClauseBound.Alg MainTheoremForms TwoMachines PairsToBound FixedWidth Wrap

/-- The time of the «In particular» of Theorem D (a) at the width w is at most 2^{C·w²·E(n)}. -/
theorem timeVariablesAAlpha_le (C w n : ℕ) (α : ℝ) : (timeVariablesAAlpha C w n α : ℝ) ≤ (2 : ℝ) ^ (((C * w ^ 2 : ℕ) : ℝ) * expVariables α n) := by
  refine (Nat.floor_le (by positivity)).trans (le_of_eq ?_)
  congr 1
  unfold expVariables
  push_cast
  ring

/-- The main statement, from the «In particular» of Theorem D (a), the conditions for all but
finitely many n, the finitely many other n, and the facts on the width that the algorithm takes. -/
theorem everyChoiceCountsFrom : EveryChoiceCountsFrom := by
  intro hVariablesA hCond hSmall hW Idx _ S e C₀ Q α a hα he M C' hM Mb c hMb pre test hpre htest N q hN k hk
  obtain ⟨C1, h1⟩ := hVariablesA Idx S e C₀ Q α a hα he M C' hM
  obtain ⟨n₀, hn₀⟩ := hCond (max k 3) (S.K (Q.idx 0))
  obtain ⟨C2, h2⟩ := hSmall α c k n₀ hα.le
  obtain ⟨c₁, hc₁, hB⟩ := lg_le_exp hSmall α hα.le
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = C1 * max k 3 ^ 2 := ⟨_, rfl⟩
  refine ⟨q * (2 * (A + C2 + 5 * k) + 2) * c₁, fun n φ hn hφ => ?_⟩
  obtain ⟨hw3, hwk, hwle⟩ := hW n φ
  have hwmax := (hwle k hk hφ).1
  have hE := expVariables_pos α hn
  have hX : (SatM.enc k φ).length + 1 ≤ (n + 2) ^ (A + C2 + 5 * k) :=
    (UniformInK.Time.length_enc_succ_le hk hφ).trans (Nat.pow_le_pow_right (by omega) (by omega))
  by_cases ht : test (SatM.enc k φ) = true
  · obtain ⟨hK, hw4⟩ := (htest k n φ hk hφ).1 ht
    have hrun : Outputs M (SatM.enc (widthOr3 φ) φ) (SatK.binary n (SatK.numSat φ)) (timeVariablesAAlpha C1 (widthOr3 φ) n α) := h1 (widthOr3 φ) n φ hK hw3 hw4 (hwk hφ.2)
    rw [← hpre k n φ hk hφ] at hrun
    have hle : C1 * widthOr3 φ ^ 2 ≤ A + C2 + 5 * k := by
      have : C1 * widthOr3 φ ^ 2 ≤ A := by rw [hA]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hwmax 2)
      omega
    exact Outputs.mono ((hN _ _ _).1 ht hrun) (absorb α hc₁ hB q _ hn ((timeVariablesAAlpha_le C1 _ n α).trans (two_rpow_mono hle hE.le)) hX)
  · have ht' : test (SatM.enc k φ) = false := by simpa using ht
    have hlt : n < n₀ := by
      by_contra hge
      obtain ⟨a1, a2⟩ := hn₀ n (not_lt.1 hge)
      exact ht ((htest k n φ hk hφ).2 ⟨a1, le_trans (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hwmax) 4) a2⟩)
    have hrun : Outputs Mb (SatM.enc k φ) (SatK.binary n (SatK.numSat φ)) (2 ^ (c * n) * n ^ (c * k)) := hMb k n φ hk (by omega) hφ
    have hle : ((2 ^ (c * n) * n ^ (c * k) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((A + C2 + 5 * k : ℕ) : ℝ) * expVariables α n) :=
      le_trans (le_trans (Nat.cast_le.2 (h2 n hn hlt)) (timeVariables_le α C2 n)) (two_rpow_mono (by omega) hE.le)
    exact Outputs.mono ((hN _ _ _).2 ht' hrun) (absorb α hc₁ hB q _ hn hle hX)

end FixedWidthSteps
