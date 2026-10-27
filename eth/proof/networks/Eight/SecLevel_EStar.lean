/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import EightSquareStatement
public import Paper.SecLevel_Recursion

/-! # «Hence e* = 0», with ρ = 11/12

Proves e* = 0 with ρ = 11/12, following the last paragraph of the proof of Proposition 3 sentence by
sentence, up to the conclusion e* = 0. The first sentence of Proposition 3 with ρ = 11/12 is a
hypothesis `hP3` of every theorem
here. e* (`Paper.eStar`), `Paper.Achievable` and the two general facts
`Paper.achievable_of_eStar_lt` and `Paper.eStar_le` do not depend on Lemma 2. -/

public section

namespace Eight

open Paper

/-- «Let e > e*; then (K, e) is achievable for infinitely many K. Let e'' > ρe. For all large K we
have (ρ + 2/K)e + 2/K ≤ e'', so (9K¹⁶, e'') is achievable for infinitely many K, and therefore e* ≤
e''.» Same as in the paper;
«large» is K ≥ (2e + 2)/(e'' − ρe). -/
theorem eStar_le_of (hP3 : ∀ {K : ℕ} {e : ℝ}, 2 ≤ K → 0 ≤ e → Achievable K e → Achievable (9 * K ^ 16) ((rho + 2 / K) * e + 2 / K))
    {e e'' : ℝ} (he : eStar < e) (he'' : rho * e < e'') : eStar ≤ e'' := by
  have hs0 := eStar_nonneg
  have h0 : 0 ≤ e := by linarith
  have hd : 0 < e'' - rho * e := by linarith
  have hρe : 0 ≤ rho * e := mul_nonneg (by unfold rho; norm_num) h0
  refine eStar_le (by linarith) fun K₀ => ?_
  obtain ⟨K, hK, hA⟩ := achievable_of_eStar_lt he (max K₀ (max 2 ⌈(2 * e + 2) / (e'' - rho * e)⌉₊))
  have hK0 : K₀ ≤ K := (le_max_left _ _).trans hK
  have hK2 : 2 ≤ K := ((le_max_left _ _).trans (le_max_right _ _)).trans hK
  have hKd : (2 * e + 2) / (e'' - rho * e) ≤ K :=
    (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans (le_max_right _ _)).trans hK)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hsmall : (2 * e + 2) / (K : ℝ) ≤ e'' - rho * e := by
    rw [div_le_iff₀ hd] at hKd
    rw [div_le_iff₀ hKpos]
    linarith
  have hexp : (rho + 2 / K) * e + 2 / K ≤ e'' := by
    have : (rho + 2 / K) * e + 2 / K = rho * e + (2 * e + 2) / (K : ℝ) := by ring
    linarith
  refine ⟨9 * K ^ 16, ?_, (hP3 hK2 h0 hA).mono hexp⟩
  have : K ≤ K ^ 16 := Nat.le_self_pow (by norm_num) K
  omega

/-- «Letting e'' → ρe and e → e* gives e* ≤ ρe*.» Here: for every η > 0, take e = e* + η/2 and e'' =
ρe + η/2, which is at most ρe* + η. -/
theorem eStar_le_rho_mul_of (hP3 : ∀ {K : ℕ} {e : ℝ}, 2 ≤ K → 0 ≤ e → Achievable K e → Achievable (9 * K ^ 16) ((rho + 2 / K) * e + 2 / K)) :
    eStar ≤ rho * eStar := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  have h1 : eStar ≤ rho * (eStar + η / 2) + η / 2 := eStar_le_of @hP3 (e := eStar + η / 2) (by linarith) (by linarith)
  have h2 : rho * (η / 2) ≤ 1 * (η / 2) := mul_le_mul_of_nonneg_right (by unfold rho; norm_num) (by linarith)
  linarith

/-- **Proposition 3**, second sentence, with ρ = 11/12: e* = 0. «Since 0 ≤ e* ≤ 1/2 and ρ < 1, e* = 0.»
Same as in the paper (e* ≤ 1/2 is not needed). -/
theorem eStar_eq_zero_of (hP3 : ∀ {K : ℕ} {e : ℝ}, 2 ≤ K → 0 ≤ e → Achievable K e → Achievable (9 * K ^ 16) ((rho + 2 / K) * e + 2 / K)) :
    eStar = 0 := by
  have h1 := eStar_le_rho_mul_of @hP3
  have h2 := eStar_nonneg
  have h3 : rho < 1 := by unfold rho; norm_num
  nlinarith

end Eight
