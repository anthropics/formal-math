/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec5.Corollary40.HintSizeArithmetic
public import ThreeSumApsp.Util.Basic

/-!
# Corollary 40, "General τ", Conjecture 5.12: rounding does no harm for large t₁

Proof of Corollary 40: "we use the same blocks, which requires n^{τ₁} ≤ n^{ετ₂}".  The hint
dimensions are the integers t₁ = ⌊n^{τ₁}⌋ and t₂ = ⌊n^{τ₂}⌋, and the condition of the data
structure, t₁ ≤ t₂^ε, can fail for some n although τ₁ < ε τ₂.  It holds as soon as t₁ exceeds a
constant: then n is so large that n^{ετ₂ − τ₁} ≥ 2, and t₂^ε ≥ n^{ετ₂}/2 ≥ n^{τ₁} ≥ t₁.  Below that
constant the data structure does not need the condition, because it answers queries by inner
products.
-/

public section

namespace ThreeSumApsp

open ThreeSumApsp.WordRam

/-- If t₁ exceeds 4^K with K ≥ τ₁/δ, then n is so large that n^δ ≥ 2. -/
theorem two_le_rpow_of_pow_lt_hintSize {τ₁ δ : ℝ} (hτ₁ : 0 < τ₁) (hδ : 0 < δ) {n K : ℕ} (hn : 1 ≤ n)
    (hK : τ₁ / δ ≤ (K : ℝ)) (hlarge : 4 ^ K < hintSize τ₁ n) : 2 ≤ (n : ℝ) ^ δ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (4 : ℝ) ^ (K : ℝ) ≤ (n : ℝ) ^ τ₁ := by
    rw [Real.rpow_natCast]
    have hcast : ((4 ^ K : ℕ) : ℝ) ≤ (hintSize τ₁ n : ℝ) := by exact_mod_cast hlarge.le
    push_cast at hcast
    exact hcast.trans (hintSize_le_rpow n τ₁)
  have hexp : 1 ≤ (K : ℝ) * (δ / τ₁) := by
    have hKδ : τ₁ ≤ (K : ℝ) * δ := (div_le_iff₀ hδ).1 hK
    rw [← mul_div_assoc, le_div_iff₀ hτ₁]
    linarith
  calc (2 : ℝ) ≤ (4 : ℝ) ^ (1 : ℝ) := by norm_num
    _ ≤ (4 : ℝ) ^ ((K : ℝ) * (δ / τ₁)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = ((4 : ℝ) ^ (K : ℝ)) ^ (δ / τ₁) := Real.rpow_mul (by norm_num) _ _
    _ ≤ ((n : ℝ) ^ τ₁) ^ (δ / τ₁) := Real.rpow_le_rpow (by positivity) hpow (by positivity)
    _ = (n : ℝ) ^ δ := by
      rw [← Real.rpow_mul hn0.le]
      congr 1
      field_simp

/-- Rounding t₂ down loses at most a factor 2: (n^τ₂)^ε ≤ 2 t₂^ε for 0 ≤ ε ≤ 1. -/
theorem rpow_rpow_le_two_mul_hintSize_rpow {τ₂ ε : ℝ} (hτ₂ : 0 ≤ τ₂) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) : ((n : ℝ) ^ τ₂) ^ ε ≤ 2 * (hintSize τ₂ n : ℝ) ^ ε :=
  calc ((n : ℝ) ^ τ₂) ^ ε ≤ (2 * (hintSize τ₂ n : ℝ)) ^ ε :=
        Real.rpow_le_rpow (by positivity) (rpow_le_two_mul_hintSize hn hτ₂) hε0
    _ = (2 : ℝ) ^ ε * (hintSize τ₂ n : ℝ) ^ ε := Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ 2 * (hintSize τ₂ n : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_right (two_rpow_le_two hε1) (by positivity)

/-- For τ₁ < ε τ₂ there is a threshold M such that t₁ ≤ t₂^ε whenever ⌈log₄ t₁⌉ ≥ M. -/
theorem exists_hint_threshold {τ₁ τ₂ ε : ℝ} (h1 : 0 < τ₁) (h2 : 0 ≤ τ₂) (hε : τ₁ < ε * τ₂)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∃ M : ℕ, ∀ n : ℕ, 1 ≤ n → M ≤ Nat.clog 4 (hintSize τ₁ n) →
      (hintSize τ₁ n : ℝ) ≤ (hintSize τ₂ n : ℝ) ^ ε := by
  set δ := ε * τ₂ - τ₁ with hδ
  have hδ0 : 0 < δ := sub_pos.2 hε
  refine ⟨⌈τ₁ / δ⌉₊ + 1, fun n hn hM => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- t₁ is large, so n^δ ≥ 2
  have hlarge : 4 ^ ⌈τ₁ / δ⌉₊ < hintSize τ₁ n := by
    by_contra hsmall
    have := (Nat.clog_le_iff_le_pow (by norm_num)).2 (not_lt.1 hsmall)
    omega
  have htwo := two_le_rpow_of_pow_lt_hintSize h1 hδ0 hn (Nat.le_ceil _) hlarge
  -- t₁ ≤ n^τ₁, 2 n^τ₁ ≤ n^τ₁ n^δ = (n^τ₂)^ε ≤ 2 t₂^ε
  have hround := rpow_rpow_le_two_mul_hintSize_rpow h2 hε0 hε1 hn
  have hsplit : ((n : ℝ) ^ τ₂) ^ ε = (n : ℝ) ^ τ₁ * (n : ℝ) ^ δ := by
    rw [← Real.rpow_mul hn0.le, ← Real.rpow_add hn0]
    congr 1
    rw [hδ]
    ring
  have hdouble : (n : ℝ) ^ τ₁ * 2 ≤ (n : ℝ) ^ τ₁ * (n : ℝ) ^ δ :=
    mul_le_mul_of_nonneg_left htwo (by positivity)
  have ht₁ := hintSize_le_rpow n τ₁
  linarith

end ThreeSumApsp
