/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Num.Asymptotic
public import PaddedDescent.F.FuelCert

/-! # Lemmas on the proviso of the second sentence of Theorem A(c): numbers between 0.85·ρ^ℓ and ρ^ℓ for ρ = 11/12 and for ρ = 1/√2

«… provided that a number between 0.85·ρ^ℓ and ρ^ℓ can be computed from ℓ in time polynomial in K_ℓ,
as is the case for ρ = 11/12 and for ρ = 1/√2.» For ρ = 11/12 such a number is ρ^ℓ = 11^ℓ/12^ℓ
itself (`eleven_pow`).
For ρ = 1/√2 it is `num ℓ`/`den ℓ`, that is 2^{−ℓ/2} for even ℓ and (7/5)·2^{−(ℓ+1)/2} for odd ℓ,
because 0.85·√2 ≤ 7/5 ≤ √2 (`between_half`); numerator and denominator are computed from ℓ in unary
in time polynomial in ℓ (`num_den_polyT`),
which is stronger than what the text asks for, because ℓ < K_ℓ. The proof of the second sentence of
Theorem A(c) in this development does not use these lemmas. -/

public section

namespace GeneralPieces.Between

open Groundwork PaddedDescent.F Levels.Gen

/-- 11^ℓ/12^ℓ = (11/12)^ℓ. -/
theorem eleven_pow (l : ℕ) : ((11 ^ l : ℕ) : ℝ) / ((12 ^ l : ℕ) : ℝ) = (11 / 12 : ℝ) ^ l := by
  push_cast
  rw [div_pow]

/-- The numerator for ρ = 1/√2: 5 for even ℓ, 7 for odd ℓ. -/
def num (l : ℕ) : ℕ := 5 + 2 * (l - 2 * (l / 2))

/-- The denominator for ρ = 1/√2: 5·2^{⌈ℓ/2⌉}. -/
def den (l : ℕ) : ℕ := 5 * 2 ^ ((l + 1) / 2)

/-- (1/√2)^{2j} = 2^{−j}. -/
theorem half_pow_even (j : ℕ) : (1 / Real.sqrt 2) ^ (2 * j) = 1 / (2 : ℝ) ^ j := by
  rw [pow_mul, div_pow, Real.sq_sqrt (by norm_num), one_pow, div_pow, one_pow]

/-- 0.85·(1/√2)^ℓ ≤ num ℓ/den ℓ ≤ (1/√2)^ℓ. -/
theorem between_half (l : ℕ) : 0.85 * (1 / Real.sqrt 2) ^ l ≤ (num l : ℝ) / (den l : ℝ) ∧ (num l : ℝ) / (den l : ℝ) ≤ (1 / Real.sqrt 2) ^ l := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' l
  · have h1 : num (2 * j) = 5 := by unfold num; omega
    have h2 : (2 * j + 1) / 2 = j := by omega
    have h3 : (0 : ℝ) < 1 / 2 ^ j := by positivity
    have h4 : ((5 : ℕ) : ℝ) / ((5 * 2 ^ j : ℕ) : ℝ) = 1 / 2 ^ j := by push_cast; field_simp
    rw [h1, den, h2, half_pow_even, h4]
    exact ⟨by linarith, le_rfl⟩
  · have h1 : num (2 * j + 1) = 7 := by unfold num; omega
    have h2 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    have h3 : (0 : ℝ) < 1 / 2 ^ j := by positivity
    have h4 : ((7 : ℕ) : ℝ) / ((5 * 2 ^ (j + 1) : ℕ) : ℝ) = 1 / 2 ^ j * (7 / 10) := by push_cast; rw [pow_succ]; field_simp; norm_num
    have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h5 : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by field_simp; linarith
    rw [h1, den, h2, pow_succ, half_pow_even, h4, h5]
    generalize Real.sqrt 2 = s at *
    have hs1 : 7 / 5 ≤ s := by
      by_contra h
      have h' : s < 7 / 5 := not_le.1 h
      nlinarith
    have hs3 : 0.85 * s ≤ 7 / 5 := by
      by_contra h
      have h' : 7 / 5 < 0.85 * s := not_le.1 h
      nlinarith
    constructor
    · have := mul_le_mul_of_nonneg_left hs3 h3.le
      linarith
    · have := mul_le_mul_of_nonneg_left hs1 h3.le
      linarith

/-- Numerator and denominator are computed from ℓ, in unary, in polynomial time. -/
theorem num_den_polyT : PolyT fun u : U => (num u.length, den u.length) := by
  have hl : Unary fun u : U => u.length := unary_length PolyT.id'
  have h1 : PolyT fun u : U => 5 + 2 * (u.length - 2 * (u.length / 2)) :=
    PolyT.add (PolyT.const 5) (PolyT.mul (PolyT.const 2) (unary_sub hl (PolyT.mul (PolyT.const 2) (unary_div hl (PolyT.const 2)).poly)).poly)
  have h2 : PolyT fun u : U => 5 * 2 ^ ((u.length + 1) / 2) :=
    PolyT.mul (PolyT.const 5) (pow_polyT (PolyT.const 2) (unary_div (unary_add hl (unary_const 1)) (PolyT.const 2)))
  exact PolyT.prodMk h1 h2

end GeneralPieces.Between
