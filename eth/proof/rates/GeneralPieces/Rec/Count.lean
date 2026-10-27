/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Num.Remarks
public import ClauseBound.Gen.Seq

/-! # The count of operations in the proof of part (b) of Theorem A, as arithmetic

Here a number of operations is rendered as a padding string of that many ones (Appendix E), and the
induction for part (b) bounds the exponent of its length. The text counts operations. This file
checks
the arithmetic of the text's count, as the text has it: the two inequalities of the display «So the
total number of operations is at most …», in real variables, with arbitrary natural numbers for C₁,
C₂, C₃.
The constant C₄, which the text does not write out, is (c+4)C₁ + C₂ + C₃ + c + 4 in the exponent of
the first inequality; the second takes it as a parameter. -/

@[expose] public section

namespace GeneralPieces.Count

open Levels.Gen ClauseBound.Gen

/-- The first inequality of the display, in real variables: X = Ξ, s = 2^{2N/K}, u = 2^{cλ}, a = |𝓘|^{|R|}
≤ Ξ^A, κ = K^g ≤ Ξ^G, q = (2|𝓘|+2)·2^{cλ} ≤ Ξ^{c+1}τ, τ = u·Ξ^{C₂}, D₁ = (c+4)C₁. Every sum of two
numbers is bounded by Ξ times the larger bound («a sum of numbers that are at least 2 is at most
their product»). -/
theorem count_first (X T s u a κ q : ℝ) (A G c D₁ C₂ C₃ : ℕ) (hX : 2 ≤ X) (hT : 1 ≤ T) (hs : 1 ≤ s) (hu : 1 ≤ u) (ha : a ≤ X ^ A)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ X ^ G) (hq : q ≤ X ^ (c + 1) * (u * X ^ C₂)) :
    a * ((κ + T * s * (u * X ^ C₂)) * X ^ D₁ + 2 * X ^ C₃) + q + X ^ C₃ ≤ X ^ (A + G + (D₁ + C₂ + C₃ + c + 4)) * T * (s * u) := by
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  obtain ⟨W, hW⟩ : ∃ W, W = T * s * u := ⟨_, rfl⟩
  have hW1 : 1 ≤ W := by rw [hW]; exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hT hs) hu
  have hW0 : 0 ≤ W := by linarith
  have huW : u ≤ W := by rw [hW]; exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le hT hs)
  have pw : ∀ i j : ℕ, i ≤ j → X ^ i ≤ X ^ j := fun i j h => pow_le_pow_right₀ hX1 h
  have e0 : T * s * (u * X ^ C₂) = W * X ^ C₂ := by rw [hW]; ring
  have e1 : X ^ (A + G + (D₁ + C₂ + C₃ + c + 4)) * T * (s * u) = X ^ (A + G + (D₁ + C₂ + C₃ + c + 4)) * W := by rw [hW]; ring
  rw [e0, e1]
  have b1 : κ + W * X ^ C₂ ≤ X ^ (G + C₂ + 1) * W := by
    have c1 : κ ≤ X ^ (G + C₂) * W :=
      calc κ ≤ X ^ G := hκ
        _ ≤ X ^ (G + C₂) := pw _ _ (by omega)
        _ ≤ X ^ (G + C₂) * W := le_mul_of_one_le_right (by positivity) hW1
    have c2 : W * X ^ C₂ ≤ X ^ (G + C₂) * W := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right (pw _ _ (by omega)) hW0
    have c3 : 2 * (X ^ (G + C₂) * W) ≤ X * (X ^ (G + C₂) * W) := mul_le_mul_of_nonneg_right hX (by positivity)
    calc κ + W * X ^ C₂ ≤ X * (X ^ (G + C₂) * W) := by linarith
      _ = X ^ (G + C₂ + 1) * W := by ring
  have b2 : (κ + W * X ^ C₂) * X ^ D₁ + 2 * X ^ C₃ ≤ X ^ (G + C₂ + D₁ + C₃ + 2) * W := by
    have c1 : (κ + W * X ^ C₂) * X ^ D₁ ≤ X ^ (G + C₂ + D₁ + C₃ + 1) * W :=
      calc (κ + W * X ^ C₂) * X ^ D₁ ≤ (X ^ (G + C₂ + 1) * W) * X ^ D₁ := mul_le_mul_of_nonneg_right b1 (by positivity)
        _ = X ^ (G + C₂ + 1 + D₁) * W := by ring
        _ ≤ X ^ (G + C₂ + D₁ + C₃ + 1) * W := mul_le_mul_of_nonneg_right (pw _ _ (by omega)) hW0
    have c2 : 2 * X ^ C₃ ≤ X ^ (G + C₂ + D₁ + C₃ + 1) * W :=
      calc 2 * X ^ C₃ ≤ X * X ^ C₃ := mul_le_mul_of_nonneg_right hX (by positivity)
        _ = X ^ (C₃ + 1) := by ring
        _ ≤ X ^ (G + C₂ + D₁ + C₃ + 1) := pw _ _ (by omega)
        _ ≤ X ^ (G + C₂ + D₁ + C₃ + 1) * W := le_mul_of_one_le_right (by positivity) hW1
    have c3 : 2 * (X ^ (G + C₂ + D₁ + C₃ + 1) * W) ≤ X * (X ^ (G + C₂ + D₁ + C₃ + 1) * W) :=
      mul_le_mul_of_nonneg_right hX (by positivity)
    calc (κ + W * X ^ C₂) * X ^ D₁ + 2 * X ^ C₃ ≤ X * (X ^ (G + C₂ + D₁ + C₃ + 1) * W) := by linarith
      _ = X ^ (G + C₂ + D₁ + C₃ + 2) * W := by ring
  obtain ⟨E, hE⟩ : ∃ E, E = A + G + C₂ + D₁ + C₃ + c + 2 := ⟨_, rfl⟩
  have b3 : a * ((κ + W * X ^ C₂) * X ^ D₁ + 2 * X ^ C₃) ≤ X ^ E * W :=
    calc a * ((κ + W * X ^ C₂) * X ^ D₁ + 2 * X ^ C₃) ≤ X ^ A * (X ^ (G + C₂ + D₁ + C₃ + 2) * W) :=
          mul_le_mul ha b2 (by positivity) (by positivity)
      _ = X ^ (A + (G + C₂ + D₁ + C₃ + 2)) * W := by ring
      _ ≤ X ^ E * W := mul_le_mul_of_nonneg_right (pw _ _ (by omega)) hW0
  have b4 : q ≤ X ^ E * W :=
    calc q ≤ X ^ (c + 1) * (u * X ^ C₂) := hq
      _ = X ^ (c + 1 + C₂) * u := by ring
      _ ≤ X ^ E * W := mul_le_mul (pw _ _ (by omega)) huW (by linarith) (by positivity)
  have b5 : X ^ C₃ ≤ X ^ E * W :=
    calc X ^ C₃ ≤ X ^ E := pw _ _ (by omega)
      _ ≤ X ^ E * W := le_mul_of_one_le_right (by positivity) hW1
  have h4 : 3 * (X ^ E * W) ≤ X ^ 2 * (X ^ E * W) := mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  have e2 : X ^ (A + G + (D₁ + C₂ + C₃ + c + 4)) = X ^ 2 * X ^ E := by rw [← pow_add]; congr 1; omega
  rw [e2]
  linarith

/-- The second inequality of the display, in real variables: x = e(ρ+3ζ)N, y = 2N/K + cλ, z =
e_{ℓ+1}N, A = cg⁴/4, G = g, k2 = K², Z = (c+5)C₀K². -/
theorem count_second (X T x y z : ℝ) (A G C₄ k2 Z : ℕ) (hX : 0 < X) (hT : T ≤ (2 : ℝ) ^ x * X ^ (A + k2 + Z)) (hxyz : x + y ≤ z) :
    X ^ (A + G + C₄) * T * (2 : ℝ) ^ y ≤ (2 : ℝ) ^ z * X ^ (2 * A + G + k2 + C₄ + Z) := by
  have h1 : (2 : ℝ) ^ x * (2 : ℝ) ^ y ≤ (2 : ℝ) ^ z := by
    rw [← Real.rpow_add (by norm_num)]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hxyz
  have hy : (0 : ℝ) < (2 : ℝ) ^ y := Real.rpow_pos_of_pos (by norm_num) _
  calc X ^ (A + G + C₄) * T * (2 : ℝ) ^ y ≤ X ^ (A + G + C₄) * ((2 : ℝ) ^ x * X ^ (A + k2 + Z)) * (2 : ℝ) ^ y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT (by positivity)) hy.le
    _ = ((2 : ℝ) ^ x * (2 : ℝ) ^ y) * X ^ (2 * A + G + k2 + C₄ + Z) := by ring
    _ ≤ (2 : ℝ) ^ z * X ^ (2 * A + G + k2 + C₄ + Z) := mul_le_mul_of_nonneg_right h1 (by positivity)

end GeneralPieces.Count
