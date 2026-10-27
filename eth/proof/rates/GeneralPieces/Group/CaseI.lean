/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Defs
public import Groundwork.Net.Colouring
public import Mathlib.Algebra.Order.Floor.Ring

/-! # The lemma on groupings with explicit cost: case (i)

The proof of Lemma 8 first shows that some grouping has at most 2g/K nodes in every group and Y ≤ L
for all γ ≠ γ'. In case (i) this is shown in the proof of Lemma 1, by Chebyshev's inequality for
independent uniform χ(a): that is `Groundwork.Colouring.exists_colouring`, restated here with the
letters of Appendix A (`GeneralPieces.caseI`). It gives fewer than 2g/K nodes in every group. -/

public section

namespace GeneralPieces

open Finset

/-- Case (i): g = 3K⁸ and ζ = 1/(2K). If the numbers c_{a,b} are symmetric and every node shares at
most P bits in all, some grouping has fewer than 2g/K nodes in every group and
Y ≤ (U + 2ζgP)/K² = (U + gP/K)/K² for any two groups. The proof is
`Groundwork.Colouring.exists_colouring`, which has a natural number P; a real P is rounded down. -/
theorem caseI (K g : ℕ) (c : Fin g → Fin g → ℕ) (P ζ : ℝ) (hK : 2 ≤ K) (hg : g = 3 * K ^ 8) (hζ : ζ = 1 / (2 * K)) (hs : ∀ a b, c a b = c b a)
    (hP : ∀ a, ∑ b ∈ univ.erase a, (c a b : ℝ) ≤ P) :
    ∃ χ : Fin g → Fin K, (∀ γ, K * #{a | χ a = γ} < 2 * g) ∧
      ∀ γ γ', γ ≠ γ' → (∑ a with χ a = γ, ∑ b with χ b = γ', (c a b : ℝ)) ≤
        ((∑ a, ∑ b ∈ univ.erase a, (c a b : ℝ)) + 2 * ζ * g * P) / (K : ℝ) ^ 2 := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hg0 : 0 < g := by rw [hg]; positivity
  have her : ∀ a : Fin g, ({b | b ≠ a} : Finset (Fin g)) = univ.erase a := fun a => by
    ext b; simp
  have hP0 : 0 ≤ P := le_trans (sum_nonneg fun _ _ => Nat.cast_nonneg _) (hP ⟨0, hg0⟩)
  obtain ⟨χ, h1, h2⟩ := Groundwork.Colouring.exists_colouring hK hg.ge c hs ⌊P⌋₊ fun a => by
    rw [her]
    exact Nat.le_floor (by push_cast; exact hP a)
  refine ⟨χ, h1, fun γ γ' hne => ?_⟩
  have h3 := h2 γ γ' hne
  simp only [her] at h3
  have h4 : (K : ℝ) ^ 3 * (∑ a with χ a = γ, ∑ b with χ b = γ', (c a b : ℝ)) ≤
      K * (∑ a, ∑ b ∈ univ.erase a, (c a b : ℝ)) + g * (⌊P⌋₊ : ℝ) := by exact_mod_cast h3
  have h5 : (g : ℝ) * (⌊P⌋₊ : ℝ) ≤ g * P := mul_le_mul_of_nonneg_left (Nat.floor_le hP0) (Nat.cast_nonneg _)
  rw [hζ, le_div_iff₀ (by positivity)]
  have e : (∑ a, ∑ b ∈ univ.erase a, (c a b : ℝ)) + 2 * (1 / (2 * (K : ℝ))) * g * P =
      (K * (∑ a, ∑ b ∈ univ.erase a, (c a b : ℝ)) + g * P) / K := by field_simp
  rw [e, le_div_iff₀ hK0]
  calc (∑ a with χ a = γ, ∑ b with χ b = γ', (c a b : ℝ)) * (K : ℝ) ^ 2 * K
      = (K : ℝ) ^ 3 * (∑ a with χ a = γ, ∑ b with χ b = γ', (c a b : ℝ)) := by ring
    _ ≤ _ := h4.trans (by linarith)

end GeneralPieces
