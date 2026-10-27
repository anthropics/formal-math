/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Ring.ThmHalfPieces
public import GeneralPieces.Half.Order

/-! # The sizes of the numbers that the programs for the pieces with ρ = 1/√2 return, from the sizes of Appendix B

The programs return entries of the integer matrices `ClauseBound.Boson.topK` and
`ClauseBound.Boson.botK`, which are the factors of displays (54) and (55), the first with the sign
(`GeneralPieces.Half.topK_eq`, `botK_eq`), and their sums of products are the pieces A_s
(`GeneralPieces.ApcL_eq_piece`).
So the bounds of the paragraph «Sizes and operations» hold for them: 2^{3h}·2^{12h²} for a factor
with a^⟨i⟩ (`GeneralPieces.Sizes.abs_factor_a_le`), h!·2^{12h²} for a factor with b
(`abs_factor_b_le`), and Δ times the product of the two for A_s
(`GeneralPieces.ThmHalfPieces.abs_piece_le`). The programs work with one bound for all numbers,
2^{40(h+1)² + ⌈log Δ⌉}, which the appendix does not name (it has 2^{O(h²)}); all three numbers are
below it (`GeneralPieces.ThmHalfPieces.bound_lt_big` for A_s, and `factor_lt_big` for the two
factors). -/

public section

namespace GeneralPieces.Half

open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes ClauseBound.Inst.Half

/-- Each of the two bounds for a factor is at most the bound for A_s, so it is below the one bound
of the programs. -/
theorem factor_lt_big (h : ℕ) : 2 ^ (3 * h) * 2 ^ (12 * h ^ 2) < 2 ^ ClauseBound.Boson.big h ∧ h.factorial * 2 ^ (12 * h ^ 2) < 2 ^ ClauseBound.Boson.big h := by
  have h1 : 1 ≤ Delta h := (ClauseBound.Part.p_pos 0).trans (single_le_sum (f := Partitions.p) (fun _ _ => Nat.zero_le _) (mem_range.2 (Nat.succ_pos _)))
  have h2 : 1 ≤ 2 ^ (3 * h) * 2 ^ (12 * h ^ 2) := Nat.mul_pos (by positivity) (by positivity)
  have h3 : 1 ≤ h.factorial * 2 ^ (12 * h ^ 2) := Nat.mul_pos h.factorial_pos (by positivity)
  have h4 := ThmHalfPieces.bound_lt_big h
  generalize 2 ^ (3 * h) * 2 ^ (12 * h ^ 2) = a at h2 h4 ⊢
  generalize h.factorial * 2 ^ (12 * h ^ 2) = b at h3 h4 ⊢
  have h5 : a ≤ a * b := Nat.le_mul_of_pos_right _ h3
  have h6 : b ≤ a * b := Nat.le_mul_of_pos_left _ h2
  have h7 : a * b ≤ Delta h * (a * b) := Nat.le_mul_of_pos_left _ h1
  exact ⟨(h5.trans h7).trans_lt h4, (h6.trans h7).trans_lt h4⟩

/-- The entries of the matrix that carries a^μ, at listed partitions, are below 2^{big h}, the one
bound of the programs. -/
theorem abs_topK_lt {h : ℕ} (hh : 1 ≤ h) {L : List ℕ} (hL : ClauseBound.Boson.Pos L) (hs : L.sum = h) (i : ℕ) (r : ℤ) {π σ : List ℕ} (hπ : ClauseBound.Boson.Pos π)
    (hπ' : π.sum ≤ 4 * h) (hσ : ClauseBound.Boson.Pos σ) (hσ' : σ.sum ≤ 4 * h) : |ClauseBound.Boson.topK L h i r (π : Multiset ℕ) (σ : Multiset ℕ)| < 2 ^ ClauseBound.Boson.big h := by
  have h1 := abs_factor_a_le hh i (ξ := ptn L) (by rw [wt_ptn hL, hs]) r (σ' := ptn π) (σ := ptn σ) (by rwa [wt_ptn hπ]) (by rwa [wt_ptn hσ])
  have h2 : |((ClauseBound.Boson.topK L h i r (π : Multiset ℕ) (σ : Multiset ℕ) : ℤ) : ℚ)| ≤ 2 ^ (3 * h) * 2 ^ (12 * h ^ 2) := by
    rw [← toN_ptn hπ, ← toN_ptn hσ, topK_eq hL hs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact h1
  have h3 : |ClauseBound.Boson.topK L h i r (π : Multiset ℕ) (σ : Multiset ℕ)| ≤ ((2 ^ (3 * h) * 2 ^ (12 * h ^ 2) : ℕ) : ℤ) := by exact_mod_cast h2
  exact h3.trans_lt (by exact_mod_cast (factor_lt_big h).1)

/-- The entries of the matrix that carries b^ν, at listed partitions, are below 2^{big h}. -/
theorem abs_botK_lt {h : ℕ} (hh : 1 ≤ h) {L : List ℕ} (hL : ClauseBound.Boson.Pos L) (hs : L.sum = h) (r : ℤ) {π σ : List ℕ} (hπ : ClauseBound.Boson.Pos π)
    (hπ' : π.sum ≤ 4 * h) (hσ : ClauseBound.Boson.Pos σ) (hσ' : σ.sum ≤ 4 * h) : |ClauseBound.Boson.botK L h r (π : Multiset ℕ) (σ : Multiset ℕ)| < 2 ^ ClauseBound.Boson.big h := by
  have h1 := abs_factor_b_le hh (ν := ptn L) (by rw [wt_ptn hL, hs]) r (σ' := ptn π) (σ := ptn σ) (by rwa [wt_ptn hπ]) (by rwa [wt_ptn hσ])
  have h2 : |((ClauseBound.Boson.botK L h r (π : Multiset ℕ) (σ : Multiset ℕ) : ℤ) : ℚ)| ≤ h.factorial * 2 ^ (12 * h ^ 2) := by
    rw [← toN_ptn hπ, ← toN_ptn hσ, botK_eq hL hs]
    exact h1
  have h3 : |ClauseBound.Boson.botK L h r (π : Multiset ℕ) (σ : Multiset ℕ)| ≤ ((h.factorial * 2 ^ (12 * h ^ 2) : ℕ) : ℤ) := by exact_mod_cast h2
  exact h3.trans_lt (by exact_mod_cast (factor_lt_big h).2)

/-- The values that the two programs of a factorization return, at a label that stands for a pair
(j, τ) with a listed partition τ, are below 2^{big h}. -/
theorem abs_valK_lt {h : ℕ} (hh : 1 ≤ h) (tr top : Bool) (s : ℤ) {α β : List ℕ} (hα : ClauseBound.Boson.Pos α ∧ α.sum = h) (hβ : ClauseBound.Boson.Pos β ∧ β.sum = h)
    {p : ℕ × List ℕ} (hp : ClauseBound.Boson.Pos p.2) (hp' : p.2.sum ≤ 4 * h) : |valK tr top h s α β p| < 2 ^ ClauseBound.Boson.big h := by
  have h2 : α.sum ≤ 4 * h := by omega
  have h3 : β.sum ≤ 4 * h := by omega
  cases tr <;> cases top <;> simp only [valK, cond_true, cond_false]
  · exact abs_botK_lt hh hβ.1 hβ.2 _ hα.1 h2 hp hp'
  · exact abs_topK_lt hh hα.1 hα.2 _ _ hp hp' hβ.1 h3
  · exact abs_botK_lt hh hβ.1 hβ.2 _ hp hp' hα.1 h2
  · exact abs_topK_lt hh hα.1 hα.2 _ _ hβ.1 h3 hp hp'

/-- «And A_s is a sum of at most Δ products of two factors»: the size of the integer functions that
the programs factorize. -/
theorem abs_ApcL_lt (hPF : PieceFacts) {lam h : ℕ} (hp : 2 ^ lam ≤ Partitions.p h) (hℓ : ∀ x : Pieces.Bits lam, ClauseBound.Boson.Pos (ell h x) ∧ (ell h x).sum = h) (hh : 1 ≤ h)
    {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) (x y u v : Pieces.Bits lam) : |ClauseBound.Boson.ApcL (ell h) h s x y u v| < 2 ^ ClauseBound.Boson.big h := by
  have h1 := ThmHalfPieces.abs_piece_le hPF (isMu hp) hh hs x y u v
  rw [← ApcL_eq_piece hPF hℓ hh] at h1
  have h2 : |ClauseBound.Boson.ApcL (ell h) h s x y u v| ≤ ((Delta h * ((2 ^ (3 * h) * 2 ^ (12 * h ^ 2)) * (h.factorial * 2 ^ (12 * h ^ 2))) : ℕ) : ℤ) := by exact_mod_cast h1
  exact h2.trans_lt (by exact_mod_cast ThmHalfPieces.bound_lt_big h)

end GeneralPieces.Half
