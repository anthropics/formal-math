/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.ArithStack

/-! # The profiles and the layers fit under the pad (the fields `prof` and `lay` of `MarkFits`)

One evaluation runs through `Mark.nProf g m (R + 2)` = (m+1)^(g·g·(R+2)) numbers as profiles, and
the division of the clauses into layers is a word of length
at most `layLen k n m R`. Here: for s = `sOf n` ≥ 1, g = 3·K⁸ with K = `Kseq (depthOf s)`, R =
`layersOf s`, every width k ≤ s and m = Δ·n clauses with any Δ ≤ 2^β, β = `betaOf s`, both numbers
are
at most every F with 2^(C₀·(⌊n/2^s⌋+1)) ≤ F, for C₀ ≥ 1; F is the length of the pad, the padding
string given to the algorithm with its input. No programs occur here. -/

public section

namespace PaddedDescent.F.Arith

open PaddedDescent

/-- The number of clauses of a sparsified formula, plus one, is at most 2^(β + size n). -/
theorem clauses_succ_le {Δ s : ℕ} (hΔ : Δ ≤ 2 ^ betaOf s) (n : ℕ) : Δ * n + 1 ≤ 2 ^ (betaOf s + Nat.size n) := by
  have h2 : n + 1 ≤ 2 ^ Nat.size n := Nat.lt_size_self n
  have h3 : 1 ≤ 2 ^ betaOf s := Nat.one_le_two_pow
  calc Δ * n + 1 ≤ 2 ^ betaOf s * n + 2 ^ betaOf s := Nat.add_le_add (Nat.mul_le_mul_right _ hΔ) h3
    _ = 2 ^ betaOf s * (n + 1) := by ring
    _ ≤ 2 ^ betaOf s * 2 ^ Nat.size n := Nat.mul_le_mul_left _ h2
    _ = 2 ^ (betaOf s + Nat.size n) := (pow_add _ _ _).symm

/-- The logarithm of the number of profiles is at most ⌊n/2^s⌋, for s = sOf n ≥ 1. -/
theorem prof_exponent_le {n : ℕ} (hs : 1 ≤ sOf n) :
    (betaOf (sOf n) + Nat.size n) * (Ytop (sOf n) * (layersOf (sOf n) + 2)) ≤ n / 2 ^ sOf n := by
  refine overhead_sOf_le_div (a := 3) (c := 3) hs (by norm_num) (by norm_num) ?_
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Ytop (sOf n) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = Nat.sqrt n + 1 := ⟨_, rfl⟩
  have h1 := betaOf_lt_Ytop (sOf n)
  have h2 := size_le_sqrt n
  rw [← hY] at h1 ⊢
  rw [← hr]
  have hr1 : 1 ≤ r := by omega
  have hY1 : 1 ≤ Y := by omega
  have hYr : Y ≤ Y * r := Nat.le_mul_of_pos_right _ hr1
  have hrY : r ≤ Y * r := Nat.le_mul_of_pos_left _ hY1
  have e1 : betaOf (sOf n) + Nat.size n ≤ 3 * (Y * r) := by omega
  have e2 : layersOf (sOf n) + 2 ≤ Y := by unfold layersOf; omega
  calc (betaOf (sOf n) + Nat.size n) * (Y * (layersOf (sOf n) + 2)) ≤ 3 * (Y * r) * (Y * Y) := by gcongr
    _ = 3 * Y ^ 3 * r := by ring

/-- The field `prof` of `MarkFits`: the pad has a unit for every number that is tried as a profile. -/
theorem nProf_le {Δ n C₀ F : ℕ} (hs : 1 ≤ sOf n) (hC : 1 ≤ C₀) (hF : 2 ^ (C₀ * (n / 2 ^ sOf n + 1)) ≤ F) (hΔ : Δ ≤ 2 ^ betaOf (sOf n)) :
    Mark.nProf (3 * Kseq (depthOf (sOf n)) ^ 8) (Δ * n) (layersOf (sOf n) + 2) ≤ F := by
  have hg : 3 * Kseq (depthOf (sOf n)) ^ 8 * (3 * Kseq (depthOf (sOf n)) ^ 8) = Ytop (sOf n) := by
    rw [Ytop, gtop, Ktop, sq]
  have h1 := prof_exponent_le hs
  unfold Mark.nProf
  rw [hg]
  calc (Δ * n + 1) ^ (Ytop (sOf n) * (layersOf (sOf n) + 2))
      ≤ (2 ^ (betaOf (sOf n) + Nat.size n)) ^ (Ytop (sOf n) * (layersOf (sOf n) + 2)) :=
        Nat.pow_le_pow_left (clauses_succ_le hΔ _) _
    _ = 2 ^ ((betaOf (sOf n) + Nat.size n) * (Ytop (sOf n) * (layersOf (sOf n) + 2))) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ (C₀ * (n / 2 ^ sOf n + 1)) := Nat.pow_le_pow_right (by norm_num) (h1.trans ((Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ hC)))
    _ ≤ F := hF

/-- The field `lay` of `MarkFits`: the word of the layers fits under the pad. -/
theorem layLen_le {k Δ n C₀ F : ℕ} (hs : 1 ≤ sOf n) (hC : 1 ≤ C₀) (hF : 2 ^ (C₀ * (n / 2 ^ sOf n + 1)) ≤ F) (hk : k ≤ sOf n)
    (hΔ : Δ ≤ 2 ^ betaOf (sOf n)) : layLen k n (Δ * n) (layersOf (sOf n)) ≤ F := by
  refine le_pad_of_le hs hC hF ?_
  obtain ⟨a, ha⟩ : ∃ a, a = 2 ^ Nat.size n := ⟨_, rfl⟩
  have hn : n < a := ha ▸ Nat.lt_size_self n
  have hbig := two_pow_betaOf_le hs
  have hlt : 4 * betaOf (sOf n) + 10 * sOf n + 1000 < 2 ^ (4 * betaOf (sOf n) + 10 * sOf n + 1000) := Nat.lt_two_pow_self
  have h1 : Δ ≤ a := (hΔ.trans (Nat.pow_le_pow_right (by norm_num) (by omega))).trans (hbig.trans hn.le)
  have h2 : layersOf (sOf n) + 1 ≤ a := by
    unfold layersOf
    omega
  have h3 := clause_word_le hn (show k < a by omega) (show 4 ≤ a by omega)
  have ha1 : 1 ≤ a := by omega
  have h5 : a ≤ a ^ 5 := Nat.le_self_pow (by norm_num) _
  have h9 : a ^ 5 ≤ a ^ 9 := Nat.pow_le_pow_right ha1 (by norm_num)
  unfold layLen
  calc Δ * n * (k * (3 * n + 5) + 10) + 4 * (layersOf (sOf n) + 1) + 2 ≤ a * a * a ^ 3 + 4 * a + 2 := by
        gcongr
    _ = a ^ 5 + 4 * a + 2 := by ring
    _ ≤ 2 ^ 30 * a ^ 9 := by
      norm_num
      omega
    _ = 2 ^ (9 * Nat.size n + 30) := by rw [ha, ← pow_mul, ← pow_add]; congr 1; ring

end PaddedDescent.F.Arith
