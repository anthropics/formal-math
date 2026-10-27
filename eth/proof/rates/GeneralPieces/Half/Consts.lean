/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Ring.ThmHalfPieces
public import ClauseBound.Inst.HalfIfc

/-! # The constants of the programs for the pieces with ρ = 1/√2, from the numbers of Appendix B

The programs `halfF c₀ c` have two constants. What these have to satisfy at a length λ is the
structure `ClauseBound.Inst.Half.Cst`. `exists_cst2`: there are constants that satisfy it at every λ
≥ 1.
Here h is the least integer ≥ 2 with p(h) ≥ 2^λ, and Δ is the number of the partitions of 0, …, 4h.
The fields come from the proof of the theorem on the pieces with ρ = 1/√2 in Appendix B:
* the number 4h + 1 of pieces, d = h! and c^row_s + c^col_s ≤ 2√2·λ + c·log 2λ are read off that
  theorem itself, in the form without the running time (`AppHalfPieces.ThmHalfPiecesPure`, a
  hypothesis here; `numbers_of_thmHalfPieces`);
* h ≤ c₀·λ² is the sentence «Hence h = O(λ²)» (`GeneralPieces.Bits.exists_hOf_le`);
* the rest speaks of numbers of the programs that the appendix does not name: the cut-off 2cλ for
  each number of bits, the number 40(h+1)² + ⌈log Δ⌉ of bits of all values (the appendix has sizes
  2^{O(h²)}), and the number
  2^10·(h+2)^4·(Δ+1)² of units of the pad that is enough for them (the appendix has Δ^{O(1)}
  operations). These are bounded by elementary arithmetic (`cap_le`;
  `ClauseBound.Boson.Final.big_le`; `pad_le`) from the display on
  c^row_s + c^col_s, from h ≤ c₀·λ² and from the sentence «log Δ = O(λ)»
  (`GeneralPieces.Bits.exists_Delta_le`).
Both h = O(λ²) and log Δ = O(λ) rest on display (46), the bounds on log p(E) from the
Hardy–Ramanujan formula, in the form proved in Lean as `ClauseBound.Part.exists_bounds`. -/

public section

namespace GeneralPieces

open Finset Real ClauseBound.Inst.Half

namespace Consts

/-- What the theorem on the pieces with ρ = 1/√2 says about numbers only: |𝓘| = 4h + 1 ≤ (2λ)^c, d =
h! < 2^{(2λ)^c}, and c^row_s + c^col_s ≤ 4ρλ + c·log 2λ for |s| ≤ 2h. -/
theorem numbers_of_thmHalfPieces (hT : AppHalfPieces.ThmHalfPiecesPure) : ∃ c : ℕ, ∀ lam : ℕ, 1 ≤ lam →
    4 * AppHalfPieces.hOf lam + 1 ≤ (2 * lam) ^ c ∧ (AppHalfPieces.hOf lam).factorial < 2 ^ (2 * lam) ^ c ∧
    ∀ s : ℤ, |s| ≤ 2 * (AppHalfPieces.hOf lam : ℤ) →
      ((Nat.clog 2 (AppHalfPieces.Rrow (AppHalfPieces.hOf lam) s) + Nat.clog 2 (AppHalfPieces.Rcol (AppHalfPieces.hOf lam) s) : ℕ) : ℝ) ≤ 4 * (1 / √2) * lam + c * logb 2 (2 * lam) := by
  obtain ⟨c, H⟩ := hT
  refine ⟨c, fun lam hl => ?_⟩
  obtain ⟨mu, P, -, hP, hd, hI, -, hrow, hcol⟩ := H lam hl
  refine ⟨?_, ?_, fun s hs => ?_⟩
  · have h1 := hP.card_I
    rw [hI, Int.card_Icc] at h1
    omega
  · have h1 := hP.abs_d
    rw [hd] at h1
    exact_mod_cast h1
  · have h1 := hP.caps s (by rw [hI]; exact mem_Icc.2 (abs_le.1 hs))
    rwa [hrow, hcol] at h1

/-- 4ρ = 2√2 ≤ 3. -/
theorem four_mul_rho_le : 4 * (1 / √(2 : ℝ)) ≤ 3 := by
  rw [Bits.four_mul_rho]
  have h1 : √(2 : ℝ) ≤ 3 / 2 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  linarith

/-- Two numbers of bits with a + b ≤ 4ρλ + c·log 2λ have a + b ≤ (3 + c)·λ, because 4ρ ≤ 3 and log
2λ ≤ λ. So the cut-off of the programs at 2c'λ bits is not active if 3 + c ≤ 2c'. -/
theorem cap_le {a b c lam : ℕ} (hl : 1 ≤ lam) (h : ((a + b : ℕ) : ℝ) ≤ 4 * (1 / √2) * lam + c * logb 2 (2 * lam)) : a + b ≤ (3 + c) * lam := by
  have h1 : 4 * (1 / √(2 : ℝ)) * lam ≤ 3 * lam := mul_le_mul_of_nonneg_right four_mul_rho_le (Nat.cast_nonneg _)
  have h2 : (c : ℝ) * logb 2 (2 * lam) ≤ c * lam := mul_le_mul_of_nonneg_left (Bits.logb_two_mul_le hl) (Nat.cast_nonneg _)
  have h3 : ((a + b : ℕ) : ℝ) ≤ (((3 + c) * lam : ℕ) : ℝ) := by
    push_cast at h ⊢
    linarith
  exact_mod_cast h3

/-- The pad of the programs: if h ≤ c₀·λ² and Δ ≤ 2^{c₂λ}, then 2^10·(h+2)^4·(Δ+1)² ≤
2^{(4c₀+2c₂+28)λ}. -/
theorem pad_le {c₀ c₂ lam h D : ℕ} (hl : 1 ≤ lam) (hh : h ≤ c₀ * lam ^ 2) (hD : D ≤ 2 ^ (c₂ * lam)) :
    2 ^ 10 * (h + 2) ^ 4 * (D + 1) ^ 2 ≤ 2 ^ ((4 * c₀ + 2 * c₂ + 28) * lam) := by
  have h2 : lam ^ 2 ≤ 2 ^ (2 * lam) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le 2
  have h3 : 1 ≤ lam ^ 2 := Nat.one_le_pow _ _ hl
  have h1 : h + 2 ≤ 2 ^ (c₀ + 2 + 2 * lam) :=
    calc h + 2 ≤ (c₀ + 2) * lam ^ 2 := by nlinarith
      _ ≤ 2 ^ (c₀ + 2) * 2 ^ (2 * lam) := Nat.mul_le_mul Nat.lt_two_pow_self.le h2
      _ = 2 ^ (c₀ + 2 + 2 * lam) := (pow_add _ _ _).symm
  have hD1 : D + 1 ≤ 2 ^ (c₂ * lam + 1) := by
    have : 1 ≤ 2 ^ (c₂ * lam) := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  have h4 : c₀ ≤ c₀ * lam := Nat.le_mul_of_pos_right _ hl
  calc 2 ^ 10 * (h + 2) ^ 4 * (D + 1) ^ 2 ≤ 2 ^ 10 * (2 ^ (c₀ + 2 + 2 * lam)) ^ 4 * (2 ^ (c₂ * lam + 1)) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 4)) (Nat.pow_le_pow_left hD1 2)
    _ = 2 ^ (10 + (c₀ + 2 + 2 * lam) * 4 + (c₂ * lam + 1) * 2) := by rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    _ ≤ 2 ^ ((4 * c₀ + 2 * c₂ + 28) * lam) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

end Consts

open Consts

/-- The choice of the constants in the last sentence of the proof, «if c is large enough»: there are
constants c₀ and c that are large enough for the programs at every length. -/
theorem exists_cst2 (hT : AppHalfPieces.ThmHalfPiecesPure) : ∃ c₀ c : ℕ, ∀ lam : ℕ, 1 ≤ lam → Cst c₀ c lam := by
  obtain ⟨B, C, hB⟩ := ClauseBound.Part.exists_bounds
  obtain ⟨cT, hnum⟩ := numbers_of_thmHalfPieces hT
  obtain ⟨c₀, hh0⟩ := Bits.exists_hOf_le hB
  obtain ⟨c₂, hall⟩ := Bits.exists_Delta_le hB
  refine ⟨c₀, cT + (4 * c₀ + 2 * c₂ + 28) + 4 + (40 * (c₀ + 1) ^ 2 + c₂), fun lam hl => ?_⟩
  have hh := hh0 lam hl
  have hD : ∑ E ∈ range (4 * AppHalfPieces.hOf lam + 1), Partitions.p E ≤ 2 ^ (c₂ * lam) := hall lam hl
  obtain ⟨h1, h2, h3⟩ := hnum lam hl
  have hbig := ClauseBound.Boson.Final.big_le (c₁ := cT + (4 * c₀ + 2 * c₂ + 28)) hl hh hD
  have hpad := pad_le hl hh hD
  generalize hc : cT + (4 * c₀ + 2 * c₂ + 28) + 4 + (40 * (c₀ + 1) ^ 2 + c₂) = c at hbig ⊢
  rw [Lex.hOf_eq] at hh hD h1 h2 h3 hbig hpad
  have hpow : (2 * lam) ^ cT ≤ (2 * lam) ^ c := Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨hh, h1.trans hpow, h2.trans_le (Nat.pow_le_pow_right (by norm_num) hpow), hbig,
    hpad.trans (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))), fun s hs => ?_⟩
  have h4 := cap_le hl (h3 s hs)
  have h5 : (3 + cT) * lam ≤ 2 * c * lam := Nat.mul_le_mul_right _ (by omega)
  have hL : 0 ≤ logb 2 (2 * (lam : ℝ)) := Real.logb_nonneg one_lt_two (by
    have : (1 : ℝ) ≤ lam := by exact_mod_cast hl
    linarith)
  have h6 : (cT : ℝ) * logb 2 (2 * (lam : ℝ)) ≤ (c : ℝ) * logb 2 (2 * (lam : ℝ)) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : cT ≤ c)) hL
  exact ⟨(Nat.le_add_right _ _).trans (h4.trans h5), (Nat.le_add_left _ _).trans (h4.trans h5), (h3 s hs).trans (by linarith)⟩

end GeneralPieces
