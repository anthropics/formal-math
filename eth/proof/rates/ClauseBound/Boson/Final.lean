/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Boson.Half
public import ClauseBound.Part.Bounds

/-! # Bounds on `big h`, for the constant c of pieces with ρ = 1/√2

Elementary lemmas on the number `big h` of proof/rates/ClauseBound/Boson/Half.lean, of the kind
needed to choose the constant c of pieces with parameters (1/√2, c) (Definition 7, Appendix B); here
h is any natural number.
If h ≤ c₀·λ² and the partitions of the integers up to 4h are at most 2^(c₂·λ), then big h ≤ (2λ)^c
for c = c₁ + 4 + 40(c₀ + 1)² + c₂ (`big_le`); moreover 4h + 1 ≤ big h and h! < 2^(big h).
A factorization with values below b is also one with values below any larger bound
(`factorsThrough_mono`). -/

public section

namespace ClauseBound.Boson

open Finset

namespace Final

/-- A factorization with values below b is one with values below any b' ≥ b. -/
theorem factorsThrough_mono {X X' : Type} {F : X → X' → ℤ} {c : ℕ} {b b' : ℤ} (h : Pieces.FactorsThrough F c b) (hb : b ≤ b') :
    Pieces.FactorsThrough F c b' := by
  obtain ⟨f, f', h1, h2, h3⟩ := h
  exact ⟨f, f', h1, fun z θ => (h2 z θ).trans_le hb, fun z θ => (h3 z θ).trans_le hb⟩

/-- If h ≤ c₀·λ² and the partitions of the integers up to 4h are at most 2^(c₂·λ), then big h ≤
(2λ)^c for c = c₁ + 4 + 40(c₀ + 1)² + c₂. -/
theorem big_le {c₀ c₁ c₂ lam h : ℕ} (hl : 1 ≤ lam) (hh : h ≤ c₀ * lam ^ 2) (hS : ∑ E ∈ range (4 * h + 1), Partitions.p E ≤ 2 ^ (c₂ * lam)) :
    big h ≤ (2 * lam) ^ (c₁ + 4 + (40 * (c₀ + 1) ^ 2 + c₂)) := by
  have h0 : Nat.clog 2 (∑ E ∈ range (4 * h + 1), Partitions.p E) ≤ c₂ * lam := (Nat.clog_le_iff_le_pow (by norm_num)).2 hS
  have h1 : (h + 1) ^ 2 ≤ (c₀ + 1) ^ 2 * lam ^ 4 := by
    have : h + 1 ≤ (c₀ + 1) * lam ^ 2 := by
      have : 1 ≤ lam ^ 2 := Nat.one_le_pow _ _ hl
      rw [Nat.add_mul, Nat.one_mul]
      omega
    calc (h + 1) ^ 2 ≤ ((c₀ + 1) * lam ^ 2) ^ 2 := Nat.pow_le_pow_left this 2
      _ = (c₀ + 1) ^ 2 * lam ^ 4 := by ring
  have h2 : c₂ * lam ≤ c₂ * lam ^ 4 := Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) lam)
  have h3 : (40 * (c₀ + 1) ^ 2 + c₂) * lam ^ 4 ≤ (2 * lam) ^ (c₁ + 4 + (40 * (c₀ + 1) ^ 2 + c₂)) := by
    generalize 40 * (c₀ + 1) ^ 2 + c₂ = A
    have e1 : 1 ≤ (2 * lam) ^ c₁ := Nat.one_le_pow _ _ (by omega)
    have e2 : lam ^ 4 ≤ (2 * lam) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have e3 : A ≤ (2 * lam) ^ A := (Nat.lt_two_pow_self (n := A)).le.trans (Nat.pow_le_pow_left (by omega) A)
    calc A * lam ^ 4 = 1 * lam ^ 4 * A := by ring
      _ ≤ (2 * lam) ^ c₁ * (2 * lam) ^ 4 * (2 * lam) ^ A := Nat.mul_le_mul (Nat.mul_le_mul e1 e2) e3
      _ = (2 * lam) ^ (c₁ + 4 + A) := by rw [pow_add, pow_add]
  calc big h ≤ 40 * ((c₀ + 1) ^ 2 * lam ^ 4) + c₂ * lam ^ 4 := Nat.add_le_add (Nat.mul_le_mul_left _ h1) (h0.trans h2)
    _ = (40 * (c₀ + 1) ^ 2 + c₂) * lam ^ 4 := by ring
    _ ≤ _ := h3

/-- 4h + 1 ≤ big h. -/
theorem four_mul_add_one_le_big (h : ℕ) : 4 * h + 1 ≤ big h := by
  have : 4 * h + 1 ≤ 40 * (h + 1) ^ 2 := by nlinarith
  exact this.trans (Nat.le_add_right _ _)

/-- h! < 2^(big h). -/
theorem factorial_lt_two_pow_big (h : ℕ) : h.factorial < 2 ^ big h := by
  have h1 : h * h < big h := by
    have : h * h < 40 * (h + 1) ^ 2 := by nlinarith
    exact this.trans_le (Nat.le_add_right _ _)
  calc h.factorial ≤ h ^ h := Nat.factorial_le_pow h
    _ ≤ (2 ^ h) ^ h := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := h)).le h
    _ = 2 ^ (h * h) := (pow_mul 2 h h).symm
    _ < 2 ^ big h := Nat.pow_lt_pow_right (by norm_num) h1

end Final

open Final

end ClauseBound.Boson
