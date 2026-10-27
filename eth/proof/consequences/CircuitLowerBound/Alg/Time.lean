/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.Alg.Machine
import ToTuring.Machine.EndTM
import Mathlib.Tactic

/-! # The circuit lower bound for E^NP (Section 7): the time bound of the algorithm

The arithmetic for the proof, elsewhere in this development, of the interface statement `StAlg` from
a procedure for #3-SAT and the statements on the formula (`StForm`), on circuits as data (`StNorm`),
on the schedule (`StCertSched`) and on the last place of a chain (`StFlip`). For a given c₀ the
engine for #3-SAT is
taken with δ = 1/(32·(3c₀ + a₀ + 1)), where a₀ is the constant of `StForm`, which does not depend on
the table; so the machine is fixed before the table. For a table e the formula has at most (3c₀ +
a₀)(m+1) + g(e) variables; so the engine takes
at most c·2^{(m+1+g(e))/32} steps, the host multiplies this by a polynomial in m whose coefficients
depend on e, and the product is at most 2^{⌊m/8⌋} from some m₀(e) on (`Time.exists_threshold`). -/

public section

namespace CircuitLowerBound

open ENP Groundwork Turing

namespace Time

/-- K·2^{m/32}·2^{m/32} ≤ 2^{⌊m/8⌋} for m ≥ 16(K + 1). -/
theorem final_le (K : ℕ) {m : ℕ} (hm : 16 * (K + 1) ≤ m) :
    (K : ℝ) * ((2 : ℝ) ^ ((1 / 32 : ℝ) * m) * (2 : ℝ) ^ ((1 / 32 : ℝ) * m)) ≤ (2 : ℝ) ^ (((m / 8 : ℕ) : ℝ)) := by
  have h1 : m < 8 * (m / 8 + 1) := Nat.lt_mul_div_succ m (by norm_num)
  have h2 : (m : ℝ) ≤ 8 * (((m / 8 : ℕ) : ℝ) + 1) := by exact_mod_cast h1.le
  have h3 : (16 : ℝ) * ((K : ℝ) + 1) ≤ m := by exact_mod_cast hm
  have h4 : (1 / 32 : ℝ) * m + (1 / 32 : ℝ) * m + K ≤ ((m / 8 : ℕ) : ℝ) := by linarith
  have h5 : (K : ℝ) ≤ (2 : ℝ) ^ (K : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast (Nat.lt_two_pow_self (n := K)).le
  calc (K : ℝ) * ((2 : ℝ) ^ ((1 / 32 : ℝ) * m) * (2 : ℝ) ^ ((1 / 32 : ℝ) * m))
      ≤ (2 : ℝ) ^ (K : ℝ) * ((2 : ℝ) ^ ((1 / 32 : ℝ) * m) * (2 : ℝ) ^ ((1 / 32 : ℝ) * m)) :=
        mul_le_mul_of_nonneg_right h5 (by positivity)
    _ = (2 : ℝ) ^ ((1 / 32 : ℝ) * m + (1 / 32 : ℝ) * m + K) := by
        rw [Real.rpow_add two_pos, Real.rpow_add two_pos]
        ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two h4

/-- The length of the input and the size of the states are polynomial in m. Here n is the number of
gates and Nv the number of variables. -/
theorem base_le {cE c₀ a₀ G m n Nv : ℕ} (hn : n ≤ c₀ * (m + 1)) (hNv : Nv ≤ 3 * n + a₀ * (m + 1) + G) :
    (m + 1 + ((m + n) + 1 + n * (4 + 2 * (m + n)))) + cE * (Nv + 2) ^ cE + 1
      ≤ (8 + cE) * (3 * c₀ + a₀ + G + 2) ^ (cE + 2) * (m + 2) ^ (cE + 2) := by
  obtain ⟨X, hX⟩ : ∃ X, X = (3 * c₀ + a₀ + G + 2) * (m + 2) := ⟨_, rfl⟩
  have h1 : m + 2 ≤ X := by rw [hX]; nlinarith
  have h2 : m + n + 1 ≤ X := by rw [hX]; nlinarith
  have h3 : Nv + 2 ≤ X := by rw [hX]; nlinarith
  have h4 : (m + 1 + ((m + n) + 1 + n * (4 + 2 * (m + n)))) + 1 ≤ 8 * X ^ 2 := by
    have h5 : n * (4 + 2 * (m + n)) ≤ X * (4 + 2 * X) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have h6 : X ^ 2 ≤ X ^ (cE + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have h7 : (Nv + 2) ^ cE ≤ X ^ (cE + 2) := (Nat.pow_le_pow_left h3 cE).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have h8 := Nat.mul_le_mul_left cE h7
  rw [mul_assoc, ← mul_pow, ← hX, add_mul]
  omega

/-- The threshold. -/
theorem exists_threshold (q cE c₀ a₀ G : ℕ) : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ n Nv T : ℕ, n ≤ c₀ * (m + 1) → Nv ≤ 3 * n + a₀ * (m + 1) + G →
    (T : ℝ) ≤ cE * (2 : ℝ) ^ (1 / (32 * ((3 * c₀ + a₀ + 1 : ℕ) : ℝ)) * Nv) →
    q * (T + 1) * ((m + 1 + ((m + n) + 1 + n * (4 + 2 * (m + n)))) + cE * (Nv + 2) ^ cE + 1) ^ q ≤ 2 ^ (m / 8) := by
  obtain ⟨C₁, hC₁⟩ := exists_pow_le ((cE + 2) * q) (ε := 1 / 32) (by norm_num)
  obtain ⟨Kb, hKb⟩ : ∃ Kb, Kb = (8 + cE) * (3 * c₀ + a₀ + G + 2) ^ (cE + 2) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = q * ((cE + 1) * 2 ^ (G + 1)) * (Kb ^ q * C₁) := ⟨_, rfl⟩
  refine ⟨16 * (K + 1), fun m hm n Nv T hn hNv hT => ?_⟩
  have hb := base_le (cE := cE) hn hNv
  rw [← hKb] at hb
  obtain ⟨base, hbase⟩ : ∃ base, base = (m + 1 + ((m + n) + 1 + n * (4 + 2 * (m + n)))) + cE * (Nv + 2) ^ cE + 1 := ⟨_, rfl⟩
  rw [← hbase] at hb ⊢
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (2 : ℝ) ^ ((1 / 32 : ℝ) * m) := ⟨_, rfl⟩
  have hp0 : 0 < p := by rw [hp]; positivity
  -- the polynomial part
  have h1 : ((base : ℝ)) ^ q ≤ ((Kb ^ q * C₁ : ℕ) : ℝ) * p := by
    have h2 : (base : ℝ) ≤ (Kb : ℝ) * ((m : ℝ) + 2) ^ (cE + 2) := by exact_mod_cast hb
    calc ((base : ℝ)) ^ q ≤ ((Kb : ℝ) * ((m : ℝ) + 2) ^ (cE + 2)) ^ q := by gcongr
      _ = (Kb : ℝ) ^ q * ((m : ℝ) + 2) ^ ((cE + 2) * q) := by rw [mul_pow, ← pow_mul]
      _ ≤ (Kb : ℝ) ^ q * (C₁ * (2 : ℝ) ^ ((1 / 32 : ℝ) * m)) := by gcongr; exact hC₁ m
      _ = _ := by rw [hp]; push_cast; ring
  -- the exponential part
  have h3 : (T : ℝ) + 1 ≤ (((cE + 1) * 2 ^ (G + 1) : ℕ) : ℝ) * p := by
    obtain ⟨A, hA⟩ : ∃ A : ℕ, A = 3 * c₀ + a₀ + 1 := ⟨_, rfl⟩
    rw [← hA] at hT
    have hA0 : (0 : ℝ) < A := by rw [hA]; positivity
    have h4 : Nv ≤ A * (m + 1 + G) := by rw [hA]; nlinarith
    have h5 : (Nv : ℝ) ≤ A * ((m : ℝ) + 1 + G) := by exact_mod_cast h4
    have h6 : 1 / (32 * (A : ℝ)) * Nv ≤ (1 / 32 : ℝ) * m + ((G + 1 : ℕ) : ℝ) := by
      have h7 : 1 / (32 * (A : ℝ)) * Nv ≤ 1 / (32 * (A : ℝ)) * (A * ((m : ℝ) + 1 + G)) := mul_le_mul_of_nonneg_left h5 (by positivity)
      have h8 : 1 / (32 * (A : ℝ)) * (A * ((m : ℝ) + 1 + G)) = ((m : ℝ) + 1 + G) / 32 := by field_simp
      have h9 : (0 : ℝ) ≤ G := Nat.cast_nonneg G
      push_cast
      linarith
    have h10 : (2 : ℝ) ^ (1 / (32 * (A : ℝ)) * Nv) ≤ p * (2 : ℝ) ^ (G + 1) := by
      rw [hp, ← Real.rpow_natCast 2 (G + 1), ← Real.rpow_add two_pos]
      exact Real.rpow_le_rpow_of_exponent_le one_le_two h6
    have h11 : (1 : ℝ) ≤ p * (2 : ℝ) ^ (G + 1) := by
      have h12 : (1 : ℝ) ≤ p := by rw [hp]; exact Real.one_le_rpow one_le_two (by positivity)
      have h13 : (1 : ℝ) ≤ (2 : ℝ) ^ (G + 1) := one_le_pow₀ one_le_two
      nlinarith
    have h14 : (cE : ℝ) * (2 : ℝ) ^ (1 / (32 * (A : ℝ)) * Nv) ≤ cE * (p * (2 : ℝ) ^ (G + 1)) := mul_le_mul_of_nonneg_left h10 (Nat.cast_nonneg _)
    push_cast
    nlinarith
  have h15 : ((q * (T + 1) * base ^ q : ℕ) : ℝ) ≤ ((2 ^ (m / 8) : ℕ) : ℝ) := by
    calc ((q * (T + 1) * base ^ q : ℕ) : ℝ) = (q : ℝ) * ((T : ℝ) + 1) * (base : ℝ) ^ q := by push_cast; ring
      _ ≤ (q : ℝ) * ((((cE + 1) * 2 ^ (G + 1) : ℕ) : ℝ) * p) * (((Kb ^ q * C₁ : ℕ) : ℝ) * p) := by gcongr
      _ = (K : ℝ) * (p * p) := by rw [hK]; push_cast; ring
      _ ≤ (2 : ℝ) ^ (((m / 8 : ℕ) : ℝ)) := by rw [hp]; exact final_le K hm
      _ = _ := by rw [Real.rpow_natCast]; push_cast; rfl
  exact_mod_cast h15

end Time

end CircuitLowerBound
