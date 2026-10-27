/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import NamesInOrder.Defs
import MinOfBounds.Arith
import PairsToBound.Arith
import VariableBound.Paper.Arith
import VariableBound.Paper.Forms
import ClauseBound.Alg.End
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # The inequalities by which the added polynomial goes

If the variables are x₀ … x_(n−1) and each of them occurs, the input has at most 6·(km)² bits; as no
clause is repeated, it has at most k·(2n+1)^(k+3) bits. The first number is at most 2^{6X} for X =
km/√(log m), the second at most 2^{9Y} for Y = k²·n·log log n/√(log n). So a polynomial c·L^c in the
length L of the input is at most 2^{7c·X} and at most 2^{10c·Y}, hence at most 2^{10c·min(X, Y)},
and it goes into the constant of the exponent.

**What is proved.** `variablesAreFew`, `codeIsShort`, `polynomialIsBelowTheBoundInM` (c′ = 7c),
`polynomialIsBelowTheBoundInN` (c′ = 10c), `polynomialIsBelowTheBound` (c′ the larger of these two),
`alternationCostGoesIntoC` (C = q·(max(C₁, C₂, c′ + 1) + 2), c′ that of `polynomialIsBelowTheBound`
at c = 1) and `boundInMWithoutThePolynomial` (C′ = max(C, c′) + 1, c′ that of
`polynomialIsBelowTheBoundInM` at C).

**Who uses whom.** `codeIsShort` takes n ≤ km from `variablesAreFew`. `polynomialIsBelowTheBoundInM`
and `polynomialIsBelowTheBoundInN` come from one lemma (`poly_le_two_rpow`): if N ≤ 2^{aX} and X ≥
1, then c·N^c ≤ 2^{(c + ac)X}. `polynomialIsBelowTheBound` follows from these two and `codeIsShort`,
with `MinOfBounds.min_time_le`. `alternationCostGoesIntoC` takes the bound on the length of the
input from `polynomialIsBelowTheBound`; the cost itself is bounded by `PairsToBound.choice_le`.
`boundInMWithoutThePolynomial` follows from `codeIsShort` and `polynomialIsBelowTheBoundInM`. -/

public section

namespace NamesInOrder

open Turing MainTheoremForms VariableBound.Paper MinOfBounds PairsToBound
open Sat3 (CNF)

/-! ### The length of the input -/

/-- As every variable occurs and a clause has at most k literals, n ≤ k·m. -/
theorem variablesAreFew : VariablesAreFew := fun _ _ _ hφ ho => ClauseBound.Alg.End.n_le hφ ho

/-- ⌊log₂(2n)⌋ + 1 ≤ 2x if n ≤ x and x ≥ 1. -/
theorem log2_succ_le {n x : ℕ} (h : n ≤ x) (hx : 1 ≤ x) : Nat.log2 (2 * n) + 1 ≤ 2 * x := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.mul_zero, Nat.log2_zero]
    omega
  · have h1 : Nat.log2 (2 * n) < 2 * n := by
      rw [Nat.log2_eq_log_two]
      exact Nat.log_lt_self 2 (by omega)
    omega

/-- If every variable occurs and there is at least one clause, the input has at most 6·(km)² bits (k
≥ 1; n may be 0). -/
theorem length_le_sq {k n : ℕ} {φ : CNF n} (hk : 1 ≤ k) (hm : 1 ≤ φ.length) (hφ : SatK.IsKCNF k φ) (ho : SatM.AllOccur φ) : (SatM.enc k φ).length ≤ 6 * (k * φ.length) ^ 2 := by
  have hn := variablesAreFew k n φ hφ ho
  have hx : 1 ≤ k * φ.length := Nat.mul_pos hk hm
  have hkx : k ≤ k * φ.length := Nat.le_mul_of_pos_right k hm
  have hl := log2_succ_le hn hx
  rw [ClauseBound.Alg.End.length_enc]
  have e : φ.length * (k * (Nat.log2 (2 * n) + 1)) = k * φ.length * (Nat.log2 (2 * n) + 1) := by ring
  rw [e]
  generalize k * φ.length = x at *
  have h2 : x * (Nat.log2 (2 * n) + 1) ≤ x * (2 * x) := Nat.mul_le_mul_left x hl
  nlinarith

/-- As no clause is repeated, the input has at most k·(2n+1)^(k+3) bits (k ≥ 1, n ≥ 1). -/
theorem length_le_pow {k n : ℕ} {φ : CNF n} (hk : 1 ≤ k) (hn : 1 ≤ n) (hφ : SatK.IsKCNF k φ) : (SatM.enc k φ).length ≤ k * (2 * n + 1) ^ (k + 3) := by
  have hm := clauseCount k n φ hφ
  have hl := log2_succ_le (le_refl n) hn
  rw [ClauseBound.Alg.End.length_enc]
  generalize hy : 2 * n + 1 = y at *
  have hy3 : 3 ≤ y := by omega
  have h1 : φ.length * (k * (Nat.log2 (2 * n) + 1)) ≤ y ^ k * (k * y) := Nat.mul_le_mul hm (Nat.mul_le_mul_left k (by omega))
  have h2 : k + n + 2 ≤ k * y ^ 2 := by
    have : n + 3 ≤ y ^ 2 := by nlinarith
    nlinarith
  have h3 : y ^ 2 ≤ y ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : y ^ (k + 3) = y ^ (k + 1) * y ^ 2 := by rw [← pow_add]
  have h5 : y ^ k * (k * y) = k * y ^ (k + 1) := by rw [pow_succ]; ring
  have h6 : 9 ≤ y ^ 2 := by nlinarith
  have h7 : 0 < y ^ (k + 1) := by positivity
  rw [h4]
  calc k + n + 2 + φ.length * (k * (Nat.log2 (2 * n) + 1)) ≤ k * y ^ (k + 1) + k * y ^ (k + 1) := Nat.add_le_add (h2.trans (Nat.mul_le_mul_left k h3)) (h1.trans_eq h5)
    _ = k * (y ^ (k + 1) * 2) := by ring
    _ ≤ k * (y ^ (k + 1) * y ^ 2) := Nat.mul_le_mul_left k (Nat.mul_le_mul_left _ (by omega))

/-- The length of the input, and the two bounds on it. -/
theorem codeIsShort : CodeIsShort := by
  intro k n φ hk hn hφ
  refine ⟨ClauseBound.Alg.End.length_enc k φ, fun ho => ?_, length_le_pow hk hn hφ⟩
  have hm : 1 ≤ φ.length := by
    have := variablesAreFew k n φ hφ ho
    rcases Nat.eq_zero_or_pos φ.length with h0 | h0
    · rw [h0] at this
      omega
    · exact h0
  exact length_le_sq hk hm hφ ho

/-! ### Below the exponential terms -/

/-- If N ≤ 2^{aX} and X ≥ 1, then c·N^c ≤ 2^{(c + ac)X}. -/
theorem poly_le_two_rpow (c a : ℕ) {N : ℕ} {X : ℝ} (hX : 1 ≤ X) (hN : (N : ℝ) ≤ (2 : ℝ) ^ ((a : ℝ) * X)) : ((c * N ^ c : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((c + a * c : ℕ) : ℝ) * X) := by
  calc ((c * N ^ c : ℕ) : ℝ) = (c : ℝ) * (N : ℝ) ^ c := by push_cast; ring
    _ ≤ (2 : ℝ) ^ ((c : ℝ) * X) * ((2 : ℝ) ^ ((a : ℝ) * X)) ^ c := mul_le_mul (natCast_le_two_rpow c hX) (pow_le_pow_left₀ (Nat.cast_nonneg N) hN c) (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (((c + a * c : ℕ) : ℝ) * X) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul two_pos.le, ← Real.rpow_add two_pos]
        congr 1
        push_cast
        ring

/-- k ≤ km/√(log m) and log m ≤ km/√(log m), for k ≥ 1 and m ≥ 2. -/
theorem le_expM {k m : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) : (k : ℝ) ≤ expM k m ∧ lg m ≤ expM k m := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 := lg_le_div_sqrt hm
  have h2 := one_le_lg hm
  rw [expM_eq]
  constructor
  · nlinarith
  · nlinarith

/-- 6·(km)² ≤ 2^{6X}, X = km/√(log m), for k ≥ 1 and m ≥ 2. -/
theorem sq_le_two_rpow {k m : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) : ((6 * (k * m) ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((6 : ℕ) : ℝ) * expM k m) := by
  obtain ⟨h1, h2⟩ := le_expM hk hm
  have hX := two_le_expM hk hm
  have hk2 : (k : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
    have := natCast_le_two_rpow k (le_refl (1 : ℝ))
    rwa [mul_one] at this
  have hm2 : (m : ℝ) ^ 2 = (2 : ℝ) ^ (((2 : ℕ) : ℝ) * lg m) := natCast_pow_eq (by omega) 2
  have h8 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  calc ((6 * (k * m) ^ 2 : ℕ) : ℝ) = 6 * ((k : ℝ) ^ 2 * (m : ℝ) ^ 2) := by push_cast; ring
    _ ≤ 8 * (((2 : ℝ) ^ (k : ℝ)) ^ 2 * (m : ℝ) ^ 2) := by
        have a1 : (k : ℝ) ^ 2 ≤ ((2 : ℝ) ^ (k : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg k) hk2 2
        have a2 : (0 : ℝ) ≤ (m : ℝ) ^ 2 := by positivity
        have a3 : (0 : ℝ) ≤ (k : ℝ) ^ 2 * (m : ℝ) ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right a1 a2]
    _ = (2 : ℝ) ^ ((3 : ℝ) + (k : ℝ) * 2 + ((2 : ℕ) : ℝ) * lg m) := by
        rw [hm2, h8, ← Real.rpow_natCast ((2 : ℝ) ^ (k : ℝ)) 2, ← Real.rpow_mul two_pos.le, ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
        congr 1
        push_cast
        ring
    _ ≤ (2 : ℝ) ^ (((6 : ℕ) : ℝ) * expM k m) := by
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        push_cast
        linarith

/-- k·(2n+1)^(k+3) ≤ 2^{9Y}, Y = k²·n·log log n/√(log n), for k ≥ 1 and n ≥ 4. -/
theorem pow_le_two_rpow {k n : ℕ} (hk : 1 ≤ k) (hn : 4 ≤ n) : ((k * (2 * n + 1) ^ (k + 3) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((9 : ℕ) : ℝ) * expN k n) := by
  have h1 := mul_lg_le_expN hk hn
  have hL : 1 ≤ lg n := one_le_lg (by omega)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk2 : (k : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
    have := natCast_le_two_rpow k (le_refl (1 : ℝ))
    rwa [mul_one] at this
  have hnat : (2 * n + 1) ^ (k + 3) ≤ n ^ (8 * k) := by
    calc (2 * n + 1) ^ (k + 3) ≤ (n ^ 2) ^ (k + 3) := Nat.pow_le_pow_left (by nlinarith) _
      _ = n ^ (2 * (k + 3)) := by rw [← pow_mul]
      _ ≤ n ^ (8 * k) := Nat.pow_le_pow_right (by omega) (by omega)
  have hcast : (((2 * n + 1) ^ (k + 3) : ℕ) : ℝ) ≤ (n : ℝ) ^ (8 * k) := by exact_mod_cast hnat
  calc ((k * (2 * n + 1) ^ (k + 3) : ℕ) : ℝ) = (k : ℝ) * (((2 * n + 1) ^ (k + 3) : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (2 : ℝ) ^ (k : ℝ) * (n : ℝ) ^ (8 * k) := mul_le_mul hk2 hcast (Nat.cast_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ ((k : ℝ) + ((8 * k : ℕ) : ℝ) * lg n) := by rw [natCast_pow_eq (by omega) (8 * k), ← Real.rpow_add two_pos]
    _ ≤ (2 : ℝ) ^ (((9 : ℕ) : ℝ) * expN k n) := by
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        push_cast
        nlinarith

/-- A polynomial in km is below the bound in m. -/
theorem polynomialIsBelowTheBoundInM : PolynomialIsBelowTheBoundInM :=
  fun c => ⟨c + 6 * c, fun k m hk hm => Nat.le_floor (poly_le_two_rpow c 6 (by linarith [two_le_expM hk hm]) (sq_le_two_rpow hk hm))⟩

/-- A power of k·(2n+1)^(k+3) is below the bound in n. -/
theorem polynomialIsBelowTheBoundInN : PolynomialIsBelowTheBoundInN :=
  fun c => ⟨c + 9 * c, fun k n hk hn => Nat.le_floor (poly_le_two_rpow c 9 (by linarith [two_le_expN hk hn]) (pow_le_two_rpow hk hn))⟩

/-- The smaller of the two exponents is at least 2. -/
theorem two_le_min {k m n : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (hn : 4 ≤ n) : 2 ≤ min (expM k m) (expN k n) := le_min (two_le_expM hk hm) (two_le_expN hk hn)

/-- So a polynomial in the length of the input is below the bound of the Main Theorem: by
`codeIsShort` it is below both polynomials, which are below the two bounds. -/
theorem polynomialIsBelowTheBound : PolynomialIsBelowTheBound := by
  intro c
  obtain ⟨c₁, h₁⟩ := polynomialIsBelowTheBoundInM c
  obtain ⟨c₂, h₂⟩ := polynomialIsBelowTheBoundInN c
  refine ⟨max c₁ c₂, fun k n φ hk hφ hm hn ho => ?_⟩
  obtain ⟨-, hs, hp⟩ := codeIsShort k n φ hk (by omega) hφ
  have a₁ : c * (SatM.enc k φ).length ^ c ≤ timeM c₁ k φ.length := (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (hs ho) c)).trans (h₁ k φ.length hk hm)
  have a₂ : c * (SatM.enc k φ).length ^ c ≤ timeN c₂ k n := (Nat.mul_le_mul_left c (Nat.pow_le_pow_left hp c)).trans (h₂ k n hk hn)
  exact Nat.le_floor (((Nat.cast_le (α := ℝ)).2 (le_min a₁ a₂)).trans (min_time_le c₁ c₂ hk hm hn))

/-- The cost of the alternation goes into C: the length of the input is below the bound by
`polynomialIsBelowTheBound` at c = 1. -/
theorem alternationCostGoesIntoC : AlternationCostGoesIntoC := by
  intro C₁ C₂ q
  obtain ⟨c', hc'⟩ := polynomialIsBelowTheBound 1
  refine ⟨q * (max (max C₁ C₂) (c' + 1) + 2), fun k n φ hk hφ hm hn ho => ?_⟩
  have hX := two_le_min (n := n) hk hm hn
  have hX0 : 0 ≤ min (expM k φ.length) (expN k n) := by linarith
  have ht := (min_time_le C₁ C₂ hk hm hn).trans (two_rpow_mono (le_max_left (max C₁ C₂) (c' + 1)) hX0)
  have hL : ((SatM.enc k φ).length : ℝ) ≤ (2 : ℝ) ^ ((c' : ℝ) * min (expM k φ.length) (expN k n)) := by
    have h1 : (SatM.enc k φ).length ≤ timeMin c' k φ.length n := by
      have := hc' k n φ hk hφ hm hn ho
      rwa [one_mul, pow_one] at this
    exact ((Nat.cast_le (α := ℝ)).2 h1).trans (Nat.floor_le (by positivity))
  have hl : (((SatM.enc k φ).length + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((max (max C₁ C₂) (c' + 1) : ℕ) : ℝ) * min (expM k φ.length) (expN k n)) := by
    refine le_trans ?_ (two_rpow_mono (le_max_right (max C₁ C₂) (c' + 1)) hX0)
    have e : (2 : ℝ) ^ (((c' + 1 : ℕ) : ℝ) * min (expM k φ.length) (expN k n)) = (2 : ℝ) ^ ((c' : ℝ) * min (expM k φ.length) (expN k n)) * (2 : ℝ) ^ min (expM k φ.length) (expN k n) := by
      rw [← Real.rpow_add two_pos]
      congr 1
      push_cast
      ring
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ min (expM k φ.length) (expN k n) := by
      have := Real.rpow_le_rpow_of_exponent_le one_le_two (show (1 : ℝ) ≤ min (expM k φ.length) (expN k n) by linarith)
      rwa [Real.rpow_one] at this
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((c' : ℝ) * min (expM k φ.length) (expN k n)) := Real.one_le_rpow one_le_two (mul_nonneg (Nat.cast_nonneg c') hX0)
    have h3 := mul_le_mul_of_nonneg_left h2 (zero_le_one.trans h1)
    rw [e, Nat.cast_add, Nat.cast_one]
    linarith
  exact choice_le q (max (max C₁ C₂) (c' + 1)) (by linarith) ht hl

/-! ### The first sentence of Theorem A (c) with nothing added -/

/-- 2^{aX} + 2^{bX} ≤ 2^{(max(a, b) + 1)X}, all rounded down, X = km/√(log m). -/
theorem timeM_add_timeM_le (a b : ℕ) {k m : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) : timeM a k m + timeM b k m ≤ timeM (max a b + 1) k m := by
  have hX := two_le_expM hk hm
  have hX0 : 0 ≤ expM k m := by linarith
  have h1 : ((timeM a k m : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((max a b : ℕ) : ℝ) * expM k m) := (Nat.floor_le (by positivity)).trans (two_rpow_mono (le_max_left a b) hX0)
  have h2 : ((timeM b k m : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((max a b : ℕ) : ℝ) * expM k m) := (Nat.floor_le (by positivity)).trans (two_rpow_mono (le_max_right a b) hX0)
  have e : (2 : ℝ) ^ (((max a b + 1 : ℕ) : ℝ) * expM k m) = (2 : ℝ) ^ (((max a b : ℕ) : ℝ) * expM k m) * (2 : ℝ) ^ expM k m := by
    rw [← Real.rpow_add two_pos]
    congr 1
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have h3 : (2 : ℝ) ≤ (2 : ℝ) ^ expM k m := by
    have := Real.rpow_le_rpow_of_exponent_le one_le_two (show (1 : ℝ) ≤ expM k m by linarith)
    rwa [Real.rpow_one] at this
  have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (((max a b : ℕ) : ℝ) * expM k m) := by positivity
  have h4 := mul_le_mul_of_nonneg_left h3 hp
  refine Nat.le_floor ?_
  rw [e, Nat.cast_add]
  linarith

/-- EVERY machine that meets the bound in m with a polynomial in the length of the input added meets
it with nothing added, with another constant: by `codeIsShort` the length is at most 6·(km)², and by
`polynomialIsBelowTheBoundInM` the polynomial is below the bound in m. -/
theorem boundInMWithoutThePolynomial : BoundInMWithoutThePolynomial := by
  intro M C h
  obtain ⟨c', hc'⟩ := polynomialIsBelowTheBoundInM C
  refine ⟨max C c' + 1, fun k n φ hk hφ hm ho => ?_⟩
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      have := clauseCount k 0 φ hφ
      rw [Nat.mul_zero, Nat.zero_add, one_pow] at this
      omega
    · exact h0
  obtain ⟨-, hs, -⟩ := codeIsShort k n φ hk hn hφ
  obtain ⟨ev⟩ := h k n φ hk hφ hm ho
  have a₁ : C * (SatM.enc k φ).length ^ C ≤ timeM c' k φ.length := (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (hs ho) C)).trans (hc' k φ.length hk hm)
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ((Nat.add_le_add_left a₁ _).trans (timeM_add_timeM_le C c' hk hm))⟩⟩

end NamesInOrder
