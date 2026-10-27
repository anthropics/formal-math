/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import MainTheoremFormsStatement
import Wrap.Arith
import VariableBound.Paper.Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # A polynomial in a time bound of the Main Theorem's form stays below c·2^{c·9·n·lg lg(n+4)/√(lg(n+4))}
An expression of this kind bounds the time of a machine that decides 3-SAT on the plain input code
by a polynomial-time front end and a simulation of a machine that counts within the bound of the
Main Theorem.
The expression is that of Arith.lean: q·(t + X + 1)^q, where t is 2^{C₁·min{m'/√(lg m'), n'·lg lg
n'/√(lg n')}}, rounded down, plus C₂·L^{C₂}, with 4 ≤ n' ≤ n + 4, and L and X are at most a·(n+2)^d.
The main lemma of this file, `Wrap.wrapped_time_le_rate`, says: there is a c such that the whole
expression is at most ⌊c·2^{c·9·n·r(n)}⌋ with r(n) = lg lg(n+4)/√(lg(n+4)), for all n, m', n', L, X
within these bounds.

The steps, with E = n·r(n):
1. `div_sqrt_lg_mono`: x/√(lg x) grows with x ≥ 2. So n'·lg lg n'/√(lg n') ≤ (n+4)·r(n)
   (`exponent_le`), and this is at most E + 32, because r(n) ≤ 8 (`rate_le_eight`).
2. `lg_le_rate`: lg(n+4) ≤ 64·E + 256. So (n+2)^D ≤ 2^{D·(64·E + 256)} (`pow_le_rate`).
3. So t + X + 1 ≤ K·2^{κE} with constants K and κ = C₁ + 64·(d·C₂ + d), and the q-th power of the
   right side is K^q·2^{qκE}.

Only the bound in n' of the minimum is used. Only numbers; no machine and no formula occurs in this
file. Throughout, lg is the logarithm to base 2. -/

public section

namespace Wrap

open MainTheoremForms

namespace Arith

/-! ### The rate -/

/-- The rate with exponents 1 and 1/2, written with lg and a square root: lg lg(n+4)/√(lg(n+4)). -/
theorem rate_eq (n : ℕ) : SatK.rN 1 (1 / 2) n = lg (lg ((n : ℝ) + 4)) / Real.sqrt (lg ((n : ℝ) + 4)) := by
  unfold SatK.rN
  rw [← Real.sqrt_eq_rpow, pow_one]
  rfl

/-- lg(n+4) ≥ 2 and lg lg(n+4) ≥ 1, for every n ≥ 0. -/
theorem lg_add_four_facts (n : ℕ) : 2 ≤ lg ((n : ℝ) + 4) ∧ 1 ≤ lg (lg ((n : ℝ) + 4)) := by
  obtain ⟨h1, -, h2, -, -⟩ := VariableBound.Paper.lg_add_four (n := n + 4) (by omega)
  push_cast at h1 h2
  exact ⟨h1, h2⟩

/-- The rate is not negative. -/
theorem rate_nonneg (n : ℕ) : 0 ≤ SatK.rN 1 (1 / 2) n := by
  obtain ⟨-, h2⟩ := lg_add_four_facts n
  rw [rate_eq]
  exact div_nonneg (by linarith) (Real.sqrt_nonneg _)

/-- The rate is at most 8. -/
theorem rate_le_eight (n : ℕ) : SatK.rN 1 (1 / 2) n ≤ 8 := by
  obtain ⟨h1, -⟩ := lg_add_four_facts n
  have hw1 : 1 ≤ Real.sqrt (Real.sqrt (lg ((n : ℝ) + 4))) := Real.one_le_sqrt.2 (Real.one_le_sqrt.2 (by linarith))
  rw [rate_eq]
  exact (lg_div_sqrt_le (by linarith)).trans (div_le_self (by norm_num) hw1)

/-! ### x/√(lg x) grows -/

/-- lg t ≤ 2·(t − 1) for t ≥ 1. -/
theorem lg_le_two_mul_sub {t : ℝ} (ht : 1 ≤ t) : lg t ≤ 2 * (t - 1) := by
  have h2 := half_lt_log_two
  have hl : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos (by linarith)
  unfold lg Real.logb
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 ht) (sub_pos.2 h2).le]

/-- lg x ≥ 1 for real x ≥ 2. -/
theorem one_le_lg_real {x : ℝ} (hx : 2 ≤ x) : 1 ≤ lg x := by
  rw [← VariableBound.Paper.lg_two]
  exact VariableBound.Paper.lg_mono two_pos hx

/-- x²·lg y ≤ y²·lg x for 2 ≤ x ≤ y. With t = y/x: lg y = lg x + lg t ≤ lg x + 2(t−1) ≤ t²·lg x,
because lg x ≥ 1. -/
theorem sq_mul_lg_le {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) : x ^ 2 * lg y ≤ y ^ 2 * lg x := by
  have hx0 : 0 < x := by linarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = y / x := ⟨_, rfl⟩
  have ht1 : 1 ≤ t := by rw [ht]; exact (one_le_div hx0).2 hxy
  have hy : y = x * t := by rw [ht]; field_simp
  have hl1 := one_le_lg_real hx
  have hlt := lg_le_two_mul_sub ht1
  have hly : lg y = lg x + lg t := by
    rw [hy]
    unfold lg
    exact Real.logb_mul hx0.ne' (by linarith)
  have key : lg x + lg t ≤ t ^ 2 * lg x := by
    nlinarith [mul_nonneg (sq_nonneg (t - 1)) (by linarith : (0 : ℝ) ≤ lg x), mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hl1)]
  rw [hly, hy]
  calc x ^ 2 * (lg x + lg t) ≤ x ^ 2 * (t ^ 2 * lg x) := mul_le_mul_of_nonneg_left key (by positivity)
    _ = (x * t) ^ 2 * lg x := by ring

/-- x/√(lg x) ≤ y/√(lg y) for 2 ≤ x ≤ y. -/
theorem div_sqrt_lg_mono {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) : x / Real.sqrt (lg x) ≤ y / Real.sqrt (lg y) := by
  have hlx := one_le_lg_real hx
  have hly := one_le_lg_real (hx.trans hxy)
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 (by linarith)) (Real.sqrt_pos.2 (by linarith))]
  refine (pow_le_pow_iff_left₀ (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
  exact sq_mul_lg_le hx hxy

/-- n'·lg lg n'/√(lg n') ≤ (n+4)·lg lg(n+4)/√(lg(n+4)) for 4 ≤ n' ≤ n + 4. -/
theorem exponent_le {n n' : ℕ} (hn' : 4 ≤ n') (hnn : n' ≤ n + 4) :
    (n' : ℝ) * lg (lg n') / Real.sqrt (lg n') ≤ ((n : ℝ) + 4) * SatK.rN 1 (1 / 2) n := by
  have h4 : (4 : ℝ) ≤ n' := by exact_mod_cast hn'
  have hle : (n' : ℝ) ≤ (n : ℝ) + 4 := by exact_mod_cast hnn
  obtain ⟨hL2, -, hl1, -, -⟩ := VariableBound.Paper.lg_add_four hn'
  have hmono := div_sqrt_lg_mono (by linarith) hle
  have hll : lg (lg n') ≤ lg (lg ((n : ℝ) + 4)) := VariableBound.Paper.lg_mono (by linarith) (VariableBound.Paper.lg_mono (by linarith) hle)
  rw [rate_eq]
  calc (n' : ℝ) * lg (lg n') / Real.sqrt (lg n') = (n' : ℝ) / Real.sqrt (lg n') * lg (lg n') := by ring
    _ ≤ ((n : ℝ) + 4) / Real.sqrt (lg ((n : ℝ) + 4)) * lg (lg ((n : ℝ) + 4)) :=
        mul_le_mul hmono hll (by linarith) (div_nonneg (by positivity) (Real.sqrt_nonneg _))
    _ = ((n : ℝ) + 4) * (lg (lg ((n : ℝ) + 4)) / Real.sqrt (lg ((n : ℝ) + 4))) := by ring

/-! ### A polynomial is below a power of 2 with the rate in the exponent -/

/-- lg(n+4) ≤ 64·n·r(n) + 256 with r(n) = lg lg(n+4)/√(lg(n+4)). With Λ = lg(n+4): Λ·√Λ ≤ Λ² ≤
64·√(n+4) ≤ 64·(n+4); divide by √Λ ≥ 1 and use lg Λ ≥ 1. -/
theorem lg_le_rate (n : ℕ) : lg ((n : ℝ) + 4) ≤ 64 * ((n : ℝ) * SatK.rN 1 (1 / 2) n) + 256 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hN : (0 : ℝ) < (n : ℝ) + 4 := by positivity
  obtain ⟨h2, hl⟩ := lg_add_four_facts n
  have hroot := lg_le_fourth_root hN
  rw [rate_eq]
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = lg ((n : ℝ) + 4) := ⟨_, rfl⟩
  rw [← hΛ] at h2 hl hroot ⊢
  have hv1 : 1 ≤ Real.sqrt ((n : ℝ) + 4) := Real.one_le_sqrt.2 (by linarith)
  have hvv : Real.sqrt ((n : ℝ) + 4) * Real.sqrt ((n : ℝ) + 4) = (n : ℝ) + 4 := Real.mul_self_sqrt hN.le
  have hww : Real.sqrt (Real.sqrt ((n : ℝ) + 4)) * Real.sqrt (Real.sqrt ((n : ℝ) + 4)) = Real.sqrt ((n : ℝ) + 4) := Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hsq : Λ * Λ ≤ 64 * ((n : ℝ) + 4) := by
    have h3 : Λ * Λ ≤ (8 * Real.sqrt (Real.sqrt ((n : ℝ) + 4))) * (8 * Real.sqrt (Real.sqrt ((n : ℝ) + 4))) := mul_self_le_mul_self (by linarith) hroot
    have h4 : Real.sqrt ((n : ℝ) + 4) ≤ (n : ℝ) + 4 := by nlinarith
    nlinarith
  have hs1 : 1 ≤ Real.sqrt Λ := Real.one_le_sqrt.2 (by linarith)
  have hs0 : 0 < Real.sqrt Λ := by linarith
  have hss : Real.sqrt Λ * Real.sqrt Λ = Λ := Real.mul_self_sqrt (by linarith)
  have a1 : Λ * Real.sqrt Λ ≤ 64 * ((n : ℝ) + 4) := by
    have h5 : Real.sqrt Λ ≤ Λ := by nlinarith
    have h6 : Λ * Real.sqrt Λ ≤ Λ * Λ := mul_le_mul_of_nonneg_left h5 (by linarith)
    linarith
  have a2 : Λ ≤ 64 * ((n : ℝ) + 4) / Real.sqrt Λ := (le_div_iff₀ hs0).2 a1
  have a3 : 64 * ((n : ℝ) + 4) / Real.sqrt Λ = 64 * ((n : ℝ) / Real.sqrt Λ) + 256 / Real.sqrt Λ := by ring
  have a4 : 256 / Real.sqrt Λ ≤ 256 := div_le_self (by norm_num) hs1
  have a5 : (n : ℝ) / Real.sqrt Λ ≤ (n : ℝ) * (lg Λ / Real.sqrt Λ) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_right hn0 hl) hs0.le
  linarith

/-- (n+2)^D ≤ 2^{D·(64·n·r(n) + 256)} with r(n) = lg lg(n+4)/√(lg(n+4)), because n + 2 ≤ n + 4 =
2^{lg(n+4)}. -/
theorem pow_le_rate (D n : ℕ) : ((n : ℝ) + 2) ^ D ≤ (2 : ℝ) ^ ((D : ℝ) * (64 * ((n : ℝ) * SatK.rN 1 (1 / 2) n) + 256)) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hN : (0 : ℝ) < (n : ℝ) + 4 := by positivity
  have e : (2 : ℝ) ^ lg ((n : ℝ) + 4) = (n : ℝ) + 4 := Real.rpow_logb two_pos (by norm_num) hN
  calc ((n : ℝ) + 2) ^ D ≤ ((n : ℝ) + 4) ^ D := pow_le_pow_left₀ (by positivity) (by linarith) D
    _ = (2 : ℝ) ^ ((D : ℝ) * lg ((n : ℝ) + 4)) := by
        rw [mul_comm, Real.rpow_mul zero_le_two, e, Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ ((D : ℝ) * (64 * ((n : ℝ) * SatK.rN 1 (1 / 2) n) + 256)) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left (lg_le_rate n) (Nat.cast_nonneg D))

end Arith

/-! ### The main lemma -/

open Arith

/-- For all q, C₁, C₂, a, d there is a c such that q·(⌊2^{C₁·min{m'/√(lg m'), n'·lg lg n'/√(lg
n')}}⌋ + C₂·L^{C₂} + X + 1)^q ≤ ⌊c·2^{c·9·n·lg lg(n+4)/√(lg(n+4))}⌋ whenever m' ≥ 2, 4 ≤ n' ≤ n + 4
and L, X ≤ a·(n+2)^d.
The proof does not use m' ≥ 2. -/
theorem wrapped_time_le_rate (q C₁ C₂ a d : ℕ) :
    ∃ c : ℕ, ∀ (n m' n' L X : ℕ), 2 ≤ m' → 4 ≤ n' → n' ≤ n + 4 → L ≤ a * (n + 2) ^ d → X ≤ a * (n + 2) ^ d →
      q * ((MainTheoremForms.timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1) ^ q ≤ SatM.boundNK (SatK.rN 1 (1 / 2)) c 3 n := by
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = d * C₂ + d := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = C₂ * a ^ C₂ + a + 1 := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℕ, κ = C₁ + 64 * D := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (2 : ℝ) ^ ((C₁ : ℝ) * 32) + (A : ℝ) * (2 : ℝ) ^ ((D : ℝ) * 256) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨c₀, hc₀⟩ := exists_nat_ge ((q : ℝ) * K ^ q)
  refine ⟨c₀ + κ * q, fun n m' n' L X _ hn' hnn hL hX => Nat.le_floor ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (n : ℝ) * SatK.rN 1 (1 / 2) n := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; exact mul_nonneg hn0 (rate_nonneg n)
  have hC₁κ : (C₁ : ℝ) ≤ κ := by rw [hκ]; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) D]
  have hDκ : (D : ℝ) * 64 ≤ κ := by rw [hκ]; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) C₁]
  have hT : (timeMin3 C₁ m' n' : ℝ) ≤ (2 : ℝ) ^ ((C₁ : ℝ) * 32) * (2 : ℝ) ^ ((κ : ℝ) * E) := by
    have h1 : (n' : ℝ) * lg (lg n') / Real.sqrt (lg n') ≤ 32 + E := by
      have h2 := exponent_le hn' hnn
      have h3 := rate_le_eight n
      rw [hE]
      linarith
    calc (timeMin3 C₁ m' n' : ℝ) ≤ (2 : ℝ) ^ ((C₁ : ℝ) * ((n' : ℝ) * lg (lg n') / Real.sqrt (lg n'))) := timeMin3_le C₁ m' n'
      _ ≤ (2 : ℝ) ^ ((C₁ : ℝ) * (32 + E)) := Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg C₁))
      _ = (2 : ℝ) ^ ((C₁ : ℝ) * 32) * (2 : ℝ) ^ ((C₁ : ℝ) * E) := by rw [mul_add, Real.rpow_add two_pos]
      _ ≤ (2 : ℝ) ^ ((C₁ : ℝ) * 32) * (2 : ℝ) ^ ((κ : ℝ) * E) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right hC₁κ hE0)) (Real.rpow_nonneg zero_le_two _)
  have hQ : ((C₂ * L ^ C₂ + X + 1 : ℕ) : ℝ) ≤ (A : ℝ) * (2 : ℝ) ^ ((D : ℝ) * 256) * (2 : ℝ) ^ ((κ : ℝ) * E) := by
    calc ((C₂ * L ^ C₂ + X + 1 : ℕ) : ℝ) ≤ ((A * (n + 2) ^ D : ℕ) : ℝ) := by
          rw [hA, hD]
          exact_mod_cast poly_part_le C₂ a d hL hX
      _ = (A : ℝ) * ((n : ℝ) + 2) ^ D := by push_cast; ring
      _ ≤ (A : ℝ) * (2 : ℝ) ^ ((D : ℝ) * (64 * E + 256)) := by
          rw [hE]
          exact mul_le_mul_of_nonneg_left (pow_le_rate D n) (Nat.cast_nonneg A)
      _ = (A : ℝ) * ((2 : ℝ) ^ ((D : ℝ) * 256) * (2 : ℝ) ^ ((D : ℝ) * 64 * E)) := by
          rw [← Real.rpow_add two_pos]
          congr 2
          ring
      _ ≤ (A : ℝ) * ((2 : ℝ) ^ ((D : ℝ) * 256) * (2 : ℝ) ^ ((κ : ℝ) * E)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right hDκ hE0))
            (Real.rpow_nonneg zero_le_two _)) (Nat.cast_nonneg A)
      _ = (A : ℝ) * (2 : ℝ) ^ ((D : ℝ) * 256) * (2 : ℝ) ^ ((κ : ℝ) * E) := by ring
  have hb : (((timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1 : ℕ) : ℝ) ≤ K * (2 : ℝ) ^ ((κ : ℝ) * E) := by
    have e1 : (((timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1 : ℕ) : ℝ) = (timeMin3 C₁ m' n' : ℝ) + ((C₂ * L ^ C₂ + X + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    have e2 : K * (2 : ℝ) ^ ((κ : ℝ) * E) = (2 : ℝ) ^ ((C₁ : ℝ) * 32) * (2 : ℝ) ^ ((κ : ℝ) * E) + (A : ℝ) * (2 : ℝ) ^ ((D : ℝ) * 256) * (2 : ℝ) ^ ((κ : ℝ) * E) := by
      rw [hK]
      ring
    rw [e1, e2]
    exact add_le_add hT hQ
  have hc₀' : (q : ℝ) * K ^ q ≤ ((c₀ + κ * q : ℕ) : ℝ) := by
    push_cast
    have : (0 : ℝ) ≤ (κ : ℝ) * q := by positivity
    linarith
  have hpow : ((2 : ℝ) ^ ((κ : ℝ) * E)) ^ q ≤ (2 : ℝ) ^ (((c₀ + κ * q : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ 2 * n * SatK.rN 1 (1 / 2) n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
    refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    have e3 : ((c₀ + κ * q : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ 2 * n * SatK.rN 1 (1 / 2) n = (((c₀ : ℝ) + (κ : ℝ) * q) * 9) * E := by
      rw [hE]
      push_cast
      ring
    rw [e3]
    have h7 : (κ : ℝ) * q ≤ ((c₀ : ℝ) + (κ : ℝ) * q) * 9 := by
      have h8 : (0 : ℝ) ≤ (κ : ℝ) * q := by positivity
      have h9 : (0 : ℝ) ≤ (c₀ : ℝ) := Nat.cast_nonneg c₀
      linarith
    calc (κ : ℝ) * E * q = (κ : ℝ) * q * E := by ring
      _ ≤ ((c₀ : ℝ) + (κ : ℝ) * q) * 9 * E := mul_le_mul_of_nonneg_right h7 hE0
  calc ((q * ((timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1) ^ q : ℕ) : ℝ)
        = (q : ℝ) * (((timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1 : ℕ) : ℝ) ^ q := by push_cast; ring
    _ ≤ (q : ℝ) * (K * (2 : ℝ) ^ ((κ : ℝ) * E)) ^ q := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hb q) (Nat.cast_nonneg q)
    _ = (q : ℝ) * K ^ q * ((2 : ℝ) ^ ((κ : ℝ) * E)) ^ q := by rw [mul_pow]; ring
    _ ≤ ((c₀ + κ * q : ℕ) : ℝ) * (2 : ℝ) ^ (((c₀ + κ * q : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ 2 * n * SatK.rN 1 (1 / 2) n) :=
        mul_le_mul hc₀' hpow (by positivity) (Nat.cast_nonneg _)

end Wrap
