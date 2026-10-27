/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import MainTheoremFormsStatement
import VariableBound.Paper.Arith
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-! # A power of the time of the wrapped machine is below c·2^{δn}

A machine that is put around another one needs q·(t + X + 1)^q steps, where t bounds the steps of
the inner machine, X is the length of the outer input and q is a constant. Here t is
2^{C₁·min{m'/√(lg m'), n'·lg lg n'/√(lg n')}}, rounded down, plus C₂·L^{C₂}, with 4 ≤ n' ≤ n + 4,
and L and X are at most a·(n+2)^d. The main lemma of this file, `Wrap.wrapped_time_le`, says: for
every δ > 0 there is a c
such that the whole expression is at most ⌊c·2^{δn}⌋, for all n, m', n', L, X within these bounds.

The steps, with ε = δ/(q+1):
1. `rate_below`: 2^{B·n·lg lg n/√(lg n)} ≤ c·2^{εn} for n ≥ 4, because lg lg n/√(lg n) tends to 0.
2. `poly_below`: (n+2)^D ≤ c·2^{εn}.
3. `poly_part_le`: C·L^C + X + 1 ≤ (C·a^C + a + 1)·(n+2)^{dC+d}.
4. So t + X + 1 ≤ K·2^{εn} for a constant K, and the q-th power of the right side is at most
   K^q·2^{δn}.

Only the bound in n' of the minimum is used. Only numbers; no machine and no formula occurs in this
file. Throughout, lg is the logarithm to base 2. -/

public section

namespace Wrap

open MainTheoremForms

namespace Arith

/-! ### The rate n·lg lg n/√(lg n) is below ε·n, up to a constant -/

/-- The natural logarithm of 2 is above 1/2. -/
theorem half_lt_log_two : (1 : ℝ) / 2 < Real.log 2 := by
  linarith [Real.log_two_gt_d9]

/-- lg y ≤ 8·y^(1/4) for y > 0; the fourth root is written as a square root of a square root. -/
theorem lg_le_fourth_root {y : ℝ} (hy : 0 < y) : lg y ≤ 8 * Real.sqrt (Real.sqrt y) := by
  have h2 := half_lt_log_two
  have hw : 0 < Real.sqrt (Real.sqrt y) := Real.sqrt_pos.2 (Real.sqrt_pos.2 hy)
  have hy4 : Real.sqrt (Real.sqrt y) ^ 4 = y := by
    calc Real.sqrt (Real.sqrt y) ^ 4 = (Real.sqrt (Real.sqrt y) ^ 2) ^ 2 := by ring
      _ = Real.sqrt y ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg y)]
      _ = y := Real.sq_sqrt hy.le
  have hl : Real.log y ≤ 4 * Real.sqrt (Real.sqrt y) := by
    have h1 := Real.log_le_sub_one_of_pos hw
    have h3 : Real.log (Real.sqrt (Real.sqrt y) ^ 4) = 4 * Real.log (Real.sqrt (Real.sqrt y)) := (Real.log_pow _ 4).trans (by norm_num)
    rw [hy4] at h3
    linarith
  unfold lg Real.logb
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_pos hw (sub_pos.2 h2)]

/-- lg y/√y ≤ 8/y^(1/4) for y > 0. -/
theorem lg_div_sqrt_le {y : ℝ} (hy : 0 < y) : lg y / Real.sqrt y ≤ 8 / Real.sqrt (Real.sqrt y) := by
  have hw : 0 < Real.sqrt (Real.sqrt y) := Real.sqrt_pos.2 (Real.sqrt_pos.2 hy)
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 hy) hw]
  calc lg y * Real.sqrt (Real.sqrt y) ≤ 8 * Real.sqrt (Real.sqrt y) * Real.sqrt (Real.sqrt y) :=
        mul_le_mul_of_nonneg_right (lg_le_fourth_root hy) hw.le
    _ = 8 * Real.sqrt y := by rw [mul_assoc, Real.mul_self_sqrt (Real.sqrt_nonneg y)]

/-- For B ≥ 0, ε > 0 and any natural number n₀ ≥ 2^((8B/ε)^4): B·n·lg lg n/√(lg n) ≤ 8·B·n₀ + ε·n
for all n ≥ 4.
For n ≤ n₀ the first summand is enough, because lg lg n/√(lg n) ≤ 8; for n ≥ n₀ the second is
enough, because then B·lg lg n/√(lg n) ≤ ε. -/
theorem rate_le_const_add {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) {n₀ : ℕ} (hn₀ : (2 : ℝ) ^ ((8 * B / ε) ^ 4) ≤ n₀) {n : ℕ} (hn : 4 ≤ n) :
    B * ((n : ℝ) * lg (lg n) / Real.sqrt (lg n)) ≤ 8 * B * n₀ + ε * n := by
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  obtain ⟨hy, -, hyy, -, -⟩ := VariableBound.Paper.lg_add_four hn
  have hy0 : 0 < lg n := by linarith
  have hw1 : 1 ≤ Real.sqrt (Real.sqrt (lg n)) := Real.one_le_sqrt.2 (Real.one_le_sqrt.2 (by linarith))
  have hw0 : 0 < Real.sqrt (Real.sqrt (lg n)) := by linarith
  have hg := lg_div_sqrt_le hy0
  have hg0 : 0 ≤ lg (lg n) / Real.sqrt (lg n) := div_nonneg (by linarith) (Real.sqrt_nonneg _)
  rw [mul_div_assoc]
  rcases le_total n n₀ with hle | hle
  · have hle' : (n : ℝ) ≤ n₀ := by exact_mod_cast hle
    have hg8 : lg (lg n) / Real.sqrt (lg n) ≤ 8 := hg.trans (div_le_self (by norm_num) hw1)
    have h1 : (n : ℝ) * (lg (lg n) / Real.sqrt (lg n)) ≤ n₀ * 8 := mul_le_mul hle' hg8 hg0 (Nat.cast_nonneg n₀)
    have h2 := mul_le_mul_of_nonneg_left h1 hB
    have h3 : 0 ≤ ε * n := mul_nonneg hε.le hn0
    linarith
  · have hle' : (n₀ : ℝ) ≤ n := by exact_mod_cast hle
    have ha : (8 * B / ε) ^ 4 ≤ lg n := by
      unfold lg
      rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith)]
      exact hn₀.trans hle'
    have haw : 8 * B / ε ≤ Real.sqrt (Real.sqrt (lg n)) := by
      apply Real.le_sqrt_of_sq_le
      apply Real.le_sqrt_of_sq_le
      calc ((8 * B / ε) ^ 2) ^ 2 = (8 * B / ε) ^ 4 := by ring
        _ ≤ lg n := ha
    have h1 : B * (lg (lg n) / Real.sqrt (lg n)) ≤ ε := by
      calc B * (lg (lg n) / Real.sqrt (lg n)) ≤ B * (8 / Real.sqrt (Real.sqrt (lg n))) := mul_le_mul_of_nonneg_left hg hB
        _ = 8 * B / Real.sqrt (Real.sqrt (lg n)) := by ring
        _ ≤ ε := by
          rw [div_le_iff₀ hw0]
          rw [div_le_iff₀ hε] at haw
          linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hn0
    have h3 : 0 ≤ 8 * B * n₀ := mul_nonneg (mul_nonneg (by norm_num) hB) (Nat.cast_nonneg n₀)
    calc B * ((n : ℝ) * (lg (lg n) / Real.sqrt (lg n))) = n * (B * (lg (lg n) / Real.sqrt (lg n))) := by ring
      _ ≤ n * ε := h2
      _ ≤ 8 * B * n₀ + ε * n := by linarith

/-- For every B ≥ 0 and ε > 0 there is a c with 2^{B·n·lg lg n/√(lg n)} ≤ c·2^{εn} for all n ≥ 4:
take a natural number n₀ ≥ 2^((8B/ε)^4) and then c ≥ 2^(8·B·n₀). -/
theorem rate_below {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ c : ℕ, ∀ n : ℕ, 4 ≤ n → (2 : ℝ) ^ (B * ((n : ℝ) * lg (lg n) / Real.sqrt (lg n))) ≤ (c : ℝ) * (2 : ℝ) ^ (ε * n) := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge ((2 : ℝ) ^ ((8 * B / ε) ^ 4))
  obtain ⟨c, hc⟩ := exists_nat_ge ((2 : ℝ) ^ (8 * B * n₀))
  refine ⟨c, fun n hn => ?_⟩
  calc (2 : ℝ) ^ (B * ((n : ℝ) * lg (lg n) / Real.sqrt (lg n))) ≤ (2 : ℝ) ^ (8 * B * n₀ + ε * n) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two (rate_le_const_add hB hε hn₀ hn)
    _ = (2 : ℝ) ^ (8 * B * n₀) * (2 : ℝ) ^ (ε * n) := Real.rpow_add two_pos _ _
    _ ≤ (c : ℝ) * (2 : ℝ) ^ (ε * n) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg zero_le_two _)

/-- The time with the minimum of the two exponents is at most the power of 2 with the exponent in n
alone: ⌊2^{C·min{m/√(lg m), n·lg lg n/√(lg n)}}⌋ ≤ 2^{C·n·lg lg n/√(lg n)}. No hypothesis on C, m,
n. -/
theorem timeMin3_le (C m n : ℕ) : (timeMin3 C m n : ℝ) ≤ (2 : ℝ) ^ ((C : ℝ) * ((n : ℝ) * lg (lg n) / Real.sqrt (lg n))) := by
  unfold timeMin3
  refine (Nat.floor_le (by positivity)).trans ?_
  exact Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg C))

/-! ### A polynomial is below c·2^{εn} -/

/-- s ≤ 2·2^s for every real s ≥ 0. -/
theorem le_two_mul_two_rpow {s : ℝ} (hs : 0 ≤ s) : s ≤ 2 * (2 : ℝ) ^ s := by
  have h2 := half_lt_log_two
  have h1 : s * Real.log 2 + 1 ≤ Real.exp (s * Real.log 2) := Real.add_one_le_exp _
  have e : (2 : ℝ) ^ s = Real.exp (s * Real.log 2) := by
    rw [Real.rpow_def_of_pos two_pos, mul_comm]
  rw [e]
  nlinarith

/-- For every D and ε > 0 there is a c with (n+2)^D ≤ c·2^{εn} for all n. With K = D + 1: n + 2 ≤
(2K/ε + 2)·2^{εn/K}, and the K-th power of the right side is (2K/ε + 2)^K·2^{εn}. -/
theorem poly_below (D : ℕ) {ε : ℝ} (hε : 0 < ε) : ∃ c : ℕ, ∀ n : ℕ, ((n : ℝ) + 2) ^ D ≤ (c : ℝ) * (2 : ℝ) ^ (ε * n) := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (D : ℝ) + 1 := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  obtain ⟨c, hc⟩ := exists_nat_ge ((2 * K / ε + 2) ^ (D + 1))
  refine ⟨c, fun n => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs : 0 ≤ ε * n / K := by positivity
  have h1 := le_two_mul_two_rpow hs
  have hp1 : 1 ≤ (2 : ℝ) ^ (ε * n / K) := Real.one_le_rpow one_le_two hs
  have h2 : (n : ℝ) + 2 ≤ (2 * K / ε + 2) * (2 : ℝ) ^ (ε * n / K) := by
    have e1 : (n : ℝ) = (K / ε) * (ε * n / K) := by field_simp
    have h3 : (K / ε) * (ε * n / K) ≤ (K / ε) * (2 * (2 : ℝ) ^ (ε * n / K)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    have e2 : (2 * K / ε + 2) * (2 : ℝ) ^ (ε * n / K) = (K / ε) * (2 * (2 : ℝ) ^ (ε * n / K)) + 2 * (2 : ℝ) ^ (ε * n / K) := by ring
    rw [e2]
    linarith
  calc ((n : ℝ) + 2) ^ D ≤ ((n : ℝ) + 2) ^ (D + 1) := pow_le_pow_right₀ (by linarith) (Nat.le_succ D)
    _ ≤ ((2 * K / ε + 2) * (2 : ℝ) ^ (ε * n / K)) ^ (D + 1) := pow_le_pow_left₀ (by positivity) h2 _
    _ = (2 * K / ε + 2) ^ (D + 1) * (2 : ℝ) ^ (ε * n) := by
        rw [mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ (ε * n / K)), ← Real.rpow_mul zero_le_two]
        congr 2
        push_cast
        rw [← hK]
        field_simp
    _ ≤ (c : ℝ) * (2 : ℝ) ^ (ε * n) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg zero_le_two _)

/-- If L and X are at most a·(n+2)^d, then C·L^C + X + 1 ≤ (C·a^C + a + 1)·(n+2)^{dC+d}. -/
theorem poly_part_le (C a d : ℕ) {n L X : ℕ} (hL : L ≤ a * (n + 2) ^ d) (hX : X ≤ a * (n + 2) ^ d) :
    C * L ^ C + X + 1 ≤ (C * a ^ C + a + 1) * (n + 2) ^ (d * C + d) := by
  have hb : 1 ≤ n + 2 := by omega
  have h1 : L ^ C ≤ a ^ C * (n + 2) ^ (d * C + d) := by
    calc L ^ C ≤ (a * (n + 2) ^ d) ^ C := Nat.pow_le_pow_left hL C
      _ = a ^ C * (n + 2) ^ (d * C) := by rw [mul_pow, ← pow_mul]
      _ ≤ a ^ C * (n + 2) ^ (d * C + d) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb (Nat.le_add_right _ _))
  have h2 : X ≤ a * (n + 2) ^ (d * C + d) := hX.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb (Nat.le_add_left _ _)))
  have h3 : 1 ≤ (n + 2) ^ (d * C + d) := Nat.one_le_pow _ _ (by omega)
  calc C * L ^ C + X + 1 ≤ C * (a ^ C * (n + 2) ^ (d * C + d)) + a * (n + 2) ^ (d * C + d) + (n + 2) ^ (d * C + d) :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ h1) h2) h3
    _ = (C * a ^ C + a + 1) * (n + 2) ^ (d * C + d) := by ring

end Arith

/-! ### The main lemma -/

open Arith

/-- For all q, C₁, C₂, a, d and every δ > 0 there is a c such that q·(⌊2^{C₁·min{m'/√(lg m'), n'·lg
lg n'/√(lg n')}}⌋ + C₂·L^{C₂} + X + 1)^q ≤ ⌊c·2^{δn}⌋ whenever m' ≥ 2, 4 ≤ n' ≤ n + 4 and L, X ≤
a·(n+2)^d.
The constant C₁ in the exponent and the constant C₂ in the polynomial need not be equal. The proof
does not use m' ≥ 2. -/
theorem wrapped_time_le (q C₁ C₂ a d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℕ, ∀ (n m' n' L X : ℕ), 2 ≤ m' → 4 ≤ n' → n' ≤ n + 4 → L ≤ a * (n + 2) ^ d → X ≤ a * (n + 2) ^ d →
      q * ((MainTheoremForms.timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1) ^ q ≤ ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = δ / ((q : ℝ) + 1) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; exact div_pos hδ hq1
  have hεq : ε * q ≤ δ := by
    rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ hq1]
    nlinarith
  obtain ⟨c₁, hc₁⟩ := rate_below (Nat.cast_nonneg C₁) hε
  obtain ⟨c₂, hc₂⟩ := poly_below (d * C₂ + d) hε
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = C₂ * a ^ C₂ + a + 1 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (c₁ : ℝ) * (2 : ℝ) ^ (ε * 4) + (A : ℝ) * c₂ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨c, hc⟩ := exists_nat_ge ((q : ℝ) * K ^ q)
  refine ⟨c, fun n m' n' L X _ hn' hnn hL hX => Nat.le_floor ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hT : (timeMin3 C₁ m' n' : ℝ) ≤ (c₁ : ℝ) * (2 : ℝ) ^ (ε * 4) * (2 : ℝ) ^ (ε * n) := by
    have hnn' : (n' : ℝ) ≤ (n : ℝ) + 4 := by exact_mod_cast hnn
    calc (timeMin3 C₁ m' n' : ℝ) ≤ (2 : ℝ) ^ ((C₁ : ℝ) * ((n' : ℝ) * lg (lg n') / Real.sqrt (lg n'))) := timeMin3_le C₁ m' n'
      _ ≤ (c₁ : ℝ) * (2 : ℝ) ^ (ε * n') := hc₁ n' hn'
      _ ≤ (c₁ : ℝ) * (2 : ℝ) ^ (ε * ((n : ℝ) + 4)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left hnn' hε.le)) (Nat.cast_nonneg c₁)
      _ = (c₁ : ℝ) * (2 : ℝ) ^ (ε * 4) * (2 : ℝ) ^ (ε * n) := by
          rw [mul_add, Real.rpow_add two_pos]
          ring
  have hQ : ((C₂ * L ^ C₂ + X + 1 : ℕ) : ℝ) ≤ (A : ℝ) * c₂ * (2 : ℝ) ^ (ε * n) := by
    calc ((C₂ * L ^ C₂ + X + 1 : ℕ) : ℝ) ≤ ((A * (n + 2) ^ (d * C₂ + d) : ℕ) : ℝ) := by
          rw [hA]
          exact_mod_cast poly_part_le C₂ a d hL hX
      _ = (A : ℝ) * ((n : ℝ) + 2) ^ (d * C₂ + d) := by push_cast; ring
      _ ≤ (A : ℝ) * ((c₂ : ℝ) * (2 : ℝ) ^ (ε * n)) := mul_le_mul_of_nonneg_left (hc₂ n) (Nat.cast_nonneg A)
      _ = (A : ℝ) * c₂ * (2 : ℝ) ^ (ε * n) := by ring
  have hb : (((timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1 : ℕ) : ℝ) ≤ K * (2 : ℝ) ^ (ε * n) := by
    have e1 : (((timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1 : ℕ) : ℝ) = (timeMin3 C₁ m' n' : ℝ) + ((C₂ * L ^ C₂ + X + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    have e2 : K * (2 : ℝ) ^ (ε * n) = (c₁ : ℝ) * (2 : ℝ) ^ (ε * 4) * (2 : ℝ) ^ (ε * n) + (A : ℝ) * c₂ * (2 : ℝ) ^ (ε * n) := by
      rw [hK]
      ring
    rw [e1, e2]
    exact add_le_add hT hQ
  have hpow : ((2 : ℝ) ^ (ε * n)) ^ q ≤ (2 : ℝ) ^ (δ * n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
    refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    calc ε * n * q = ε * q * n := by ring
      _ ≤ δ * n := mul_le_mul_of_nonneg_right hεq hn0
  calc ((q * ((timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1) ^ q : ℕ) : ℝ)
        = (q : ℝ) * (((timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1 : ℕ) : ℝ) ^ q := by push_cast; ring
    _ ≤ (q : ℝ) * (K * (2 : ℝ) ^ (ε * n)) ^ q := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hb q) (Nat.cast_nonneg q)
    _ = (q : ℝ) * K ^ q * ((2 : ℝ) ^ (ε * n)) ^ q := by rw [mul_pow]; ring
    _ ≤ (q : ℝ) * K ^ q * (2 : ℝ) ^ (δ * n) := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ (c : ℝ) * (2 : ℝ) ^ (δ * n) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg zero_le_two _)

end Wrap
