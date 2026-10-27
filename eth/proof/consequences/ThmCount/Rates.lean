/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThmCount.Defs
import Wrap.Arith
import Wrap.ArithRate
import VariableBound.Paper.Arith
import Mathlib.Tactic

/-! # Theorem C from Theorem D(b): the comparison of the rates

No sentence of the paper stands behind this file. Write r(n) = log log(n+4)/√(log(n+4))
(`SatK.rN 1 (1/2) n`), with log = log₂.
* `time_le`: for all constants C, q, a, d there is K such that q·(2^{C·9·(n+4)·r(n)} + a·(n+2)^d + 1)^q
  ≤ 2^{K·R} for every n and every real R ≥ 1 with n·r(n) ≤ 8·R. It uses r(n) ≤ 8 and (n+2)^d ≤
  2^{d·(64·n·r(n) + 256)} from proof/machines/Wrap/ArithRate.lean.
* `rate_le`: for n ≥ 2 and e ≤ 1/4, R = n/(log n)^e is such a number. It uses log y/√y ≤ 8/y^{1/4}
  (`Wrap.Arith.lg_div_sqrt_le`).
* `stRates` (= `ThmCount.StRates`): e = 1/20. `remark_rate`: for n ≥ 4, R = n·(log log n)^{2/3}/(log
  n)^{1/6} is such a number too, because (log log n)^{2/3} ≥ 1. -/

public section

namespace ThmCount

/-- The fourth root, written with two square roots. -/
theorem sqrt_sqrt_eq {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) = x ^ ((1 : ℝ) / 4) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num

/-- log₂ n ≥ 1 for n ≥ 2. -/
theorem one_le_logb {x : ℝ} (hx : 2 ≤ x) : 1 ≤ Real.logb 2 x := by
  have h := Real.logb_le_logb_of_le one_lt_two two_pos hx
  rwa [Real.logb_self_eq_one one_lt_two] at h

/-- For n ≥ 2 and e ≤ 1/4: n·r(n) ≤ 8·n/(log n)^e, and n/(log n)^e ≥ 1. -/
theorem rate_le {n : ℕ} (hn : 2 ≤ n) {e : ℝ} (he : e ≤ 1 / 4) :
    (n : ℝ) * SatK.rN 1 (1 / 2) n ≤ 8 * ((n : ℝ) / Real.logb 2 n ^ e) ∧ 1 ≤ (n : ℝ) / Real.logb 2 n ^ e := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨x, hx⟩ : ∃ x, x = Real.logb 2 (n : ℝ) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = Real.logb 2 ((n : ℝ) + 4) := ⟨_, rfl⟩
  have hx1 : 1 ≤ x := by rw [hx]; exact one_le_logb hn2
  have hxL : x ≤ L := by rw [hx, hL]; exact Real.logb_le_logb_of_le one_lt_two hn0 (by linarith)
  have hxe : 0 < x ^ e := Real.rpow_pos_of_pos (by linarith) e
  have h1 : x ^ e ≤ Real.sqrt (Real.sqrt L) := by
    calc x ^ e ≤ x ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le hx1 he
      _ = Real.sqrt (Real.sqrt x) := (sqrt_sqrt_eq (by linarith)).symm
      _ ≤ Real.sqrt (Real.sqrt L) := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hxL)
  have h2 : SatK.rN 1 (1 / 2) n ≤ 8 / Real.sqrt (Real.sqrt L) := by
    have h := Wrap.Arith.lg_div_sqrt_le (y := L) (by linarith)
    rw [Wrap.Arith.rate_eq]
    rw [hL] at h ⊢
    exact h
  have h3 : 8 / Real.sqrt (Real.sqrt L) ≤ 8 / x ^ e := div_le_div_of_nonneg_left (by norm_num) hxe h1
  rw [← hx]
  constructor
  · calc (n : ℝ) * SatK.rN 1 (1 / 2) n ≤ n * (8 / x ^ e) := mul_le_mul_of_nonneg_left (h2.trans h3) hn0.le
      _ = 8 * ((n : ℝ) / x ^ e) := by ring
  · rw [one_le_div hxe]
    have h4 : Real.logb 2 (n : ℝ) ≤ (n : ℝ) - 1 := VariableBound.Paper.lg_le_sub_one (m := n) (by omega)
    calc x ^ e ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x := Real.rpow_one x
      _ ≤ n := by rw [hx]; linarith

/-- A natural number q is at most 2^q. -/
theorem natCast_le_two_rpow (q : ℕ) : (q : ℝ) ≤ (2 : ℝ) ^ (q : ℝ) := by
  rw [Real.rpow_natCast]
  exact_mod_cast (Nat.lt_two_pow_self (n := q)).le

/-- For all constants C, q, a, d there is K such that, for every n and every real R ≥ 1 with n·r(n)
≤ 8·R: q·(2^{C·9·(n+4)·log log(n+4)/√(log(n+4))} + a·(n+2)^d + 1)^q ≤ 2^{K·R}. -/
theorem time_le (C q a d : ℕ) : ∃ K : ℝ, ∀ (n : ℕ) (R : ℝ), (n : ℝ) * SatK.rN 1 (1 / 2) n ≤ 8 * R → 1 ≤ R →
    (q : ℝ) * ((2 : ℝ) ^ ((C : ℝ) * MainTheoremForms.expN 3 (n + 4)) + (a : ℝ) * ((n : ℝ) + 2) ^ d + 1) ^ q ≤ (2 : ℝ) ^ (K * R) := by
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = (q : ℝ) * (9 * C + 64 * d) := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℝ, c₂ = (q : ℝ) * (288 * C + 256 * d + a + 3) := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; positivity
  refine ⟨8 * c₁ + c₂, fun n R hR h1 => ?_⟩
  obtain ⟨r, hr⟩ : ∃ r, r = SatK.rN 1 (1 / 2) n := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := hr ▸ Wrap.Arith.rate_nonneg n
  have hr8 : r ≤ 8 := hr ▸ Wrap.Arith.rate_le_eight n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hexp : MainTheoremForms.expN 3 (n + 4) = 9 * (((n : ℝ) + 4) * r) := by
    rw [hr, Wrap.Arith.rate_eq]
    unfold MainTheoremForms.expN
    push_cast
    ring
  have p1 := Wrap.Arith.pow_le_rate d n
  rw [← hr] at hR p1
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = (n : ℝ) * r := ⟨_, rfl⟩
  rw [← hρ] at hR p1
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hexp' : MainTheoremForms.expN 3 (n + 4) ≤ 9 * ρ + 288 := by rw [hexp, hρ]; linarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = C * (9 * ρ + 288) + d * (64 * ρ + 256) + a := ⟨_, rfl⟩
  have t1 : (0 : ℝ) ≤ C * (9 * ρ + 288) := by positivity
  have t2 : (0 : ℝ) ≤ d * (64 * ρ + 256) := by positivity
  have hB0 : 0 ≤ B := by rw [hB]; linarith
  obtain ⟨X₁, hX₁⟩ : ∃ X₁ : ℝ, X₁ = (2 : ℝ) ^ ((C : ℝ) * MainTheoremForms.expN 3 (n + 4)) := ⟨_, rfl⟩
  obtain ⟨X₂, hX₂⟩ : ∃ X₂ : ℝ, X₂ = (a : ℝ) * ((n : ℝ) + 2) ^ d := ⟨_, rfl⟩
  rw [← hX₁, ← hX₂]
  have hX₁0 : 0 ≤ X₁ := by rw [hX₁]; positivity
  have hX₂0 : 0 ≤ X₂ := by rw [hX₂]; positivity
  have x1 : X₁ ≤ (2 : ℝ) ^ B := by
    rw [hX₁]
    refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    have := mul_le_mul_of_nonneg_left hexp' hC0
    rw [hB]
    linarith
  have x2 : X₂ ≤ (2 : ℝ) ^ B := by
    rw [hX₂]
    calc (a : ℝ) * ((n : ℝ) + 2) ^ d ≤ (2 : ℝ) ^ (a : ℝ) * (2 : ℝ) ^ ((d : ℝ) * (64 * ρ + 256)) :=
          mul_le_mul (natCast_le_two_rpow a) p1 (by positivity) (by positivity)
      _ = (2 : ℝ) ^ ((a : ℝ) + (d : ℝ) * (64 * ρ + 256)) := (Real.rpow_add two_pos _ _).symm
      _ ≤ (2 : ℝ) ^ B := Real.rpow_le_rpow_of_exponent_le one_le_two (by rw [hB]; linarith)
  have x3 : (1 : ℝ) ≤ (2 : ℝ) ^ B := Real.one_le_rpow one_le_two hB0
  have e4 : (2 : ℝ) ^ (B + 2) = (2 : ℝ) ^ B * 4 := by
    rw [Real.rpow_add two_pos, Real.rpow_two]
    norm_num
  have hsum : X₁ + X₂ + 1 ≤ (2 : ℝ) ^ (B + 2) := by rw [e4]; linarith
  have hpow : (X₁ + X₂ + 1) ^ q ≤ (2 : ℝ) ^ ((B + 2) * q) := by
    rw [Real.rpow_mul_natCast two_pos.le]
    exact pow_le_pow_left₀ (by positivity) hsum q
  calc (q : ℝ) * (X₁ + X₂ + 1) ^ q ≤ (2 : ℝ) ^ (q : ℝ) * (2 : ℝ) ^ ((B + 2) * q) :=
        mul_le_mul (natCast_le_two_rpow q) hpow (by positivity) (by positivity)
    _ = (2 : ℝ) ^ ((q : ℝ) + (B + 2) * q) := (Real.rpow_add two_pos _ _).symm
    _ ≤ (2 : ℝ) ^ ((8 * c₁ + c₂) * R) := by
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        have e : (q : ℝ) + (B + 2) * q = c₁ * ρ + c₂ := by rw [hB, hc₁, hc₂]; ring
        have u1 : c₁ * ρ ≤ c₁ * (8 * R) := mul_le_mul_of_nonneg_left hR hc₁0
        have u2 : c₂ ≤ c₂ * R := le_mul_of_one_le_right hc₂0 h1
        have u3 : (8 * c₁ + c₂) * R = c₁ * (8 * R) + c₂ * R := by ring
        rw [e, u3]
        linarith

/-- The comparison of the rates: for all constants C, q, a, d there is C' such that for every n ≥ 2,
q·(2^{C·9·(n+4)·log log(n+4)/√(log(n+4))} + a·(n+2)^d + 1)^q ≤ 2^{C'·n/(log n)^{1/20}}. This is the
statement `ThmCount.StRates`. -/
theorem stRates : StRates := fun C q a d => by
  obtain ⟨K, hK⟩ := time_le C q a d
  refine ⟨K, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := rate_le hn (e := (1 : ℝ) / 20) (by norm_num)
  exact hK n _ h1 h2

/-- For n ≥ 4, R = n·(log log n)^{2/3}/(log n)^{1/6} has n·r(n) ≤ 8·R and R ≥ 1. -/
theorem remark_rate {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) * SatK.rN 1 (1 / 2) n ≤ 8 * ((n : ℝ) * Real.logb 2 (Real.logb 2 n) ^ ((2 : ℝ) / 3) / Real.logb 2 n ^ ((1 : ℝ) / 6)) ∧
      1 ≤ (n : ℝ) * Real.logb 2 (Real.logb 2 n) ^ ((2 : ℝ) / 3) / Real.logb 2 n ^ ((1 : ℝ) / 6) := by
  obtain ⟨h1, h2⟩ := rate_le (n := n) (by omega) (e := (1 : ℝ) / 6) (by norm_num)
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hx2 : 2 ≤ Real.logb 2 (n : ℝ) := by
    have h := Real.logb_le_logb_of_le one_lt_two (by norm_num : (0 : ℝ) < 4) hn4
    have e : Real.logb 2 (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one one_lt_two]
      norm_num
    rwa [e] at h
  have hy : 1 ≤ Real.logb 2 (Real.logb 2 (n : ℝ)) ^ ((2 : ℝ) / 3) := Real.one_le_rpow (one_le_logb hx2) (by norm_num)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Real.logb 2 (Real.logb 2 (n : ℝ)) ^ ((2 : ℝ) / 3) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = (n : ℝ) / Real.logb 2 n ^ ((1 : ℝ) / 6) := ⟨_, rfl⟩
  rw [← hY] at hy ⊢
  rw [← hR] at h1 h2
  have e : (n : ℝ) * Y / Real.logb 2 n ^ ((1 : ℝ) / 6) = R * Y := by rw [hR]; ring
  rw [e]
  have hRY : R ≤ R * Y := le_mul_of_one_le_right (by linarith) hy
  exact ⟨by linarith, by linarith⟩

end ThmCount
