/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements
public import ThreeSumApsp.Util.Asymptotics.Logarithms
public import ThreeSumApsp.Util.Ceil

/-!
# The arithmetic of t = ⌊n^τ⌋

The hinted problems of Section 5.4 have matrices with t = ⌊n^τ⌋ rows or columns (hintSize τ n).  The
running times of the programs are expressions in n and t; the statements want powers of n.  This
file has the inequalities between the two, as inequalities between real numbers with explicit
constants.  No programs here.
-/

public section

namespace ThreeSumApsp

open ThreeSumApsp.WordRam

variable {n : ℕ} {τ τ₁ τ₂ : ℝ}

/-! ## The number t -/

/-- 1 ≤ t. -/
theorem one_le_hintSize (hn : 1 ≤ n) (hτ : 0 ≤ τ) : 1 ≤ hintSize τ n :=
  Nat.le_floor (by simpa using Real.one_le_rpow (Nat.one_le_cast.2 hn) hτ)

/-- t ≤ n^τ. -/
theorem hintSize_le_rpow (n : ℕ) (τ : ℝ) : (hintSize τ n : ℝ) ≤ (n : ℝ) ^ τ :=
  Nat.floor_le (by positivity)

/-- n^τ ≤ 2 t: rounding down loses at most a factor 2. -/
theorem rpow_le_two_mul_hintSize (hn : 1 ≤ n) (hτ : 0 ≤ τ) :
    (n : ℝ) ^ τ ≤ 2 * (hintSize τ n : ℝ) := by
  have h1 : (n : ℝ) ^ τ < (hintSize τ n : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2 : (1 : ℝ) ≤ (hintSize τ n : ℝ) := by exact_mod_cast one_le_hintSize hn hτ
  linarith

/-- A power of n with a smaller exponent is smaller. -/
theorem natCast_rpow_le_rpow (hn : 1 ≤ n) {a b : ℝ} (h : a ≤ b) : (n : ℝ) ^ a ≤ (n : ℝ) ^ b :=
  Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hn) h

/-- t ≤ n for τ ≤ 1. -/
theorem hintSize_le (hn : 1 ≤ n) (hτ : τ ≤ 1) : hintSize τ n ≤ n := by
  have h := (hintSize_le_rpow n τ).trans (natCast_rpow_le_rpow hn hτ)
  rw [Real.rpow_one] at h
  exact_mod_cast h

/-- t^k ≤ ⌊n^σ⌋ if kτ ≤ σ. -/
theorem hintSize_pow_le_hintSize (hn : 1 ≤ n) (k : ℕ) {σ : ℝ} (h : k * τ ≤ σ) :
    hintSize τ n ^ k ≤ hintSize σ n := by
  refine Nat.le_floor ?_
  push_cast
  calc (hintSize τ n : ℝ) ^ k ≤ ((n : ℝ) ^ τ) ^ k :=
        pow_le_pow_left₀ (by positivity) (hintSize_le_rpow n τ) k
    _ = (n : ℝ) ^ (τ * k) := by rw [Real.rpow_mul_natCast (by positivity)]
    _ ≤ (n : ℝ) ^ σ := natCast_rpow_le_rpow hn (by linarith)

/-- t^18 ≤ n for τ ≤ 1/18: the condition N ≥ D^18 of Corollary 26. -/
theorem hintSize_pow_eighteen_le (hn : 1 ≤ n) (hτ : τ ≤ 1 / 18) : hintSize τ n ^ 18 ≤ n := by
  have h := hintSize_pow_le_hintSize (τ := τ) hn 18 (σ := 1) (by push_cast; linarith)
  exact h.trans (hintSize_le hn le_rfl)

/-- t₁^18 ≤ t₂ for τ₁ ≤ τ₂/18. -/
theorem hintSize_pow_eighteen_le_hintSize (hn : 1 ≤ n) (h : τ₁ ≤ τ₂ / 18) :
    hintSize τ₁ n ^ 18 ≤ hintSize τ₂ n :=
  hintSize_pow_le_hintSize hn 18 (by push_cast; linarith)

/-! ## Powers of t -/

/-- t^q ≤ n^{qτ}. -/
theorem hintSize_rpow_le (n : ℕ) (τ : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    (hintSize τ n : ℝ) ^ q ≤ (n : ℝ) ^ (q * τ) := by
  calc (hintSize τ n : ℝ) ^ q ≤ ((n : ℝ) ^ τ) ^ q :=
        Real.rpow_le_rpow (by positivity) (hintSize_le_rpow n τ) hq
    _ = (n : ℝ) ^ (q * τ) := by rw [← Real.rpow_mul (by positivity), mul_comm]

/-- n^{γτ} ≤ 2^γ t^γ. -/
theorem rpow_le_two_rpow_mul (hn : 1 ≤ n) (hτ : 0 ≤ τ) {γ : ℝ} (hγ : 0 ≤ γ) :
    (n : ℝ) ^ (γ * τ) ≤ (2 : ℝ) ^ γ * (hintSize τ n : ℝ) ^ γ := by
  calc (n : ℝ) ^ (γ * τ) = ((n : ℝ) ^ τ) ^ γ := by rw [← Real.rpow_mul (by positivity), mul_comm]
    _ ≤ (2 * (hintSize τ n : ℝ)) ^ γ :=
        Real.rpow_le_rpow (by positivity) (rpow_le_two_mul_hintSize hn hτ) hγ
    _ = (2 : ℝ) ^ γ * (hintSize τ n : ℝ) ^ γ := Real.mul_rpow (by norm_num) (by positivity)

/-- 1/t^γ ≤ 2^γ/n^{γτ}, in the form A/t^γ ≤ 2^γ A n^{-γτ}. -/
theorem div_hintSize_rpow_le (hn : 1 ≤ n) (hτ : 0 ≤ τ) {γ A : ℝ} (hγ : 0 ≤ γ) (hA : 0 ≤ A) :
    A / (hintSize τ n : ℝ) ^ γ ≤ (2 : ℝ) ^ γ * (A * (n : ℝ) ^ (-(γ * τ))) := by
  have ht : (0 : ℝ) < (hintSize τ n : ℝ) := by exact_mod_cast one_le_hintSize hn hτ
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hp : (0 : ℝ) < (hintSize τ n : ℝ) ^ γ := Real.rpow_pos_of_pos ht _
  have hq : (0 : ℝ) < (n : ℝ) ^ (γ * τ) := Real.rpow_pos_of_pos hn0 _
  rw [div_le_iff₀ hp, Real.rpow_neg hn0.le]
  have key := rpow_le_two_rpow_mul hn hτ hγ
  have : A = A * ((n : ℝ) ^ (γ * τ))⁻¹ * (n : ℝ) ^ (γ * τ) := by field_simp
  calc A = A * ((n : ℝ) ^ (γ * τ))⁻¹ * (n : ℝ) ^ (γ * τ) := this
    _ ≤ A * ((n : ℝ) ^ (γ * τ))⁻¹ * ((2 : ℝ) ^ γ * (hintSize τ n : ℝ) ^ γ) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = (2 : ℝ) ^ γ * (A * ((n : ℝ) ^ (γ * τ))⁻¹) * (hintSize τ n : ℝ) ^ γ := by ring

/-- 2^γ ≤ 2 for γ ≤ 1. -/
theorem two_rpow_le_two {γ : ℝ} (h1 : γ ≤ 1) : (2 : ℝ) ^ γ ≤ 2 := by
  calc (2 : ℝ) ^ γ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    _ = 2 := Real.rpow_one 2

/-- n^a / t^γ ≤ 2^γ n^{a - γτ}. -/
theorem rpow_div_hintSize_rpow_le (hn : 1 ≤ n) (hτ : 0 ≤ τ) {γ : ℝ} (hγ : 0 ≤ γ) (a : ℝ) :
    (n : ℝ) ^ a / (hintSize τ n : ℝ) ^ γ ≤ (2 : ℝ) ^ γ * (n : ℝ) ^ (a - γ * τ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h := div_hintSize_rpow_le hn hτ hγ (A := (n : ℝ) ^ a) (by positivity)
  rwa [← Real.rpow_add hn0, ← sub_eq_add_neg] at h

/-- n^a t^q ≤ n^{a + qτ}. -/
theorem rpow_mul_hintSize_rpow_le (hn : 1 ≤ n) (τ : ℝ) {q : ℝ} (hq : 0 ≤ q) (a : ℝ) :
    (n : ℝ) ^ a * (hintSize τ n : ℝ) ^ q ≤ (n : ℝ) ^ (a + q * τ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Real.rpow_add hn0]
  exact mul_le_mul_of_nonneg_left (hintSize_rpow_le n τ hq) (by positivity)

/-- n^a t ≤ n^{a + τ}. -/
theorem rpow_mul_hintSize_le (hn : 1 ≤ n) (τ a : ℝ) :
    (n : ℝ) ^ a * (hintSize τ n : ℝ) ≤ (n : ℝ) ^ (a + τ) := by
  have h := rpow_mul_hintSize_rpow_le hn τ (q := 1) (by norm_num) a
  rwa [Real.rpow_one, one_mul] at h

/-! ## Corollary 40 with the data structure of Corollary 26: the exponents 0.063 and 0.437 -/

/-- The preprocessing: n²/t^{0.063} ≤ 2 n^{2 - 0.063τ}. -/
theorem sq_div_hintSize_le (hn : 1 ≤ n) (hτ : 0 ≤ τ) :
    (n : ℝ) ^ 2 / (hintSize τ n : ℝ) ^ (0.063 : ℝ) ≤ 2 * (n : ℝ) ^ (2 - 0.063 * τ) := by
  have h := rpow_div_hintSize_rpow_le hn hτ (γ := 0.063) (by norm_num) 2
  rw [show (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ 2 by exact_mod_cast Real.rpow_natCast (n : ℝ) 2] at h
  exact h.trans (mul_le_mul_of_nonneg_right (two_rpow_le_two (by norm_num)) (by positivity))

/-- n queries: n t^{0.437} ≤ n^{1 + 0.437τ}. -/
theorem mul_hintSize_rpow_le (hn : 1 ≤ n) (τ : ℝ) :
    (n : ℝ) * (hintSize τ n : ℝ) ^ (0.437 : ℝ) ≤ (n : ℝ) ^ (1 + 0.437 * τ) := by
  have h := rpow_mul_hintSize_rpow_le hn τ (q := 0.437) (by norm_num) 1
  rwa [Real.rpow_one] at h

/-- Reading or writing an n × t matrix: n t ≤ n^{2 - 0.063τ} for τ ≤ 1/18. -/
theorem mul_hintSize_le (hn : 1 ≤ n) (hτ : τ ≤ 1 / 18) :
    (n : ℝ) * (hintSize τ n : ℝ) ≤ (n : ℝ) ^ (2 - 0.063 * τ) := by
  have h := rpow_mul_hintSize_le hn τ 1
  rw [Real.rpow_one] at h
  exact h.trans (natCast_rpow_le_rpow hn (by linarith))

/-! ## The number of blocks -/

/-- A number c of blocks of b rows with c b < a + b, as ⌈a/b⌉ has, is at most 2a/b if b ≤ a. -/
theorem blocks_mul_le {a b c : ℕ} (hab : b ≤ a) (hc : c * b < a + b) : (c : ℝ) * b ≤ 2 * a := by
  have : c * b ≤ 2 * a := by omega
  exact_mod_cast this

/-- c ≤ ⌈n/t₂⌉ blocks of t₂ rows and t₂ columns have c t₂² ≤ 2 n t₂ ≤ 2 n^{1 + τ₂} entries. -/
theorem blocks_mul_sq_le (hn : 1 ≤ n) (h2 : τ₂ ≤ 1) {c : ℕ}
    (hc : c * hintSize τ₂ n < n + hintSize τ₂ n) :
    (c : ℝ) * (hintSize τ₂ n : ℝ) ^ 2 ≤ 2 * (n : ℝ) ^ (1 + τ₂) :=
  calc (c : ℝ) * (hintSize τ₂ n : ℝ) ^ 2
      = (c : ℝ) * (hintSize τ₂ n : ℝ) * (hintSize τ₂ n : ℝ) := by ring
    _ ≤ 2 * (n : ℝ) * (hintSize τ₂ n : ℝ) :=
        mul_le_mul_of_nonneg_right (blocks_mul_le (hintSize_le hn h2) hc) (Nat.cast_nonneg _)
    _ = 2 * ((n : ℝ) ^ (1 : ℝ) * (hintSize τ₂ n : ℝ)) := by rw [Real.rpow_one, mul_assoc]
    _ ≤ 2 * (n : ℝ) ^ (1 + τ₂) := by
        gcongr
        exact rpow_mul_hintSize_le hn τ₂ 1

/-! ## The uMv problem with the data structure of Corollary 26 -/

/-- The preprocessing of c ≤ ⌈n/t₂⌉ blocks: c t₂²/t₁^{0.063} ≤ 4 n^{1 + τ₂ - 0.063τ₁}. -/
theorem blocks_sq_div_le (hn : 1 ≤ n) (h1 : 0 ≤ τ₁) (h2 : τ₂ ≤ 1) {c : ℕ}
    (hc : c * hintSize τ₂ n < n + hintSize τ₂ n) :
    (c : ℝ) * (hintSize τ₂ n : ℝ) ^ 2 / (hintSize τ₁ n : ℝ) ^ (0.063 : ℝ)
      ≤ 4 * (n : ℝ) ^ (1 + τ₂ - 0.063 * τ₁) := by
  have ht1 : (0 : ℝ) < (hintSize τ₁ n : ℝ) ^ (0.063 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast one_le_hintSize hn h1) _
  have hnum := blocks_mul_sq_le hn h2 hc
  have h4 := rpow_div_hintSize_rpow_le hn h1 (γ := 0.063) (by norm_num) (1 + τ₂)
  have h5 : (2 : ℝ) ^ (0.063 : ℝ) * (n : ℝ) ^ (1 + τ₂ - 0.063 * τ₁)
      ≤ 2 * (n : ℝ) ^ (1 + τ₂ - 0.063 * τ₁) :=
    mul_le_mul_of_nonneg_right (two_rpow_le_two (by norm_num)) (by positivity)
  calc (c : ℝ) * (hintSize τ₂ n : ℝ) ^ 2 / (hintSize τ₁ n : ℝ) ^ (0.063 : ℝ)
      ≤ 2 * (n : ℝ) ^ (1 + τ₂) / (hintSize τ₁ n : ℝ) ^ (0.063 : ℝ) :=
        div_le_div_of_nonneg_right hnum ht1.le
    _ = 2 * ((n : ℝ) ^ (1 + τ₂) / (hintSize τ₁ n : ℝ) ^ (0.063 : ℝ)) := by ring
    _ ≤ 4 * (n : ℝ) ^ (1 + τ₂ - 0.063 * τ₁) := by linarith

/-- t₁ t₂ ≤ n^{τ₁ + τ₂}. -/
theorem hintSize_mul_hintSize_le (hn : 1 ≤ n) (τ₁ τ₂ : ℝ) :
    (hintSize τ₁ n : ℝ) * (hintSize τ₂ n : ℝ) ≤ (n : ℝ) ^ (τ₁ + τ₂) :=
  calc (hintSize τ₁ n : ℝ) * (hintSize τ₂ n : ℝ) ≤ (n : ℝ) ^ τ₁ * (n : ℝ) ^ τ₂ :=
        mul_le_mul (hintSize_le_rpow n τ₁) (hintSize_le_rpow n τ₂) (by positivity) (by positivity)
    _ = (n : ℝ) ^ (τ₁ + τ₂) := (Real.rpow_add (by exact_mod_cast hn) _ _).symm

/-- t₂ queries: t₂ t₁^{0.437} ≤ n^{τ₂ + 0.437τ₁}. -/
theorem hintSize_mul_hintSize_rpow_le (hn : 1 ≤ n) (τ₁ τ₂ : ℝ) :
    (hintSize τ₂ n : ℝ) * (hintSize τ₁ n : ℝ) ^ (0.437 : ℝ) ≤ (n : ℝ) ^ (τ₂ + 0.437 * τ₁) :=
  (mul_le_mul_of_nonneg_right (hintSize_le_rpow n τ₂) (by positivity)).trans
    (rpow_mul_hintSize_rpow_le hn τ₁ (by norm_num) τ₂)

/-! ## The general form, with logarithmic factors -/

/-- For 0 ≤ γ < γ': n^a (log t + 1)²/t^{γ'} = O(n^{a - γτ}), with one constant for all n, τ, a. -/
theorem rpow_mul_log_sq_div_le {γ γ' : ℝ} (hγ : 0 ≤ γ) (hγ' : γ < γ') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (τ a : ℝ), 1 ≤ n → 0 ≤ τ →
      (n : ℝ) ^ a * (Real.log (hintSize τ n : ℝ) + 1) ^ 2 / (hintSize τ n : ℝ) ^ γ'
        ≤ C * (n : ℝ) ^ (a - γ * τ) := by
  obtain ⟨C, hC, hlog⟩ := dominated_log_add_one_pow_rpow (sub_pos.2 hγ') 2
  refine ⟨C * (2 : ℝ) ^ γ, by positivity, fun n τ a hn hτ => ?_⟩
  have ht1 : (1 : ℝ) ≤ hintSize τ n := Nat.one_le_cast.2 (one_le_hintSize hn hτ)
  have ht0 : (0 : ℝ) < hintSize τ n := zero_lt_one.trans_le ht1
  calc (n : ℝ) ^ a * (Real.log (hintSize τ n : ℝ) + 1) ^ 2 / (hintSize τ n : ℝ) ^ γ'
      ≤ (n : ℝ) ^ a * (C * (hintSize τ n : ℝ) ^ (γ' - γ)) / (hintSize τ n : ℝ) ^ γ' := by
        gcongr
        exact hlog _ ht1
    _ = C * ((n : ℝ) ^ a / (hintSize τ n : ℝ) ^ γ) := by
        rw [Real.rpow_sub ht0]
        field_simp
    _ ≤ C * ((2 : ℝ) ^ γ * (n : ℝ) ^ (a - γ * τ)) := by
        gcongr
        exact rpow_div_hintSize_rpow_le hn hτ hγ a
    _ = C * (2 : ℝ) ^ γ * (n : ℝ) ^ (a - γ * τ) := by ring

/-- For 0 ≤ q < r: n^a t^q (log t + 1) = O(n^{a + rτ}), with one constant for all n, τ, a. -/
theorem rpow_mul_rpow_mul_log_le {q r : ℝ} (hq : 0 ≤ q) (hr : q < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (τ a : ℝ), 1 ≤ n → 0 ≤ τ →
      (n : ℝ) ^ a * (hintSize τ n : ℝ) ^ q * (Real.log (hintSize τ n : ℝ) + 1)
        ≤ C * (n : ℝ) ^ (a + r * τ) := by
  obtain ⟨C, hC, hlog⟩ := dominated_log_add_one_rpow (sub_pos.2 hr)
  refine ⟨C, hC, fun n τ a hn hτ => ?_⟩
  have ht1 : (1 : ℝ) ≤ hintSize τ n := Nat.one_le_cast.2 (one_le_hintSize hn hτ)
  have ht0 : (0 : ℝ) < hintSize τ n := zero_lt_one.trans_le ht1
  calc (n : ℝ) ^ a * (hintSize τ n : ℝ) ^ q * (Real.log (hintSize τ n : ℝ) + 1)
      ≤ (n : ℝ) ^ a * (hintSize τ n : ℝ) ^ q * (C * (hintSize τ n : ℝ) ^ (r - q)) := by
        gcongr
        exact hlog _ ht1
    _ = C * ((n : ℝ) ^ a * (hintSize τ n : ℝ) ^ r) := by
        rw [Real.rpow_sub ht0]
        field_simp
    _ ≤ C * (n : ℝ) ^ (a + r * τ) := by
        gcongr
        exact rpow_mul_hintSize_rpow_le hn τ (hq.trans hr.le) a

/-! ## The four general bounds of Corollary 40 -/

/-- The preprocessing, general form: n² (log t + 1)²/t^{γ'} ≤ C n^{2 - γτ}. -/
theorem general_pre_le {γ γ' : ℝ} (hγ : 0 ≤ γ) (hγ' : γ < γ') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (τ : ℝ), 1 ≤ n → 0 ≤ τ →
      (n : ℝ) ^ 2 * (Real.log (hintSize τ n : ℝ) + 1) ^ 2 / (hintSize τ n : ℝ) ^ γ'
        ≤ C * (n : ℝ) ^ (2 - γ * τ) := by
  obtain ⟨C, hC, h⟩ := rpow_mul_log_sq_div_le hγ hγ'
  refine ⟨C, hC, fun n τ hn hτ => ?_⟩
  simpa only [Real.rpow_ofNat] using h n τ 2 hn hτ

/-- n queries, general form: n t^q (log t + 1) ≤ C n^{1 + τ/2} for q < 1/2. -/
theorem general_query_le {q : ℝ} (hq : 0 ≤ q) (hq' : q < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (τ : ℝ), 1 ≤ n → 0 ≤ τ →
      (n : ℝ) * (hintSize τ n : ℝ) ^ q * (Real.log (hintSize τ n : ℝ) + 1)
        ≤ C * (n : ℝ) ^ (1 + τ / 2) := by
  obtain ⟨C, hC, h⟩ := rpow_mul_rpow_mul_log_le hq hq'
  refine ⟨C, hC, fun n τ hn hτ => ?_⟩
  simpa only [Real.rpow_one, one_div_mul_eq_div] using h n τ 1 hn hτ

/-- The preprocessing of the blocks of the uMv problem, general form: c t₂² (log t₁ + 1)²/t₁^{γ'} ≤
C n^{1 + τ₂ - γτ₁}. -/
theorem general_umv_pre_le {γ γ' : ℝ} (hγ : 0 ≤ γ) (hγ' : γ < γ') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n c : ℕ) (τ₁ τ₂ : ℝ), 1 ≤ n → 0 ≤ τ₁ → τ₂ ≤ 1 →
      c * hintSize τ₂ n < n + hintSize τ₂ n →
      (c : ℝ) * (hintSize τ₂ n : ℝ) ^ 2 * (Real.log (hintSize τ₁ n : ℝ) + 1) ^ 2 /
        (hintSize τ₁ n : ℝ) ^ γ'
        ≤ C * (n : ℝ) ^ (1 + τ₂ - γ * τ₁) := by
  obtain ⟨C, hC, h⟩ := rpow_mul_log_sq_div_le hγ hγ'
  refine ⟨2 * C, by positivity, fun n c τ₁ τ₂ hn h1 h2 hc => ?_⟩
  have hnum := blocks_mul_sq_le hn h2 hc
  calc (c : ℝ) * (hintSize τ₂ n : ℝ) ^ 2 * (Real.log (hintSize τ₁ n : ℝ) + 1) ^ 2 /
        (hintSize τ₁ n : ℝ) ^ γ'
      ≤ 2 * (n : ℝ) ^ (1 + τ₂) * (Real.log (hintSize τ₁ n : ℝ) + 1) ^ 2 /
        (hintSize τ₁ n : ℝ) ^ γ' := by gcongr
    _ = 2 * ((n : ℝ) ^ (1 + τ₂) * (Real.log (hintSize τ₁ n : ℝ) + 1) ^ 2 /
        (hintSize τ₁ n : ℝ) ^ γ') := by ring
    _ ≤ 2 * (C * (n : ℝ) ^ (1 + τ₂ - γ * τ₁)) := by
        gcongr
        exact h n τ₁ (1 + τ₂) hn h1
    _ = 2 * C * (n : ℝ) ^ (1 + τ₂ - γ * τ₁) := by ring

/-- t₂ queries of the uMv problem, general form: t₂ t₁^q (log t₁ + 1) ≤ C n^{τ₂ + τ₁/2} for q < 1/2.
-/
theorem general_umv_query_le {q : ℝ} (hq : 0 ≤ q) (hq' : q < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (τ₁ τ₂ : ℝ), 1 ≤ n → 0 ≤ τ₁ →
      (hintSize τ₂ n : ℝ) * (hintSize τ₁ n : ℝ) ^ q * (Real.log (hintSize τ₁ n : ℝ) + 1)
        ≤ C * (n : ℝ) ^ (τ₂ + τ₁ / 2) := by
  obtain ⟨C, hC, h⟩ := rpow_mul_rpow_mul_log_le hq hq'
  refine ⟨C, hC, fun n τ₁ τ₂ hn h1 => ?_⟩
  have hlog : 0 ≤ Real.log (hintSize τ₁ n : ℝ) :=
    Real.log_nonneg (Nat.one_le_cast.2 (one_le_hintSize hn h1))
  calc (hintSize τ₂ n : ℝ) * (hintSize τ₁ n : ℝ) ^ q * (Real.log (hintSize τ₁ n : ℝ) + 1)
      ≤ (n : ℝ) ^ τ₂ * (hintSize τ₁ n : ℝ) ^ q * (Real.log (hintSize τ₁ n : ℝ) + 1) := by
        gcongr
        exact hintSize_le_rpow n τ₂
    _ ≤ C * (n : ℝ) ^ (τ₂ + τ₁ / 2) := by
        simpa only [one_div_mul_eq_div] using h n τ₁ τ₂ hn h1

end ThreeSumApsp
