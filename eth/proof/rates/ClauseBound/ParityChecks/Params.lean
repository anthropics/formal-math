/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.RunDefs
public import ClauseBound.Rec.Few

/-! # Parameters for the run of ClauseBound.ParityChecks.RunDefs that chooses the checks: a variant, not the parameters of Step 2 of Appendix D
These parameters are a variant that the paper does not state; they are not those of Step 2 of
Appendix D: here nb = ⌊n/⌈log₂(2Δ)⌉⌋ need not be a power of two,
r is chosen with (5/8)^r in place of (3/4)^r, and a binomial series is cut off at i₀. The parameters
nb, β₀, r, i₀, β₁, β are computed from n, Δ and m. Two of the conditions of the run hold for all n.
The others hold for n ≥ n₀(c) if Δ ≤ (⌊log₂ n⌋ + 1)^c.
With ℓ = ⌊log₂ n⌋ and t = ⌈log₂(ℓ + 1)⌉, all that is used of the size of n is 84·(c + 1)·t ≤ ℓ,
which holds as soon as ℓ ≥ 2·(84·(c + 1))². Binomial coefficients are bounded by
C(N, j) ≤ (3N/k)^k for j ≤ k ≤ N. The tail of the binomial series is bounded term by term by a
geometric series with ratio 2^{−⌈ℓ/2⌉}. -/

public section

namespace ClauseBound.ParityChecks

open Finset _root_.ParityChecks

/-- ⌈log₂(2Δ)⌉. -/
@[expose] def LD (Δ : ℕ) : ℕ := Nat.clog 2 (2 * Δ)

/-- nb = ⌊n/⌈log₂(2Δ)⌉⌋. -/
@[expose] def nbOf (n Δ : ℕ) : ℕ := n / LD Δ

/-- β₀ = ⌈log₂ C(m, nb + 1)⌉. -/
@[expose] def beta0 (m nb : ℕ) : ℕ := Nat.clog 2 (m.choose (nb + 1))

/-- r = ⌈(59/40)·(n + β₀ + 3)⌉; 59/40 is just above 1/log₂(8/5). -/
@[expose] def rOf (n β₀ : ℕ) : ℕ := (59 * (n + β₀ + 3) + 39) / 40

/-- i₀ = ⌈20n/⌊log₂ n⌋⌉. -/
@[expose] def i0Of (n : ℕ) : ℕ := (20 * n + Nat.log 2 n - 1) / Nat.log 2 n

/-- β₁ = max_{i ≤ i₀} ⌈log₂ C(m, i)⌉. -/
@[expose] def beta1 (m i₀ : ℕ) : ℕ := (range (i₀ + 1)).sup fun i => Nat.clog 2 (m.choose i)

/-- The parameters for n variables, m clauses, and at most Δ occurrences of each variable. -/
@[expose] def parOf (n Δ m : ℕ) : Par where
  m := m
  nb := nbOf n Δ
  r := rOf n (beta0 m (nbOf n Δ))
  i₀ := i0Of n
  β := n + beta0 m (nbOf n Δ) + beta1 m (i0Of n) + 2

/-- (8/5)^59 ≥ 2^40. -/
theorem pow_59 : (2 : ℚ) ^ 40 ≤ (8 / 5) ^ 59 := by norm_num

namespace Params

/-- C(m, nb + 1) ≤ 2^{β₀}. -/
theorem choose_le_beta0 (m nb : ℕ) : m.choose (nb + 1) ≤ 2 ^ beta0 m nb := Nat.le_pow_clog (by norm_num) _

/-- C(m, i) ≤ 2^{β₁} for i ≤ i₀. -/
theorem choose_le_beta1 (m i₀ i : ℕ) (hi : i ≤ i₀) : m.choose i ≤ 2 ^ beta1 m i₀ := by
  refine le_trans (Nat.le_pow_clog (by norm_num) _) (Nat.pow_le_pow_right (by norm_num) ?_)
  exact Finset.le_sup (f := fun i => Nat.clog 2 (m.choose i)) (mem_range.2 (by omega))

/-- 2^X ≤ (8/5)^r if 59·X ≤ 40·r. -/
theorem two_pow_le (X r : ℕ) (h : 59 * X ≤ 40 * r) : (2 : ℚ) ^ X ≤ (8 / 5) ^ r := by
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (show 40 ≠ 0 by norm_num)).1
  calc ((2 : ℚ) ^ X) ^ 40 = (2 ^ 40) ^ X := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ ((8 / 5) ^ 59) ^ X := pow_le_pow_left₀ (by positivity) pow_59 X
    _ = (8 / 5) ^ (59 * X) := by rw [← pow_mul]
    _ ≤ (8 / 5) ^ (40 * r) := pow_le_pow_right₀ (by norm_num) h
    _ = ((8 / 5 : ℚ) ^ r) ^ 40 := by rw [← pow_mul, mul_comm]

end Params

open Params

/-- The conditions that need no largeness of n. -/
theorem start_parOf (n Δ m : ℕ) : (5 / 8 : ℚ) ^ (parOf n Δ m).r * (2 ^ n * m.choose ((parOf n Δ m).nb + 1) : ℕ) ≤ 1 / 8 := by
  show (5 / 8 : ℚ) ^ rOf n (beta0 m (nbOf n Δ)) * (2 ^ n * m.choose (nbOf n Δ + 1) : ℕ) ≤ 1 / 8
  have h1 : ((2 ^ n * m.choose (nbOf n Δ + 1) : ℕ) : ℚ) ≤ 2 ^ (n + beta0 m (nbOf n Δ)) := by
    have : 2 ^ n * m.choose (nbOf n Δ + 1) ≤ 2 ^ (n + beta0 m (nbOf n Δ)) := by
      rw [pow_add]; exact Nat.mul_le_mul_left _ (choose_le_beta0 _ _)
    exact_mod_cast this
  have h2 := two_pow_le (n + beta0 m (nbOf n Δ) + 3) (rOf n (beta0 m (nbOf n Δ))) (by unfold rOf; omega)
  generalize rOf n (beta0 m (nbOf n Δ)) = r at *
  generalize n + beta0 m (nbOf n Δ) = X at *
  have h3 : (5 / 8 : ℚ) ^ r * (8 / 5) ^ r = 1 := by rw [← mul_pow]; norm_num
  have h4 : (0 : ℚ) < (5 / 8) ^ r := by positivity
  rw [pow_add] at h2
  calc (5 / 8 : ℚ) ^ r * ((2 ^ n * m.choose (nbOf n Δ + 1) : ℕ) : ℚ) ≤ (5 / 8) ^ r * 2 ^ X := mul_le_mul_of_nonneg_left h1 h4.le
    _ = 1 / 8 * ((5 / 8) ^ r * (2 ^ X * 2 ^ 3)) := by ring
    _ ≤ 1 / 8 * ((5 / 8) ^ r * (8 / 5) ^ r) := by gcongr
    _ = 1 / 8 := by rw [h3]; ring

theorem small_parOf (n Δ m : ℕ) : ∀ i ≤ (parOf n Δ m).i₀, 2 ^ n * m.choose ((parOf n Δ m).nb + 1) * m.choose i ≤ 2 ^ ((parOf n Δ m).β - 2) := by
  intro i hi
  show 2 ^ n * m.choose (nbOf n Δ + 1) * m.choose i ≤ 2 ^ (n + beta0 m (nbOf n Δ) + beta1 m (i0Of n) + 2 - 2)
  rw [Nat.add_sub_cancel, pow_add, pow_add]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (choose_le_beta0 _ _)) (choose_le_beta1 _ _ _ hi)

namespace Params

/-! ### Tools -/

/-- x·(x + 1) ≤ 2^{x+1}. -/
theorem mul_succ_le_two_pow (x : ℕ) : x * (x + 1) ≤ 2 ^ (x + 1) := by
  induction x with
  | zero => simp
  | succ x ih =>
    have h : x + 1 ≤ 2 ^ x := Nat.lt_two_pow_self
    rw [pow_succ] at ih ⊢
    rw [pow_succ]
    nlinarith

/-- A·⌈log₂(ℓ + 1)⌉ ≤ ℓ for ℓ ≥ 2A². -/
theorem mul_clog_le (A ℓ : ℕ) (hA : 1 ≤ A) (hℓ : 2 * A ^ 2 ≤ ℓ) : A * Nat.clog 2 (ℓ + 1) ≤ ℓ := by
  have h1 : ℓ < A * (ℓ / A + 1) := Nat.lt_mul_div_succ ℓ hA
  have h2 : 2 * A ≤ ℓ / A := by
    rw [Nat.le_div_iff_mul_le hA]
    calc 2 * A * A = 2 * A ^ 2 := by ring
      _ ≤ ℓ := hℓ
  have h3 := mul_succ_le_two_pow (ℓ / A)
  have h4 : ℓ + 1 ≤ 2 ^ (ℓ / A) := by
    generalize ℓ / A = x at *
    have h5 : 2 * A * (x + 1) ≤ x * (x + 1) := Nat.mul_le_mul_right _ h2
    rw [pow_succ] at h3
    nlinarith
  calc A * Nat.clog 2 (ℓ + 1) ≤ A * (ℓ / A) := Nat.mul_le_mul_left _ (Nat.clog_le_of_le_pow h4)
    _ ≤ ℓ := Nat.mul_div_le _ _

/-- 200·ℓ + 300 ≤ 2^ℓ for ℓ ≥ 12. -/
theorem lin_le_two_pow (ℓ : ℕ) (h : 12 ≤ ℓ) : 200 * ℓ + 300 ≤ 2 ^ ℓ := by
  induction ℓ, h using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

/-- C(N, j) ≤ 2^{w·k} for j ≤ k ≤ N, if 3N ≤ k·2^w. -/
theorem choose_le_two_pow {N k j w : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ N) (hj : j ≤ k) (hw : 3 * N ≤ k * 2 ^ w) : N.choose j ≤ 2 ^ (w * k) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast h1
  have h3 := ClauseBound.Rec.sum_choose_le h1 h2
  have h4 : (N.choose j : ℝ) ≤ ∑ ν ∈ range (k + 1), (N.choose ν : ℝ) :=
    single_le_sum (f := fun ν => (N.choose ν : ℝ)) (fun _ _ => by positivity) (mem_range.2 (by omega))
  have h5 : (3 * (N : ℝ) / k) ≤ 2 ^ w := by
    rw [div_le_iff₀ hk]
    have : ((3 * N : ℕ) : ℝ) ≤ ((k * 2 ^ w : ℕ) : ℝ) := by exact_mod_cast hw
    push_cast at this
    linarith
  have h6 : (3 * (N : ℝ) / k) ^ k ≤ (2 ^ w) ^ k := pow_le_pow_left₀ (by positivity) h5 k
  have h7 : (N.choose j : ℝ) ≤ ((2 ^ (w * k) : ℕ) : ℝ) := by
    push_cast
    rw [pow_mul]
    linarith
  exact_mod_cast h7

end Params

namespace Params

/-! ### What is used of the size of n -/

/-- 2Δ ≤ 2^{⌈log₂(2Δ)⌉}. -/
theorem two_Δ_le (Δ : ℕ) : 2 * Δ ≤ 2 ^ LD Δ := Nat.le_pow_clog (by norm_num) _

/-- nb·⌈log₂(2Δ)⌉ ≤ n. -/
theorem nb_mul_le (n Δ : ℕ) : nbOf n Δ * LD Δ ≤ n := Nat.div_mul_le_self _ _

/-- The hypotheses on n, Δ and m, with ℓ = ⌊log₂ n⌋ and t = ⌈log₂(ℓ + 1)⌉. -/
structure Big (c n Δ m ℓ t : ℕ) : Prop where
  hℓ : ℓ = Nat.log 2 n
  ht : t = Nat.clog 2 (ℓ + 1)
  hℓ1 : 1 ≤ ℓ
  hA : 84 * (c + 1) * t ≤ ℓ
  hΔ2 : 2 ≤ Δ
  hΔ : Δ ≤ (ℓ + 1) ^ c
  hnb : nbOf n Δ < m
  hm : m ≤ Δ * n

namespace Big

variable {c n Δ m ℓ t : ℕ} (b : Big c n Δ m ℓ t)
include b

theorem t_pos : 1 ≤ t := by
  rw [b.ht]; exact Nat.clog_pos (by norm_num) (by have := b.hℓ1; omega)

/-- 84·c·t + 84·t ≤ ℓ. -/
theorem hA' : 84 * (c * t) + 84 * t ≤ ℓ := by
  have h := b.hA
  have e : 84 * (c + 1) * t = 84 * (c * t) + 84 * t := by ring
  omega

theorem ℓ_ge : 84 ≤ ℓ := by
  have := b.hA'; have := b.t_pos; omega

theorem n_ne : n ≠ 0 := by
  intro h
  have h1 := b.hℓ
  have h2 := b.hℓ1
  rw [h, Nat.log_zero_right] at h1
  omega

theorem pow_le_n : 2 ^ ℓ ≤ n := by
  rw [b.hℓ]; exact Nat.pow_log_le_self 2 b.n_ne

theorem n_big : 200 * ℓ + 300 ≤ n :=
  le_trans (lin_le_two_pow ℓ (by have := b.ℓ_ge; omega)) b.pow_le_n

theorem succ_le : ℓ + 1 ≤ 2 ^ t := by
  rw [b.ht]; exact Nat.le_pow_clog (by norm_num) _

/-- Δ ≤ 2^{c·t}. -/
theorem Δ_le : Δ ≤ 2 ^ (c * t) := by
  calc Δ ≤ (ℓ + 1) ^ c := b.hΔ
    _ ≤ (2 ^ t) ^ c := Nat.pow_le_pow_left b.succ_le c
    _ = 2 ^ (c * t) := by rw [← pow_mul, mul_comm]

theorem LD_le : LD Δ ≤ 1 + c * t := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add, pow_one]
  exact Nat.mul_le_mul_left _ b.Δ_le

theorem two_le_LD : 2 ≤ LD Δ := by
  have h : 1 < LD Δ := (Nat.lt_clog_iff_pow_lt (by norm_num)).2 (by have := b.hΔ2; omega)
  exact h

/-- 42·(⌈log₂(2Δ)⌉ + t) ≤ ℓ. -/
theorem LDt_le : 42 * (LD Δ + t) ≤ ℓ := by
  have := b.LD_le; have := b.hA'; have := b.t_pos; omega

theorem lt_succ_mul : n < (nbOf n Δ + 1) * LD Δ := by
  have h := Nat.lt_mul_div_succ n (show 0 < LD Δ by have := b.two_le_LD; omega)
  rw [mul_comm] at h
  exact h

theorem two_le_nb : 2 ≤ nbOf n Δ := by
  unfold nbOf
  rw [Nat.le_div_iff_mul_le (by have := b.two_le_LD; omega)]
  have := b.LDt_le; have := b.n_big; omega

theorem lt_two_mul : n < 2 * (nbOf n Δ * LD Δ) := by
  have h1 := b.lt_succ_mul
  have h2 : LD Δ ≤ nbOf n Δ * LD Δ := Nat.le_mul_of_pos_left _ (by have := b.two_le_nb; omega)
  rw [add_mul, one_mul] at h1
  omega

/-- β₀ ≤ 3·⌈log₂(2Δ)⌉·(nb + 1). -/
theorem beta0_le : beta0 m (nbOf n Δ) ≤ 3 * LD Δ * (nbOf n Δ + 1) := by
  apply Nat.clog_le_of_le_pow
  apply choose_le_two_pow (by omega) b.hnb le_rfl
  have h1 := (two_Δ_le Δ)
  have h2 : LD Δ ≤ 2 ^ LD Δ := Nat.lt_two_pow_self.le
  have h3 : 3 ≤ 2 ^ LD Δ := by
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ LD Δ := Nat.pow_le_pow_right (by norm_num) b.two_le_LD
  have h4 : Δ ≤ 2 ^ LD Δ := by omega
  have h5 : 2 ^ (3 * LD Δ) = 2 ^ LD Δ * 2 ^ LD Δ * 2 ^ LD Δ := by
    rw [show 3 * LD Δ = LD Δ + LD Δ + LD Δ by ring, pow_add, pow_add]
  rw [h5]
  calc 3 * m ≤ 3 * (Δ * ((nbOf n Δ + 1) * LD Δ)) :=
        Nat.mul_le_mul_left _ (le_trans b.hm (Nat.mul_le_mul_left _ b.lt_succ_mul.le))
    _ = (nbOf n Δ + 1) * (3 * Δ * LD Δ) := by ring
    _ ≤ (nbOf n Δ + 1) * (2 ^ LD Δ * 2 ^ LD Δ * 2 ^ LD Δ) := by gcongr

/-- β₀ ≤ 3n + 3·⌈log₂(2Δ)⌉. -/
theorem beta0_le' : beta0 m (nbOf n Δ) ≤ 3 * n + 3 * LD Δ := by
  have h1 := b.beta0_le
  have h2 := (nb_mul_le n Δ)
  have e : 3 * LD Δ * (nbOf n Δ + 1) = 3 * (nbOf n Δ * LD Δ) + 3 * LD Δ := by ring
  omega

/-- 20n ≤ ℓ·i₀ ≤ 20n + ℓ − 1. -/
theorem i0_spec : 20 * n ≤ ℓ * i0Of n ∧ ℓ * i0Of n ≤ 20 * n + ℓ - 1 := by
  have hℓ1 := b.hℓ1
  unfold i0Of
  rw [← b.hℓ]
  have h1 := Nat.lt_mul_div_succ (20 * n + ℓ - 1) (show 0 < ℓ by omega)
  have h2 := Nat.mul_div_le (20 * n + ℓ - 1) ℓ
  rw [mul_add, mul_one] at h1
  constructor <;> omega

theorem i0_pos : 1 ≤ i0Of n := by
  have h1 := b.i0_spec.1
  have h2 := b.n_ne
  rcases Nat.eq_zero_or_pos (i0Of n) with h | h
  · rw [h, mul_zero] at h1; omega
  · exact h

/-- β₁ ≤ (⌈log₂(2Δ)⌉ + t)·i₀. -/
theorem beta1_le : beta1 m (i0Of n) ≤ (LD Δ + t) * i0Of n := by
  unfold beta1
  apply Finset.sup_le
  intro i hi
  have hi' : i ≤ i0Of n := Nat.lt_succ_iff.1 (mem_range.1 hi)
  apply Nat.clog_le_of_le_pow
  by_cases h : i0Of n ≤ m
  · apply choose_le_two_pow b.i0_pos h hi'
    rw [pow_add]
    have h1 : 2 * Δ * (ℓ + 1) ≤ 2 ^ LD Δ * 2 ^ t := Nat.mul_le_mul (two_Δ_le Δ) b.succ_le
    calc 3 * m ≤ 3 * (Δ * n) := Nat.mul_le_mul_left _ b.hm
      _ ≤ 2 * Δ * (20 * n) := by nlinarith [Nat.zero_le (Δ * n)]
      _ ≤ 2 * Δ * (ℓ * i0Of n) := Nat.mul_le_mul_left _ b.i0_spec.1
      _ ≤ 2 * Δ * ((ℓ + 1) * i0Of n) := by gcongr; omega
      _ = i0Of n * (2 * Δ * (ℓ + 1)) := by ring
      _ ≤ i0Of n * (2 ^ LD Δ * 2 ^ t) := Nat.mul_le_mul_left _ h1
  · refine le_trans (Nat.choose_le_two_pow m i) (Nat.pow_le_pow_right (by norm_num) ?_)
    have h2 : i0Of n ≤ (LD Δ + t) * i0Of n := Nat.le_mul_of_pos_left _ (by have := b.t_pos; omega)
    omega

/-- 2·(⌈log₂(2Δ)⌉ + t)·i₀ ≤ n. -/
theorem beta1_small : 2 * ((LD Δ + t) * i0Of n) ≤ n := by
  have h1 : 42 * (LD Δ + t) * i0Of n ≤ ℓ * i0Of n := Nat.mul_le_mul_right _ b.LDt_le
  have h2 := b.i0_spec.2
  have h3 := b.n_big
  have e : 42 * (LD Δ + t) * i0Of n = 42 * ((LD Δ + t) * i0Of n) := by ring
  omega

theorem r_le : rOf n (beta0 m (nbOf n Δ)) ≤ 6 * n := by
  have h1 := b.beta0_le'
  have h2 := b.LDt_le
  have h3 := b.n_big
  unfold rOf
  omega

theorem beta_le : n + beta0 m (nbOf n Δ) + beta1 m (i0Of n) + 2 ≤ 5 * n := by
  have h1 := b.beta0_le'
  have h2 := b.LDt_le
  have h3 := b.n_big
  have h4 := b.beta1_le
  have h5 := b.beta1_small
  omega

theorem beta0_le_four : beta0 m (nbOf n Δ) ≤ 4 * n := by
  have h1 := b.beta0_le'
  have h2 := b.LDt_le
  have h3 := b.n_big
  omega

end Big

end Params

namespace Params

/-! ### The tail of the binomial series -/

/-- One term of the series beyond i₀. -/
theorem term_le {u i nb i₀ m h : ℕ} (hu : u ≤ m) (hi : i₀ ≤ i) (hi0 : 1 ≤ i₀) (hnb : 1 ≤ nb) (key : 6 * m * 2 ^ h ≤ nb * i₀) :
    |(-2 * (1 / (nb : ℝ))) ^ i * (u.choose i : ℝ)| ≤ (1 / 2 ^ h) ^ i := by
  by_cases hiu : u < i
  · rw [Nat.choose_eq_zero_of_lt hiu]
    simp only [Nat.cast_zero, mul_zero, abs_zero]
    positivity
  have hi1 : 1 ≤ i := hi0.trans hi
  have hnb' : (0 : ℝ) < nb := by exact_mod_cast hnb
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi1
  have h1 : (u.choose i : ℝ) ≤ (3 * u / i) ^ i :=
    le_trans (single_le_sum (f := fun ν => (u.choose ν : ℝ)) (fun _ _ => by positivity) (mem_range.2 (by omega)))
      (ClauseBound.Rec.sum_choose_le hi1 (by omega))
  have h2 : |(-2 * (1 / (nb : ℝ))) ^ i| = (2 / nb) ^ i := by
    rw [abs_pow]
    congr 1
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (by positivity)]
    ring
  have h3 : 2 / (nb : ℝ) * (3 * u / i) ≤ 1 / 2 ^ h := by
    have h4 : 6 * u * 2 ^ h ≤ nb * i :=
      le_trans (by gcongr) (le_trans key (Nat.mul_le_mul_left _ hi))
    have h5 : (6 : ℝ) * u * 2 ^ h ≤ nb * i := by exact_mod_cast h4
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  rw [abs_mul, h2, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (u.choose i : ℝ))]
  calc (2 / (nb : ℝ)) ^ i * (u.choose i : ℝ) ≤ (2 / nb) ^ i * (3 * u / i) ^ i := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (2 / nb * (3 * u / i)) ^ i := by rw [mul_pow]
    _ ≤ (1 / 2 ^ h) ^ i := pow_le_pow_left₀ (by positivity) h3 i

/-- The binomial series cut off at i₀, over the real numbers. -/
theorem series_real {u nb i₀ m h : ℕ} (hu : u ≤ m) (hi0 : 1 ≤ i₀) (hnb : 1 ≤ nb) (hh : 1 ≤ h) (key : 6 * m * 2 ^ h ≤ nb * i₀) :
    |(1 - 2 * (1 / (nb : ℝ))) ^ u - ∑ i ∈ range (i₀ + 1), (-2 * (1 / (nb : ℝ))) ^ i * (u.choose i : ℝ)| ≤ 2 * (1 / 2 ^ h) ^ i₀ := by
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = -2 * (1 / (nb : ℝ)) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 / 2 ^ h := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq2 : q ≤ 1 / 2 := by
    rw [hq]
    apply one_div_le_one_div_of_le (by norm_num)
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ h := pow_le_pow_right₀ (by norm_num) hh
  have e1 : (1 - 2 * (1 / (nb : ℝ))) ^ u = ∑ i ∈ range (u + 1), y ^ i * (u.choose i : ℝ) := by
    rw [show 1 - 2 * (1 / (nb : ℝ)) = y + 1 by rw [hy]; ring, add_pow]
    refine sum_congr rfl fun i _ => ?_
    rw [one_pow, mul_one]
  have e2 : ∑ i ∈ range (u + 1), y ^ i * (u.choose i : ℝ) = ∑ i ∈ range (i₀ + 1 + u), y ^ i * (u.choose i : ℝ) := by
    refine sum_subset (range_mono (by omega)) fun i _ hi => ?_
    rw [Nat.choose_eq_zero_of_lt (by have := mem_range.not.1 hi; omega)]
    simp
  rw [e1, e2, sum_range_add, ← hy, add_sub_cancel_left, ← hq]
  calc |∑ j ∈ range u, y ^ (i₀ + 1 + j) * (u.choose (i₀ + 1 + j) : ℝ)|
      ≤ ∑ j ∈ range u, |y ^ (i₀ + 1 + j) * (u.choose (i₀ + 1 + j) : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range u, q ^ (i₀ + 1 + j) := by
        refine sum_le_sum fun j _ => ?_
        rw [hy, hq]
        exact term_le hu (by omega) hi0 hnb key
    _ = q ^ (i₀ + 1) * ∑ j ∈ range u, q ^ j := by
        rw [mul_sum]
        exact sum_congr rfl fun j _ => pow_add _ _ _
    _ ≤ q ^ (i₀ + 1) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact le_trans (sum_le_sum fun j _ => pow_le_pow_left₀ hq0 hq2 j) (sum_geometric_two_le u)
    _ ≤ 2 * q ^ i₀ := by
        rw [pow_succ]
        have h1 : 0 ≤ q ^ i₀ := by positivity
        nlinarith

namespace Big

variable {c n Δ m ℓ t : ℕ} (b : Big c n Δ m ℓ t)
include b

/-- 12·Δ·⌈log₂(2Δ)⌉·ℓ ≤ 2^{⌊ℓ/2⌋}. -/
theorem poly_le : 12 * Δ * LD Δ * ℓ ≤ 2 ^ (ℓ / 2) := by
  have h1 := b.Δ_le
  have h2 : LD Δ ≤ 2 ^ (c * t) := le_trans b.LD_le (by rw [add_comm]; exact Nat.lt_two_pow_self)
  have h3 : ℓ ≤ 2 ^ t := by have := b.succ_le; omega
  have h4 : 4 + c * t + c * t + t ≤ ℓ / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have := b.hA'; have := b.t_pos; omega
  calc 12 * Δ * LD Δ * ℓ ≤ 2 ^ 4 * 2 ^ (c * t) * 2 ^ (c * t) * 2 ^ t := by gcongr; norm_num
    _ = 2 ^ (4 + c * t + c * t + t) := by rw [pow_add, pow_add, pow_add]
    _ ≤ 2 ^ (ℓ / 2) := Nat.pow_le_pow_right (by norm_num) h4

/-- 6·m·2^{⌈ℓ/2⌉} ≤ nb·i₀. -/
theorem key : 6 * m * 2 ^ (ℓ - ℓ / 2) ≤ nbOf n Δ * i0Of n := by
  have hLD := b.two_le_LD
  have hℓ1 := b.hℓ1
  have hpos : 0 < 2 * LD Δ * ℓ := by positivity
  apply Nat.le_of_mul_le_mul_right _ hpos
  have h1 : 12 * Δ * LD Δ * ℓ * 2 ^ (ℓ - ℓ / 2) ≤ n := by
    calc 12 * Δ * LD Δ * ℓ * 2 ^ (ℓ - ℓ / 2) ≤ 2 ^ (ℓ / 2) * 2 ^ (ℓ - ℓ / 2) := Nat.mul_le_mul_right _ b.poly_le
      _ = 2 ^ ℓ := by rw [← pow_add]; congr 1; omega
      _ ≤ n := b.pow_le_n
  calc 6 * m * 2 ^ (ℓ - ℓ / 2) * (2 * LD Δ * ℓ) ≤ 6 * (Δ * n) * 2 ^ (ℓ - ℓ / 2) * (2 * LD Δ * ℓ) := by
        have := b.hm; gcongr
    _ = n * (12 * Δ * LD Δ * ℓ * 2 ^ (ℓ - ℓ / 2)) := by ring
    _ ≤ n * n := Nat.mul_le_mul_left _ h1
    _ ≤ (2 * (nbOf n Δ * LD Δ)) * (ℓ * i0Of n) := Nat.mul_le_mul b.lt_two_mul.le (by have := b.i0_spec.1; omega)
    _ = nbOf n Δ * i0Of n * (2 * LD Δ * ℓ) := by ring

/-- 10n ≤ ⌈ℓ/2⌉·i₀. -/
theorem ten_n_le : 10 * n ≤ (ℓ - ℓ / 2) * i0Of n := by
  have h1 := b.i0_spec.1
  have h2 : ℓ * i0Of n ≤ 2 * (ℓ - ℓ / 2) * i0Of n := Nat.mul_le_mul_right _ (by omega)
  have e : 2 * (ℓ - ℓ / 2) * i0Of n = 2 * ((ℓ - ℓ / 2) * i0Of n) := by ring
  omega

/-- The binomial series cut off at i₀. -/
theorem series (u : ℕ) (hu : u ≤ m) :
    |(1 - 2 * pr (nbOf n Δ)) ^ u - ∑ i ∈ range (i0Of n + 1), (-2 * pr (nbOf n Δ)) ^ i * (u.choose i : ℚ)| ≤ 2 / 2 ^ (10 * n) := by
  have h1 := series_real hu b.i0_pos (by have := b.two_le_nb; omega) (by have := b.ℓ_ge; omega : 1 ≤ ℓ - ℓ / 2) b.key
  have h2 : (1 / (2 : ℝ) ^ (ℓ - ℓ / 2)) ^ i0Of n ≤ 1 / 2 ^ (10 * n) := by
    rw [one_div_pow, ← pow_mul]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) b.ten_n_le)
  have h3 : ((|(1 - 2 * pr (nbOf n Δ)) ^ u - ∑ i ∈ range (i0Of n + 1), (-2 * pr (nbOf n Δ)) ^ i * (u.choose i : ℚ)| : ℚ) : ℝ) ≤
      ((2 / 2 ^ (10 * n) : ℚ) : ℝ) := by
    unfold pr
    push_cast
    calc _ ≤ 2 * (1 / (2 : ℝ) ^ (ℓ - ℓ / 2)) ^ i0Of n := h1
      _ ≤ 2 * (1 / 2 ^ (10 * n)) := by linarith
      _ = 2 / 2 ^ (10 * n) := by ring
  exact_mod_cast h3

/-- The bound 2/2^{10n} of `series`, times 2^n·C(m, nb + 1) and times m·r, is below 1/4. -/
theorem drift : (2 / 2 ^ (10 * n) : ℚ) * (2 ^ n * m.choose (nbOf n Δ + 1) : ℕ) * (m * rOf n (beta0 m (nbOf n Δ))) < 1 / 4 := by
  have h1 : m.choose (nbOf n Δ + 1) ≤ 2 ^ (4 * n) :=
    le_trans (choose_le_beta0 _ _) (Nat.pow_le_pow_right (by norm_num) b.beta0_le_four)
  have hn : n < 2 ^ n := Nat.lt_two_pow_self
  have hΔ : Δ ≤ 2 ^ n := by
    have h2 : 2 ^ LD Δ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by have := b.LDt_le; have := b.n_big; omega)
    have := two_Δ_le Δ
    omega
  have h64 : 64 ≤ 2 ^ n := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by have := b.n_big; omega)
  have h3 : 8 * (2 ^ n * m.choose (nbOf n Δ + 1)) * (m * rOf n (beta0 m (nbOf n Δ))) < 2 ^ (10 * n) := by
    calc 8 * (2 ^ n * m.choose (nbOf n Δ + 1)) * (m * rOf n (beta0 m (nbOf n Δ)))
        ≤ 8 * (2 ^ n * 2 ^ (4 * n)) * (2 ^ n * 2 ^ n * (6 * 2 ^ n)) := by
          have := b.r_le
          have hm : m ≤ 2 ^ n * 2 ^ n := le_trans b.hm (Nat.mul_le_mul hΔ hn.le)
          have hr : rOf n (beta0 m (nbOf n Δ)) ≤ 6 * 2 ^ n := by omega
          gcongr
      _ = 48 * 2 ^ (8 * n) := by
          rw [show 8 * n = n + 4 * n + n + n + n by ring, pow_add, pow_add, pow_add, pow_add]; ring
      _ < 64 * 2 ^ (8 * n) := by
          have : 0 < 2 ^ (8 * n) := by positivity
          omega
      _ ≤ 2 ^ n * 2 ^ n * 2 ^ (8 * n) := by
          have : 64 ≤ 2 ^ n * 2 ^ n := le_trans h64 (Nat.le_mul_of_pos_left _ (by positivity))
          gcongr
      _ = 2 ^ (10 * n) := by
          rw [show 10 * n = n + n + 8 * n by ring, pow_add, pow_add]
  have h4 : (8 : ℚ) * ((2 ^ n * m.choose (nbOf n Δ + 1) : ℕ) : ℚ) * ((m : ℚ) * (rOf n (beta0 m (nbOf n Δ)) : ℚ)) < 2 ^ (10 * n) := by
    exact_mod_cast h3
  have hP : (0 : ℚ) < 2 ^ (10 * n) := by positivity
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_iff₀ hP]
  linarith

/-- All that the run needs. -/
theorem hyp : Hyp (parOf n Δ m) (2 ^ n) (2 / 2 ^ (10 * n)) where
  nb_two := b.two_le_nb
  r_pos := by
    show 1 ≤ rOf n (beta0 m (nbOf n Δ))
    unfold rOf; omega
  m_pos := by
    show 1 ≤ m
    have := b.hnb; omega
  β_pos := by
    show 2 ≤ n + beta0 m (nbOf n Δ) + beta1 m (i0Of n) + 2
    omega
  start := start_parOf n Δ m
  series := b.series
  drift := b.drift
  small := small_parOf n Δ m

end Big

end Params

/-- For n large enough in terms of c, if 2 ≤ Δ ≤ (⌊log₂ n⌋ + 1)^c and nb < m ≤ Δ·n, the parameters
satisfy all that the run needs, with ε = 2^{1−10n}, and r ≤ 6n, β ≤ 5n. -/
theorem exists_n0 (c : ℕ) : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ Δ m : ℕ, 2 ≤ Δ → Δ ≤ (Nat.log 2 n + 1) ^ c → nbOf n Δ < m → m ≤ Δ * n →
    Hyp (parOf n Δ m) (2 ^ n) (2 / 2 ^ (10 * n)) ∧ (parOf n Δ m).r ≤ 6 * n ∧ (parOf n Δ m).β ≤ 5 * n ∧
      beta0 m (nbOf n Δ) ≤ 4 * n ∧ nbOf n Δ * LD Δ ≤ n ∧ n < 2 * (nbOf n Δ * LD Δ) := by
  refine ⟨2 ^ (2 * (84 * (c + 1)) ^ 2), fun n hn Δ m hΔ2 hΔ hnb hm => ?_⟩
  have hℓ : 2 * (84 * (c + 1)) ^ 2 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  have b : Big c n Δ m (Nat.log 2 n) (Nat.clog 2 (Nat.log 2 n + 1)) :=
    { hℓ := rfl
      ht := rfl
      hℓ1 := le_trans (Nat.succ_le_of_lt (by positivity)) hℓ
      hA := mul_clog_le (84 * (c + 1)) _ (by omega) hℓ
      hΔ2 := hΔ2
      hΔ := hΔ
      hnb := hnb
      hm := hm }
  exact ⟨b.hyp, b.r_le, b.beta_le, b.beta0_le_four, nb_mul_le n Δ, b.lt_two_mul⟩

end ClauseBound.ParityChecks
