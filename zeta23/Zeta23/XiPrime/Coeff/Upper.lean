/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Coeff/Upper.lean — the uniform upper bound for the ξ′ diagonal sum and (H1), (H2).

[XF′ Lemma 7.1 (iii)] in the crude form the prime side consumes ([XF′ Remark 7.2]):
  S(u) := Σ_{N ≤ e^u} ‖C(N;Λ⋆)‖²/N ≤ C·(1+u)²      for 0 ≤ u with ‖Λ⋆‖⁻¹·u ≤ 4 and ‖Λ⋆‖ ≥ 32eK   (K = log 4 + 4),
whence for a T-indexed parameter Λ⋆(T) with ‖Λ⋆(T)‖ ≥ l(T)/2:
  (H2) Σ_{N≤x} ‖C(N;Λ⋆(T))‖² ≤ C·x·l(T)²,   (H1) Σ_{N≤x} ‖C(N;Λ⋆(T))‖/√N ≤ C·√x·l(T)     (2 ≤ x ≤ e^{l(T)}, T ≥ T₀).
Route (no asymptotics): ‖C‖² ≤ 2Λ² + 2log²N·F²  (Basic), F(N)² ≤ Σ_m 2^m x^{2m} Λ^{∗m}(N)² (dyadic Cauchy–Schwarz),
Λ^{∗m}(N)² ≤ u^m Λ^{∗m}(N) (Basic.lamPow_le_log_pow), Σ_{N≤e^u} Λ^{∗m}(N)/N ≤ (u+mK)^m/m! (PowerSums), and
Σ_m [(4x²u²)^m/m! + (4eK·x²u)^m] ≤ e^{64} + 2.
-/
import Zeta23.XiPrime.Coeff.PowerSums
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Chebyshev

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Omega
open Finset Real

noncomputable section

namespace Zeta23
namespace XiPrime

/-! ### small combinatorial facts -/

lemma two_pow_length_le_prod : ∀ (L : List ℕ), (∀ p ∈ L, 2 ≤ p) → 2 ^ L.length ≤ L.prod
  | [], _ => by simp
  | a :: L, h => by
      have ha : 2 ≤ a := h a (by simp)
      have ih := two_pow_length_le_prod L fun p hp => h p (by simp [hp])
      simp only [List.length_cons, List.prod_cons, pow_succ]
      calc 2 ^ L.length * 2 ≤ L.prod * a := Nat.mul_le_mul ih ha
        _ = a * L.prod := mul_comm _ _

/-- Ω n ≤ n. -/
lemma cardFactors_le_self (n : ℕ) : Ω n ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [ArithmeticFunction.cardFactors_apply]
  have h2 : ∀ p ∈ n.primeFactorsList, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le
  calc n.primeFactorsList.length ≤ 2 ^ n.primeFactorsList.length := (Nat.lt_two_pow_self).le
    _ ≤ n.primeFactorsList.prod := two_pow_length_le_prod _ h2
    _ = n := Nat.prod_primeFactorsList hn.ne'

/-- dyadic Cauchy–Schwarz: (Σ_{i<n} a_i)² ≤ Σ_{i<n} 2^{i+1} a_i². -/
lemma sq_sum_range_le_sum_two_pow_mul_sq : ∀ (n : ℕ) (a : ℕ → ℝ),
    (∑ i ∈ range n, a i) ^ 2 ≤ ∑ i ∈ range n, 2 ^ (i + 1) * a i ^ 2
  | 0, a => by simp
  | n + 1, a => by
      rw [sum_range_succ' a, sum_range_succ' (fun i => (2:ℝ) ^ (i + 1) * a i ^ 2)]
      have ih := sq_sum_range_le_sum_two_pow_mul_sq n (fun i => a (i + 1))
      have h2 : (∑ i ∈ range n, a (i + 1) + a 0) ^ 2 ≤ 2 * (∑ i ∈ range n, a (i + 1)) ^ 2 + 2 * a 0 ^ 2 := by
        nlinarith [sq_nonneg (∑ i ∈ range n, a (i + 1) - a 0)]
      calc (∑ i ∈ range n, a (i + 1) + a 0) ^ 2
          ≤ 2 * (∑ i ∈ range n, 2 ^ (i + 1) * a (i + 1) ^ 2) + 2 * a 0 ^ 2 := by nlinarith [ih]
        _ = ∑ i ∈ range n, 2 ^ (i + 1 + 1) * a (i + 1) ^ 2 + 2 ^ (0 + 1) * a 0 ^ 2 := by
            rw [mul_sum]; congr 1
            · exact sum_congr rfl fun i _ => by ring
            · ring

/-! ### the F-majorant: Σ_{N≤e^u} F_x(N)²/N is bounded -/

/-- the absolute constant bounding Σ F²/N. -/
def CF : ℝ := Real.exp 64 + 2

lemma CF_pos : 0 < CF := by unfold CF; positivity

/-- per-m bound:  2^m x^{2m} u^m (u+mK)^m/m! ≤ (4x²u²)^m/m! + (4eK x²u)^m. -/
lemma term_bound {x u : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u) (m : ℕ) :
    2 ^ m * x ^ (2 * m) * u ^ m * ((u + m * KM) ^ m / m.factorial)
      ≤ (4 * x ^ 2 * u ^ 2) ^ m / m.factorial + (4 * Real.exp 1 * KM * x ^ 2 * u) ^ m := by
  have hK := KM_nonneg
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hmf : (0:ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  -- (u + mK)^m ≤ (2 max)^m ≤ 2^m (u^m + (mK)^m)
  have hsplit : (u + m * KM) ^ m ≤ 2 ^ m * (u ^ m + (m * KM) ^ m) := by
    have hle : u + m * KM ≤ 2 * max u (m * KM) := by
      rcases le_total u (m * KM) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    calc (u + m * KM) ^ m ≤ (2 * max u (m * KM)) ^ m :=
          pow_le_pow_left₀ (by positivity) hle m
      _ = 2 ^ m * (max u (m * KM)) ^ m := by rw [mul_pow]
      _ ≤ 2 ^ m * (u ^ m + (m * KM) ^ m) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rcases le_total u (m * KM) with h | h
          · rw [max_eq_right h]; linarith [pow_nonneg hu m]
          · rw [max_eq_left h]; linarith [pow_nonneg (by positivity : (0:ℝ) ≤ m * KM) m]
  -- m^m / m! ≤ e^m
  have hStirling : (m : ℝ) ^ m / m.factorial ≤ Real.exp 1 ^ m := by
    rw [Real.exp_one_pow]
    exact Real.pow_div_factorial_le_exp (x := (m : ℝ)) hm0 m
  have hA0 : 0 ≤ 2 ^ m * x ^ (2 * m) * u ^ m := by positivity
  have hB0 : 0 ≤ (4 * KM * x ^ 2 * u) ^ m :=
    pow_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK) (sq_nonneg x)) hu) m
  calc 2 ^ m * x ^ (2 * m) * u ^ m * ((u + m * KM) ^ m / m.factorial)
      ≤ 2 ^ m * x ^ (2 * m) * u ^ m * (2 ^ m * (u ^ m + (m * KM) ^ m) / m.factorial) := by
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsplit hmf.le) hA0
    _ = (4 * x ^ 2 * u ^ 2) ^ m / m.factorial
        + (4 * KM * x ^ 2 * u) ^ m * ((m : ℝ) ^ m / m.factorial) := by
        have h4 : (4:ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
        simp only [div_eq_mul_inv, mul_pow, h4]
        ring
    _ ≤ (4 * x ^ 2 * u ^ 2) ^ m / m.factorial + (4 * KM * x ^ 2 * u) ^ m * Real.exp 1 ^ m :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hStirling hB0)
    _ = (4 * x ^ 2 * u ^ 2) ^ m / m.factorial + (4 * Real.exp 1 * KM * x ^ 2 * u) ^ m := by
        rw [← mul_pow]; ring

/-- the m-th dyadic term is summable-small:  2^m x^{2m} u^m Σ_{N≤e^u}Λ^{∗m}(N)/N ≤ 64^m/m! + 2^{-m}
(m = i+1), provided x·u ≤ 4 and 32eK·x ≤ 1. -/
lemma Fmaj_term_le {x u : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u) (hxu : x * u ≤ 4)
    (hxK : 32 * Real.exp 1 * KM * x ≤ 1) (i : ℕ) :
    2 ^ (i + 1) * x ^ (2 * (i + 1)) * u ^ (i + 1) * Sdiv (Λ ^ (i + 1)) u
      ≤ (64:ℝ) ^ (i + 1) / (i + 1).factorial + (1 / 2 : ℝ) ^ (i + 1) := by
  have h1 : 2 ^ (i + 1) * x ^ (2 * (i + 1)) * u ^ (i + 1) * Sdiv (Λ ^ (i + 1)) u
      ≤ 2 ^ (i + 1) * x ^ (2 * (i + 1)) * u ^ (i + 1) * ((u + ↑(i + 1) * KM) ^ (i + 1) / (i + 1).factorial) :=
    mul_le_mul_of_nonneg_left (Sdiv_lamPow_le (i + 1) hu) (by positivity)
  refine h1.trans ((term_bound hx hu (i + 1)).trans ?_)
  have h0 : 0 ≤ 4 * Real.exp 1 * KM * x ^ 2 * u :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) KM_nonneg) (sq_nonneg x)) hu
  have hhalf : 4 * Real.exp 1 * KM * x ^ 2 * u ≤ 1 / 2 := by
    have hprod : (32 * Real.exp 1 * KM * x) * (x * u) ≤ 1 * 4 :=
      mul_le_mul hxK hxu (mul_nonneg hx hu) zero_le_one
    calc 4 * Real.exp 1 * KM * x ^ 2 * u = (32 * Real.exp 1 * KM * x) * (x * u) / 8 := by ring
      _ ≤ 1 * 4 / 8 := div_le_div_of_nonneg_right hprod (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  have h64 : 4 * x ^ 2 * u ^ 2 ≤ 64 := by nlinarith [sq_nonneg (x * u), mul_nonneg hx hu]
  have h640 : 0 ≤ 4 * x ^ 2 * u ^ 2 := by positivity
  exact add_le_add (div_le_div_of_nonneg_right (pow_le_pow_left₀ h640 h64 _) (Nat.cast_nonneg _))
    (pow_le_pow_left₀ h0 hhalf _)

/-- **Σ_{N ≤ e^u} F_x(N)²/N ≤ CF**, provided x·u ≤ 4 and 32eK·x ≤ 1 (x ≥ 0, u ≥ 0). -/
theorem sum_Fmaj_sq_div_le {x u : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u) (hxu : x * u ≤ 4)
    (hxK : 32 * Real.exp 1 * KM * x ≤ 1) :
    ∑ N ∈ Ioc 0 ⌊Real.exp u⌋₊, Fmaj x N ^ 2 / N ≤ CF := by
  set X : ℕ := ⌊Real.exp u⌋₊ with hX
  -- (1) pointwise: F(N)² ≤ Σ_{i<X} 2^{i+1} (x^{i+1} Λ^{i+1} N)², and (Λ^{i+1}N)² ≤ u^{i+1} Λ^{i+1} N
  have hpt : ∀ N ∈ Ioc 0 X, Fmaj x N ^ 2 / N
      ≤ ∑ i ∈ range X, 2 ^ (i + 1) * x ^ (2 * (i + 1)) * u ^ (i + 1) * ((Λ ^ (i + 1)) N / N) := by
    intro N hN
    have hN0 : 0 < N := (mem_Ioc.mp hN).1
    have hNX : N ≤ X := (mem_Ioc.mp hN).2
    have hΩ : Ω N ≤ X := (cardFactors_le_self N).trans hNX
    have hlogN : Real.log N ≤ u := log_le_of_mem_Ioc_floor_exp hN
    have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    rw [Fmaj_eq_sum_range_of_le x hΩ, div_eq_mul_inv, ]
    calc (∑ i ∈ range X, x ^ (i + 1) * (Λ ^ (i + 1)) N) ^ 2 * (N:ℝ)⁻¹
        ≤ (∑ i ∈ range X, 2 ^ (i + 1) * (x ^ (i + 1) * (Λ ^ (i + 1)) N) ^ 2) * (N:ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right (sq_sum_range_le_sum_two_pow_mul_sq X _) (by positivity)
      _ = ∑ i ∈ range X, 2 ^ (i + 1) * x ^ (2 * (i + 1)) * ((Λ ^ (i + 1)) N * (Λ ^ (i + 1)) N) * (N:ℝ)⁻¹ := by
          rw [sum_mul]; refine sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i ∈ range X, 2 ^ (i + 1) * x ^ (2 * (i + 1)) * (u ^ (i + 1) * (Λ ^ (i + 1)) N) * (N:ℝ)⁻¹ := by
          refine sum_le_sum fun i _ => ?_
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine mul_le_mul_of_nonneg_right ?_ (lamPow_nonneg _ _)
          exact (lamPow_le_log_pow _ _).trans (pow_le_pow_left₀ hlog0 hlogN _)
      _ = _ := sum_congr rfl fun i _ => by ring
  -- (2) sum over N, swap, use the PowerSums bound
  have hswap : ∑ N ∈ Ioc 0 X, ∑ i ∈ range X, 2 ^ (i + 1) * x ^ (2 * (i + 1)) * u ^ (i + 1) * ((Λ ^ (i + 1)) N / N)
      = ∑ i ∈ range X, 2 ^ (i + 1) * x ^ (2 * (i + 1)) * u ^ (i + 1) * Sdiv (Λ ^ (i + 1)) u := by
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [← mul_sum]; rfl
  have hterm : ∀ i ∈ range X, 2 ^ (i + 1) * x ^ (2 * (i + 1)) * u ^ (i + 1) * Sdiv (Λ ^ (i + 1)) u
      ≤ (4 * x ^ 2 * u ^ 2) ^ (i + 1) / (i + 1).factorial + (1 / 2 : ℝ) ^ (i + 1) := by
    intro i _
    have h1 : 2 ^ (i + 1) * x ^ (2 * (i + 1)) * u ^ (i + 1) * Sdiv (Λ ^ (i + 1)) u
        ≤ 2 ^ (i + 1) * x ^ (2 * (i + 1)) * u ^ (i + 1) * ((u + ↑(i + 1) * KM) ^ (i + 1) / (i + 1).factorial) :=
      mul_le_mul_of_nonneg_left (Sdiv_lamPow_le (i + 1) hu) (by positivity)
    refine h1.trans ((term_bound hx hu (i + 1)).trans ?_)
    have h0 : 0 ≤ 4 * Real.exp 1 * KM * x ^ 2 * u :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) KM_nonneg) (sq_nonneg x)) hu
    have hhalf : 4 * Real.exp 1 * KM * x ^ 2 * u ≤ 1 / 2 := by
      have hprod : (32 * Real.exp 1 * KM * x) * (x * u) ≤ 1 * 4 :=
        mul_le_mul hxK hxu (mul_nonneg hx hu) zero_le_one
      calc 4 * Real.exp 1 * KM * x ^ 2 * u = (32 * Real.exp 1 * KM * x) * (x * u) / 8 := by ring
        _ ≤ 1 * 4 / 8 := div_le_div_of_nonneg_right hprod (by norm_num)
        _ ≤ 1 / 2 := by norm_num
    exact add_le_add le_rfl (pow_le_pow_left₀ h0 hhalf _)
  calc ∑ N ∈ Ioc 0 X, Fmaj x N ^ 2 / N
      ≤ ∑ N ∈ Ioc 0 X, ∑ i ∈ range X, 2 ^ (i + 1) * x ^ (2 * (i + 1)) * u ^ (i + 1) * ((Λ ^ (i + 1)) N / N) :=
        sum_le_sum hpt
    _ = ∑ i ∈ range X, 2 ^ (i + 1) * x ^ (2 * (i + 1)) * u ^ (i + 1) * Sdiv (Λ ^ (i + 1)) u := hswap
    _ ≤ ∑ i ∈ range X, ((4 * x ^ 2 * u ^ 2) ^ (i + 1) / (i + 1).factorial + (1 / 2 : ℝ) ^ (i + 1)) := sum_le_sum hterm
    _ = (∑ i ∈ range X, (4 * x ^ 2 * u ^ 2) ^ (i + 1) / (i + 1).factorial) + ∑ i ∈ range X, (1 / 2 : ℝ) ^ (i + 1) :=
        sum_add_distrib
    _ ≤ Real.exp 64 + 2 := by
        gcongr
        · -- shift index and compare with the exponential series of 4x²u² ≤ 16 ≤ 32
          have h8 : 4 * x ^ 2 * u ^ 2 ≤ 64 := by nlinarith [sq_nonneg (x * u), mul_nonneg hx hu]
          have h80 : 0 ≤ 4 * x ^ 2 * u ^ 2 := by positivity
          calc ∑ i ∈ range X, (4 * x ^ 2 * u ^ 2) ^ (i + 1) / (i + 1).factorial
              ≤ ∑ i ∈ range (X + 1), (4 * x ^ 2 * u ^ 2) ^ i / i.factorial := by
                rw [sum_range_succ']
                simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
                linarith
            _ ≤ Real.exp (4 * x ^ 2 * u ^ 2) := Real.sum_le_exp_of_nonneg h80 _
            _ ≤ Real.exp 64 := Real.exp_le_exp.mpr h8
        · calc ∑ i ∈ range X, (1 / 2 : ℝ) ^ (i + 1) ≤ ∑ i ∈ range (X + 1), (1 / 2 : ℝ) ^ i := by
                rw [sum_range_succ']; simp only [pow_zero]; linarith
            _ ≤ 2 := sum_geometric_two_le _
    _ = CF := rfl

/-! ### the diagonal sum: S(u) ≤ C(1+u)² -/

/-- Σ_{N ≤ e^u} Λ(N)²/N ≤ u(u + K). -/
lemma sum_vonMangoldt_sq_div_le {u : ℝ} (hu : 0 ≤ u) :
    ∑ N ∈ Ioc 0 ⌊Real.exp u⌋₊, Λ N ^ 2 / N ≤ u * (u + KM) := by
  calc ∑ N ∈ Ioc 0 ⌊Real.exp u⌋₊, Λ N ^ 2 / N ≤ ∑ N ∈ Ioc 0 ⌊Real.exp u⌋₊, u * (Λ N / N) := by
        refine sum_le_sum fun N hN => ?_
        have hlog : Λ N ≤ u := ArithmeticFunction.vonMangoldt_le_log.trans (log_le_of_mem_Ioc_floor_exp hN)
        rw [sq, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right hlog (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg N))
    _ = u * Sdiv Λ u := by rw [← mul_sum]; rfl
    _ ≤ u * (u + KM) := mul_le_mul_of_nonneg_left (Sdiv_lam_le hu) hu

/-- the absolute constant in S(u) ≤ CS·(1+u)². -/
def CS : ℝ := 2 * (1 + KM) + 2 * CF

lemma CS_pos : 0 < CS := by unfold CS; nlinarith [KM_pos, CF_pos]

/-- **uniform upper bound for the diagonal sum.**  For ‖Λ⋆‖ ≥ 32eK and u·‖Λ⋆‖⁻¹ ≤ 4 (u ≥ 0):
  Σ_{N ≤ e^u} ‖C(N;Λ⋆)‖²/N ≤ CS·(1+u)². -/
theorem diagSum_le {Λs : ℂ} {u : ℝ} (hu : 0 ≤ u) (hxu : ‖Λs‖⁻¹ * u ≤ 4)
    (hbig : 32 * Real.exp 1 * KM ≤ ‖Λs‖) :
    ∑ N ∈ Ioc 0 ⌊Real.exp u⌋₊, ‖xiCoeff Λs N‖ ^ 2 / N ≤ CS * (1 + u) ^ 2 := by
  have hΛpos : 0 < ‖Λs‖ := lt_of_lt_of_le (mul_pos (by positivity) KM_pos) hbig
  have hx : 0 ≤ ‖Λs‖⁻¹ := by positivity
  have hxK : 32 * Real.exp 1 * KM * ‖Λs‖⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hΛpos]; exact hbig
  have hF := sum_Fmaj_sq_div_le hx hu hxu hxK
  have hΛ2 := sum_vonMangoldt_sq_div_le hu
  calc ∑ N ∈ Ioc 0 ⌊Real.exp u⌋₊, ‖xiCoeff Λs N‖ ^ 2 / N
      ≤ ∑ N ∈ Ioc 0 ⌊Real.exp u⌋₊, (2 * (Λ N ^ 2 / N) + 2 * u ^ 2 * (Fmaj ‖Λs‖⁻¹ N ^ 2 / N)) := by
        refine sum_le_sum fun N hN => ?_
        have hlogN : Real.log N ≤ u := log_le_of_mem_Ioc_floor_exp hN
        have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
        have hN0 : (0:ℝ) ≤ (N:ℝ)⁻¹ := by positivity
        have h := norm_xiCoeff_sq_le Λs N
        have hlog2 : Real.log N ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hlog0 hlogN 2
        have hF0 : 0 ≤ Fmaj ‖Λs‖⁻¹ N ^ 2 := sq_nonneg _
        calc ‖xiCoeff Λs N‖ ^ 2 / N = ‖xiCoeff Λs N‖ ^ 2 * (N:ℝ)⁻¹ := div_eq_mul_inv _ _
          _ ≤ (2 * Λ N ^ 2 + 2 * Real.log N ^ 2 * Fmaj ‖Λs‖⁻¹ N ^ 2) * (N:ℝ)⁻¹ :=
              mul_le_mul_of_nonneg_right h hN0
          _ ≤ (2 * Λ N ^ 2 + 2 * u ^ 2 * Fmaj ‖Λs‖⁻¹ N ^ 2) * (N:ℝ)⁻¹ := by gcongr
          _ = 2 * (Λ N ^ 2 / N) + 2 * u ^ 2 * (Fmaj ‖Λs‖⁻¹ N ^ 2 / N) := by ring
    _ = 2 * ∑ N ∈ Ioc 0 ⌊Real.exp u⌋₊, Λ N ^ 2 / N
        + 2 * u ^ 2 * ∑ N ∈ Ioc 0 ⌊Real.exp u⌋₊, Fmaj ‖Λs‖⁻¹ N ^ 2 / N := by
        rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ 2 * (u * (u + KM)) + 2 * u ^ 2 * CF := by gcongr
    _ ≤ CS * (1 + u) ^ 2 := by
        unfold CS
        nlinarith [KM_nonneg, CF_pos.le, sq_nonneg u, mul_nonneg hu KM_nonneg, mul_nonneg (sq_nonneg u) CF_pos.le]

/-! ### (H2) and (H1) for a T-indexed parameter with ‖Λ⋆(T)‖ ≥ l(T)/2 -/

/-- the height threshold: l(T) ≥ 64eK (so ‖Λ⋆‖ ≥ l/2 ≥ 32eK) and l(T) ≥ 1. -/
def T0coeff : ℝ := 2 * Real.pi * Real.exp (64 * Real.exp 1 * KM + 1)

lemma l_ge_of_T0coeff_le {T : ℝ} (hT : T0coeff ≤ T) : 64 * Real.exp 1 * KM + 1 ≤ l T := by
  unfold T0coeff at hT
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hT
  unfold l
  rw [Real.le_log_iff_exp_le (div_pos hTpos h2pi), le_div_iff₀ h2pi]
  linarith

/-- **(H2)**: Σ_{N≤x} ‖C(N;Λ⋆(T))‖² ≤ 4CS·x·l(T)² for 2 ≤ x ≤ e^{l(T)}, T ≥ T0coeff, whenever ‖Λ⋆(T)‖ ≥ l(T)/2. -/
theorem coeff_H2 (Λf : ℝ → ℂ) (hΛ : ∀ T, T0coeff ≤ T → l T / 2 ≤ ‖Λf T‖) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp (l T) →
      (∑ N ∈ Finset.Ioc 0 ⌊x⌋₊, ‖xiCoeff (Λf T) N‖ ^ 2) ≤ C * x * l T ^ 2 := by
  refine ⟨4 * CS, T0coeff, fun T hT x hx2 hxl => ?_⟩
  have hl := l_ge_of_T0coeff_le hT
  have hl1 : 1 ≤ l T := by nlinarith [KM_nonneg, Real.exp_pos 1]
  have hxpos : 0 < x := by linarith
  set u := Real.log x with hudef
  have hu0 : 0 ≤ u := Real.log_nonneg (by linarith)
  have hul : u ≤ l T := (Real.log_le_iff_le_exp hxpos).mpr hxl
  have hxexp : ⌊x⌋₊ = ⌊Real.exp u⌋₊ := by rw [hudef, Real.exp_log hxpos]
  have hnorm : l T / 2 ≤ ‖Λf T‖ := hΛ T hT
  have hΛpos : 0 < ‖Λf T‖ := lt_of_lt_of_le (by linarith) hnorm
  have hbig : 32 * Real.exp 1 * KM ≤ ‖Λf T‖ := by linarith
  have hxu : ‖Λf T‖⁻¹ * u ≤ 4 := by
    rw [inv_mul_le_iff₀ hΛpos]; linarith
  have hS := diagSum_le hu0 hxu hbig
  rw [← hxexp] at hS
  -- Σ ‖c‖² ≤ x · Σ ‖c‖²/N
  have hstep : ∑ N ∈ Ioc 0 ⌊x⌋₊, ‖xiCoeff (Λf T) N‖ ^ 2 ≤ x * ∑ N ∈ Ioc 0 ⌊x⌋₊, ‖xiCoeff (Λf T) N‖ ^ 2 / N := by
    rw [mul_sum]
    refine sum_le_sum fun N hN => ?_
    have hN0 : (0:ℝ) < N := by exact_mod_cast (mem_Ioc.mp hN).1
    have hNx : (N:ℝ) ≤ x := (Nat.cast_le.mpr (mem_Ioc.mp hN).2).trans (Nat.floor_le hxpos.le)
    rw [mul_div_assoc', le_div_iff₀ hN0, mul_comm x]
    exact mul_le_mul_of_nonneg_left hNx (sq_nonneg _)
  calc ∑ N ∈ Ioc 0 ⌊x⌋₊, ‖xiCoeff (Λf T) N‖ ^ 2
      ≤ x * (CS * (1 + u) ^ 2) := hstep.trans (mul_le_mul_of_nonneg_left hS hxpos.le)
    _ ≤ x * (CS * (2 * l T) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by linarith) (by linarith) 2) CS_pos.le) hxpos.le
    _ = 4 * CS * x * l T ^ 2 := by ring

/-- **(H1)**: Σ_{N≤x} ‖C(N;Λ⋆(T))‖/√N ≤ 2√CS·√x·l(T), same range, by Cauchy–Schwarz from the diagonal bound. -/
theorem coeff_H1 (Λf : ℝ → ℂ) (hΛ : ∀ T, T0coeff ≤ T → l T / 2 ≤ ‖Λf T‖) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp (l T) →
      (∑ N ∈ Finset.Ioc 0 ⌊x⌋₊, ‖xiCoeff (Λf T) N‖ / Real.sqrt N) ≤ C * Real.sqrt x * l T := by
  refine ⟨2 * Real.sqrt CS, T0coeff, fun T hT x hx2 hxl => ?_⟩
  have hl := l_ge_of_T0coeff_le hT
  have hl1 : 1 ≤ l T := by nlinarith [KM_nonneg, Real.exp_pos 1]
  have hxpos : 0 < x := by linarith
  set u := Real.log x with hudef
  have hu0 : 0 ≤ u := Real.log_nonneg (by linarith)
  have hul : u ≤ l T := (Real.log_le_iff_le_exp hxpos).mpr hxl
  have hxexp : ⌊x⌋₊ = ⌊Real.exp u⌋₊ := by rw [hudef, Real.exp_log hxpos]
  have hnorm : l T / 2 ≤ ‖Λf T‖ := hΛ T hT
  have hΛpos : 0 < ‖Λf T‖ := lt_of_lt_of_le (by linarith) hnorm
  have hbig : 32 * Real.exp 1 * KM ≤ ‖Λf T‖ := by linarith
  have hxu : ‖Λf T‖⁻¹ * u ≤ 4 := by
    rw [inv_mul_le_iff₀ hΛpos]; linarith
  have hS := diagSum_le hu0 hxu hbig
  rw [← hxexp] at hS
  -- Cauchy–Schwarz: (Σ a_N)² ≤ #· Σ a_N², a_N = ‖c‖/√N, a_N² = ‖c‖²/N
  have hcs := sq_sum_le_card_mul_sum_sq (s := Ioc 0 ⌊x⌋₊) (f := fun N => ‖xiCoeff (Λf T) N‖ / Real.sqrt N)
  have hsq : ∀ N ∈ Ioc 0 ⌊x⌋₊, (‖xiCoeff (Λf T) N‖ / Real.sqrt N) ^ 2 = ‖xiCoeff (Λf T) N‖ ^ 2 / N := by
    intro N hN
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  rw [sum_congr rfl hsq] at hcs
  have hcard : ((Ioc 0 ⌊x⌋₊).card : ℝ) ≤ x := by
    simp only [Nat.card_Ioc, Nat.sub_zero]
    exact Nat.floor_le hxpos.le
  have hS0 : 0 ≤ ∑ N ∈ Ioc 0 ⌊x⌋₊, ‖xiCoeff (Λf T) N‖ ^ 2 / N :=
    sum_nonneg fun N _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg N)
  have hbound : (∑ N ∈ Ioc 0 ⌊x⌋₊, ‖xiCoeff (Λf T) N‖ / Real.sqrt N) ^ 2 ≤ x * (CS * (2 * l T) ^ 2) := by
    calc (∑ N ∈ Ioc 0 ⌊x⌋₊, ‖xiCoeff (Λf T) N‖ / Real.sqrt N) ^ 2
        ≤ (Ioc 0 ⌊x⌋₊).card * ∑ N ∈ Ioc 0 ⌊x⌋₊, ‖xiCoeff (Λf T) N‖ ^ 2 / N := hcs
      _ ≤ x * (CS * (1 + u) ^ 2) := mul_le_mul hcard hS hS0 hxpos.le
      _ ≤ x * (CS * (2 * l T) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by linarith) (by linarith) 2) CS_pos.le) hxpos.le
  have hlhs0 : 0 ≤ ∑ N ∈ Ioc 0 ⌊x⌋₊, ‖xiCoeff (Λf T) N‖ / Real.sqrt N :=
    sum_nonneg fun N _ => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hrhs : x * (CS * (2 * l T) ^ 2) = (2 * Real.sqrt CS * Real.sqrt x * l T) ^ 2 := by
    rw [show (2 * Real.sqrt CS * Real.sqrt x * l T) ^ 2
        = 4 * Real.sqrt CS ^ 2 * Real.sqrt x ^ 2 * l T ^ 2 by ring,
      Real.sq_sqrt CS_pos.le, Real.sq_sqrt hxpos.le]
    ring
  rw [hrhs] at hbound
  have hrhs0 : 0 ≤ 2 * Real.sqrt CS * Real.sqrt x * l T := mul_nonneg (by positivity) (by linarith)
  exact (pow_le_pow_iff_left₀ hlhs0 hrhs0 two_ne_zero).mp hbound

end XiPrime
end Zeta23
