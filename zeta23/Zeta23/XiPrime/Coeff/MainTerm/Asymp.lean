/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Coeff/MainTerm/Asymp.lean — the k-fold Mertens induction.

  Tk k u := Σ_{N ≤ e^u} (Λ·log)^{∗k}(N)/N,      Wk k u := Σ_{N ≤ e^u} (Λ·log)^{∗k}(N)·log²N/N.
Results:
  Tk_zero, Tk_succ (the recursion from PowerSums.Sdiv_mul),
  Tk_asymp : |Tk k u − u^{2k}/(2k)!| ≤ C_k (1+u)^{2k−1}            (u ≥ 0),
  Wk_asymp : |Wk k u − k/((k+1)(2k)!)·u^{2k+2}| ≤ C_k (1+u)^{2k+1}  (u ≥ 0, k ≥ 1).
The only analytic input is Coeff/Abel.mertens_step (Mertens' first theorem + Abel summation); Wk is
obtained from Tk by one more Abel summation in N with weight log²N.  All constants are free except the
leading rational k/((k+1)(2k)!) of Wk_asymp, which is exact ([XF′ Lemma 7.1(i)]: it produces D_{1,k}).
-/
import Zeta23.XiPrime.Coeff.PowerSums

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Omega
open Finset Real MeasureTheory

noncomputable section

namespace Zeta23
namespace XiPrime

/-! ### definitions and the recursion -/

/-- Tk k u := Σ_{N ≤ e^u} (Λ·log)^{∗k}(N)/N. -/
def Tk (k : ℕ) (u : ℝ) : ℝ := Sdiv (lamLog ^ k) u

/-- Wk k u := Σ_{N ≤ e^u} (Λ·log)^{∗k}(N)·(log N)²/N. -/
def Wk (k : ℕ) (u : ℝ) : ℝ :=
  ∑ N ∈ Finset.Ioc 0 ⌊Real.exp u⌋₊, (lamLog ^ k) N * Real.log N ^ 2 / N

lemma Tk_def (k : ℕ) (u : ℝ) : Tk k u = ∑ N ∈ Finset.Ioc 0 ⌊Real.exp u⌋₊, (lamLog ^ k) N / N := rfl

lemma Wk_def (k : ℕ) (u : ℝ) :
    Wk k u = ∑ N ∈ Finset.Ioc 0 ⌊Real.exp u⌋₊, (lamLog ^ k) N * Real.log N ^ 2 / N := rfl

lemma Tk_zero {u : ℝ} (hu : 0 ≤ u) : Tk 0 u = 1 := by
  rw [Tk, pow_zero]; exact Sdiv_one hu

lemma Tk_succ (k : ℕ) (u : ℝ) :
    Tk (k + 1) u = ∑ d ∈ Ioc 0 ⌊Real.exp u⌋₊, Λ d * Real.log d / d * Tk k (u - Real.log d) := by
  unfold Tk
  rw [pow_succ', Sdiv_mul]
  simp_rw [lamLog_apply]

lemma Tk_mono (k : ℕ) : Monotone (Tk k) := Sdiv_mono (lamLogPow_nonneg k)

lemma Tk_nonneg (k : ℕ) (u : ℝ) : 0 ≤ Tk k u := Sdiv_nonneg (lamLogPow_nonneg k) u

/-- Σ_{d ≤ e^u} Λ(d) log d / d ≤ u·(u + K). -/
lemma sum_lam_log_div_le {u : ℝ} (hu : 0 ≤ u) :
    ∑ d ∈ Ioc 0 ⌊Real.exp u⌋₊, Λ d * Real.log d / d ≤ u * (u + KM) := by
  calc ∑ d ∈ Ioc 0 ⌊Real.exp u⌋₊, Λ d * Real.log d / d
      ≤ ∑ d ∈ Ioc 0 ⌊Real.exp u⌋₊, u * (Λ d / d) := by
        refine sum_le_sum fun d hd => ?_
        have hlog : Real.log d ≤ u := log_le_of_mem_Ioc_floor_exp hd
        have h0 : 0 ≤ Λ d / d := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d)
        calc Λ d * Real.log d / d = Real.log d * (Λ d / d) := by ring
          _ ≤ u * (Λ d / d) := mul_le_mul_of_nonneg_right hlog h0
    _ = u * Sdiv Λ u := by rw [← mul_sum]; rfl
    _ ≤ u * (u + KM) := mul_le_mul_of_nonneg_left (Sdiv_lam_le hu) hu

/-- **the one-variable Mertens sums**  Σ_{n ≤ e^u} Λ(n)/n·(log n)^j = u^{j+1}/(j+1) + O((1+u)^j)
(mertens_step with f(v) = v^j; j = 1 is Tk 1, and j = 1, 2, 3 are the three sums of the k = 1 (prime) term). -/
theorem sum_vonMangoldt_div_mul_log_pow (j : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |(∑ n ∈ Ioc 0 ⌊Real.exp u⌋₊, Λ n / n * Real.log n ^ j) - u ^ (j + 1) / (j + 1)|
      ≤ KM * (j + 1) * (1 + u) ^ j := by
  have hK := KM_nonneg
  have hderiv : ∀ v ∈ Set.Icc 0 u, HasDerivAt (fun v : ℝ => v ^ j) ((fun v : ℝ => (j : ℝ) * v ^ (j - 1)) v) v :=
    fun v _ => by simpa using (hasDerivAt_id' v).fun_pow j
  have hcont : ContinuousOn (fun v : ℝ => (j : ℝ) * v ^ (j - 1)) (Set.Icc 0 u) := by fun_prop
  have hstep := mertens_step hu hderiv hcont
  rw [integral_pow] at hstep
  simp only [zero_pow (Nat.succ_ne_zero j), sub_zero] at hstep
  have h1 : |u ^ j| ≤ (1 + u) ^ j := by
    rw [abs_of_nonneg (pow_nonneg hu j)]; exact pow_le_pow_left₀ hu (by linarith) j
  have h2 : ∫ v in (0:ℝ)..u, |(j : ℝ) * v ^ (j - 1)| ≤ j * (1 + u) ^ j := by
    have hint : IntervalIntegrable (fun v : ℝ => |(j : ℝ) * v ^ (j - 1)|) MeasureTheory.volume 0 u := by
      apply Continuous.intervalIntegrable; fun_prop
    calc ∫ v in (0:ℝ)..u, |(j : ℝ) * v ^ (j - 1)| ≤ ∫ _ in (0:ℝ)..u, (j : ℝ) * (1 + u) ^ (j - 1) := by
          refine intervalIntegral.integral_mono_on hu hint intervalIntegrable_const fun v hv => ?_
          rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg j) (pow_nonneg hv.1 _))]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv.1 (by linarith [hv.2]) _) (Nat.cast_nonneg j)
      _ = (j : ℝ) * (u * (1 + u) ^ (j - 1)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]; ring
      _ ≤ j * (1 + u) ^ j := by
          rcases j with _ | m
          · simp
          · refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            rw [Nat.add_sub_cancel, pow_succ' (1 + u) m]
            exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have e : ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) := by push_cast; ring
  calc |(∑ n ∈ Ioc 0 ⌊Real.exp u⌋₊, Λ n / n * Real.log n ^ j) - u ^ (j + 1) / (j + 1)|
      ≤ KM * (|u ^ j| + ∫ v in (0:ℝ)..u, |(j : ℝ) * v ^ (j - 1)|) := by exact_mod_cast hstep
    _ ≤ KM * ((1 + u) ^ j + j * (1 + u) ^ j) := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hK
    _ = KM * (j + 1) * (1 + u) ^ j := by ring

/-! ### the Mertens induction for Tk -/

/-- the polynomial integral ∫₀ᵘ v (u − v)^N dv = u^{N+2}/((N+1)(N+2)). -/
lemma integral_mul_sub_pow (u : ℝ) (N : ℕ) :
    ∫ v in (0:ℝ)..u, v * (u - v) ^ N = u ^ (N + 2) / ((N + 1) * (N + 2)) := by
  have h := intervalIntegral.integral_comp_sub_left (fun w => (u - w) * w ^ N) u (a := 0) (b := u)
  simp only [sub_sub_cancel, sub_self, sub_zero] at h
  rw [h]
  have h2 : ∫ w in (0:ℝ)..u, (u - w) * w ^ N = ∫ w in (0:ℝ)..u, (u * w ^ N - w ^ (N + 1)) :=
    intervalIntegral.integral_congr fun w _ => by ring
  rw [h2, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  · have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
    have h3 : (N : ℝ) + 1 + 1 ≠ 0 := by positivity
    simp only [zero_pow (Nat.succ_ne_zero _), sub_zero]
    push_cast
    field_simp
    ring
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop

/-- **The induction step.**  From |Tk k v − v^N/N!| ≤ C(1+v)^n (v ≥ 0, N = n+1) deduce
|Tk (k+1) u − u^{N+2}/(N+2)!| ≤ (K(N+1) + C(1+K))·(1+u)^{N+1}  (u ≥ 0). -/
lemma Tk_step (k n N : ℕ) (hN : N = n + 1) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v, 0 ≤ v → |Tk k v - v ^ N / N.factorial| ≤ C * (1 + v) ^ n) :
    ∀ u, 0 ≤ u → |Tk (k + 1) u - u ^ (N + 2) / (N + 2).factorial|
      ≤ (KM * (N + 1) + C * (1 + KM)) * (1 + u) ^ (N + 1) := by
  subst hN
  intro u hu
  have hK := KM_nonneg
  have hNf : (0:ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hNf1 : (1:ℝ) ≤ (n + 1).factorial := by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
  -- the comparison function f(v) = v (u − v)^N / N! and its derivative
  set f : ℝ → ℝ := fun v => v * (u - v) ^ (n + 1) / (n + 1).factorial with hf
  set f' : ℝ → ℝ := fun v =>
    ((u - v) ^ (n + 1) - (n + 1) * v * (u - v) ^ n) / (n + 1).factorial with hf'
  have hderiv : ∀ v ∈ Set.Icc 0 u, HasDerivAt f (f' v) v := by
    intro v _
    have h1 : HasDerivAt (fun v : ℝ => v) 1 v := hasDerivAt_id' v
    have h2 := ((hasDerivAt_id' v).const_sub u).fun_pow (n + 1)
    have h3 := (h1.mul h2).div_const ((n + 1).factorial : ℝ)
    refine h3.congr_deriv ?_
    simp only [hf', Nat.add_sub_cancel]
    push_cast
    ring
  have hf'c : ContinuousOn f' (Set.Icc 0 u) := by
    simp only [hf']
    fun_prop
  have hstep := mertens_step hu hderiv hf'c
  -- f u = 0
  have hfu : f u = 0 := by simp [hf]
  -- ∫₀ᵘ f = u^{N+2}/(N+2)!
  have hint_f : ∫ v in (0:ℝ)..u, f v = u ^ (n + 1 + 2) / (n + 1 + 2).factorial := by
    simp only [hf]
    rw [intervalIntegral.integral_div, integral_mul_sub_pow]
    rw [show n + 1 + 2 = (n + 1 + 1) + 1 from rfl, Nat.factorial_succ (n + 1 + 1),
      Nat.factorial_succ (n + 1)]
    push_cast
    field_simp
    ring
  -- ∫₀ᵘ |f′| ≤ (N+1)(1+u)^{N+1}
  have hbound_f' : ∀ v ∈ Set.Icc 0 u, |f' v| ≤ (n + 2) * (1 + u) ^ (n + 1) := by
    intro v hv
    have hv0 : 0 ≤ v := hv.1
    have hw : 0 ≤ u - v := by linarith [hv.2]
    have hw1 : u - v ≤ 1 + u := by linarith
    have hv1 : v ≤ 1 + u := by linarith [hv.2]
    have ha : (u - v) ^ (n + 1) ≤ (1 + u) ^ (n + 1) := pow_le_pow_left₀ hw hw1 _
    have hb : (n + 1 : ℝ) * v * (u - v) ^ n ≤ (n + 1) * (1 + u) * (1 + u) ^ n := by
      gcongr
    have hnum : |(u - v) ^ (n + 1) - (n + 1) * v * (u - v) ^ n|
        ≤ (n + 2) * (1 + u) ^ (n + 1) := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg (pow_nonneg hw _),
        abs_of_nonneg (mul_nonneg (mul_nonneg (by positivity) hv0) (pow_nonneg hw _))]
      calc (u - v) ^ (n + 1) + (n + 1) * v * (u - v) ^ n
          ≤ (1 + u) ^ (n + 1) + (n + 1) * (1 + u) * (1 + u) ^ n := add_le_add ha hb
        _ = (n + 2) * (1 + u) ^ (n + 1) := by ring
    simp only [hf']
    rw [abs_div, abs_of_pos hNf]
    exact (div_le_self (abs_nonneg _) hNf1).trans hnum
  have hint_f'_int : IntervalIntegrable (fun v => |f' v|) volume 0 u := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hu]
    exact hf'c.abs
  have hint_f' : ∫ v in (0:ℝ)..u, |f' v| ≤ (n + 2) * (1 + u) ^ (n + 1 + 1) := by
    calc ∫ v in (0:ℝ)..u, |f' v| ≤ ∫ _ in (0:ℝ)..u, ((n:ℝ) + 2) * (1 + u) ^ (n + 1) :=
          intervalIntegral.integral_mono_on hu hint_f'_int intervalIntegrable_const hbound_f'
      _ = u * ((n + 2) * (1 + u) ^ (n + 1)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      _ ≤ (1 + u) * ((n + 2) * (1 + u) ^ (n + 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (n + 2) * (1 + u) ^ (n + 1 + 1) := by ring
  -- split Tk (k+1) u = main + error
  set X : ℕ := ⌊Real.exp u⌋₊ with hX
  set R : ℕ → ℝ := fun d => Tk k (u - Real.log d) - (u - Real.log d) ^ (n + 1) / (n + 1).factorial
    with hR
  have hsplit : Tk (k + 1) u
      = (∑ d ∈ Ioc 0 X, Λ d / d * f (Real.log d)) + ∑ d ∈ Ioc 0 X, Λ d * Real.log d / d * R d := by
    rw [Tk_succ, ← sum_add_distrib]
    refine sum_congr rfl fun d _ => ?_
    simp only [hf, hR]
    ring
  -- the error sum
  have hRd : ∀ d ∈ Ioc 0 X, |R d| ≤ C * (1 + u) ^ n := by
    intro d hd
    have hlog : Real.log d ≤ u := log_le_of_mem_Ioc_floor_exp hd
    have hlog0 : 0 ≤ Real.log d := Real.log_natCast_nonneg d
    refine (h (u - Real.log d) (by linarith)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hC
    exact pow_le_pow_left₀ (by linarith) (by linarith) n
  have herr : |∑ d ∈ Ioc 0 X, Λ d * Real.log d / d * R d| ≤ C * (1 + u) ^ n * (u * (u + KM)) := by
    calc |∑ d ∈ Ioc 0 X, Λ d * Real.log d / d * R d|
        ≤ ∑ d ∈ Ioc 0 X, |Λ d * Real.log d / d * R d| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Ioc 0 X, Λ d * Real.log d / d * (C * (1 + u) ^ n) := by
          refine sum_le_sum fun d hd => ?_
          have ha : 0 ≤ Λ d * Real.log d / d :=
            div_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg d))
              (Nat.cast_nonneg d)
          rw [abs_mul, abs_of_nonneg ha]
          exact mul_le_mul_of_nonneg_left (hRd d hd) ha
      _ = C * (1 + u) ^ n * ∑ d ∈ Ioc 0 X, Λ d * Real.log d / d := by rw [← sum_mul]; ring
      _ ≤ C * (1 + u) ^ n * (u * (u + KM)) :=
          mul_le_mul_of_nonneg_left (sum_lam_log_div_le hu) (by positivity)
  -- assemble
  have hmain : |(∑ d ∈ Ioc 0 X, Λ d / d * f (Real.log d)) - u ^ (n + 1 + 2) / (n + 1 + 2).factorial|
      ≤ KM * ((n + 2) * (1 + u) ^ (n + 1 + 1)) := by
    rw [← hint_f]
    refine hstep.trans ?_
    rw [hfu, abs_zero, zero_add]
    exact mul_le_mul_of_nonneg_left hint_f' hK
  have huK : u * (u + KM) ≤ (1 + u) * ((1 + u) * (1 + KM)) := by
    apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
    nlinarith
  calc |Tk (k + 1) u - u ^ (n + 1 + 2) / (n + 1 + 2).factorial|
      = |((∑ d ∈ Ioc 0 X, Λ d / d * f (Real.log d)) - u ^ (n + 1 + 2) / (n + 1 + 2).factorial)
          + ∑ d ∈ Ioc 0 X, Λ d * Real.log d / d * R d| := by rw [hsplit]; ring_nf
    _ ≤ |(∑ d ∈ Ioc 0 X, Λ d / d * f (Real.log d)) - u ^ (n + 1 + 2) / (n + 1 + 2).factorial|
          + |∑ d ∈ Ioc 0 X, Λ d * Real.log d / d * R d| := abs_add_le _ _
    _ ≤ KM * ((n + 2) * (1 + u) ^ (n + 1 + 1)) + C * (1 + u) ^ n * (u * (u + KM)) :=
        add_le_add hmain herr
    _ ≤ KM * ((n + 2) * (1 + u) ^ (n + 1 + 1)) + C * (1 + u) ^ n * ((1 + u) * ((1 + u) * (1 + KM))) := by
        gcongr
    _ = (KM * ((n + 1 : ℕ) + 1) + C * (1 + KM)) * (1 + u) ^ (n + 1 + 1) := by push_cast; ring

/-- base case: |Tk 1 u − u²/2| ≤ 2K(1+u). -/
lemma Tk_one_asymp (u : ℝ) (hu : 0 ≤ u) : |Tk 1 u - u ^ 2 / (2).factorial| ≤ 2 * KM * (1 + u) ^ 1 := by
  have hK := KM_nonneg
  have hT1 : Tk 1 u = ∑ d ∈ Ioc 0 ⌊Real.exp u⌋₊, Λ d / d * (fun v : ℝ => v) (Real.log d) := by
    rw [show (1:ℕ) = 0 + 1 from rfl, Tk_succ]
    refine sum_congr rfl fun d hd => ?_
    have hlog : Real.log d ≤ u := log_le_of_mem_Ioc_floor_exp hd
    rw [Tk_zero (by linarith)]
    ring
  have hderiv : ∀ v ∈ Set.Icc 0 u, HasDerivAt (fun v : ℝ => v) ((fun _ => (1:ℝ)) v) v :=
    fun v _ => hasDerivAt_id' v
  have hstep := mertens_step hu hderiv continuousOn_const
  rw [← hT1, integral_id, abs_of_nonneg hu] at hstep
  simp only [abs_one, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at hstep
  have h2 : ((2).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [h2]
  calc |Tk 1 u - u ^ 2 / 2| = |Tk 1 u - (u ^ 2 - 0 ^ 2) / 2| := by ring_nf
    _ ≤ KM * (u + u) := hstep
    _ ≤ 2 * KM * (1 + u) ^ 1 := by nlinarith

/-- the induction, in the subtraction-free form k = j+1. -/
lemma Tk_asymp_succ : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u →
    |Tk (j + 1) u - u ^ (2 * j + 2) / (2 * j + 2).factorial| ≤ C * (1 + u) ^ (2 * j + 1)
  | 0 => ⟨2 * KM, by positivity [KM_nonneg], fun u hu => by simpa using Tk_one_asymp u hu⟩
  | j + 1 => by
      obtain ⟨C, hC, h⟩ := Tk_asymp_succ j
      refine ⟨KM * ((2 * j + 2 : ℕ) + 1) + C * (1 + KM), by positivity [KM_nonneg], fun u hu => ?_⟩
      have := Tk_step (j + 1) (2 * j + 1) (2 * j + 2) (by ring) hC h u hu
      have e1 : 2 * (j + 1) + 2 = 2 * j + 2 + 2 := by ring
      have e2 : 2 * (j + 1) + 1 = 2 * j + 2 + 1 := by ring
      rw [e1, e2]
      exact this

/-- **B2.**  |Tk k u − u^{2k}/(2k)!| ≤ C_k (1+u)^{2k−1} for u ≥ 0. -/
theorem Tk_asymp (k : ℕ) :
    ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → |Tk k u - u ^ (2 * k) / (2 * k).factorial| ≤ C * (1 + u) ^ (2 * k - 1) := by
  rcases k with _ | j
  · refine ⟨0, fun u hu => ?_⟩
    rw [Tk_zero hu]
    simp
  · obtain ⟨C, -, h⟩ := Tk_asymp_succ j
    refine ⟨C, fun u hu => ?_⟩
    have e1 : 2 * (j + 1) = 2 * j + 2 := by ring
    have e2 : 2 * j + 2 - 1 = 2 * j + 1 := by omega
    rw [e1, e2]
    exact h u hu

/-- Tk_asymp with a nonnegative constant. -/
lemma Tk_asymp' (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ u : ℝ, 0 ≤ u → |Tk k u - u ^ (2 * k) / (2 * k).factorial| ≤ C * (1 + u) ^ (2 * k - 1) := by
  obtain ⟨C, h⟩ := Tk_asymp k
  refine ⟨|C|, abs_nonneg C, fun u hu => (h u hu).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)

/-! ### Wk from Tk by Abel summation with weight log² -/

/-- Tk k (log t) as the partial sum that Abel summation produces. -/
lemma Tk_log_eq_sum_Icc (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ∑ N ∈ Icc 0 ⌊t⌋₊, (lamLog ^ k) N / N = Tk k (Real.log t) := by
  unfold Tk Sdiv
  rw [Real.exp_log ht]
  exact sum_Icc_eq_sum_Ioc' (by simp) _

/-- **B3.**  |Wk k u − k/((k+1)(2k)!)·u^{2k+2}| ≤ C_k (1+u)^{2k+1} for u ≥ 0 (k ≥ 1). -/
theorem Wk_asymp (k : ℕ) (hk : 1 ≤ k) : ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    |Wk k u - (k : ℝ) / ((k + 1) * (2 * k).factorial) * u ^ (2 * k + 2)| ≤ C * (1 + u) ^ (2 * k + 1) := by
  obtain ⟨C, hC, hT⟩ := Tk_asymp' k
  refine ⟨3 * C, fun u hu => ?_⟩
  set x : ℝ := Real.exp u with hxdef
  have hx : 1 ≤ x := by rw [hxdef]; exact Real.one_le_exp hu
  have hx0 : 0 < x := Real.exp_pos u
  have hlogx : Real.log x = u := by rw [hxdef, Real.log_exp]
  have huIcc : Set.uIcc 1 x = Set.Icc 1 x := Set.uIcc_of_le hx
  have hpos : ∀ t ∈ Set.Icc (1:ℝ) x, 0 < t := fun t ht => lt_of_lt_of_le one_pos ht.1
  have hfk : (0:ℝ) < (2 * k).factorial := by exact_mod_cast Nat.factorial_pos _
  -- weight g(t) = log² t and its derivative
  set g : ℝ → ℝ := fun t => Real.log t ^ 2 with hg
  set g' : ℝ → ℝ := fun t => 2 * Real.log t * t⁻¹ with hg'
  have hgd : ∀ t ∈ Set.Icc 1 x, HasDerivAt g (g' t) t := by
    intro t ht
    have := (Real.hasDerivAt_log (hpos t ht).ne').fun_pow 2
    refine this.congr_deriv ?_
    simp [hg']
  have hlogc : ContinuousOn Real.log (Set.Icc 1 x) := fun t ht =>
    (Real.continuousAt_log (hpos t ht).ne').continuousWithinAt
  have hinvc : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc 1 x) :=
    continuousOn_inv₀.mono fun t ht => (hpos t ht).ne'
  have hg'c : ContinuousOn g' (Set.Icc 1 x) := by
    simp only [hg']
    exact (continuousOn_const.mul hlogc).mul hinvc
  -- (1) Abel summation:  Wk k u = u²·Tk k u − ∫₁ˣ g′(t)·Tk k (log t) dt
  have habel : Wk k u = u ^ 2 * Tk k u - ∫ t in (1:ℝ)..x, g' t * Tk k (Real.log t) := by
    have hdiff : ∀ t ∈ Set.Icc 1 x, DifferentiableAt ℝ g t := fun t ht => (hgd t ht).differentiableAt
    have hint : IntegrableOn (deriv g) (Set.Icc 1 x) :=
      (hg'c.integrableOn_Icc).congr_fun (fun t ht => ((hgd t ht).deriv).symm) measurableSet_Icc
    have h := sum_mul_eq_sub_integral_mul₀ (fun N => (lamLog ^ k) N / N) (by simp) x hdiff hint
    rw [Tk_log_eq_sum_Icc k hx0, hlogx] at h
    have hL : ∑ N ∈ Icc 0 ⌊x⌋₊, g N * ((lamLog ^ k) N / N) = Wk k u := by
      rw [sum_Icc_eq_sum_Ioc' (by simp [hg])]
      unfold Wk
      refine sum_congr rfl fun N _ => ?_
      simp only [hg]; ring
    rw [hL] at h
    rw [h, intervalIntegral.integral_of_le hx]
    have hgx : g x = u ^ 2 := by simp only [hg]; rw [hlogx]
    rw [hgx]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht' : t ∈ Set.Icc 1 x := Set.Ioc_subset_Icc_self ht
    rw [(hgd t ht').deriv, Tk_log_eq_sum_Icc k (hpos t ht')]
  -- (2) the main integral  ∫₁ˣ g′(t)·(log t)^{2k}/(2k)! dt = u^{2k+2}/((k+1)(2k)!)
  set m : ℝ → ℝ := fun t => Real.log t ^ (2 * k) / (2 * k).factorial with hm
  have hmc : ContinuousOn m (Set.Icc 1 x) := by
    simp only [hm]; exact (hlogc.pow _).div_const _
  have hI1int : IntervalIntegrable (fun t => g' t * m t) volume 1 x := by
    apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact hg'c.mul hmc
  have hI1 : ∫ t in (1:ℝ)..x, g' t * m t = u ^ (2 * k + 2) / ((k + 1) * (2 * k).factorial) := by
    set F : ℝ → ℝ := fun t => Real.log t ^ (2 * k + 2) / ((k + 1) * (2 * k).factorial) with hF
    have hFd : ∀ t ∈ Set.uIcc 1 x, HasDerivAt F (g' t * m t) t := by
      intro t ht
      rw [huIcc] at ht
      have h1 := ((Real.hasDerivAt_log (hpos t ht).ne').fun_pow (2 * k + 2)).div_const
        ((k + 1) * (2 * k).factorial : ℝ)
      have e : 2 * k + 2 - 1 = 2 * k + 1 := by omega
      rw [e] at h1
      refine h1.congr_deriv ?_
      simp only [hg', hm]
      have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      push_cast
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hFd hI1int]
    simp only [hF, Real.log_one, hlogx]
    have : (0:ℝ) ^ (2 * k + 2) = 0 := zero_pow (by omega)
    rw [this, zero_div, sub_zero]
  -- (3) the error integral
  have hTlog : IntervalIntegrable (fun t => Tk k (Real.log t)) volume 1 x := by
    apply MonotoneOn.intervalIntegrable
    rw [huIcc]
    intro s hs t ht hst
    exact Tk_mono k (Real.log_le_log (hpos s hs) hst)
  have hmint : IntervalIntegrable m volume 1 x := by
    apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact hmc
  have hI2int : IntervalIntegrable (fun t => g' t * (Tk k (Real.log t) - m t)) volume 1 x :=
    (hTlog.sub hmint).continuousOn_mul (by rw [huIcc]; exact hg'c)
  have hsplitI : ∫ t in (1:ℝ)..x, g' t * Tk k (Real.log t)
      = (∫ t in (1:ℝ)..x, g' t * m t) + ∫ t in (1:ℝ)..x, g' t * (Tk k (Real.log t) - m t) := by
    rw [← intervalIntegral.integral_add hI1int hI2int]
    exact intervalIntegral.integral_congr fun t _ => by ring
  have hI2 : |∫ t in (1:ℝ)..x, g' t * (Tk k (Real.log t) - m t)|
      ≤ 2 * u * C * (1 + u) ^ (2 * k - 1) * u := by
    have hbd : ∀ t ∈ Set.Icc 1 x, |g' t * (Tk k (Real.log t) - m t)|
        ≤ 2 * u * C * (1 + u) ^ (2 * k - 1) * t⁻¹ := by
      intro t ht
      have ht0 := hpos t ht
      have hlt0 : 0 ≤ Real.log t := Real.log_nonneg ht.1
      have hltu : Real.log t ≤ u := by rw [← hlogx]; exact Real.log_le_log ht0 ht.2
      have hg'0 : 0 ≤ g' t := by simp only [hg']; positivity
      have hg'le : g' t ≤ 2 * u * t⁻¹ := by
        simp only [hg']
        exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr ht0.le)
      have hRt : |Tk k (Real.log t) - m t| ≤ C * (1 + u) ^ (2 * k - 1) := by
        refine (hT (Real.log t) hlt0).trans ?_
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) _) hC
      rw [abs_mul, abs_of_nonneg hg'0]
      calc g' t * |Tk k (Real.log t) - m t| ≤ (2 * u * t⁻¹) * (C * (1 + u) ^ (2 * k - 1)) :=
            mul_le_mul hg'le hRt (abs_nonneg _) (by positivity)
        _ = 2 * u * C * (1 + u) ^ (2 * k - 1) * t⁻¹ := by ring
    have hbint : IntervalIntegrable (fun t : ℝ => 2 * u * C * (1 + u) ^ (2 * k - 1) * t⁻¹) volume 1 x := by
      apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact continuousOn_const.mul hinvc
    calc |∫ t in (1:ℝ)..x, g' t * (Tk k (Real.log t) - m t)|
        ≤ ∫ t in (1:ℝ)..x, |g' t * (Tk k (Real.log t) - m t)| :=
          intervalIntegral.abs_integral_le_integral_abs hx
      _ ≤ ∫ t in (1:ℝ)..x, 2 * u * C * (1 + u) ^ (2 * k - 1) * t⁻¹ :=
          intervalIntegral.integral_mono_on hx hI2int.abs hbint hbd
      _ = 2 * u * C * (1 + u) ^ (2 * k - 1) * u := by
          rw [intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos hx0, div_one, hlogx]
  -- (4) assemble
  have hkey : Wk k u - (k : ℝ) / ((k + 1) * (2 * k).factorial) * u ^ (2 * k + 2)
      = u ^ 2 * (Tk k u - u ^ (2 * k) / (2 * k).factorial)
        - ∫ t in (1:ℝ)..x, g' t * (Tk k (Real.log t) - m t) := by
    rw [habel, hsplitI, hI1]
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have hpow : (1 + u) ^ (2 * k - 1) * (1 + u) ^ 2 = (1 + u) ^ (2 * k + 1) := by
    rw [← pow_add]; congr 1; omega
  have hu2 : u ^ 2 ≤ (1 + u) ^ 2 := pow_le_pow_left₀ hu (by linarith) 2
  have hP : 0 ≤ (1 + u) ^ (2 * k - 1) := by positivity
  rw [hkey]
  calc |u ^ 2 * (Tk k u - u ^ (2 * k) / (2 * k).factorial)
          - ∫ t in (1:ℝ)..x, g' t * (Tk k (Real.log t) - m t)|
      ≤ |u ^ 2 * (Tk k u - u ^ (2 * k) / (2 * k).factorial)|
          + |∫ t in (1:ℝ)..x, g' t * (Tk k (Real.log t) - m t)| := abs_sub _ _
    _ ≤ u ^ 2 * (C * (1 + u) ^ (2 * k - 1)) + 2 * u * C * (1 + u) ^ (2 * k - 1) * u := by
        refine add_le_add ?_ hI2
        rw [abs_mul, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (hT u hu) (by positivity)
    _ = 3 * C * ((1 + u) ^ (2 * k - 1) * u ^ 2) := by ring
    _ ≤ 3 * C * ((1 + u) ^ (2 * k - 1) * (1 + u) ^ 2) := by gcongr
    _ = 3 * C * (1 + u) ^ (2 * k + 1) := by rw [hpow]

end XiPrime
end Zeta23
