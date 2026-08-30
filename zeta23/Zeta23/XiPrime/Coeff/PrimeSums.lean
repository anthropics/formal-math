/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Coeff/PrimeSums.lean — Mertens-level monomial sums and the prime sums Σ_{p≤e^u} log^b p / p.
Used for the k = 1 (N prime) part of the diagonal law [XF′ Lemma 7.1 (i), D_{1,1}].

  |Σ_{n ≤ e^u} (Λ(n)/n)(log n)^a − u^{a+1}/(a+1)| ≤ 2K(1+u)^a                    (mertens_step with f = v^a),
  |Σ_{p ≤ e^u, p prime} (log p)^{b}/p − u^{b}/b| ≤ C_b (1+u)^{b−1}   (b ≥ 2)      (non-primes: defect bound).
-/
import Zeta23.XiPrime.Coeff.NonSquarefree
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped BigOperators ArithmeticFunction
open Finset Real

noncomputable section

namespace Zeta23
namespace XiPrime

/-- Σ_{n ≤ e^u} (Λ n/n)·(log n)^a = u^{a+1}/(a+1) + O((1+u)^a). -/
theorem mertens_monomial (a : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |(∑ n ∈ Ioc 0 ⌊Real.exp u⌋₊, Λ n / n * Real.log n ^ a) - u ^ (a + 1) / (a + 1)|
      ≤ 2 * KM * (1 + u) ^ a := by
  have hderiv : ∀ v ∈ Set.Icc 0 u, HasDerivAt (fun v => v ^ a) ((a : ℝ) * v ^ (a - 1)) v := by
    intro v _
    simpa using (hasDerivAt_id v).fun_pow a
  have hcont : ContinuousOn (fun v => (a : ℝ) * v ^ (a - 1)) (Set.Icc 0 u) := by fun_prop
  have h := mertens_step hu hderiv hcont
  rw [integral_pow] at h
  rw [zero_pow (Nat.succ_ne_zero a), sub_zero] at h
  have h1 : |u ^ a| ≤ (1 + u) ^ a := by
    rw [abs_of_nonneg (pow_nonneg hu a)]
    exact pow_le_pow_left₀ hu (by linarith) a
  have h2 : ∫ v in (0:ℝ)..u, |(a : ℝ) * v ^ (a - 1)| ≤ (1 + u) ^ a := by
    have heq : ∀ v ∈ Set.uIcc 0 u, |(a : ℝ) * v ^ (a - 1)| = (a : ℝ) * v ^ (a - 1) := by
      intro v hv
      rw [Set.uIcc_of_le hu] at hv
      exact abs_of_nonneg (mul_nonneg (Nat.cast_nonneg a) (pow_nonneg hv.1 _))
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_const_mul, integral_pow]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · have hsub : a - 1 + 1 = a := Nat.sub_add_cancel ha
      rw [hsub]
      simp only [zero_pow (Nat.pos_iff_ne_zero.mp ha), sub_zero]
      have ha' : (a : ℝ) - 1 + 1 = a := by ring
      have hcast : ((a - 1 : ℕ) : ℝ) + 1 = a := by
        rw [Nat.cast_sub ha]; push_cast; ring
      rw [hcast]
      have hane : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp ha)
      rw [mul_div_cancel₀ _ hane]
      exact pow_le_pow_left₀ hu (by linarith) a
  have hpos : 0 ≤ KM := KM_nonneg
  calc |(∑ n ∈ Ioc 0 ⌊Real.exp u⌋₊, Λ n / n * Real.log n ^ a) - u ^ (a + 1) / (a + 1)|
      ≤ KM * (|u ^ a| + ∫ v in (0:ℝ)..u, |(a : ℝ) * v ^ (a - 1)|) := h
    _ ≤ KM * ((1 + u) ^ a + (1 + u) ^ a) := by gcongr
    _ = 2 * KM * (1 + u) ^ a := by ring

/-- Σ_{n ≤ X, n not prime} Λ(n)(log n)^a/n ≤ 2·Cdef·(log X)^{a−1}... we only need the crude form with u:
for n ≤ e^u:  Σ_{n not prime} Λ n (log n)^{b-1}/n ≤ u^{b-2}·2Cdef  (b ≥ 2). -/
lemma sum_not_prime_lam_logpow_div_le (b : ℕ) (hb : 2 ≤ b) {u : ℝ} (hu : 0 ≤ u) :
    ∑ n ∈ (Ioc 0 ⌊Real.exp u⌋₊).filter (fun n => ¬ n.Prime), Λ n / n * Real.log n ^ (b - 1)
      ≤ u ^ (b - 2) * (2 * Cdef) := by
  have hX := fun n (hn : n ∈ Ioc 0 ⌊Real.exp u⌋₊) => log_le_of_mem_Ioc_floor_exp hn
  calc ∑ n ∈ (Ioc 0 ⌊Real.exp u⌋₊).filter (fun n => ¬ n.Prime), Λ n / n * Real.log n ^ (b - 1)
      ≤ ∑ n ∈ (Ioc 0 ⌊Real.exp u⌋₊).filter (fun n => ¬ n.Prime), u ^ (b - 2) * (2 * (Λ n * (Real.log n - Λ n) / n)) := by
        refine sum_le_sum fun n hn => ?_
        obtain ⟨hn', hnp⟩ := mem_filter.mp hn
        have hlog : Real.log n ≤ u := hX n hn'
        have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
        rcases eq_or_ne (Λ n) 0 with h0 | h0
        · simp [h0]
        · have h1 := (vonMangoldt_le_log_sub_of_not_prime h0 hnp).1
          have hΛ0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
          have hN0 : (0:ℝ) ≤ (n:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
          -- log^{b-1} n = log^{b-2} n · log n ≤ u^{b-2} · 2(log n − Λ n)
          have hsplit : Real.log n ^ (b - 1) = Real.log n ^ (b - 2) * Real.log n := by
            rw [← pow_succ]; congr 1; omega
          have hlog2 : Real.log n ≤ 2 * (Real.log n - Λ n) := by linarith
          calc Λ n / n * Real.log n ^ (b - 1)
              = (Λ n * (n:ℝ)⁻¹) * (Real.log n ^ (b - 2) * Real.log n) := by rw [hsplit, div_eq_mul_inv]
            _ ≤ (Λ n * (n:ℝ)⁻¹) * (u ^ (b - 2) * (2 * (Real.log n - Λ n))) := by
                refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hΛ0 hN0)
                exact mul_le_mul (pow_le_pow_left₀ hlog0 hlog _) hlog2 hlog0 (pow_nonneg hu _)
            _ = u ^ (b - 2) * (2 * (Λ n * (Real.log n - Λ n) / n)) := by ring
    _ = u ^ (b - 2) * (2 * ∑ n ∈ (Ioc 0 ⌊Real.exp u⌋₊).filter (fun n => ¬ n.Prime),
          Λ n * (Real.log n - Λ n) / n) := by rw [mul_sum, mul_sum]
    _ ≤ u ^ (b - 2) * (2 * Cdef) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hu _)
        refine mul_le_mul_of_nonneg_left ?_ zero_le_two
        calc ∑ n ∈ (Ioc 0 ⌊Real.exp u⌋₊).filter (fun n => ¬ n.Prime), Λ n * (Real.log n - Λ n) / n
            ≤ ∑ n ∈ Ioc 0 ⌊Real.exp u⌋₊, Λ n * (Real.log n - Λ n) / n :=
              sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n _ _ => defect_term_nonneg n
          _ ≤ Cdef := by simpa using defect_le (⌊Real.exp u⌋₊ : ℝ)

/-- the prime sum as "all n" minus "non-primes":  Σ_p log^b p/p = Σ_n Λ n log^{b−1} n/n − Σ_{n not prime} Λ n log^{b−1} n/n. -/
lemma sum_prime_logpow_eq (b : ℕ) (hb : 1 ≤ b) (X : ℕ) :
    ∑ p ∈ (Ioc 0 X).filter Nat.Prime, Real.log p ^ b / p
      = (∑ n ∈ Ioc 0 X, Λ n / n * Real.log n ^ (b - 1))
        - ∑ n ∈ (Ioc 0 X).filter (fun n => ¬ n.Prime), Λ n / n * Real.log n ^ (b - 1) := by
  rw [eq_sub_iff_add_eq, ← sum_filter_add_sum_filter_not (Ioc 0 X) Nat.Prime]
  congr 1
  refine sum_congr rfl fun p hp => ?_
  have hpp : p.Prime := (mem_filter.mp hp).2
  rw [ArithmeticFunction.vonMangoldt_apply_prime hpp, div_mul_eq_mul_div, ← pow_succ']
  congr 2; omega

/-- **Σ_{p ≤ e^u} (log p)^b/p = u^b/b + O((1+u)^{b−1})**  for b ≥ 2. -/
theorem prime_logpow_sum (b : ℕ) (hb : 2 ≤ b) : ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    |(∑ p ∈ (Ioc 0 ⌊Real.exp u⌋₊).filter Nat.Prime, Real.log p ^ b / p) - u ^ b / b|
      ≤ C * (1 + u) ^ (b - 1) := by
  refine ⟨2 * KM + 2 * Cdef, fun u hu => ?_⟩
  have hb1 : 1 ≤ b := by omega
  rw [sum_prime_logpow_eq b hb1]
  have hmain := mertens_monomial (b - 1) hu
  have hb' : b - 1 + 1 = b := Nat.sub_add_cancel hb1
  rw [hb'] at hmain
  have hcast : ((b - 1 : ℕ) : ℝ) + 1 = b := by rw [Nat.cast_sub hb1]; push_cast; ring
  rw [hcast] at hmain
  have hnp := sum_not_prime_lam_logpow_div_le b hb hu
  have hnp0 : 0 ≤ ∑ n ∈ (Ioc 0 ⌊Real.exp u⌋₊).filter (fun n => ¬ n.Prime), Λ n / n * Real.log n ^ (b - 1) :=
    sum_nonneg fun n _ => mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n))
      (pow_nonneg (Real.log_natCast_nonneg n) _)
  have hu1 : u ^ (b - 2) ≤ (1 + u) ^ (b - 1) := by
    calc u ^ (b - 2) ≤ (1 + u) ^ (b - 2) := pow_le_pow_left₀ hu (by linarith) _
      _ ≤ (1 + u) ^ (b - 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have hCdef : (0:ℝ) ≤ Cdef := by unfold Cdef; norm_num
  rw [abs_le] at hmain ⊢
  constructor
  · nlinarith [hmain.1, hnp, hu1, KM_nonneg, pow_nonneg (by linarith : (0:ℝ) ≤ 1 + u) (b - 1)]
  · nlinarith [hmain.2, hnp0, hu1, KM_nonneg, pow_nonneg (by linarith : (0:ℝ) ≤ 1 + u) (b - 1)]

end XiPrime
end Zeta23
