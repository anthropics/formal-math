/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Coeff/NonSquarefree.lean — "each repeated prime costs a factor 1/l"  [XF′ Lemma 7.1 (ii)].

For each fixed m:  Σ_{N ≤ e^u, N not squarefree} Λ^{∗m}(N)/N ≤ C_m·(u + mK + 1)^{m−1}   — one power of u less than
the full sum Σ_{N≤e^u}Λ^{∗m}(N)/N ≍ u^m/m! (Coeff/PowerSums).  Route: a PREDICATED version of the swap recursion,
  Σ_{N≤X, P N}(g∗f)(N)/N ≤ Σ_{d≤X, Q d} g(d)/d·Sdiv f(·) + Σ_{d≤X} g(d)/d·Σ_{e, R d e} f(e)/e    whenever P(de) ⇒ Q d ∨ R d e,
applied with P = ¬Squarefree:  de not squarefree ⇒ d not prime ∨ e not squarefree ∨ (d prime ∧ d ∣ e), and with
P = (p ∣ ·).  The only arithmetic input beyond Mertens is the tree's proper-prime-power defect bound
Cheb.defect_bounded_explicit:  Σ_{n≤x} Λ(n)(log n − Λ(n))/n ≤ 1537, which dominates Σ_{n not prime}Λ(n)/n,
Σ_{n not sqfree}Λ(n)²/n, Σ_{n not sqfree}Λ(n)log n/n and Σ_p log²p/p².
-/
import Zeta23.XiPrime.Coeff.PowerSums

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Omega
open Finset Real

noncomputable section

namespace Zeta23
namespace XiPrime

/-! ### predicated sums and the predicated recursion -/

/-- Σ_{N ≤ e^u, P N} f(N)/N. -/
def SdivP (f : ArithmeticFunction ℝ) (P : ℕ → Prop) [DecidablePred P] (u : ℝ) : ℝ :=
  ∑ N ∈ (Ioc 0 ⌊Real.exp u⌋₊).filter P, f N / N

lemma SdivP_nonneg {f : ArithmeticFunction ℝ} (hf : ∀ n, 0 ≤ f n) (P : ℕ → Prop) [DecidablePred P]
    (u : ℝ) : 0 ≤ SdivP f P u :=
  sum_nonneg fun N _ => div_nonneg (hf N) (Nat.cast_nonneg N)

lemma SdivP_le_Sdiv {f : ArithmeticFunction ℝ} (hf : ∀ n, 0 ≤ f n) (P : ℕ → Prop) [DecidablePred P]
    (u : ℝ) : SdivP f P u ≤ Sdiv f u :=
  sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun N _ _ => div_nonneg (hf N) (Nat.cast_nonneg N)

lemma SdivP_mono_pred {f : ArithmeticFunction ℝ} (hf : ∀ n, 0 ≤ f n) {P Q : ℕ → Prop} [DecidablePred P]
    [DecidablePred Q] (hPQ : ∀ n, P n → Q n) (u : ℝ) : SdivP f P u ≤ SdivP f Q u :=
  sum_le_sum_of_subset_of_nonneg (fun N hN => by
      rw [mem_filter] at hN ⊢; exact ⟨hN.1, hPQ N hN.2⟩)
    fun N _ _ => div_nonneg (hf N) (Nat.cast_nonneg N)

lemma SdivP_or_le {f : ArithmeticFunction ℝ} (hf : ∀ n, 0 ≤ f n) (P Q : ℕ → Prop) [DecidablePred P]
    [DecidablePred Q] (u : ℝ) : SdivP f (fun n => P n ∨ Q n) u ≤ SdivP f P u + SdivP f Q u := by
  unfold SdivP
  rw [filter_or]
  have h := sum_union_inter (s₁ := (Ioc 0 ⌊Real.exp u⌋₊).filter P)
    (s₂ := (Ioc 0 ⌊Real.exp u⌋₊).filter Q) (f := fun N => f N / (N:ℝ))
  have h0 : 0 ≤ ∑ N ∈ (Ioc 0 ⌊Real.exp u⌋₊).filter P ∩ (Ioc 0 ⌊Real.exp u⌋₊).filter Q, f N / N :=
    sum_nonneg fun N _ => div_nonneg (hf N) (Nat.cast_nonneg N)
  linarith

lemma SdivP_mono_u {f : ArithmeticFunction ℝ} (hf : ∀ n, 0 ≤ f n) (P : ℕ → Prop) [DecidablePred P] :
    Monotone (SdivP f P) := by
  intro a b hab
  refine sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (Ioc_subset_Ioc le_rfl ?_)) ?_
  · exact Nat.floor_le_floor (Real.exp_le_exp.mpr hab)
  · exact fun N _ _ => div_nonneg (hf N) (Nat.cast_nonneg N)

/-- SdivP as an unrestricted sum with an indicator. -/
lemma SdivP_eq_sum_ite (f : ArithmeticFunction ℝ) (P : ℕ → Prop) [DecidablePred P] (u : ℝ) :
    SdivP f P u = ∑ N ∈ Ioc 0 ⌊Real.exp u⌋₊, f N * (if P N then ((N:ℕ):ℝ)⁻¹ else 0) := by
  unfold SdivP
  rw [sum_filter]
  refine sum_congr rfl fun N _ => ?_
  split_ifs <;> simp [div_eq_mul_inv]

/-- **the predicated recursion.**  If P(de) (with g d ≠ 0 ≠ f e) forces Q d ∨ R d e, then
  Σ_{N≤e^u, P N}(g∗f)(N)/N ≤ Σ_{d ≤ e^u, Q d} g(d)/d · Sdiv f (u − log d) + Σ_{d ≤ e^u} g(d)/d · SdivP f (R d) (u − log d). -/
theorem SdivP_mul_le {g f : ArithmeticFunction ℝ} (hg : ∀ n, 0 ≤ g n) (hf : ∀ n, 0 ≤ f n)
    (P Q : ℕ → Prop) (R : ℕ → ℕ → Prop) [DecidablePred P] [DecidablePred Q] [∀ d, DecidablePred (R d)]
    (hsplit : ∀ d e, g d ≠ 0 → f e ≠ 0 → P (d * e) → Q d ∨ R d e) (u : ℝ) :
    SdivP (g * f) P u ≤
      (∑ d ∈ (Ioc 0 ⌊Real.exp u⌋₊).filter Q, g d / d * Sdiv f (u - Real.log d))
      + ∑ d ∈ Ioc 0 ⌊Real.exp u⌋₊, g d / d * SdivP f (R d) (u - Real.log d) := by
  set X : ℕ := ⌊Real.exp u⌋₊ with hX
  rw [SdivP_eq_sum_ite, sum_Ioc_mul_apply g f (fun N => if P N then ((N:ℕ):ℝ)⁻¹ else 0) X]
  -- termwise bound inside the double sum
  have hterm : ∀ d ∈ Ioc 0 X, ∀ e ∈ Ioc 0 (X / d),
      g d * (f e * (if P (d * e) then (((d * e : ℕ)) : ℝ)⁻¹ else 0))
        ≤ g d * (f e * ((((d * e : ℕ)) : ℝ)⁻¹ * (if Q d then 1 else 0)))
          + g d * (f e * ((((d * e : ℕ)) : ℝ)⁻¹ * (if R d e then 1 else 0))) := by
    intro d _ e _
    have hde : (0:ℝ) ≤ (((d * e : ℕ)) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    have hA : 0 ≤ g d * (f e * ((((d * e : ℕ)) : ℝ)⁻¹ * (if Q d then 1 else 0))) :=
      mul_nonneg (hg d) (mul_nonneg (hf e) (mul_nonneg hde (by split_ifs <;> norm_num)))
    have hB : 0 ≤ g d * (f e * ((((d * e : ℕ)) : ℝ)⁻¹ * (if R d e then 1 else 0))) :=
      mul_nonneg (hg d) (mul_nonneg (hf e) (mul_nonneg hde (by split_ifs <;> norm_num)))
    by_cases hP : P (d * e)
    · rw [if_pos hP]
      rcases eq_or_ne (g d) 0 with hg0 | hg0
      · rw [hg0]; simp
      rcases eq_or_ne (f e) 0 with hf0 | hf0
      · rw [hf0]; simp
      rcases hsplit d e hg0 hf0 hP with hQ | hR
      · rw [if_pos hQ, mul_one]; linarith
      · rw [if_pos hR, mul_one]; linarith
    · rw [if_neg hP, mul_zero, mul_zero]; linarith
  calc ∑ d ∈ Ioc 0 X, g d * ∑ e ∈ Ioc 0 (X / d), f e * (if P (d * e) then (((d * e : ℕ)) : ℝ)⁻¹ else 0)
      ≤ ∑ d ∈ Ioc 0 X, ∑ e ∈ Ioc 0 (X / d),
          (g d * (f e * ((((d * e : ℕ)) : ℝ)⁻¹ * (if Q d then 1 else 0)))
            + g d * (f e * ((((d * e : ℕ)) : ℝ)⁻¹ * (if R d e then 1 else 0)))) := by
        refine sum_le_sum fun d hd => ?_
        rw [mul_sum]
        exact sum_le_sum fun e he => hterm d hd e he
    _ = (∑ d ∈ Ioc 0 X, ∑ e ∈ Ioc 0 (X / d), g d * (f e * ((((d * e : ℕ)) : ℝ)⁻¹ * (if Q d then 1 else 0))))
        + ∑ d ∈ Ioc 0 X, ∑ e ∈ Ioc 0 (X / d), g d * (f e * ((((d * e : ℕ)) : ℝ)⁻¹ * (if R d e then 1 else 0))) := by
        rw [← sum_add_distrib]; exact sum_congr rfl fun d _ => sum_add_distrib
    _ = (∑ d ∈ (Ioc 0 X).filter Q, g d / d * Sdiv f (u - Real.log d))
        + ∑ d ∈ Ioc 0 X, g d / d * SdivP f (R d) (u - Real.log d) := by
        congr 1
        · rw [sum_filter]
          refine sum_congr rfl fun d hd => ?_
          have hd0 : 0 < d := (mem_Ioc.mp hd).1
          split_ifs with hQ
          · unfold Sdiv
            rw [← floor_exp_div u hd0, ← hX, mul_sum]
            refine sum_congr rfl fun e _ => ?_
            rw [Nat.cast_mul, mul_inv]; ring
          · simp
        · refine sum_congr rfl fun d hd => ?_
          have hd0 : 0 < d := (mem_Ioc.mp hd).1
          rw [SdivP_eq_sum_ite, ← floor_exp_div u hd0, ← hX, mul_sum]
          refine sum_congr rfl fun e _ => ?_
          split_ifs
          · rw [Nat.cast_mul, mul_inv]; ring
          · simp

/-! ### the arithmetic inputs: proper prime powers are sparse -/

/-- the defect constant. -/
def Cdef : ℝ := 1537

lemma defect_le (x : ℝ) : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (Real.log n - Λ n) / n ≤ Cdef :=
  Cheb.defect_bounded_explicit x

lemma defect_term_nonneg (n : ℕ) : 0 ≤ Λ n * (Real.log n - Λ n) / n :=
  div_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (sub_nonneg.mpr ArithmeticFunction.vonMangoldt_le_log)) (Nat.cast_nonneg n)

/-- structure of n with Λ n ≠ 0: n = p^k, p prime, k ≥ 1, Λ n = log p, log n = k log p. -/
lemma exists_prime_pow_of_vonMangoldt_ne_zero {n : ℕ} (h : Λ n ≠ 0) :
    ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ p ^ k = n ∧ Λ n = Real.log p ∧ Real.log n = k * Real.log p := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h)
  refine ⟨p, k, hp, hk, rfl, ?_, ?_⟩
  · rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.pos_iff_ne_zero.mp hk),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  · push_cast; rw [Real.log_pow]

/-- if Λ n ≠ 0 and n is not prime, then log n − Λ n ≥ Λ n ≥ log 2  (n = p^k with k ≥ 2). -/
lemma vonMangoldt_le_log_sub_of_not_prime {n : ℕ} (h : Λ n ≠ 0) (hn : ¬ n.Prime) :
    Λ n ≤ Real.log n - Λ n ∧ Real.log 2 ≤ Λ n := by
  obtain ⟨p, k, hp, hk, hpk, hΛ, hlog⟩ := exists_prime_pow_of_vonMangoldt_ne_zero h
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have : k = 1 := by omega
    subst this; rw [pow_one] at hpk; exact hn (hpk ▸ hp)
  have hlogp : Real.log 2 ≤ Real.log p :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  have hlogp0 : 0 ≤ Real.log p := le_trans (Real.log_nonneg (by norm_num)) hlogp
  refine ⟨?_, hΛ ▸ hlogp⟩
  rw [hΛ, hlog]
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk2
  nlinarith

/-- a non-squarefree n with Λ n ≠ 0 is not prime. -/
lemma not_prime_of_not_squarefree {n : ℕ} (hn : ¬ Squarefree n) : ¬ n.Prime :=
  fun hp => hn hp.prime.squarefree

/-- Σ_{n ≤ x, n not prime} Λ(n)/n ≤ Cdef / log 2. -/
lemma sum_not_prime_vonMangoldt_div_le (X : ℕ) :
    ∑ n ∈ (Ioc 0 X).filter (fun n => ¬ n.Prime), Λ n / n ≤ Cdef / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2, sum_mul]
  calc ∑ n ∈ (Ioc 0 X).filter (fun n => ¬ n.Prime), Λ n / n * Real.log 2
      ≤ ∑ n ∈ (Ioc 0 X).filter (fun n => ¬ n.Prime), Λ n * (Real.log n - Λ n) / n := by
        refine sum_le_sum fun n hn => ?_
        have hnp : ¬ n.Prime := (mem_filter.mp hn).2
        rcases eq_or_ne (Λ n) 0 with h0 | h0
        · simp [h0]
        · obtain ⟨h1, h2⟩ := vonMangoldt_le_log_sub_of_not_prime h0 hnp
          rw [div_mul_eq_mul_div]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (h2.trans h1)
            ArithmeticFunction.vonMangoldt_nonneg) (Nat.cast_nonneg n)
    _ ≤ ∑ n ∈ Ioc 0 X, Λ n * (Real.log n - Λ n) / n :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n _ _ => defect_term_nonneg n
    _ ≤ Cdef := by simpa using defect_le (X : ℝ)

/-- Σ_{n ≤ x, n not squarefree} Λ(n)²/n ≤ Cdef. -/
lemma sum_not_squarefree_vonMangoldt_sq_div_le (X : ℕ) :
    ∑ n ∈ (Ioc 0 X).filter (fun n => ¬ Squarefree n), Λ n ^ 2 / n ≤ Cdef := by
  calc ∑ n ∈ (Ioc 0 X).filter (fun n => ¬ Squarefree n), Λ n ^ 2 / n
      ≤ ∑ n ∈ (Ioc 0 X).filter (fun n => ¬ Squarefree n), Λ n * (Real.log n - Λ n) / n := by
        refine sum_le_sum fun n hn => ?_
        have hns : ¬ Squarefree n := (mem_filter.mp hn).2
        rcases eq_or_ne (Λ n) 0 with h0 | h0
        · simp [h0]
        · have h1 := (vonMangoldt_le_log_sub_of_not_prime h0 (not_prime_of_not_squarefree hns)).1
          rw [sq]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1
            ArithmeticFunction.vonMangoldt_nonneg) (Nat.cast_nonneg n)
    _ ≤ ∑ n ∈ Ioc 0 X, Λ n * (Real.log n - Λ n) / n :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n _ _ => defect_term_nonneg n
    _ ≤ Cdef := by simpa using defect_le (X : ℝ)

/-- Σ_{n ≤ x, n not squarefree} Λ(n) log n/n ≤ 2·Cdef. -/
lemma sum_not_squarefree_lamLog_div_le (X : ℕ) :
    ∑ n ∈ (Ioc 0 X).filter (fun n => ¬ Squarefree n), Λ n * Real.log n / n ≤ 2 * Cdef := by
  calc ∑ n ∈ (Ioc 0 X).filter (fun n => ¬ Squarefree n), Λ n * Real.log n / n
      ≤ ∑ n ∈ (Ioc 0 X).filter (fun n => ¬ Squarefree n), 2 * (Λ n * (Real.log n - Λ n) / n) := by
        refine sum_le_sum fun n hn => ?_
        have hns : ¬ Squarefree n := (mem_filter.mp hn).2
        rcases eq_or_ne (Λ n) 0 with h0 | h0
        · simp [h0]
        · have h1 := (vonMangoldt_le_log_sub_of_not_prime h0 (not_prime_of_not_squarefree hns)).1
          -- log n ≤ 2 (log n − Λ n)
          have : Λ n * Real.log n ≤ 2 * (Λ n * (Real.log n - Λ n)) := by
            nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)]
          calc Λ n * Real.log n / n = (Λ n * Real.log n) / n := by ring
            _ ≤ (2 * (Λ n * (Real.log n - Λ n))) / n := div_le_div_of_nonneg_right this (Nat.cast_nonneg n)
            _ = 2 * (Λ n * (Real.log n - Λ n) / n) := by ring
    _ = 2 * ∑ n ∈ (Ioc 0 X).filter (fun n => ¬ Squarefree n), Λ n * (Real.log n - Λ n) / n := by
        rw [mul_sum]
    _ ≤ 2 * ∑ n ∈ Ioc 0 X, Λ n * (Real.log n - Λ n) / n :=
        mul_le_mul_of_nonneg_left
          (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n _ _ => defect_term_nonneg n) zero_le_two
    _ ≤ 2 * Cdef := by have := defect_le (X : ℝ); simp at this; linarith

/-- Σ_{p ≤ X prime} log²p/p² ≤ Cdef  (the a = 2 slice of the defect sum at X²). -/
lemma sum_prime_log_sq_div_sq_le (X : ℕ) :
    ∑ p ∈ (Ioc 0 X).filter Nat.Prime, Real.log p ^ 2 / (p:ℝ) ^ 2 ≤ Cdef := by
  have hinj : Set.InjOn (fun p : ℕ => p ^ 2) ((Ioc 0 X).filter Nat.Prime : Set ℕ) :=
    fun a _ b _ h => by simpa using (Nat.pow_left_injective two_ne_zero) h
  calc ∑ p ∈ (Ioc 0 X).filter Nat.Prime, Real.log p ^ 2 / (p:ℝ) ^ 2
      = ∑ n ∈ ((Ioc 0 X).filter Nat.Prime).image (fun p => p ^ 2), Λ n * (Real.log n - Λ n) / n := by
        rw [sum_image hinj]
        refine sum_congr rfl fun p hp => ?_
        have hpp : p.Prime := (mem_filter.mp hp).2
        rw [ArithmeticFunction.vonMangoldt_apply_pow two_ne_zero,
          ArithmeticFunction.vonMangoldt_apply_prime hpp]
        push_cast
        rw [Real.log_pow]; ring
    _ ≤ ∑ n ∈ Ioc 0 (X ^ 2), Λ n * (Real.log n - Λ n) / n := by
        refine sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => defect_term_nonneg n
        intro n hn
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hn
        have hp' := mem_Ioc.mp (mem_filter.mp hp).1
        exact mem_Ioc.mpr ⟨pow_pos hp'.1 2, Nat.pow_le_pow_left hp'.2 2⟩
    _ ≤ Cdef := by simpa using defect_le ((X ^ 2 : ℕ) : ℝ)

/-- Σ_{d ≤ X, p ∣ d} Λ(d)/d ≤ 2 log p / p  for p prime (d ranges over the powers of p). -/
lemma sum_dvd_vonMangoldt_div_le {p : ℕ} (hp : p.Prime) (X : ℕ) :
    ∑ d ∈ (Ioc 0 X).filter (fun d => p ∣ d), Λ d / d ≤ 2 * Real.log p / p := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ) < p := by linarith
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  -- restrict to the support and re-index by d = p^(a+1), a < X
  have hsupp : ∑ d ∈ (Ioc 0 X).filter (fun d => p ∣ d), Λ d / d
      = ∑ d ∈ ((Ioc 0 X).filter (fun d => p ∣ d)).filter (fun d => Λ d ≠ 0), Λ d / d := by
    refine (sum_filter_of_ne fun d _ h => ?_).symm
    intro h0
    exact h (by rw [h0, zero_div])
  have hsub : ((Ioc 0 X).filter (fun d => p ∣ d)).filter (fun d => Λ d ≠ 0)
      ⊆ (range X).image (fun a => p ^ (a + 1)) := by
    intro d hd
    simp only [mem_filter, mem_Ioc] at hd
    obtain ⟨⟨⟨hd0, hdX⟩, hpd⟩, hΛ⟩ := hd
    obtain ⟨q, k, hq, hk, hqk, -, -⟩ := exists_prime_pow_of_vonMangoldt_ne_zero hΛ
    have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow (hqk ▸ hpd))
    subst hpq
    refine mem_image.mpr ⟨k - 1, mem_range.mpr ?_, ?_⟩
    · have : k < p ^ k := Nat.lt_pow_self hp.one_lt
      omega
    · rw [Nat.sub_add_cancel hk, hqk]
  calc ∑ d ∈ (Ioc 0 X).filter (fun d => p ∣ d), Λ d / d
      = ∑ d ∈ ((Ioc 0 X).filter (fun d => p ∣ d)).filter (fun d => Λ d ≠ 0), Λ d / d := hsupp
    _ ≤ ∑ d ∈ (range X).image (fun a => p ^ (a + 1)), Λ d / d :=
        sum_le_sum_of_subset_of_nonneg hsub fun d _ _ =>
          div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d)
    _ ≤ ∑ a ∈ range X, Λ (p ^ (a + 1)) / ((p ^ (a + 1) : ℕ) : ℝ) :=
        sum_image_le_of_nonneg fun a _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
    _ = ∑ a ∈ range X, Real.log p / p * (1 / p) ^ a := by
        refine sum_congr rfl fun a _ => ?_
        rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero a),
          ArithmeticFunction.vonMangoldt_apply_prime hp]
        have hcast : ((p ^ (a + 1) : ℕ) : ℝ) = (p : ℝ) * (p : ℝ) ^ a := by push_cast; ring
        rw [hcast, one_div, inv_pow]
        field_simp
    _ = Real.log p / p * ∑ a ∈ range X, (1 / p : ℝ) ^ a := by rw [mul_sum]
    _ ≤ Real.log p / p * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hlogp hp0.le)
        calc ∑ a ∈ range X, (1 / p : ℝ) ^ a ≤ ∑ a ∈ range X, (1 / 2 : ℝ) ^ a := by
              refine sum_le_sum fun a _ => pow_le_pow_left₀ (by positivity) ?_ a
              exact one_div_le_one_div_of_le (by norm_num) hp2
          _ ≤ 2 := sum_geometric_two_le X
    _ = 2 * Real.log p / p := by ring

/-! ### sums over multiples of a prime:  D m p u := Σ_{N ≤ e^u, p ∣ N} Λ^{∗m}(N)/N -/

/-- Σ_{N≤e^u, p∣N} Λ^{∗m}(N)/N. -/
def Dsum (m p : ℕ) (u : ℝ) : ℝ := SdivP (Λ ^ m) (fun N => p ∣ N) u

lemma Dsum_zero {p : ℕ} (hp : p.Prime) (u : ℝ) : Dsum 0 p u = 0 := by
  unfold Dsum SdivP
  refine sum_eq_zero fun N hN => ?_
  have hpN : p ∣ N := (mem_filter.mp hN).2
  rw [pow_zero, ArithmeticFunction.one_apply]
  split_ifs with h1
  · subst h1; exact absurd (Nat.eq_one_of_dvd_one hpN ▸ hp) Nat.not_prime_one
  · simp

/-- the bracket G := u + (m+1)K + 1 used in all the inductions (≥ 1, ≥ u + K, monotone in m and u). -/
def Gb (m : ℕ) (u : ℝ) : ℝ := u + (m + 1) * KM + 1

lemma Gb_ge_one {m : ℕ} {u : ℝ} (hu : 0 ≤ u) : 1 ≤ Gb m u := by
  unfold Gb; nlinarith [KM_nonneg, (by positivity : (0:ℝ) ≤ (m:ℝ) + 1)]

lemma Gb_nonneg {m : ℕ} {u : ℝ} (hu : 0 ≤ u) : 0 ≤ Gb m u := (zero_le_one.trans (Gb_ge_one hu))

lemma Gb_mono_u (m : ℕ) : Monotone (Gb m) := fun a b h => by unfold Gb; linarith

lemma Gb_succ (m : ℕ) (u : ℝ) : Gb (m + 1) u = Gb m u + KM := by unfold Gb; push_cast; ring

lemma u_add_KM_le_Gb (m : ℕ) (u : ℝ) : u + KM ≤ Gb m u := by
  unfold Gb; nlinarith [KM_nonneg, (Nat.cast_nonneg m : (0:ℝ) ≤ m)]

lemma pow_bound_le_Gb_pow {m : ℕ} {u : ℝ} (hu : 0 ≤ u) :
    (u + m * KM) ^ m / m.factorial ≤ Gb m u ^ m := by
  have h1 : (u + m * KM) ^ m / m.factorial ≤ (u + m * KM) ^ m :=
    div_le_self (pow_nonneg (by nlinarith [KM_nonneg, (Nat.cast_nonneg m : (0:ℝ) ≤ m)]) m)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m))
  refine h1.trans (pow_le_pow_left₀ (by nlinarith [KM_nonneg, (Nat.cast_nonneg m : (0:ℝ) ≤ m)]) ?_ m)
  unfold Gb; nlinarith [KM_nonneg]

/-- **D_{m+1}(p,u) ≤ (m+1)·(2 log p/p)·Gb m u ^ m.** -/
theorem Dsum_le {p : ℕ} (hp : p.Prime) : ∀ (m : ℕ) {u : ℝ}, 0 ≤ u →
    Dsum (m + 1) p u ≤ (m + 1) * (2 * Real.log p / p) * Gb m u ^ m := by
  have hlp : 0 ≤ 2 * Real.log p / p :=
    div_nonneg (mul_nonneg zero_le_two (Real.log_natCast_nonneg p)) (Nat.cast_nonneg p)
  intro m
  induction m with
  | zero =>
      intro u hu
      -- D_1 = Σ_{d: p|d} Λ d/d ≤ 2 log p/p
      unfold Dsum
      rw [pow_one]
      have := sum_dvd_vonMangoldt_div_le hp ⌊Real.exp u⌋₊
      unfold SdivP
      simpa using this
  | succ m ih =>
      intro u hu
      have hrec := SdivP_mul_le (g := Λ) (f := Λ ^ (m + 1)) vonMangoldt_nonneg' (lamPow_nonneg (m + 1))
        (fun N => p ∣ N) (fun d => p ∣ d) (fun _ e => p ∣ e)
        (fun d e _ _ h => (Nat.Prime.dvd_mul hp).mp h) u
      rw [← pow_succ'] at hrec
      unfold Dsum
      refine hrec.trans ?_
      -- first sum ≤ (2 log p/p)·Gb m u ^ (m+1)... we bound Sdiv (Λ^(m+1)) (u - log d) ≤ Gb (m+1) u ^ (m+1)
      have hG0 : 0 ≤ Gb (m + 1) u := Gb_nonneg hu
      have h1 : ∑ d ∈ (Ioc 0 ⌊Real.exp u⌋₊).filter (fun d => p ∣ d), Λ d / d * Sdiv (Λ ^ (m + 1)) (u - Real.log d)
          ≤ (2 * Real.log p / p) * Gb (m + 1) u ^ (m + 1) := by
        calc ∑ d ∈ (Ioc 0 ⌊Real.exp u⌋₊).filter (fun d => p ∣ d), Λ d / d * Sdiv (Λ ^ (m + 1)) (u - Real.log d)
            ≤ ∑ d ∈ (Ioc 0 ⌊Real.exp u⌋₊).filter (fun d => p ∣ d), Λ d / d * Gb (m + 1) u ^ (m + 1) := by
              refine sum_le_sum fun d hd => ?_
              have hd' := (mem_filter.mp hd).1
              have hlog : Real.log d ≤ u := log_le_of_mem_Ioc_floor_exp hd'
              have hlog0 : 0 ≤ Real.log d := Real.log_natCast_nonneg d
              refine mul_le_mul_of_nonneg_left ?_ (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d))
              refine (Sdiv_lamPow_le (m + 1) (by linarith)).trans ?_
              refine (pow_bound_le_Gb_pow (by linarith)).trans ?_
              exact pow_le_pow_left₀ (Gb_nonneg (by linarith)) (Gb_mono_u _ (by linarith)) _
          _ = (∑ d ∈ (Ioc 0 ⌊Real.exp u⌋₊).filter (fun d => p ∣ d), Λ d / d) * Gb (m + 1) u ^ (m + 1) := by
              rw [sum_mul]
          _ ≤ (2 * Real.log p / p) * Gb (m + 1) u ^ (m + 1) :=
              mul_le_mul_of_nonneg_right (sum_dvd_vonMangoldt_div_le hp _) (pow_nonneg hG0 _)
      have h2 : ∑ d ∈ Ioc 0 ⌊Real.exp u⌋₊, Λ d / d * SdivP (Λ ^ (m + 1)) (fun e => p ∣ e) (u - Real.log d)
          ≤ (u + KM) * ((m + 1) * (2 * Real.log p / p) * Gb (m + 1) u ^ m) := by
        calc ∑ d ∈ Ioc 0 ⌊Real.exp u⌋₊, Λ d / d * SdivP (Λ ^ (m + 1)) (fun e => p ∣ e) (u - Real.log d)
            ≤ ∑ d ∈ Ioc 0 ⌊Real.exp u⌋₊, Λ d / d * ((m + 1) * (2 * Real.log p / p) * Gb (m + 1) u ^ m) := by
              refine sum_le_sum fun d hd => ?_
              have hlog : Real.log d ≤ u := log_le_of_mem_Ioc_floor_exp hd
              have hlog0 : 0 ≤ Real.log d := Real.log_natCast_nonneg d
              refine mul_le_mul_of_nonneg_left ?_ (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d))
              have ih' := ih (u := u - Real.log d) (by linarith)
              unfold Dsum at ih'
              refine ih'.trans ?_
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) hlp)
              exact pow_le_pow_left₀ (Gb_nonneg (by linarith))
                ((Gb_mono_u m (by linarith : u - Real.log d ≤ u)).trans (by rw [Gb_succ]; linarith [KM_nonneg])) m
          _ = Sdiv Λ u * ((m + 1) * (2 * Real.log p / p) * Gb (m + 1) u ^ m) := by
              rw [← sum_mul]; rfl
          _ ≤ (u + KM) * ((m + 1) * (2 * Real.log p / p) * Gb (m + 1) u ^ m) :=
              mul_le_mul_of_nonneg_right (Sdiv_lam_le hu)
                (mul_nonneg (mul_nonneg (by positivity) hlp) (pow_nonneg hG0 m))
      have hGK : u + KM ≤ Gb (m + 1) u := u_add_KM_le_Gb _ _
      calc _ ≤ (2 * Real.log p / p) * Gb (m + 1) u ^ (m + 1)
            + (u + KM) * ((m + 1) * (2 * Real.log p / p) * Gb (m + 1) u ^ m) := add_le_add h1 h2
        _ ≤ (2 * Real.log p / p) * Gb (m + 1) u ^ (m + 1)
            + Gb (m + 1) u * ((m + 1) * (2 * Real.log p / p) * Gb (m + 1) u ^ m) := by
            gcongr
        _ = (↑(m + 1) + 1) * (2 * Real.log p / p) * Gb (m + 1) u ^ (m + 1) := by push_cast; ring

/-! ### the non-squarefree sums:  Nsf m u := Σ_{N ≤ e^u, N not squarefree} Λ^{∗m}(N)/N -/

/-- Σ_{N≤e^u, ¬Squarefree N} Λ^{∗m}(N)/N. -/
def Nsf (m : ℕ) (u : ℝ) : ℝ := SdivP (Λ ^ m) (fun N => ¬ Squarefree N) u

lemma Nsf_nonneg (m : ℕ) (u : ℝ) : 0 ≤ Nsf m u := SdivP_nonneg (lamPow_nonneg m) _ u

/-- the splitting: d·e not squarefree, Λ d ≠ 0 ⇒ d not prime ∨ e not squarefree ∨ (d prime ∧ d ∣ e). -/
lemma split_not_squarefree (d e : ℕ) (_hd : Λ d ≠ 0) (h : ¬ Squarefree (d * e)) :
    ¬ d.Prime ∨ (¬ Squarefree e ∨ (d.Prime ∧ d ∣ e)) := by
  by_cases hp : d.Prime
  · right
    by_cases he : Squarefree e
    · right
      refine ⟨hp, ?_⟩
      by_contra hnd
      have hcop : d.Coprime e := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd
      exact h ((Nat.squarefree_mul hcop).mpr ⟨hp.prime.squarefree, he⟩)
    · left; exact he
  · left; exact hp

/-- **Nsf (m+1) u ≤ C_m · Gb m u ^ m**, with an (inexplicit) constant depending on m only. -/
theorem Nsf_le : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → Nsf (m + 1) u ≤ C * Gb m u ^ m
  | 0 => by
      refine ⟨Cdef / Real.log 2, div_nonneg (by unfold Cdef; norm_num) (Real.log_nonneg (by norm_num)), fun u hu => ?_⟩
      unfold Nsf SdivP
      rw [pow_one, pow_zero, mul_one]
      calc ∑ N ∈ (Ioc 0 ⌊Real.exp u⌋₊).filter (fun N => ¬ Squarefree N), Λ N / N
          ≤ ∑ N ∈ (Ioc 0 ⌊Real.exp u⌋₊).filter (fun N => ¬ N.Prime), Λ N / N :=
            sum_le_sum_of_subset_of_nonneg
              (fun N hN => by
                rw [mem_filter] at hN ⊢
                exact ⟨hN.1, not_prime_of_not_squarefree hN.2⟩)
              fun N _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg N)
        _ ≤ Cdef / Real.log 2 := sum_not_prime_vonMangoldt_div_le _
  | m + 1 => by
      obtain ⟨C, hC0, hC⟩ := Nsf_le m
      refine ⟨Cdef / Real.log 2 + C + 2 * (m + 1) * Cdef, by
        have : 0 ≤ Cdef / Real.log 2 := div_nonneg (by unfold Cdef; norm_num) (Real.log_nonneg (by norm_num))
        have : (0:ℝ) ≤ Cdef := by unfold Cdef; norm_num
        positivity, fun u hu => ?_⟩
      have hG0 : 0 ≤ Gb (m + 1) u := Gb_nonneg hu
      have hG1 : 1 ≤ Gb (m + 1) u := Gb_ge_one hu
      have hrec := SdivP_mul_le (g := Λ) (f := Λ ^ (m + 1)) vonMangoldt_nonneg' (lamPow_nonneg (m + 1))
        (fun N => ¬ Squarefree N) (fun d => ¬ d.Prime) (fun d e => ¬ Squarefree e ∨ (d.Prime ∧ d ∣ e))
        (fun d e hd _ h => split_not_squarefree d e hd h) u
      rw [← pow_succ'] at hrec
      unfold Nsf
      refine hrec.trans ?_
      -- (a) the non-prime d's
      have ha : ∑ d ∈ (Ioc 0 ⌊Real.exp u⌋₊).filter (fun d => ¬ d.Prime), Λ d / d * Sdiv (Λ ^ (m + 1)) (u - Real.log d)
          ≤ Cdef / Real.log 2 * Gb (m + 1) u ^ (m + 1) := by
        calc ∑ d ∈ (Ioc 0 ⌊Real.exp u⌋₊).filter (fun d => ¬ d.Prime), Λ d / d * Sdiv (Λ ^ (m + 1)) (u - Real.log d)
            ≤ ∑ d ∈ (Ioc 0 ⌊Real.exp u⌋₊).filter (fun d => ¬ d.Prime), Λ d / d * Gb (m + 1) u ^ (m + 1) := by
              refine sum_le_sum fun d hd => ?_
              have hd' := (mem_filter.mp hd).1
              have hlog : Real.log d ≤ u := log_le_of_mem_Ioc_floor_exp hd'
              have hlog0 : 0 ≤ Real.log d := Real.log_natCast_nonneg d
              refine mul_le_mul_of_nonneg_left ?_ (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d))
              refine (Sdiv_lamPow_le (m + 1) (by linarith)).trans ?_
              refine (pow_bound_le_Gb_pow (by linarith)).trans ?_
              exact pow_le_pow_left₀ (Gb_nonneg (by linarith)) (Gb_mono_u _ (by linarith)) _
          _ = (∑ d ∈ (Ioc 0 ⌊Real.exp u⌋₊).filter (fun d => ¬ d.Prime), Λ d / d) * Gb (m + 1) u ^ (m + 1) := by
              rw [sum_mul]
          _ ≤ Cdef / Real.log 2 * Gb (m + 1) u ^ (m + 1) :=
              mul_le_mul_of_nonneg_right (sum_not_prime_vonMangoldt_div_le _) (pow_nonneg hG0 _)
      -- (b) the recursive + prime-multiple part
      have hb : ∑ d ∈ Ioc 0 ⌊Real.exp u⌋₊, Λ d / d *
            SdivP (Λ ^ (m + 1)) (fun e => ¬ Squarefree e ∨ (d.Prime ∧ d ∣ e)) (u - Real.log d)
          ≤ C * Gb (m + 1) u ^ (m + 1) + 2 * (m + 1) * Cdef * Gb (m + 1) u ^ (m + 1) := by
        -- pointwise: SdivP(...∨...) ≤ Nsf (m+1) (u−log d) + [d prime]·Dsum (m+1) d (u−log d)
        have hpt : ∀ d ∈ Ioc 0 ⌊Real.exp u⌋₊, Λ d / d *
              SdivP (Λ ^ (m + 1)) (fun e => ¬ Squarefree e ∨ (d.Prime ∧ d ∣ e)) (u - Real.log d)
            ≤ Λ d / d * (C * Gb (m + 1) u ^ m)
              + (if d.Prime then Real.log d ^ 2 / (d:ℝ) ^ 2 * (2 * (m + 1) * Gb (m + 1) u ^ m) else 0) := by
          intro d hd
          have hlog : Real.log d ≤ u := log_le_of_mem_Ioc_floor_exp hd
          have hlog0 : 0 ≤ Real.log d := Real.log_natCast_nonneg d
          have hu' : 0 ≤ u - Real.log d := by linarith
          have hΛd : 0 ≤ Λ d / d := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d)
          have hGle : Gb m (u - Real.log d) ≤ Gb (m + 1) u :=
            (Gb_mono_u m (by linarith : u - Real.log d ≤ u)).trans (by rw [Gb_succ]; linarith [KM_nonneg])
          have hGpow : Gb m (u - Real.log d) ^ m ≤ Gb (m + 1) u ^ m :=
            pow_le_pow_left₀ (Gb_nonneg hu') hGle m
          have hN : SdivP (Λ ^ (m + 1)) (fun e => ¬ Squarefree e) (u - Real.log d) ≤ C * Gb (m + 1) u ^ m := by
            have := hC (u - Real.log d) hu'
            unfold Nsf at this
            exact this.trans (mul_le_mul_of_nonneg_left hGpow hC0)
          have hsplit := SdivP_or_le (lamPow_nonneg (m + 1)) (fun e => ¬ Squarefree e)
            (fun e => d.Prime ∧ d ∣ e) (u - Real.log d)
          by_cases hdp : d.Prime
          · rw [if_pos hdp]
            have hD : SdivP (Λ ^ (m + 1)) (fun e => d.Prime ∧ d ∣ e) (u - Real.log d)
                ≤ (m + 1) * (2 * Real.log d / d) * Gb (m + 1) u ^ m := by
              calc SdivP (Λ ^ (m + 1)) (fun e => d.Prime ∧ d ∣ e) (u - Real.log d)
                  ≤ SdivP (Λ ^ (m + 1)) (fun e => d ∣ e) (u - Real.log d) :=
                    SdivP_mono_pred (lamPow_nonneg (m + 1)) (fun e h => h.2) _
                _ ≤ (m + 1) * (2 * Real.log d / d) * Gb m (u - Real.log d) ^ m := Dsum_le hdp m hu'
                _ ≤ (m + 1) * (2 * Real.log d / d) * Gb (m + 1) u ^ m := by
                    refine mul_le_mul_of_nonneg_left hGpow (mul_nonneg (by positivity) ?_)
                    exact div_nonneg (mul_nonneg zero_le_two hlog0) (Nat.cast_nonneg d)
            have hΛd' : Λ d / d = Real.log d / d := by
              rw [ArithmeticFunction.vonMangoldt_apply_prime hdp]
            calc Λ d / d * SdivP (Λ ^ (m + 1)) (fun e => ¬ Squarefree e ∨ (d.Prime ∧ d ∣ e)) (u - Real.log d)
                ≤ Λ d / d * (C * Gb (m + 1) u ^ m + (m + 1) * (2 * Real.log d / d) * Gb (m + 1) u ^ m) :=
                  mul_le_mul_of_nonneg_left (hsplit.trans (add_le_add hN hD)) hΛd
              _ = Λ d / d * (C * Gb (m + 1) u ^ m)
                  + Real.log d ^ 2 / (d:ℝ) ^ 2 * (2 * (m + 1) * Gb (m + 1) u ^ m) := by
                  rw [mul_add, hΛd']; ring
          · rw [if_neg hdp, add_zero]
            have hD0 : SdivP (Λ ^ (m + 1)) (fun e => d.Prime ∧ d ∣ e) (u - Real.log d) = 0 := by
              unfold SdivP
              refine sum_eq_zero fun e he => ?_
              exact absurd (mem_filter.mp he).2.1 hdp
            calc Λ d / d * SdivP (Λ ^ (m + 1)) (fun e => ¬ Squarefree e ∨ (d.Prime ∧ d ∣ e)) (u - Real.log d)
                ≤ Λ d / d * (C * Gb (m + 1) u ^ m + 0) := by
                  refine mul_le_mul_of_nonneg_left ?_ hΛd
                  exact hsplit.trans (by rw [hD0]; exact add_le_add hN le_rfl)
              _ = Λ d / d * (C * Gb (m + 1) u ^ m) := by rw [add_zero]
        calc _ ≤ ∑ d ∈ Ioc 0 ⌊Real.exp u⌋₊, (Λ d / d * (C * Gb (m + 1) u ^ m)
              + (if d.Prime then Real.log d ^ 2 / (d:ℝ) ^ 2 * (2 * (m + 1) * Gb (m + 1) u ^ m) else 0)) :=
              sum_le_sum hpt
          _ = Sdiv Λ u * (C * Gb (m + 1) u ^ m)
              + (∑ p ∈ (Ioc 0 ⌊Real.exp u⌋₊).filter Nat.Prime, Real.log p ^ 2 / (p:ℝ) ^ 2)
                * (2 * (m + 1) * Gb (m + 1) u ^ m) := by
              rw [sum_add_distrib, ← sum_mul, ← sum_filter, ← sum_mul]; rfl
          _ ≤ (u + KM) * (C * Gb (m + 1) u ^ m) + Cdef * (2 * (m + 1) * Gb (m + 1) u ^ m) :=
              add_le_add (mul_le_mul_of_nonneg_right (Sdiv_lam_le hu) (mul_nonneg hC0 (pow_nonneg hG0 m)))
                (mul_le_mul_of_nonneg_right (sum_prime_log_sq_div_sq_le _)
                  (mul_nonneg (by positivity) (pow_nonneg hG0 m)))
          _ ≤ Gb (m + 1) u * (C * Gb (m + 1) u ^ m) + Cdef * (2 * (m + 1) * (Gb (m + 1) u ^ m * Gb (m + 1) u)) := by
              have hCdef : (0:ℝ) ≤ Cdef := by unfold Cdef; norm_num
              exact add_le_add
                (mul_le_mul_of_nonneg_right (u_add_KM_le_Gb _ _) (mul_nonneg hC0 (pow_nonneg hG0 m)))
                (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                  (le_mul_of_one_le_right (pow_nonneg hG0 m) hG1) (by positivity)) hCdef)
          _ = C * Gb (m + 1) u ^ (m + 1) + 2 * (m + 1) * Cdef * Gb (m + 1) u ^ (m + 1) := by ring
      calc _ ≤ Cdef / Real.log 2 * Gb (m + 1) u ^ (m + 1)
            + (C * Gb (m + 1) u ^ (m + 1) + 2 * (m + 1) * Cdef * Gb (m + 1) u ^ (m + 1)) := add_le_add ha hb
        _ = (Cdef / Real.log 2 + C + 2 * (↑m + 1) * Cdef) * Gb (m + 1) u ^ (m + 1) := by ring

/-- polynomial form: for each m ≥ 1 there is C with  Nsf m u ≤ C·(1+u)^{m−1}  (u ≥ 0). -/
theorem Nsf_le_poly (m : ℕ) (hm : 1 ≤ m) : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → Nsf m u ≤ C * (1 + u) ^ (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨C, hC0, hC⟩ := Nsf_le k
  -- Gb k u = u + (k+1)K + 1 ≤ ((k+1)K + 1)·(1 + u)
  refine ⟨C * ((k + 1) * KM + 1) ^ k,
    mul_nonneg hC0 (pow_nonneg (add_nonneg (mul_nonneg (by positivity) KM_nonneg) zero_le_one) k),
    fun u hu => ?_⟩
  have hG : Gb k u ≤ ((k + 1) * KM + 1) * (1 + u) := by
    unfold Gb; nlinarith [KM_nonneg, mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ) + 1) KM_nonneg) hu]
  simp only [Nat.add_sub_cancel]
  calc Nsf (k + 1) u ≤ C * Gb k u ^ k := hC u hu
    _ ≤ C * (((k + 1) * KM + 1) * (1 + u)) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Gb_nonneg hu) hG k) hC0
    _ = C * ((k + 1) * KM + 1) ^ k * (1 + u) ^ k := by rw [mul_pow]; ring

end XiPrime
end Zeta23
