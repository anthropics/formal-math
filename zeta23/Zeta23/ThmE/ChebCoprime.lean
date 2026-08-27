/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/ChebCoprime.lean — [eq:cheb2] restricted to
(n,q) = 1, derived from the unrestricted Zeta23.Cheb.chebyshevMertens by bounding the removed
prime-power terms: Σ_{p ∣ q} Σ_{k≥1} (log p)²/p^k ≤ Σ_{p∣q} (log p)² ≤ (log q)²
([thm:E] proof (iii): 'finitely many primes removed', O_q(·) errors).
-/
import Zeta23.ThmE.Hypotheses
import Zeta23.Chebyshev

open Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

namespace Zeta23
namespace ThmE

private lemma sum_half_pow_Icc_le (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, ((1:ℝ)/2) ^ k ≤ 1 - ((1:ℝ)/2) ^ N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 = n + 1 from rfl, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    have h2 : ((1:ℝ)/2) ^ (n+1) = ((1:ℝ)/2) ^ n * (1/2) := by ring
    rw [h2]
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n]

/-- The removed-terms bound: for a weight `w` with `0 ≤ w ≤ W` on the window,
`Σ_{n ≤ x, ¬(n,q)=1} Λ(n)²/n · w(n) ≤ W·(log q)²`. -/
private lemma removed_le (q : ℕ) (hq : 1 ≤ q) (x : ℝ) (w : ℕ → ℝ) (W : ℝ)
    (hw : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, 0 ≤ w n ∧ w n ≤ W) (hW : 0 ≤ W) :
    ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q),
        (Λ n : ℝ) ^ 2 / n * w n
      ≤ W * Real.log q ^ 2 := by
  classical
  have hq0 : 0 < q := hq
  set f : ℕ → ℝ := fun n => (Λ n : ℝ) ^ 2 / n * w n with hf
  have hf0 : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, 0 ≤ f n := by
    intro n hn
    have := (hw n hn).1
    have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    positivity
  set U : ℕ → Finset ℕ :=
    fun p => (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ∃ k, 0 < k ∧ n = p ^ k) with hU
  -- step 1: restrict to the nonzero terms and embed into the fibers
  have hsub : ((Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q)).filter (fun n => f n ≠ 0)
      ⊆ q.primeFactors.biUnion U := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnT, hne⟩ := hn
    rw [Finset.mem_filter] at hnT
    obtain ⟨hnIoc, hncop⟩ := hnT
    have hΛ : Λ n ≠ 0 := by
      intro h0
      apply hne
      rw [hf]
      simp [h0]
    have hpp : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hΛ
    obtain ⟨p, k, hp, hk, rfl⟩ := hpp
    have hp' : p.Prime := hp.nat_prime
    have hpq : p ∣ q := by
      by_contra hnd
      apply hncop
      exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp').2 hnd)
    rw [Finset.mem_biUnion]
    refine ⟨p, Nat.mem_primeFactors.2 ⟨hp', hpq, hq0.ne'⟩, ?_⟩
    rw [hU]
    exact Finset.mem_filter.2 ⟨hnIoc, ⟨k, hk, rfl⟩⟩
  -- step 2: the fibers are pairwise disjoint
  have hdisj : ∀ p₁ ∈ q.primeFactors, ∀ p₂ ∈ q.primeFactors, p₁ ≠ p₂ →
      Disjoint (U p₁) (U p₂) := by
    intro p₁ h₁ p₂ h₂ hne
    rw [Finset.disjoint_left]
    intro n hn₁ hn₂
    rw [hU, Finset.mem_filter] at hn₁ hn₂
    obtain ⟨-, k₁, hk₁, rfl⟩ := hn₁
    obtain ⟨-, k₂, hk₂, he⟩ := hn₂
    have hp₁ : p₁.Prime := Nat.prime_of_mem_primeFactors h₁
    have hp₂ : p₂.Prime := Nat.prime_of_mem_primeFactors h₂
    apply hne
    have hdvd : p₂ ∣ p₁ ^ k₁ := he ▸ dvd_pow_self p₂ hk₂.ne'
    have := (Nat.Prime.dvd_of_dvd_pow hp₂ hdvd)
    exact ((Nat.prime_dvd_prime_iff_eq hp₂ hp₁).1 this).symm
  -- step 3: per-fiber bound
  have hfiber : ∀ p ∈ q.primeFactors, ∑ n ∈ U p, f n ≤ W * Real.log p ^ 2 := by
    intro p hpmem
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hp2 : 2 ≤ p := hp'.two_le
    have hlogp : (0:ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hp'.pos.ne')
    -- U p = image of the exponent set
    set Kp := (Finset.Icc 1 ⌊x⌋₊).filter (fun k => p ^ k ∈ Finset.Ioc 0 ⌊x⌋₊) with hKp
    have hUeq : U p = Kp.image (fun k => p ^ k) := by
      ext n
      rw [hU, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hnIoc, k, hk, rfl⟩
        refine ⟨k, ?_, rfl⟩
        rw [hKp, Finset.mem_filter, Finset.mem_Icc]
        have hkx : k ≤ ⌊x⌋₊ := by
          have h1 : k < 2 ^ k := Nat.lt_two_pow_self
          have h2 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp2 k
          have h3 : p ^ k ≤ ⌊x⌋₊ := (Finset.mem_Ioc.1 hnIoc).2
          omega
        exact ⟨⟨hk, hkx⟩, hnIoc⟩
      · rintro ⟨k, hk, rfl⟩
        rw [hKp, Finset.mem_filter, Finset.mem_Icc] at hk
        exact ⟨hk.2, k, hk.1.1, rfl⟩
    have hinj : Set.InjOn (fun k => p ^ k) ↑Kp :=
      fun a _ b _ hab => Nat.pow_right_injective hp2 hab
    rw [hUeq, Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)]
    -- per-exponent bound
    have hterm : ∀ k ∈ Kp, f (p ^ k) ≤ W * Real.log p ^ 2 * ((1:ℝ)/2) ^ k := by
      intro k hkmem
      rw [hKp, Finset.mem_filter, Finset.mem_Icc] at hkmem
      obtain ⟨⟨hk1, -⟩, hIoc⟩ := hkmem
      have hΛpk : (Λ (p ^ k) : ℝ) = Real.log p := by
        rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : k ≠ 0),
          ArithmeticFunction.vonMangoldt_apply_prime hp']
      have hwk := hw (p ^ k) hIoc
      have hpk2 : ((2:ℝ)) ^ k ≤ (p : ℝ) ^ k := by
        apply pow_le_pow_left₀ (by norm_num)
        exact_mod_cast hp2
      have hpk0 : (0:ℝ) < (p:ℝ) ^ k := by positivity
      rw [hf]
      have e1 : ((Λ (p ^ k) : ℝ)) ^ 2 = Real.log p ^ 2 := by rw [hΛpk]
      push_cast
      rw [e1]
      calc Real.log p ^ 2 / ((p:ℝ) ^ k) * w (p ^ k)
          ≤ Real.log p ^ 2 / ((p:ℝ) ^ k) * W := by
            apply mul_le_mul_of_nonneg_left (hwk.2)
            positivity
        _ ≤ Real.log p ^ 2 / ((2:ℝ) ^ k) * W := by
            apply mul_le_mul_of_nonneg_right _ hW
            apply div_le_div_of_nonneg_left (by positivity) (by positivity) hpk2
        _ = W * Real.log p ^ 2 * ((1:ℝ)/2) ^ k := by
            rw [div_pow, one_pow]
            ring
    calc ∑ k ∈ Kp, f (p ^ k) ≤ ∑ k ∈ Kp, W * Real.log p ^ 2 * ((1:ℝ)/2) ^ k :=
          Finset.sum_le_sum hterm
      _ ≤ ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, W * Real.log p ^ 2 * ((1:ℝ)/2) ^ k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · rw [hKp]
            exact Finset.filter_subset _ _
          · intro k _ _
            positivity
      _ = W * Real.log p ^ 2 * ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, ((1:ℝ)/2) ^ k := by
          rw [Finset.mul_sum]
      _ ≤ W * Real.log p ^ 2 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine (sum_half_pow_Icc_le _).trans ?_
          have : (0:ℝ) ≤ ((1:ℝ)/2) ^ ⌊x⌋₊ := by positivity
          linarith
      _ = W * Real.log p ^ 2 := mul_one _
  -- assemble
  calc ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q), f n
      = ∑ n ∈ ((Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q)).filter
          (fun n => f n ≠ 0), f n := (Finset.sum_filter_ne_zero _).symm
    _ ≤ ∑ n ∈ q.primeFactors.biUnion U, f n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro n hn _
        apply hf0
        rw [Finset.mem_biUnion] at hn
        obtain ⟨p, -, hp⟩ := hn
        rw [hU] at hp
        exact (Finset.mem_filter.1 hp).1
    _ = ∑ p ∈ q.primeFactors, ∑ n ∈ U p, f n := Finset.sum_biUnion hdisj
    _ ≤ ∑ p ∈ q.primeFactors, W * Real.log p ^ 2 := Finset.sum_le_sum hfiber
    _ = W * ∑ p ∈ q.primeFactors, Real.log p ^ 2 := by rw [Finset.mul_sum]
    _ ≤ W * (∑ p ∈ q.primeFactors, Real.log p) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hW
        apply Finset.sum_sq_le_sq_sum_of_nonneg
        intro p hp
        exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.prime_of_mem_primeFactors hp).pos.ne')
    _ ≤ W * Real.log q ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hW
        have hsum : ∑ p ∈ q.primeFactors, Real.log p = Real.log (∏ p ∈ q.primeFactors, (p:ℝ)) := by
          rw [Real.log_prod]
          intro p hp
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos.ne'
        have hprod : (∏ p ∈ q.primeFactors, (p:ℝ)) ≤ (q:ℝ) := by
          have hd : (∏ p ∈ q.primeFactors, p) ∣ q := Nat.prod_primeFactors_dvd q
          have h0 : (∏ p ∈ q.primeFactors, p) ≤ q := Nat.le_of_dvd hq0 hd
          calc (∏ p ∈ q.primeFactors, (p:ℝ)) = ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
                push_cast
                rfl
            _ ≤ (q:ℝ) := by exact_mod_cast h0
        have hprod0 : (0:ℝ) < ∏ p ∈ q.primeFactors, (p:ℝ) := by
          apply Finset.prod_pos
          intro p hp
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
        have h1 : ∑ p ∈ q.primeFactors, Real.log p ≤ Real.log q := by
          rw [hsum]
          exact Real.log_le_log hprod0 hprod
        have h2 : (0:ℝ) ≤ ∑ p ∈ q.primeFactors, Real.log p := by
          apply Finset.sum_nonneg
          intro p hp
          exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.prime_of_mem_primeFactors hp).pos.ne')
        nlinarith

/-- **[eq:cheb2] with the (n,q)=1 restriction** ([thm:E] proof (iii)). -/
theorem chebyshevMertensCoprime (q : ℕ) (hq : 1 ≤ q) : ChebyshevMertensCoprime q := by
  obtain ⟨Ca, hCa⟩ := Zeta23.Cheb.chebyshevMertens.cheb2a
  obtain ⟨Cb, hCb⟩ := Zeta23.Cheb.chebyshevMertens.cheb2b
  have hlq0 : (0:ℝ) ≤ Real.log q ^ 2 := sq_nonneg _
  constructor
  · -- cheb2a
    refine ⟨Ca + 2 * Real.log q ^ 2, fun x hx => ?_⟩
    have hlogx : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
    have hlog2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊x⌋₊)
      (fun n => Nat.Coprime n q) (fun n => (Λ n : ℝ) ^ 2 / n)
    have hrem : ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q),
        (Λ n : ℝ) ^ 2 / n ≤ Real.log q ^ 2 := by
      have h0 := removed_le q hq x (fun _ => 1) 1 (fun n _ => ⟨zero_le_one, le_rfl⟩) zero_le_one
      simpa using h0
    have hrem0 : (0:ℝ) ≤ ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q),
        (Λ n : ℝ) ^ 2 / n := by
      apply Finset.sum_nonneg
      intro n _
      have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      positivity
    have hall := hCa x hx
    have hq2 : Real.log q ^ 2 ≤ 2 * Real.log q ^ 2 * Real.log x := by nlinarith
    calc |∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => Nat.Coprime n q), (Λ n : ℝ) ^ 2 / n
          - Real.log x ^ 2 / 2|
        = |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) ^ 2 / n - Real.log x ^ 2 / 2)
            - ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q),
              (Λ n : ℝ) ^ 2 / n| := by
          rw [← hsplit]
          congr 1
          ring
      _ ≤ |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) ^ 2 / n - Real.log x ^ 2 / 2|
            + |∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q),
              (Λ n : ℝ) ^ 2 / n| := abs_sub _ _
      _ ≤ Ca * Real.log x + Real.log q ^ 2 := by
          rw [abs_of_nonneg hrem0]
          linarith
      _ ≤ (Ca + 2 * Real.log q ^ 2) * Real.log x := by nlinarith
  · -- cheb2b
    refine ⟨Cb + 2 * Real.log q ^ 2, fun x hx => ?_⟩
    have hx1 : (1:ℝ) ≤ x := by linarith
    have hlogx : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
    have hlogx0 : (0:ℝ) ≤ Real.log x := Real.log_nonneg hx1
    have hlog2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊x⌋₊)
      (fun n => Nat.Coprime n q) (fun n => (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n))
    have hwbd : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        0 ≤ Real.log x - Real.log n ∧ Real.log x - Real.log n ≤ Real.log x := by
      intro n hn
      obtain ⟨hn0, hnx⟩ := Finset.mem_Ioc.1 hn
      have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn0
      have hnn : (n:ℝ) ≤ x := le_trans (by exact_mod_cast hnx) (Nat.floor_le (by linarith))
      constructor
      · have := Real.log_le_log (by linarith : (0:ℝ) < (n:ℝ)) hnn
        linarith
      · have := Real.log_nonneg hn1
        linarith
    have hrem := removed_le q hq x (fun n => Real.log x - Real.log n) (Real.log x) hwbd hlogx0
    have hrem0 : (0:ℝ) ≤ ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q),
        (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n) := by
      apply Finset.sum_nonneg
      intro n hn
      have hmem := (Finset.mem_filter.1 hn).1
      have hw := (hwbd n hmem).1
      have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      positivity
    have hall := hCb x hx
    have hq2 : Real.log x * Real.log q ^ 2 ≤ 2 * Real.log q ^ 2 * Real.log x ^ 2 := by nlinarith
    calc |∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => Nat.Coprime n q),
            (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n) - Real.log x ^ 3 / 6|
        = |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n)
              - Real.log x ^ 3 / 6)
            - ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q),
              (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n)| := by
          rw [← hsplit]
          congr 1
          ring
      _ ≤ |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n)
              - Real.log x ^ 3 / 6|
            + |∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q),
              (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n)| := abs_sub _ _
      _ ≤ Cb * Real.log x ^ 2 + Real.log x * Real.log q ^ 2 := by
          rw [abs_of_nonneg hrem0]
          linarith
      _ ≤ (Cb + 2 * Real.log q ^ 2) * Real.log x ^ 2 := by nlinarith

/-- **Uniform coprime Chebyshev–Mertens**: one absolute `A` with
`ChebyshevMertensCoprimeBounded q (A·(1 + log q)²)` for every `q ≥ 1` (the uniform-in-`q`
`chebq_uniform` input; constant = ζ-constants + the (log q)² prime-power loss). -/
theorem chebyshevMertensCoprimeBounded :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ q : ℕ, 1 ≤ q →
      ChebyshevMertensCoprimeBounded q (A * (1 + Real.log q) ^ 2) := by
  obtain ⟨Ca, hCa⟩ := Zeta23.Cheb.chebyshevMertens.cheb2a
  obtain ⟨Cb, hCb⟩ := Zeta23.Cheb.chebyshevMertens.cheb2b
  refine ⟨|Ca| + |Cb| + 2, by positivity, fun q hq => ?_⟩
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hlq : (0:ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hA1 : (1:ℝ) ≤ (1 + Real.log q) ^ 2 := by nlinarith
  have hq2 : Real.log q ^ 2 ≤ (1 + Real.log q) ^ 2 := by nlinarith
  constructor
  · intro x hx
    have hlogx : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
    have hlog2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊x⌋₊)
      (fun n => Nat.Coprime n q) (fun n => (Λ n : ℝ) ^ 2 / n)
    have hrem : ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q),
        (Λ n : ℝ) ^ 2 / n ≤ Real.log q ^ 2 := by
      have h0 := removed_le q hq x (fun _ => 1) 1 (fun n _ => ⟨zero_le_one, le_rfl⟩) zero_le_one
      simpa using h0
    have hrem0 : (0:ℝ) ≤ ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q),
        (Λ n : ℝ) ^ 2 / n := by
      apply Finset.sum_nonneg
      intro n _
      have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      positivity
    have hall := hCa x hx
    calc |∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => Nat.Coprime n q), (Λ n : ℝ) ^ 2 / n
          - Real.log x ^ 2 / 2|
        = |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) ^ 2 / n - Real.log x ^ 2 / 2)
            - ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q),
              (Λ n : ℝ) ^ 2 / n| := by
          rw [← hsplit]
          congr 1
          ring
      _ ≤ |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) ^ 2 / n - Real.log x ^ 2 / 2|
            + |∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q),
              (Λ n : ℝ) ^ 2 / n| := abs_sub _ _
      _ ≤ Ca * Real.log x + Real.log q ^ 2 := by
          rw [abs_of_nonneg hrem0]
          linarith
      _ ≤ (|Ca| + |Cb| + 2) * (1 + Real.log q) ^ 2 * Real.log x := by
          have e1 : Ca * Real.log x ≤ |Ca| * ((1 + Real.log q) ^ 2 * Real.log x) := by
            have h2 : Ca ≤ |Ca| := le_abs_self _
            have h3 : (0:ℝ) ≤ Real.log x := by linarith
            calc Ca * Real.log x ≤ |Ca| * Real.log x := mul_le_mul_of_nonneg_right h2 h3
              _ = |Ca| * Real.log x * 1 := (mul_one _).symm
              _ ≤ |Ca| * Real.log x * (1 + Real.log q) ^ 2 :=
                  mul_le_mul_of_nonneg_left hA1 (mul_nonneg (abs_nonneg Ca) h3)
              _ = |Ca| * ((1 + Real.log q) ^ 2 * Real.log x) := by ring
          have e2 : Real.log q ^ 2 ≤ 2 * ((1 + Real.log q) ^ 2 * Real.log x) := by
            have h3 : (1:ℝ)/2 ≤ Real.log x := by linarith
            nlinarith
          have e3 : (0:ℝ) ≤ |Cb| * ((1 + Real.log q) ^ 2 * Real.log x) := by
            have h3 : (0:ℝ) ≤ Real.log x := by linarith
            positivity
          nlinarith
  · intro x hx
    have hx1 : (1:ℝ) ≤ x := by linarith
    have hlogx : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
    have hlogx0 : (0:ℝ) ≤ Real.log x := Real.log_nonneg hx1
    have hlog2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊x⌋₊)
      (fun n => Nat.Coprime n q) (fun n => (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n))
    have hwbd : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        0 ≤ Real.log x - Real.log n ∧ Real.log x - Real.log n ≤ Real.log x := by
      intro n hn
      obtain ⟨hn0, hnx⟩ := Finset.mem_Ioc.1 hn
      have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn0
      have hnn : (n:ℝ) ≤ x := le_trans (by exact_mod_cast hnx) (Nat.floor_le (by linarith))
      constructor
      · have h0 := Real.log_le_log (by linarith : (0:ℝ) < (n:ℝ)) hnn
        linarith
      · have h0 := Real.log_nonneg hn1
        linarith
    have hrem := removed_le q hq x (fun n => Real.log x - Real.log n) (Real.log x) hwbd hlogx0
    have hrem0 : (0:ℝ) ≤ ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q),
        (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n) := by
      apply Finset.sum_nonneg
      intro n hn
      have hmem := (Finset.mem_filter.1 hn).1
      have hw := (hwbd n hmem).1
      have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      positivity
    have hall := hCb x hx
    calc |∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => Nat.Coprime n q),
            (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n) - Real.log x ^ 3 / 6|
        = |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n)
              - Real.log x ^ 3 / 6)
            - ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q),
              (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n)| := by
          rw [← hsplit]
          congr 1
          ring
      _ ≤ |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n)
              - Real.log x ^ 3 / 6|
            + |∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q),
              (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n)| := abs_sub _ _
      _ ≤ Cb * Real.log x ^ 2 + Real.log x * Real.log q ^ 2 := by
          rw [abs_of_nonneg hrem0]
          linarith
      _ ≤ (|Ca| + |Cb| + 2) * (1 + Real.log q) ^ 2 * Real.log x ^ 2 := by
          have h3 : (1:ℝ)/2 ≤ Real.log x := by linarith
          have e1 : Cb * Real.log x ^ 2 ≤ |Cb| * ((1 + Real.log q) ^ 2 * Real.log x ^ 2) := by
            calc Cb * Real.log x ^ 2 ≤ |Cb| * Real.log x ^ 2 :=
                  mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
              _ = |Cb| * Real.log x ^ 2 * 1 := (mul_one _).symm
              _ ≤ |Cb| * Real.log x ^ 2 * (1 + Real.log q) ^ 2 :=
                  mul_le_mul_of_nonneg_left hA1 (mul_nonneg (abs_nonneg Cb) (sq_nonneg _))
              _ = |Cb| * ((1 + Real.log q) ^ 2 * Real.log x ^ 2) := by ring
          have e2 : Real.log x * Real.log q ^ 2 ≤ 2 * ((1 + Real.log q) ^ 2 * Real.log x ^ 2) := by
            nlinarith [sq_nonneg (Real.log x)]
          have e3 : (0:ℝ) ≤ |Ca| * ((1 + Real.log q) ^ 2 * Real.log x ^ 2) := by positivity
          nlinarith

/-- the plain (per-q) version, re-derived from the uniform one. -/
theorem chebyshevMertensCoprime' (q : ℕ) (hq : 1 ≤ q) : ChebyshevMertensCoprime q := by
  obtain ⟨A, hA0, hA⟩ := chebyshevMertensCoprimeBounded
  exact (hA q hq).toChebyshevMertensCoprime

end ThmE
end Zeta23
