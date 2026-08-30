/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Coeff/MainTerm/Squarefree.lean — exact evaluation of the Dirichlet powers at squarefree N.

For N squarefree, every prime-power divisor of N is a prime, so the k-fold Dirichlet power of any
arithmetic function supported on prime powers is explicit:
  (f^{∗k})(N) = k! · ∏_{p | N} f(p)  if ω(N) = k,  and 0 otherwise.
Consequences ([XF′] Def 2.3, "For squarefree N = p_1⋯p_k …"):
  Λ^{∗k}(N), (Λ·log)^{∗k}(N), [(Λ·log) ∗ Λ^{∗j}](N) = j!·log N·∏ log p  (ω N = j+1),
  C(N;Λ⋆) = (k−1)!·Λ⋆^{−k}·log N·∏_{p|N} log p   (k = ω N ≥ 2),   C(p;Λ⋆) = −log p + Λ⋆^{−1} log²p,
  ‖C(N;Λ⋆)‖² = ‖Λ⋆‖^{−2k}·((k−1)!²/k!)·(Λ·log)^{∗k}(N)·log²N.
No analysis in this file.
-/
import Zeta23.XiPrime.Coeff.Basic

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Omega ArithmeticFunction.omega ComplexConjugate
open Finset

noncomputable section

namespace Zeta23
namespace XiPrime

/-! ### squarefree bookkeeping -/

/-- A0: ω N = #(prime factors of N). -/
lemma cardDistinctFactors_eq_card_primeFactors (N : ℕ) : ω N = N.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

/-- a prime-power divisor of a squarefree number is a prime. -/
lemma prime_of_isPrimePow_dvd_squarefree {N d : ℕ} (hN : Squarefree N) (hd : d ∣ N)
    (hpp : IsPrimePow d) : d.Prime :=
  Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hN.squarefree_of_dvd hd, hpp⟩

/-- for p a prime factor of squarefree N: the prime factors of N/p. -/
lemma primeFactors_div_of_mem {N p : ℕ} (hN : Squarefree N) (hp : p ∈ N.primeFactors) :
    (N / p).primeFactors = N.primeFactors.erase p := by
  have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ N := Nat.dvd_of_mem_primeFactors hp
  have hg : N.gcd p = p := Nat.gcd_eq_right hpd
  have h := Nat.primeFactors_div_gcd hN hpP.ne_zero
  rw [hg, hpP.primeFactors, sdiff_singleton_eq_erase] at h
  exact h

lemma squarefree_div_of_mem {N p : ℕ} (hN : Squarefree N) (hp : p ∈ N.primeFactors) :
    Squarefree (N / p) :=
  hN.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp))

lemma cardDistinctFactors_div_of_mem {N p : ℕ} (hN : Squarefree N) (hp : p ∈ N.primeFactors) :
    ω (N / p) + 1 = ω N := by
  rw [cardDistinctFactors_eq_card_primeFactors, cardDistinctFactors_eq_card_primeFactors,
    primeFactors_div_of_mem hN hp, card_erase_of_mem hp]
  have : 0 < N.primeFactors.card := card_pos.mpr ⟨p, hp⟩
  omega

/-- ω N ≠ 1 means N is not a prime power, so Λ N = 0. -/
lemma vonMangoldt_eq_zero_of_cardDistinctFactors_ne_one {N : ℕ} (h : ω N ≠ 1) : Λ N = 0 := by
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
  intro hpp
  exact h (ArithmeticFunction.cardDistinctFactors_eq_one_iff.mpr hpp)

/-- for squarefree N, Ω N = ω N. -/
lemma cardFactors_eq_cardDistinctFactors_of_squarefree {N : ℕ} (hN : Squarefree N) : Ω N = ω N :=
  ((ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hN.ne_zero).mpr hN).symm

/-! ### the generic evaluation -/

/-- **Dirichlet powers at squarefree N.**  If f is supported on prime powers then, for N squarefree,
(f^{∗k})(N) = k!·∏_{p|N} f(p) when ω N = k, and 0 otherwise. -/
theorem pow_apply_squarefree {f : ArithmeticFunction ℝ} (hf : ∀ n, ¬IsPrimePow n → f n = 0) :
    ∀ (k : ℕ) {N : ℕ}, Squarefree N →
      (f ^ k) N = if ω N = k then (k.factorial : ℝ) * ∏ p ∈ N.primeFactors, f p else 0
  | 0, N, hN => by
      rw [pow_zero, ArithmeticFunction.one_apply]
      by_cases h1 : N = 1
      · subst h1; simp
      · have hω : ω N ≠ 0 := by
          rw [Ne, ArithmeticFunction.cardDistinctFactors_eq_zero]
          have := hN.ne_zero; omega
        rw [if_neg h1, if_neg hω]
  | k + 1, N, hN => by
      have hN0 : N ≠ 0 := hN.ne_zero
      rw [pow_succ, ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal' (f := fun a b => (f ^ k) a * f b)]
      -- only prime divisors b contribute
      have hsub : N.primeFactors ⊆ N.divisors := fun p hp =>
        Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_primeFactors hp, hN0⟩
      have hext : ∑ b ∈ N.primeFactors, (f ^ k) (N / b) * f b
          = ∑ b ∈ N.divisors, (f ^ k) (N / b) * f b := by
        refine sum_subset hsub fun b hb hbp => ?_
        have hbd : b ∣ N := Nat.dvd_of_mem_divisors hb
        have hfb : f b = 0 := by
          refine hf b fun hpp => hbp ?_
          exact Nat.mem_primeFactors.mpr ⟨prime_of_isPrimePow_dvd_squarefree hN hbd hpp, hbd, hN0⟩
        rw [hfb, mul_zero]
      rw [← hext]
      -- evaluate each term by the induction hypothesis at N/p
      have hterm : ∀ p ∈ N.primeFactors, (f ^ k) (N / p) * f p =
          if ω N = k + 1 then (k.factorial : ℝ) * ∏ q ∈ N.primeFactors, f q else 0 := by
        intro p hp
        rw [pow_apply_squarefree hf k (squarefree_div_of_mem hN hp), primeFactors_div_of_mem hN hp]
        have hω := cardDistinctFactors_div_of_mem hN hp
        by_cases hk : ω N = k + 1
        · have : ω (N / p) = k := by omega
          rw [if_pos this, if_pos hk, mul_assoc, prod_erase_mul _ _ hp]
        · have : ω (N / p) ≠ k := by omega
          rw [if_neg this, if_neg hk, zero_mul]
      rw [sum_congr rfl hterm, sum_const, ← cardDistinctFactors_eq_card_primeFactors, nsmul_eq_mul]
      by_cases hk : ω N = k + 1
      · rw [if_pos hk, if_pos hk, hk, Nat.factorial_succ]; push_cast; ring
      · rw [if_neg hk, if_neg hk, mul_zero]

lemma vonMangoldt_supported (n : ℕ) (h : ¬IsPrimePow n) : Λ n = 0 :=
  ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h

lemma lamLog_supported (n : ℕ) (h : ¬IsPrimePow n) : lamLog n = 0 := by
  rw [lamLog_apply, vonMangoldt_supported n h, zero_mul]

/-- A1. -/
theorem lamPow_apply_squarefree {N : ℕ} (hN : Squarefree N) (k : ℕ) :
    (Λ ^ k) N = if ω N = k then (k.factorial : ℝ) * ∏ p ∈ N.primeFactors, Real.log p else 0 := by
  rw [pow_apply_squarefree vonMangoldt_supported k hN]
  split_ifs with h
  · congr 1
    exact prod_congr rfl fun p hp =>
      ArithmeticFunction.vonMangoldt_apply_prime (Nat.prime_of_mem_primeFactors hp)
  · rfl

/-- A2. -/
theorem lamLogPow_apply_squarefree {N : ℕ} (hN : Squarefree N) (k : ℕ) :
    (lamLog ^ k) N =
      if ω N = k then (k.factorial : ℝ) * ∏ p ∈ N.primeFactors, Real.log p ^ 2 else 0 := by
  rw [pow_apply_squarefree lamLog_supported k hN]
  split_ifs with h
  · congr 1
    refine prod_congr rfl fun p hp => ?_
    rw [lamLog_apply, ArithmeticFunction.vonMangoldt_apply_prime (Nat.prime_of_mem_primeFactors hp), sq]
  · rfl

/-- Σ_{p | N} log p = log N for squarefree N. -/
lemma sum_primeFactors_log_of_squarefree {N : ℕ} (hN : Squarefree N) :
    ∑ p ∈ N.primeFactors, Real.log p = Real.log N := by
  rw [← Real.log_prod (fun p hp => ?_)]
  · rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hN]
  · exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- A3: [(Λ·log) ∗ Λ^{∗j}](N) = j!·log N·∏_{p|N} log p if ω N = j+1, else 0  (N squarefree). -/
theorem lamLogConv_apply_squarefree {N : ℕ} (hN : Squarefree N) (j : ℕ) :
    lamLogConv j N =
      if ω N = j + 1 then (j.factorial : ℝ) * Real.log N * ∏ p ∈ N.primeFactors, Real.log p
      else 0 := by
  have hN0 : N ≠ 0 := hN.ne_zero
  rw [lamLogConv_eq, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (f := fun a b => lamLog a * (Λ ^ j) b)]
  have hsub : N.primeFactors ⊆ N.divisors := fun p hp =>
    Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_primeFactors hp, hN0⟩
  have hext : ∑ a ∈ N.primeFactors, lamLog a * (Λ ^ j) (N / a)
      = ∑ a ∈ N.divisors, lamLog a * (Λ ^ j) (N / a) := by
    refine sum_subset hsub fun a ha hap => ?_
    have had : a ∣ N := Nat.dvd_of_mem_divisors ha
    have hfa : lamLog a = 0 := by
      refine lamLog_supported a fun hpp => hap ?_
      exact Nat.mem_primeFactors.mpr ⟨prime_of_isPrimePow_dvd_squarefree hN had hpp, had, hN0⟩
    rw [hfa, zero_mul]
  rw [← hext]
  have hterm : ∀ p ∈ N.primeFactors, lamLog p * (Λ ^ j) (N / p) =
      if ω N = j + 1 then (j.factorial : ℝ) * Real.log p * ∏ q ∈ N.primeFactors, Real.log q
      else 0 := by
    intro p hp
    have hpP := Nat.prime_of_mem_primeFactors hp
    rw [lamPow_apply_squarefree (squarefree_div_of_mem hN hp), primeFactors_div_of_mem hN hp,
      lamLog_apply, ArithmeticFunction.vonMangoldt_apply_prime hpP]
    have hω := cardDistinctFactors_div_of_mem hN hp
    by_cases hk : ω N = j + 1
    · have : ω (N / p) = j := by omega
      rw [if_pos this, if_pos hk, ← prod_erase_mul _ _ hp]
      ring
    · have : ω (N / p) ≠ j := by omega
      rw [if_neg this, if_neg hk, mul_zero]
  rw [sum_congr rfl hterm]
  by_cases hk : ω N = j + 1
  · simp_rw [if_pos hk]
    rw [← sum_mul, ← mul_sum, sum_primeFactors_log_of_squarefree hN]
  · simp_rw [if_neg hk]
    rw [sum_const_zero]

/-! ### C(N; Λ⋆) at squarefree N -/

/-- A4: for squarefree N with k = ω N ≥ 2:  C(N;Λ⋆) = (k−1)!·Λ⋆^{−k}·log N·∏_{p|N} log p. -/
theorem xiCoeff_squarefree {N : ℕ} (hN : Squarefree N) (hk : 2 ≤ ω N) (Λs : ℂ) :
    xiCoeff Λs N = ((ω N - 1).factorial : ℂ) * (Λs⁻¹) ^ (ω N) * (Real.log N : ℂ)
                     * ((∏ p ∈ N.primeFactors, Real.log p : ℝ) : ℂ) := by
  have hΩ : Ω N = ω N := cardFactors_eq_cardDistinctFactors_of_squarefree hN
  have hΛ0 : Λ N = 0 := vonMangoldt_eq_zero_of_cardDistinctFactors_ne_one (by omega)
  unfold xiCoeff
  rw [hΛ0, hΩ, Complex.ofReal_zero, neg_zero, zero_add]
  rw [sum_eq_single_of_mem (ω N - 1) (mem_range.mpr (by omega))]
  · rw [lamLogConv_apply_squarefree hN, if_pos (by omega),
      show ω N - 1 + 1 = ω N by omega]
    push_cast
    ring
  · intro j _ hj
    rw [lamLogConv_apply_squarefree hN, if_neg (by omega), Complex.ofReal_zero, mul_zero]

/-- C(p;Λ⋆) = −log p + Λ⋆^{−1} log²p. -/
theorem xiCoeff_prime {p : ℕ} (hp : p.Prime) (Λs : ℂ) :
    xiCoeff Λs p = -(Real.log p : ℂ) + Λs⁻¹ * (Real.log p : ℂ) ^ 2 := by
  unfold xiCoeff
  rw [ArithmeticFunction.cardFactors_apply_prime hp, sum_range_one, zero_add, pow_one,
    ArithmeticFunction.vonMangoldt_apply_prime hp, lamLogConv_eq, pow_zero, mul_one, lamLog_apply,
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  push_cast
  ring

/-- ‖C(N;Λ⋆)‖² for squarefree N with ω N ≥ 2, in terms of (Λ·log)^{∗ω N}(N). -/
theorem norm_sq_xiCoeff_squarefree {N : ℕ} (hN : Squarefree N) (hk : 2 ≤ ω N) (Λs : ℂ)
    (hΛ : Λs ≠ 0) :
    ‖xiCoeff Λs N‖ ^ 2 = (‖Λs‖ ^ 2)⁻¹ ^ (ω N) * ((((ω N - 1).factorial : ℝ) ^ 2) / (ω N).factorial)
                           * (lamLog ^ (ω N)) N * Real.log N ^ 2 := by
  have _ := hΛ
  rw [xiCoeff_squarefree hN hk, lamLogPow_apply_squarefree hN, if_pos rfl]
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_inv, Complex.norm_natCast, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hfac : ((ω N).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hb : (‖Λs‖ ^ 2)⁻¹ ^ ω N = (‖Λs‖⁻¹ ^ ω N) ^ 2 := by
    rw [← inv_pow, ← pow_mul, ← pow_mul, mul_comm]
  rw [prod_pow, hb, mul_pow, mul_pow, mul_pow, sq_abs, sq_abs]
  field_simp

end XiPrime
end Zeta23
