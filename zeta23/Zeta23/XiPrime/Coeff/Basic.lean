/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Coeff/Basic.lean — pointwise algebra of the ξ′ coefficients C(N; Λ⋆).

The definitions  lamLogConv j := (Λ·log) ∗ Λ^{∗j}  and
  xiCoeff Λ⋆ N := −Λ(N) + Σ_{j < Ω N} Λ⋆^{-(j+1)} · lamLogConv j N
live in Zeta23/XiPrime/Defs.lean.  Here: nonnegativity / support / size of the Dirichlet
powers Λ^{∗m} (the ring power in ArithmeticFunction ℝ IS the Dirichlet power), the vanishing of the j-sum
beyond Ω(N), C(0) = C(1) = 0, conjugation symmetry, and the basic majorant
  ‖C(N;Λ⋆)‖ ≤ Λ(N) + log N · Σ_{1 ≤ m ≤ Ω N} ‖Λ⋆‖^{-m} Λ^{∗m}(N)        (lamLogConv j N ≤ log N · Λ^{∗(j+1)} N).
No analysis in this file.
-/
import Zeta23.XiPrime.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Omega ComplexConjugate
open Finset

noncomputable section

namespace Zeta23
namespace XiPrime

/-! ## §0. Summing a Dirichlet convolution over N ≤ X

  Σ_{N ≤ X} (f ∗ g)(N) · h(N)  =  Σ_{d ≤ X} f(d) · Σ_{e ≤ X/d} g(e) · h(d·e),  and for nonnegative f, g and a nonnegative
  sub-multiplicative weight w:  Σ_{N≤X}(f∗g)(N)w(N) ≤ (Σ f w)(Σ g w),  Σ_{N≤X} f^{∗(m+1)}(N)w(N) ≤ (Σ f w)^{m+1}. -/

section Swap

variable {R : Type*} [CommSemiring R]

/-- Σ_{N≤X} (f∗g)(N)·h(N) = Σ_{d≤X} f(d) Σ_{e≤X/d} g(e) h(de). -/
theorem sum_Ioc_mul_apply (f g : ArithmeticFunction R) (h : ℕ → R) (X : ℕ) :
    ∑ N ∈ Ioc 0 X, (f * g) N * h N =
      ∑ d ∈ Ioc 0 X, f d * ∑ e ∈ Ioc 0 (X / d), g e * h (d * e) := by
  simp_rw [ArithmeticFunction.mul_apply, sum_mul, mul_sum]
  rw [sum_sigma', sum_sigma']
  refine sum_nbij' (fun x => ⟨x.2.1, x.2.2⟩) (fun y => ⟨y.1 * y.2, (y.1, y.2)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨N, ⟨a, b⟩⟩ hx
    simp only [mem_sigma, mem_Ioc, Nat.mem_divisorsAntidiagonal] at hx ⊢
    obtain ⟨⟨hN0, hNX⟩, hab, hN⟩ := hx
    have ha : a ≠ 0 := by rintro rfl; simp at hab; exact hN hab.symm
    have hb : b ≠ 0 := by rintro rfl; simp at hab; exact hN hab.symm
    refine ⟨⟨Nat.pos_of_ne_zero ha, ?_⟩, Nat.pos_of_ne_zero hb, ?_⟩
    · calc a ≤ a * b := Nat.le_mul_of_pos_right a (Nat.pos_of_ne_zero hb)
        _ = N := hab
        _ ≤ X := hNX
    · rw [Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero ha), mul_comm, hab]; exact hNX
  · rintro ⟨d, e⟩ hy
    simp only [mem_sigma, mem_Ioc, Nat.mem_divisorsAntidiagonal] at hy ⊢
    obtain ⟨⟨hd0, hdX⟩, he0, heX⟩ := hy
    rw [Nat.le_div_iff_mul_le hd0] at heX
    exact ⟨⟨Nat.mul_pos hd0 he0, by rwa [mul_comm] at heX⟩, by simp, (Nat.mul_pos hd0 he0).ne'⟩
  · rintro ⟨N, ⟨a, b⟩⟩ hx
    simp only [mem_sigma, Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨_, hab, _⟩ := hx
    simp [hab]
  · rintro ⟨d, e⟩ _
    rfl
  · rintro ⟨N, ⟨a, b⟩⟩ hx
    simp only [mem_sigma, Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨_, hab, _⟩ := hx
    simp [hab, mul_assoc]

/-- Same with the factors swapped: Σ_{N≤X} (f∗g)(N) h(N) = Σ_{e≤X} g(e) Σ_{d≤X/e} f(d) h(de). -/
theorem sum_Ioc_mul_apply' (f g : ArithmeticFunction R) (h : ℕ → R) (X : ℕ) :
    ∑ N ∈ Ioc 0 X, (f * g) N * h N =
      ∑ e ∈ Ioc 0 X, g e * ∑ d ∈ Ioc 0 (X / e), f d * h (d * e) := by
  rw [mul_comm f g, sum_Ioc_mul_apply]
  refine sum_congr rfl fun e _ => ?_
  congr 1
  refine sum_congr rfl fun d _ => ?_
  rw [mul_comm e d]


/-- A nonnegative weight with w(de) ≤ w(d)·w(e) (e.g. N ↦ N^{-σ}, or N ↦ g(N)/N with g submultiplicative). -/
structure SubmultWeight (w : ℕ → ℝ) : Prop where
  nonneg : ∀ n, 0 ≤ w n
  submul : ∀ d e, w (d * e) ≤ w d * w e

lemma SubmultWeight.rpow_neg (σ : ℝ) : SubmultWeight (fun n : ℕ => (n : ℝ) ^ (-σ)) where
  nonneg n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  submul d e := by rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg e)]

/-- product bound: Σ_{N≤X} (f∗g)(N) w(N) ≤ (Σ_{d≤X} f(d)w(d))·(Σ_{e≤X} g(e)w(e)) for f, g, w ≥ 0, w submult. -/
theorem sum_Ioc_mul_apply_le {f g : ArithmeticFunction ℝ} {w : ℕ → ℝ} (hw : SubmultWeight w)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (X : ℕ) :
    ∑ N ∈ Ioc 0 X, (f * g) N * w N ≤
      (∑ d ∈ Ioc 0 X, f d * w d) * (∑ e ∈ Ioc 0 X, g e * w e) := by
  rw [sum_Ioc_mul_apply, sum_mul]
  refine sum_le_sum fun d hd => ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hf d)
  calc ∑ e ∈ Ioc 0 (X / d), g e * w (d * e)
      ≤ ∑ e ∈ Ioc 0 (X / d), g e * (w d * w e) :=
        sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hw.submul d e) (hg e)
    _ ≤ ∑ e ∈ Ioc 0 X, g e * (w d * w e) := by
        refine sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc le_rfl (Nat.div_le_self X d)) ?_
        exact fun e _ _ => mul_nonneg (hg e) (mul_nonneg (hw.nonneg d) (hw.nonneg e))
    _ = w d * ∑ e ∈ Ioc 0 X, g e * w e := by rw [mul_sum]; refine sum_congr rfl fun e _ => by ring

/-- f ≥ 0 and g ≥ 0 pointwise ⇒ f ∗ g ≥ 0 pointwise. -/
lemma mul_apply_nonneg {f g : ArithmeticFunction ℝ} (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℕ) :
    0 ≤ (f * g) n := by
  rw [ArithmeticFunction.mul_apply]
  exact sum_nonneg fun x _ => mul_nonneg (hf _) (hg _)

/-- f ≥ 0 pointwise ⇒ every Dirichlet power f^{∗m} ≥ 0 pointwise. -/
lemma pow_apply_nonneg {f : ArithmeticFunction ℝ} (hf : ∀ n, 0 ≤ f n) : ∀ (m n : ℕ), 0 ≤ (f ^ m) n
  | 0, n => by
      rw [pow_zero, ArithmeticFunction.one_apply]
      split_ifs <;> norm_num
  | m + 1, n => by
      rw [pow_succ]
      exact mul_apply_nonneg (pow_apply_nonneg hf m) hf n

/-- power bound: Σ_{N≤X} f^{∗(m+1)}(N) w(N) ≤ (Σ_{n≤X} f(n)w(n))^{m+1}. -/
theorem sum_Ioc_pow_apply_le {f : ArithmeticFunction ℝ} {w : ℕ → ℝ} (hw : SubmultWeight w)
    (hf : ∀ n, 0 ≤ f n) (X : ℕ) :
    ∀ m : ℕ, ∑ N ∈ Ioc 0 X, (f ^ (m + 1)) N * w N ≤ (∑ n ∈ Ioc 0 X, f n * w n) ^ (m + 1)
  | 0 => by simp
  | m + 1 => by
      have h0 : 0 ≤ ∑ n ∈ Ioc 0 X, f n * w n := sum_nonneg fun n _ => mul_nonneg (hf n) (hw.nonneg n)
      calc ∑ N ∈ Ioc 0 X, (f ^ (m + 1 + 1)) N * w N
          = ∑ N ∈ Ioc 0 X, (f ^ (m + 1) * f) N * w N := by rw [pow_succ]
        _ ≤ (∑ d ∈ Ioc 0 X, (f ^ (m + 1)) d * w d) * (∑ e ∈ Ioc 0 X, f e * w e) :=
            sum_Ioc_mul_apply_le hw (pow_apply_nonneg hf (m + 1)) hf X
        _ ≤ (∑ n ∈ Ioc 0 X, f n * w n) ^ (m + 1) * (∑ e ∈ Ioc 0 X, f e * w e) :=
            mul_le_mul_of_nonneg_right (sum_Ioc_pow_apply_le hw hf X m) h0
        _ = (∑ n ∈ Ioc 0 X, f n * w n) ^ (m + 1 + 1) := by ring


end Swap

/-! ### Λ, Λ·log and the Dirichlet powers Λ^{∗m} -/

/-- (Λ·log)(n) = Λ(n)·log n  (the first factor of lamLogConv). -/
def lamLog : ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul (Λ : ArithmeticFunction ℝ) ArithmeticFunction.log

@[simp] lemma lamLog_apply (n : ℕ) : lamLog n = Λ n * Real.log n := by
  simp [lamLog, ArithmeticFunction.pmul_apply, ArithmeticFunction.log_apply]

lemma lamLogConv_eq (j : ℕ) : lamLogConv j = lamLog * Λ ^ j := rfl

lemma lamLog_nonneg (n : ℕ) : 0 ≤ lamLog n := by
  rw [lamLog_apply]
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg n)

lemma vonMangoldt_nonneg' (n : ℕ) : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg

lemma lamPow_nonneg (m n : ℕ) : 0 ≤ (Λ ^ m) n := pow_apply_nonneg vonMangoldt_nonneg' m n

lemma lamLogConv_nonneg (j n : ℕ) : 0 ≤ lamLogConv j n := by
  rw [lamLogConv_eq]
  exact mul_apply_nonneg lamLog_nonneg (lamPow_nonneg j) n

/-- Λ(b) ≠ 0 forces b > 1, hence Ω b ≥ 1. -/
lemma one_le_cardFactors_of_vonMangoldt_ne_zero {b : ℕ} (h : Λ b ≠ 0) : 1 ≤ Ω b := by
  have hb : IsPrimePow b := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h
  exact ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hb.one_lt

/-- in a divisor pair (a,b) of n, Ω n = Ω a + Ω b. -/
lemma cardFactors_of_mem_divisorsAntidiagonal {n : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ n.divisorsAntidiagonal) : Ω n = Ω x.1 + Ω x.2 := by
  obtain ⟨hprod, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have h1 : x.1 ≠ 0 := by rintro h; simp [h] at hprod; exact hn hprod.symm
  have h2 : x.2 ≠ 0 := by rintro h; simp [h] at hprod; exact hn hprod.symm
  rw [← hprod, ArithmeticFunction.cardFactors_mul h1 h2]

/-- Λ^{∗m}(n) = 0 unless Ω(n) ≥ m  (each Λ-factor uses up one prime factor counted with multiplicity). -/
lemma lamPow_eq_zero_of_cardFactors_lt : ∀ {m n : ℕ}, Ω n < m → (Λ ^ m) n = 0
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, n, h => by
      rw [pow_succ, ArithmeticFunction.mul_apply]
      refine sum_eq_zero fun x hx => ?_
      by_cases hb : Λ x.2 = 0
      · rw [hb, mul_zero]
      · have h1 := one_le_cardFactors_of_vonMangoldt_ne_zero hb
        have h2 := cardFactors_of_mem_divisorsAntidiagonal hx
        rw [lamPow_eq_zero_of_cardFactors_lt (m := m) (by omega), zero_mul]

/-- lamLogConv j n = 0 unless Ω(n) ≥ j+1. -/
lemma lamLogConv_eq_zero_of_le {j n : ℕ} (h : Ω n ≤ j) : lamLogConv j n = 0 := by
  rw [lamLogConv_eq, ArithmeticFunction.mul_apply]
  refine sum_eq_zero fun x hx => ?_
  by_cases ha : Λ x.1 = 0
  · simp [lamLog_apply, ha]
  · have h1 := one_le_cardFactors_of_vonMangoldt_ne_zero ha
    have h2 := cardFactors_of_mem_divisorsAntidiagonal hx
    rw [lamPow_eq_zero_of_cardFactors_lt (m := j) (by omega), mul_zero]

/-- Λ^{∗m}(n) ≤ (log n)^m : induct, using Σ_{d | n} Λ(d) = log n and log a ≤ log n for a | n. -/
lemma lamPow_le_log_pow : ∀ (m n : ℕ), (Λ ^ m) n ≤ Real.log n ^ m
  | 0, n => by
      rw [pow_zero, pow_zero, ArithmeticFunction.one_apply]
      split_ifs <;> norm_num
  | m + 1, n => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      rw [pow_succ, ArithmeticFunction.mul_apply]
      have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      calc ∑ x ∈ n.divisorsAntidiagonal, (Λ ^ m) x.1 * Λ x.2
          ≤ ∑ x ∈ n.divisorsAntidiagonal, Real.log n ^ m * Λ x.2 := by
            refine sum_le_sum fun x hx => ?_
            refine mul_le_mul_of_nonneg_right ?_ ArithmeticFunction.vonMangoldt_nonneg
            refine (lamPow_le_log_pow m x.1).trans ?_
            have hx1 : x.1 ∣ n := Nat.fst_mem_divisors_of_mem_antidiagonal hx |> Nat.dvd_of_mem_divisors
            have hx1pos : 0 < x.1 := Nat.pos_of_dvd_of_pos hx1 hn
            exact pow_le_pow_left₀ (Real.log_natCast_nonneg _)
              (Real.log_le_log (by exact_mod_cast hx1pos) (by exact_mod_cast Nat.le_of_dvd hn hx1)) m
        _ = Real.log n ^ m * ∑ x ∈ n.divisorsAntidiagonal, Λ x.2 := by rw [mul_sum]
        _ = Real.log n ^ m * Real.log n := by
            rw [Nat.sum_divisorsAntidiagonal' (f := fun _ b => Λ b), ArithmeticFunction.vonMangoldt_sum]
        _ = Real.log n ^ (m + 1) := by ring

/-- lamLogConv j n ≤ log n · Λ^{∗(j+1)}(n)  (bound log a ≤ log n on the (Λ·log)-factor). -/
lemma lamLogConv_le (j n : ℕ) : lamLogConv j n ≤ Real.log n * (Λ ^ (j + 1)) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [lamLogConv_eq, ArithmeticFunction.mul_apply, pow_succ', ArithmeticFunction.mul_apply, mul_sum]
  refine sum_le_sum fun x hx => ?_
  rw [lamLog_apply]
  have hx1 : x.1 ∣ n := Nat.fst_mem_divisors_of_mem_antidiagonal hx |> Nat.dvd_of_mem_divisors
  have hx1pos : 0 < x.1 := Nat.pos_of_dvd_of_pos hx1 hn
  have hlog : Real.log x.1 ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast hx1pos) (by exact_mod_cast Nat.le_of_dvd hn hx1)
  calc Λ x.1 * Real.log x.1 * (Λ ^ j) x.2 = Real.log x.1 * (Λ x.1 * (Λ ^ j) x.2) := by ring
    _ ≤ Real.log n * (Λ x.1 * (Λ ^ j) x.2) :=
        mul_le_mul_of_nonneg_right hlog (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (lamPow_nonneg _ _))

/-- (Λ·log)^{∗k}(n) ≤ (log n)^k · Λ^{∗k}(n)  (each log q_i ≤ log n). -/
lemma lamLogPow_le : ∀ (k n : ℕ), (lamLog ^ k) n ≤ Real.log n ^ k * (Λ ^ k) n
  | 0, n => by simp
  | k + 1, n => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      rw [pow_succ lamLog k, pow_succ (Λ : ArithmeticFunction ℝ) k, pow_succ (Real.log (n:ℝ)) k,
        ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, mul_sum]
      refine sum_le_sum fun x hx => ?_
      have hx1 : x.1 ∣ n := Nat.fst_mem_divisors_of_mem_antidiagonal hx |> Nat.dvd_of_mem_divisors
      have hx2 : x.2 ∣ n := Nat.snd_mem_divisors_of_mem_antidiagonal hx |> Nat.dvd_of_mem_divisors
      have hx1pos : 0 < x.1 := Nat.pos_of_dvd_of_pos hx1 hn
      have hx2pos : 0 < x.2 := Nat.pos_of_dvd_of_pos hx2 hn
      have hl1 : Real.log x.1 ≤ Real.log n :=
        Real.log_le_log (by exact_mod_cast hx1pos) (by exact_mod_cast Nat.le_of_dvd hn hx1)
      have hl2 : Real.log x.2 ≤ Real.log n :=
        Real.log_le_log (by exact_mod_cast hx2pos) (by exact_mod_cast Nat.le_of_dvd hn hx2)
      have h01 : 0 ≤ Real.log x.1 := Real.log_natCast_nonneg _
      have h02 : 0 ≤ Real.log x.2 := Real.log_natCast_nonneg _
      rw [lamLog_apply]
      calc (lamLog ^ k) x.1 * (Λ x.2 * Real.log x.2)
          ≤ (Real.log x.1 ^ k * (Λ ^ k) x.1) * (Λ x.2 * Real.log x.2) :=
            mul_le_mul_of_nonneg_right (lamLogPow_le k x.1)
              (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg h02)
        _ ≤ (Real.log n ^ k * (Λ ^ k) x.1) * (Λ x.2 * Real.log n) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h01 hl1 k) (lamPow_nonneg _ _))
              (mul_le_mul_of_nonneg_left hl2 ArithmeticFunction.vonMangoldt_nonneg)
              (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg h02)
              (mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k) (lamPow_nonneg _ _))
        _ = Real.log n ^ k * Real.log n * ((Λ ^ k) x.1 * Λ x.2) := by ring

lemma lamLogPow_nonneg (k n : ℕ) : 0 ≤ (lamLog ^ k) n := pow_apply_nonneg lamLog_nonneg k n

/-! ### C(N; Λ⋆): trivial values, range-independence, conjugation, basic majorant -/

@[simp] lemma xiCoeff_zero (Λs : ℂ) : xiCoeff Λs 0 = 0 := by
  simp [xiCoeff]

@[simp] lemma xiCoeff_one (Λs : ℂ) : xiCoeff Λs 1 = 0 := by
  simp [xiCoeff, ArithmeticFunction.vonMangoldt_apply_one]

/-- the j-sum may be taken over any range ⊇ range (Ω N): the extra terms vanish. -/
lemma xiCoeff_eq_sum_range_of_le (Λs : ℂ) {N M : ℕ} (hM : Ω N ≤ M) :
    xiCoeff Λs N = -((Λ N : ℝ) : ℂ) +
      ∑ j ∈ Finset.range M, (Λs⁻¹) ^ (j + 1) * ((lamLogConv j N : ℝ) : ℂ) := by
  unfold xiCoeff
  congr 1
  refine (sum_subset (range_subset_range.mpr hM) fun j _ hj => ?_)
  have : Ω N ≤ j := by simpa using hj
  rw [lamLogConv_eq_zero_of_le this]; simp

/-- C(N; conj Λ⋆) = conj C(N; Λ⋆)  (C is a real polynomial in Λ⋆⁻¹). -/
lemma xiCoeff_conj (Λs : ℂ) (N : ℕ) : xiCoeff (conj Λs) N = conj (xiCoeff Λs N) := by
  unfold xiCoeff
  simp [map_sum, map_neg, map_add, map_mul, map_pow, map_inv₀, Complex.conj_ofReal]

/-- the "j-part" of C:  C_J(N;Λ⋆) := Σ_{j<Ω N} Λ⋆^{-(j+1)}·lamLogConv j N, so that C = −Λ + C_J.
This is the coefficient sequence met by the explicit formula: its L-series is B/(Λ⋆ − A). -/
def xiCoeffJ (Λs : ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (Ω N), (Λs⁻¹) ^ (j + 1) * ((lamLogConv j N : ℝ) : ℂ)

lemma xiCoeff_eq_neg_add_xiCoeffJ (Λs : ℂ) (N : ℕ) :
    xiCoeff Λs N = -((Λ N : ℝ) : ℂ) + xiCoeffJ Λs N := rfl

@[simp] lemma xiCoeffJ_zero (Λs : ℂ) : xiCoeffJ Λs 0 = 0 := by
  simp [xiCoeffJ]

@[simp] lemma xiCoeffJ_one (Λs : ℂ) : xiCoeffJ Λs 1 = 0 := by
  simp [xiCoeffJ]

lemma xiCoeffJ_eq_sum_range_of_le (Λs : ℂ) {N M : ℕ} (hM : Ω N ≤ M) :
    xiCoeffJ Λs N = ∑ j ∈ Finset.range M, (Λs⁻¹) ^ (j + 1) * ((lamLogConv j N : ℝ) : ℂ) := by
  unfold xiCoeffJ
  refine (sum_subset (range_subset_range.mpr hM) fun j _ hj => ?_)
  have : Ω N ≤ j := by simpa using hj
  rw [lamLogConv_eq_zero_of_le this]; simp

lemma xiCoeffJ_conj (Λs : ℂ) (N : ℕ) : xiCoeffJ (conj Λs) N = conj (xiCoeffJ Λs N) := by
  unfold xiCoeffJ
  simp [map_sum, map_mul, map_pow, map_inv₀, Complex.conj_ofReal]

/-- ‖C_J(N;Λ⋆)‖ ≤ log N · F_{‖Λ⋆‖⁻¹}(N)  (proved below, after Fmaj). -/
lemma norm_xiCoeffJ_le_aux (Λs : ℂ) (N : ℕ) :
    ‖xiCoeffJ Λs N‖ ≤ ∑ j ∈ Finset.range (Ω N), ‖Λs‖⁻¹ ^ (j + 1) * (Real.log N * (Λ ^ (j + 1)) N) := by
  unfold xiCoeffJ
  refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (lamLogConv_nonneg j N)]
  exact mul_le_mul_of_nonneg_left (lamLogConv_le j N) (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _)

/-- the majorant  F_x(N) := Σ_{m=1}^{Ω N} x^m Λ^{∗m}(N)  (x = ‖Λ⋆‖⁻¹); indexing m = i+1, i < Ω N. -/
def Fmaj (x : ℝ) (N : ℕ) : ℝ := ∑ i ∈ Finset.range (Ω N), x ^ (i + 1) * (Λ ^ (i + 1)) N

lemma Fmaj_nonneg {x : ℝ} (hx : 0 ≤ x) (N : ℕ) : 0 ≤ Fmaj x N :=
  sum_nonneg fun _ _ => mul_nonneg (pow_nonneg hx _) (lamPow_nonneg _ _)

/-- like xiCoeff, Fmaj may be summed over any range ⊇ range (Ω N). -/
lemma Fmaj_eq_sum_range_of_le (x : ℝ) {N M : ℕ} (hM : Ω N ≤ M) :
    Fmaj x N = ∑ i ∈ Finset.range M, x ^ (i + 1) * (Λ ^ (i + 1)) N := by
  unfold Fmaj
  refine sum_subset (range_subset_range.mpr hM) fun j _ hj => ?_
  have : Ω N ≤ j := by simpa using hj
  rw [lamPow_eq_zero_of_cardFactors_lt (by omega), mul_zero]

/-- ‖C_J(N;Λ⋆)‖ ≤ log N · F_{‖Λ⋆‖⁻¹}(N). -/
lemma norm_xiCoeffJ_le (Λs : ℂ) (N : ℕ) : ‖xiCoeffJ Λs N‖ ≤ Real.log N * Fmaj ‖Λs‖⁻¹ N := by
  refine (norm_xiCoeffJ_le_aux Λs N).trans (le_of_eq ?_)
  unfold Fmaj
  rw [mul_sum]
  exact sum_congr rfl fun j _ => by ring

/-- ‖C(N;Λ⋆)‖ ≤ Λ(N) + log N · F_{‖Λ⋆‖⁻¹}(N). -/
lemma norm_xiCoeff_le (Λs : ℂ) (N : ℕ) :
    ‖xiCoeff Λs N‖ ≤ Λ N + Real.log N * Fmaj ‖Λs‖⁻¹ N := by
  unfold xiCoeff Fmaj
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  · refine (norm_sum_le _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun j _ => ?_
    rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (lamLogConv_nonneg j N)]
    calc ‖Λs‖⁻¹ ^ (j + 1) * lamLogConv j N ≤ ‖Λs‖⁻¹ ^ (j + 1) * (Real.log N * (Λ ^ (j + 1)) N) :=
          mul_le_mul_of_nonneg_left (lamLogConv_le j N) (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _)
      _ = Real.log N * (‖Λs‖⁻¹ ^ (j + 1) * (Λ ^ (j + 1)) N) := by ring

/-- squared form used by the diagonal sums: ‖C‖² ≤ 2Λ(N)² + 2 log²N · F_x(N)². -/
lemma norm_xiCoeff_sq_le (Λs : ℂ) (N : ℕ) :
    ‖xiCoeff Λs N‖ ^ 2 ≤ 2 * Λ N ^ 2 + 2 * (Real.log N) ^ 2 * Fmaj ‖Λs‖⁻¹ N ^ 2 := by
  have h := norm_xiCoeff_le Λs N
  have h0 : 0 ≤ ‖xiCoeff Λs N‖ := norm_nonneg _
  have hA : 0 ≤ Λ N := ArithmeticFunction.vonMangoldt_nonneg
  have hB : 0 ≤ Real.log N * Fmaj ‖Λs‖⁻¹ N :=
    mul_nonneg (Real.log_natCast_nonneg N) (Fmaj_nonneg (inv_nonneg.mpr (norm_nonneg _)) N)
  nlinarith [sq_nonneg (Λ N - Real.log N * Fmaj ‖Λs‖⁻¹ N), sq_abs ‖xiCoeff Λs N‖]

end XiPrime
end Zeta23
