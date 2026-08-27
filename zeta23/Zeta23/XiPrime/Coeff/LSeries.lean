/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Coeff/LSeries.lean — the L-series of the j-part of the ξ′ coefficients
(consumed by XiEF / [XF′ Thm 4.2]).

  C_J(N;Λ⋆) := Σ_{j<Ω N} Λ⋆^{-(j+1)} [(Λ·log) ∗ Λ^{∗j}](N)   (Basic.xiCoeffJ;  C = −Λ + C_J).
EXACT CONVOLUTION IDENTITY (finite telescoping in j, no analysis):   Λ⋆·C_J − Λ ∗ C_J = Λ·log.
Hence on any half plane of absolute convergence  L(C_J, s)·(Λ⋆ − A(s)) = B(s),  A = L(Λ), B = L(Λ·log), i.e.
  L(C_J, s) = B(s)/(Λ⋆ − A(s))      — the object E′/E ≈ B/(Λ⋆ − A) of the explicit formula.
Absolute bound on any line σ₀ > 1:  Σ_N ‖C_J(N)‖ N^{-σ₀} ≤ (4/(σ₀−1))·A(σ′)/‖Λ⋆‖  for ‖Λ⋆‖ ≥ R₀(σ₀) := 2A(σ′)+1,
σ′ := (σ₀+1)/2, A(σ) := Σ Λ(n) n^{-σ}  (log N ≤ N^ε/ε, F-majorant, the multiplicative weight N^{-σ′}); the line 5/4 (ξ′)
and the lines c ∈ [9/8, 5/4] (Z′) are instances.
-/
import Zeta23.XiPrime.Coeff.Upper
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Omega LSeries.notation
open Finset

noncomputable section

namespace Zeta23
namespace XiPrime

/-- Λ as a complex sequence. -/
def lamC : ℕ → ℂ := fun n => ((Λ n : ℝ) : ℂ)
/-- Λ·log as a complex sequence. -/
def lamLogC : ℕ → ℂ := fun n => ((Λ n * Real.log n : ℝ) : ℂ)

@[simp] lemma lamC_apply (n : ℕ) : lamC n = ((Λ n : ℝ) : ℂ) := rfl
@[simp] lemma lamLogC_apply (n : ℕ) : lamLogC n = ((Λ n * Real.log n : ℝ) : ℂ) := rfl

/-! ### the convolution identity  Λ⋆·C_J − Λ ∗ C_J = Λ·log -/

/-- lamLogConv 0 = Λ·log. -/
lemma lamLogConv_zero_apply (N : ℕ) : lamLogConv 0 N = Λ N * Real.log N := by
  rw [lamLogConv_eq, pow_zero, mul_one, lamLog_apply]

/-- Λ ∗ lamLogConv j = lamLogConv (j+1)  (commutativity of Dirichlet convolution). -/
lemma lam_mul_lamLogConv (j : ℕ) : (Λ : ArithmeticFunction ℝ) * lamLogConv j = lamLogConv (j + 1) := by
  rw [lamLogConv_eq, lamLogConv_eq, pow_succ, ← mul_assoc, mul_comm (Λ : ArithmeticFunction ℝ) lamLog,
    mul_assoc, mul_comm (Λ : ArithmeticFunction ℝ) (Λ ^ j)]

/-- the Dirichlet convolution (Λ ∗ C_J)(N), written through the fixed j-range Ω N. -/
lemma lamC_conv_xiCoeffJ (Λs : ℂ) (N : ℕ) :
    (lamC ⍟ xiCoeffJ Λs) N
      = ∑ j ∈ Finset.range (Ω N), (Λs⁻¹) ^ (j + 1) * ((lamLogConv (j + 1) N : ℝ) : ℂ) := by
  rw [LSeries.convolution_def]
  simp only
  have hexp : ∀ p ∈ N.divisorsAntidiagonal,
      lamC p.1 * xiCoeffJ Λs p.2
        = ∑ j ∈ Finset.range (Ω N), lamC p.1 * ((Λs⁻¹) ^ (j + 1) * ((lamLogConv j p.2 : ℝ) : ℂ)) := by
    intro p hp
    have hΩ : Ω p.2 ≤ Ω N := by
      have := cardFactors_of_mem_divisorsAntidiagonal hp; omega
    rw [xiCoeffJ_eq_sum_range_of_le Λs hΩ, mul_sum]
  rw [sum_congr rfl hexp, sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [← lam_mul_lamLogConv j, ArithmeticFunction.mul_apply]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun p _ => ?_
  simp only [lamC_apply]
  ring

/-- **the convolution identity**, pointwise:  Λ⋆·C_J(N) − (Λ ∗ C_J)(N) = Λ(N) log N  (Λ⋆ ≠ 0). -/
theorem xiCoeffJ_identity {Λs : ℂ} (hΛ : Λs ≠ 0) (N : ℕ) :
    Λs * xiCoeffJ Λs N - (lamC ⍟ xiCoeffJ Λs) N = lamLogC N := by
  rw [lamC_conv_xiCoeffJ]
  unfold xiCoeffJ
  rw [mul_sum]
  have h1 : ∀ j ∈ Finset.range (Ω N),
      Λs * ((Λs⁻¹) ^ (j + 1) * ((lamLogConv j N : ℝ) : ℂ)) = (Λs⁻¹) ^ j * ((lamLogConv j N : ℝ) : ℂ) := by
    intro j _
    calc Λs * ((Λs⁻¹) ^ (j + 1) * ((lamLogConv j N : ℝ) : ℂ))
        = (Λs * Λs⁻¹) * ((Λs⁻¹) ^ j * ((lamLogConv j N : ℝ) : ℂ)) := by rw [pow_succ]; ring
      _ = (Λs⁻¹) ^ j * ((lamLogConv j N : ℝ) : ℂ) := by rw [mul_inv_cancel₀ hΛ, one_mul]
  rw [sum_congr rfl h1, ← sum_sub_distrib,
    Finset.sum_range_sub' (fun j => (Λs⁻¹) ^ j * ((lamLogConv j N : ℝ) : ℂ)),
    lamLogConv_eq_zero_of_le (le_refl (Ω N)), lamLogConv_zero_apply]
  simp [lamLogC]

/-- the identity as an equality of sequences:  Λ·log = Λ⋆•C_J − Λ ∗ C_J. -/
lemma lamLogC_eq {Λs : ℂ} (hΛ : Λs ≠ 0) :
    lamLogC = (Λs • xiCoeffJ Λs) - (lamC ⍟ xiCoeffJ Λs) := by
  funext N
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact (xiCoeffJ_identity hΛ N).symm

/-! ### helpers -/

/-- the sequence  N ↦ ‖C_J(N)‖ N^{-5/4}  is nonnegative and vanishes at 0. -/
lemma norm_xiCoeffJ_rpow_nonneg (Λs : ℂ) (σ : ℝ) (N : ℕ) : 0 ≤ ‖xiCoeffJ Λs N‖ * (N : ℝ) ^ (-σ) :=
  mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg N) _)

lemma sum_range_le_sum_Ioc {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hf0 : f 0 = 0) (n : ℕ) :
    ∑ i ∈ range n, f i ≤ ∑ i ∈ Ioc 0 n, f i := by
  have hsub : range n ⊆ insert 0 (Ioc 0 n) := by
    intro i hi
    rw [mem_insert, mem_Ioc]
    rcases Nat.eq_zero_or_pos i with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, (mem_range.mp hi).le⟩
  calc ∑ i ∈ range n, f i ≤ ∑ i ∈ insert 0 (Ioc 0 n), f i :=
        sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hf i
    _ = ∑ i ∈ Ioc 0 n, f i := by rw [sum_insert (by simp), hf0, zero_add]

/-- ‖term f s n‖ for our sequences: ‖C_J(N)‖ N^{-Re s}. -/
lemma norm_term_xiCoeffJ (Λs s : ℂ) (N : ℕ) :
    ‖LSeries.term (fun N => xiCoeffJ Λs N) s N‖ = ‖xiCoeffJ Λs N‖ * (N : ℝ) ^ (-s.re) := by
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  · rw [if_neg hN, div_eq_mul_inv, Real.rpow_neg (Nat.cast_nonneg N)]

/-! ### lines Re s ≥ σ₀ > 1:  ε := (σ₀−1)/2,  log N ≤ N^ε/ε,  weight N^{−σ′}, σ′ = σ₀ − ε > 1 -/

section general
variable {σ₀ : ℝ}

/-- A(σ) := Σ' Λ(n) n^{−σ}. -/
def Asig (σ : ℝ) : ℝ := ∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ)

lemma summable_lam_rpow_of_gt_one {σ : ℝ} (hσ : 1 < σ) : Summable (fun n : ℕ => Λ n * (n : ℝ) ^ (-σ)) := by
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := ((σ : ℝ) : ℂ)) (by simp only [Complex.ofReal_re]; exact hσ)).norm
  refine h.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow (by linarith : (-σ) ≠ 0)]
  · rw [if_neg hn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Complex.ofReal_re, div_eq_mul_inv, Real.rpow_neg (Nat.cast_nonneg n)]

lemma lam_rpow_nonneg' (σ : ℝ) (n : ℕ) : 0 ≤ Λ n * (n : ℝ) ^ (-σ) :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)

lemma Asig_nonneg (σ : ℝ) : 0 ≤ Asig σ := tsum_nonneg (lam_rpow_nonneg' σ)

lemma sum_lam_rpow_le_Asig {σ : ℝ} (hσ : 1 < σ) (X : ℕ) :
    ∑ n ∈ Ioc 0 X, Λ n * (n : ℝ) ^ (-σ) ≤ Asig σ :=
  (summable_lam_rpow_of_gt_one hσ).sum_le_tsum _ fun n _ => lam_rpow_nonneg' σ n

/-- the auxiliary exponent σ′ := (σ₀+1)/2 ∈ (1, σ₀) and ε := (σ₀−1)/2. -/
def sigAux (σ₀ : ℝ) : ℝ := (σ₀ + 1) / 2

lemma one_lt_sigAux (hσ₀ : 1 < σ₀) : 1 < sigAux σ₀ := by unfold sigAux; linarith

/-- the threshold radius R₀(σ₀) := 2·A(σ′) + 1. -/
def R0sig (σ₀ : ℝ) : ℝ := 2 * Asig (sigAux σ₀) + 1

lemma R0sig_pos (σ₀ : ℝ) : 0 < R0sig σ₀ := by unfold R0sig; linarith [Asig_nonneg (sigAux σ₀)]

/-- partial sums on the line σ₀:  Σ_{N≤X} ‖C_J(N)‖ N^{−σ₀} ≤ (4/(σ₀−1))·A(σ′)/‖Λ⋆‖. -/
lemma sum_norm_xiCoeffJ_rpow_le_gen (hσ₀ : 1 < σ₀) {Λs : ℂ} (hΛ : R0sig σ₀ ≤ ‖Λs‖) (X : ℕ) :
    ∑ N ∈ Ioc 0 X, ‖xiCoeffJ Λs N‖ * (N : ℝ) ^ (-σ₀) ≤ (4 / (σ₀ - 1)) * Asig (sigAux σ₀) / ‖Λs‖ := by
  set ε : ℝ := (σ₀ - 1) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set σ' : ℝ := sigAux σ₀ with hσ'
  have hσ'1 : 1 < σ' := one_lt_sigAux hσ₀
  have hsplitexp : ε + -σ₀ = -σ' := by rw [hε, hσ', sigAux]; ring
  have hΛpos : 0 < ‖Λs‖ := lt_of_lt_of_le (R0sig_pos σ₀) hΛ
  set x : ℝ := ‖Λs‖⁻¹ with hxdef
  have hx0 : 0 ≤ x := by positivity
  set A : ℝ := Asig σ' with hA
  have hA0 : 0 ≤ A := Asig_nonneg σ'
  have hxA : x * A ≤ 1 / 2 := by
    rw [hxdef, inv_mul_le_iff₀ hΛpos]; unfold R0sig at hΛ; rw [← hσ', ← hA] at hΛ; linarith
  have hxA0 : 0 ≤ x * A := mul_nonneg hx0 hA0
  have hpt : ∀ N ∈ Ioc 0 X, ‖xiCoeffJ Λs N‖ * (N : ℝ) ^ (-σ₀)
      ≤ (1 / ε) * ∑ i ∈ range X, x ^ (i + 1) * ((Λ ^ (i + 1)) N * (N : ℝ) ^ (-σ')) := by
    intro N hN
    have hN0 : (0:ℝ) < N := by exact_mod_cast (mem_Ioc.mp hN).1
    have hΩ : Ω N ≤ X := (cardFactors_le_self N).trans (mem_Ioc.mp hN).2
    have h1 := norm_xiCoeffJ_le Λs N
    have hF0 : 0 ≤ Fmaj x N := Fmaj_nonneg hx0 N
    have hr0 : (0:ℝ) ≤ (N:ℝ) ^ (-σ₀) := Real.rpow_nonneg hN0.le _
    have hlog : Real.log N ≤ (1 / ε) * (N : ℝ) ^ ε := by
      have := Real.log_le_rpow_div (Nat.cast_nonneg N) hε0
      rw [div_eq_mul_one_div, mul_comm] at this
      exact this
    have hsplit : (N : ℝ) ^ ε * (N : ℝ) ^ (-σ₀) = (N : ℝ) ^ (-σ') := by
      rw [← Real.rpow_add hN0, hsplitexp]
    calc ‖xiCoeffJ Λs N‖ * (N : ℝ) ^ (-σ₀)
        ≤ (Real.log N * Fmaj x N) * (N : ℝ) ^ (-σ₀) := mul_le_mul_of_nonneg_right h1 hr0
      _ ≤ ((1 / ε) * (N : ℝ) ^ ε * Fmaj x N) * (N : ℝ) ^ (-σ₀) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlog hF0) hr0
      _ = (1 / ε) * (Fmaj x N * ((N : ℝ) ^ ε * (N : ℝ) ^ (-σ₀))) := by ring
      _ = (1 / ε) * (Fmaj x N * (N : ℝ) ^ (-σ')) := by rw [hsplit]
      _ = (1 / ε) * ∑ i ∈ range X, x ^ (i + 1) * ((Λ ^ (i + 1)) N * (N : ℝ) ^ (-σ')) := by
          rw [Fmaj_eq_sum_range_of_le x hΩ, sum_mul]
          congr 1; exact sum_congr rfl fun i _ => by ring
  have hε' : 0 ≤ 1 / ε := by positivity
  calc ∑ N ∈ Ioc 0 X, ‖xiCoeffJ Λs N‖ * (N : ℝ) ^ (-σ₀)
      ≤ ∑ N ∈ Ioc 0 X, (1 / ε) * ∑ i ∈ range X, x ^ (i + 1) * ((Λ ^ (i + 1)) N * (N : ℝ) ^ (-σ')) :=
        sum_le_sum hpt
    _ = (1 / ε) * ∑ i ∈ range X, x ^ (i + 1) * ∑ N ∈ Ioc 0 X, (Λ ^ (i + 1)) N * (N : ℝ) ^ (-σ') := by
        rw [← mul_sum, sum_comm]
        congr 1; exact sum_congr rfl fun i _ => by rw [mul_sum]
    _ ≤ (1 / ε) * ∑ i ∈ range X, x ^ (i + 1) * (∑ n ∈ Ioc 0 X, Λ n * (n : ℝ) ^ (-σ')) ^ (i + 1) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => ?_) hε'
        exact mul_le_mul_of_nonneg_left
          (sum_Ioc_pow_apply_le (SubmultWeight.rpow_neg σ') vonMangoldt_nonneg' X i) (pow_nonneg hx0 _)
    _ ≤ (1 / ε) * ∑ i ∈ range X, x ^ (i + 1) * A ^ (i + 1) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => ?_) hε'
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sum_nonneg fun n _ => lam_rpow_nonneg' σ' n)
          (sum_lam_rpow_le_Asig hσ'1 X) _) (pow_nonneg hx0 _)
    _ = (1 / ε) * ((x * A) * ∑ i ∈ range X, (x * A) ^ i) := by
        congr 1
        rw [mul_sum]
        exact sum_congr rfl fun i _ => by rw [mul_pow]; ring
    _ ≤ (1 / ε) * ((x * A) * 2) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hxA0) hε'
        calc ∑ i ∈ range X, (x * A) ^ i ≤ ∑ i ∈ range X, (1 / 2 : ℝ) ^ i :=
              sum_le_sum fun i _ => pow_le_pow_left₀ hxA0 hxA i
          _ ≤ 2 := sum_geometric_two_le X
    _ = (4 / (σ₀ - 1)) * A / ‖Λs‖ := by
        rw [hxdef, hε]
        have : σ₀ - 1 ≠ 0 := by linarith
        field_simp
        ring

/-- summability on the line σ₀. -/
lemma summable_norm_xiCoeffJ_gen (hσ₀ : 1 < σ₀) {Λs : ℂ} (hΛ : R0sig σ₀ ≤ ‖Λs‖) :
    Summable (fun N : ℕ => ‖xiCoeffJ Λs N‖ * (N : ℝ) ^ (-σ₀)) := by
  have hf : ∀ N, 0 ≤ ‖xiCoeffJ Λs N‖ * (N : ℝ) ^ (-σ₀) := norm_xiCoeffJ_rpow_nonneg Λs σ₀
  have hf0 : ‖xiCoeffJ Λs 0‖ * ((0:ℕ) : ℝ) ^ (-σ₀) = 0 := by simp
  exact summable_of_sum_range_le hf fun n =>
    (sum_range_le_sum_Ioc hf hf0 n).trans (sum_norm_xiCoeffJ_rpow_le_gen hσ₀ hΛ n)

/-- **(C2) on any line σ₀ > 1.** -/
theorem norm_xiCoeffJ_tsum_le_of_gt_one (σ₀ : ℝ) (hσ₀ : 1 < σ₀) :
    ∃ R₀ C : ℝ, 0 < R₀ ∧ ∀ Λs : ℂ, R₀ ≤ ‖Λs‖ →
      Summable (fun N : ℕ => ‖xiCoeffJ Λs N‖ * (N : ℝ) ^ (-σ₀)) ∧
      ∑' N, ‖xiCoeffJ Λs N‖ * (N : ℝ) ^ (-σ₀) ≤ C / ‖Λs‖ := by
  refine ⟨R0sig σ₀, (4 / (σ₀ - 1)) * Asig (sigAux σ₀), R0sig_pos σ₀, fun Λs hΛ => ?_⟩
  have hf : ∀ N, 0 ≤ ‖xiCoeffJ Λs N‖ * (N : ℝ) ^ (-σ₀) := norm_xiCoeffJ_rpow_nonneg Λs σ₀
  have hf0 : ‖xiCoeffJ Λs 0‖ * ((0:ℕ) : ℝ) ^ (-σ₀) = 0 := by simp
  have hbound : ∀ n, ∑ i ∈ range n, ‖xiCoeffJ Λs i‖ * (i : ℝ) ^ (-σ₀)
      ≤ (4 / (σ₀ - 1)) * Asig (sigAux σ₀) / ‖Λs‖ :=
    fun n => (sum_range_le_sum_Ioc hf hf0 n).trans (sum_norm_xiCoeffJ_rpow_le_gen hσ₀ hΛ n)
  exact ⟨summable_of_sum_range_le hf hbound, Real.tsum_le_of_sum_range_le hf hbound⟩

/-- summability of ‖C_J‖·N^{−σ} for σ ≥ σ₀. -/
lemma summable_norm_xiCoeffJ_rpow_gen (hσ₀ : 1 < σ₀) {Λs : ℂ} (hΛ : R0sig σ₀ ≤ ‖Λs‖) {σ : ℝ} (hσ : σ₀ ≤ σ) :
    Summable (fun N : ℕ => ‖xiCoeffJ Λs N‖ * (N : ℝ) ^ (-σ)) := by
  refine (summable_norm_xiCoeffJ_gen hσ₀ hΛ).of_nonneg_of_le (norm_xiCoeffJ_rpow_nonneg Λs σ) fun N => ?_
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hσ0 : -σ ≠ 0 := by linarith
    simp [Real.zero_rpow hσ0]
  · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)

/-- ‖A(s)‖ ≤ A(σ′) for Re s ≥ σ₀. -/
lemma norm_LSeries_lamC_le_gen (hσ₀ : 1 < σ₀) {s : ℂ} (hs : σ₀ ≤ s.re) :
    ‖LSeries lamC s‖ ≤ Asig (sigAux σ₀) := by
  have hσ'1 : 1 < sigAux σ₀ := one_lt_sigAux hσ₀
  have hσ' : sigAux σ₀ ≤ σ₀ := by unfold sigAux; linarith
  have hΛC : LSeriesSummable lamC s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by linarith : 1 < s.re)
  unfold LSeries
  refine (norm_tsum_le_tsum_norm hΛC.norm).trans ?_
  refine hΛC.norm.tsum_le_tsum (fun n => ?_) (summable_lam_rpow_of_gt_one hσ'1)
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, lamC_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n)]
    refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.pos_of_ne_zero hn) (by linarith)

/-- **(C1) the closed form on any line σ₀ > 1**:  L(C_J, s) = B(s)/(Λ⋆ − A(s))  for σ₀ ≤ Re s, ‖Λ⋆‖ ≥ R₀(σ₀). -/
theorem LSeries_xiCoeffJ_of_gt_one (σ₀ : ℝ) (hσ₀ : 1 < σ₀) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ Λs : ℂ, R₀ ≤ ‖Λs‖ → ∀ s : ℂ, σ₀ ≤ s.re →
      Summable (fun N : ℕ => ‖xiCoeffJ Λs N‖ * (N : ℝ) ^ (-s.re)) ∧
      Λs - LSeries (fun n => ((Λ n : ℝ) : ℂ)) s ≠ 0 ∧
      LSeries (fun N => xiCoeffJ Λs N) s
        = LSeries (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) s / (Λs - LSeries (fun n => ((Λ n : ℝ) : ℂ)) s) := by
  refine ⟨R0sig σ₀, R0sig_pos σ₀, fun Λs hΛ s hs => ?_⟩
  have hΛpos : 0 < ‖Λs‖ := lt_of_lt_of_le (R0sig_pos σ₀) hΛ
  have hΛ0 : Λs ≠ 0 := norm_pos_iff.mp hΛpos
  have hsumσ := summable_norm_xiCoeffJ_rpow_gen hσ₀ hΛ hs
  have hCJ : LSeriesSummable (fun N => xiCoeffJ Λs N) s := by
    refine Summable.of_norm ?_
    exact hsumσ.congr fun N => (norm_term_xiCoeffJ Λs s N).symm
  have hΛC : LSeriesSummable lamC s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by linarith : 1 < s.re)
  have hconv : LSeriesSummable (lamC ⍟ (fun N => xiCoeffJ Λs N)) s :=
    (LSeriesHasSum.convolution hΛC.LSeriesHasSum hCJ.LSeriesHasSum).LSeriesSummable
  have hsmul : LSeriesSummable (Λs • (fun N => xiCoeffJ Λs N)) s := hCJ.smul Λs
  have hA := norm_LSeries_lamC_le_gen hσ₀ hs
  have hne : Λs - LSeries lamC s ≠ 0 := by
    intro h
    have : ‖Λs‖ = ‖LSeries lamC s‖ := by rw [sub_eq_zero.mp h]
    unfold R0sig at hΛ; linarith [Asig_nonneg (sigAux σ₀)]
  have hB : LSeries lamLogC s = LSeries (fun N => xiCoeffJ Λs N) s * (Λs - LSeries lamC s) := by
    have hfun : lamLogC = (Λs • (fun N => xiCoeffJ Λs N)) - (lamC ⍟ (fun N => xiCoeffJ Λs N)) :=
      lamLogC_eq hΛ0
    rw [hfun, LSeries_sub hsmul hconv, LSeries_smul, LSeries_convolution' hΛC hCJ]
    ring
  refine ⟨hsumσ, hne, ?_⟩
  change LSeries (fun N => xiCoeffJ Λs N) s = LSeries lamLogC s / (Λs - LSeries lamC s)
  rw [eq_div_iff hne, hB]

end general

/-! ### the line Re s = 5/4 (the ξ′ explicit formula's contour): instances of the general statements -/

/-- **(C2) absolute bound** at 5/4:  Σ' ‖C_J(N;Λ⋆)‖ N^{-5/4} ≤ C/‖Λ⋆‖ for ‖Λ⋆‖ ≥ R₀ (with summability). -/
theorem norm_xiCoeffJ_tsum_le : ∃ R₀ C : ℝ, 0 < R₀ ∧ ∀ Λs : ℂ, R₀ ≤ ‖Λs‖ →
    Summable (fun N : ℕ => ‖xiCoeffJ Λs N‖ * (N : ℝ) ^ (-(5/4 : ℝ))) ∧
    ∑' N, ‖xiCoeffJ Λs N‖ * (N : ℝ) ^ (-(5/4 : ℝ)) ≤ C / ‖Λs‖ :=
  norm_xiCoeffJ_tsum_le_of_gt_one (5/4) (by norm_num)

/-- **(C1) the closed form** at 5/4:  L(C_J, s) = B(s)/(Λ⋆ − A(s))  for 5/4 ≤ Re s and ‖Λ⋆‖ ≥ R₀. -/
theorem LSeries_xiCoeffJ : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ Λs : ℂ, R₀ ≤ ‖Λs‖ → ∀ s : ℂ, 5 / 4 ≤ s.re →
    Summable (fun N : ℕ => ‖xiCoeffJ Λs N‖ * (N : ℝ) ^ (-s.re)) ∧
    Λs - LSeries (fun n => ((Λ n : ℝ) : ℂ)) s ≠ 0 ∧
    LSeries (fun N => xiCoeffJ Λs N) s
      = LSeries (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) s / (Λs - LSeries (fun n => ((Λ n : ℝ) : ℂ)) s) :=
  LSeries_xiCoeffJ_of_gt_one (5/4) (by norm_num)

end XiPrime
end Zeta23
