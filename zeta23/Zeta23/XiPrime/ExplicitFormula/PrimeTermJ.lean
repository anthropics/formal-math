/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ExplicitFormula/PrimeTermJ.lean — the prime term of the explicit formula with COMPLEX coefficients
(generalises Zeta23.EF.prime_term of Zeta23/ExplicitFormula.lean).

For k continuous with supp k ⊆ [−L, L], 𝓕k integrable, and any c : ℕ → ℂ:
  Σ_N (c_N k(log N) + c̄_N k(−log N))/√N = ∫ h_k(τ) · P_c(e^L; τ) dτ,
  P_c(X;τ) = (1/π) Σ_{N ≤ X} (Re c_N cos(τ log N) + Im c_N sin(τ log N))/√N   (Zeta23.XiPrime.Pc),
by inversion k(u) = (1/2π)∫ h(r)e^{−iru}dr twice and  c e^{−iθ} + c̄ e^{iθ} = 2(Re c·cos θ + Im c·sin θ).
Also: integrability of h·P_c, additivity of P_c in c, P_{−Λ} = P_X (Zeta23.PX), and hence
ν_c(X) for c = C(·;Λ⋆) splits as ν_X + P_{C+Λ}(X) (nuc_xiCoeff_eq').
-/
import Zeta23.ExplicitFormula
import Zeta23.XiPrime.Defs

open MeasureTheory Complex Filter Set
open scoped Real FourierTransform ComplexConjugate ArithmeticFunction

noncomputable section

namespace Zeta23
namespace XiPrime

open Zeta23.EF

/-- h(r)·sin(r y) is integrable in r when h is. -/
theorem integrable_paperFT_mul_sin {k : ℝ → ℂ} (hFk : Integrable (𝓕 k)) (y : ℝ) :
    Integrable (fun r : ℝ => paperFT k r * (Real.sin (r * y) : ℂ)) := by
  refine (integrable_paperFT_ofReal hFk).mul_bdd (c := 1) (by fun_prop) ?_
  filter_upwards with r
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_sin_le_one _

/-- the real trigonometric combination attached to a complex coefficient. -/
theorem integrable_paperFT_mul_trig {k : ℝ → ℂ} (hFk : Integrable (𝓕 k)) (c : ℂ) (y : ℝ) :
    Integrable (fun r : ℝ => paperFT k r * ((c.re * Real.cos (r * y) + c.im * Real.sin (r * y) : ℝ) : ℂ)) := by
  have h := ((integrable_paperFT_mul_cos hFk y).const_mul (c.re : ℂ)).add
    ((integrable_paperFT_mul_sin hFk y).const_mul (c.im : ℂ))
  refine h.congr ?_
  filter_upwards with r
  simp only [Pi.add_apply, Complex.ofReal_add, Complex.ofReal_mul]
  ring

/-- c e^{−iθ} + c̄ e^{iθ} = 2 (Re c · cos θ + Im c · sin θ). -/
theorem mul_cexp_add_conj_mul_cexp (c : ℂ) (θ : ℝ) :
    c * cexp (-I * θ) + conj c * cexp (I * θ) = 2 * ((c.re * Real.cos θ + c.im * Real.sin θ : ℝ) : ℂ) := by
  have e1 : cexp (-I * θ) = Real.cos θ - I * Real.sin θ := by
    rw [show -I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  have e2 : cexp (I * θ) = Real.cos θ + I * Real.sin θ := by
    rw [show I * (θ : ℂ) = (θ : ℂ) * I by ring, Complex.exp_mul_I]
    push_cast
    ring
  rw [e1, e2]
  apply Complex.ext
  · simp
    ring
  · simp
    ring

/-- **c·k(y) + c̄·k(−y) = (1/π) ∫ h(τ) (Re c · cos(τy) + Im c · sin(τy)) dτ.** -/
theorem c_mul_k_add_conj_mul_k_neg {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (𝓕 k)) (c : ℂ) (y : ℝ) :
    c * k y + conj c * k (-y)
      = (1 / π : ℂ) * ∫ τ : ℝ, paperFT k τ * ((c.re * Real.cos (τ * y) + c.im * Real.sin (τ * y) : ℝ) : ℂ) := by
  rw [paper_inversion hk hki hFk y, paper_inversion hk hki hFk (-y)]
  have hI1 := (integrable_paperFT_mul_cexp hFk y).const_mul c
  have hI2 := (integrable_paperFT_mul_cexp hFk (-y)).const_mul (conj c)
  have e : c * ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * cexp (-I * r * y))
      + conj c * ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * cexp (-I * r * ↑(-y)))
      = (1 / (2 * π) : ℂ) * ((∫ r : ℝ, c * (paperFT k r * cexp (-I * r * y)))
          + ∫ r : ℝ, conj c * (paperFT k r * cexp (-I * r * ↑(-y)))) := by
    rw [cintegral_const_mul, cintegral_const_mul]
    ring
  rw [e, ← integral_add hI1 hI2]
  have h2 : ∀ τ : ℝ, c * (paperFT k τ * cexp (-I * τ * y)) + conj c * (paperFT k τ * cexp (-I * τ * ↑(-y)))
      = 2 * (paperFT k τ * ((c.re * Real.cos (τ * y) + c.im * Real.sin (τ * y) : ℝ) : ℂ)) := by
    intro τ
    have key := mul_cexp_add_conj_mul_cexp c (τ * y)
    have a1 : -I * (τ : ℂ) * (y : ℂ) = -I * ((τ * y : ℝ) : ℂ) := by push_cast; ring
    have a2 : -I * (τ : ℂ) * ((-y : ℝ) : ℂ) = I * ((τ * y : ℝ) : ℂ) := by push_cast; ring
    rw [a1, a2]
    calc c * (paperFT k τ * cexp (-I * ↑(τ * y))) + conj c * (paperFT k τ * cexp (I * ↑(τ * y)))
        = paperFT k τ * (c * cexp (-I * ↑(τ * y)) + conj c * cexp (I * ↑(τ * y))) := by ring
      _ = 2 * (paperFT k τ * ((c.re * Real.cos (τ * y) + c.im * Real.sin (τ * y) : ℝ) : ℂ)) := by
          rw [key]; ring
  simp_rw [h2]
  rw [cintegral_const_mul, ← mul_assoc]
  congr 1
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- support step: for N ∉ (0, e^L] the N-th summand vanishes (√0 = 0 in Lean for N = 0; k(±log N) = 0 for N > e^L). -/
theorem complex_summand_eq_zero {k : ℝ → ℂ} {L : ℝ} (hks : tsupport k ⊆ Icc (-L) L) (c : ℕ → ℂ)
    {N : ℕ} (hN : N ∉ Finset.Ioc 0 ⌊Real.exp L⌋₊) :
    (c N * k (Real.log N) + conj (c N) * k (-Real.log N)) / ((Real.sqrt N : ℝ) : ℂ) = 0 := by
  rcases Nat.eq_zero_or_pos N with rfl | hpos
  · simp
  · have hn' : ⌊Real.exp L⌋₊ < N := by
      simp only [Finset.mem_Ioc, not_and, not_le] at hN
      exact hN hpos
    have hX : Real.exp L < N := (Nat.floor_lt (Real.exp_pos L).le).mp hn'
    have hlog : L < Real.log N := by
      rw [← Real.log_exp L]
      exact Real.log_lt_log (Real.exp_pos L) hX
    have h1 : k (Real.log N) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem; have := (hks hmem).2; linarith
    have h2 : k (-Real.log N) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem; have := (hks hmem).1; linarith
    rw [h1, h2, mul_zero, mul_zero, add_zero, zero_div]

theorem paperFT_mul_Pc_eq (k : ℝ → ℂ) (L : ℝ) (c : ℕ → ℂ) :
    (fun τ : ℝ => paperFT k τ * ((Pc (Real.exp L) c τ : ℝ) : ℂ))
      = fun τ : ℝ => ∑ N ∈ Finset.Ioc 0 ⌊Real.exp L⌋₊,
          ((1 / π : ℂ) / ((Real.sqrt N : ℝ) : ℂ)) *
            (paperFT k τ * (((c N).re * Real.cos (τ * Real.log N) + (c N).im * Real.sin (τ * Real.log N) : ℝ) : ℂ)) := by
  ext τ
  simp only [Pc]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun N _ => ?_
  ring

/-- h·P_c(e^L) is integrable. -/
theorem integrable_paperFT_mul_Pc {k : ℝ → ℂ} (L : ℝ) (hFk : Integrable (𝓕 k)) (c : ℕ → ℂ) :
    Integrable (fun τ : ℝ => paperFT k τ * ((Pc (Real.exp L) c τ : ℝ) : ℂ)) := by
  rw [paperFT_mul_Pc_eq]
  exact integrable_finset_sum _ (fun N _ => (integrable_paperFT_mul_trig hFk (c N) _).const_mul _)

/-- **Prime term with complex coefficients.**  For k continuous with supp k ⊆ [−L, L], 𝓕k integrable, c : ℕ → ℂ:
Σ_N (c_N k(log N) + c̄_N k(−log N))/√N = ∫ h_k(τ) P_c(e^L; τ) dτ. -/
theorem prime_term_complex {k : ℝ → ℂ} {L : ℝ} (hk : Continuous k) (hks : tsupport k ⊆ Icc (-L) L)
    (hFk : Integrable (𝓕 k)) (c : ℕ → ℂ) :
    (∑' N : ℕ, (c N * k (Real.log N) + conj (c N) * k (-Real.log N)) / ((Real.sqrt N : ℝ) : ℂ))
      = ∫ τ : ℝ, paperFT k τ * ((Pc (Real.exp L) c τ : ℝ) : ℂ) := by
  have hki : Integrable k :=
    hk.integrable_of_hasCompactSupport (hasCompactSupport_of_tsupport_subset hks)
  set S := Finset.Ioc 0 ⌊Real.exp L⌋₊ with hS
  rw [tsum_eq_sum (s := S) (fun N hN => complex_summand_eq_zero hks c hN)]
  have step1 : ∑ N ∈ S, (c N * k (Real.log N) + conj (c N) * k (-Real.log N)) / ((Real.sqrt N : ℝ) : ℂ)
      = ∑ N ∈ S, ((1 / π : ℂ) * ∫ τ : ℝ, paperFT k τ *
          (((c N).re * Real.cos (τ * Real.log N) + (c N).im * Real.sin (τ * Real.log N) : ℝ) : ℂ))
            / ((Real.sqrt N : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun N _ => ?_
    rw [c_mul_k_add_conj_mul_k_neg hk hki hFk]
  rw [step1, paperFT_mul_Pc_eq, integral_finset_sum _
    (fun N _ => (integrable_paperFT_mul_trig hFk (c N) _).const_mul _)]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [cintegral_const_mul]
  ring

/-! ### algebra of P_c -/

theorem Pc_add (X : ℝ) (c₁ c₂ : ℕ → ℂ) (τ : ℝ) :
    Pc X (fun N => c₁ N + c₂ N) τ = Pc X c₁ τ + Pc X c₂ τ := by
  simp only [Pc, Complex.add_re, Complex.add_im, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun N _ => ?_
  ring

theorem Pc_congr {X : ℝ} {c₁ c₂ : ℕ → ℂ} (h : ∀ N ∈ Finset.Ioc 0 ⌊X⌋₊, c₁ N = c₂ N) (τ : ℝ) :
    Pc X c₁ τ = Pc X c₂ τ := by
  simp only [Pc]
  congr 1
  exact Finset.sum_congr rfl fun N hN => by rw [h N hN]

/-- P_{−Λ}(X) = P_X. -/
theorem Pc_neg_vonMangoldt (X τ : ℝ) : Pc X (fun N => -((Λ N : ℝ) : ℂ)) τ = PX X τ := by
  simp only [Pc, PX, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, neg_zero,
    zero_mul, add_zero]
  rw [neg_mul, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun N _ => ?_
  ring

/-- ν_c(X) for the ξ′ coefficients c = C(·;Λ⋆) = −Λ + (C + Λ):  ν_c = ν_X + P_{C+Λ}(X). -/
theorem nuc_xiCoeff_eq' (X : ℝ) (Λs : ℂ) (τ : ℝ) :
    nuc X (xiCoeff Λs) τ = nuX X τ + Pc X (fun N => xiCoeff Λs N + ((Λ N : ℝ) : ℂ)) τ := by
  have hsplit : Pc X (xiCoeff Λs) τ
      = Pc X (fun N => -((Λ N : ℝ) : ℂ)) τ + Pc X (fun N => xiCoeff Λs N + ((Λ N : ℝ) : ℂ)) τ := by
    rw [← Pc_add]
    exact Pc_congr (fun N _ => by ring) τ
  simp only [nuc, nucW, nuX, one_mul]
  rw [hsplit, Pc_neg_vonMangoldt]
  ring

end XiPrime
end Zeta23
