/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization.

Zeta23/XiPrime/PrimeSide/Trace.lean — generalised-coefficient prime side:
[prop:trace] for the density ν = μ + cΠ·Π_X + P_c with ARBITRARY complex coefficients:
    |tr G̃(ν) − a L N| ≤ C · (L √X + L · S₁(c)),      S₁(c) = Σ_{N≤X} ‖c_N‖/√N,
for T ≥ T₀ and every N with |N − Tℓ₁/2π| ≤ A·l (C, T₀ depend on cϱ, λ, A, cΠ, H-Γ), c 1 = 0.

Route: BY DIFFERENCE from the ζ result PrimeSide.prop_trace (tr G̃(ν_X) = aLN + O(L√X), proved,
with the proved Chebyshev bound): ν − ν_X = (cΠ−1)Π_X + (P_c − P_X), and the grid sums of
the Π-part (Pi_part_bound), the P_X-part (sum_P_part_bound) and the P_c-part (complex grid kernel
Aphi_mul_norm_tauKernel_le of ThmE/PrimeSideChi, here with weights ‖c_N‖/√N) are each O(L²√X)
resp. O(L² S₁).
-/
import Zeta23.XiPrime.PrimeSide.Density
import Zeta23.ThmE.PrimeSideChi

noncomputable section

open Real Filter MeasureTheory Set Finset
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace XiPrime

open PrimeSide ThmE

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

/-- Integrability of `φ̂(r)² P_c(t+r)` (bounded × integrable). -/
lemma Pc_part_integrable (hF : LocalHypsCore cϱ p F) (c : ℕ → ℂ) (t : ℝ) :
    Integrable (fun r => F.phiHat r ^ 2 * Pc p.X c (t + r)) :=
  hF.phiHat_sq_mul_integrable_of_bdd ((Pc_continuous p.X c).comp (continuous_const_add t))
    (fun x => Pc_abs_le p.X c (t + x))

/-- **P_c-part of [prop:trace] at one grid point** (mirror of ThmE.P_part_chi_eq):
`∫ φ̂(r)² P_c(t+r) dr = 2 Σ_{N≤X} (√N)⁻¹ A_φ(log N)·(Re c_N cos(t log N) + Im c_N sin(t log N))`. -/
lemma Pc_part_eq (hF : LocalHypsCoreW cϱ p F) (c : ℕ → ℂ) (t : ℝ) :
    ∫ r, F.phiHat r ^ 2 * Pc p.X c (t + r)
      = 2 * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Real.sqrt n)⁻¹ * F.Aphi (Real.log n)
          * ((c n).re * Real.cos (t * Real.log n) + (c n).im * Real.sin (t * Real.log n)) := by
  have h1 : (fun r => F.phiHat r ^ 2 * Pc p.X c (t + r))
      = fun r => ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
          ((1 / Real.pi) * (Real.sqrt n)⁻¹)
            * ((c n).re * (F.phiHat r ^ 2 * Real.cos ((t + r) * Real.log n))
              + (c n).im * (F.phiHat r ^ 2 * Real.sin ((t + r) * Real.log n))) := by
    funext r
    unfold Pc
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [div_eq_mul_inv]
    ring
  rw [h1, MeasureTheory.integral_finset_sum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      integral_phiHat_sq_mul_cos_shift_core hF, integral_phiHat_sq_mul_sin_shift_core hF]
    · have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
    · exact (hF.phiHat_sq_mul_integrable_of_bdd (by fun_prop)
        (fun x => Real.abs_cos_le_one _)).const_mul _
    · exact (hF.phiHat_sq_mul_integrable_of_bdd (by fun_prop)
        (fun x => Real.abs_sin_le_one _)).const_mul _
  · intro n _
    exact (((hF.phiHat_sq_mul_integrable_of_bdd (by fun_prop)
        (fun x => Real.abs_cos_le_one _)).const_mul _).add
      ((hF.phiHat_sq_mul_integrable_of_bdd (by fun_prop)
        (fun x => Real.abs_sin_le_one _)).const_mul _)).const_mul _

/-- **Sum of the P_c-parts over the grid** (mirror of ThmE.sum_P_part_chi_bound with weights
`‖c_N‖/√N`): `|Σ_{k<d} ∫ φ̂(r)² P_c(τ_k + r) dr| ≤ (L²/log 2) · S₁(c; X)`, provided `c 1 = 0`. -/
lemma sum_Pc_part_bound (hF : LocalHypsCoreW cϱ p F) {c : ℕ → ℂ} (hc1 : c 1 = 0) :
    |∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * Pc p.X c (p.tau k + r)|
      ≤ p.L ^ 2 / Real.log 2 * S1 c p.X := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  simp_rw [Pc_part_eq hF c]
  rw [← Finset.mul_sum, Finset.sum_comm, abs_mul, abs_two]
  have hterm : ∀ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
      |∑ k ∈ Finset.range p.d, (Real.sqrt n)⁻¹ * F.Aphi (Real.log n)
          * ((c n).re * Real.cos (p.tau k * Real.log n)
            + (c n).im * Real.sin (p.tau k * Real.log n))|
        ≤ ‖c n‖ / Real.sqrt n * (p.L ^ 2 / (2 * Real.log 2)) := by
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Ioc.1 hn).1
    have hs0 : (0:ℝ) ≤ (Real.sqrt n)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have hn1 : n = 1 := by omega
      subst hn1
      simp [hc1]
    · have hre : ∀ θ : ℝ, (c n).re * Real.cos θ + (c n).im * Real.sin θ
          = (c n * Complex.exp ((-θ : ℝ) * Complex.I)).re := by
        intro θ
        rw [show ((-θ : ℝ) : ℂ) = -(θ : ℂ) by push_cast; ring]
        rw [show (-(θ:ℂ)) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
        rw [Complex.exp_mul_I]
        simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
          Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
          Complex.sin_ofReal_im, Real.cos_neg, Real.sin_neg, Complex.I_re, Complex.I_im]
        ring
      have hsum_eq : ∑ k ∈ Finset.range p.d, (Real.sqrt n)⁻¹ * F.Aphi (Real.log n)
            * ((c n).re * Real.cos (p.tau k * Real.log n)
              + (c n).im * Real.sin (p.tau k * Real.log n))
          = (Real.sqrt n)⁻¹ * (F.Aphi (Real.log n)
              * (c n * ∑ k ∈ Finset.range p.d,
                  Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re) := by
        rw [Finset.mul_sum, Complex.re_sum]
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hre (p.tau k * Real.log n)]
        ring
      rw [hsum_eq, abs_mul, abs_of_nonneg hs0, div_eq_mul_inv, mul_comm (‖c n‖), mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hs0
      have hy : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn2)
      have hA0 := hF.Aphi_nonneg (Real.log n)
      calc |F.Aphi (Real.log n) * (c n * ∑ k ∈ Finset.range p.d,
              Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re|
          = F.Aphi (Real.log n) * |(c n * ∑ k ∈ Finset.range p.d,
              Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re| := by
            rw [abs_mul, abs_of_nonneg hA0]
        _ ≤ F.Aphi (Real.log n) * (‖c n‖ * ‖∑ k ∈ Finset.range p.d,
              Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)‖) := by
            gcongr
            exact (Complex.abs_re_le_norm _).trans (norm_mul_le _ _)
        _ = ‖c n‖ * (F.Aphi (Real.log n) * ‖∑ k ∈ Finset.range p.d,
              Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)‖) := by ring
        _ ≤ ‖c n‖ * (p.L ^ 2 / (2 * Real.log 2)) :=
            mul_le_mul_of_nonneg_left (Aphi_mul_norm_tauKernel_le hF hy) (norm_nonneg _)
  calc 2 * |∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, ∑ k ∈ Finset.range p.d,
          (Real.sqrt n)⁻¹ * F.Aphi (Real.log n)
          * ((c n).re * Real.cos (p.tau k * Real.log n)
            + (c n).im * Real.sin (p.tau k * Real.log n))|
      ≤ 2 * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, |∑ k ∈ Finset.range p.d,
          (Real.sqrt n)⁻¹ * F.Aphi (Real.log n)
          * ((c n).re * Real.cos (p.tau k * Real.log n)
            + (c n).im * Real.sin (p.tau k * Real.log n))| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ 2 * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, ‖c n‖ / Real.sqrt n * (p.L ^ 2 / (2 * Real.log 2)) := by
        gcongr with n hn
        exact hterm n hn
    _ = p.L ^ 2 / Real.log 2 * S1 c p.X := by
        rw [← Finset.sum_mul]
        unfold S1
        field_simp

/-- **Decomposition of a diagonal entry for ν** (mirror of GentryA_diag_eq):
`G_kk(ν) = G^μ_kk + cΠ·G^Π_kk + G^{P_c}_kk` after translating `τ = τ_k + r`. -/
lemma GentryW_diag_eq (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p F) (cPi : ℝ) (c : ℕ → ℂ)
    (k : ℤ) (hk : 0 < p.tau k) :
    GentryW cPi c p F k k = (∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r))
      + cPi * (∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r))
      + (∫ r, F.phiHat r ^ 2 * Pc p.X c (p.tau k + r)) := by
  show (∫ τ, F.phiHat (τ - p.tau k) * F.phiHat (τ - p.tau k) * nucW cPi p.X c τ) = _
  have htrans : (∫ τ, F.phiHat (τ - p.tau k) * F.phiHat (τ - p.tau k) * nucW cPi p.X c τ)
      = ∫ r, F.phiHat r ^ 2 * nucW cPi p.X c (p.tau k + r) := by
    rw [← integral_add_right_eq_self _ (p.tau k)]
    congr 1; funext r; simp only [add_sub_cancel_right]; ring_nf
  rw [htrans]
  have hν : ∀ r, F.phiHat r ^ 2 * nucW cPi p.X c (p.tau k + r)
      = (F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r)
          + cPi * (F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r)))
        + F.phiHat r ^ 2 * Pc p.X c (p.tau k + r) := by
    intro r; simp only [nucW]; ring
  simp_rw [hν]
  have h2 : Integrable (fun r => cPi * (F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r))) :=
    (Pi_part_integrable hF _).const_mul cPi
  have h12 : Integrable (fun r => F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r)
      + cPi * (F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r))) :=
    (mu_part_integrable hΓ hF hk).add h2
  rw [integral_add h12 (Pc_part_integrable hF c _),
    integral_add (mu_part_integrable hΓ hF hk) h2, integral_const_mul]

set_option maxHeartbeats 1600000 in
/-- **[prop:trace] for ν = μ + cΠ·Π_X + P_c** with arbitrary complex coefficients (`c 1 = 0`):
`|tr G̃(ν) − a L N| ≤ C · (L √X + L · S₁(c; X))` for `T ≥ T₀` and every `N` with
`|N − Tℓ₁/2π| ≤ A·l`.  Constants depend on (cϱ, λ, A, cΠ, H-Γ); the Chebyshev bound used is
`Zeta23.Cheb.chebyshevMertens`. -/
theorem prop_trace_W (cϱ lam : ℝ) (hΓ : Zeta23.GammaFacts) (hlam : 0 < lam ∧ lam ≤ 1)
    (cPi A : ℝ) :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (c : ℕ → ℂ), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCore cϱ p F → c 1 = 0 → ∀ N : ℝ, |N - p.T * p.ell1 / (2 * π)| ≤ A * p.l →
      |trGtW cPi c p F - F.a * p.L * N| ≤ C * (p.L * Real.sqrt p.X + p.L * S1 c p.X) := by
  have hcheb := Zeta23.Cheb.chebyshevMertens
  obtain ⟨C₀, T₀, hC₀⟩ := PrimeSide.prop_trace cϱ lam hΓ hcheb hlam A
  obtain ⟨x₀, hx₀⟩ := hcheb.cheb1b
  refine ⟨|C₀| + |cPi - 1| * (12 * π + 96 + 24 * cϱ ^ 2) + 3 / Real.log 2 + 1 / Real.log 2,
    max (max T₀ 4) (2 * π * Real.exp (|x₀| / lam)), fun p F c hplam hT hF hc1 N hN => ?_⟩
  have hTa : max T₀ 4 ≤ p.T := (le_max_left _ _).trans hT
  have hT₀' : T₀ ≤ p.T := (le_max_left _ _).trans hTa
  have hT4 : 4 ≤ p.T := (le_max_right _ _).trans hTa
  have hTx : 2 * π * Real.exp (|x₀| / lam) ≤ p.T := (le_max_right _ _).trans hT
  have hT0 : 0 < p.T := by linarith
  have h0 := hC₀ p F hplam hT₀' hF N hN
  have hL := hF.L_pos
  have hc4 := hF.four_le_cϱ
  have hlam0 : 0 < p.lam := hplam ▸ hlam.1
  have hX : x₀ ≤ p.X := Setting.le_X_of_T hlam0 (by rw [hplam]; exact hTx)
  have hsX : 0 ≤ Real.sqrt p.X := Real.sqrt_nonneg _
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have ha1 := hF.a_le_one
  have ha0 := hF.a_pos.le
  have hS1 := S1_nonneg c p.X
  -- the second taper moment
  set I₂ := ∫ r, F.phiHat r ^ 2 * r ^ 2 with hI₂def
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun r => by positivity
  have hI₂ : I₂ ≤ 8 + 2 * cϱ ^ 2 := by
    refine hF.integral_phiHat_sq_mul_sq_le.trans ?_
    have : (cϱ / p.w) ^ 2 ≤ cϱ ^ 2 := by
      rw [div_pow]; exact div_le_self (sq_nonneg _) (by nlinarith [hF.one_le_w])
    linarith
  -- grid facts
  have hτ : ∀ k ∈ Finset.range p.d, p.T ≤ p.tau k ∧ p.tau k ≤ 2 * p.T := fun k hk =>
    p.tau_mem hL hT0.le hk
  have hd : (p.d : ℝ) ≤ p.L * p.T := by
    refine (p.d_le (by positivity)).trans (div_le_self (by positivity) ?_)
    linarith [Real.pi_gt_three]
  -- the three grid sums of the difference
  set GPi : ℕ → ℝ := fun k => ∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r) with hGPi
  set GP : ℕ → ℝ := fun k => ∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r) with hGP
  set GPc : ℕ → ℝ := fun k => ∫ r, F.phiHat r ^ 2 * Pc p.X c (p.tau k + r) with hGPc
  have hdiff : ∑ k : Fin p.d, GentryW cPi c p F k k - ∑ k : Fin p.d, GentryA p F k k
      = (cPi - 1) * ∑ k ∈ Finset.range p.d, GPi k + ∑ k ∈ Finset.range p.d, GPc k
        - ∑ k ∈ Finset.range p.d, GP k := by
    rw [Fin.sum_univ_eq_sum_range (fun k => GentryW cPi c p F k k) p.d,
      Fin.sum_univ_eq_sum_range (fun k => GentryA p F k k) p.d, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : 0 < p.tau k := by linarith [(hτ k hk).1]
    rw [GentryW_diag_eq hΓ hF cPi c k hk0, GentryA_diag_eq hΓ hF k hk0]
    ring
  -- (1) Π-part
  have h3 : |∑ k ∈ Finset.range p.d, GPi k|
      ≤ p.d * ((6 * Real.sqrt p.X / p.T) * (2 * π * p.L) + (12 * Real.sqrt p.X / p.T) * I₂) := by
    have hbound : ∀ k ∈ Finset.range p.d, |GPi k|
        ≤ (6 * Real.sqrt p.X / p.T) * (2 * π * p.L) + (12 * Real.sqrt p.X / p.T) * I₂ := by
      intro k hk
      have ht := (hτ k hk).1
      have ht2 : 2 ≤ p.tau k := by linarith
      refine (Pi_part_bound hF ht2).trans ?_
      have e1 : 6 * Real.sqrt p.X / p.tau k ≤ 6 * Real.sqrt p.X / p.T :=
        div_le_div_of_nonneg_left (by positivity) hT0 ht
      have e2 : 12 * Real.sqrt p.X / p.tau k ^ 2 ≤ 12 * Real.sqrt p.X / p.T :=
        div_le_div_of_nonneg_left (by positivity) hT0 (by nlinarith)
      have e3 : 2 * π * F.a * p.L ≤ 2 * π * p.L := by
        have h1 : 2 * π * F.a ≤ 2 * π := mul_le_of_le_one_right (by positivity) ha1
        nlinarith
      have b1 : 6 * Real.sqrt p.X / p.tau k * (2 * π * F.a * p.L)
          ≤ 6 * Real.sqrt p.X / p.T * (2 * π * p.L) :=
        mul_le_mul e1 e3 (by positivity) (by positivity)
      have b2 : 12 * Real.sqrt p.X / p.tau k ^ 2 * I₂
          ≤ 12 * Real.sqrt p.X / p.T * I₂ := mul_le_mul_of_nonneg_right e2 hI₂0
      linarith
    refine ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hbound)).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h3' : |(cPi - 1) * ∑ k ∈ Finset.range p.d, GPi k|
      ≤ |cPi - 1| * (12 * π + 96 + 24 * cϱ ^ 2) * (p.L ^ 2 * Real.sqrt p.X) := by
    rw [abs_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left (h3.trans ?_) (abs_nonneg _)
    calc (p.d : ℝ) * ((6 * Real.sqrt p.X / p.T) * (2 * π * p.L) + (12 * Real.sqrt p.X / p.T) * I₂)
        ≤ (p.L * p.T) * ((6 * Real.sqrt p.X / p.T) * (2 * π * p.L)
            + (12 * Real.sqrt p.X / p.T) * (8 + 2 * cϱ ^ 2)) := by gcongr
      _ = (12 * π * p.L + 12 * (8 + 2 * cϱ ^ 2)) * (p.L * Real.sqrt p.X) := by
          field_simp
          ring
      _ ≤ (12 * π * p.L + (96 + 24 * cϱ ^ 2) * p.L) * (p.L * Real.sqrt p.X) := by
          have hL1 : 1 ≤ p.L := by linarith [hF.eight_le_L]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith [sq_nonneg cϱ]
      _ = (12 * π + 96 + 24 * cϱ ^ 2) * (p.L ^ 2 * Real.sqrt p.X) := by ring
  -- (2) P_X-part
  have h4 : |∑ k ∈ Finset.range p.d, GP k| ≤ 3 / Real.log 2 * (p.L ^ 2 * Real.sqrt p.X) := by
    refine (sum_P_part_bound hF).trans ?_
    calc p.L ^ 2 / Real.log 2 * ∑ n ∈ primeRange p.X, acoef n
        ≤ p.L ^ 2 / Real.log 2 * (3 * Real.sqrt p.X) :=
          mul_le_mul_of_nonneg_left (hx₀ _ hX) (div_nonneg (sq_nonneg _) hlog2.le)
      _ = 3 / Real.log 2 * (p.L ^ 2 * Real.sqrt p.X) := by field_simp
  -- (3) P_c-part
  have h5 : |∑ k ∈ Finset.range p.d, GPc k| ≤ 1 / Real.log 2 * (p.L ^ 2 * S1 c p.X) := by
    refine (sum_Pc_part_bound hF.toCoreW hc1).trans (le_of_eq ?_)
    field_simp
  -- combine
  have hsplit : trGtW cPi c p F - F.a * p.L * N
      = (trGtA p F - F.a * p.L * N)
        + (p.L)⁻¹ * ((cPi - 1) * ∑ k ∈ Finset.range p.d, GPi k
            + ∑ k ∈ Finset.range p.d, GPc k - ∑ k ∈ Finset.range p.d, GP k) := by
    rw [← hdiff]
    unfold trGtW trGtA
    ring
  rw [hsplit]
  have hLinv : 0 < (p.L)⁻¹ := inv_pos.2 hL
  have hA : 0 ≤ p.L * Real.sqrt p.X := by positivity
  have hB : 0 ≤ p.L * S1 c p.X := by positivity
  have h0' : |trGtA p F - F.a * p.L * N| ≤ |C₀| * (p.L * Real.sqrt p.X) :=
    h0.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hA)
  set K₁ := |cPi - 1| * (12 * π + 96 + 24 * cϱ ^ 2) with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  calc |(trGtA p F - F.a * p.L * N)
        + (p.L)⁻¹ * ((cPi - 1) * ∑ k ∈ Finset.range p.d, GPi k
            + ∑ k ∈ Finset.range p.d, GPc k - ∑ k ∈ Finset.range p.d, GP k)|
      ≤ |trGtA p F - F.a * p.L * N|
        + (p.L)⁻¹ * (|(cPi - 1) * ∑ k ∈ Finset.range p.d, GPi k|
            + |∑ k ∈ Finset.range p.d, GPc k| + |∑ k ∈ Finset.range p.d, GP k|) := by
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [abs_mul, abs_of_pos hLinv]
        refine mul_le_mul_of_nonneg_left ?_ hLinv.le
        exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |C₀| * (p.L * Real.sqrt p.X)
        + (p.L)⁻¹ * (K₁ * (p.L ^ 2 * Real.sqrt p.X)
            + 1 / Real.log 2 * (p.L ^ 2 * S1 c p.X)
            + 3 / Real.log 2 * (p.L ^ 2 * Real.sqrt p.X)) := by
        gcongr
    _ = |C₀| * (p.L * Real.sqrt p.X) + K₁ * (p.L * Real.sqrt p.X)
        + 3 / Real.log 2 * (p.L * Real.sqrt p.X) + 1 / Real.log 2 * (p.L * S1 c p.X) := by
        field_simp
        ring
    _ ≤ (|C₀| + K₁ + 3 / Real.log 2 + 1 / Real.log 2)
        * (p.L * Real.sqrt p.X + p.L * S1 c p.X) := by
        have hk2 : 0 ≤ 3 / Real.log 2 := by positivity
        have hk3 : 0 ≤ 1 / Real.log 2 := by positivity
        nlinarith [mul_nonneg (abs_nonneg C₀) hB, mul_nonneg hK₁0 hB, mul_nonneg hk2 hB,
          mul_nonneg hk3 hA]

end XiPrime
end Zeta23
