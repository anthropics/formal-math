/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/
import Zeta23.PrimeSideA.Basic
import Zeta23.PrimeSideA.MuMu
import Zeta23.PrimeSideA.CrossMuP
import Zeta23.PrimeSideA.Ends

/-!
# Prime side, part A — paper §5 [sec:prime]:  [prop:trace], [lem:ends], [eq:Msplit], [prop:mumu], [prop:cross]

Seam with `PrimeSideB.lean` ([prop:PP], [thm:traces]): see the header of
`Zeta23/PrimeSideA/Defs.lean`.  Everything here is ζ-free: the zeros never
appear in §5 ("In this section the zeros play no role", §5); `N(T,2T)` enters [prop:trace]
only through [eq:muints] + [eq:RvM], which we take as hypotheses on an abstract real `N`.

## Shape of the results
All error terms are explicit inequalities, uniform in `T`:
  `∃ C, EventuallyAt cϱ lam (fun p F => |lhs p F − main p F| ≤ C * err p)`
where `EventuallyAt cϱ lam P` means: there is `T₀` such that `P p F` holds for every parameter set
`p` with `p.lam = lam`, `T₀ ≤ p.T` and every taper datum `F` satisfying `LocalHyps cϱ p F`.
So `C` and `T₀` may depend on `c_ϱ`, on the constants inside H-Γ/H-cheb, and on `λ` — the paper
has `C` depending on ϱ only and `T₀ = T₀(λ)` (§5.5); ours is the (weaker, sufficient at fixed λ)
reading.  This is a deviation from the paper.

## Hypotheses consumed (all proved elsewhere in the repository; none is a Lean axiom)
* `Zeta23.GammaFacts` (H-Γ [eq:mufacts]+[eq:muints]) and `Zeta23.ChebyshevMertens` (H-cheb
  [lem:cheb]) — Zeta23/Hypotheses.lean, verbatim (fields of `PaperInputs`).
* `LocalHyps cϱ p F` — taper/test-family facts [eq:psidef], [eq:abdef], [eq:gbounds], [eq:Phi2FT],
                      `∫φ̂² = 2πaL`, `Φ(0) = aL`, `∫Φ² = 2πbL`;
                      [lem:poisson] (★); [eq:PiPfacts] for Π_X;
                      parameter regime [eq:wrange], `0<λ≤1`.
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace PrimeSide

section Results

variable (cϱ lam : ℝ)
/-! ## [prop:trace]  (§5.2) -/

set_option maxHeartbeats 1000000 in
/-- **[prop:trace], μ-form** (the paper's proof, §5.2, before [eq:muints] is invoked):
`L·tr G̃ = aL² ∫_T^{2T} μ + O(L²√X + L l)`, divided by `L` and with `l ≤ L√X/λ`:
`|tr G̃ − aL ∫_T^{2T} μ| ≤ C · L√X`. -/
theorem prop_trace_mu (hΓ : Zeta23.GammaFacts) (hcheb : Zeta23.ChebyshevMertens)
    (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |trGtA p F - F.a * p.L * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ| ≤ C * (p.L * Real.sqrt p.X)) := by
  obtain ⟨K, hK0, hK⟩ := mu_increment_bound hΓ
  obtain ⟨x₀, hx₀⟩ := hcheb.cheb1b
  obtain ⟨T₁, hT₁⟩ := mu_abs_le_l hΓ
  obtain ⟨τ₀, hτ₀0, hτ₀⟩ := mu_nonneg_eventually hΓ
  refine ⟨8 * K + 2 * |cϱ| * K + 44 * cϱ ^ 2 + 4 * π / lam + 245,
    max (max T₁ 4) (max (2 * π * Real.exp (|x₀| / lam)) (τ₀ + 1)), fun p F hplam hT hF => ?_⟩
  -- thresholds
  have hTa : max T₁ 4 ≤ p.T := (le_max_left _ _).trans hT
  have hTb : max (2 * π * Real.exp (|x₀| / lam)) (τ₀ + 1) ≤ p.T := (le_max_right _ _).trans hT
  have hT₁' : T₁ ≤ p.T := (le_max_left _ _).trans hTa
  have hT4 : 4 ≤ p.T := (le_max_right _ _).trans hTa
  have hTx : 2 * π * Real.exp (|x₀| / lam) ≤ p.T := (le_max_left _ _).trans hTb
  have hTτ : τ₀ + 1 ≤ p.T := (le_max_right _ _).trans hTb
  have hT0 : 0 < p.T := by linarith
  have hL := hF.L_pos
  have hL8 := hF.eight_le_L
  have hc4 := hF.four_le_cϱ
  have hc0 : 0 ≤ cϱ := by linarith
  have hlam0 : 0 < p.lam := hplam ▸ hlam.1
  have hX : x₀ ≤ p.X := Setting.le_X_of_T hlam0 (by rw [hplam]; exact hTx)
  have hX1 : 1 ≤ Real.sqrt p.X := by
    rw [Real.le_sqrt' one_pos, one_pow]; exact Real.one_le_exp hL.le |>.trans_eq rfl
  have hsX : 0 ≤ Real.sqrt p.X := Real.sqrt_nonneg _
  have hh0 : 0 < p.h := by simp only [Setting.h]; positivity
  have hh1 : p.h ≤ 1 := by
    simp only [Setting.h]; rw [div_le_one hL]; linarith [Real.pi_lt_four]
  have hl1 := hF.one_le_l
  have ha1 := hF.a_le_one
  have ha0 := hF.a_pos.le
  -- the two taper integrals
  set I₁ := ∫ r, F.phiHat r ^ 2 * |r| with hI₁def
  set I₂ := ∫ r, F.phiHat r ^ 2 * r ^ 2 with hI₂def
  have hI₁0 : 0 ≤ I₁ := integral_nonneg fun r => by positivity
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun r => by positivity
  have hI₁ : I₁ ≤ 8 + 2 * cϱ * p.L := by
    refine hF.integral_phiHat_sq_mul_abs_le.trans ?_
    have h1 : Real.log (cϱ * p.L / (4 * p.w)) ≤ cϱ * p.L / (4 * p.w) :=
      Real.log_le_self (by have := hF.one_le_w; positivity)
    have h2 : cϱ * p.L / (4 * p.w) ≤ cϱ * p.L / 4 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num); linarith [hF.one_le_w]
    linarith
  have hI₂ : I₂ ≤ 8 + 2 * cϱ ^ 2 := by
    refine hF.integral_phiHat_sq_mul_sq_le.trans ?_
    have : (cϱ / p.w) ^ 2 ≤ cϱ ^ 2 := by
      rw [div_pow]; exact div_le_self (sq_nonneg _) (by nlinarith [hF.one_le_w])
    linarith
  -- rewrite tr G̃ as a sum over range d
  have hsumFin : ∑ k : Fin p.d, GentryA p F k k = ∑ k ∈ Finset.range p.d, GentryA p F k k :=
    Fin.sum_univ_eq_sum_range (fun k => GentryA p F k k) p.d
  -- grid facts
  have hτ : ∀ k ∈ Finset.range p.d, p.T ≤ p.tau k ∧ p.tau k ≤ 2 * p.T := fun k hk =>
    p.tau_mem hL hT0.le hk
  -- decomposition of each diagonal entry
  set Gμ : ℕ → ℝ := fun k => ∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r) with hGμ
  set GPi : ℕ → ℝ := fun k => ∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r) with hGPi
  set GP : ℕ → ℝ := fun k => ∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r) with hGP
  have hdecomp : ∑ k ∈ Finset.range p.d, GentryA p F k k
      = ∑ k ∈ Finset.range p.d, Gμ k + ∑ k ∈ Finset.range p.d, GPi k
        + ∑ k ∈ Finset.range p.d, GP k := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    exact GentryA_diag_eq hΓ hF k (by linarith [(hτ k hk).1])
  -- (1) μ-part vs 2πaL μ(τ_k)
  have h1 : |∑ k ∈ Finset.range p.d, Gμ k - 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d,
      Zeta23.mu (p.tau k)| ≤ p.d * ((K * I₁ + 10 * I₂) / p.T) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ k ∈ Finset.range p.d, |Gμ k - 2 * π * F.a * p.L * Zeta23.mu (p.tau k)|
        ≤ (K * I₁ + 10 * I₂) / p.T := by
      intro k hk
      have ht2 : 2 ≤ p.tau k := by linarith [(hτ k hk).1]
      refine (mu_part_bound hΓ hF hK ht2).trans ?_
      exact div_le_div_of_nonneg_left (by positivity) hT0 (hτ k hk).1
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- (2) Riemann sum: 2πaL Σ μ(τ_k) vs aL² ∫ μ
  have h2 : |2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, Zeta23.mu (p.tau k)
      - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ| ≤ 4 * π * p.L * p.l := by
    have hR := riemann_sum_monotone (μ := Zeta23.mu) (T := p.T) hh0 (by linarith)
      (hΓ.monotoneOn.mono (fun x hx => by
        simp only [Set.mem_Ici] at hx ⊢; linarith))
      (fun x hx => hτ₀ x (by linarith))
    rw [← p.d_eq_floor hL] at hR
    have hsum : ∑ k ∈ Finset.range p.d, Zeta23.mu (p.tau k)
        = ∑ k ∈ Finset.range p.d, Zeta23.mu (p.T + k * p.h) := by
      refine Finset.sum_congr rfl fun k _ => by rw [Setting.tau_natCast]
    rw [hsum]
    have hid : 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, Zeta23.mu (p.T + k * p.h)
        - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ
        = F.a * p.L ^ 2 * (p.h * ∑ k ∈ Finset.range p.d, Zeta23.mu (p.T + k * p.h)
            - ∫ τ in p.T..(2 * p.T), Zeta23.mu τ) := by
      simp only [Setting.h]; field_simp
    rw [hid, abs_mul, abs_of_nonneg (by positivity)]
    have hμ2T : Zeta23.mu (2 * p.T) ≤ p.l := by
      have := hT₁ p hT₁' (2 * p.T) ⟨by linarith, le_rfl⟩
      exact (le_abs_self _).trans this
    have hμ2T0 : 0 ≤ Zeta23.mu (2 * p.T) := hτ₀ _ (by linarith)
    calc F.a * p.L ^ 2 * |p.h * ∑ k ∈ Finset.range p.d, Zeta23.mu (p.T + k * p.h)
          - ∫ τ in p.T..(2 * p.T), Zeta23.mu τ|
        ≤ F.a * p.L ^ 2 * (2 * p.h * Zeta23.mu (2 * p.T)) := by gcongr
      _ ≤ 1 * p.L ^ 2 * (2 * p.h * p.l) := by gcongr
      _ = 4 * π * p.L * p.l := by simp only [Setting.h]; field_simp; ring
  -- (3) Π-part
  have h3 : |∑ k ∈ Finset.range p.d, GPi k|
      ≤ p.d * ((6 * Real.sqrt p.X / p.T) * (2 * π * p.L) + (12 * Real.sqrt p.X / p.T) * I₂) := by
    have hbound : ∀ k ∈ Finset.range p.d, |GPi k|
        ≤ (6 * Real.sqrt p.X / p.T) * (2 * π * p.L) + (12 * Real.sqrt p.X / p.T) * I₂ := by
      intro k hk
      have ht := (hτ k hk).1
      have ht2 : 2 ≤ p.tau k := by linarith
      have ht0 : 0 < p.tau k := by linarith
      refine (Pi_part_bound hF ht2).trans ?_
      have e1 : 6 * Real.sqrt p.X / p.tau k ≤ 6 * Real.sqrt p.X / p.T :=
        div_le_div_of_nonneg_left (by positivity) hT0 ht
      have e2 : 12 * Real.sqrt p.X / p.tau k ^ 2 ≤ 12 * Real.sqrt p.X / p.T :=
        div_le_div_of_nonneg_left (by positivity) hT0 (by nlinarith)
      have e3 : 2 * π * F.a * p.L ≤ 2 * π * p.L := by
        have h1 : 2 * π * F.a ≤ 2 * π := mul_le_of_le_one_right (by positivity) ha1
        have h2 : (2 * π * F.a) * p.L ≤ (2 * π) * p.L := mul_le_mul_of_nonneg_right h1 hL.le
        linarith
      have b1 : 6 * Real.sqrt p.X / p.tau k * (2 * π * F.a * p.L)
          ≤ 6 * Real.sqrt p.X / p.T * (2 * π * p.L) :=
        mul_le_mul e1 e3 (by positivity) (by positivity)
      have b2 : 12 * Real.sqrt p.X / p.tau k ^ 2 * I₂
          ≤ 12 * Real.sqrt p.X / p.T * I₂ := mul_le_mul_of_nonneg_right e2 hI₂0
      linarith
    refine ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hbound)).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- (4) P-part
  have h4 : |∑ k ∈ Finset.range p.d, GP k| ≤ p.L ^ 2 / Real.log 2 * (3 * Real.sqrt p.X) := by
    refine (sum_P_part_bound hF).trans ?_
    exact mul_le_mul_of_nonneg_left (hx₀ _ hX)
      (div_nonneg (sq_nonneg _) (Real.log_nonneg one_le_two))
  -- d ≤ L T
  have hd : (p.d : ℝ) ≤ p.L * p.T := by
    refine (p.d_le (by positivity)).trans (div_le_self (by positivity) ?_)
    linarith [Real.pi_gt_three]
  have hdT : (p.d : ℝ) / p.T ≤ p.L := by rwa [div_le_iff₀ hT0]
  -- combine: |Σ G_kk − aL² ∫μ| ≤ …
  have hmain : |∑ k ∈ Finset.range p.d, GentryA p F k k
      - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ|
      ≤ p.L * (K * I₁ + 10 * I₂) + 4 * π * p.L * p.l
        + p.L * ((6 * Real.sqrt p.X) * (2 * π * p.L) + (12 * Real.sqrt p.X) * I₂)
        + p.L ^ 2 / Real.log 2 * (3 * Real.sqrt p.X) := by
    rw [hdecomp]
    have e1 : p.d * ((K * I₁ + 10 * I₂) / p.T) ≤ p.L * (K * I₁ + 10 * I₂) := by
      rw [mul_div_assoc', div_le_iff₀ hT0]
      calc (p.d : ℝ) * (K * I₁ + 10 * I₂) ≤ (p.L * p.T) * (K * I₁ + 10 * I₂) := by
            gcongr
        _ = p.L * (K * I₁ + 10 * I₂) * p.T := by ring
    have e3 : p.d * ((6 * Real.sqrt p.X / p.T) * (2 * π * p.L) + (12 * Real.sqrt p.X / p.T) * I₂)
        ≤ p.L * ((6 * Real.sqrt p.X) * (2 * π * p.L) + (12 * Real.sqrt p.X) * I₂) := by
      have : p.d * ((6 * Real.sqrt p.X / p.T) * (2 * π * p.L) + (12 * Real.sqrt p.X / p.T) * I₂)
          = (p.d / p.T) * ((6 * Real.sqrt p.X) * (2 * π * p.L) + (12 * Real.sqrt p.X) * I₂) := by
        field_simp
      rw [this]; gcongr
    calc |∑ k ∈ Finset.range p.d, Gμ k + ∑ k ∈ Finset.range p.d, GPi k
          + ∑ k ∈ Finset.range p.d, GP k - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ|
        = |(∑ k ∈ Finset.range p.d, Gμ k - 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d,
              Zeta23.mu (p.tau k))
            + (2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, Zeta23.mu (p.tau k)
              - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ)
            + ∑ k ∈ Finset.range p.d, GPi k + ∑ k ∈ Finset.range p.d, GP k| := by ring_nf
      _ ≤ |∑ k ∈ Finset.range p.d, Gμ k - 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d,
              Zeta23.mu (p.tau k)|
            + |2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, Zeta23.mu (p.tau k)
              - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ|
            + |∑ k ∈ Finset.range p.d, GPi k| + |∑ k ∈ Finset.range p.d, GP k| := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ _ := by linarith [h1.trans e1, h2, h3.trans e3, h4]
  -- divide by L and pass to tr G̃
  have htr : trGtA p F - F.a * p.L * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ
      = p.L⁻¹ * (∑ k ∈ Finset.range p.d, GentryA p F k k
          - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ) := by
    simp only [trGtA, hsumFin]; field_simp
  -- final arithmetic: everything ≤ C · L√X
  set S := p.L * Real.sqrt p.X with hS
  have hS8 : 8 ≤ S := by nlinarith
  have hS1 : 1 ≤ S := by linarith
  have hLS : p.L ≤ S := by nlinarith
  have hlS : p.l ≤ S / lam := by
    rw [le_div_iff₀ hlam.1]
    have : p.l * lam = p.L := by rw [← hplam]; simp only [Setting.L]; ring
    rw [this]; exact hLS
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2' : 0 < Real.log 2 := by linarith
  have t1 : K * I₁ + 10 * I₂ ≤ (8 * K + 2 * |cϱ| * K + 80 + 20 * cϱ ^ 2) * S := by
    rw [abs_of_nonneg hc0]
    have v1 : K * I₁ ≤ K * (8 + 2 * cϱ * p.L) := by gcongr
    have v2 : 10 * I₂ ≤ 10 * (8 + 2 * cϱ ^ 2) := by linarith
    have u1 : 8 * K ≤ 8 * K * S := le_mul_of_one_le_right (by positivity) hS1
    have u2 : 2 * cϱ * K * p.L ≤ 2 * cϱ * K * S :=
      mul_le_mul_of_nonneg_left hLS (by positivity)
    have u3 : (80:ℝ) ≤ 80 * S := by linarith
    have u4 : 20 * cϱ ^ 2 ≤ 20 * cϱ ^ 2 * S := le_mul_of_one_le_right (by positivity) hS1
    nlinarith [mul_nonneg hc0 hK0]
  have t2 : 4 * π * p.l ≤ (4 * π / lam) * S := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlam.1]
    have hls : p.l * lam ≤ S := by rw [← le_div_iff₀ hlam.1]; exact hlS
    calc 4 * π * p.l * lam = 4 * π * (p.l * lam) := by ring
      _ ≤ 4 * π * S := by gcongr
      _ = 4 * π * S := rfl
  have t3 : (6 * Real.sqrt p.X) * (2 * π * p.L) + (12 * Real.sqrt p.X) * I₂
      ≤ (160 + 24 * cϱ ^ 2) * S := by
    have e : (6 * Real.sqrt p.X) * (2 * π * p.L) = 12 * π * S := by rw [hS]; ring
    have f : (12 * Real.sqrt p.X) * I₂ ≤ 12 * (8 + 2 * cϱ ^ 2) * S := by
      calc (12 * Real.sqrt p.X) * I₂ ≤ (12 * Real.sqrt p.X) * (8 + 2 * cϱ ^ 2) := by gcongr
        _ = 12 * (8 + 2 * cϱ ^ 2) * (1 * Real.sqrt p.X) := by ring
        _ ≤ 12 * (8 + 2 * cϱ ^ 2) * (p.L * Real.sqrt p.X) := by gcongr; linarith
        _ = 12 * (8 + 2 * cϱ ^ 2) * S := by rw [hS]
    have hS0 : 0 ≤ S := by linarith
    have g : 12 * π * S ≤ 48 * S :=
      mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four]) hS0
    rw [e]; linarith
  have t4 : p.L / Real.log 2 * (3 * Real.sqrt p.X) ≤ 5 * S := by
    rw [hS, div_mul_eq_mul_div, div_le_iff₀ hlog2']
    have h5 : 3 * (p.L * Real.sqrt p.X) ≤ 5 * Real.log 2 * (p.L * Real.sqrt p.X) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hL.le hsX)
    linarith
  calc |trGtA p F - F.a * p.L * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ|
      = p.L⁻¹ * |∑ k ∈ Finset.range p.d, GentryA p F k k
          - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ| := by
        rw [htr, abs_mul, abs_of_pos (inv_pos.2 hL)]
    _ ≤ p.L⁻¹ * (p.L * (K * I₁ + 10 * I₂) + 4 * π * p.L * p.l
        + p.L * ((6 * Real.sqrt p.X) * (2 * π * p.L) + (12 * Real.sqrt p.X) * I₂)
        + p.L ^ 2 / Real.log 2 * (3 * Real.sqrt p.X)) := by gcongr
    _ = (K * I₁ + 10 * I₂) + 4 * π * p.l
        + ((6 * Real.sqrt p.X) * (2 * π * p.L) + (12 * Real.sqrt p.X) * I₂)
        + p.L / Real.log 2 * (3 * Real.sqrt p.X) := by field_simp
    _ ≤ (8 * K + 2 * |cϱ| * K + 80 + 20 * cϱ ^ 2) * S + (4 * π / lam) * S
        + (160 + 24 * cϱ ^ 2) * S + 5 * S := by linarith
    _ = (8 * K + 2 * |cϱ| * K + 44 * cϱ ^ 2 + 4 * π / lam + 245) * S := by ring

/-- **[prop:trace]** (§5.2, verbatim): `tr G̃ = aL·N(T,2T) + O(L√X)`.
Here `N` is an abstract real standing for `N(T,2T)` and the two hypotheses are exactly what the
paper's proof uses to pass from `∫_T^{2T}μ` to `N(T,2T)`: [eq:muints] (field `int_mu` of
`Zeta23.GammaFacts`) and [eq:RvM] `N(T,2T) = Tℓ₁/2π + O(l)` with constant `A` (hypothesis `hRvM`). -/
theorem prop_trace (hΓ : Zeta23.GammaFacts) (hcheb : Zeta23.ChebyshevMertens)
    (hlam : 0 < lam ∧ lam ≤ 1) (A : ℝ) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F => ∀ N : ℝ,
      |N - p.T * p.ell1 / (2 * π)| ≤ A * p.l →
      |trGtA p F - F.a * p.L * N| ≤ C * (p.L * Real.sqrt p.X)) := by
  obtain ⟨C₀, T₀, hC₀⟩ := prop_trace_mu cϱ lam hΓ hcheb hlam
  obtain ⟨Cμ, T₂, hCμ⟩ := hΓ.int_mu
  refine ⟨C₀ + |Cμ| + 2 * |A| / lam, max T₀ (max T₂ 1), fun p F hplam hT hF => ?_⟩
  intro N hN
  subst hplam
  have h0 := hC₀ p F rfl ((le_max_left _ _).trans hT) hF
  have hT2 : T₂ ≤ p.T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have hT1 : (1:ℝ) ≤ p.T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  have hμint := hCμ p.T hT2
  have hL := hF.L_pos
  have hlam0 : 0 < p.lam := hlam.1
  have ha0 := hF.a_pos.le
  have ha1 := hF.a_le_one
  have hsX : 0 ≤ Real.sqrt p.X := Real.sqrt_nonneg _
  have hX1 : 1 ≤ Real.sqrt p.X := by
    rw [Real.le_sqrt' one_pos, one_pow]; exact Real.one_le_exp hL.le
  -- l ≤ (2/λ)√X  (since √X = e^{L/2} = e^{λl/2} ≥ λl/2)
  have hl0 : 0 ≤ p.l := zero_le_one.trans hF.one_le_l
  have hlX : p.l ≤ 2 / p.lam * Real.sqrt p.X := by
    have he : Real.sqrt p.X = Real.exp (p.lam * p.l / 2) := by
      rw [show p.X = Real.exp (p.lam * p.l) from rfl, ← Real.exp_half]
    rw [he, div_mul_eq_mul_div, le_div_iff₀ hlam0]
    have h1 := Real.add_one_le_exp (p.lam * p.l / 2)
    nlinarith
  -- assemble
  have e1 : |trGtA p F - F.a * p.L * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ|
      ≤ C₀ * (p.L * Real.sqrt p.X) := h0
  have e2 : |F.a * p.L * ((∫ τ in p.T..(2 * p.T), Zeta23.mu τ) - p.T * p.ell1 / (2 * π))|
      ≤ |Cμ| * (p.L * Real.sqrt p.X) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ F.a * p.L)]
    have h1 : |(∫ τ in p.T..(2 * p.T), Zeta23.mu τ) - p.T * p.ell1 / (2 * π)| ≤ |Cμ| := by
      refine hμint.trans ?_
      calc Cμ / p.T ≤ |Cμ| / p.T := by gcongr; exact le_abs_self _
        _ ≤ |Cμ| / 1 := by apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos; exact hT1
        _ = |Cμ| := div_one _
    calc F.a * p.L * |(∫ τ in p.T..(2 * p.T), Zeta23.mu τ) - p.T * p.ell1 / (2 * π)|
        ≤ 1 * p.L * |Cμ| := by gcongr
      _ = p.L * |Cμ| := by ring
      _ ≤ (p.L * Real.sqrt p.X) * |Cμ| := by
          have := mul_le_mul_of_nonneg_left hX1 hL.le
          have h0' : 0 ≤ |Cμ| := abs_nonneg _
          nlinarith
      _ = |Cμ| * (p.L * Real.sqrt p.X) := by ring
  have e3 : |F.a * p.L * (p.T * p.ell1 / (2 * π) - N)|
      ≤ (2 * |A| / p.lam) * (p.L * Real.sqrt p.X) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ F.a * p.L), abs_sub_comm]
    have hAl : A * p.l ≤ |A| * (2 / p.lam * Real.sqrt p.X) := by
      calc A * p.l ≤ |A| * p.l := mul_le_mul_of_nonneg_right (le_abs_self A) hl0
        _ ≤ |A| * (2 / p.lam * Real.sqrt p.X) :=
            mul_le_mul_of_nonneg_left hlX (abs_nonneg A)
    calc F.a * p.L * |N - p.T * p.ell1 / (2 * π)| ≤ 1 * p.L * (A * p.l) := by gcongr
      _ = p.L * (A * p.l) := by ring
      _ ≤ p.L * (|A| * (2 / p.lam * Real.sqrt p.X)) := mul_le_mul_of_nonneg_left hAl hL.le
      _ = (2 * |A| / p.lam) * (p.L * Real.sqrt p.X) := by field_simp
  calc |trGtA p F - F.a * p.L * N|
      = |(trGtA p F - F.a * p.L * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ)
          + F.a * p.L * ((∫ τ in p.T..(2 * p.T), Zeta23.mu τ) - p.T * p.ell1 / (2 * π))
          + F.a * p.L * (p.T * p.ell1 / (2 * π) - N)| := by ring_nf
    _ ≤ |trGtA p F - F.a * p.L * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ|
          + |F.a * p.L * ((∫ τ in p.T..(2 * p.T), Zeta23.mu τ) - p.T * p.ell1 / (2 * π))|
          + |F.a * p.L * (p.T * p.ell1 / (2 * π) - N)| := abs_add_three _ _ _
    _ ≤ (C₀ + |Cμ| + 2 * |A| / p.lam) * (p.L * Real.sqrt p.X) := by linarith

/-! ## [lem:ends]  (§5.3), with [eq:Kdef], [eq:trG2int], [eq:Kbounds] -/

-- **[lem:ends]** is proved in Zeta23/PrimeSideA/Ends.lean:
-- `Zeta23.PrimeSide.lem_ends` (§5.3) — imported by this module.
#check @lem_ends

/-! ## [eq:Msplit]  (§5.4) -/

/-- **[eq:Msplit]** (§5.4, verbatim):
`𝓜 = 𝓜[μ,μ] + 𝓜[P_X,P_X] + 2𝓜[μ,P_X] + 2𝓜[μ,Π_X] + 2𝓜[P_X,Π_X] + 𝓜[Π_X,Π_X]`,
valid because `𝓜[·,·]` is a symmetric bilinear form (`Φ²` even) and all six densities are
continuous on the compact square `I×I` (so every integral is a genuine Lebesgue integral). -/
theorem eq_Msplit (hΓ : Zeta23.GammaFacts) (p : Setting) (F : LocalFun) (hF : LocalHypsCore cϱ p F) :
    MtotalA p F =
      Mform F.Phi p.T Zeta23.mu Zeta23.mu + Mform F.Phi p.T (Zeta23.PX p.X) (Zeta23.PX p.X)
        + 2 * Mform F.Phi p.T Zeta23.mu (Zeta23.PX p.X) + 2 * Mform F.Phi p.T Zeta23.mu (Zeta23.PiX p.X)
        + 2 * Mform F.Phi p.T (Zeta23.PX p.X) (Zeta23.PiX p.X)
        + Mform F.Phi p.T (Zeta23.PiX p.X) (Zeta23.PiX p.X) := by
  have hν : Zeta23.nuX p.X = Zeta23.mu + Zeta23.PiX p.X + Zeta23.PX p.X := rfl
  unfold MtotalA
  rw [hν, Mform_trinomial hF.Phi_contDiff.continuous hF.Phi_even hΓ.smooth.continuous
    hF.PiX_cont (PX_continuous p.X)]

/-! ## [prop:mumu]  (§5.4) -/

/-! **[prop:mumu]**, first form (§5.4, verbatim): `𝓜[μ,μ] = 2πbL ∫_T^{2T} μ² + O(l² log L)`.
(The second form `= (bLTℓ₁²/2π)(1+O(l⁻²)) + O(l² log L)` follows with [eq:muints] and is taken in
PrimeSideB.)  We write `log L` as in the paper; note `log L ≤ log l` since `λ ≤ 1`. -/
-- **[prop:mumu]** is proved in Zeta23/PrimeSideA/MuMu.lean:
-- `Zeta23.PrimeSide.prop_mumu` — imported by this module, so available here under the same name.
#check @prop_mumu

/-! ## [prop:cross]  (§5.4) -/

-- **[prop:cross] (i)** is proved in Zeta23/PrimeSideA/CrossMuP.lean:
-- `Zeta23.PrimeSide.prop_cross_muP` (§5.4: 𝓜[μ,P_X] ≪ l√X) — imported by this module.
#check @prop_cross_muP

/-- **[prop:cross] (ii)** (§5.4): `𝓜[μ,Π_X] ≪ l L √X`.  Proof (§5.4): `0<μ≤l` and
`|Π_X| ≤ 3√X/T` on `I`, inserted into the sup-bound: `≤ l·(3√X/T)·T·2πbL ≤ 6π·lL√X`. -/
theorem prop_cross_muPi (hΓ : Zeta23.GammaFacts) (_hcheb : Zeta23.ChebyshevMertens)
    (_hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |Mform F.Phi p.T Zeta23.mu (Zeta23.PiX p.X)| ≤ C * (p.l * p.L * Real.sqrt p.X)) := by
  obtain ⟨T₁, hT₁⟩ := mu_abs_le_l hΓ
  refine ⟨6 * π, max T₁ 1, fun p F _ hT hF => ?_⟩
  have hT0 : 0 < p.T := by linarith [le_max_right T₁ 1]
  have hμ := hT₁ p ((le_max_left _ _).trans hT)
  have hPi := hF.PiX_le_on_I hT0
  have h := abs_Mform_le hT0.le hF.Phi_contDiff.continuous hΓ.smooth.continuous hF.PiX_cont
    hF.Phi_sq_integrable hμ hPi
  have hl0 : 0 ≤ p.l := le_trans zero_le_one hF.one_le_l
  have hX0 := hF.integral_Phi_sq_le
  calc |Mform F.Phi p.T Zeta23.mu (Zeta23.PiX p.X)|
      ≤ p.l * (3 * Real.sqrt p.X / p.T) * (p.T * ∫ x, F.Phi x ^ 2) := h
    _ ≤ p.l * (3 * Real.sqrt p.X / p.T) * (p.T * (2 * π * p.L)) := by gcongr
    _ = 6 * π * (p.l * p.L * Real.sqrt p.X) := by field_simp; ring

/-- **[prop:cross] (iii)** (§5.4): `𝓜[P_X,Π_X] ≪ L X`.  Proof (§5.4): `|P_X| ≤ √X` (H-cheb) and
`|Π_X| ≤ 3√X/T` on `I`: `≤ √X·(3√X/T)·T·2πbL ≤ 6π·LX`. -/
theorem prop_cross_PPi (_hΓ : Zeta23.GammaFacts) (hcheb : Zeta23.ChebyshevMertens)
    (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |Mform F.Phi p.T (Zeta23.PX p.X) (Zeta23.PiX p.X)| ≤ C * (p.L * p.X)) := by
  obtain ⟨x₀, hx₀⟩ := PX_abs_le hcheb
  refine ⟨6 * π, max (2 * π * Real.exp (|x₀| / lam)) 1, fun p F hplam hT hF => ?_⟩
  have hT0 : 0 < p.T := by linarith [le_max_right (2 * π * Real.exp (|x₀| / lam)) 1]
  have hX : x₀ ≤ p.X := Setting.le_X_of_T (hplam ▸ hlam.1) (by rw [hplam]; exact (le_max_left _ _).trans hT)
  have hP : ∀ τ ∈ Set.Icc p.T (2 * p.T), |Zeta23.PX p.X τ| ≤ Real.sqrt p.X := fun τ _ => hx₀ _ hX τ
  have hPi := hF.PiX_le_on_I hT0
  have h := abs_Mform_le hT0.le hF.Phi_contDiff.continuous (PX_continuous p.X) hF.PiX_cont
    hF.Phi_sq_integrable hP hPi
  have hX0 := hF.integral_Phi_sq_le
  calc |Mform F.Phi p.T (Zeta23.PX p.X) (Zeta23.PiX p.X)|
      ≤ Real.sqrt p.X * (3 * Real.sqrt p.X / p.T) * (p.T * ∫ x, F.Phi x ^ 2) := h
    _ ≤ Real.sqrt p.X * (3 * Real.sqrt p.X / p.T) * (p.T * (2 * π * p.L)) := by gcongr
    _ = 6 * π * (p.L * (Real.sqrt p.X) ^ 2) := by field_simp; ring
    _ = 6 * π * (p.L * p.X) := by rw [Real.sq_sqrt p.X_pos.le]

/-- **[prop:cross] (iv)** (§5.4): `𝓜[Π_X,Π_X] ≪ L X / T`.  Proof (§5.4): `|Π_X| ≤ 3√X/T` on
`I` twice: `≤ (3√X/T)²·T·2πbL ≤ 18π·LX/T`. -/
theorem prop_cross_PiPi (_hΓ : Zeta23.GammaFacts) (_hcheb : Zeta23.ChebyshevMertens)
    (_hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |Mform F.Phi p.T (Zeta23.PiX p.X) (Zeta23.PiX p.X)| ≤ C * (p.L * p.X / p.T)) := by
  refine ⟨18 * π, 1, fun p F _ hT hF => ?_⟩
  have hT0 : 0 < p.T := by linarith
  have hPi := hF.PiX_le_on_I hT0
  have h := abs_Mform_le hT0.le hF.Phi_contDiff.continuous hF.PiX_cont hF.PiX_cont
    hF.Phi_sq_integrable hPi hPi
  have hX0 := hF.integral_Phi_sq_le
  calc |Mform F.Phi p.T (Zeta23.PiX p.X) (Zeta23.PiX p.X)|
      ≤ (3 * Real.sqrt p.X / p.T) * (3 * Real.sqrt p.X / p.T) * (p.T * ∫ x, F.Phi x ^ 2) := h
    _ ≤ (3 * Real.sqrt p.X / p.T) * (3 * Real.sqrt p.X / p.T) * (p.T * (2 * π * p.L)) := by
        gcongr
    _ = 18 * π * (p.L * (Real.sqrt p.X) ^ 2 / p.T) := by field_simp; ring
    _ = 18 * π * (p.L * p.X / p.T) := by rw [Real.sq_sqrt p.X_pos.le]

end Results

/-!
## Contents
Proved in this file:
* eq_Msplit — [eq:Msplit]
* prop_cross_muPi / _PPi / _PiPi — [prop:cross] (ii)(iii)(iv)
* prop_trace_mu, prop_trace — **[prop:trace]** (μ-form and the paper's aL·N(T,2T) + O(L√X) form)
Proved in child files, imported here:
* prop_mumu      — [prop:mumu]     — Zeta23/PrimeSideA/MuMu.lean
* prop_cross_muP — [prop:cross](i) — Zeta23/PrimeSideA/CrossMuP.lean
* lem_ends       — [lem:ends]      — Zeta23/PrimeSideA/Ends.lean
-/

end PrimeSide
end Zeta23
