/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Costs
public import ThreeSumApsp.Sec4.Corollary31.Limit
public import ThreeSumApsp.Sec4.Corollary31.RationalParameters

/-!
# Corollaries 31 and 32: the parameters of the program, and where its costs are bounded

For real c > 10, 0 < θ < 0.9 and ε < R_c(γ) there are parameters G for the program text (rational c'
and θ', a threshold m₀) and a constant C such that on every instance with 1 ≤ D ≤ N^ε and with m ≥
m₀ the costs of Theorem 30 at these parameters are at most C times

    Tp = N² (log D + 1)²/D^γ     and     Tq = D^q (log D + 1),

γ and q being those of c and θ (`exists_ratParams`).

The rational parameters come from `exists_rat_params` and the costs at them from
`Corollary31.costs`. What is left is to compare the bounds: γ(c', θ') ≥ γ(c, θ) and q(θ') ≤ q(θ)
make the bounds at the rational parameters smaller (`le_preBound31`, `le_queryBound31`), and both
bounds are at least 1 (`one_le_preBound31`, `one_le_queryBound31`), so that additive constants can
be absorbed.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

/-- The bound on the preprocessing, N² (log D + 1)²/D^γ. -/
noncomputable def preBound31 (γ : ℝ) (N D₀ : ℕ) : ℝ :=
  (N : ℝ) ^ 2 * (Real.log D₀ + 1) ^ 2 / (D₀ : ℝ) ^ γ
/-- The bound on a query, D^q (log D + 1); the summand 1 makes it at least 1 at D = 1. -/
noncomputable def queryBound31 (q : ℝ) (D₀ : ℕ) : ℝ := (D₀ : ℝ) ^ q * (Real.log D₀ + 1)

/-- ε γ ≤ 1 for ε < R_c(γ). -/
theorem eps_mul_gamma_le (c γ ε : ℝ) (hc : 10 < c) (hγ : 0 < γ) (hε : ε < Rc c γ) :
    ε * γ ≤ 1 := by
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hB := lnΛ_ge c γ hc.le
  have h10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hpos : 0 < lnΛ c γ := lnΛ_pos c γ hc.le hγ.le
  have h1 : Rc c γ * γ ≤ 1 := by
    unfold Rc
    rw [div_mul_eq_mul_div, div_le_one hpos]
    nlinarith
  nlinarith

section bounds

variable {N D₀ : ℕ}

/-- D ≤ N^ε with ε ≤ 1 gives D ≤ N. -/
private theorem le_of_le_rpow {ε : ℝ} (hN : 1 ≤ N) (hε : ε ≤ 1) (h : (D₀ : ℝ) ≤ (N : ℝ) ^ ε) :
    D₀ ≤ N := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have : (D₀ : ℝ) ≤ (N : ℝ) :=
    h.trans ((Real.rpow_le_rpow_of_exponent_le hNR hε).trans_eq (Real.rpow_one _))
  exact_mod_cast this

/-- D ≤ N^ε with ε γ ≤ 1 gives D^γ ≤ N². -/
private theorem rpow_le_sq {ε γ : ℝ} (hN : 1 ≤ N) (hγ : 0 ≤ γ) (hεγ : ε * γ ≤ 1)
    (h : (D₀ : ℝ) ≤ (N : ℝ) ^ ε) : (D₀ : ℝ) ^ γ ≤ (N : ℝ) ^ 2 := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc (D₀ : ℝ) ^ γ ≤ ((N : ℝ) ^ ε) ^ γ := Real.rpow_le_rpow (by positivity) h hγ
    _ = (N : ℝ) ^ (ε * γ) := by rw [← Real.rpow_mul (by positivity)]
    _ ≤ (N : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
    _ = (N : ℝ) ^ 2 := by norm_cast

/-- The bound on the preprocessing is at least 1 if D^γ ≤ N². -/
private theorem one_le_preBound31 {γ : ℝ} (hD : 1 ≤ D₀) (h : (D₀ : ℝ) ^ γ ≤ (N : ℝ) ^ 2) :
    1 ≤ preBound31 γ N D₀ := by
  have hDR : (1 : ℝ) ≤ D₀ := by exact_mod_cast hD
  have hlog := Real.log_nonneg hDR
  unfold preBound31
  rw [le_div_iff₀ (Real.rpow_pos_of_pos (by linarith) _), one_mul]
  exact h.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith)))

/-- The bound on a query is at least 1. -/
private theorem one_le_queryBound31 {q : ℝ} (hD : 1 ≤ D₀) (hq : 0 ≤ q) : 1 ≤ queryBound31 q D₀ := by
  have hDR : (1 : ℝ) ≤ D₀ := by exact_mod_cast hD
  have hlog := Real.log_nonneg hDR
  exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hDR hq) (by linarith)

/-- A larger exponent of D in the denominator, and log D in place of log D + 1, make the bound on
the preprocessing smaller. -/
private theorem le_preBound31 {γ γ' : ℝ} (hD : 1 ≤ D₀) (hγ : γ ≤ γ') :
    (N : ℝ) ^ 2 * Real.log (D₀ : ℝ) ^ 2 / (D₀ : ℝ) ^ γ' ≤ preBound31 γ N D₀ := by
  have hDR : (1 : ℝ) ≤ D₀ := by exact_mod_cast hD
  have hlog := Real.log_nonneg hDR
  have hsq : Real.log (D₀ : ℝ) ^ 2 ≤ (Real.log D₀ + 1) ^ 2 := pow_le_pow_left₀ hlog (by linarith) 2
  exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hsq (by positivity))
    (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_le_rpow_of_exponent_le hDR hγ)

/-- A smaller exponent of D, and log D in place of log D + 1, make the bound on a query smaller. -/
private theorem le_queryBound31 {q q' : ℝ} (hD : 1 ≤ D₀) (hq : q' ≤ q) :
    (D₀ : ℝ) ^ q' * Real.log (D₀ : ℝ) ≤ queryBound31 q D₀ := by
  have hDR : (1 : ℝ) ≤ D₀ := by exact_mod_cast hD
  have hlog := Real.log_nonneg hDR
  exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hDR hq) (by linarith) hlog (by positivity)

end bounds

/-- **The parameters of the program.** On every instance with 1 ≤ D ≤ N^ε the two bounds are at
least 1, and from the threshold on the hypotheses of Theorem 30 hold and its costs are within a
constant times the two bounds. -/
theorem exists_ratParams {c θ ε : ℝ} (h : Admissible c θ ε) :
    ∃ (G : RatParams) (C : ℝ), 0 ≤ C ∧ ∀ N D₀ : ℕ, 1 ≤ N → 1 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      CostsWithin G C N D₀ (preBound31 (gammaOf c θ) N D₀) (queryBound31 (qOf θ) D₀) := by
  -- rational parameters, and the costs of Corollary 31 at them
  obtain ⟨a, b, p, q, hG⟩ := exists_rat_params h
  obtain ⟨C, m₁, hC, hcost⟩ := Corollary31.costs hG.admissible
  obtain ⟨hc, hθ0, hθ1, hε⟩ := h
  have hγ := corollary_31_gamma_pos c θ hc hθ0
  have hε1 : ε ≤ 1 := by
    have := sec4_Rc_lt_epsStar c (gammaOf c θ) hc hγ.le
    have := sec4_epsStar_numeric.2
    linarith
  refine ⟨⟨a, b, p, q, max m₁ 1, hG.b_pos, hG.q_pos, hG.ratio_gt, hG.p_pos, hG.switch_lt,
      le_max_right _ _⟩, C, hC,
    fun N D₀ hN hD hDN => ⟨hN, hD, le_of_le_rpow hN hε1 hDN,
      one_le_preBound31 hD (rpow_le_sq hN hγ.le (eps_mul_gamma_le c _ ε hc hγ hε) hDN),
      one_le_queryBound31 hD (qOf_nonneg θ hθ0 hθ1), fun hm => ?_⟩⟩
  -- from the threshold on
  have hm1 : 1 ≤ logFour D₀ := le_trans (le_max_right m₁ 1) hm
  obtain ⟨hfit, hpre, hquery⟩ := hcost D₀ N (logFour D₀) (two_le_of_clog hm1) hDN
    (ceil_logb_four D₀).symm (le_trans (le_max_left m₁ 1) hm)
  rw [levelsOf_div a _ hG.b_pos] at hfit hpre hquery
  rw [switchOf_div p _ hG.q_pos] at hpre hquery
  exact ⟨⟨hm1, RatParams.ten_le_L _ _, RatParams.t_le _ _, hfit⟩,
    hpre.trans (mul_le_mul_of_nonneg_left (le_preBound31 hD hG.gamma_le) hC),
    hquery.trans (mul_le_mul_of_nonneg_left (le_queryBound31 hD hG.qOf_le) hC)⟩

end Light.Sec4
