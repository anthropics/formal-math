/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec4.Corollary31
public import ThreeSumApsp.Util.Ceil

/-!
# Rational parameters for Corollary 31

Corollary 31 has real parameters `c > 10` and `0 < θ < 0.9`, and a real `ε < R_c(γ)` with
`γ = θ ln(1/ρ_c)/ln 4`. A program can only contain rational numbers. This file shows that the
parameters can be replaced by rational ones without loss (`exists_rat_params`): first a rational
`c' > c` so close to `c` that `ε` is still below `R_{c'}(γ)`, by continuity (`continuousAt_Rc`);
then a rational `θ' < θ` so close to `θ` that the exponent `γ` of `c'` and `θ'` is still at least
that of `c` and `θ`. A smaller `θ` makes `q` smaller and `R_{c'}(γ)` larger. The file also writes
the numbers `⌈c m⌉` and `⌈θ m⌉` for rational parameters in integer arithmetic (`levelsOf_div`,
`switchOf_div`).
-/

@[expose] public section

namespace ThreeSumApsp

/-- Between two real numbers, the smaller of which is not negative, lies a quotient of two natural
numbers. -/
private lemma exists_nat_div_btwn {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    ∃ a b : ℕ, 1 ≤ b ∧ x < (a : ℝ) / b ∧ (a : ℝ) / b < y := by
  obtain ⟨r, hxr, hry⟩ := exists_rat_btwn hxy
  have hr : 0 ≤ r := by exact_mod_cast hx.trans hxr.le
  have hcast : ((r.num.toNat : ℕ) : ℝ) / (r.den : ℝ) = r := by
    rw [Rat.cast_def, ← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.2 hr)]
  exact ⟨r.num.toNat, r.den, r.den_pos, hcast ▸ hxr, hcast ▸ hry⟩

/-- With `θ` fixed, `R_c(γ)` is continuous in `c`. -/
private lemma continuousAt_Rc {c θ : ℝ} (hc : 10 < c) (hθ : 0 < θ) :
    ContinuousAt (fun x : ℝ => Rc x (gammaOf x θ)) c := by
  have hc0 : c ≠ 0 := by linarith
  have hc9 : (c - 1) / 9 ≠ 0 := by linarith
  have hgamma : ContinuousAt (fun x : ℝ => gammaOf x θ) c := by
    simp only [gammaOf, one_div_rhoC]
    exact (continuousAt_const.mul
      (((continuousAt_id.sub continuousAt_const).div_const 9).log hc9)).div_const _
  have hentropy : ContinuousAt (fun x : ℝ => entropy (1 / x)) c :=
    entropy_continuous.continuousAt.comp (continuousAt_const.div continuousAt_id hc0)
  have hlnΛ : ContinuousAt (fun x : ℝ => lnΛ x (gammaOf x θ)) c := by
    unfold lnΛ
    fun_prop
  exact continuousAt_const.div hlnΛ (lnΛ_pos c _ hc.le (corollary_31_gamma_pos c θ hc hθ).le).ne'

/-- The rational numbers `a/b` and `p/q` can take the place of the parameters `c` and `θ` of
Corollary 31, for the same `ε`. -/
structure RatApprox (c θ ε : ℝ) (a b p q : ℕ) : Prop where
  b_pos : 1 ≤ b
  q_pos : 1 ≤ q
  /-- `a/b > 10`, in the natural numbers. -/
  ratio_gt : 10 * b < a
  /-- `p/q > 0`, in the natural numbers. -/
  p_pos : 1 ≤ p
  /-- `p/q < 0.9`, in the natural numbers. -/
  switch_lt : 10 * p < 9 * q
  /-- The hypotheses of Corollary 31 hold for `a/b`, `p/q` and `ε`. -/
  admissible : Admissible ((a : ℝ) / b) ((p : ℝ) / q) ε
  /-- The exponent `γ` does not get smaller. -/
  gamma_le : gammaOf c θ ≤ gammaOf ((a : ℝ) / b) ((p : ℝ) / q)
  /-- The exponent `q` does not get larger. -/
  qOf_le : qOf ((p : ℝ) / q) ≤ qOf θ

/-- A rational `c' = a/b` above `c` for which `ε` is still below `R_{c'}(γ)`, at the same `θ`. -/
private lemma exists_rat_ratio {c θ ε : ℝ} (h : Admissible c θ ε) :
    ∃ a b : ℕ, 1 ≤ b ∧ c < (a : ℝ) / b ∧ ε < Rc ((a : ℝ) / b) (gammaOf ((a : ℝ) / b) θ) := by
  have hc := h.c_gt
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    ((continuousAt_Rc hc h.θ_pos).tendsto.eventually_const_lt h.thin)
  obtain ⟨a, b, hb, hca, hac⟩ := exists_nat_div_btwn (x := c) (y := c + δ) (by linarith)
    (by linarith)
  exact ⟨a, b, hb, hca, hball (by rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith)⟩

/-- **Rational parameters suffice.** For `c`, `θ`, `ε` as in Corollary 31 there are rational numbers
`c' = a/b > c` and `θ' = p/q < θ` that satisfy the hypotheses of the corollary with the same `ε`,
and whose exponents are no worse: `γ(c', θ') ≥ γ(c, θ)` and `q(θ') ≤ q(θ)`. -/
theorem exists_rat_params {c θ ε : ℝ} (h : Admissible c θ ε) :
    ∃ a b p q : ℕ, RatApprox c θ ε a b p q := by
  obtain ⟨a, b, hb, hca, hε'⟩ := exists_rat_ratio h
  obtain ⟨hc, hθ0, hθ1, -⟩ := h
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hc' : (10 : ℝ) < (a : ℝ) / b := hc.trans hca
  have hlog' := log_inv_rhoC_pos hc'
  -- a rational `θ'` between `θ ln(1/ρ_c)/ln(1/ρ_{c'})` and `θ`
  have hlow : θ * Real.log (1 / rhoC c) / Real.log (1 / rhoC ((a : ℝ) / b)) < θ :=
    (div_lt_iff₀ hlog').2 (mul_lt_mul_of_pos_left (log_inv_rhoC_lt hc hca) hθ0)
  obtain ⟨p, q, hq, hlp, hpθ⟩ := exists_nat_div_btwn
    (div_nonneg (mul_nonneg hθ0.le (log_inv_rhoC_pos hc).le) hlog'.le) hlow
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hθ'0 : (0 : ℝ) < (p : ℝ) / q :=
    (div_nonneg (mul_nonneg hθ0.le (log_inv_rhoC_pos hc).le) hlog'.le).trans_lt hlp
  have hθ'1 : (p : ℝ) / q < 0.9 := hpθ.trans hθ1
  -- `γ` gets smaller with `θ`, so `R_{c'}(γ)` gets larger
  have hγ' := corollary_31_gamma_pos _ _ hc' hθ'0
  have hγlt : gammaOf ((a : ℝ) / b) ((p : ℝ) / q) < gammaOf ((a : ℝ) / b) θ :=
    gammaOf_strictMono _ hc' hpθ
  have hthin := hε'.trans (Rc_strictAntiOn_right _ hc'.le (Set.mem_Ici.2 hγ'.le)
    (Set.mem_Ici.2 (hγ'.trans hγlt).le) hγlt)
  refine ⟨a, b, p, q, hb, hq, ?_, ?_, ?_, ⟨hc', hθ'0, hθ'1, hthin⟩, ?_,
    (qOf_strictMonoOn ⟨hθ'0.le, hθ'1.le⟩ ⟨hθ0.le, hθ1.le⟩ hpθ).le⟩
  · exact_mod_cast (lt_div_iff₀ hb').1 hc'
  · exact Nat.pos_of_ne_zero fun hp => by simp [hp] at hθ'0
  · have hpq : (10 : ℝ) * p < 9 * q := by linarith [(div_lt_iff₀ hq').1 hθ'1]
    exact_mod_cast hpq
  · exact div_le_div_of_nonneg_right ((div_lt_iff₀ hlog').1 hlp).le log_four_pos.le

/-- `L = ⌈c m⌉` for a rational `c = a/b`. -/
theorem levelsOf_div (a m : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    levelsOf ((a : ℝ) / b) m = (a * m + b - 1) / b := by
  unfold levelsOf
  rw [← Nat.ceilDiv_eq_add_pred_div, ← Nat.ceil_div_eq_ceilDiv (a * m) hb]
  congr 1
  push_cast
  ring

/-- `t = ⌈θ m⌉` for a rational `θ = p/q`. -/
theorem switchOf_div (p m : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    switchOf ((p : ℝ) / q) m = (p * m + q - 1) / q := by
  unfold switchOf
  rw [← Nat.ceilDiv_eq_add_pred_div, ← Nat.ceil_div_eq_ceilDiv (p * m) hq]
  congr 1
  push_cast
  ring

end ThreeSumApsp
