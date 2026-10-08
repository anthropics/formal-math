/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec4.Corollary31

/-!
# Corollary 31: the limit `ε*`; the choice of `c` and `θ` in the proof of Theorem 24

The bound `R_c(γ) = ln 4/ln Λ` of equation (11) increases to `ε* = ln 4/(5 ln 10) = 0.1204…` as `c`
decreases to 10 and `γ` to 0.

* The limit. The paper's "direct calculation" is done here with the derivative of `ln Λ` with
  respect to `c`, which is positive (`hasDerivAt_lnΛ`, `deriv_lnΛ_pos`), so `R_c(γ)` decreases in
  `c` (`sec4_Rc_strictAntiOn`); at `c = 10`, `γ = 0` the identity `H(1/10) + (9/10) ln 9 = ln 10`
  gives `ln Λ = 5 ln 10` (`lnΛ_ten_zero`, `tendsto_lnΛ`). Hence `sec4_Rc_zero_tendsto`,
  `sec4_Rc_lt_epsStar`, and the value `sec4_epsStar_numeric`.
* The proof of Theorem 24. Given `ε < ε*` and `q > 0`, first `c` and then `θ` are chosen by
  continuity (`exists_admissible`).
-/

public section

open Finset

namespace ThreeSumApsp

/-! ### The limit `ε*` -/

/-- `H(x) - x H'(x) = -ln(1-x)` for `0 < x < 1`, with `H'(x) = ln((1-x)/x)` (see
`hasDerivAt_entropy`). -/
theorem entropy_sub_mul_deriv (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    entropy x - x * Real.log ((1 - x) / x) = -Real.log (1 - x) := by
  rw [entropy, Real.log_div (sub_pos.2 hx1).ne' hx0.ne']
  ring

/-- The derivative of `c H(1/c)` with respect to `c` is `H(1/c) - (1/c) H'(1/c) = ln(c/(c-1))`. -/
private lemma hasDerivAt_mul_entropy_inv (c : ℝ) (hc : 1 < c) :
    HasDerivAt (fun x : ℝ => x * entropy (1 / x)) (Real.log (c / (c - 1))) c := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hx0 : (0 : ℝ) < 1 / c := by positivity
  have hx1 : 1 / c < 1 := by rw [div_lt_one hc0]; exact hc
  have hinv : HasDerivAt (fun x : ℝ => 1 / x) (-(c ^ 2)⁻¹) c := by
    simpa only [one_div] using hasDerivAt_inv hc0.ne'
  have hcomp : HasDerivAt (fun x : ℝ => entropy (1 / x))
      (Real.log ((1 - 1 / c) / (1 / c)) * -(c ^ 2)⁻¹) c :=
    (hasDerivAt_entropy (1 / c) hx0 hx1).comp c hinv
  have hmul := (hasDerivAt_id c).mul hcomp
  refine hmul.congr_deriv ?_
  have hkey := entropy_sub_mul_deriv (1 / c) hx0 hx1
  have hlog : -Real.log (1 - 1 / c) = Real.log (c / (c - 1)) := by
    rw [← Real.log_inv]
    congr 1
    have : c - 1 ≠ 0 := by linarith
    field_simp
  rw [← hlog, ← hkey]
  simp only [id]
  field_simp
  ring

/-- The derivative of `ln Λ` with respect to `c` is `ln(10/3) - (1/2) ln(c/(c-1))`, for `c > 1` and
every `γ`. -/
theorem hasDerivAt_lnΛ (c γ : ℝ) (hc : 1 < c) :
    HasDerivAt (fun x : ℝ => lnΛ x γ) (Real.log (10 / 3) - (1 / 2) * Real.log (c / (c - 1))) c := by
  -- the three summands of `ln Λ` that depend on `c`
  have hten : HasDerivAt (fun x : ℝ => x * Real.log 10) (Real.log 10) c := by
    simpa using (hasDerivAt_id c).mul_const (Real.log 10)
  have hent : HasDerivAt (fun x : ℝ => (1 / 2) * (x * entropy (1 / x)))
      ((1 / 2) * Real.log (c / (c - 1))) c := (hasDerivAt_mul_entropy_inv c hc).const_mul _
  have hthree : HasDerivAt (fun x : ℝ => (x - 1) * Real.log 3) (Real.log 3) c := by
    simpa using ((hasDerivAt_id c).sub_const 1).mul_const (Real.log 3)
  have h := ((hten.sub hent).sub hthree).add_const (γ * Real.log 4)
  have hlog : Real.log (10 / 3) = Real.log 10 - Real.log 3 :=
    Real.log_div (by norm_num) (by norm_num)
  rw [hlog]
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  simp only [lnΛ, Pi.sub_apply]
  ring

/-- The derivative of `ln Λ` with respect to `c` is positive for `c ≥ 10`, because
`c/(c-1) ≤ 10/9 < (10/3)²`. -/
theorem deriv_lnΛ_pos {c : ℝ} (hc : 10 ≤ c) :
    0 < Real.log (10 / 3) - (1 / 2) * Real.log (c / (c - 1)) := by
  have hle : Real.log (c / (c - 1)) ≤ Real.log (10 / 9) := by
    refine Real.log_le_log (div_pos (by linarith) (by linarith)) ?_
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hlt : Real.log (10 / 9) < 2 * Real.log (10 / 3) := by
    rw [show 2 * Real.log (10 / 3) = Real.log ((10 / 3) ^ 2) by rw [Real.log_pow]; norm_num]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-- Proof of Corollary 31: "the identity H(1/10) + (9/10) ln 9 = ln 10". -/
theorem entropy_one_tenth : entropy (1 / 10) + (9 / 10) * Real.log 9 = Real.log 10 := by
  rw [entropy, show (1 : ℝ) - 1 / 10 = 9 / 10 by norm_num, Real.log_div (by norm_num) (by norm_num),
    Real.log_div (by norm_num) (by norm_num), Real.log_one]
  ring

/-- At `c = 10` and `γ = 0`, `ln Λ = 10 ln 10 - 5 H(1/10) - 9 ln 3 = 5 ln 10`. -/
theorem lnΛ_ten_zero : lnΛ 10 0 = 5 * Real.log 10 := by
  have h := entropy_one_tenth
  rw [Real.log_nine] at h
  simp only [lnΛ]
  linarith

/-- Proof of Corollary 31: "ln Λ increases with c", on `[10, ∞)` and for every `γ`, since its
derivative is positive. -/
private lemma lnΛ_strictMonoOn (γ : ℝ) : StrictMonoOn (fun c : ℝ => lnΛ c γ) (Set.Ici 10) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 10) (fun c hc => ?_) fun c hc => ?_
  · have hc : 10 ≤ c := hc
    exact (hasDerivAt_lnΛ c γ (by linarith)).continuousAt.continuousWithinAt
  · rw [interior_Ici] at hc
    have hc : 10 < c := hc
    rw [(hasDerivAt_lnΛ c γ (by linarith)).deriv]
    exact deriv_lnΛ_pos hc.le

/-- `ln 10 > 0`. -/
private lemma log_ten_pos : 0 < Real.log 10 := Real.log_pos (by norm_num)

/-- For `c ≥ 10`, `ln Λ ≥ 5 ln 10 + γ ln 4`, its value at `c = 10`. -/
theorem lnΛ_ge (c γ : ℝ) (hc : 10 ≤ c) : 5 * Real.log 10 + γ * Real.log 4 ≤ lnΛ c γ := by
  rw [lnΛ_eq_add c γ, ← lnΛ_ten_zero]
  have := (lnΛ_strictMonoOn 0).monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hc) hc
  simpa using this

/-- Corollary 31: "R_c(0) increases [...] as c decreases to 10": the monotonicity.  It holds for
every fixed `γ ≥ 0`; the paper says it for `γ = 0` ("for γ = 0, ln Λ increases with c", proof of
Corollary 31). -/
theorem sec4_Rc_strictAntiOn (γ : ℝ) (hγ : 0 ≤ γ) :
    StrictAntiOn (fun c : ℝ => Rc c γ) (Set.Ici 10) := by
  intro c₁ h₁ c₂ h₂ h
  exact div_lt_div_of_pos_left log_four_pos (lnΛ_pos c₁ γ h₁ hγ) (lnΛ_strictMonoOn γ h₁ h₂ h)

/-- Proof of Corollary 31: "for γ = 0, ln Λ [...] tends to 5 ln 10 as c decreases to 10, by the
identity H(1/10) + (9/10) ln 9 = ln 10". The limit is the value at `c = 10` (`lnΛ_ten_zero`). -/
theorem tendsto_lnΛ :
    Filter.Tendsto (fun c : ℝ => lnΛ c 0) (nhdsWithin 10 (Set.Ioi 10))
      (nhds (5 * Real.log 10)) := by
  have h := (hasDerivAt_lnΛ 10 0 (by norm_num)).continuousAt.tendsto
  simp only [lnΛ_ten_zero] at h
  exact tendsto_nhdsWithin_of_tendsto_nhds h

/-- Corollary 31: "Moreover, R_c(0) increases to ε* = ln 4/(5 ln 10) = 0.1204… as c decreases to
10": the limit. (The monotonicity is `sec4_Rc_strictAntiOn` at `γ = 0`.) -/
theorem sec4_Rc_zero_tendsto :
    Filter.Tendsto (fun c : ℝ => Rc c 0) (nhdsWithin 10 (Set.Ioi 10)) (nhds epsStar) :=
  tendsto_const_nhds.div tendsto_lnΛ (mul_pos (by norm_num) log_ten_pos).ne'

/-- Section 4.1: "Let ε* := ln 4/(5 ln 10) = 0.1204…". -/
theorem sec4_epsStar_numeric : 0.1204 < epsStar ∧ epsStar < 0.1205 := by
  have hten := log_ten_pos
  -- `10^59 < 2^196` and `2^93 < 10^28` give `59/196 < ln 2 / ln 10 < 28/93`.
  have hlo : 59 * Real.log 10 < 196 * Real.log 2 := by
    have := Real.log_lt_log (by positivity) (by norm_num : (10 : ℝ) ^ 59 < 2 ^ 196)
    simpa [Real.log_pow] using this
  have hhi : 93 * Real.log 2 < 28 * Real.log 10 := by
    have := Real.log_lt_log (by positivity) (by norm_num : (2 : ℝ) ^ 93 < 10 ^ 28)
    simpa [Real.log_pow] using this
  rw [epsStar, Real.log_four]
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    linarith
  · rw [div_lt_iff₀ (by positivity)]
    linarith

/-- Table 1, row `ε`: "R_c(γ) < 0.1204…", that is `R_c(γ) < ε*`, for `c > 10` and
`γ ≥ 0`. -/
theorem sec4_Rc_lt_epsStar (c γ : ℝ) (hc : 10 < c) (hγ : 0 ≤ γ) : Rc c γ < epsStar := by
  have hanti : Rc c γ < Rc 10 γ :=
    sec4_Rc_strictAntiOn γ hγ (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hc.le) hc
  -- at `c = 10` the denominator is at least `5 ln 10`
  have hge := lnΛ_ge 10 γ le_rfl
  have hγ4 := mul_nonneg hγ log_four_pos.le
  have hten := log_ten_pos
  exact hanti.trans_le
    (div_le_div_of_nonneg_left log_four_pos.le (by positivity) (by linarith))

/-! ### The choice of `c` and `θ` in the proof of Theorem 24 -/

/-- Proof of Theorem 24: "as θ → 0, the first expression tends to 0". The first expression is
`q = (H(θ) + θ ln 9)/ln 4`. -/
theorem tendsto_qOf_zero : Filter.Tendsto qOf (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h := continuous_qOf.tendsto 0
  rw [qOf_zero] at h
  exact tendsto_nhdsWithin_of_tendsto_nhds h

/-- As `θ → 0`, `γ = θ ln(1/ρ_c)/ln 4` tends to 0. -/
theorem tendsto_gammaOf_zero (c : ℝ) :
    Filter.Tendsto (gammaOf c) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h : Continuous (gammaOf c) := by
    unfold gammaOf
    fun_prop
  have hzero := h.tendsto 0
  rw [gammaOf_eq_mul, zero_mul] at hzero
  exact tendsto_nhdsWithin_of_tendsto_nhds hzero

/-- The choice of c and θ in the proof of Theorem 24. The paper: "Let ε < ε* and q > 0. Choose c >
10 with R_c(0) > ε (Corollary 31), and then θ ∈ (0, 0.9) small enough that (H(θ) + θ ln 9)/ln 4 < q
and R_c(θ ln(1/ρ_c)/ln 4) > ε." -/
theorem exists_admissible {ε q : ℝ} (hε : ε < epsStar) (hq : 0 < q) :
    ∃ c θ : ℝ, Admissible c θ ε ∧ qOf θ < q := by
  -- Choose `c > 10` with `R_c(0) > ε`.
  obtain ⟨c, hεc, hc⟩ :=
    ((sec4_Rc_zero_tendsto.eventually (lt_mem_nhds hε)).and self_mem_nhdsWithin).exists
  have hc : 10 < c := Set.mem_Ioi.1 hc
  -- `q` and `γ` tend to 0 with `θ`, and `R_c` is continuous.
  have hγ_within :
      Filter.Tendsto (gammaOf c) (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ici 0)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_gammaOf_zero c, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact (corollary_31_gamma_pos c θ hc hθ).le
  have hcont : Filter.Tendsto (fun γ => Rc c γ) (nhdsWithin 0 (Set.Ici 0)) (nhds (Rc c 0)) :=
    Rc_continuousOn c hc.le 0 (Set.mem_Ici.2 le_rfl)
  have hR : Filter.Tendsto (fun θ => Rc c (gammaOf c θ)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Rc c 0)) := hcont.comp hγ_within
  -- so all small `θ > 0` have `q(θ) < q`, `R_c(γ(θ)) > ε` and `θ < 0.9`
  have hrange : ∀ᶠ θ : ℝ in nhdsWithin 0 (Set.Ioi 0), θ ∈ Set.Ioo (0 : ℝ) 0.9 :=
    Ioo_mem_nhdsGT (by norm_num)
  obtain ⟨θ, hqθ, hεθ, hθ⟩ := ((tendsto_qOf_zero.eventually (gt_mem_nhds hq)).and
    ((hR.eventually (lt_mem_nhds hεc)).and hrange)).exists
  exact ⟨c, θ, ⟨hc, hθ.1, hθ.2, hεθ⟩, hqθ⟩

end ThreeSumApsp
