/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements
public import ThreeSumApsp.Util.Basic
public import ThreeSumApsp.Util.Choose
public import ThreeSumApsp.Util.Log
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# 4.4 Choosing the parameters: the entropy function, the exponents `γ` and `q`, equation (11)

Section 4.4 chooses the parameters `L` and `t` of Theorem 30. This file has the facts that its
proofs use about `D = 4^m` and about the notions with which Corollary 31 is stated ("Other choices
of the parameters"). The notation of the paper: `entropy` is `H`, `rhoC c` is `ρ_c = 9/(c-1)`,
`gammaOf c θ` is `γ = θ ln(1/ρ_c)/ln 4`, `qOf θ` is `q = (H(θ) + θ ln 9)/ln 4`, `lnΛ c γ` is the
denominator `ln Λ` of (11), `Rc c γ` is `R_c(γ) = ln 4/ln Λ`, and `D m` is `D = 4^m`.

* The entropy function `H` is Mathlib's `Real.binEntropy` (`entropy_eq_binEntropy`); continuity,
  concavity and the derivative come from there.
* Powers and logarithms of `D = 4^m` (`cast_D_pos`, `one_le_cast_D`, `log_cast_D`,
  `cast_le_log_cast_D`, `cast_D_rpow`).
* The bound `binom(n, k) ≥ e^{n H(k/n)}/(n+1)` (`exp_entropy_div_le_choose`): it is the standard
  bound `binom(n, k) ≥ 1/(n+1) · n^n/(k^k (n-k)^{n-k})`, as `e^{n H(k/n)} = n^n/(k^k (n-k)^{n-k})`.
* One section for each of `ρ_c`, `γ`, `q`, and `ln Λ` with `R_c(γ)`: signs, monotonicity and
  continuity, and the three facts that tie them to the costs: `ρ_c^{θm} = D^{-γ}`
  (`rhoC_rpow_eq_D_rpow`), `e^{m(H(θ) + θ ln 9)} = D^q` (`exp_entropy_eq_D_rpow_qOf`), and
  `Λ < 4^{1/ε}` if and only if `ε < R_c(γ)` (`eq_11_iff`).
-/

public section

open Finset

namespace ThreeSumApsp

/-! ### The entropy function: the link with Mathlib's `Real.binEntropy` -/

/-- The entropy function of Section 4.4 is Mathlib's binary entropy function. -/
theorem entropy_eq_binEntropy : entropy = Real.binEntropy := by
  funext x
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, entropy, Real.negMulLog, Real.negMulLog]
  ring

/-- The entropy function is continuous on the whole real line. -/
theorem entropy_continuous : Continuous entropy := by
  rw [entropy_eq_binEntropy]
  exact Real.binEntropy_continuous

/-- `H(x) ≥ 0` for `0 ≤ x ≤ 1`. -/
theorem entropy_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ entropy x := by
  rw [entropy_eq_binEntropy]
  exact Real.binEntropy_nonneg hx0 hx1

/-- `H(x) ≤ ln 2`. -/
private lemma entropy_le_log_two (x : ℝ) : entropy x ≤ Real.log 2 := by
  rw [entropy_eq_binEntropy]
  exact Real.binEntropy_le_log_two

/-- `H(0) = 0`. -/
theorem entropy_zero : entropy 0 = 0 := by simp [entropy]

/-- The entropy function is concave on `[0, 1]`. -/
theorem entropy_concaveOn : ConcaveOn ℝ (Set.Icc 0 1) entropy := by
  rw [entropy_eq_binEntropy]
  exact Real.strictConcave_binEntropy.concaveOn

/-- The derivative of the entropy function, `H'(x) = ln((1-x)/x)` for `0 < x < 1`. -/
theorem hasDerivAt_entropy (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt entropy (Real.log ((1 - x) / x)) x := by
  rw [entropy_eq_binEntropy, Real.log_div (by linarith) hx0.ne']
  exact Real.hasDerivAt_binEntropy hx0.ne' hx1.ne

/-! ### Powers and logarithms of `D = 4^m` -/

/-- `ln 4 > 0`. -/
theorem log_four_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)

/-- `D = 4^m` as a real number. -/
theorem cast_D_eq (m : ℕ) : (D m : ℝ) = (4 : ℝ) ^ m := by
  simp [D]

/-- `D > 0`. -/
theorem cast_D_pos (m : ℕ) : (0 : ℝ) < (D m : ℝ) := by
  rw [cast_D_eq]
  positivity

/-- `D ≥ 1`. -/
theorem one_le_cast_D (m : ℕ) : (1 : ℝ) ≤ (D m : ℝ) := by
  rw [cast_D_eq]
  exact one_le_pow₀ (by norm_num)

/-- `ln D = m ln 4`. -/
theorem log_cast_D (m : ℕ) : Real.log (D m : ℝ) = (m : ℝ) * Real.log 4 := by
  rw [cast_D_eq, Real.log_pow]

/-- `m ≤ ln D`. -/
theorem cast_le_log_cast_D (m : ℕ) : (m : ℝ) ≤ Real.log (D m : ℝ) := by
  rw [log_cast_D]
  exact le_mul_of_one_le_right (Nat.cast_nonneg m) Real.one_le_log_four

/-- `D^x = e^{x m ln 4}`. -/
theorem cast_D_rpow (m : ℕ) (x : ℝ) :
    (D m : ℝ) ^ x = Real.exp (x * ((m : ℝ) * Real.log 4)) := by
  rw [Real.rpow_def_of_pos (cast_D_pos m), log_cast_D]
  ring_nf

/-! ### The lower bound on binomial coefficients by the entropy function -/

/-- `x^j = e^{j ln x}` for `x ≥ 0`, provided that `x = 0` forces `j = 0`. -/
private lemma pow_eq_exp_mul_log (x : ℝ) (j : ℕ) (hx : 0 ≤ x) (h : x = 0 → j = 0) :
    x ^ j = Real.exp (j * Real.log x) := by
  rcases hx.eq_or_lt with hx0 | hx'
  · subst hx0
    simp [h rfl]
  · rw [Real.exp_nat_mul, Real.exp_log hx']

/-- `e^{b H(a/b)} = 1 / (p^a (1-p)^{b-a})` with `p = a/b`. -/
private lemma exp_entropy_eq (a b : ℕ) (hab : a ≤ b) (hb : 1 ≤ b) :
    Real.exp ((b : ℝ) * entropy ((a : ℝ) / (b : ℝ)))
      = (((a : ℝ) / b) ^ a * (1 - (a : ℝ) / b) ^ (b - a))⁻¹ := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  set p : ℝ := (a : ℝ) / b with hp
  have hbp : (b : ℝ) * p = a := by rw [hp]; field_simp
  have hpa : p ^ a = Real.exp (a * Real.log p) := by
    refine pow_eq_exp_mul_log p a (by positivity) fun h0 => ?_
    rw [hp, div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact_mod_cast h0
    · exact absurd h0 hb0
  have h1pa : (1 - p) ^ (b - a) = Real.exp ((b - a : ℕ) * Real.log (1 - p)) := by
    refine pow_eq_exp_mul_log (1 - p) (b - a) ?_ fun h0 => ?_
    · rw [hp, sub_nonneg, div_le_one (by positivity)]
      exact_mod_cast hab
    · have hp1 : p = 1 := by linarith
      have hab' : a = b := by exact_mod_cast (by rw [← hbp, hp1, mul_one] : (a : ℝ) = b)
      omega
  rw [hpa, h1pa, ← Real.exp_add, ← Real.exp_neg]
  congr 1
  unfold entropy
  rw [Nat.cast_sub hab, ← hbp]
  ring

/-- Proof of Corollary 31: "the same bound on the binomial coefficient, binom(n, k) ≥ e^{n
H(k/n)}/(n+1)", for `k ≤ n`. -/
theorem exp_entropy_div_le_choose (k n : ℕ) (hkn : k ≤ n) :
    Real.exp ((n : ℝ) * entropy ((k : ℝ) / (n : ℝ))) / ((n : ℝ) + 1) ≤ (Nat.choose n k : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : k = 0 := by omega
    simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- `e^{n H(k/n)} = 1/T` for `T = p^k (1-p)^{n-k}`, `p = k/n`, and `T n^n = k^k (n-k)^{n-k}`
  set T : ℝ := ((k : ℝ) / n) ^ k * (1 - (k : ℝ) / n) ^ (n - k) with hTdef
  have hexp : Real.exp ((n : ℝ) * entropy ((k : ℝ) / (n : ℝ))) = T⁻¹ := exp_entropy_eq k n hkn hn
  have hT : 0 < T := inv_pos.1 (hexp ▸ Real.exp_pos _)
  have hTn : T * (n : ℝ) ^ n = (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k) := by
    rw [hTdef, show 1 - (k : ℝ) / n = ((n - k : ℕ) : ℝ) / n by rw [Nat.cast_sub hkn]; field_simp,
      div_pow, div_pow, ← Nat.add_sub_cancel' hkn, pow_add, Nat.add_sub_cancel_left]
    field_simp
  have hstd : (n : ℝ) ^ n
      ≤ ((n : ℝ) + 1) * ((n.choose k : ℝ) * (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k)) := by
    exact_mod_cast Nat.pow_self_le_mul_choose_mul_pow_mul_pow hkn
  rw [hexp, inv_eq_one_div, div_div, div_le_iff₀ (by positivity)]
  refine le_of_mul_le_mul_right ?_ (pow_pos hn0 n)
  calc 1 * (n : ℝ) ^ n
      ≤ ((n : ℝ) + 1) * ((n.choose k : ℝ) * (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k)) := by
        rwa [one_mul]
    _ = (n.choose k : ℝ) * (T * ((n : ℝ) + 1)) * (n : ℝ) ^ n := by
        rw [mul_assoc (n.choose k : ℝ), ← hTn]
        ring

/-! ### The decay rate `ρ_c` -/

/-- `ρ_c = 9/(c-1) > 0` for `c > 10`. -/
theorem rhoC_pos {c : ℝ} (hc : 10 < c) : 0 < rhoC c := div_pos (by norm_num) (by linarith)

/-- `ρ_c = 9/(c-1) < 1` for `c > 10`. -/
theorem rhoC_lt_one {c : ℝ} (hc : 10 < c) : rhoC c < 1 :=
  (div_lt_one (by linarith)).2 (by linarith)

/-- `1/ρ_c = (c - 1)/9`. -/
theorem one_div_rhoC (c : ℝ) : 1 / rhoC c = (c - 1) / 9 := by
  rw [rhoC, one_div_div]

/-- `ln(1/ρ_c) = ln((c - 1)/9)` is positive for `c > 10`. -/
theorem log_inv_rhoC_pos {c : ℝ} (hc : 10 < c) : 0 < Real.log (1 / rhoC c) :=
  Real.log_pos (by rw [one_div_rhoC]; linarith)

/-- `ln(1/ρ_c)` increases with `c`. -/
theorem log_inv_rhoC_lt {c c' : ℝ} (hc : 10 < c) (h : c < c') :
    Real.log (1 / rhoC c) < Real.log (1 / rhoC c') := by
  rw [one_div_rhoC, one_div_rhoC]
  exact Real.log_lt_log (by linarith) (by linarith)

/-! ### The exponent `γ` -/

/-- `γ` is proportional to `θ`. -/
theorem gammaOf_eq_mul (c θ : ℝ) : gammaOf c θ = θ * gammaOf c 1 := by
  unfold gammaOf
  ring

/-- Corollary 31: "γ := θ ln(1/ρ_c)/ln 4 > 0". -/
theorem corollary_31_gamma_pos (c θ : ℝ) (hc : 10 < c) (hθ0 : 0 < θ) : 0 < gammaOf c θ :=
  div_pos (mul_pos hθ0 (log_inv_rhoC_pos hc)) log_four_pos

/-- `γ` increases with `θ` (for fixed `c > 10`). -/
theorem gammaOf_strictMono (c : ℝ) (hc : 10 < c) : StrictMono (fun θ : ℝ => gammaOf c θ) :=
  fun _ _ hab => div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hab (log_inv_rhoC_pos hc))
    log_four_pos

/-- At a fixed `θ > 0`, `γ` increases with the ratio `c > 10`, because `1/ρ_c = (c - 1)/9`. -/
theorem gammaOf_lt_gammaOf {θ c₁ c₂ : ℝ} (hθ : 0 < θ) (h1 : 10 < c₁) (h12 : c₁ < c₂) :
    gammaOf c₁ θ < gammaOf c₂ θ :=
  div_lt_div_of_pos_right (mul_lt_mul_of_pos_left (log_inv_rhoC_lt h1 h12) hθ) log_four_pos

/-- Proof of Corollary 31: "ρ_c^{θm} = D^{-γ}", with `D = 4^m` and `γ = θ ln(1/ρ_c)/ln 4`. -/
theorem rhoC_rpow_eq_D_rpow (c θ : ℝ) (hc : 10 < c) (m : ℕ) :
    rhoC c ^ (θ * (m : ℝ)) = (D m : ℝ) ^ (-gammaOf c θ) := by
  rw [cast_D_rpow, Real.rpow_def_of_pos (rhoC_pos hc)]
  congr 1
  have hfour := log_four_pos.ne'
  unfold gammaOf
  rw [one_div, Real.log_inv]
  field_simp

/-! ### The exponent `q` -/

/-- `q` is a continuous function of `θ`. -/
theorem continuous_qOf : Continuous qOf :=
  (entropy_continuous.add (continuous_id.mul continuous_const)).div_const _

/-- The exponent `q` is strictly increasing in `θ` on `[0, 0.9]`: the derivative of `H(θ) + θ ln 9`
is `ln(9(1-θ)/θ)`, which is positive for `0 < θ < 0.9`. -/
theorem qOf_strictMonoOn : StrictMonoOn qOf (Set.Icc 0 0.9) := by
  have hnum : StrictMonoOn (fun θ : ℝ => entropy θ + θ * Real.log 9) (Set.Icc 0 0.9) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 0.9)
      (entropy_continuous.add (continuous_id.mul continuous_const)).continuousOn fun θ hθ => ?_
    rw [interior_Icc] at hθ
    obtain ⟨hθ0, hθ1⟩ : 0 < θ ∧ θ < 0.9 := hθ
    have hderiv : HasDerivAt (fun θ : ℝ => entropy θ + θ * Real.log 9)
        (Real.log ((1 - θ) / θ) + 1 * Real.log 9) θ :=
      (hasDerivAt_entropy θ hθ0 (by linarith)).add ((hasDerivAt_id θ).mul_const (Real.log 9))
    rw [hderiv.deriv, one_mul, ← Real.log_mul (div_pos (by linarith) hθ0).ne' (by norm_num)]
    refine Real.log_pos ?_
    rw [div_mul_eq_mul_div, lt_div_iff₀ hθ0]
    linarith
  exact fun x hx y hy hxy => div_lt_div_of_pos_right (hnum hx hy hxy) log_four_pos

/-- The exponent `q` is not negative for `0 < θ < 0.9`. -/
theorem qOf_nonneg (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 0.9) : 0 ≤ qOf θ :=
  div_nonneg (add_nonneg (entropy_nonneg hθ0.le (by linarith))
    (mul_nonneg hθ0.le (Real.log_nonneg (by norm_num)))) log_four_pos.le

/-- `q` increases with `θ` from 0 to `log_4 10` on `(0, 0.9)`: the value at `θ = 0`. That `q`
increases is `qOf_strictMonoOn`. -/
theorem qOf_zero : qOf 0 = 0 := by
  simp [qOf, entropy]

/-- `q` increases with `θ` from 0 to `log_4 10` on `(0, 0.9)`: the value at `θ = 0.9`. Indeed
`H(0.9) + 0.9 ln 9 = ln 10`, because `ln 0.9 = ln 9 - ln 10` and `ln 0.1 = -ln 10`. -/
theorem qOf_nine_tenths : qOf 0.9 = Real.logb 4 10 := by
  have hnine : Real.log 0.9 = Real.log 9 - Real.log 10 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have htenth : Real.log (1 - 0.9) = -Real.log 10 := by
    rw [← Real.log_inv]
    norm_num
  rw [qOf, entropy, Real.logb, hnine, htenth]
  congr 1
  ring

/-- The sum `γ + q`, which is `κ` at the `θ` of an entry of the right half of Table 2, is continuous
in `θ`. -/
theorem continuous_gammaOf_add_qOf (c : ℝ) : Continuous fun θ : ℝ => gammaOf c θ + qOf θ := by
  refine Continuous.add ?_ continuous_qOf
  unfold gammaOf
  fun_prop

/-- `e^{m(H(θ) + θ ln 9)} = D^q` with `D = 4^m` and `q = (H(θ) + θ ln 9)/ln 4`. -/
theorem exp_entropy_eq_D_rpow_qOf (θ : ℝ) (m : ℕ) :
    Real.exp ((m : ℝ) * (entropy θ + θ * Real.log 9)) = (D m : ℝ) ^ qOf θ := by
  rw [cast_D_rpow]
  congr 1
  have hfour := log_four_pos.ne'
  unfold qOf
  field_simp

/-! ### The denominator `ln Λ` of equation (11), and `R_c(γ)` -/

/-- `ln Λ` depends on `γ` through the summand `γ ln 4` only. -/
theorem lnΛ_eq_add (c γ : ℝ) : lnΛ c γ = lnΛ c 0 + γ * Real.log 4 := by
  simp only [lnΛ]
  ring

/-- The denominator `ln Λ` of (11) is positive for `c ≥ 10` and `γ ≥ 0`. (Implicit in the paper,
which divides by it. Here it follows from `H ≤ ln 2` and `ln 10 = ln 2 + ln 5`.) -/
theorem lnΛ_pos (c γ : ℝ) (hc : 10 ≤ c) (hγ : 0 ≤ γ) : 0 < lnΛ c γ := by
  have hc0 : 0 ≤ c := by linarith
  have hthree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hten : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have hγ4 : 0 ≤ γ * Real.log 4 := mul_nonneg hγ log_four_pos.le
  have hcH : c * entropy (1 / c) ≤ c * Real.log 2 :=
    mul_le_mul_of_nonneg_left (entropy_le_log_two (1 / c)) hc0
  have hc2 : 0 ≤ c * Real.log 2 := mul_nonneg hc0 (Real.log_nonneg (by norm_num))
  have hc53 : 0 ≤ c * (Real.log 5 - Real.log 3) :=
    mul_nonneg hc0 (sub_nonneg.2 (Real.log_le_log (by norm_num) (by norm_num)))
  -- `ln Λ ≥ c (ln 2 + ln 5) - c ln 2/2 - (c - 1) ln 3 = c ln 2/2 + c (ln 5 - ln 3) + ln 3`
  unfold lnΛ
  rw [hten]
  linarith

/-- Equation (11) defines `R_c(γ) := ln 4/ln Λ` (the definition `Rc`, where `lnΛ c γ` is `ln Λ`).
The proof of Corollary 31 uses it in this form: "ε < R_c(γ) says that Λ < 4^{1/ε}".  Here `c ≥ 10`,
`γ ≥ 0`, and `ε > 0`, which the hypothesis 2 ≤ D ≤ N^ε of the corollary implies; for `ε ≤ 0`,
ε < R_c(γ) holds and Λ < 4^{1/ε} does not. -/
theorem eq_11_iff (c γ ε : ℝ) (hc : 10 ≤ c) (hγ : 0 ≤ γ) (hε : 0 < ε) :
    Real.exp (lnΛ c γ) < (4 : ℝ) ^ (1 / ε) ↔ ε < Rc c γ := by
  have hB := lnΛ_pos c γ hc hγ
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), Real.exp_lt_exp, Rc, lt_div_iff₀ hB,
    mul_one_div, lt_div_iff₀ hε, mul_comm]

/-- `R_c(γ)` is continuous in `γ`, which the proof of Theorem 24 uses ("as θ → 0, the first
expression tends to 0 and the second to R_c(0)"). -/
theorem Rc_continuousOn (c : ℝ) (hc : 10 ≤ c) : ContinuousOn (fun γ : ℝ => Rc c γ) (Set.Ici 0) := by
  refine ContinuousOn.div continuousOn_const ?_ fun γ hγ => (lnΛ_pos c γ hc hγ).ne'
  unfold lnΛ
  fun_prop

/-- `R_c(γ)` decreases as `γ` increases; so in "The ε of a row of the table is the smallest R_c(γ)
over its entries" (Section 4.4) the smallest is at the largest `γ` of the row. -/
theorem Rc_strictAntiOn_right (c : ℝ) (hc : 10 ≤ c) :
    StrictAntiOn (fun γ : ℝ => Rc c γ) (Set.Ici 0) := by
  intro γ₁ h₁ γ₂ _ h
  refine div_lt_div_of_pos_left log_four_pos (lnΛ_pos c γ₁ hc h₁) ?_
  rw [lnΛ_eq_add c γ₁, lnΛ_eq_add c γ₂]
  linarith [mul_lt_mul_of_pos_right h log_four_pos]

end ThreeSumApsp
