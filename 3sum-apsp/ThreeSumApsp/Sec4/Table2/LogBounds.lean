/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec4.ChoosingParameters

/-!
# The numerical toolkit for Table 2

Table 2 and the proof of Corollary 26 evaluate the exponents `q(θ)` and `γ = θ ln(1/ρ_c)/ln 4` of
Corollary 31 and the bound `R_c(γ)` of (11) at rational points. All three are built from logarithms
of rational numbers. This file turns each such claim into inequalities between rational numbers,
which the tactic `numerics` checks by evaluating both sides.

* `log_mem` encloses `log θ`: write `θ = 2^k (1 + x)/(1 - x)` with `2^k` near `θ`, and sum `n` terms
  of `log ((1 + x)/(1 - x)) = 2 (x + x³/3 + x⁵/5 + ⋯)`.
* `qOf_le` and `le_qOf` bound `q(θ)` at a rational `θ`.
* `gammaOf_one_mem`, `lnΛ_zero_mem`, `lt_Rc_of_lnΛ_zero_mem` and `Rc_lt_of_lnΛ_zero_mem` treat the
  two numbers on which a row of the table depends: `ln(1/ρ_c)/ln 4` and the denominator of (11) at
  `γ = 0`.
* `Table2Query.intro`, `Table2Ninth.intro` and `Table2Density.intro` give an entry of the table from
  two rational numbers that enclose its `θ`; the `θ` itself comes from the intermediate value
  theorem.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## Logarithms of rational numbers -/

/-- Mathlib's lower bound on `ln 2 = 0.693147180559…`. -/
noncomputable def logTwoLo : ℝ := 0.6931471803

/-- Mathlib's upper bound on `ln 2 = 0.693147180559…`. -/
noncomputable def logTwoHi : ℝ := 0.6931471808

/-- A lower bound on `ln 3 = 1.098612288668…`. -/
noncomputable def logThreeLo : ℝ := 1.0986122881

/-- An upper bound on `ln 3 = 1.098612288668…`. -/
noncomputable def logThreeHi : ℝ := 1.0986122892

/-- A lower bound on `ln 10 = 2.302585092994…`. -/
noncomputable def logTenLo : ℝ := 2.3025850922

/-- An upper bound on `ln 10 = 2.302585092994…`. -/
noncomputable def logTenHi : ℝ := 2.3025850938

/-- The `x` with `θ = 2^k (1 + x)/(1 - x)`. It is small when `2^k` is near `θ`. -/
noncomputable def seriesArg (k : ℤ) (θ : ℝ) : ℝ := (θ - 2 ^ k) / (θ + 2 ^ k)

/-- The approximation `k ln 2 + 2 (x + x³/3 + ⋯)` of `log θ`, with `n` terms of the series at
`x = seriesArg k θ`, and with the midpoint of the two bounds in place of `ln 2`. -/
noncomputable def logApprox (k : ℤ) (n : ℕ) (θ : ℝ) : ℝ :=
  k * ((logTwoLo + logTwoHi) / 2)
    + 2 * ∑ i ∈ Finset.range n, seriesArg k θ ^ (2 * i + 1) / (2 * i + 1)

/-- A bound on the error of `logApprox`: `|k|` times half the distance of the two bounds on `ln 2`,
and the remainder of the series. -/
noncomputable def logErr (k : ℤ) (n : ℕ) (θ : ℝ) : ℝ :=
  |(k : ℝ)| * ((logTwoHi - logTwoLo) / 2) + 2 * (seriesArg k θ ^ (2 * n) / (1 - seriesArg k θ ^ 2))

/-- Proves an equation or inequality between explicit rational numbers by evaluating both sides,
after unfolding the approximations of logarithms. -/
macro "numerics" : tactic =>
  `(tactic| norm_num [logApprox, logErr, seriesArg, logTwoLo, logTwoHi, logThreeLo, logThreeHi,
    logTenLo, logTenHi, Finset.sum_range_succ, rhoC])

private lemma log_two_mem : Real.log 2 ∈ Set.Icc logTwoLo logTwoHi :=
  ⟨Real.log_two_gt_d9.le, Real.log_two_lt_d9.le⟩

/-- The enclosure of `log θ`, between two rational numbers if `θ` is rational. It holds for every
`k` and `n`; they decide only how tight it is. -/
theorem log_mem (k : ℤ) (n : ℕ) {θ : ℝ} (hθ : 0 < θ := by numerics) :
    Real.log θ ∈ Set.Icc (logApprox k n θ - logErr k n θ) (logApprox k n θ + logErr k n θ) := by
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hx : |seriesArg k θ| < 1 := by
    rw [seriesArg, abs_div, abs_of_pos (add_pos hθ hpow), div_lt_one (add_pos hθ hpow), abs_lt]
    constructor <;> linarith
  have hsq : 0 < 1 - seriesArg k θ ^ 2 := sub_pos.2 ((sq_lt_one_iff_abs_lt_one _).2 hx)
  -- `log θ = k log 2 + log ((1 + x)/(1 - x))`
  have hlog : Real.log θ
      = k * Real.log 2 + Real.log ((1 + seriesArg k θ) / (1 - seriesArg k θ)) := by
    have hdiv : (1 + seriesArg k θ) / (1 - seriesArg k θ) = θ / 2 ^ k := by
      rw [seriesArg]
      field_simp
      ring
    rw [hdiv, Real.log_div hθ.ne' hpow.ne', Real.log_zpow]
    ring
  have htwo : |k * Real.log 2 - k * ((logTwoLo + logTwoHi) / 2)|
      ≤ |(k : ℝ)| * ((logTwoHi - logTwoLo) / 2) := by
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left (abs_le.2 ⟨?_, ?_⟩) (abs_nonneg _) <;>
      linarith [log_two_mem.1, log_two_mem.2]
  -- Mathlib: the sum of `n` terms differs from `½ log ((1 + x)/(1 - x))` by at most
  -- `|x|^(2n+1)/(1 - x²)`. We use `|x|^(2n+1) ≤ x^(2n)`, which is free of absolute values.
  have hseries := (Real.sum_range_sub_log_div_le hx n).trans
    (div_le_div_of_nonneg_right (pow_le_pow_of_le_one (abs_nonneg _) hx.le (Nat.le_succ _)) hsq.le)
  rw [(even_two_mul n).pow_abs] at hseries
  rw [abs_le] at htwo hseries
  rw [hlog, logApprox, logErr]
  constructor <;> linarith [htwo.1, htwo.2, hseries.1, hseries.2]

private lemma log_three_mem : Real.log 3 ∈ Set.Icc logThreeLo logThreeHi :=
  ⟨le_trans (by numerics) (log_mem 2 7).1, (log_mem 2 7).2.trans (by numerics)⟩

private lemma log_ten_mem : Real.log 10 ∈ Set.Icc logTenLo logTenHi :=
  ⟨le_trans (by numerics) (log_mem 3 6).1, (log_mem 3 6).2.trans (by numerics)⟩

/-! ## The exponent `q` of the query time (Corollary 31) -/

/-- `q(θ)` written out in terms of `log 2` and `log 3`. -/
private lemma qOf_eq_div (θ : ℝ) :
    qOf θ = (-θ * Real.log θ - (1 - θ) * Real.log (1 - θ) + θ * (2 * Real.log 3))
      / (2 * Real.log 2) := by
  unfold qOf entropy
  rw [Real.log_four, Real.log_nine]

/-- An upper bound on `q(θ)` at a rational `θ`. The hypothesis `h` is `H(θ) + θ ln 9 ≤ r ln 4` with
every logarithm replaced by the bound that makes the inequality harder. Here `2^k` is the power of
two nearest to `θ`; four terms of the series for `log θ` and for `log (1 - θ)` are enough for every
entry of Table 2. -/
theorem qOf_le (k : ℤ) {θ r : ℝ} (h0 : 0 < θ := by numerics) (h1 : θ < 1 := by numerics)
    (hr : 0 ≤ r := by numerics)
    (h : -θ * (logApprox k 4 θ - logErr k 4 θ)
        - (1 - θ) * (logApprox 0 4 (1 - θ) - logErr 0 4 (1 - θ)) + θ * (2 * logThreeHi)
      ≤ r * (2 * logTwoLo) := by numerics) : qOf θ ≤ r := by
  have hcompl : 0 < 1 - θ := sub_pos.2 h1
  rw [qOf_eq_div, div_le_iff₀ (mul_pos two_pos (Real.log_pos one_lt_two))]
  have hlog := mul_le_mul_of_nonneg_left (log_mem k 4 h0).1 h0.le
  have hlogc := mul_le_mul_of_nonneg_left (log_mem 0 4 hcompl).1 hcompl.le
  have hthree := mul_le_mul_of_nonneg_left log_three_mem.2 h0.le
  have htwo := mul_le_mul_of_nonneg_left log_two_mem.1 hr
  linarith [h, hlog, hlogc, hthree, htwo]

/-- A lower bound on `q(θ)` at a rational `θ`, computed as in `qOf_le`. -/
theorem le_qOf (k : ℤ) {θ r : ℝ} (h0 : 0 < θ := by numerics) (h1 : θ < 1 := by numerics)
    (hr : 0 ≤ r := by numerics)
    (h : r * (2 * logTwoHi)
      ≤ -θ * (logApprox k 4 θ + logErr k 4 θ)
        - (1 - θ) * (logApprox 0 4 (1 - θ) + logErr 0 4 (1 - θ)) + θ * (2 * logThreeLo) := by
      numerics) : r ≤ qOf θ := by
  have hcompl : 0 < 1 - θ := sub_pos.2 h1
  rw [qOf_eq_div, le_div_iff₀ (mul_pos two_pos (Real.log_pos one_lt_two))]
  have hlog := mul_le_mul_of_nonneg_left (log_mem k 4 h0).2 h0.le
  have hlogc := mul_le_mul_of_nonneg_left (log_mem 0 4 hcompl).2 hcompl.le
  have hthree := mul_le_mul_of_nonneg_left log_three_mem.1 h0.le
  have htwo := mul_le_mul_of_nonneg_left log_two_mem.2 hr
  linarith [h, hlog, hlogc, hthree, htwo]

/-! ## The exponent `γ` (Corollary 31) -/

/-- Bounds on `γ` at `θ = 1`, that is on `ln(1/ρ_c)/ln 4`, from bounds on `ln(1/ρ_c)`. -/
theorem gammaOf_one_mem {c a b glo ghi : ℝ} (h : Real.log (1 / rhoC c) ∈ Set.Icc a b)
    (hglo : 0 ≤ glo := by numerics) (hghi : 0 ≤ ghi := by numerics)
    (hlo : glo * (2 * logTwoHi) ≤ a := by numerics)
    (hhi : b ≤ ghi * (2 * logTwoLo) := by numerics) : gammaOf c 1 ∈ Set.Icc glo ghi := by
  have hpos : 0 < 2 * Real.log 2 := mul_pos two_pos (Real.log_pos one_lt_two)
  have htwolo := mul_le_mul_of_nonneg_left log_two_mem.2 hglo
  have htwohi := mul_le_mul_of_nonneg_left log_two_mem.1 hghi
  rw [Set.mem_Icc, gammaOf, Real.log_four, one_mul, le_div_iff₀ hpos, div_le_iff₀ hpos]
  exact ⟨by linarith [hlo, htwolo, h.1], by linarith [hhi, htwohi, h.2]⟩

/-- `γ` at a `θ` between `θlo` and `θhi`, from bounds on `γ` at `θ = 1`. -/
theorem gammaOf_mem {c θ θlo θhi glo ghi : ℝ} (hg : gammaOf c 1 ∈ Set.Icc glo ghi)
    (hglo : 0 ≤ glo) (h0 : 0 ≤ θlo) (hθ : θ ∈ Set.Icc θlo θhi) :
    gammaOf c θ ∈ Set.Icc (θlo * glo) (θhi * ghi) := by
  rw [gammaOf_eq_mul]
  exact ⟨mul_le_mul hθ.1 hg.1 hglo (h0.trans hθ.1),
    mul_le_mul hθ.2 hg.2 (hglo.trans hg.1) ((h0.trans hθ.1).trans hθ.2)⟩

/-! ## The bound `R_c(γ)` (equation (11)) -/

/-- Bounds on the denominator of (11) at `γ = 0` from bounds on `log (1/c)` and `log (1 - 1/c)`. -/
theorem lnΛ_zero_mem {c alo ahi blo bhi Blo Bhi : ℝ} (ha : Real.log (1 / c) ∈ Set.Icc alo ahi)
    (hb : Real.log (1 - 1 / c) ∈ Set.Icc blo bhi) (hc : 1 ≤ c := by numerics)
    (hlo : Blo ≤ c * logTenLo + 1 / 2 * alo + 1 / 2 * (c - 1) * blo - (c - 1) * logThreeHi := by
      numerics)
    (hhi : c * logTenHi + 1 / 2 * ahi + 1 / 2 * (c - 1) * bhi - (c - 1) * logThreeLo ≤ Bhi := by
      numerics) : lnΛ c 0 ∈ Set.Icc Blo Bhi := by
  have hc0 : 0 ≤ c := by linarith
  have hc1 : 0 ≤ c - 1 := by linarith
  have heq : lnΛ c 0 = c * Real.log 10 + 1 / 2 * Real.log (1 / c)
      + 1 / 2 * (c - 1) * Real.log (1 - 1 / c) - (c - 1) * Real.log 3 := by
    have : c ≠ 0 := by positivity
    unfold lnΛ entropy
    field_simp
    ring
  rw [heq]
  constructor
  · linarith [hlo, ha.1, mul_le_mul_of_nonneg_left log_ten_mem.1 hc0,
      mul_le_mul_of_nonneg_left hb.1 hc1, mul_le_mul_of_nonneg_left log_three_mem.2 hc1]
  · linarith [hhi, ha.2, mul_le_mul_of_nonneg_left log_ten_mem.2 hc0,
      mul_le_mul_of_nonneg_left hb.2 hc1, mul_le_mul_of_nonneg_left log_three_mem.1 hc1]

/-- `ε < R_c(γ)` for all `0 ≤ γ ≤ Γ`, from an upper bound on the denominator of (11) at `γ = 0`. -/
theorem lt_Rc_of_lnΛ_zero_mem {c ε Γ Blo Bhi : ℝ} (hB : lnΛ c 0 ∈ Set.Icc Blo Bhi)
    (hBlo : 0 < Blo := by numerics) (hε : 0 ≤ ε := by numerics)
    (h : ε * (Bhi + Γ * (2 * logTwoHi)) < 2 * logTwoLo := by numerics) :
    ∀ γ : ℝ, 0 ≤ γ → γ ≤ Γ → ε < Rc c γ := by
  intro γ hγ0 hγ
  have htwo := log_two_mem
  have hpos : 0 ≤ 2 * Real.log 2 := (mul_pos two_pos (Real.log_pos one_lt_two)).le
  have hγ' : γ * (2 * Real.log 2) ≤ Γ * (2 * logTwoHi) :=
    mul_le_mul hγ (by linarith [htwo.2]) hpos (hγ0.trans hγ)
  rw [Rc, lnΛ_eq_add, Real.log_four,
    lt_div_iff₀ (by linarith [hBlo, hB.1, mul_nonneg hγ0 hpos])]
  calc ε * (lnΛ c 0 + γ * (2 * Real.log 2)) ≤ ε * (Bhi + Γ * (2 * logTwoHi)) :=
        mul_le_mul_of_nonneg_left (by linarith [hB.2, hγ']) hε
    _ < 2 * logTwoLo := h
    _ ≤ 2 * Real.log 2 := by linarith [htwo.1]

/-- `R_c(γ) < r` for all `γ ≥ γlo ≥ 0`, from a lower bound on the denominator of (11) at `γ = 0`. -/
theorem Rc_lt_of_lnΛ_zero_mem {c r γlo Blo Bhi : ℝ} (hB : lnΛ c 0 ∈ Set.Icc Blo Bhi)
    (hBlo : 0 < Blo := by numerics) (hr : 0 ≤ r := by numerics) (hγlo : 0 ≤ γlo := by numerics)
    (h : 2 * logTwoHi < r * (Blo + γlo * (2 * logTwoLo)) := by numerics) :
    ∀ γ : ℝ, γlo ≤ γ → Rc c γ < r := by
  intro γ hγ
  have htwo := log_two_mem
  have hpos : (0 : ℝ) ≤ 2 * logTwoLo := by numerics
  have hγ' : γlo * (2 * logTwoLo) ≤ γ * (2 * Real.log 2) :=
    mul_le_mul hγ (by linarith [htwo.1]) hpos (hγlo.trans hγ)
  rw [Rc, lnΛ_eq_add, Real.log_four,
    div_lt_iff₀ (by linarith [hBlo, hB.1, hγ', mul_nonneg hγlo hpos])]
  calc 2 * Real.log 2 ≤ 2 * logTwoHi := by linarith [htwo.2]
    _ < r * (Blo + γlo * (2 * logTwoLo)) := h
    _ ≤ r * (lnΛ c 0 + γ * (2 * Real.log 2)) :=
        mul_le_mul_of_nonneg_left (by linarith [hB.1, hγ']) hr

/-! ## Entries of Table 2

An entry needs two facts on its row, `hg` (an enclosure of `ln(1/ρ_c)/ln 4`) and `hR` (the `ε` of
the row is below `R_c(γ)` up to the largest `γ` of the row), and two rational numbers `θlo ≤ θhi`
that enclose its `θ`. -/

/-- What all entries have in common: if `θ` lies between `θlo` and `θhi` then the printed `γ₀` is
`γ` rounded down to four decimals, and `ε < R_c(γ)`. -/
private lemma entry_of_mem {c ε γ₀ θ θlo θhi glo ghi Γ : ℝ} (hg : gammaOf c 1 ∈ Set.Icc glo ghi)
    (hR : ∀ γ : ℝ, 0 ≤ γ → γ ≤ Γ → ε < Rc c γ) (hθ : θ ∈ Set.Icc θlo θhi) (hglo : 0 ≤ glo)
    (h0 : 0 ≤ θlo) (hdown : γ₀ ≤ θlo * glo) (hup : θhi * ghi < γ₀ + 0.0001)
    (hΓ : γ₀ + 0.0001 ≤ Γ) :
    γ₀ ≤ gammaOf c θ ∧ gammaOf c θ < γ₀ + 0.0001 ∧ ε < Rc c (gammaOf c θ) := by
  obtain ⟨hlow, hupp⟩ := gammaOf_mem hg hglo h0 hθ
  exact ⟨hdown.trans hlow, hupp.trans_lt hup,
    hR _ ((mul_nonneg h0 hglo).trans hlow) ((hupp.trans hup.le).trans hΓ)⟩

/-- If `q(θlo) ≤ q ≤ q(θhi)` then `q(θ) = q` for some `θ` between `θlo` and `θhi`. -/
theorem exists_qOf_eq {q θlo θhi : ℝ} (hlo : qOf θlo ≤ q) (hhi : q ≤ qOf θhi)
    (hle : θlo ≤ θhi := by numerics) : ∃ θ ∈ Set.Icc θlo θhi, qOf θ = q :=
  intermediate_value_Icc hle continuous_qOf.continuousOn ⟨hlo, hhi⟩

/-- An entry of the left half of Table 2, from an enclosure of the `θ` of its column. -/
theorem Table2Query.intro {c ε q γ₀ θlo θhi glo ghi Γ : ℝ}
    (hθ : ∃ θ ∈ Set.Icc θlo θhi, qOf θ = q) (hg : gammaOf c 1 ∈ Set.Icc glo ghi)
    (hR : ∀ γ : ℝ, 0 ≤ γ → γ ≤ Γ → ε < Rc c γ)
    (hc : 10 < c := by numerics) (hglo : 0 ≤ glo := by numerics) (h0 : 0 < θlo := by numerics)
    (h9 : θhi < 0.9 := by numerics) (hdown : γ₀ ≤ θlo * glo := by numerics)
    (hup : θhi * ghi < γ₀ + 0.0001 := by numerics) (hΓ : γ₀ + 0.0001 ≤ Γ := by numerics) :
    Table2Query c ε q γ₀ := by
  obtain ⟨θ, hθ, hq⟩ := hθ
  exact ⟨hc, θ, h0.trans_le hθ.1, hθ.2.trans_lt h9, hq,
    entry_of_mem hg hR hθ hglo h0.le hdown hup hΓ⟩

/-- An entry of the column `q = 0.43` of Table 2, which uses `θ = 1/9`. -/
theorem Table2Ninth.intro {c ε γ₀ glo ghi Γ : ℝ} (hg : gammaOf c 1 ∈ Set.Icc glo ghi)
    (hR : ∀ γ : ℝ, 0 ≤ γ → γ ≤ Γ → ε < Rc c γ)
    (hc : 10 < c := by numerics) (hglo : 0 ≤ glo := by numerics)
    (hdown : γ₀ ≤ 1 / 9 * glo := by numerics) (hup : 1 / 9 * ghi < γ₀ + 0.0001 := by numerics)
    (hΓ : γ₀ + 0.0001 ≤ Γ := by numerics) : Table2Ninth c ε γ₀ :=
  ⟨hc, entry_of_mem hg hR ⟨le_rfl, le_rfl⟩ hglo (by norm_num) hdown hup hΓ⟩

/-- An entry of the right half of Table 2: `γ + q` is at most `κ` at `θlo` (`hqlo`) and at least `κ`
at `θhi` (`hqhi`), so it equals `κ` in between. -/
theorem Table2Density.intro {c ε κ γ₀ glo ghi Γ : ℝ} (hg : gammaOf c 1 ∈ Set.Icc glo ghi)
    (hR : ∀ γ : ℝ, 0 ≤ γ → γ ≤ Γ → ε < Rc c γ)
    (θlo θhi : ℝ) (hqlo : qOf θlo ≤ κ - θlo * ghi) (hqhi : κ - θhi * glo ≤ qOf θhi)
    (hc : 10 < c := by numerics) (hκ : 0 < κ := by numerics) (hglo : 0 ≤ glo := by numerics)
    (h0 : 0 < θlo := by numerics) (hle : θlo ≤ θhi := by numerics) (h9 : θhi < 0.9 := by numerics)
    (hdown : γ₀ ≤ θlo * glo := by numerics) (hup : θhi * ghi < γ₀ + 0.0001 := by numerics)
    (hΓ : γ₀ + 0.0001 ≤ Γ := by numerics) : Table2Density c ε κ γ₀ := by
  have hbelow := (gammaOf_mem hg hglo h0.le ⟨le_rfl, le_rfl⟩).2
  have habove := (gammaOf_mem hg hglo (h0.le.trans hle) ⟨le_rfl, le_rfl⟩).1
  obtain ⟨θ, hθ, hκθ⟩ := intermediate_value_Icc hle (continuous_gammaOf_add_qOf c).continuousOn
    (show κ ∈ Set.Icc (gammaOf c θlo + qOf θlo) (gammaOf c θhi + qOf θhi) from
      ⟨by linarith [hbelow, hqlo], by linarith [habove, hqhi]⟩)
  exact ⟨hc, hκ, θ, h0.trans_le hθ.1, hθ.2.trans_lt h9, eq_sub_of_add_eq hκθ,
    entry_of_mem hg hR hθ hglo h0.le hdown hup hΓ⟩

/-- At the `θ` of a column of the left half, `R_c(γ) < r`. With `r = ε + 0.001` this shows that the
`ε` of a row is the smallest `R_c(γ)` of the row rounded down to three decimals (Section 4.4). -/
theorem exists_Rc_lt {c r q θlo θhi glo ghi Blo Bhi : ℝ} (hθ : ∃ θ ∈ Set.Icc θlo θhi, qOf θ = q)
    (hg : gammaOf c 1 ∈ Set.Icc glo ghi) (hB : lnΛ c 0 ∈ Set.Icc Blo Bhi)
    (hglo : 0 ≤ glo := by numerics) (h0 : 0 < θlo := by numerics) (h9 : θhi < 0.9 := by numerics)
    (hBlo : 0 < Blo := by numerics) (hr : 0 ≤ r := by numerics)
    (h : 2 * logTwoHi < r * (Blo + θlo * glo * (2 * logTwoLo)) := by numerics) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 0.9 ∧ qOf θ = q ∧ Rc c (gammaOf c θ) < r := by
  obtain ⟨θ, hθ, hq⟩ := hθ
  exact ⟨θ, h0.trans_le hθ.1, hθ.2.trans_lt h9, hq,
    Rc_lt_of_lnΛ_zero_mem hB hBlo hr (mul_nonneg h0.le hglo) h _ (gammaOf_mem hg hglo h0.le hθ).1⟩

end ThreeSumApsp
