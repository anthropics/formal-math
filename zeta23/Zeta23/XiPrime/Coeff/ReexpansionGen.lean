/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Coeff/ReexpansionGen.lean — the δ-re-expansion of C(N; L + δ) about a GENERAL base L = Lb(T) with
Re Lb(T) = l(T)/2, and the (H1)–(H3)-type bounds for its coefficients  [XF′ §6; §9.3(ii)]
(the generic API; Coeff/ReexpansionW.lean and Coeff/Reexpansion.lean are its instances).

  eGen Lb T r N := Σ_{j<Ω N} (−1)^r C(r+j, j) Lb(T)^{−(j+1+r)} [(Λ·log)∗Λ^{∗j}](N)
  eGen_expand : C(N; Lb T + δ) − C(N; Lb T) = Σ_{r≥1} eGen Lb T r N · δ^r     (l(T) ≥ 2, 0 ≤ δ ≤ 1/2)
  eGen_H1/H2/H3 : the Reexpansion-shaped bounds with ρ₀ = 4, A = CF, threshold T0re (l ≥ 128eK + 2).
Instances: Coeff/Reexpansion.lean (ξ′: Lb = LT = l/2 + iπ/4), Coeff/ReexpansionW.lean (Z′: Lb = l/2 real).
Every step uses only Re Lb = l/2 (⇒ ‖Lb‖ ≥ l/2, Lb ≠ 0, Lb + δ ≠ 0).
-/
import Zeta23.XiPrime.Coeff.Upper
import Mathlib.Analysis.SpecificLimits.Normed

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Omega
open Finset Real

noncomputable section

namespace Zeta23
namespace XiPrime

/-! ### shared elementary helpers -/

lemma choose_le_two_pow (n k : ℕ) : n.choose k ≤ 2 ^ n := by
  by_cases hk : k ≤ n
  · rw [← Nat.sum_range_choose n]
    exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  · rw [Nat.choose_eq_zero_of_lt (not_le.mp hk)]; exact Nat.zero_le _


/-- the height threshold: l(T) ≥ 128eK + 2. -/
def T0re : ℝ := 2 * Real.pi * Real.exp (128 * Real.exp 1 * KM + 2)

lemma l_ge_of_T0re_le {T : ℝ} (hT : T0re ≤ T) : 128 * Real.exp 1 * KM + 2 ≤ l T := by
  unfold T0re at hT
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hT
  unfold l
  rw [Real.le_log_iff_exp_le (div_pos hTpos h2pi), le_div_iff₀ h2pi]
  linarith


section generic
variable (Lb : ℝ → ℂ)

/-! ### elementary facts about a base with Re Lb(T) = l(T)/2 -/

lemma norm_base_ge {Lb : ℝ → ℂ} (hre : ∀ T, (Lb T).re = l T / 2) (T : ℝ) : l T / 2 ≤ ‖Lb T‖ := by
  calc l T / 2 ≤ |(Lb T).re| := by rw [hre]; exact le_abs_self _
    _ ≤ ‖Lb T‖ := Complex.abs_re_le_norm _

lemma base_ne_zero {Lb : ℝ → ℂ} (hre : ∀ T, (Lb T).re = l T / 2) {T : ℝ} (hl : 0 < l T) : Lb T ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [hre, Complex.zero_re] at this
  linarith

lemma base_add_ne_zero {Lb : ℝ → ℂ} (hre : ∀ T, (Lb T).re = l T / 2) {T δ : ℝ} (hl : 0 < l T) (hδ : 0 ≤ δ) :
    Lb T + (δ : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [Complex.add_re, hre, Complex.ofReal_re, Complex.zero_re] at this
  linarith

/-- e_r(N) := Σ_{j<Ω N} (−1)^r · C(r+j, j) · L^{−(j+1+r)} · [(Λ·log)∗Λ^{∗j}](N), about the base L = Lb T. -/
def eGen (T : ℝ) (r N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (Ω N),
    (-1 : ℂ) ^ r * ((r + j).choose j : ℂ) * ((Lb T)⁻¹) ^ (j + 1 + r) * ((lamLogConv j N : ℝ) : ℂ)

/-! ### e_r(1) = 0 -/

theorem eGen_one (T : ℝ) (r : ℕ) : eGen Lb T r 1 = 0 := by
  simp [eGen]

/-! ### the expansion identity -/

/-- the n-th Taylor block: g_n := Σ_j L^{−(j+1)} conv_j · C(n+j,j)(−δ/L)ⁿ = e_n(N)·δⁿ. -/
lemma eGen_block_eq (T δ : ℝ) (N n : ℕ) :
    ∑ j ∈ Finset.range (Ω N), ((Lb T)⁻¹) ^ (j + 1) * ((lamLogConv j N : ℝ) : ℂ)
        * ((((n + j).choose j : ℕ) : ℂ) * (-(δ : ℂ) / Lb T) ^ n)
      = eGen Lb T n N * (δ : ℂ) ^ n := by
  unfold eGen
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hr : (-(δ : ℂ) / Lb T) ^ n = (-1) ^ n * (δ : ℂ) ^ n * ((Lb T)⁻¹) ^ n := by
    rw [show (-(δ : ℂ) / Lb T) = (-1) * ((δ : ℂ) * (Lb T)⁻¹) by ring, mul_pow, mul_pow, mul_assoc]
  rw [hr]
  ring

/-- **the δ-expansion**: for l(T) ≥ 2 and 0 ≤ δ ≤ 1/2,
C(N; L_T + δ) − C(N; L_T) = Σ_{r≥1} e_r(N) δ^r. -/
theorem eGen_expand (hre : ∀ T, (Lb T).re = l T / 2) {T : ℝ} (hl : 2 ≤ l T) {δ : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (1 / 2)) (N : ℕ) :
    HasSum (fun r : ℕ => eGen Lb T (r + 1) N * (δ : ℂ) ^ (r + 1))
      (xiCoeff (Lb T + δ) N - xiCoeff (Lb T) N) := by
  set L := Lb T with hLdef
  have hl0 : 0 < l T := by linarith
  have hL0 : L ≠ 0 := base_ne_zero hre hl0
  have hLδ : L + (δ : ℂ) ≠ 0 := base_add_ne_zero hre hl0 hδ.1
  have hnormL : 1 ≤ ‖L‖ := le_trans (by linarith) (norm_base_ge hre T)
  -- the ratio
  set q : ℂ := -(δ : ℂ) / L with hq
  have hqn : ‖q‖ < 1 := by
    rw [hq, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ.1]
    rw [div_lt_one (by linarith)]
    linarith [hδ.2]
  have h1q : (1 : ℂ) - q = (L + δ) / L := by rw [hq]; field_simp; ring
  -- per-j geometric/binomial series
  have hj : ∀ j ∈ Finset.range (Ω N),
      HasSum (fun n : ℕ => (L⁻¹) ^ (j + 1) * ((lamLogConv j N : ℝ) : ℂ)
          * ((((n + j).choose j : ℕ) : ℂ) * q ^ n))
        (((L + δ)⁻¹) ^ (j + 1) * ((lamLogConv j N : ℝ) : ℂ)) := by
    intro j _
    have h := (hasSum_choose_mul_geometric_of_norm_lt_one j hqn).mul_left
      ((L⁻¹) ^ (j + 1) * ((lamLogConv j N : ℝ) : ℂ))
    have hv : (L⁻¹) ^ (j + 1) * ((lamLogConv j N : ℝ) : ℂ) * (1 / (1 - q) ^ (j + 1))
        = ((L + δ)⁻¹) ^ (j + 1) * ((lamLogConv j N : ℝ) : ℂ) := by
      rw [h1q, div_pow, one_div, inv_div, inv_pow, inv_pow]
      field_simp
    rw [hv] at h
    exact h
  have hsum := hasSum_sum hj
  -- value of the full series: Σ_j (L+δ)^{-(j+1)} conv_j = C(N;L+δ) + Λ(N)
  have hval : ∑ j ∈ Finset.range (Ω N), ((L + δ)⁻¹) ^ (j + 1) * ((lamLogConv j N : ℝ) : ℂ)
      = xiCoeff (L + δ) N + ((Λ N : ℝ) : ℂ) := by
    unfold xiCoeff; ring
  -- drop the n = 0 block (= C(N;L) + Λ(N))
  have hshift := (hasSum_nat_add_iff' 1).mpr hsum
  simp only [Finset.sum_range_one] at hshift
  have h0 : ∑ j ∈ Finset.range (Ω N), (L⁻¹) ^ (j + 1) * ((lamLogConv j N : ℝ) : ℂ)
        * ((((0 + j).choose j : ℕ) : ℂ) * q ^ 0)
      = xiCoeff L N + ((Λ N : ℝ) : ℂ) := by
    unfold xiCoeff
    simp only [zero_add, Nat.choose_self, Nat.cast_one, pow_zero, mul_one]
    ring
  rw [hval, h0] at hshift
  have hfun : (fun n : ℕ => ∑ j ∈ Finset.range (Ω N), (L⁻¹) ^ (j + 1) * ((lamLogConv j N : ℝ) : ℂ)
        * ((((n + 1 + j).choose j : ℕ) : ℂ) * q ^ (n + 1)))
      = fun r : ℕ => eGen Lb T (r + 1) N * (δ : ℂ) ^ (r + 1) := by
    funext n
    rw [← eGen_block_eq Lb T δ N (n + 1)]
  rw [hfun] at hshift
  convert hshift using 1
  all_goals first | ring | rfl

/-! ### the pointwise majorant ‖e_r(N)‖ ≤ (2/‖L‖)^r · log N · F_{2/‖L‖}(N) -/

theorem norm_eGen_le (T : ℝ) (r N : ℕ) :
    ‖eGen Lb T r N‖ ≤ (2 / ‖Lb T‖) ^ r * (Real.log N * Fmaj (2 / ‖Lb T‖) N) := by
  unfold eGen Fmaj
  rw [Finset.mul_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hconv0 : 0 ≤ lamLogConv j N := lamLogConv_nonneg j N
  have hconv : lamLogConv j N ≤ Real.log N * (Λ ^ (j + 1)) N := lamLogConv_le j N
  have hL0 : 0 ≤ ‖Lb T‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast,
    norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hconv0]
  have hch : (((r + j).choose j : ℕ) : ℝ) ≤ 2 ^ (r + j) := by exact_mod_cast choose_le_two_pow (r + j) j
  have hlam0 : 0 ≤ Real.log N * (Λ ^ (j + 1)) N :=
    mul_nonneg (Real.log_natCast_nonneg N) (lamPow_nonneg _ _)
  calc (((r + j).choose j : ℕ) : ℝ) * ‖Lb T‖⁻¹ ^ (j + 1 + r) * lamLogConv j N
      ≤ 2 ^ (r + j) * ‖Lb T‖⁻¹ ^ (j + 1 + r) * (Real.log N * (Λ ^ (j + 1)) N) := by
        gcongr
    _ ≤ 2 * (2 ^ (r + j) * ‖Lb T‖⁻¹ ^ (j + 1 + r) * (Real.log N * (Λ ^ (j + 1)) N)) := by
        have : 0 ≤ 2 ^ (r + j) * ‖Lb T‖⁻¹ ^ (j + 1 + r) * (Real.log N * (Λ ^ (j + 1)) N) := by positivity
        linarith
    _ = (2 / ‖Lb T‖) ^ r * (Real.log N * ((2 / ‖Lb T‖) ^ (j + 1) * (Λ ^ (j + 1)) N)) := by
        rw [div_eq_mul_inv]; ring

/-! ### the core sum bound -/

/-- **core**: Σ_{N≤x} ‖e_r(N)‖²/N ≤ CF·(4/l)^{2r}·log²x for 2 ≤ x ≤ e^{l}, T ≥ T0re. -/
theorem sum_norm_eGen_sq_div_le (hre : ∀ T, (Lb T).re = l T / 2) {T : ℝ} (hT : T0re ≤ T) (r : ℕ) {x : ℝ} (hx2 : 2 ≤ x)
    (hxl : x ≤ Real.exp (l T)) :
    ∑ N ∈ Ioc 0 ⌊x⌋₊, ‖eGen Lb T r N‖ ^ 2 / N ≤ CF * (4 / l T) ^ (2 * r) * Real.log x ^ 2 := by
  have hl := l_ge_of_T0re_le hT
  have hKe : 0 ≤ 128 * Real.exp 1 * KM := mul_nonneg (by positivity) KM_nonneg
  have hl2 : 2 ≤ l T := by linarith
  have hl0 : 0 < l T := by linarith
  have hnorm : l T / 2 ≤ ‖Lb T‖ := norm_base_ge hre T
  have hLpos : 0 < ‖Lb T‖ := lt_of_lt_of_le (by linarith) hnorm
  set x' := 2 / ‖Lb T‖ with hx'
  have hx'0 : 0 ≤ x' := by positivity
  have hx'le : x' ≤ 4 / l T := by
    rw [hx', div_le_div_iff₀ hLpos hl0]; linarith
  have hxpos : 0 < x := by linarith
  set u := Real.log x with hudef
  have hu0 : 0 ≤ u := Real.log_nonneg (by linarith)
  have hul : u ≤ l T := (Real.log_le_iff_le_exp hxpos).mpr hxl
  have hxexp : ⌊x⌋₊ = ⌊Real.exp u⌋₊ := by rw [hudef, Real.exp_log hxpos]
  -- hypotheses of the Upper machinery at x'
  have hxu : x' * u ≤ 4 := by
    calc x' * u ≤ (4 / l T) * l T := mul_le_mul hx'le hul hu0 (by positivity)
      _ = 4 := by field_simp
  have hxK : 32 * Real.exp 1 * KM * x' ≤ 1 := by
    calc 32 * Real.exp 1 * KM * x' ≤ 32 * Real.exp 1 * KM * (4 / l T) :=
          mul_le_mul_of_nonneg_left hx'le (mul_nonneg (by positivity) KM_nonneg)
      _ = (128 * Real.exp 1 * KM) / l T := by ring
      _ ≤ 1 := by rw [div_le_one hl0]; linarith
  have hF := sum_Fmaj_sq_div_le hx'0 hu0 hxu hxK
  rw [← hxexp] at hF
  -- pointwise
  have hpt : ∀ N ∈ Ioc 0 ⌊x⌋₊, ‖eGen Lb T r N‖ ^ 2 / N ≤ x' ^ (2 * r) * u ^ 2 * (Fmaj x' N ^ 2 / N) := by
    intro N hN
    have hN0 : (0:ℝ) < N := by exact_mod_cast (mem_Ioc.mp hN).1
    have hlogN : Real.log N ≤ u := by
      rw [hxexp] at hN; exact log_le_of_mem_Ioc_floor_exp hN
    have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have hFm0 : 0 ≤ Fmaj x' N := Fmaj_nonneg hx'0 N
    have he := norm_eGen_le Lb T r N
    have he0 : 0 ≤ ‖eGen Lb T r N‖ := norm_nonneg _
    have hsq : ‖eGen Lb T r N‖ ^ 2 ≤ (x' ^ r * (u * Fmaj x' N)) ^ 2 := by
      apply pow_le_pow_left₀ he0
      refine he.trans ?_
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlogN hFm0) (pow_nonneg hx'0 _)
    calc ‖eGen Lb T r N‖ ^ 2 / N ≤ (x' ^ r * (u * Fmaj x' N)) ^ 2 / N :=
          div_le_div_of_nonneg_right hsq hN0.le
      _ = x' ^ (2 * r) * u ^ 2 * (Fmaj x' N ^ 2 / N) := by rw [pow_mul]; ring
  calc ∑ N ∈ Ioc 0 ⌊x⌋₊, ‖eGen Lb T r N‖ ^ 2 / N
      ≤ ∑ N ∈ Ioc 0 ⌊x⌋₊, x' ^ (2 * r) * u ^ 2 * (Fmaj x' N ^ 2 / N) := Finset.sum_le_sum hpt
    _ = x' ^ (2 * r) * u ^ 2 * ∑ N ∈ Ioc 0 ⌊x⌋₊, Fmaj x' N ^ 2 / N := by rw [Finset.mul_sum]
    _ ≤ (4 / l T) ^ (2 * r) * u ^ 2 * CF := by gcongr
    _ = CF * (4 / l T) ^ (2 * r) * u ^ 2 := by ring

/-! ### (H3), (H2), (H1) -/

theorem eGen_H3 (hre : ∀ T, (Lb T).re = l T / 2) {T : ℝ} (hT : T0re ≤ T) (r : ℕ) {x : ℝ} (hx2 : 2 ≤ x) (hxl : x ≤ Real.exp (l T)) :
    ∑ N ∈ Ioc 0 ⌊x⌋₊, ‖eGen Lb T r N‖ ^ 2 / N ≤ CF * (4 / l T) ^ (2 * r) * l T ^ 2 * (1 + Real.log x) := by
  have h := sum_norm_eGen_sq_div_le Lb hre hT r hx2 hxl
  have hl := l_ge_of_T0re_le hT
  have hKe : 0 ≤ 128 * Real.exp 1 * KM := mul_nonneg (by positivity) KM_nonneg
  have hxpos : 0 < x := by linarith
  have hu0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hul : Real.log x ≤ l T := (Real.log_le_iff_le_exp hxpos).mpr hxl
  have hA : 0 ≤ CF * (4 / l T) ^ (2 * r) := by
    have : 0 ≤ 4 / l T := by apply div_nonneg (by norm_num); linarith
    exact mul_nonneg CF_pos.le (pow_nonneg this _)
  calc ∑ N ∈ Ioc 0 ⌊x⌋₊, ‖eGen Lb T r N‖ ^ 2 / N ≤ CF * (4 / l T) ^ (2 * r) * Real.log x ^ 2 := h
    _ ≤ CF * (4 / l T) ^ (2 * r) * (l T ^ 2 * (1 + Real.log x)) := by
        apply mul_le_mul_of_nonneg_left _ hA
        have h1 : Real.log x ^ 2 ≤ l T ^ 2 := pow_le_pow_left₀ hu0 hul 2
        have h2 : l T ^ 2 ≤ l T ^ 2 * (1 + Real.log x) := by
          have : 0 ≤ l T ^ 2 := sq_nonneg _
          nlinarith
        linarith
    _ = _ := by ring

theorem eGen_H2 (hre : ∀ T, (Lb T).re = l T / 2) {T : ℝ} (hT : T0re ≤ T) (r : ℕ) {x : ℝ} (hx2 : 2 ≤ x) (hxl : x ≤ Real.exp (l T)) :
    ∑ N ∈ Ioc 0 ⌊x⌋₊, ‖eGen Lb T r N‖ ^ 2 ≤ CF * (4 / l T) ^ (2 * r) * x * l T ^ 2 := by
  have h := sum_norm_eGen_sq_div_le Lb hre hT r hx2 hxl
  have hl := l_ge_of_T0re_le hT
  have hKe : 0 ≤ 128 * Real.exp 1 * KM := mul_nonneg (by positivity) KM_nonneg
  have hxpos : 0 < x := by linarith
  have hu0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hul : Real.log x ≤ l T := (Real.log_le_iff_le_exp hxpos).mpr hxl
  have hA : 0 ≤ CF * (4 / l T) ^ (2 * r) := by
    have : 0 ≤ 4 / l T := by apply div_nonneg (by norm_num); linarith
    exact mul_nonneg CF_pos.le (pow_nonneg this _)
  have hstep : ∑ N ∈ Ioc 0 ⌊x⌋₊, ‖eGen Lb T r N‖ ^ 2 ≤ x * ∑ N ∈ Ioc 0 ⌊x⌋₊, ‖eGen Lb T r N‖ ^ 2 / N := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun N hN => ?_
    have hN0 : (0:ℝ) < N := by exact_mod_cast (mem_Ioc.mp hN).1
    have hNx : (N:ℝ) ≤ x := (Nat.cast_le.mpr (mem_Ioc.mp hN).2).trans (Nat.floor_le hxpos.le)
    rw [mul_div_assoc', le_div_iff₀ hN0, mul_comm x]
    exact mul_le_mul_of_nonneg_left hNx (sq_nonneg _)
  calc ∑ N ∈ Ioc 0 ⌊x⌋₊, ‖eGen Lb T r N‖ ^ 2
      ≤ x * (CF * (4 / l T) ^ (2 * r) * Real.log x ^ 2) := hstep.trans (mul_le_mul_of_nonneg_left h hxpos.le)
    _ ≤ x * (CF * (4 / l T) ^ (2 * r) * l T ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hxpos.le
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu0 hul 2) hA
    _ = _ := by ring

theorem eGen_H1 (hre : ∀ T, (Lb T).re = l T / 2) {T : ℝ} (hT : T0re ≤ T) (r : ℕ) {x : ℝ} (hx2 : 2 ≤ x) (hxl : x ≤ Real.exp (l T)) :
    ∑ N ∈ Ioc 0 ⌊x⌋₊, ‖eGen Lb T r N‖ / Real.sqrt N ≤ CF * (4 / l T) ^ r * Real.sqrt x * l T := by
  have h := sum_norm_eGen_sq_div_le Lb hre hT r hx2 hxl
  have hl := l_ge_of_T0re_le hT
  have hKe : 0 ≤ 128 * Real.exp 1 * KM := mul_nonneg (by positivity) KM_nonneg
  have hl0 : 0 < l T := by linarith
  have hxpos : 0 < x := by linarith
  have hu0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hul : Real.log x ≤ l T := (Real.log_le_iff_le_exp hxpos).mpr hxl
  have hρ : 0 ≤ 4 / l T := by positivity
  -- Cauchy–Schwarz
  have hcs := sq_sum_le_card_mul_sum_sq (s := Ioc 0 ⌊x⌋₊) (f := fun N => ‖eGen Lb T r N‖ / Real.sqrt N)
  have hsq : ∀ N ∈ Ioc 0 ⌊x⌋₊, (‖eGen Lb T r N‖ / Real.sqrt N) ^ 2 = ‖eGen Lb T r N‖ ^ 2 / N := by
    intro N _; rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  rw [Finset.sum_congr rfl hsq] at hcs
  have hcard : ((Ioc 0 ⌊x⌋₊).card : ℝ) ≤ x := by
    simp only [Nat.card_Ioc, Nat.sub_zero]; exact Nat.floor_le hxpos.le
  have hS0 : 0 ≤ ∑ N ∈ Ioc 0 ⌊x⌋₊, ‖eGen Lb T r N‖ ^ 2 / N :=
    Finset.sum_nonneg fun N _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg N)
  have hbound : (∑ N ∈ Ioc 0 ⌊x⌋₊, ‖eGen Lb T r N‖ / Real.sqrt N) ^ 2
      ≤ (CF * (4 / l T) ^ r * Real.sqrt x * l T) ^ 2 := by
    calc (∑ N ∈ Ioc 0 ⌊x⌋₊, ‖eGen Lb T r N‖ / Real.sqrt N) ^ 2
        ≤ (Ioc 0 ⌊x⌋₊).card * ∑ N ∈ Ioc 0 ⌊x⌋₊, ‖eGen Lb T r N‖ ^ 2 / N := hcs
      _ ≤ x * (CF * (4 / l T) ^ (2 * r) * Real.log x ^ 2) := mul_le_mul hcard h hS0 hxpos.le
      _ ≤ x * (CF * (4 / l T) ^ (2 * r) * l T ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hxpos.le
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu0 hul 2)
            (mul_nonneg CF_pos.le (pow_nonneg hρ _))
      _ ≤ x * (CF ^ 2 * (4 / l T) ^ (2 * r) * l T ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hxpos.le
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hρ _)
          -- CF ≤ CF² since CF ≥ 1
          have hCF1 : 1 ≤ CF := by unfold CF; linarith [Real.exp_pos 64]
          nlinarith
      _ = (CF * (4 / l T) ^ r * Real.sqrt x * l T) ^ 2 := by
          rw [show (CF * (4 / l T) ^ r * Real.sqrt x * l T) ^ 2
              = CF ^ 2 * ((4 / l T) ^ r) ^ 2 * Real.sqrt x ^ 2 * l T ^ 2 by ring,
            Real.sq_sqrt hxpos.le, ← pow_mul, mul_comm r 2]
          ring
  have hlhs0 : 0 ≤ ∑ N ∈ Ioc 0 ⌊x⌋₊, ‖eGen Lb T r N‖ / Real.sqrt N :=
    Finset.sum_nonneg fun N _ => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hrhs0 : 0 ≤ CF * (4 / l T) ^ r * Real.sqrt x * l T := by
    have := CF_pos.le; positivity
  exact (pow_le_pow_iff_left₀ hlhs0 hrhs0 two_ne_zero).mp hbound


end generic

end XiPrime
end Zeta23
