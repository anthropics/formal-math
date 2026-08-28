/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Coeff/H3.lean — (H3) assembled  [XF′ Lemma 7.1].

  ∀ ε > 0 ∃ T₀ ∀ T ≥ T₀ ∀ y ∈ [0, l(T)]:  | Σ_{N≤e^y} ‖C(N;Λ⋆(T))‖²/N − l(T)²·∫₀^{y/l} D₁ | ≤ ε·l(T)²
from Coeff/DiagLaw (partition; remainder bound; layers ω = k ≥ 2), Coeff/LayerOne (layer ω = 1),
Coeff/Tail, Certificate/D1, and Coeff/MainTerm.
-/
import Zeta23.XiPrime.Coeff.LayerOne
import Zeta23.XiPrime.Certificate.D1

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Omega ArithmeticFunction.omega
open Finset Real Filter

noncomputable section

namespace Zeta23
namespace XiPrime

/-- d_{j+2} is the (j+1)-st integrated D₁ coefficient:  dcoef (j+2) = D1coeff (j+1)/(2(j+1)+4). -/
lemma dcoef_eq_D1coeff (j : ℕ) : dcoef (j + 2) = D1coeff (j + 1) / (2 * ((j + 1 : ℕ) : ℝ) + 4) := by
  simp only [dcoef, D1coeff]
  rw [show j + 2 - 1 = j + 1 by omega, show 2 * (j + 1) + 2 = 2 * (j + 2) by ring]
  have h1 : ((j + 1).factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((2 * (j + 2)).factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- l(T) ≥ l₀ once T ≥ 2π·e^{l₀}. -/
lemma l_ge_of_le {l₀ T : ℝ} (hT : 2 * Real.pi * Real.exp l₀ ≤ T) : l₀ ≤ l T := by
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hT
  unfold l
  rw [Real.le_log_iff_exp_le (div_pos hTpos h2pi), le_div_iff₀ h2pi]
  linarith

set_option maxHeartbeats 1600000 in
/-- **(H3) the diagonal law** [XF′ Lemma 7.1] for a parameter family with Re Λ⋆ = l/2, |Im Λ⋆| ≤ 1. -/
theorem coeff_H3 (Λf : ℝ → ℂ) (hre : ∀ T, (Λf T).re = l T / 2) (him : ∀ T, |(Λf T).im| ≤ 1) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ y : ℝ, 0 ≤ y → y ≤ l T →
      |(∑ N ∈ Finset.Ioc 0 ⌊Real.exp y⌋₊, ‖xiCoeff (Λf T) N‖ ^ 2 / N)
          - l T ^ 2 * ∫ s in (0:ℝ)..(y / l T), D1 s| ≤ ε * l T ^ 2 := by
  intro ε hε
  -- (1) the two tails fix K
  obtain ⟨K₁, hK₁⟩ := Fmaj_tail_small (ε / 8) (by positivity)
  have hD := tendsto_D1coeff_tail
  rw [Metric.tendsto_atTop] at hD
  obtain ⟨K₂, hK₂⟩ := hD (ε / 8) (by positivity)
  obtain ⟨K', hK'def⟩ : ∃ K' : ℕ, max K₁ K₂ ≤ K' := ⟨max K₁ K₂, le_rfl⟩
  set K : ℕ := K' + 1 with hKdef
  have hK1 : 1 ≤ K := Nat.succ_le_succ (Nat.zero_le _)
  have hKK₁ : K₁ ≤ K := by have := le_max_left K₁ K₂; omega
  have hKK₂ : K₂ ≤ K := by have := le_max_right K₁ K₂; omega
  -- (2) per-layer constants
  obtain ⟨C1, hC1⟩ := sfPart_one_asymp
  choose Ck hCk using fun i : ℕ => sfPart_asymp (i + 2) (by omega)
  obtain ⟨Cn, hCn0, hCn⟩ := bPart_le K hK1
  set CA : ℝ := |C1| + ∑ i ∈ range K', |Ck i| with hCA
  set CB : ℝ := ∑ i ∈ range K, 2 ^ (i + 1) * 2 ^ i * 4 ^ (i + 1) * Cn i with hCB
  have hCA0 : 0 ≤ CA := by positivity
  have hCB0 : 0 ≤ CB := sum_nonneg fun i _ => by have := hCn0 i; positivity
  have hCdef0 : (0:ℝ) ≤ Cdef := by unfold Cdef; norm_num
  set CT : ℝ := 2 * CA + 2 * Cdef + 2 * CB with hCT
  have hCT0 : 0 ≤ CT := by positivity
  -- (3) the threshold
  set l₀ : ℝ := max (64 * Real.exp 1 * KM + 2) (2 * CT / ε + 1) with hl₀
  refine ⟨2 * Real.pi * Real.exp l₀, fun T hT y hy hyl => ?_⟩
  have hl₀T : l₀ ≤ l T := l_ge_of_le hT
  set L : ℝ := l T with hLdef
  set Λs : ℂ := Λf T with hΛsdef
  have hL64 : 64 * Real.exp 1 * KM + 2 ≤ L := (le_max_left _ _).trans hl₀T
  have hLCT : 2 * CT / ε + 1 ≤ L := (le_max_right _ _).trans hl₀T
  have hL2 : 2 ≤ L := by nlinarith [KM_nonneg, Real.exp_pos 1]
  have hL0 : 0 < L := by linarith
  have hLne : L ≠ 0 := hL0.ne'
  have hreT : Λs.re = L / 2 := hre T
  have himT : |Λs.im| ≤ 1 := him T
  have hnorm : L / 2 ≤ ‖Λs‖ := norm_param_ge hL2 hreT himT
  have hΛpos : 0 < ‖Λs‖ := by linarith
  have hbig : 32 * Real.exp 1 * KM ≤ ‖Λs‖ := by linarith
  set x : ℝ := ‖Λs‖⁻¹ with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ≤ 2 / L := by
    rw [hxdef, inv_le_comm₀ hΛpos (by positivity), inv_div]; linarith
  have hxy : x * y ≤ 4 := by
    calc x * y ≤ (2 / L) * L := mul_le_mul hx2 hyl hy (by positivity)
      _ = 2 := by field_simp
      _ ≤ 4 := by norm_num
  have hxK : 32 * Real.exp 1 * KM * x ≤ 1 := by
    rw [hxdef, ← div_eq_mul_inv, div_le_one hΛpos]; exact hbig
  have hxsq : x ^ 2 ≤ 4 / L ^ 2 := by
    calc x ^ 2 ≤ (2 / L) ^ 2 := pow_le_pow_left₀ hx0 hx2 2
      _ = 4 / L ^ 2 := by rw [div_pow]; norm_num
  set s : ℝ := y / L with hsdef
  have hs0 : 0 ≤ s := div_nonneg hy hL0.le
  have hs1 : s ≤ 1 := (div_le_one hL0).mpr hyl
  have hy1 : 1 + y ≤ 2 * L := by linarith
  have hy1' : 0 ≤ 1 + y := by linarith
  -- (4) the partition and the layers
  have hsplit := diag_split Λs K y
  have hlayers : ∑ k ∈ range (K + 1), sfPart Λs k y
      = (∑ i ∈ range K', sfPart Λs (i + 2) y) + sfPart Λs 1 y + sfPart Λs 0 y := by
    rw [hKdef, sum_range_succ', sum_range_succ']
  rw [sfPart_zero, add_zero] at hlayers
  -- (5) the truncated main term
  have hmain : L ^ 2 * ∫ u in (0:ℝ)..s, D1trunc K u
      = L ^ 2 * (s ^ 2 / 2 - 4 * s ^ 3 / 3 + s ^ 4)
        + ∑ i ∈ range K', L ^ 2 * (dcoef (i + 2) * s ^ (2 * (i + 2) + 2)) := by
    rw [integral_D1trunc, hKdef, sum_range_succ', D1coeff_zero, ← mul_sum]
    have h4 : (4:ℝ) * s ^ (2 * 0 + 4) / (2 * (0:ℕ) + 4) = s ^ 4 := by norm_num
    rw [h4]
    have hterm : ∀ i ∈ range K', D1coeff (i + 1) * s ^ (2 * (i + 1) + 4) / (2 * ((i + 1 : ℕ) : ℝ) + 4)
        = dcoef (i + 2) * s ^ (2 * (i + 2) + 2) := by
      intro i _
      rw [dcoef_eq_D1coeff, show 2 * (i + 1) + 4 = 2 * (i + 2) + 2 by ring]
      ring
    rw [sum_congr rfl hterm]
    ring
  have hD1tail : |(∫ u in (0:ℝ)..s, D1 u) - ∫ u in (0:ℝ)..s, D1trunc K u| ≤ ε / 8 := by
    refine (abs_integral_D1_sub_le K hs0 hs1).trans ?_
    have h := hK₂ K hKK₂
    rw [Real.dist_eq, sub_zero] at h
    exact (le_abs_self _).trans h.le
  -- (6) layer errors
  have hE1 : |sfPart Λs 1 y - L ^ 2 * (s ^ 2 / 2 - 4 * s ^ 3 / 3 + s ^ 4)| ≤ |C1| * (1 + L) :=
    (hC1 L hL2 Λs hreT himT y hy hyl).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
  have hEk : |(∑ i ∈ range K', sfPart Λs (i + 2) y) - ∑ i ∈ range K', L ^ 2 * (dcoef (i + 2) * s ^ (2 * (i + 2) + 2))|
      ≤ (∑ i ∈ range K', |Ck i|) * (1 + L) := by
    rw [← sum_sub_distrib, sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
    exact (hCk i L hL2 Λs hreT himT y hy hyl).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
  -- (7) the remainder layer
  have hB := hCn Λs y hy hxy hbig
  have htail : ∑ i ∈ (range ⌊Real.exp y⌋₊).filter (fun i => K ≤ i),
      2 ^ (i + 1) * x ^ (2 * (i + 1)) * y ^ (i + 1) * Sdiv (Λ ^ (i + 1)) y ≤ ε / 8 := by
    refine le_trans ?_ (hK₁ x y hx0 hy hxy hxK ⌊Real.exp y⌋₊)
    refine sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => ?_
    · intro i hi
      rw [mem_filter] at hi ⊢
      exact ⟨hi.1, hKK₁.trans hi.2⟩
    · exact mul_nonneg (by positivity) (Sdiv_nonneg (lamPow_nonneg _) _)
  have hfin : 2 * y ^ 2 * ∑ i ∈ range K, 2 ^ (i + 1) * x ^ (2 * (i + 1)) * y ^ (i + 1) * (Cn i * (1 + y) ^ i)
      ≤ 2 * CB * L := by
    rw [hCB, mul_sum, mul_sum, sum_mul]
    refine sum_le_sum fun i _ => ?_
    -- x^{2(i+1)} ≤ (4/L²)^{i+1};  y^{i+3}(1+y)^i ≤ L^{i+3}(2L)^i = 2^i·(L²)^{i+1}·L
    have hxpow : x ^ (2 * (i + 1)) ≤ (4 / L ^ 2) ^ (i + 1) := by
      rw [pow_mul]; exact pow_le_pow_left₀ (sq_nonneg x) hxsq _
    have hkey : (4 / L ^ 2) ^ (i + 1) * (L ^ (i + 1 + 2) * (2 * L) ^ i) = 2 ^ i * 4 ^ (i + 1) * L := by
      have : L ^ (i + 1 + 2) * (2 * L) ^ i = 2 ^ i * ((L ^ 2) ^ (i + 1) * L) := by
        rw [mul_pow, ← pow_mul]; ring
      rw [this, div_pow]
      have hL2ne : (L ^ 2) ^ (i + 1) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hLne)
      field_simp
    calc 2 * y ^ 2 * (2 ^ (i + 1) * x ^ (2 * (i + 1)) * y ^ (i + 1) * (Cn i * (1 + y) ^ i))
        = 2 * 2 ^ (i + 1) * Cn i * (x ^ (2 * (i + 1)) * (y ^ (i + 1 + 2) * (1 + y) ^ i)) := by ring
      _ ≤ 2 * 2 ^ (i + 1) * Cn i * ((4 / L ^ 2) ^ (i + 1) * (L ^ (i + 1 + 2) * (2 * L) ^ i)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by have := hCn0 i; positivity)
          exact mul_le_mul hxpow (mul_le_mul (pow_le_pow_left₀ hy hyl _) (pow_le_pow_left₀ hy1' hy1 _)
            (pow_nonneg hy1' _) (pow_nonneg hL0.le _)) (mul_nonneg (pow_nonneg hy _) (pow_nonneg hy1' _))
            (pow_nonneg (by positivity) _)
      _ = 2 * 2 ^ (i + 1) * Cn i * (2 ^ i * 4 ^ (i + 1) * L) := by rw [hkey]
      _ = 2 * (2 ^ (i + 1) * 2 ^ i * 4 ^ (i + 1) * Cn i) * L := by ring
  have hBle : bPart Λs K y ≤ 2 * Cdef + ε / 4 * L ^ 2 + 2 * CB * L := by
    have hy2 : y ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hy hyl 2
    calc bPart Λs K y ≤ _ := hB
      _ = 2 * Cdef + 2 * y ^ 2 * (∑ i ∈ (range ⌊Real.exp y⌋₊).filter (fun i => K ≤ i),
            2 ^ (i + 1) * x ^ (2 * (i + 1)) * y ^ (i + 1) * Sdiv (Λ ^ (i + 1)) y)
          + 2 * y ^ 2 * ∑ i ∈ range K, 2 ^ (i + 1) * x ^ (2 * (i + 1)) * y ^ (i + 1) * (Cn i * (1 + y) ^ i) := by
          ring
      _ ≤ 2 * Cdef + 2 * L ^ 2 * (ε / 8) + 2 * CB * L := by
          refine add_le_add (add_le_add le_rfl ?_) hfin
          exact mul_le_mul (by linarith) htail (sum_nonneg fun i _ =>
            mul_nonneg (by positivity) (Sdiv_nonneg (lamPow_nonneg _) _)) (by positivity)
      _ = 2 * Cdef + ε / 4 * L ^ 2 + 2 * CB * L := by ring
  -- (8) assemble
  have hdecomp : (∑ N ∈ Ioc 0 ⌊Real.exp y⌋₊, ‖xiCoeff Λs N‖ ^ 2 / N) - L ^ 2 * ∫ u in (0:ℝ)..s, D1 u
      = (sfPart Λs 1 y - L ^ 2 * (s ^ 2 / 2 - 4 * s ^ 3 / 3 + s ^ 4))
        + ((∑ i ∈ range K', sfPart Λs (i + 2) y) - ∑ i ∈ range K', L ^ 2 * (dcoef (i + 2) * s ^ (2 * (i + 2) + 2)))
        + bPart Λs K y
        - L ^ 2 * ((∫ u in (0:ℝ)..s, D1 u) - ∫ u in (0:ℝ)..s, D1trunc K u) := by
    rw [hsplit, hlayers, mul_sub, hmain]; ring
  rw [hdecomp]
  have hB0 := bPart_nonneg Λs K y
  calc |(sfPart Λs 1 y - L ^ 2 * (s ^ 2 / 2 - 4 * s ^ 3 / 3 + s ^ 4))
        + ((∑ i ∈ range K', sfPart Λs (i + 2) y) - ∑ i ∈ range K', L ^ 2 * (dcoef (i + 2) * s ^ (2 * (i + 2) + 2)))
        + bPart Λs K y
        - L ^ 2 * ((∫ u in (0:ℝ)..s, D1 u) - ∫ u in (0:ℝ)..s, D1trunc K u)|
      ≤ |(sfPart Λs 1 y - L ^ 2 * (s ^ 2 / 2 - 4 * s ^ 3 / 3 + s ^ 4))
          + ((∑ i ∈ range K', sfPart Λs (i + 2) y) - ∑ i ∈ range K', L ^ 2 * (dcoef (i + 2) * s ^ (2 * (i + 2) + 2)))|
        + |bPart Λs K y|
        + |L ^ 2 * ((∫ u in (0:ℝ)..s, D1 u) - ∫ u in (0:ℝ)..s, D1trunc K u)| := abs_sub_le_of_three _ _ _
    _ ≤ (|C1| * (1 + L) + (∑ i ∈ range K', |Ck i|) * (1 + L))
        + (2 * Cdef + ε / 4 * L ^ 2 + 2 * CB * L) + L ^ 2 * (ε / 8) := by
        refine add_le_add (add_le_add ((abs_add_le _ _).trans (add_le_add hE1 hEk)) ?_) ?_
        · rw [abs_of_nonneg hB0]; exact hBle
        · rw [abs_mul, abs_of_nonneg (sq_nonneg L)]
          exact mul_le_mul_of_nonneg_left hD1tail (sq_nonneg L)
    _ = CA * (1 + L) + 2 * Cdef + 2 * CB * L + (3 * ε / 8) * L ^ 2 := by rw [hCA]; ring
    _ ≤ CT * L + (3 * ε / 8) * L ^ 2 := by
        have hL1 : 1 ≤ L := by linarith
        have h1 : CA * (1 + L) ≤ 2 * CA * L := by nlinarith [mul_nonneg hCA0 (sub_nonneg.mpr hL1)]
        have h2 : 2 * Cdef ≤ 2 * Cdef * L := by nlinarith [mul_nonneg hCdef0 (sub_nonneg.mpr hL1)]
        rw [hCT]; linarith
    _ ≤ (ε / 2) * L ^ 2 + (3 * ε / 8) * L ^ 2 := by
        -- from 2CT/ε + 1 ≤ L:  CT ≤ (ε/2)·L
        have h1 : 2 * CT / ε ≤ L := by linarith
        have h2 : 2 * CT ≤ L * ε := by rwa [div_le_iff₀ hε] at h1
        have h3 : 2 * CT * L ≤ L * ε * L := mul_le_mul_of_nonneg_right h2 hL0.le
        have h4 : CT * L ≤ (ε / 2) * L ^ 2 := by nlinarith [h3]
        linarith
    _ ≤ ε * L ^ 2 := by
        have : 0 ≤ ε * L ^ 2 := mul_nonneg hε.le (sq_nonneg L)
        linarith

end XiPrime
end Zeta23
