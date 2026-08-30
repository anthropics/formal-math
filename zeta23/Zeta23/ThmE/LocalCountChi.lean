/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The two-sided local zero count for L(s,χ):
  N_χ(t, t+1] ≤ A₀ log(|t|+3)  for ALL real t  (A₀ depends on q through the growth constants) —
  derived from the q-uniform count `localCountChi_uniform_proof` (one absolute A₀, log(q(|t|+3))).
Route: halve by Zeta23.ZeroConfig.N_le_two_mul_half
(applied to LZeros), then ZerosBound on g(w) := L(c₀+1.9w,χ)/L(c₀,χ),
c₀ = 2+(t+½)i, r = .84, R = .95, with Zeta23.ThmE.LFunction_growth_right / LFunction_lower_bound_two;
L(·,χ) is entire for χ ≠ 1, so no pole bookkeeping and no |t| ≥ 4 split.
-/
import Zeta23.ThmE.LGrowth
import Zeta23.ThmE.Statement
import Zeta23.RvM.Halving
import Zeta23.RvM.ReZeroCount
import Zeta23.FromPNTPlus.StrongPNTPrefix

open Complex Set DirichletCharacter

noncomputable section

namespace Zeta23
namespace ThmE

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- rescaled L: w ↦ L(c₀ + κ w, χ) · u. -/
def gfunL (χ : DirichletCharacter ℂ q) (c₀ κ u : ℂ) (z : ℂ) : ℂ := χ.LFunction (c₀ + κ * z) * u

lemma gfunL_analyticAt (hχ1 : χ ≠ 1) (c₀ κ u z : ℂ) : AnalyticAt ℂ (gfunL χ c₀ κ u) z := by
  unfold gfunL
  have hL : AnalyticAt ℂ χ.LFunction (c₀ + κ * z) :=
    LFunction_analyticOnNhd hχ1 _ (Set.mem_univ _)
  have haff : AnalyticAt ℂ (fun z : ℂ => c₀ + κ * z) z := by fun_prop
  have hcomp : AnalyticAt ℂ (fun z => χ.LFunction (c₀ + κ * z)) z := hL.comp_of_eq haff rfl
  have hconst : AnalyticAt ℂ (fun _ : ℂ => u) z := analyticAt_const
  exact hcomp.mul hconst

lemma analyticOrderNatAt_gfunL (hχ1 : χ ≠ 1) {c₀ κ u : ℂ} (hκ0 : κ ≠ 0) (hu0 : u ≠ 0) (w : ℂ) :
    analyticOrderNatAt (gfunL χ c₀ κ u) w = zeroMultL χ (c₀ + κ * w) := by
  unfold analyticOrderNatAt zeroMultL gfunL
  congr 1
  have haff : AnalyticAt ℂ (fun z : ℂ => c₀ + κ * z) w := by fun_prop
  have hcomp : AnalyticAt ℂ (fun z => χ.LFunction (c₀ + κ * z)) w := by
    have hL : AnalyticAt ℂ χ.LFunction (c₀ + κ * w) :=
      LFunction_analyticOnNhd hχ1 _ (Set.mem_univ _)
    exact hL.comp_of_eq haff rfl
  have hmul : (fun z ↦ χ.LFunction (c₀ + κ * z) * u) =
      (fun z => χ.LFunction (c₀ + κ * z)) * fun _ => u := rfl
  rw [hmul, analyticOrderAt_mul hcomp analyticAt_const]
  have hconst : analyticOrderAt (fun _ : ℂ => u) w = 0 :=
    (analyticAt_const).analyticOrderAt_eq_zero.mpr hu0
  rw [hconst, add_zero]
  have hderiv : deriv (fun z : ℂ => c₀ + κ * z) w ≠ 0 := by
    rw [deriv_const_add, deriv_const_mul _ differentiableAt_id, deriv_id'']; simpa using hκ0
  have := analyticOrderAt_comp_of_deriv_ne_zero (f := χ.LFunction) haff hderiv
  simpa [Function.comp_def] using this

/-! ## The q-UNIFORM count (one absolute A₀ for every primitive χ mod q > 1) -/

set_option maxHeartbeats 1600000 in
/-- **q-uniform local count**: ONE absolute A₀ with
N_χ(t,t+1] ≤ A₀·log(q(|t|+3)) for every primitive χ mod q > 1.  Same disc/ZerosBound argument as the ζ local
count, with the uniform linear growth ‖L(s,χ)‖ ≤ 8q(|Im s|+3) (LFunction_growth_right_uniform) so that log B
stays additive in log q. -/
theorem localCountChi_uniform_proof : ∃ A₀ : ℝ, 1 ≤ A₀ ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
    ∀ t : ℝ, (NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)) := by
  set r : ℝ := 0.84 with hr
  set R : ℝ := 0.95 with hR
  have hlogRr : 0 < Real.log (R / r) := Real.log_pos (by norm_num [hr, hR])
  refine ⟨max 1 (2 * (1 / Real.log (R / r) * 5)), le_max_left _ _, ?_⟩
  intro q _ χ hq1 hprim t
  have hχ1 : χ ≠ 1 := ne_one_of_primitive hq1 hprim
  have hs : LSeam χ := LSeam_of hq1 hprim
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  -- the absolute log quantity
  set L : ℝ := Real.log ((q:ℝ) * (|t| + 3)) with hLdef
  have hqt6 : (6:ℝ) ≤ (q:ℝ) * (|t| + 3) := by nlinarith [abs_nonneg t]
  have hL1 : 1 ≤ L := by
    rw [hLdef, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have hL0 : 0 < L := by linarith
  -- halving
  have hhalf : (NcountL χ t (t + 1) : ℝ) ≤
      2 * ∑ᶠ ρ ∈ (LZeros hs).window t (t + 1) ∩ {ρ : ℂ | 1/2 ≤ ρ.re}, ((LZeros hs).mult ρ : ℝ) := by
    have := (LZeros hs).N_le_two_mul_half t (t + 1)
    rwa [LZeros_N] at this
  set c₀ : ℂ := 2 + (t + 1/2 : ℝ) * I with hc₀
  set κ : ℂ := ((19/10 : ℝ) : ℂ) with hκ
  have hκ0 : κ ≠ 0 := by simp [hκ]
  have hnormκ : ‖κ‖ = 1.9 := by simp [hκ]; norm_num
  have hLc₀ : (1/3 : ℝ) ≤ ‖χ.LFunction c₀‖ := LFunction_lower_bound_two (by simp [hc₀])
  have hLc₀ne : χ.LFunction c₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hLc₀; norm_num at hLc₀
  set u : ℂ := (χ.LFunction c₀)⁻¹ with hu
  have hu0 : u ≠ 0 := inv_ne_zero hLc₀ne
  have hnu : ‖u‖ ≤ 3 := by
    rw [hu, norm_inv]; rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  set G : ℂ → ℂ := gfunL χ c₀ κ u with hG
  have hfAnalytic : AnalyticOnNhd ℂ G (Metric.closedBall (0:ℂ) 1) :=
    fun z _ => gfunL_analyticAt hχ1 c₀ κ u z
  have hG0 : G 0 = 1 := by
    simp only [hG, gfunL, mul_zero, add_zero, hu]
    exact mul_inv_cancel₀ hLc₀ne
  have hfin : (SetOfZeros 1 G).Finite := by
    have h := RvM.finite_zeros_closedBall (f := G) (R := 1.05) (r := 1) (by norm_num)
      (fun z _ => gfunL_analyticAt hχ1 c₀ κ u z) (z₀ := 0) (by simp; norm_num)
      (by rw [hG0]; exact one_ne_zero)
    exact h.subset (by intro z hz; exact hz)
  set B : ℝ := 24 * (q:ℝ) * (|t| + 6) with hB
  have hBpos : 0 < B := by positivity
  have hfz : ∀ z : ℂ, ‖z‖ ≤ R → ‖G z‖ ≤ B := by
    intro z hz
    set s : ℂ := c₀ + κ * z with hs'
    have hκre : κ.re = 1.9 := by rw [hκ]; norm_num [Complex.ofReal_re]
    have hκim : κ.im = 0 := by rw [hκ]; simp
    have hzre := abs_le.mp ((Complex.abs_re_le_norm z).trans hz)
    have hzim := abs_le.mp ((Complex.abs_im_le_norm z).trans hz)
    rw [hR] at hzre hzim
    have hsre : s.re = 2 + 1.9 * z.re := by
      rw [hs', hc₀]
      simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.re_ofNat, hκre, hκim]
      ring
    have hsim : s.im = (t + 1/2) + 1.9 * z.im := by
      rw [hs', hc₀]
      simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.im_ofNat, hκre, hκim]
      ring
    have h1 : (0.15:ℝ) ≤ s.re := by rw [hsre]; nlinarith
    have h3 := LFunction_growth_right_uniform hχ1 h1
    have hbase : |s.im| + 3 ≤ |t| + 6 := by
      rw [hsim]
      have h4 := abs_add_le (t + 1/2) (1.9 * z.im)
      have h5 : |1.9 * z.im| ≤ 1.9 * 0.95 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1.9)]
        have : |z.im| ≤ 0.95 := abs_le.mpr ⟨hzim.1, hzim.2⟩
        nlinarith
      have h6 : |t + 1/2| ≤ |t| + 1/2 := by simpa using abs_add_le t (1/2)
      linarith
    calc ‖G z‖ = ‖χ.LFunction s‖ * ‖u‖ := by rw [hG]; exact norm_mul _ _
      _ ≤ (8 * q * (|s.im| + 3)) * 3 := by
          apply mul_le_mul h3 hnu (norm_nonneg _) (by positivity)
      _ ≤ (8 * q * (|t| + 6)) * 3 := by nlinarith
      _ = B := by rw [hB]; ring
  have hrlt1 : r < 1 := by norm_num [hr]
  have hZ := ZerosBound (B := B) (r := r) (R := R) (by norm_num [hr]) hrlt1
    (by norm_num [hr, hR]) (by norm_num [hR]) hfAnalytic hG0 hfin hfz
  set Z : Finset ℂ := (finiteSetOfZeros_mono hrlt1 hfin).toFinset with hZdef
  set W : Set ℂ := (LZeros hs).window t (t + 1) ∩ {ρ : ℂ | 1/2 ≤ ρ.re} with hW
  have hWfin : W.Finite := ((LZeros hs).window_finite t (t + 1)).subset inter_subset_left
  set φ : ℂ → ℂ := fun ρ => (ρ - c₀) / κ with hφ
  have hφinj : Function.Injective φ := by
    intro a b h; simp only [hφ] at h
    have := congrArg (fun w => c₀ + κ * w) h
    simpa [mul_div_cancel₀ _ hκ0] using this
  have hφinv : ∀ ρ, c₀ + κ * φ ρ = ρ := by intro ρ; simp only [hφ]; field_simp; ring
  have hmemS : ∀ ρ ∈ W, φ ρ ∈ Z := by
    rintro ρ ⟨⟨hρZ, hρt, hρt1⟩, hρre⟩
    have hρ : IsNontrivialZeroL χ ρ := by rwa [LZeros_carrier] at hρZ
    rw [hZdef, Set.Finite.mem_toFinset]
    refine ⟨?_, ?_⟩
    · show ‖φ ρ‖ ≤ r
      simp only [hφ, norm_div, hnormκ]
      rw [div_le_iff₀ (by norm_num), hr]
      have hre : (ρ - c₀).re = ρ.re - 2 := by simp [hc₀]
      have him : (ρ - c₀).im = ρ.im - (t + 1/2) := by simp [hc₀]
      have hsq : ‖ρ - c₀‖ ^ 2 ≤ (0.84 * 1.9) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
        have := hρ.2.2; have := hρre.out
        nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp hsq
    · show G (φ ρ) = 0
      simp only [hG, gfunL, hφinv]
      rw [hρ.1, zero_mul]
  have hmult : ∀ ρ ∈ W, ((LZeros hs).mult ρ : ℝ) = (analyticOrderNatAt G (φ ρ) : ℝ) := by
    rintro ρ ⟨⟨hρZ, -, -⟩, -⟩
    rw [LZeros_mult, hG, analyticOrderNatAt_gfunL hχ1 hκ0 hu0, hφinv]
  have hsum : (∑ᶠ ρ ∈ W, ((LZeros hs).mult ρ : ℝ)) ≤
      ((∑ ρ' ∈ Z, analyticOrderNatAt G ρ' : ℕ) : ℝ) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hWfin,
      Finset.sum_congr rfl (fun ρ hρ => hmult ρ (hWfin.mem_toFinset.mp hρ)),
      ← Finset.sum_image (f := fun w => (analyticOrderNatAt G w : ℝ))
        (fun a _ b _ h => hφinj h)]
    push_cast
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro w hw
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hw
      exact hmemS ρ (hWfin.mem_toFinset.mp hρ)
    · intros; positivity
  -- log B ≤ 5 L, by monotonicity alone
  have hsq : (q:ℝ) * (|t| + 3) * ((q:ℝ) * (|t| + 3)) = ((q:ℝ) * (|t| + 3))^2 := by ring
  have hL6 : Real.log 6 ≤ L := by rw [hLdef]; exact Real.log_le_log (by norm_num) hqt6
  have hlog24 : Real.log 24 ≤ 2 * L := by
    have h36 : Real.log 24 ≤ Real.log 36 := Real.log_le_log (by norm_num) (by norm_num)
    have h2 : Real.log 36 = 2 * Real.log 6 := by
      rw [show (36:ℝ) = 6^2 by norm_num, Real.log_pow]; push_cast; ring
    linarith
  have hlogq : Real.log (q:ℝ) ≤ L := by
    rw [hLdef]
    apply Real.log_le_log hq0
    nlinarith [abs_nonneg t]
  have hlogt6 : Real.log (|t| + 6) ≤ 2 * L := by
    have h1 : Real.log (|t| + 6) ≤ Real.log (((q:ℝ) * (|t| + 3))^2) := by
      apply Real.log_le_log (by positivity)
      nlinarith [abs_nonneg t]
    have h2 : Real.log (((q:ℝ) * (|t| + 3))^2) = 2 * L := by
      rw [hLdef, Real.log_pow]; push_cast; ring
    linarith
  have hlogB : Real.log B ≤ 5 * L := by
    rw [hB, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity)]
    linarith
  calc (NcountL χ t (t + 1) : ℝ)
      ≤ 2 * ∑ᶠ ρ ∈ W, ((LZeros hs).mult ρ : ℝ) := hhalf
    _ ≤ 2 * ((∑ ρ' ∈ Z, analyticOrderNatAt G ρ' : ℕ) : ℝ) := by linarith [hsum]
    _ ≤ 2 * (1 / Real.log (R / r) * Real.log B) := by
        have h : ((∑ ρ' ∈ Z, analyticOrderNatAt G ρ' : ℕ) : ℝ) ≤
            1 / Real.log (R / r) * Real.log B := by exact_mod_cast hZ
        linarith
    _ ≤ 2 * (1 / Real.log (R / r) * (5 * L)) := by
        have := mul_le_mul_of_nonneg_left hlogB (by positivity : (0:ℝ) ≤ 1 / Real.log (R / r))
        linarith
    _ = (2 * (1 / Real.log (R / r) * 5)) * L := by ring
    _ ≤ max 1 (2 * (1 / Real.log (R / r) * 5)) * L := by
        apply mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)


/-- **Local count for L(s,χ)**, two-sided (per-χ constant; from the q-uniform count:
log(q(|t|+3)) = log q + log(|t|+3) ≤ (1 + log q)·log(|t|+3) as log(|t|+3) ≥ 1). -/
theorem localCountChi (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ, (NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3) := by
  obtain ⟨A₀, hA₀, h⟩ := localCountChi_uniform_proof
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hq)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq.le)
  refine ⟨A₀ * (1 + Real.log q), by nlinarith, fun t => ?_⟩
  have hlog3 : 1 ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith [abs_nonneg t]
  have hsplit : Real.log (q * (|t| + 3)) = Real.log q + Real.log (|t| + 3) :=
    Real.log_mul hq0.ne' (by linarith [abs_nonneg t])
  calc (NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)) := h q χ hq hprim t
    _ = A₀ * (Real.log q + Real.log (|t| + 3)) := by rw [hsplit]
    _ ≤ A₀ * ((1 + Real.log q) * Real.log (|t| + 3)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith); nlinarith
    _ = A₀ * (1 + Real.log q) * Real.log (|t| + 3) := by ring

end ThmE
end Zeta23
