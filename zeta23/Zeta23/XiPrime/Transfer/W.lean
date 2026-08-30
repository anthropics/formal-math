/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization.

Zeta23/XiPrime/Transfer/W.lean — Z′ (Hardy W) case: **the W trace transfer**.
Target (StatementW.lean §W3): XiTraceTransfer Z Pf wCoeffFamily at Z = wZeros hZ hs, i.e. the SAME Prop as
for ξ′ — comparison matrix GpC (F.c T), pole weight 1 — starting from the W explicit formula WEF (main term GpW1:
coefficients C(N; L_{2⋆}(τ⋆_{kl})), L_{2⋆} REAL, pole weight 2).

ROUTE.  G − Mᵀ = (G − M^𝒵) + (M^𝒵 − M^{c,2}) + (M^{c,2} − M^{c,1}), each HatNegligible:
  • G − M^𝒵:     [XF′ 5.1] engine hatNegligible_of_entryBound fed by WEF;
  • M^𝒵 − M^{c,2}: [XF′ 6.1] engine hatNegligible_of_geom at the REAL base ½l (L_{2⋆}(τ⋆) = ½l + δ_{kl}, the same
                  δ_{kl} = ½log(τ⋆/T) ∈ [0, ½log 2]), input ReexpansionW (Transfer/InputsW.lean);
  • M^{c,2} − M^{c,1} = the Π-part Gram matrix (∫ φ̂_k φ̂_l Π_X)_{kl} ([XF′ §9.3(i)]): by |Π_X(t+r)| ≤ 6√X/t + 12√X r²/t²
                  (PrimeSide.PiX_shift_bound) every entry is ≤ 6√X·2πaL/T + 12√X(8+2(cϱ/w)²)/T², so the hat-trace
                  is ≪ √X = o(N) and the hat-Frobenius² is ≪ X = o(N) (X ≤ T, l → ∞; no λ < 1 needed here).
-/
import Zeta23.XiPrime.Transfer
import Zeta23.XiPrime.Transfer.InputsW
import Zeta23.XiPrime.StatementW
import Zeta23.XiPrime.PrimeSide.Moments

noncomputable section

open Finset Filter Topology RHLinalg MeasureTheory Real
open scoped BigOperators

namespace Zeta23

namespace Params
variable (P : Params) (T : ℝ)

lemma GentryCW_eq_GentryW (cPi : ℝ) (c : ℕ → ℂ) (k l : ℤ) :
    P.GentryCW T cPi c k l = XiPrime.GentryW cPi c (P.toSetting T) (P.localFun T) k l := rfl

end Params

namespace XiPrime
open PrimeSide

/-- the Z′ base point ½ l(T) ∈ ℂ (real; = Defs.L2star at τ⋆ = T). -/
def L2T (T : ℝ) : ℂ := ((l T / 2 : ℝ) : ℂ)

theorem ReexpansionW.toAt {F : CoeffFamily} {e : ℝ → ℕ → ℕ → ℂ} {ρ₀ A T₀ : ℝ}
    (h : ReexpansionW F e ρ₀ A T₀) : ReexpansionAt L2T F.c e ρ₀ A T₀ :=
  ⟨h.expand, h.e_one, h.H1, h.H2, h.H3⟩

/-- L_{2⋆}(τ⋆) = ½l + ½log(τ⋆/T). -/
lemma L2star_eq_L2T_add (T : ℝ) {τs : ℝ} (hT : 0 < T) (hτ : 0 < τs) :
    ((L2star τs : ℝ) : ℂ) = L2T T + ((Real.log (τs / T) / 2 : ℝ) : ℂ) := by
  unfold L2star L2T l
  have h2π : (0:ℝ) < 2 * Real.pi := by positivity
  rw [Real.log_div hτ.ne' h2π.ne', Real.log_div hT.ne' h2π.ne', Real.log_div hτ.ne' hT.ne']
  push_cast
  ring

/-- the entries of M^𝒵 − M^{c,2}: P-part entries of the coefficient differences (μ, 2Π_X cancel). -/
lemma GpW1_sub_GpCW_apply (P : Params) (T : ℝ) {cϱ : ℝ} (hΓ : GammaFacts)
    (hF : LocalHypsCore cϱ (P.toSetting T) (P.localFun T)) (hX : 0 < P.X T) (hT : 0 < T)
    (hh : 0 ≤ P.hgrid T) (c : ℕ → ℂ) (k l : Fin (P.d T)) :
    (P.GpW1 T - P.GpCW T 2 c) k l
      = ((GentryNu (Pc (P.toSetting T).X (xiCoeff ((L2star (P.tauStar T k l) : ℝ) : ℂ) - c))
          (P.toSetting T) (P.localFun T) k l : ℝ) : ℂ) := by
  have hk := tau_pos P T (k := k) hT hh
  have hl := tau_pos P T (k := l) hT hh
  rw [Matrix.sub_apply]
  simp only [Params.GpW1, Params.GpCW, Params.GentryW1]
  rw [← Complex.ofReal_sub, Params.GentryCW_eq_GentryW, Params.GentryCW_eq_GentryW,
    Transfer.gentryW_sub hΓ hF hX 2 _ _ hk hl]

/-- the entries of M^{c,2} − M^{c,1}: the Π-part Gram matrix. -/
lemma GpCW_two_sub_GpC_apply (P : Params) (T : ℝ) {cϱ : ℝ} (hΓ : GammaFacts)
    (hF : LocalHypsCore cϱ (P.toSetting T) (P.localFun T)) (hX : 0 < P.X T) (hT : 0 < T)
    (hh : 0 ≤ P.hgrid T) (c : ℕ → ℂ) (k l : Fin (P.d T)) :
    (P.GpCW T 2 c - P.GpC T c) k l
      = ((GentryNu (Zeta23.PiX (P.toSetting T).X) (P.toSetting T) (P.localFun T) k l : ℝ) : ℂ) := by
  have hk := tau_pos P T (k := k) hT hh
  have hl := tau_pos P T (k := l) hT hh
  rw [XiPrime.GpC_eq_GpCW, Matrix.sub_apply]
  simp only [Params.GpCW]
  rw [← Complex.ofReal_sub, Params.GentryCW_eq_GentryW, Params.GentryCW_eq_GentryW,
    Transfer.gentryW_weight_sub hΓ hF hX 2 1 c hk hl]
  norm_num

/-! ### The Π-part entries are uniformly small -/

section PiPart
variable {cϱ : ℝ} {p : Setting} {Fn : LocalFun}

/-- ∫ φ̂(τ−t)² |Π_X(τ)| dτ ≤ 6√X·2πaL/t + 12√X(8+2(cϱ/w)²)/t²  for t ≥ 2. -/
lemma integral_phiHat_sq_abs_PiX_le (hF : LocalHypsCore cϱ p Fn) {t : ℝ} (ht : 2 ≤ t) :
    ∫ τ, Fn.phiHat (τ - t) ^ 2 * |Zeta23.PiX p.X τ|
      ≤ 6 * Real.sqrt p.X / t * (2 * π * Fn.a * p.L)
        + 12 * Real.sqrt p.X / t ^ 2 * (8 + 2 * (cϱ / p.w) ^ 2) := by
  have htr : (∫ τ, Fn.phiHat (τ - t) ^ 2 * |Zeta23.PiX p.X τ|)
      = ∫ r, Fn.phiHat r ^ 2 * |Zeta23.PiX p.X (t + r)| := by
    rw [← integral_add_right_eq_self (fun τ => Fn.phiHat (τ - t) ^ 2 * |Zeta23.PiX p.X τ|) t]
    congr 1; funext r
    rw [show r + t - t = r by ring, add_comm r t]
  rw [htr]
  have hgi : Integrable (fun r => (6 * Real.sqrt p.X / t) * Fn.phiHat r ^ 2
      + (12 * Real.sqrt p.X / t ^ 2) * (Fn.phiHat r ^ 2 * r ^ 2)) :=
    (hF.phiHat_sq_integrable.const_mul _).add (hF.phiHat_sq_mul_sq_integrable.const_mul _)
  calc ∫ r, Fn.phiHat r ^ 2 * |Zeta23.PiX p.X (t + r)|
      ≤ ∫ r, (6 * Real.sqrt p.X / t) * Fn.phiHat r ^ 2
          + (12 * Real.sqrt p.X / t ^ 2) * (Fn.phiHat r ^ 2 * r ^ 2) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun r => by positivity) hgi
          (Eventually.of_forall fun r => ?_)
        calc Fn.phiHat r ^ 2 * |Zeta23.PiX p.X (t + r)|
            ≤ Fn.phiHat r ^ 2 * (6 * Real.sqrt p.X / t + 12 * Real.sqrt p.X * r ^ 2 / t ^ 2) := by
              gcongr; exact PiX_shift_bound hF ht r
          _ = _ := by ring
    _ = (6 * Real.sqrt p.X / t) * (2 * π * Fn.a * p.L)
          + (12 * Real.sqrt p.X / t ^ 2) * ∫ r, Fn.phiHat r ^ 2 * r ^ 2 := by
        rw [integral_add (hF.phiHat_sq_integrable.const_mul _)
          (hF.phiHat_sq_mul_sq_integrable.const_mul _), integral_const_mul, integral_const_mul,
          hF.phiHat_sq_integral]
    _ ≤ _ := by
        have ht0 : 0 < t := by linarith
        gcongr
        exact hF.integral_phiHat_sq_mul_sq_le

/-- the Π-part Gram entry is bounded by the same quantity, for τ_k, τ_l ≥ t ≥ 2 (2|ab| ≤ a² + b²). -/
lemma abs_gentryNu_PiX_le (hF : LocalHypsCore cϱ p Fn) {t : ℝ} (ht : 2 ≤ t) {k l : ℤ}
    (hk : t ≤ p.tau k) (hl : t ≤ p.tau l) :
    |GentryNu (Zeta23.PiX p.X) p Fn k l|
      ≤ 6 * Real.sqrt p.X / t * (2 * π * Fn.a * p.L)
        + 12 * Real.sqrt p.X / t ^ 2 * (8 + 2 * (cϱ / p.w) ^ 2) := by
  set B : ℝ → ℝ := fun s => 6 * Real.sqrt p.X / s * (2 * π * Fn.a * p.L)
    + 12 * Real.sqrt p.X / s ^ 2 * (8 + 2 * (cϱ / p.w) ^ 2) with hB
  have ht0 : 0 < t := by linarith
  have ha0 : 0 ≤ Fn.a := by
    have h := hF.phiHat_sq_integral
    have hi : 0 ≤ ∫ r, Fn.phiHat r ^ 2 := integral_nonneg fun r => sq_nonneg _
    have hL := hF.L_pos
    nlinarith [Real.pi_pos, mul_pos Real.pi_pos hL]
  -- B is antitone in s ≥ t > 0
  have hLp := hF.L_pos
  have hBmono : ∀ s, t ≤ s → B s ≤ B t := by
    intro s hs
    have hs0 : 0 < s := by linarith
    have : 0 ≤ 2 * π * Fn.a * p.L := by positivity
    simp only [hB]
    gcongr
  -- the two diagonal-type integrals
  have hIk := (integral_phiHat_sq_abs_PiX_le hF (ht.trans hk)).trans (hBmono _ hk)
  have hIl := (integral_phiHat_sq_abs_PiX_le hF (ht.trans hl)).trans (hBmono _ hl)
  -- integrability of the majorant
  have hint : ∀ s : ℝ, Integrable (fun τ => Fn.phiHat (τ - s) ^ 2 * |Zeta23.PiX p.X τ|) := by
    intro s
    have h := (Pi_part_integrable hF s).norm.comp_sub_right s
    refine h.congr (Eventually.of_forall fun τ => ?_)
    simp [Real.norm_eq_abs, add_sub_cancel]
  unfold GentryNu
  rw [← Real.norm_eq_abs]
  calc ‖∫ τ, Fn.phiHat (τ - p.tau k) * Fn.phiHat (τ - p.tau l) * Zeta23.PiX p.X τ‖
      ≤ ∫ τ, ‖Fn.phiHat (τ - p.tau k) * Fn.phiHat (τ - p.tau l) * Zeta23.PiX p.X τ‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ τ, (Fn.phiHat (τ - p.tau k) ^ 2 * |Zeta23.PiX p.X τ|
          + Fn.phiHat (τ - p.tau l) ^ 2 * |Zeta23.PiX p.X τ|) / 2 := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun τ => norm_nonneg _)
          (((hint _).add (hint _)).div_const 2) (Eventually.of_forall fun τ => ?_)
        simp only [Real.norm_eq_abs, abs_mul]
        set a := Fn.phiHat (τ - p.tau k)
        set b := Fn.phiHat (τ - p.tau l)
        have hab : |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
          nlinarith [sq_abs a, sq_abs b, sq_nonneg (|a| - |b|)]
        have hv := abs_nonneg (Zeta23.PiX p.X τ)
        calc |a| * |b| * |Zeta23.PiX p.X τ| ≤ (a ^ 2 + b ^ 2) / 2 * |Zeta23.PiX p.X τ| :=
              mul_le_mul_of_nonneg_right hab hv
          _ = _ := by ring
    _ = ((∫ τ, Fn.phiHat (τ - p.tau k) ^ 2 * |Zeta23.PiX p.X τ|)
          + ∫ τ, Fn.phiHat (τ - p.tau l) ^ 2 * |Zeta23.PiX p.X τ|) / 2 := by
        rw [integral_div, integral_add (hint _) (hint _)]
    _ ≤ (B t + B t) / 2 := by gcongr
    _ = B t := by ring

end PiPart

/-! ### The three HatNegligible pieces and the main W theorem -/

/-- **M^𝒵 − M^{c,2} is HatNegligible** ([XF′ 6.1] at the real base ½l). -/
theorem hatNegligible_entryDependenceW (Z : ZeroConfig) (Pf : ℝ → Params) (F : CoeffFamily)
    (P : Params) (hP : P.Valid) (hlam1 : P.lam < 1) (hPf : ∀ T, (Pf T).lam = P.lam ∧ (Pf T).w = P.w)
    {cϱ : ℝ} (hcore : ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T → LocalHypsCore cϱ ((Pf T).toSetting T) ((Pf T).localFun T))
    (hΓ : GammaFacts)
    (ha : ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ᶠ T in atTop, a₀ ≤ (Pf T).a T)
    (hR : RiemannVonMangoldt Z)
    {e : ℝ → ℕ → ℕ → ℂ} {ρ₀ A T₀ : ℝ} (hρ₀ : 0 ≤ ρ₀) (hA : 0 ≤ A)
    (hG : ReexpansionGeom Pf L2T F.c e ρ₀ A T₀) :
    HatNegligible Z Pf (fun T => (Pf T).GpW1 T - (Pf T).GpCW T 2 (F.c T)) := by
  refine hatNegligible_of_geom Z Pf P hP hlam1 hPf hcore ha hR hρ₀ hA hG _ (fun T hT hF => ?_)
  have hLf : (Pf T).L T = P.L T := fam_L hPf T
  have hL0 : 0 < (Pf T).L T := by
    rw [hLf]; unfold Params.L
    have : 1 ≤ l T := by
      have h := hF.one_le_l; simpa using h
    nlinarith [hP.lam_pos]
  have hh0 : 0 ≤ (Pf T).hgrid T := by unfold Params.hgrid; positivity
  have hX0 : 0 < (Pf T).X T := by unfold Params.X; exact Real.exp_pos _
  ext k l'
  rw [GpW1_sub_GpCW_apply (Pf T) T hΓ hF hX0 hT hh0 (F.c T) k l',
    L2star_eq_L2T_add T hT (tauStar_pos (Pf T) T hT hh0)]
  rfl

set_option maxHeartbeats 400000 in
/-- **the Π-part matrix M^{c,2} − M^{c,1} is HatNegligible** ([XF′ §9.3(i)]). -/
theorem hatNegligible_piPart (Z : ZeroConfig) (Pf : ℝ → Params) (c : ℝ → ℕ → ℂ)
    (P : Params) (hP : P.Valid) (hPf : ∀ T, (Pf T).lam = P.lam ∧ (Pf T).w = P.w)
    {cϱ : ℝ} (hcore : ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T → LocalHypsCore cϱ ((Pf T).toSetting T) ((Pf T).localFun T))
    (hΓ : GammaFacts)
    (ha : ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ᶠ T in atTop, a₀ ≤ (Pf T).a T)
    (hR : RiemannVonMangoldt Z) :
    HatNegligible Z Pf (fun T => (Pf T).GpCW T 2 (c T) - (Pf T).GpC T (c T)) := by
  obtain ⟨T₁, hcore⟩ := hcore
  obtain ⟨a₀, ha₀, ha⟩ := ha
  intro η hη
  have hπ := Real.pi_pos
  set K : ℝ := 8 + 2 * (cϱ / P.w) ^ 2 with hK
  have hK0 : 0 < K := by positivity
  -- the two constants: |tr D̂| ≤ κ₁ √X,  frobSq D̂ ≤ κ₂² X
  set κ₁ : ℝ := 6 + 12 * K / (2 * π * a₀) with hκ₁
  set κ₂ : ℝ := 6 + 12 * K / (2 * π * a₀) with hκ₂
  have hκ0 : 0 < κ₁ := by positivity
  have hLtop := Assembly.tendsto_L_atTop P hP.lam_pos
  filter_upwards [eventually_ge_atTop T₁, eventually_ge_atTop (2:ℝ), ha, Assembly.eventually_N_ge Z hR,
    Assembly.eventually_one_le_l, hLtop.eventually_ge_atTop 1,
    eventually_ge_atTop ((4 * π * κ₁ / η) ^ 2),
    Assembly.tendsto_l_atTop.eventually_ge_atTop (4 * π * κ₂ ^ 2 / η ^ 2)]
    with T hT₁ hT2 haT hN hl1 hL1 hTbig hlbig
  set P' := Pf T with hP'
  set p := P'.toSetting T with hp
  set Fn := P'.localFun T with hFn
  have hF : LocalHypsCore cϱ p Fn := hcore T hT₁
  have hT : 0 < T := by linarith
  have hLf : P'.L T = P.L T := fam_L hPf T
  have hXf : P'.X T = P.X T := fam_X hPf T
  have hwf : P'.w = P.w := (hPf T).2
  have hL0 : 0 < P.L T := by linarith
  have hh0 : 0 ≤ P'.hgrid T := by unfold Params.hgrid; rw [hLf]; positivity
  have hX0 : 0 < P.X T := by unfold Params.X; exact Real.exp_pos _
  have hXT : P.X T ≤ T := by
    have h1 : P.X T ≤ Real.exp (l T) := by
      unfold Params.X Params.L
      exact Real.exp_le_exp.2 (by nlinarith [hP.lam_le_one])
    rw [l, Real.exp_log (by positivity)] at h1
    have : T / (2 * π) ≤ T := div_le_self hT.le (by linarith [Real.pi_gt_three])
    linarith
  have haT0 : 0 < P'.a T := ha₀.trans_le haT
  have haL : 0 < P'.a T * P'.L T ^ 2 := by rw [hLf]; positivity
  -- entry bound (in the abstract scalars p.X = X, p.L = L, Fn.a = a, p.w = w)
  have eX : p.X = P.X T := hXf
  have eL : p.L = P.L T := hLf
  have ew : p.w = P.w := hwf
  set Bπ : ℝ := 6 * Real.sqrt p.X / T * (2 * π * Fn.a * p.L)
    + 12 * Real.sqrt p.X / T ^ 2 * (8 + 2 * (cϱ / p.w) ^ 2) with hBπ
  have hBπ0 : 0 ≤ Bπ := by
    have : 0 ≤ Fn.a := haT0.le
    have : 0 < p.L := by rw [eL]; exact hL0
    positivity
  have hentry : ∀ k l' : Fin (P'.d T), ‖(P'.GpCW T 2 (c T) - P'.GpC T (c T)) k l'‖ ≤ Bπ := by
    intro k l'
    rw [GpCW_two_sub_GpC_apply P' T hΓ hF (by rw [hXf]; exact hX0) hT hh0 (c T) k l',
      Complex.norm_real, Real.norm_eq_abs]
    have hk : T ≤ p.tau k := tau_ge_T P' T hh0
    have hl : T ≤ p.tau l' := tau_ge_T P' T hh0
    exact abs_gentryNu_PiX_le hF hT2 hk hl
  have hBπ_eval : (P'.a T * P'.L T ^ 2)⁻¹ * ((P.L T * T / (2 * π)) * Bπ)
      = 6 * Real.sqrt (P.X T) + 12 * K * Real.sqrt (P.X T) / (2 * π * P'.a T * (P.L T * T)) := by
    rw [hBπ, eX, eL, ew, ← hK, hLf]
    have : Fn.a = P'.a T := rfl
    rw [this]
    field_simp
  constructor
  · -- trace: (aL²)⁻¹ · d · Bπ ≤ κ₁ √X ≤ η N
    rw [rtrace_hat', abs_mul, abs_of_pos (inv_pos.2 haL)]
    have htr : |rtrace (P'.GpCW T 2 (c T) - P'.GpC T (c T))| ≤ (P'.d T : ℝ) * Bπ := by
      refine (Transfer.abs_rtrace_le_sum_norm_diag _).trans ?_
      calc ∑ k : Fin (P'.d T), ‖(P'.GpCW T 2 (c T) - P'.GpC T (c T)) k k‖
          ≤ ∑ _k : Fin (P'.d T), Bπ := Finset.sum_le_sum fun k _ => hentry k k
        _ = (P'.d T : ℝ) * Bπ := by simp
    have hdle : (P'.d T : ℝ) ≤ P.L T * T / (2 * π) := by
      have := d_le P' T (by rw [hLf]; positivity); rwa [hLf] at this
    have hsqT : 4 * π * κ₁ / η ≤ Real.sqrt T := by
      calc 4 * π * κ₁ / η = Real.sqrt ((4 * π * κ₁ / η) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt T := Real.sqrt_le_sqrt hTbig
    calc (P'.a T * P'.L T ^ 2)⁻¹ * |rtrace (P'.GpCW T 2 (c T) - P'.GpC T (c T))|
        ≤ (P'.a T * P'.L T ^ 2)⁻¹ * ((P.L T * T / (2 * π)) * Bπ) := by
          refine mul_le_mul_of_nonneg_left (htr.trans ?_) (inv_nonneg.2 haL.le)
          exact mul_le_mul_of_nonneg_right hdle hBπ0
      _ = 6 * Real.sqrt (P.X T) + 12 * K * Real.sqrt (P.X T) / (2 * π * P'.a T * (P.L T * T)) := hBπ_eval
      _ ≤ 6 * Real.sqrt (P.X T) + 12 * K * Real.sqrt (P.X T) / (2 * π * a₀ * (1 * 1)) := by
          gcongr
          · linarith
      _ = κ₁ * Real.sqrt (P.X T) := by rw [hκ₁]; ring
      _ ≤ κ₁ * Real.sqrt T := by gcongr
      _ = η / (4 * π) * (4 * π * κ₁ / η) * Real.sqrt T := by field_simp
      _ ≤ η / (4 * π) * Real.sqrt T * Real.sqrt T := by gcongr
      _ = η * (T / (4 * π)) := by rw [mul_assoc, Real.mul_self_sqrt hT.le]; ring
      _ ≤ η * (T * l T / (4 * π)) := by
          gcongr; exact le_mul_of_one_le_right hT.le hl1
      _ ≤ η * (Z.N T (2 * T) : ℝ) := by gcongr
  · -- Frobenius: (aL²)⁻² d² Bπ² ≤ κ₂² X ≤ η² N
    rw [frobSq_hat']
    have hfr : frobSq (P'.GpCW T 2 (c T) - P'.GpC T (c T)) ≤ (P'.d T : ℝ) ^ 2 * Bπ ^ 2 := by
      refine (Transfer.frobSq_le_of_norm_le _ (fun _ _ => Bπ) hentry).trans ?_
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact le_of_eq (by ring)
    have hdle : (P'.d T : ℝ) ≤ P.L T * T / (2 * π) := by
      have := d_le P' T (by rw [hLf]; positivity); rwa [hLf] at this
    have hd0 : (0:ℝ) ≤ (P'.d T : ℝ) := Nat.cast_nonneg _
    have key : (P'.a T * P'.L T ^ 2)⁻¹ * ((P'.d T : ℝ) * Bπ) ≤ κ₂ * Real.sqrt (P.X T) := by
      calc (P'.a T * P'.L T ^ 2)⁻¹ * ((P'.d T : ℝ) * Bπ)
          ≤ (P'.a T * P'.L T ^ 2)⁻¹ * ((P.L T * T / (2 * π)) * Bπ) := by
            refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 haL.le)
            exact mul_le_mul_of_nonneg_right hdle hBπ0
        _ = 6 * Real.sqrt (P.X T) + 12 * K * Real.sqrt (P.X T) / (2 * π * P'.a T * (P.L T * T)) := hBπ_eval
        _ ≤ 6 * Real.sqrt (P.X T) + 12 * K * Real.sqrt (P.X T) / (2 * π * a₀ * (1 * 1)) := by
            gcongr
            · linarith
        _ = κ₂ * Real.sqrt (P.X T) := by rw [hκ₂]; ring
    have key0 : 0 ≤ (P'.a T * P'.L T ^ 2)⁻¹ * ((P'.d T : ℝ) * Bπ) := by positivity
    calc ((P'.a T * P'.L T ^ 2)⁻¹) ^ 2 * frobSq (P'.GpCW T 2 (c T) - P'.GpC T (c T))
        ≤ ((P'.a T * P'.L T ^ 2)⁻¹) ^ 2 * ((P'.d T : ℝ) ^ 2 * Bπ ^ 2) :=
          mul_le_mul_of_nonneg_left hfr (sq_nonneg _)
      _ = ((P'.a T * P'.L T ^ 2)⁻¹ * ((P'.d T : ℝ) * Bπ)) ^ 2 := by ring
      _ ≤ (κ₂ * Real.sqrt (P.X T)) ^ 2 := pow_le_pow_left₀ key0 key 2
      _ = κ₂ ^ 2 * P.X T := by rw [mul_pow, Real.sq_sqrt hX0.le]
      _ ≤ κ₂ ^ 2 * T := by gcongr
      _ = η ^ 2 / (4 * π) * (4 * π * κ₂ ^ 2 / η ^ 2) * T := by field_simp
      _ ≤ η ^ 2 / (4 * π) * l T * T := by gcongr
      _ = η ^ 2 * (T * l T / (4 * π)) := by ring
      _ ≤ η ^ 2 * (Z.N T (2 * T) : ℝ) := by gcongr

/-- XiTraceTransfer Z Pf F from the W explicit formula WEF (main term M^𝒵, pole weight 2,
real base) + the Z′ re-expansion + the PP bound.  Instantiate at Z := wZeros hZ hs, F := wCoeffFamily. -/
theorem wTraceTransfer_of (Z : ZeroConfig) (Pf : ℝ → Params) (F : CoeffFamily)
    (P : Params) (hP : P.Valid) (hlam1 : P.lam < 1) (hPf : ∀ T, (Pf T).lam = P.lam ∧ (Pf T).w = P.w)
    {cϱ : ℝ} (hcore : ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T → LocalHypsCore cϱ ((Pf T).toSetting T) ((Pf T).localFun T))
    (hΓ : GammaFacts)
    (ha : ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ᶠ T in atTop, a₀ ≤ (Pf T).a T)
    (hR : RiemannVonMangoldt Z) (hEF : WEF Z Pf)
    {e : ℝ → ℕ → ℕ → ℂ} {ρ₀ A T₀ : ℝ} (hρ₀ : 0 ≤ ρ₀) (hE : ReexpansionW F e ρ₀ A T₀)
    (hPP : PPUpper cϱ P.lam) :
    XiTraceTransfer Z Pf F := by
  obtain ⟨A', T₀', hA', hG⟩ := reexpansionGeom_of Pf P hP hPf hcore hρ₀ hE.toAt hPP
  have h1 : HatNegligible Z Pf (fun T => Z.Gz (Pf T) T - (Pf T).GpW1 T) := by
    obtain ⟨C, δ, T₀, hδ, h⟩ := hEF
    exact hatNegligible_of_entryBound Z Pf P hP hPf ha hR (fun T => (Pf T).GpW1 T)
      ⟨C, δ, T₀, hδ, fun T hT k l => (h T hT k l).2⟩
  have h2 := hatNegligible_entryDependenceW Z Pf F P hP hlam1 hPf hcore hΓ ha hR hρ₀ hA' hG
  have h3 := hatNegligible_piPart Z Pf F.c P hP hPf hcore hΓ ha hR
  refine xiTraceTransfer_of_negligible₁ Z Pf F (((h1.add h2).add h3).congr fun T => ?_)
  abel

end XiPrime
end Zeta23
