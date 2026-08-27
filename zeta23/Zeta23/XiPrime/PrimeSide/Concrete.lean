/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization.

Zeta23/XiPrime/PrimeSide/Concrete.lean — ξ′ component, generalised-coefficient prime side: the
CONCRETE FactsXi instance.

Inputs:  P : Params with P.Valid and λ < 1;  an ADMISSIBLE WINDOW FAMILY win T (Zeta23.AdmWindow
at scale (P.L T, P.w), b ≥ 1/2 — the flat taper and the quartic window are instances, produced by
XiPrime/Window.lean);  a COEFFICIENT FAMILY with CoeffFamily.Hyps (XiPrime/Statement.lean §3;
XiPrime/Coeff.lean proves it for C(N; L_T), D₁);  the pole weight cΠ (1 for ξ′, 2 for Z′);  any
count Ncnt with Ncnt = Tℓ₁/2π + O(l);  H-Γ;  H-MV;  and [prop:PP] for P_c as the named input
'PPInput' (discharged by Zeta23/XiPrime/PrimeSide/PP.lean).
Output: FactsXi for the concrete data, hence (Traces.lean) TracesBoundsXi and the δ-form moments.
-/
import Zeta23.XiPrime.Statement
import Zeta23.XiPrime.PrimeSide.Traces
import Zeta23.XiPrime.PrimeSide.Density
import Zeta23.XiPrime.PrimeSide.Cross
import Zeta23.XiPrime.PrimeSide.Trace
import Zeta23.XiPrime.PrimeSide.Abel
import Zeta23.ThmD.WindowLocalHyps
import Zeta23.ThmD.Window
import Zeta23.PrimeSideB.Concrete

noncomputable section

open Real Filter Topology MeasureTheory Set
open scoped BigOperators

namespace Zeta23
namespace XiPrime

open PrimeSide PaperParams

/-! ## Named coefficient sums and the [prop:PP] input -/

/-- the diagonal `Σ_{N≤X} ‖c_N‖²/N · g(log N)` -/
def sumW2g (c : ℕ → ℂ) (X : ℝ) (g : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ‖c n‖ ^ 2 / n * g (Real.log n)

/-- `Σ_{N≤X} ‖c_N‖²/N` -/
def sumSqDivW (c : ℕ → ℂ) (X : ℝ) : ℝ := ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ‖c n‖ ^ 2 / n

/-- `Σ_{N≤X} ‖c_N‖²` -/
def sumSqW (c : ℕ → ℂ) (X : ℝ) : ℝ := ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ‖c n‖ ^ 2

lemma sumSqDivW_nonneg (c : ℕ → ℂ) (X : ℝ) : 0 ≤ sumSqDivW c X :=
  Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
lemma sumSqW_nonneg (c : ℕ → ℂ) (X : ℝ) : 0 ≤ sumSqW c X :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **[prop:PP] for P_c as a named input** (the 𝒟/𝒪₁/𝒪₂ split + Montgomery–Vaughan for a
Dirichlet polynomial with arbitrary coefficients; proved in Zeta23/XiPrime/PrimeSide/PP.lean):
for every H-MV constant `C` and taper class `cϱ` there is `K` with, for all (p, F) under LocalHypsCore,
`T ≥ 1`, and all `c` with `c 1 = 0`:
`|𝓜[P_c,P_c] − (T/π)·Σ‖c_N‖²/N·g(log N)| ≤ K·L·(Σ‖c‖²/N + Σ‖c‖² + S₁(c)²)`. -/
def PPInput : Prop :=
  ∀ (C cϱ : ℝ), Zeta23.MVHilbert C → 0 < C → ∃ K : ℝ, ∀ (p : Setting) (F : LocalFun) (c : ℕ → ℂ),
    LocalHypsCore cϱ p F → 1 ≤ p.T → c 1 = 0 →
    |Mform F.Phi p.T (Pc p.X c) (Pc p.X c) - p.T / π * sumW2g c p.X F.g|
      ≤ K * p.L * (sumSqDivW c p.X + sumSqW c p.X + S1 c p.X ^ 2)

/-! ## The concrete data -/

/-- an admissible window family at scale `(P.L T, P.w)` with `b ≥ 1/2`, eventually in `T`. -/
def AdmFamily (P : Params) (win : ℝ → ℝ → ℝ) (cW : ℝ) : Prop :=
  ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    AdmWindow (win T) (P.L T) P.w cW ∧ 1 / 2 ≤ AdmWindow.bv (win T) (P.L T)

section Data
variable (P : Params) (win : ℝ → ℝ → ℝ) (Fam : CoeffFamily) (cPi : ℝ) (Ncnt : ℝ → ℝ)

/-- taper data of the window at height `T`. -/
abbrev Fw (T : ℝ) : LocalFun := AdmWindow.localFun (win T) (P.L T)

/-- the concrete ξ′ prime-side data for (P, window family, coefficient family, pole weight). -/
def concreteData : DataXi P where
  aT := fun T => AdmWindow.av (win T) (P.L T)
  bT := fun T => AdmWindow.bv (win T) (P.L T)
  JT := fun T => JD Fam.D (AdmWindow.gv (win T)) (P.L T) (l T)
  trG := fun T => trGtW cPi (Fam.c T) (P.toSetting T) (Fw P win T)
  trG2 := fun T => trGt2W cPi (Fam.c T) (P.toSetting T) (Fw P win T)
  Ncnt := Ncnt
  Mtot := fun T => MtotalW cPi (Fam.c T) (P.toSetting T) (Fw P win T)
  Mmumu := fun T => Mform (Fw P win T).Phi T Zeta23.mu Zeta23.mu
  MPP := fun T => Mform (Fw P win T).Phi T (Pc (P.X T) (Fam.c T)) (Pc (P.X T) (Fam.c T))
  MmuP := fun T => Mform (Fw P win T).Phi T Zeta23.mu (Pc (P.X T) (Fam.c T))
  MmuPi := fun T => cPi * Mform (Fw P win T).Phi T Zeta23.mu (Zeta23.PiX (P.X T))
  MPPi := fun T => cPi * Mform (Fw P win T).Phi T (Pc (P.X T) (Fam.c T)) (Zeta23.PiX (P.X T))
  MPiPi := fun T => cPi ^ 2 * Mform (Fw P win T).Phi T (Zeta23.PiX (P.X T)) (Zeta23.PiX (P.X T))
  intMu2 := fun T => ∫ τ in T..(2 * T), Zeta23.mu τ ^ 2
  sumB2g := fun T => sumW2g (Fam.c T) (P.X T) (AdmWindow.gv (win T))

end Data

/-! ## Eventual facts: regime, taper hypotheses, coefficient sizes -/

section Facts
variable {P : Params} {win : ℝ → ℝ → ℝ} {Fam : CoeffFamily} {cPi cW : ℝ} {Ncnt : ℝ → ℝ}

lemma regime_eventually (hP : P.Valid) : ∀ᶠ T in atTop,
    1 ≤ T ∧ 1 ≤ l T ∧ 1 ≤ Real.log (l T) ∧ 1 ≤ P.L T ∧ 2 ≤ P.X T ∧ P.L T ≤ l T
      ∧ P.X T ≤ Real.exp (l T) := by
  have hlam := hP.lam_pos
  filter_upwards [eventually_ge_atTop 1, eventually_l_ge 1, eventually_log_l_ge 1,
    eventually_L_ge P hlam 1] with T h1 h2 h3 h4
  have hLl : P.L T ≤ l T := L_le_l P hP.lam_le_one (by linarith)
  refine ⟨h1, h2, h3, h4, ?_, hLl, ?_⟩
  · have : Real.exp 1 ≤ P.X T := Real.exp_le_exp.2 h4
    have he : (2:ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1:ℝ); linarith
    linarith
  · exact Real.exp_le_exp.2 hLl

/-- the taper hypotheses of §5 for the window family, eventually. -/
lemma localHypsCore_eventually (hP : P.Valid) (hwin : AdmFamily P win cW) :
    ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T → LocalHypsCore cW (P.toSetting T) (Fw P win T) := by
  obtain ⟨T₀, hT₀⟩ := hwin
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.1 (regime_eventually hP)
  refine ⟨max T₀ T₂, fun T hT => ?_⟩
  obtain ⟨hW, hb⟩ := hT₀ T ((le_max_left _ _).trans hT)
  obtain ⟨-, hl, -, -, hX, -, -⟩ := hT₂ T ((le_max_right _ _).trans hT)
  exact AdmWindow.localHypsCore (P.toSetting T) hW hP.lam_pos hP.lam_le_one hl
    (by show 1 ≤ P.X T; linarith) hb

/-- S₁ ≤ C₁ √X · l at x = X, eventually (from H1). -/
lemma S1_eventually (hP : P.Valid) (hF : Fam.Hyps) : ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ᶠ T in atTop,
    S1 (Fam.c T) (P.X T) ≤ C₁ * Real.sqrt (P.X T) * l T := by
  obtain ⟨C, T₀, hC⟩ := hF.H1
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  filter_upwards [regime_eventually hP, eventually_ge_atTop T₀] with T ⟨ _, hl, _, _, hX2, _, hXe⟩ hT
  refine (hC T hT (P.X T) hX2 hXe).trans ?_
  have : 0 ≤ Real.sqrt (P.X T) * l T := by positivity
  nlinarith [le_max_left C 0]

/-- Σ‖c‖² ≤ C₂ X l² at x = X, eventually (from H2). -/
lemma sumSq_eventually (hP : P.Valid) (hF : Fam.Hyps) : ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ᶠ T in atTop,
    sumSqW (Fam.c T) (P.X T) ≤ C₂ * P.X T * l T ^ 2 := by
  obtain ⟨C, T₀, hC⟩ := hF.H2
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  filter_upwards [regime_eventually hP, eventually_ge_atTop T₀] with T ⟨ _, hl, _, _, hX2, _, hXe⟩ hT
  refine (hC T hT (P.X T) hX2 hXe).trans ?_
  have : 0 ≤ P.X T * l T ^ 2 := by positivity
  nlinarith [le_max_left C 0]

/-- a bound for the density on [0,1]. -/
lemma D_bound (hF : Fam.Hyps) : ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Icc (0:ℝ) 1, |Fam.D s| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hF.D_cont.continuousOn (s := Icc 0 1))
  exact ⟨max M 0, le_max_right _ _, fun s hs => (Real.norm_eq_abs _ ▸ hM s hs).trans (le_max_left _ _)⟩

/-- Σ‖c‖²/N ≤ C₃ l² at x = X, eventually (from H3 with ε = 1 and the boundedness of D). -/
lemma sumSqDiv_eventually (hP : P.Valid) (hF : Fam.Hyps) : ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ᶠ T in atTop,
    sumSqDivW (Fam.c T) (P.X T) ≤ C₃ * l T ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := D_bound hF
  obtain ⟨T₀, hT₀⟩ := hF.H3 1 one_pos
  refine ⟨M + 1, by positivity, ?_⟩
  filter_upwards [regime_eventually hP, eventually_ge_atTop T₀] with T ⟨ _, hl, _, hL, _, hLl, _⟩ hT
  have hl0 : 0 < l T := by linarith
  have h := hT₀ T hT (P.L T) (by linarith) hLl
  have hX : Real.exp (P.L T) = P.X T := rfl
  rw [hX] at h
  have hI : |∫ s in (0:ℝ)..(P.L T / l T), Fam.D s| ≤ M := by
    have hq1 : P.L T / l T ≤ 1 := by rw [div_le_one hl0]; exact hLl
    have hq0 : 0 ≤ P.L T / l T := by positivity
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := P.L T / l T)
      (f := Fam.D) (C := M) (fun x hx => by
        rw [Set.uIoc_of_le hq0] at hx
        rw [Real.norm_eq_abs]; exact hM x ⟨hx.1.le, hx.2.trans hq1⟩)
    rw [Real.norm_eq_abs] at h1
    refine h1.trans ?_
    rw [sub_zero, abs_of_nonneg hq0]
    nlinarith
  have h2 := (abs_le.1 h).2
  have h3 := (abs_le.1 hI).2
  show ∑ n ∈ Finset.Ioc 0 ⌊P.X T⌋₊, ‖Fam.c T n‖ ^ 2 / n ≤ (M + 1) * l T ^ 2
  nlinarith [sq_nonneg (l T)]

/-- C¹ facts for the window moment `g = v² ⋆ v²` of an admissible window. -/
lemma gv_deriv_facts {v : ℝ → ℝ} {L w c : ℝ} (hW : AdmWindow v L w c) :
    Differentiable ℝ (AdmWindow.gv v) ∧ Continuous (deriv (AdmWindow.gv v))
      ∧ ∀ y : ℝ, |deriv (AdmWindow.gv v) y| ≤ 2 := by
  apply ThmD.autocorr_deriv_facts
  · exact (hW.contDiff.pow 2).of_le (by norm_num)
  · exact hW.sq_hasCompactSupport
  · intro x; exact hW.sq_even x
  · intro u
    rw [abs_of_nonneg (sq_nonneg _)]
    calc v u ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (hW.nonneg u) (hW.le_one u) 2
      _ = 1 := one_pow 2
  · exact hW.l1_deriv_sq

/-! ## The concrete FactsXi -/

/-- generic bridge: an EventuallyAtCore-type bound, specialised to the window family, is an
eventual pointwise bound in T. -/
lemma eventually_of_core {T₁ : ℝ} (hT₁ : ∀ T : ℝ, T₁ ≤ T → LocalHypsCore cW (P.toSetting T) (Fw P win T))
    {Q : Setting → LocalFun → Prop} {T₀ : ℝ}
    (h : ∀ (p : Setting) (F : LocalFun), p.lam = P.lam → T₀ ≤ p.T → LocalHypsCore cW p F → Q p F) :
    ∀ᶠ T in atTop, Q (P.toSetting T) (Fw P win T) := by
  filter_upwards [eventually_ge_atTop (max T₀ T₁)] with T hT
  exact h _ _ rfl ((le_max_left _ _).trans hT) (hT₁ T ((le_max_right _ _).trans hT))

set_option maxHeartbeats 3200000 in
/-- **FactsXi for the concrete data.** -/
theorem concreteFacts (hP : P.Valid) (hlam1 : P.lam < 1) (hwin : AdmFamily P win cW)
    (hF : Fam.Hyps) (hΓ : Zeta23.GammaFacts) (hMV : ∃ C : ℝ, 0 < C ∧ Zeta23.MVHilbert C)
    (hPP : PPInput) (hN : EvBound (fun T => Ncnt T - T * ell1 T / (2 * π)) l) :
    FactsXi (concreteData P win Fam cPi Ncnt) := by
  have hlam : 0 < P.lam ∧ P.lam ≤ 1 := ⟨hP.lam_pos, hP.lam_le_one⟩
  have hcheb := Zeta23.Cheb.chebyshevMertens
  obtain ⟨T₁, hT₁⟩ := localHypsCore_eventually hP hwin
  obtain ⟨Tw, hTw⟩ := id hwin
  have hCore : ∀ᶠ T in atTop, LocalHypsCore cW (P.toSetting T) (Fw P win T) :=
    eventually_atTop.2 ⟨T₁, hT₁⟩
  have hAdm : ∀ᶠ T in atTop,
      AdmWindow (win T) (P.L T) P.w cW ∧ 1 / 2 ≤ AdmWindow.bv (win T) (P.L T) :=
    eventually_atTop.2 ⟨Tw, hTw⟩
  obtain ⟨C₁, hC₁0, hS1⟩ := S1_eventually hP hF
  obtain ⟨C₂, hC₂0, hS2⟩ := sumSq_eventually hP hF
  obtain ⟨C₃, hC₃0, hS3⟩ := sumSqDiv_eventually hP hF
  have hreg := regime_eventually hP
  have hc1 : ∀ T, Fam.c T 1 = 0 := hF.c_one
  have hS1nn : ∀ T, 0 ≤ S1 (Fam.c T) (P.X T) := fun T => S1_nonneg _ _
  refine
    { lam_pos := hP.lam_pos
      lam_lt_one := hlam1
      one_le_w := hP.one_le_w
      ab_range := ?ab
      rvm := hN
      muints2 := ?mu2
      prop_trace := ?tr
      lem_ends := ?ends
      Msplit := ?msplit
      prop_mumu := ?mumu
      prop_PP := ?pp
      sumJ := ?sumJ
      cross_muP := ?cmuP
      cross_muPi := ?cmuPi
      cross_PPi := ?cPPi
      cross_PiPi := ?cPiPi }
  case ab =>
    filter_upwards [hAdm, hreg] with T ⟨hW, hb⟩ ⟨_, hl, _, hL, _, hLl, _⟩
    refine ⟨hb, hW.bv_le_av, hW.av_le_one, ?_⟩
    show 0 ≤ 2 / P.L T ^ 3 * l T *
      ∫ y in (0:ℝ)..(P.L T), (Fam.D (y / l T) * AdmWindow.gv (win T) y)
    have hl0 : 0 < l T := by linarith
    refine mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg (by linarith) fun y hy => ?_)
    refine mul_nonneg (hF.D_nonneg _ ⟨div_nonneg hy.1 hl0.le, ?_⟩) (hW.gv_nonneg y)
    rw [div_le_one hl0]; exact hy.2.trans hLl
  case mu2 =>
    obtain ⟨C, T₂, hC⟩ := hΓ.int_mu_sq
    refine ⟨max C 1, by positivity, max T₂ 0, fun T hT =>
      (hC T ((le_max_left _ _).trans hT)).trans ?_⟩
    have hT0 : 0 ≤ T := (le_max_right _ _).trans hT
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
    exact div_nonneg (div_nonneg (mul_nonneg hT0 (sq_nonneg _)) (by positivity)) (sq_nonneg _)
  case tr =>
    obtain ⟨A, hA, hNA⟩ := hN.eventually_le
    obtain ⟨C, T₂, hC⟩ := prop_trace_W cW P.lam hΓ hlam cPi A
    refine EvBound.of_eventually_le (c := max C 0 * (1 + C₁) + 1) (by positivity) ?_
    filter_upwards [eventually_of_core hT₁ (Q := fun p F => ∀ c : ℕ → ℂ, c 1 = 0 → ∀ N : ℝ,
        |N - p.T * p.ell1 / (2 * π)| ≤ A * p.l →
        |trGtW cPi c p F - F.a * p.L * N| ≤ C * (p.L * Real.sqrt p.X + p.L * S1 c p.X))
        (fun p F hl hT hF' c => hC p F c hl hT hF'), hNA, hS1, hreg]
      with T h hNT hS1T ⟨hT1, hl, _, hL, hX2, hLl, _⟩
    have h' := h (Fam.c T) (hc1 T) (Ncnt T) hNT
    show |trGtW cPi (Fam.c T) (P.toSetting T) (Fw P win T)
        - AdmWindow.av (win T) (P.L T) * P.L T * Ncnt T|
      ≤ (max C 0 * (1 + C₁) + 1) * (P.L T * Real.sqrt (P.X T) * l T)
    refine h'.trans ?_
    have hsX : 0 ≤ Real.sqrt (P.X T) := Real.sqrt_nonneg _
    have hx : 0 ≤ P.L T * Real.sqrt (P.X T) + P.L T * S1 (Fam.c T) (P.X T) := by
      have := hS1nn T; positivity
    have hm : 0 ≤ max C 0 := le_max_right _ _
    calc C * (P.L T * Real.sqrt (P.X T) + P.L T * S1 (Fam.c T) (P.X T))
        ≤ max C 0 * (P.L T * Real.sqrt (P.X T) + P.L T * S1 (Fam.c T) (P.X T)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hx
      _ ≤ max C 0 * (P.L T * Real.sqrt (P.X T) + P.L T * (C₁ * Real.sqrt (P.X T) * l T)) := by
          gcongr
      _ = max C 0 * (1 + C₁ * l T) * (P.L T * Real.sqrt (P.X T)) := by ring
      _ ≤ (max C 0 * (1 + C₁) + 1) * (P.L T * Real.sqrt (P.X T) * l T) := by
          have h0 : 0 ≤ P.L T * Real.sqrt (P.X T) := by positivity
          nlinarith [mul_nonneg hm h0, mul_nonneg (mul_nonneg hm hC₁0) h0,
            mul_nonneg (mul_nonneg hm h0) (by linarith : (0:ℝ) ≤ l T - 1)]
  case ends =>
    obtain ⟨C, T₂, hC⟩ := lem_ends_W (cϱ := cW) hΓ hlam cPi
    set K := 2 * (6 + 3 * |cPi - 1| + C₁) ^ 2 with hK
    refine EvBound.of_eventually_le (c := max C 0 * K + 1) (by positivity) ?_
    filter_upwards [eventually_of_core hT₁ (Q := fun p F => ∀ c : ℕ → ℂ,
        |trGt2W cPi c p F - MtotalW cPi c p F| ≤ C * (p.L * p.l * Real.log p.l * BcW cPi c p ^ 2))
        (fun p F hl hT hF' c => hC p F c hl hT hF'), hS1, hreg]
      with T h hS1T ⟨hT1, hl, hlog, hL, hX2, hLl, _⟩
    have h' := h (Fam.c T)
    have hB : BcW cPi (Fam.c T) (P.toSetting T) ^ 2 ≤ K * (l T ^ 2 * (1 + P.X T)) := by
      rw [hK]
      exact BcW_sq_le (cPi := cPi) (c := Fam.c T) (p := P.toSetting T) hl
        (by show 1 ≤ P.X T; linarith) hC₁0 hS1T
    show |trGt2W cPi (Fam.c T) (P.toSetting T) (Fw P win T)
        - MtotalW cPi (Fam.c T) (P.toSetting T) (Fw P win T)| ≤ (max C 0 * K + 1) * Rxi P T
    refine h'.trans ?_
    have hR0 : 0 ≤ Rxi P T := by unfold Rxi; positivity
    have hx : 0 ≤ P.L T * l T * Real.log (l T) * BcW cPi (Fam.c T) (P.toSetting T) ^ 2 := by
      positivity
    calc C * (P.L T * l T * Real.log (l T) * BcW cPi (Fam.c T) (P.toSetting T) ^ 2)
        ≤ max C 0 * (P.L T * l T * Real.log (l T) * BcW cPi (Fam.c T) (P.toSetting T) ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hx
      _ ≤ max C 0 * (P.L T * l T * Real.log (l T) * (K * (l T ^ 2 * (1 + P.X T)))) := by
          gcongr
      _ = max C 0 * K * Rxi P T := by unfold Rxi; ring
      _ ≤ (max C 0 * K + 1) * Rxi P T := by nlinarith
  case msplit =>
    filter_upwards [hCore] with T hF'
    exact eq_Msplit_W hΓ cPi (Fam.c T) (P.toSetting T) (Fw P win T) hF'
  case mumu =>
    obtain ⟨C, T₂, hC⟩ := PrimeSide.prop_mumu cW P.lam hΓ hcheb hlam
    refine EvBound.of_eventually_le (c := max C 1) (by positivity) ?_
    filter_upwards [eventually_of_core hT₁ hC, hreg] with T h ⟨hT1, hl, hlog, hL, hX2, hLl, _⟩
    show |Mform (Fw P win T).Phi T Zeta23.mu Zeta23.mu
        - 2 * π * AdmWindow.bv (win T) (P.L T) * P.L T * ∫ τ in T..(2 * T), Zeta23.mu τ ^ 2|
      ≤ max C 1 * (l T ^ 2 * Real.log (P.L T))
    refine h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    exact mul_nonneg (sq_nonneg _) (Real.log_nonneg hL)
  case pp =>
    obtain ⟨CMV, hCMV, hMV'⟩ := hMV
    obtain ⟨K, hK⟩ := hPP CMV cW hMV' hCMV
    refine EvBound.of_eventually_le (c := max K 0 * (C₃ + C₂ + C₁ ^ 2) + 1) (by positivity) ?_
    filter_upwards [hCore, hS1, hS2, hS3, hreg] with T hF' hS1T hS2T hS3T ⟨hT1, hl, _, hL, hX2, _, _⟩
    have h := hK (P.toSetting T) (Fw P win T) (Fam.c T) hF' hT1 (hc1 T)
    show |Mform (Fw P win T).Phi T (Pc (P.X T) (Fam.c T)) (Pc (P.X T) (Fam.c T))
        - T / π * sumW2g (Fam.c T) (P.X T) (AdmWindow.gv (win T))|
      ≤ (max K 0 * (C₃ + C₂ + C₁ ^ 2) + 1) * (P.L T * l T ^ 2 * P.X T)
    refine h.trans ?_
    have hsum0 : 0 ≤ sumSqDivW (Fam.c T) (P.X T) + sumSqW (Fam.c T) (P.X T)
        + S1 (Fam.c T) (P.X T) ^ 2 := by
      have := sumSqDivW_nonneg (Fam.c T) (P.X T)
      have := sumSqW_nonneg (Fam.c T) (P.X T)
      positivity
    have hS1sq : S1 (Fam.c T) (P.X T) ^ 2 ≤ C₁ ^ 2 * P.X T * l T ^ 2 := by
      calc S1 (Fam.c T) (P.X T) ^ 2 ≤ (C₁ * Real.sqrt (P.X T) * l T) ^ 2 :=
            pow_le_pow_left₀ (hS1nn T) hS1T 2
        _ = C₁ ^ 2 * P.X T * l T ^ 2 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith)]
    have hm : 0 ≤ max K 0 := le_max_right _ _
    calc K * P.L T * (sumSqDivW (Fam.c T) (P.X T) + sumSqW (Fam.c T) (P.X T)
          + S1 (Fam.c T) (P.X T) ^ 2)
        ≤ max K 0 * P.L T * (sumSqDivW (Fam.c T) (P.X T) + sumSqW (Fam.c T) (P.X T)
          + S1 (Fam.c T) (P.X T) ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ hsum0
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
      _ ≤ max K 0 * P.L T * (C₃ * l T ^ 2 + C₂ * P.X T * l T ^ 2 + C₁ ^ 2 * P.X T * l T ^ 2) := by
          gcongr
      _ ≤ max K 0 * P.L T * (C₃ * P.X T * l T ^ 2 + C₂ * P.X T * l T ^ 2
          + C₁ ^ 2 * P.X T * l T ^ 2) := by
          gcongr
          nlinarith [sq_nonneg (l T), mul_nonneg hC₃0 (sq_nonneg (l T))]
      _ = max K 0 * (C₃ + C₂ + C₁ ^ 2) * (P.L T * l T ^ 2 * P.X T) := by ring
      _ ≤ (max K 0 * (C₃ + C₂ + C₁ ^ 2) + 1) * (P.L T * l T ^ 2 * P.X T) := by
          have : 0 ≤ P.L T * l T ^ 2 * P.X T := by positivity
          nlinarith
  case sumJ =>
    intro ε hε
    obtain ⟨T₀, hT₀⟩ := hF.H3 (ε / 2) (by positivity)
    filter_upwards [hAdm, hreg, eventually_ge_atTop T₀] with T ⟨hW, hb⟩ ⟨hT1, hl, _, hL, hX2, hLl, _⟩ hT
    have hl0 : 0 < l T := by linarith
    have hL0 : 0 < P.L T := by linarith
    have hg := gv_deriv_facts hW
    have hS : ∀ t : ℝ, 1 ≤ t → t ≤ Real.exp (P.L T) →
        |(∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, ‖Fam.c T k‖ ^ 2 / k)
          - l T ^ 2 * ∫ s in (0:ℝ)..(Real.log t / l T), Fam.D s| ≤ ε / 2 * l T ^ 2 := by
      intro t ht1 ht2
      have ht0 : 0 < t := by linarith
      have hy0 : 0 ≤ Real.log t := Real.log_nonneg ht1
      have hyL : Real.log t ≤ P.L T := by
        rw [← Real.log_exp (P.L T)]; exact Real.log_le_log ht0 ht2
      have := hT₀ T hT (Real.log t) hy0 (hyL.trans hLl)
      rwa [Real.exp_log ht0] at this
    have key := abel_sum_density (c := fun k => ‖Fam.c T k‖ ^ 2 / k) (by simp) hF.D_cont hl0 hL0
      hS hg.1 hg.2.1 hg.2.2 (fun y hy => hW.gv_eq_zero (by rw [abs_of_nonneg (by linarith)]; exact hy))
    show |sumW2g (Fam.c T) (P.X T) (AdmWindow.gv (win T))
        - P.L T ^ 3 / 2 * (2 / P.L T ^ 3 * l T *
            ∫ y in (0:ℝ)..(P.L T), (Fam.D (y / l T) * AdmWindow.gv (win T) y))|
      ≤ ε * (l T ^ 2 * P.L T)
    have e : P.L T ^ 3 / 2 * (2 / P.L T ^ 3 * l T *
        ∫ y in (0:ℝ)..(P.L T), (Fam.D (y / l T) * AdmWindow.gv (win T) y))
        = l T * ∫ y in (0:ℝ)..(P.L T), (Fam.D (y / l T) * AdmWindow.gv (win T) y) := by
      field_simp
    rw [e]
    have hX : Real.exp (P.L T) = P.X T := rfl
    rw [hX] at key
    refine (le_of_eq ?_).trans (key.trans (le_of_eq (by ring)))
    rfl
  case cmuP =>
    obtain ⟨C, T₂, hC⟩ := cross_muPc (cϱ := cW) hΓ hlam
    refine EvBound.of_eventually_le (c := max C 0 * C₁ + 1) (by positivity) ?_
    filter_upwards [eventually_of_core hT₁ (Q := fun p F => ∀ c : ℕ → ℂ, c 1 = 0 →
        |Mform F.Phi p.T Zeta23.mu (Pc p.X c)| ≤ C * (p.l * p.L * S1 c p.X))
        (fun p F hl hT hF' c hc => hC p F c hl hT hF' hc), hS1, hreg]
      with T h hS1T ⟨hT1, hl, _, hL, hX2, _, _⟩
    have h' := h (Fam.c T) (hc1 T)
    show |Mform (Fw P win T).Phi T Zeta23.mu (Pc (P.X T) (Fam.c T))|
      ≤ (max C 0 * C₁ + 1) * (P.L T * l T ^ 2 * Real.sqrt (P.X T))
    refine h'.trans ?_
    have hm : 0 ≤ max C 0 := le_max_right _ _
    have hx : 0 ≤ l T * P.L T * S1 (Fam.c T) (P.X T) := by have := hS1nn T; positivity
    calc C * (l T * P.L T * S1 (Fam.c T) (P.X T))
        ≤ max C 0 * (l T * P.L T * S1 (Fam.c T) (P.X T)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hx
      _ ≤ max C 0 * (l T * P.L T * (C₁ * Real.sqrt (P.X T) * l T)) := by gcongr
      _ = max C 0 * C₁ * (P.L T * l T ^ 2 * Real.sqrt (P.X T)) := by ring
      _ ≤ (max C 0 * C₁ + 1) * (P.L T * l T ^ 2 * Real.sqrt (P.X T)) := by
          have : 0 ≤ P.L T * l T ^ 2 * Real.sqrt (P.X T) := by positivity
          nlinarith
  case cmuPi =>
    obtain ⟨C, T₂, hC⟩ := PrimeSide.prop_cross_muPi cW P.lam hΓ hcheb hlam
    refine EvBound.of_eventually_le (c := |cPi| * max C 0 + 1) (by positivity) ?_
    filter_upwards [eventually_of_core hT₁ hC, hreg] with T h ⟨hT1, hl, _, hL, hX2, _, _⟩
    show |cPi * Mform (Fw P win T).Phi T Zeta23.mu (Zeta23.PiX (P.X T))|
      ≤ (|cPi| * max C 0 + 1) * (l T * P.L T * Real.sqrt (P.X T))
    rw [abs_mul]
    have hx : 0 ≤ l T * P.L T * Real.sqrt (P.X T) := by positivity
    calc |cPi| * |Mform (Fw P win T).Phi T Zeta23.mu (Zeta23.PiX (P.X T))|
        ≤ |cPi| * (max C 0 * (l T * P.L T * Real.sqrt (P.X T))) := by
          refine mul_le_mul_of_nonneg_left (h.trans ?_) (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hx
      _ ≤ (|cPi| * max C 0 + 1) * (l T * P.L T * Real.sqrt (P.X T)) := by nlinarith
  case cPPi =>
    refine EvBound.of_eventually_le (c := |cPi| * 6 * C₁ + 1) (by positivity) ?_
    filter_upwards [hCore, hS1, hreg] with T hF' hS1T ⟨hT1, hl, _, hL, hX2, _, _⟩
    have hT0 : 0 < (P.toSetting T).T := by show 0 < T; linarith
    have h := cross_PcPi_le hF' hT0 (Fam.c T)
    show |cPi * Mform (Fw P win T).Phi T (Pc (P.X T) (Fam.c T)) (Zeta23.PiX (P.X T))|
      ≤ (|cPi| * 6 * C₁ + 1) * (P.L T * P.X T * l T)
    rw [abs_mul]
    have hsX : Real.sqrt (P.X T) * Real.sqrt (P.X T) = P.X T := Real.mul_self_sqrt (by linarith)
    have hx : 0 ≤ P.L T * P.X T * l T := by positivity
    calc |cPi| * |Mform (Fw P win T).Phi T (Pc (P.X T) (Fam.c T)) (Zeta23.PiX (P.X T))|
        ≤ |cPi| * (6 * S1 (Fam.c T) (P.X T) * (P.L T * Real.sqrt (P.X T))) :=
          mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ ≤ |cPi| * (6 * (C₁ * Real.sqrt (P.X T) * l T) * (P.L T * Real.sqrt (P.X T))) := by
          gcongr
      _ = |cPi| * 6 * C₁ * (P.L T * (Real.sqrt (P.X T) * Real.sqrt (P.X T)) * l T) := by ring
      _ = |cPi| * 6 * C₁ * (P.L T * P.X T * l T) := by rw [hsX]
      _ ≤ (|cPi| * 6 * C₁ + 1) * (P.L T * P.X T * l T) := by nlinarith
  case cPiPi =>
    obtain ⟨C, T₂, hC⟩ := PrimeSide.prop_cross_PiPi cW P.lam hΓ hcheb hlam
    refine EvBound.of_eventually_le (c := cPi ^ 2 * max C 0 + 1) (by positivity) ?_
    filter_upwards [eventually_of_core hT₁ hC, hreg] with T h ⟨hT1, hl, _, hL, hX2, _, _⟩
    show |cPi ^ 2 * Mform (Fw P win T).Phi T (Zeta23.PiX (P.X T)) (Zeta23.PiX (P.X T))|
      ≤ (cPi ^ 2 * max C 0 + 1) * (P.L T * P.X T / T)
    rw [abs_mul, abs_of_nonneg (sq_nonneg cPi)]
    have hx : 0 ≤ P.L T * P.X T / T := by positivity
    calc cPi ^ 2 * |Mform (Fw P win T).Phi T (Zeta23.PiX (P.X T)) (Zeta23.PiX (P.X T))|
        ≤ cPi ^ 2 * (max C 0 * (P.L T * P.X T / T)) := by
          refine mul_le_mul_of_nonneg_left (h.trans ?_) (sq_nonneg _)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hx
      _ ≤ (cPi ^ 2 * max C 0 + 1) * (P.L T * P.X T / T) := by nlinarith

/-- **The ξ′ two-trace package for the concrete data** (window family × coefficient family). -/
theorem tracesBoundsXi_concrete (hP : P.Valid) (hlam1 : P.lam < 1) (hwin : AdmFamily P win cW)
    (hF : Fam.Hyps) (hΓ : Zeta23.GammaFacts) (hMV : ∃ C : ℝ, 0 < C ∧ Zeta23.MVHilbert C)
    (hPP : PPInput) (hN : EvBound (fun T => Ncnt T - T * ell1 T / (2 * π)) l) :
    TracesBoundsXi P (concreteData P win Fam cPi Ncnt).aT (concreteData P win Fam cPi Ncnt).bT
      (concreteData P win Fam cPi Ncnt).JT (concreteData P win Fam cPi Ncnt).trG
      (concreteData P win Fam cPi Ncnt).trG2 Ncnt :=
  tracesBoundsXi_of_factsXi (concreteFacts hP hlam1 hwin hF hΓ hMV hPP hN)

end Facts

end XiPrime
end Zeta23
