/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/QuarticWindow/Quartic.lean — the quartic profile gives a modulated-taper factor; hence
P.phiV vQuartic T is an admissible window.

f_Q(u) := √(max 0 (vQuartic(u/L))) (so that P.phiV vQuartic T = phiM f_Q φ by rfl) satisfies `ModFactor f_Q L (3/2) 12`:
on the core |u| ≤ L/2 (s = u/L ∈ [−1/2,1/2]) one has 27/40 ≤ vQuartic s ≤ 1 (Zeta23/XiPrime/Certificate/Poly.lean), so
f_Q ≥ 4/5 and, with h(u) := vQuartic(u/L) = f_Q², |h′| ≤ (58/25)/L, |h″| ≤ (64/5)/L²:  f_Q′ = h′/(2f_Q),
f_Q″ = (h″ − 2f_Q′²)/(2f_Q) (differentiate f_Q·f_Q = h twice) give |f_Q′| ≤ (29/20)/L ≤ (3/2)/L and
|f_Q″| ≤ (5/8)(64/5 + 2·(3/2)²)/L² < 12/L².  Smoothness: vQuartic > 0 on |s| < 3/5, so f_Q = √∘vQuartic∘(·/L) is C^∞
on |u| < (3/5)L ⊇ [−L/2, L/2] + margin L/10.
-/
import Zeta23.XiPrime.QuarticWindow.ModWindow
import Zeta23.XiPrime.QuarticWindow.Params
import Zeta23.XiPrime.Certificate.Poly

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace Zeta23
namespace XiPrime

/-- the quartic modulating factor in the u-variable. -/
def fQ (L : ℝ) (u : ℝ) : ℝ := Real.sqrt (max 0 (vQuartic (u / L)))

/-- h := vQuartic(u/L), in expanded form. -/
def hQ (L : ℝ) (u : ℝ) : ℝ := vQuartic (u / L)

lemma hQ_eq (L u : ℝ) : hQ L u = 1 - 7 / 25 * (u / L) ^ 2 - 102 / 25 * (u / L) ^ 4 := by
  simp only [hQ, vQuartic_eq]

/-- vQuartic is positive on |s| ≤ 3/5 (indeed ≥ 1 − (7/25)(9/25) − (102/25)(81/625) > 9/25). -/
lemma vQuartic_pos_of_abs_le {s : ℝ} (hs : |s| ≤ 3 / 5) : 0 < vQuartic s := by
  rw [vQuartic_eq]
  have h2 : s ^ 2 ≤ 9 / 25 := by
    have := abs_le.mp hs; nlinarith
  have h4 : s ^ 4 ≤ 81 / 625 := by
    have : s ^ 4 = (s ^ 2) ^ 2 := by ring
    rw [this]; nlinarith [sq_nonneg s]
  nlinarith

/-- vQuartic is nonincreasing in |s| on [0, ∞). -/
lemma vQuartic_antitoneOn : AntitoneOn vQuartic (Ici 0) := by
  intro s hs t ht hst
  simp only [mem_Ici] at hs ht
  rw [vQuartic_eq, vQuartic_eq]
  have h2 : s ^ 2 ≤ t ^ 2 := by nlinarith
  have h4 : s ^ 4 ≤ t ^ 4 := by nlinarith [sq_nonneg s, sq_nonneg t]
  nlinarith

variable {L : ℝ}

lemma fQ_even (u : ℝ) : fQ L (-u) = fQ L u := by
  simp only [fQ, neg_div, vQuartic_even]

lemma fQ_nonneg (u : ℝ) : 0 ≤ fQ L u := Real.sqrt_nonneg _

lemma fQ_le_one (u : ℝ) : fQ L u ≤ 1 := by
  unfold fQ
  rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_le_sqrt (max_le zero_le_one (vQuartic_le_one _))

/-- on the core: u/L ∈ [−1/2, 1/2]. -/
lemma core_mem (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) : u / L ∈ Icc (-(1/2 : ℝ)) (1/2) := by
  have := abs_le.mp hu
  constructor
  · rw [le_div_iff₀ hL]; linarith
  · rw [div_le_iff₀ hL]; linarith

lemma hQ_core_ge (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) : 27 / 40 ≤ hQ L u :=
  vQuartic_ge (core_mem hL hu)

/-- on the core, f_Q = √h (no max) and f_Q ≥ 4/5. -/
lemma fQ_core_ge (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) : 4 / 5 ≤ fQ L u := by
  have h := hQ_core_ge hL hu
  unfold fQ
  rw [max_eq_right (by unfold hQ at h; linarith)]
  refine Real.le_sqrt_of_sq_le ?_
  unfold hQ at h; nlinarith

/-- the smooth region U := (−3L/5, 3L/5): there h > 0 and f_Q = √h. -/
lemma hQ_pos_of_mem (hL : 0 < L) {u : ℝ} (hu : u ∈ Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10)) :
    0 < hQ L u := by
  apply vQuartic_pos_of_abs_le
  rw [abs_div, abs_of_pos hL, div_le_iff₀ hL, abs_le]
  constructor <;> linarith [hu.1, hu.2]

lemma fQ_eq_sqrt_of_mem (hL : 0 < L) {u : ℝ} (hu : u ∈ Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10)) :
    fQ L u = Real.sqrt (hQ L u) := by
  show Real.sqrt (max 0 (hQ L u)) = _
  rw [max_eq_right (hQ_pos_of_mem hL hu).le]

lemma hQ_contDiff (_hL : 0 < L) : ContDiff ℝ ⊤ (hQ L) := by
  have : hQ L = fun u => 1 - 7 / 25 * (u / L) ^ 2 - 102 / 25 * (u / L) ^ 4 := funext (hQ_eq L)
  rw [this]; fun_prop

lemma fQ_contDiffOn (hL : 0 < L) :
    ContDiffOn ℝ 2 (fQ L) (Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10)) := by
  have h1 : ContDiffOn ℝ 2 (fun u => Real.sqrt (hQ L u)) (Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10)) :=
    ((hQ_contDiff hL).of_le le_top).contDiffOn.sqrt fun u hu => (hQ_pos_of_mem hL hu).ne'
  exact h1.congr fun u hu => fQ_eq_sqrt_of_mem hL hu

/-- f_Q · f_Q = h on U. -/
lemma fQ_mul_self_of_mem (hL : 0 < L) {u : ℝ} (hu : u ∈ Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10)) :
    fQ L u * fQ L u = hQ L u := by
  rw [fQ_eq_sqrt_of_mem hL hu, ← sq, Real.sq_sqrt (hQ_pos_of_mem hL hu).le]

/-! ### derivatives of h -/

lemma hasDerivAt_hQ (hL : 0 < L) (u : ℝ) :
    HasDerivAt (hQ L) (-(14 / 25) * u / L ^ 2 - 408 / 25 * u ^ 3 / L ^ 4) u := by
  have e : hQ L = fun u => 1 - (7 / 25 / L ^ 2) * u ^ 2 - (102 / 25 / L ^ 4) * u ^ 4 := by
    funext u; rw [hQ_eq]; field_simp
  rw [e]
  have h := ((hasDerivAt_const u (1:ℝ)).sub ((hasDerivAt_pow 2 u).const_mul (7 / 25 / L ^ 2))).sub
    ((hasDerivAt_pow 4 u).const_mul (102 / 25 / L ^ 4))
  exact h.congr_deriv (by push_cast; ring)

lemma deriv_hQ (hL : 0 < L) (u : ℝ) : deriv (hQ L) u = -(14 / 25) * u / L ^ 2 - 408 / 25 * u ^ 3 / L ^ 4 :=
  (hasDerivAt_hQ hL u).deriv

lemma hasDerivAt_deriv_hQ (hL : 0 < L) (u : ℝ) :
    HasDerivAt (deriv (hQ L)) (-(14 / 25) / L ^ 2 - 1224 / 25 * u ^ 2 / L ^ 4) u := by
  have e : deriv (hQ L) = fun u => -(14 / 25 / L ^ 2) * u - (408 / 25 / L ^ 4) * u ^ 3 := by
    funext u; rw [deriv_hQ hL]; field_simp
  rw [e]
  have h1 : HasDerivAt (fun u : ℝ => -(14 / 25 / L ^ 2) * u) (-(14 / 25 / L ^ 2)) u := by
    simpa using (hasDerivAt_id u).const_mul (-(14 / 25 / L ^ 2))
  have h2 : HasDerivAt (fun u : ℝ => 408 / 25 / L ^ 4 * u ^ 3) (408 / 25 / L ^ 4 * (3 * u ^ 2)) u := by
    simpa using (hasDerivAt_pow 3 u).const_mul (408 / 25 / L ^ 4)
  have h : HasDerivAt (fun u : ℝ => -(14 / 25 / L ^ 2) * u - 408 / 25 / L ^ 4 * u ^ 3)
      (-(14 / 25 / L ^ 2) - 408 / 25 / L ^ 4 * (3 * u ^ 2)) u := h1.sub h2
  refine h.congr_deriv ?_
  field_simp
  ring

lemma deriv2_hQ (hL : 0 < L) (u : ℝ) :
    deriv (deriv (hQ L)) u = -(14 / 25) / L ^ 2 - 1224 / 25 * u ^ 2 / L ^ 4 :=
  (hasDerivAt_deriv_hQ hL u).deriv

lemma abs_deriv_hQ_le (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) : |deriv (hQ L) u| ≤ 58 / 25 / L := by
  rw [deriv_hQ hL]
  obtain ⟨h1, h2⟩ := abs_le.mp hu
  have hL2 : 0 < L ^ 2 := by positivity
  have hL4 : 0 < L ^ 4 := by positivity
  rw [abs_le]
  constructor
  · rw [show -(58 / 25 / L) = (-(14/25) * (L/2) / L ^ 2 - 408/25 * (L/2)^3 / L ^ 4) by field_simp; ring]
    have ha : -(14 / 25) * (L / 2) / L ^ 2 ≤ -(14 / 25) * u / L ^ 2 := by
      apply div_le_div_of_nonneg_right _ hL2.le; nlinarith
    have hb : 408 / 25 * u ^ 3 / L ^ 4 ≤ 408 / 25 * (L / 2) ^ 3 / L ^ 4 := by
      apply div_le_div_of_nonneg_right _ hL4.le
      nlinarith [sq_nonneg u, sq_nonneg (L/2 - u), sq_nonneg (L/2 + u)]
    linarith
  · rw [show (58 / 25 / L) = (-(14/25) * (-(L/2)) / L ^ 2 - 408/25 * (-(L/2))^3 / L ^ 4) by field_simp; ring]
    have ha : -(14 / 25) * u / L ^ 2 ≤ -(14 / 25) * (-(L / 2)) / L ^ 2 := by
      apply div_le_div_of_nonneg_right _ hL2.le; nlinarith
    have hb : 408 / 25 * (-(L / 2)) ^ 3 / L ^ 4 ≤ 408 / 25 * u ^ 3 / L ^ 4 := by
      apply div_le_div_of_nonneg_right _ hL4.le
      nlinarith [sq_nonneg u, sq_nonneg (L/2 - u), sq_nonneg (L/2 + u)]
    linarith

lemma abs_deriv2_hQ_le (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) :
    |deriv (deriv (hQ L)) u| ≤ 64 / 5 / L ^ 2 := by
  rw [deriv2_hQ hL]
  have hu2 : u ^ 2 ≤ (L / 2) ^ 2 := by
    have := abs_le.mp hu; nlinarith
  have hL2 : 0 < L ^ 2 := by positivity
  have hL4 : 0 < L ^ 4 := by positivity
  set a : ℝ := 14 / 25 / L ^ 2 with ha
  set b : ℝ := 1224 / 25 * u ^ 2 / L ^ 4 with hb
  have hab : -(14 / 25) / L ^ 2 - 1224 / 25 * u ^ 2 / L ^ 4 = -a - b := by
    simp only [ha, hb]; ring
  rw [hab]
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  rw [abs_of_nonpos (by linarith)]
  have key : b ≤ 306 / 25 / L ^ 2 := by
    simp only [hb]
    rw [div_le_div_iff₀ hL4 hL2]
    have : L ^ 4 = L ^ 2 * L ^ 2 := by ring
    nlinarith
  have e : (64:ℝ) / 5 / L ^ 2 = a + 306 / 25 / L ^ 2 := by simp only [ha]; ring
  linarith

/-! ### derivatives of f_Q on the core, through f_Q · f_Q = h -/

lemma abs_deriv_fQ_le (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) : |deriv (fQ L) u| ≤ 3 / 2 / L := by
  set U : Set ℝ := Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10) with hUdef
  have hU : IsOpen U := isOpen_Ioo
  have huU : u ∈ U := by
    simp only [hUdef, mem_Ioo]; constructor <;> linarith [neg_abs_le u, le_abs_self u]
  have hsm := fQ_contDiffOn hL
  -- h' = 2 f_Q f_Q'
  have hev : (fun v => fQ L v * fQ L v) =ᶠ[nhds u] hQ L := by
    filter_upwards [hU.mem_nhds huU] with v hv using fQ_mul_self_of_mem hL hv
  have hd : deriv (hQ L) u = deriv (fQ L) u * fQ L u + fQ L u * deriv (fQ L) u := by
    rw [← hev.deriv_eq]; exact deriv_mul_eq hU hsm hsm huU
  have hf := fQ_core_ge hL hu
  have hh := abs_deriv_hQ_le hL hu
  have e : deriv (fQ L) u = deriv (hQ L) u / (2 * fQ L u) := by
    rw [hd]; field_simp; ring
  rw [e, abs_div, abs_of_pos (by linarith : 0 < 2 * fQ L u)]
  rw [div_le_div_iff₀ (by linarith) hL]
  calc |deriv (hQ L) u| * L ≤ 58 / 25 / L * L := by gcongr
    _ = 58 / 25 := by field_simp
    _ ≤ 3 / 2 * (2 * (4 / 5)) := by norm_num
    _ ≤ 3 / 2 * (2 * fQ L u) := by gcongr

lemma abs_deriv2_fQ_le (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) : |deriv (deriv (fQ L)) u| ≤ 12 / L ^ 2 := by
  set U : Set ℝ := Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10) with hUdef
  have hU : IsOpen U := isOpen_Ioo
  have hmemU : ∀ v, |v| < L / 2 + L / 10 → v ∈ U := fun v hv => by
    simp only [hUdef, mem_Ioo]; constructor <;> linarith [neg_abs_le v, le_abs_self v]
  have huU : u ∈ U := hmemU u (by linarith)
  have hsm := fQ_contDiffOn hL
  -- h'' = 2 f_Q f_Q'' + 2 f_Q'² : second derivatives agree on U since the functions agree on U
  have hd1 : ∀ v ∈ U, deriv (fun x => fQ L x * fQ L x) v = deriv (hQ L) v := by
    intro v hv
    have hev : (fun x => fQ L x * fQ L x) =ᶠ[nhds v] hQ L := by
      filter_upwards [hU.mem_nhds hv] with x hx using fQ_mul_self_of_mem hL hx
    exact hev.deriv_eq
  have hev2 : deriv (fun x => fQ L x * fQ L x) =ᶠ[nhds u] deriv (hQ L) := by
    filter_upwards [hU.mem_nhds huU] with v hv using hd1 v hv
  have hd2 : deriv (deriv (hQ L)) u
      = deriv (deriv (fQ L)) u * fQ L u + 2 * (deriv (fQ L) u * deriv (fQ L) u)
        + fQ L u * deriv (deriv (fQ L)) u := by
    rw [← hev2.deriv_eq]; exact deriv2_mul_eq hU hsm hsm huU
  have hf := fQ_core_ge hL hu
  have h1 := abs_deriv_fQ_le hL hu
  have h2 := abs_deriv2_hQ_le hL hu
  have e : deriv (deriv (fQ L)) u
      = (deriv (deriv (hQ L)) u - 2 * (deriv (fQ L) u * deriv (fQ L) u)) / (2 * fQ L u) := by
    rw [hd2]; field_simp; ring
  rw [e, abs_div, abs_of_pos (by linarith : 0 < 2 * fQ L u), div_le_div_iff₀ (by linarith) (by positivity)]
  have hsq : |deriv (fQ L) u| ^ 2 ≤ (3 / 2 / L) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hL2 : 0 < L ^ 2 := by positivity
  calc |deriv (deriv (hQ L)) u - 2 * (deriv (fQ L) u * deriv (fQ L) u)| * L ^ 2
      ≤ (|deriv (deriv (hQ L)) u| + 2 * |deriv (fQ L) u| ^ 2) * L ^ 2 := by
        gcongr
        calc |deriv (deriv (hQ L)) u - 2 * (deriv (fQ L) u * deriv (fQ L) u)|
            ≤ |deriv (deriv (hQ L)) u| + |2 * (deriv (fQ L) u * deriv (fQ L) u)| := abs_sub _ _
          _ = |deriv (deriv (hQ L)) u| + 2 * |deriv (fQ L) u| ^ 2 := by
              rw [abs_mul, abs_two, abs_mul, sq]
    _ ≤ (64 / 5 / L ^ 2 + 2 * (3 / 2 / L) ^ 2) * L ^ 2 := by gcongr
    _ = 64 / 5 + 9 / 2 := by field_simp; ring
    _ ≤ 12 * (2 * (4 / 5)) := by norm_num
    _ ≤ 12 * (2 * fQ L u) := by gcongr

/-! ### the ModFactor instance and the admissible window -/

theorem modFactor_fQ (hL : 0 < L) : ModFactor (fQ L) L (3 / 2) 12 where
  A_nonneg := by norm_num
  B_nonneg := by norm_num
  even := fQ_even
  nonneg := fQ_nonneg
  le_one := fun u _ => fQ_le_one u
  antitone := by
    intro x hx y hy hxy
    unfold fQ
    apply Real.sqrt_le_sqrt
    apply max_le_max le_rfl
    exact vQuartic_antitoneOn (div_nonneg hx.1 hL.le) (div_nonneg hy.1 hL.le)
      (div_le_div_of_nonneg_right hxy hL.le)
  smooth := ⟨L / 10, by positivity, fQ_contDiffOn hL⟩
  deriv_le := fun u hu => abs_deriv_fQ_le hL hu
  deriv2_le := fun u hu => abs_deriv2_fQ_le hL hu

/-- the window constant of the quartic window. -/
def cQ (ϱ : ℝ → ℝ) : ℝ := cMod ϱ (3 / 2) 12

/-- P.phiV vQuartic T is the modulated taper with factor f_Q (rfl). -/
theorem phiV_quartic_eq (P : Params) (T : ℝ) : P.phiV vQuartic T = phiM (fQ (P.L T)) P.ϱ (P.L T) P.w := rfl

/-- **The quartic window is admissible.** -/
theorem admWindow_phiV_quartic {P : Params} (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T) :
    AdmWindow (P.phiV vQuartic T) (P.L T) P.w (cQ P.ϱ) := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  rw [phiV_quartic_eq]
  exact admWindow_phiM (modFactor_fQ hL) hP.taper hP.one_le_w hwL

end XiPrime
end Zeta23

end
