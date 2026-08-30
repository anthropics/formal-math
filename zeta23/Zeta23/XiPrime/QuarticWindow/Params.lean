/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/QuarticWindow/Params.lean — the window-realizing parameter family `P.atV v T`
(mirror of Zeta23/ThmD/ParamsD.lean for the profile-v windows of Zeta23/XiPrime/Defs.lean).

`P.phiV v T u = √(max 0 (v(u/L))) · φ(u)` and `P.atV v T := ⟨x ↦ φ_v(L/2 − w·x), λ, w⟩` are those of
Zeta23/XiPrime/Defs.lean §4.  Here: λ, w — hence L, X, λ₁, d, τ_k, h, 𝓔_T, toSetting — of `P.atV v T` are P's
DEFINITIONALLY (rfl lemmas), and the window of `P.atV v T` AT HEIGHT T is φ_v (`atV_phi`, needs v even and
w ≠ 0), so its abstract local data / taper constants / prime-side traces are the AdmWindow data of φ_v.
-/
import Zeta23.XiPrime.Defs
import Zeta23.ThmD.ParamsD

noncomputable section

open Real

namespace Zeta23
namespace Params

variable (P : Params) (v : ℝ → ℝ) (T : ℝ)

@[simp] theorem atV_lam : (P.atV v T).lam = P.lam := rfl
@[simp] theorem atV_w : (P.atV v T).w = P.w := rfl
@[simp] theorem atV_L : (P.atV v T).L = P.L := rfl
@[simp] theorem atV_X : (P.atV v T).X = P.X := rfl
@[simp] theorem atV_lam1 : (P.atV v T).lam1 = P.lam1 := rfl
@[simp] theorem atV_hgrid : (P.atV v T).hgrid = P.hgrid := rfl
@[simp] theorem atV_d : (P.atV v T).d = P.d := rfl
@[simp] theorem atV_tau : (P.atV v T).tau = P.tau := rfl
@[simp] theorem atV_calE : (P.atV v T).calE = P.calE := rfl
@[simp] theorem atV_toSetting : (P.atV v T).toSetting = P.toSetting := rfl

/-- φ_v in closed form on the tree's taper: φ_v(u) = √(max 0 (v(u/L)))·Taper.phi ϱ L w u (rfl). -/
theorem phiV_eq (u : ℝ) :
    P.phiV v T u = Real.sqrt (max 0 (v (u / P.L T))) * Taper.phi P.ϱ (P.L T) P.w u := rfl

/-- φ_v is even when v is. -/
theorem phiV_even (hv : ∀ s, v (-s) = v s) (u : ℝ) : P.phiV v T (-u) = P.phiV v T u := by
  simp only [phiV_eq, neg_div, hv, Taper.phi_even]

variable {P v}

/-- **the window of `P.atV v T` at height T is φ_v** (v even, w ≠ 0). -/
theorem atV_phi (hw : P.w ≠ 0) (hv : ∀ s, v (-s) = v s) : (P.atV v T).phi T = P.phiV v T := by
  funext u
  show P.phiV v T (P.L T / 2 - P.w * ((P.lam * l T / 2 - |u|) / P.w)) = P.phiV v T u
  have e : P.L T / 2 - P.w * ((P.lam * l T / 2 - |u|) / P.w) = |u| := by
    simp only [Params.L]; field_simp; ring
  rw [e]
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]
  · rw [abs_of_neg hu]
    exact phiV_even P v T hv u

theorem atV_phi_valid (hP : P.Valid) (hv : ∀ s, v (-s) = v s) : (P.atV v T).phi T = P.phiV v T :=
  atV_phi T (by linarith [hP.one_le_w]) hv

/-- the abstract local data of `P.atV v T` at height T are the AdmWindow data of φ_v. -/
theorem atV_localFun (hP : P.Valid) (hv : ∀ s, v (-s) = v s) :
    (P.atV v T).localFun T = AdmWindow.localFun (P.phiV v T) (P.L T) := by
  rw [localFun_eq_admWindow, atV_phi_valid T hP hv]; rfl

theorem atV_a (hP : P.Valid) (hv : ∀ s, v (-s) = v s) :
    (P.atV v T).a T = AdmWindow.av (P.phiV v T) (P.L T) := by
  rw [show (P.atV v T).a T = ((P.atV v T).localFun T).a from rfl, atV_localFun T hP hv]; rfl

theorem atV_b (hP : P.Valid) (hv : ∀ s, v (-s) = v s) :
    (P.atV v T).b T = AdmWindow.bv (P.phiV v T) (P.L T) := by
  rw [show (P.atV v T).b T = ((P.atV v T).localFun T).b from rfl, atV_localFun T hP hv]; rfl

theorem atV_phiHat (hP : P.Valid) (hv : ∀ s, v (-s) = v s) :
    (P.atV v T).phiHat T = AdmWindow.vHat (P.phiV v T) := by
  show AdmWindow.vHat ((P.atV v T).phi T) = _
  rw [atV_phi_valid T hP hv]

theorem atV_phiHatR (hP : P.Valid) (hv : ∀ s, v (-s) = v s) :
    (P.atV v T).phiHatR T = AdmWindow.vHatR (P.phiV v T) := by
  show AdmWindow.vHatR ((P.atV v T).phi T) = _
  rw [atV_phi_valid T hP hv]

/-- the prime-side traces of `P.atV v T` at height T are the abstract-layer traces of the φ_v data. -/
theorem atV_trGtilde (hP : P.Valid) (hv : ∀ s, v (-s) = v s) :
    (P.atV v T).trGtilde T = PrimeSide.trGtA (P.toSetting T) (AdmWindow.localFun (P.phiV v T) (P.L T)) := by
  rw [← PrimeSide.trGtA_concrete (P.atV v T) T, atV_localFun T hP hv]; rfl

theorem atV_trGtildeSq (hP : P.Valid) (hv : ∀ s, v (-s) = v s) :
    (P.atV v T).trGtildeSq T = PrimeSide.trGt2A (P.toSetting T) (AdmWindow.localFun (P.phiV v T) (P.L T)) := by
  rw [← PrimeSide.trGt2A_concrete (P.atV v T) T, atV_localFun T hP hv]; rfl

/-! ### eventual side conditions shared by the QuarticWindow files -/

/-- L_T → ∞ (valid parameters). -/
theorem tendsto_L_of_valid (hP : P.Valid) : Filter.Tendsto P.L Filter.atTop Filter.atTop := by
  have h : Filter.Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi))) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (Filter.tendsto_id.atTop_div_const (by positivity))
  exact (h.const_mul_atTop hP.lam_pos).congr fun T => by simp [Params.L, l]

/-- eventually 8w ≤ L_T. -/
theorem eventually_w8 (hP : P.Valid) : ∀ᶠ T in Filter.atTop, 8 * P.w ≤ P.L T :=
  (tendsto_L_of_valid hP).eventually_ge_atTop _

end Params
end Zeta23

end
