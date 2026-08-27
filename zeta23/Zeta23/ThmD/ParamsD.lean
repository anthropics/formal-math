/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmD/ParamsD.lean

THE WINDOW-REALIZING PARAMETER FAMILY.  The zero side of the argument (Zeta23/ZeroSide.lean,
Zeta23/Tail.lean, the H-EF bridge Zeta23/Hypotheses/GzGp.lean) is written over 'P : Params', whose
window is hard-wired as the ramp taper 'P.phi T u = P.ϱ ((L/2 − |u|)/w)'.  The Montgomery–Taylor
window 'φ_D(u) = √cos(√2 λ u/L) · (ramp taper)' (the paper §7.1) is NOT of that form for any fixed
profile (its shape depends on L).  But every zero-side statement the §6 endgame consumes is a
statement AT ONE HEIGHT T ('BlockInputs Z P T', 'TailInputs Z P T θ₀', 'Z.Gz P T = P.Gp T'), and
their fixed-T producers ('ZeroSide.blockInputsAt', 'Tail.TailHyp.tailInputs',
'ZeroConfig.Gz_eq_Gp') are generic in P.  So for each height T we use the parameter set

    P.atD T := ⟨x ↦ φ_D^{(T)}(L/2 − w·x), λ, w⟩,

whose window AT HEIGHT T is exactly φ_D^{(T)} ('Params.atD_phi'), and whose λ, w — hence L, X,
λ₁, d, τ_k, h, 𝓔_T, toSetting — are those of P DEFINITIONALLY (all 'rfl' below).  The zero-side
Gram matrix 'Z.Gz (P.atD T) T' is then literally the paper's G for the Montgomery–Taylor window,
and no file outside Zeta23/ThmD/ is touched.  (A profile 'ϱ' of a 'Params' is only ever evaluated
through 'Params.phi', so the values of the realizing profile at x > L/(2w) are irrelevant.)
-/
import Zeta23.ThmD.BridgeD

noncomputable section

open Real

namespace Zeta23

namespace Params

variable (P : Params) (T : ℝ)

/-- the parameter set realizing the Montgomery–Taylor window of height 'T' (see file header). -/
def atD : Params := ⟨fun x => P.phiD T (P.L T / 2 - P.w * x), P.lam, P.w⟩

@[simp] theorem atD_lam : (P.atD T).lam = P.lam := rfl
@[simp] theorem atD_w : (P.atD T).w = P.w := rfl
@[simp] theorem atD_L : (P.atD T).L = P.L := rfl
@[simp] theorem atD_X : (P.atD T).X = P.X := rfl
@[simp] theorem atD_lam1 : (P.atD T).lam1 = P.lam1 := rfl
@[simp] theorem atD_hgrid : (P.atD T).hgrid = P.hgrid := rfl
@[simp] theorem atD_d : (P.atD T).d = P.d := rfl
@[simp] theorem atD_tau : (P.atD T).tau = P.tau := rfl
@[simp] theorem atD_calE : (P.atD T).calE = P.calE := rfl
@[simp] theorem atD_toSetting : (P.atD T).toSetting = P.toSetting := rfl

variable {P}

/-- **the window of 'P.atD T' at height 'T' is the Montgomery–Taylor window φ_D.** -/
theorem atD_phi (hw : P.w ≠ 0) : (P.atD T).phi T = P.phiD T := by
  funext u
  show P.phiD T (P.L T / 2 - P.w * ((P.lam * l T / 2 - |u|) / P.w)) = P.phiD T u
  have e : P.L T / 2 - P.w * ((P.lam * l T / 2 - |u|) / P.w) = |u| := by
    simp only [Params.L]; field_simp; ring
  rw [e]
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]
  · rw [abs_of_neg hu]
    exact ThmD.phiD_even u

theorem atD_phi_valid (hP : P.Valid) : (P.atD T).phi T = P.phiD T :=
  atD_phi T (by linarith [hP.one_le_w])

/-- every 'Params'' abstract local data is the 'AdmWindow.localFun' of its window (rfl). -/
theorem localFun_eq_admWindow (Q : Params) (T : ℝ) :
    Q.localFun T = AdmWindow.localFun (Q.phi T) (Q.L T) := rfl

/-- hence the abstract local data of 'P.atD T' at height T are the D-data 'P.localFunD T'. -/
theorem atD_localFun (hP : P.Valid) : (P.atD T).localFun T = P.localFunD T := by
  rw [localFun_eq_admWindow, atD_phi_valid T hP]
  rfl

theorem atD_a (hP : P.Valid) : (P.atD T).a T = (P.localFunD T).a := by
  rw [← atD_localFun T hP]; rfl

theorem atD_b (hP : P.Valid) : (P.atD T).b T = (P.localFunD T).b := by
  rw [← atD_localFun T hP]; rfl

/-- the prime-side traces of 'P.atD T' at height T are the abstract-layer traces of the D-data. -/
theorem atD_trGtilde (hP : P.Valid) :
    (P.atD T).trGtilde T = PrimeSide.trGtA (P.toSetting T) (P.localFunD T) := by
  rw [← PrimeSide.trGtA_concrete (P.atD T) T, atD_localFun T hP]; rfl

theorem atD_trGtildeSq (hP : P.Valid) :
    (P.atD T).trGtildeSq T = PrimeSide.trGt2A (P.toSetting T) (P.localFunD T) := by
  rw [← PrimeSide.trGt2A_concrete (P.atD T) T, atD_localFun T hP]; rfl

end Params

end Zeta23

end
