/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
  Part of the Zeta23 formalization of the paper
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/
import Zeta23.PrimeSideA.Basic
import Zeta23.PrimeSideTemp

/-!
# The concrete prime-side data as an instance of the abstract layer
Small, dependency-light file (imports only `PrimeSideA.Basic` and `PrimeSideTemp`):

* `Params.toSetting P T = ⟨T, λ, w⟩`, `Params.localFun P T = ⟨φ̂|_ℝ, Φ|_ℝ, A_φ, g, a, b⟩(T)` and the
  `rfl` bridges (`trGtA (P.toSetting T) (P.localFun T) = P.trGtilde T`, …);
* `PrimeSide.LocalHypsEventually cϱ P` — "the taper facts `LocalHyps` hold for the concrete data for
  all large `T`" (proved in `Zeta23/PrimeSideA/Bridge.lean`);
* `PrimeSide.evBound_of_eventuallyAt` — an `EventuallyAt`-form result specialised to the concrete
  data is an `EvBound` in `T`.
-/

noncomputable section

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace Zeta23

namespace Params
variable (P : Params) (T : ℝ)

/-- The abstract-layer parameter triple `(T, λ, w)` (`PrimeSide.Setting`). -/
def toSetting : PrimeSide.Setting := ⟨T, P.lam, P.w⟩

/-- The concrete taper data at height `T` as an abstract `PrimeSide.LocalFun`:
`(φ̂|_ℝ, Φ|_ℝ, A_φ, g, a, b)` = `(P.phiHatR T, P.PhiR T, P.Aphi T, P.g T, P.a T, P.b T)`. -/
def localFun : PrimeSide.LocalFun := ⟨P.phiHatR T, P.PhiR T, P.Aphi T, P.g T, P.a T, P.b T⟩

@[simp] lemma toSetting_T : (P.toSetting T).T = T := rfl
@[simp] lemma toSetting_lam : (P.toSetting T).lam = P.lam := rfl
@[simp] lemma toSetting_w : (P.toSetting T).w = P.w := rfl
@[simp] lemma toSetting_L : (P.toSetting T).L = P.L T := rfl
@[simp] lemma toSetting_X : (P.toSetting T).X = P.X T := rfl
@[simp] lemma toSetting_l : (P.toSetting T).l = l T := rfl
@[simp] lemma toSetting_ell1 : (P.toSetting T).ell1 = ell1 T := rfl
@[simp] lemma toSetting_d : (P.toSetting T).d = P.d T := rfl
@[simp] lemma toSetting_tau (k : ℤ) : (P.toSetting T).tau k = P.tau T k := rfl
@[simp] lemma localFun_a : (P.localFun T).a = P.a T := rfl
@[simp] lemma localFun_b : (P.localFun T).b = P.b T := rfl
@[simp] lemma localFun_Phi : (P.localFun T).Phi = P.PhiR T := rfl
@[simp] lemma localFun_g : (P.localFun T).g = P.g T := rfl
@[simp] lemma localFun_phiHat : (P.localFun T).phiHat = P.phiHatR T := rfl

end Params

namespace PrimeSide

variable (P : Params) (T : ℝ)

/-- `GentryA` on the concrete data is `Params.Gentry` ([eq:Gdef], 2nd expression). -/
lemma GentryA_concrete (k l : ℤ) : GentryA (P.toSetting T) (P.localFun T) k l = P.Gentry T k l := rfl

/-- `tr G̃` of the abstract layer on the concrete data is `Params.trGtilde`. -/
lemma trGtA_concrete : trGtA (P.toSetting T) (P.localFun T) = P.trGtilde T := rfl

/-- `tr G̃²` of the abstract layer on the concrete data is `Params.trGtildeSq`. -/
lemma trGt2A_concrete : trGt2A (P.toSetting T) (P.localFun T) = P.trGtildeSq T := rfl

/-- The taper facts `LocalHyps` hold for the concrete data for all large `T`
(proved in `Zeta23/PrimeSideA/Bridge.lean`; here a named hypothesis). -/
def LocalHypsEventually (cϱ : ℝ) (P : Params) : Prop :=
  ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → LocalHyps cϱ (P.toSetting T) (P.localFun T)

variable {P}

/-- Generic bridge: an `EventuallyAt`-form result of the abstract layer, specialised to the
concrete data, is an `EvBound` in `T` (given the local hypotheses eventually and an eventually
nonnegative majorant). -/
lemma evBound_of_eventuallyAt {cϱ : ℝ} (hLoc : LocalHypsEventually cϱ P)
    {f g : Setting → LocalFun → ℝ}
    (h : ∃ C : ℝ, EventuallyAt cϱ P.lam (fun p F => |f p F| ≤ C * g p F))
    (hg : ∀ᶠ T in atTop, 0 ≤ g (P.toSetting T) (P.localFun T)) :
    EvBound (fun T => f (P.toSetting T) (P.localFun T))
      (fun T => g (P.toSetting T) (P.localFun T)) := by
  obtain ⟨T₀, hT₀⟩ := hLoc
  obtain ⟨C, T₁, hT₁⟩ := h
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp hg
  refine ⟨max C 1, by positivity, max T₀ (max T₁ T₂), fun T hT => ?_⟩
  have h0 : T₀ ≤ T := (le_max_left _ _).trans hT
  have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  calc |f (P.toSetting T) (P.localFun T)| ≤ C * g (P.toSetting T) (P.localFun T) :=
        hT₁ _ _ rfl h1 (hT₀ T h0)
    _ ≤ max C 1 * g (P.toSetting T) (P.localFun T) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (hT₂ T h2)



end PrimeSide

end Zeta23

end
