/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmDE/Final.lean — **"Theorem D holds likewise" for Dirichlet L-functions** (the paper
[thm:E], last sentence).  For every primitive Dirichlet character χ mod q > 1
and the nontrivial zeros of Mathlib's 'DirichletCharacter.LFunction χ' (counts of
Zeta23/ThmE/Statement.lean), with NO hypotheses:

  thmE_D₀        : ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (HD 1 − ε)·N_χ(T,2T) ≤ N*_{0,χ}(T,2T),
  thmE_D₀_simple : … (2c₁* − 1 − ε)·N_χ(T,2T) ≤ N^s_{0,χ}(T,2T),
  thmE_D₀_dist   : … (c₁* − ε)·N_χ(T,2T) ≤ N_{d,χ}(T,2T),

HD 1 = 2 − 1/c₁* = 3/2 − cot(1/√2)/√2, c₁* = Zeta23.ThmD.cStar 1 — the Montgomery–Taylor constants of
[thm:D]; and the fixed-λ forms at every λ ∈ (0,1).  Assembly = Zeta23/ThmD/Final.lean's with the
χ-pieces: Concrete (χ-D prime side), ZeroSide (P.atD tail/EF-bridge for χ), Limit (λ_{1,χ} → λ),
Endgame (§6 for χ with the window-general ratio constant), and ThmE/Final.lean's unconditional
input package paperInputsChi_L (EF(χ), RvM(χ), Γ(χ), cheb, cheb-coprime, MV — all theorems).
-/
import Zeta23.ThmE.Final
import Zeta23.ThmDE.Endgame
import Zeta23.ThmDE.Concrete
import Zeta23.ThmDE.ZeroSide
import Zeta23.ThmDE.Limit
import Zeta23.ThmD.ZeroSideD
import Zeta23.ThmD.Limit

open Filter Topology

noncomputable section

namespace Zeta23
namespace ThmDE

open ThmD ThmE Assembly

/-- **Theorem D for L(s,χ) at fixed λ ∈ (0,1), abstract zero configuration with the χ-inputs** —
all three lines. -/
theorem thmDChi_lam_abstract (Z : ZeroConfig) (κ : ℕ) {q : ℕ} (hq : 1 ≤ q) (cf : ℕ → ℂ)
    (hcu : CoeffUnimodular q cf) (H : PaperInputsChi κ q cf Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1) :
    (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (HD P.lam - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.N0star T (2 * T)) ∧
    (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 * cStar P.lam - 1 - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.N0s T (2 * T)) ∧
    (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (cStar P.lam - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.Nd T (2 * T)) := by
  have hLoc : ThmD.LocalHypsCoreDEventually P := localHypsCoreD_eventually hP
  have hTr := tracesBoundsDChi_concrete (Z := Z) hP hq hcu H hLoc
  have hc := tendsto_cRatio_concreteChi hP hq _ _ _ (tendsto_aD hP) (tendsto_bD hP)
    (tendsto_JD hP)
  have hc0 := cStar_pos hP.lam_pos hP.lam_le_one
  have ha : ∀ᶠ T in atTop, 1 / 2 ≤ (concreteDataDChi P κ q cf Z).aT T ∧
      (concreteDataDChi P κ q cf Z).aT T ≤ 1 :=
    (concreteFactsDChi hP hq hcu H hLoc).ab_range.mono fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  have hBlock := eventually_blockInputsD Z hP
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  obtain ⟨θ₀, hTail, hθ₀⟩ := eventually_tailPackageD_of_localCount Z hP hA₀ hloc
  have hNII := Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp := eventually_GzGpDChi Z hP H.EF
  have hId : ∀ᶠ T in atTop,
      trGtildeChi (P.atD T) κ q cf T = (concreteDataDChi P κ q cf Z).trG T ∧
      trGtildeSqChi (P.atD T) κ q cf T = (concreteDataDChi P κ q cf Z).trG2 T ∧
      (P.atD T).a T = (concreteDataDChi P κ q cf Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atD_trGtildeChi hP κ q cf T, Params.atD_trGtildeSqChi hP κ q cf T,
        Params.atD_a T hP⟩
  have hcalE := calE_tendsto_zero P hP.lam_pos hP.lam_le_one (zero_le_one.trans hP.one_le_w)
  refine ⟨?_, ?_, ?_⟩
  · have h := thmDChi_abstract Z κ hq cf P hP hlam H.RvM _ _ _ _ _ hTr hc0 hc ha hBlock θ₀ hTail hθ₀
      hNII hGzGp hId hcalE
    simpa only [HD, one_div] using h
  · exact thmDChi_simple_abstract Z κ hq cf P hP hlam H.RvM _ _ _ _ _ hTr hc0 hc ha hBlock θ₀ hTail
      hθ₀ hNII hGzGp hId
  · exact thmDChi_dist_abstract Z κ hq cf P hP hlam H.RvM _ _ _ _ _ hTr hc0 hc ha hBlock θ₀ hTail
      hθ₀ hNII hGzGp hId

/-! ## L(s,χ): fixed λ, then λ → 1⁻ — NO hypotheses -/

section Dirichlet

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **Theorem D for L(s,χ) at fixed λ ∈ (0,1)**, Thm-A line, UNCONDITIONAL. -/
theorem thmE_D_lam (hq : 1 < q) (hprim : χ.IsPrimitive) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD lam - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0starL χ T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  simpa [paramsOf] using (thmDChi_lam_abstract (LZeros (LSeam_of hq hprim)) (parity χ) (by omega) (coeff χ)
    (coeffUnimodular_of_primitive hq hprim) (paperInputsChi_L hq hprim) (paramsOf stdProfile lam)
    hP h1).1

/-- fixed λ, Thm-B line for L(s,χ), UNCONDITIONAL. -/
theorem thmE_D_simple_lam (hq : 1 < q) (hprim : χ.IsPrimitive) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 * cStar lam - 1 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0simpleL χ T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  simpa [paramsOf] using (thmDChi_lam_abstract (LZeros (LSeam_of hq hprim)) (parity χ) (by omega) (coeff χ)
    (coeffUnimodular_of_primitive hq hprim) (paperInputsChi_L hq hprim) (paramsOf stdProfile lam)
    hP h1).2.1

/-- fixed λ, Thm-C line for L(s,χ), UNCONDITIONAL. -/
theorem thmE_D_dist_lam (hq : 1 < q) (hprim : χ.IsPrimitive) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (cStar lam - ε) * (NcountL χ T (2 * T) : ℝ) ≤ NdistL χ T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  simpa [paramsOf] using (thmDChi_lam_abstract (LZeros (LSeam_of hq hprim)) (parity χ) (by omega) (coeff χ)
    (coeffUnimodular_of_primitive hq hprim) (paperInputsChi_L hq hprim) (paramsOf stdProfile lam)
    hP h1).2.2

/-- **[thm:E] "Theorem D holds likewise", first constant, NO hypotheses**: for every primitive
Dirichlet character χ mod q > 1, for every ε > 0 and all large T, at least
(2 − 1/c₁* − ε)·N_χ(T,2T) of the zeros of Mathlib's 'DirichletCharacter.LFunction χ' with
ordinate in (T,2T], counted with multiplicity, are matched by DISTINCT critical-line zeros
(2 − 1/c₁* = HD 1 = 3/2 − cot(1/√2)/√2 = 0.6725…). -/
theorem thmE_D₀ (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD 1 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0starL χ T (2 * T) :=
  eps_form_HD (N := fun T => (NcountL χ T (2 * T) : ℝ))
    (lower := fun T => (N0starL χ T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) fun lam h1 h2 => thmE_D_lam hq hprim (by linarith) h2

/-- the same with the constant written out: (3/2 − cot(1/√2)/√2 − ε)·N_χ ≤ N*_{0,χ}. -/
theorem thmE_D₀' (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 2 - (Real.sqrt 2)⁻¹ * (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹) - ε)
        * (NcountL χ T (2 * T) : ℝ) ≤ N0starL χ T (2 * T) := by
  rw [← HD_one]; exact thmE_D₀ hq hprim

/-- **[thm:E] "Theorem D holds likewise", second constant, NO hypotheses**:
N^s_{0,χ}(T,2T) ≥ (2c₁* − 1 − ε)·N_χ(T,2T) — simple AND on the line (0.5065…). -/
theorem thmE_D₀_simple (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 * cStar 1 - 1 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0simpleL χ T (2 * T) :=
  eps_form_twoCStar (N := fun T => (NcountL χ T (2 * T) : ℝ))
    (lower := fun T => (N0simpleL χ T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) fun lam h1 h2 => thmE_D_simple_lam hq hprim (by linarith) h2

/-- **[thm:E] "Theorem D holds likewise", third constant, NO hypotheses**:
N_{d,χ}(T,2T) ≥ (c₁* − ε)·N_χ(T,2T) — distinct zeros (0.7532…). -/
theorem thmE_D₀_dist (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (cStar 1 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ NdistL χ T (2 * T) :=
  eps_form_cStar (N := fun T => (NcountL χ T (2 * T) : ℝ))
    (lower := fun T => (NdistL χ T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) fun lam h1 h2 => thmE_D_dist_lam hq hprim (by linarith) h2

end Dirichlet

end ThmDE
end Zeta23

end
