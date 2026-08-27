/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmD/Final.lean — **Theorem D** (the paper §8.1 [thm:D], the Montgomery–Taylor optimal
window), headline forms.

  thmD₀        : ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (HD 1 − ε) · N(T,2T) ≤ N₀*(T,2T)         — NO hypotheses,
  thmD₀_simple : … (2·c₁* − 1 − ε) · N(T,2T) ≤ N₀ˢ(T,2T),
  thmD₀_dist   : … (c₁* − ε) · N(T,2T) ≤ N_d(T,2T),
with c₁* = cStar 1 = √2 tan(1/√2)/(1 + tan(1/√2)/√2) [eq:vstar] and
HD 1 = 2 − 1/c₁* = 3/2 − cot(1/√2)/√2 (Zeta23.ThmD.HD_one); cumulative (liminf over (0,T]) forms;
and the fixed-λ forms at every λ ∈ (0,1) with constants HD λ = 2 − 1/c*(λ), 2c*(λ) − 1, c*(λ).
(Numerically 0.67250…, 0.50659…, 0.75329… — decimals are not formalized; the constants enter exactly.
The last two are the Cauchy–Schwarz forms; the paper's [thm:D] states the multiplicity-aware
constants 2 − 1/c₁* = 0.67250… for N₀ˢ and (3 − 1/c₁*)/2 = 0.83625… for N_d, proved in
Zeta23/ThmD/Mult.lean.)

Assembly: the D-prime side 'tracesBoundsD_concrete' (Zeta23/ThmD/Concrete.lean, from PaperInputs and
BridgeD's eventual LocalHypsCore for φ_D), the zero side for the window-realizing family 'P.atD T'
(Zeta23/ThmD/ZeroSideD.lean), the limit cRatio(λ₁; a_D, b_D, J_D) → c*(λ) (Zeta23/ThmD/Limit.lean), the
§6 endgame with abstract ratio constant (Zeta23/ThmD/Endgame.lean), then ζ: Z := zetaZeroConfig with
'paperInputs_zeta' (Zeta23/Final.lean: Weil EF, RvM, MV, Γ all proved), λ → 1⁻ (Limit.eps_form_*),
and dyadic summation (Main.cumulative_of_dyadic).
-/
import Zeta23.Final
import Zeta23.ThmD.Endgame
import Zeta23.ThmD.Concrete
import Zeta23.ThmD.ZeroSideD
import Zeta23.ThmD.Limit

open Filter Topology

noncomputable section

namespace Zeta23
namespace ThmD

open Assembly

/-- **Theorem D at fixed λ ∈ (0,1), abstract zero configuration with the paper's inputs** —
all three lines, constants HD λ = 2 − 1/c*(λ), 2c*(λ) − 1, c*(λ). -/
theorem thmD_lam_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1) :
    (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (HD P.lam - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.N0star T (2 * T)) ∧
    (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 * cStar P.lam - 1 - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.N0s T (2 * T)) ∧
    (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (cStar P.lam - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.Nd T (2 * T)) := by
  have hLoc : LocalHypsCoreDEventually P := localHypsCoreD_eventually hP
  have hTr := tracesBoundsD_concrete (Z := Z) hP H hLoc
  have hc := tendsto_cRatio_concrete hP Z
  have hc0 := cStar_pos hP.lam_pos hP.lam_le_one
  have ha : ∀ᶠ T in atTop, 1 / 2 ≤ (concreteDataD P Z).aT T ∧ (concreteDataD P Z).aT T ≤ 1 :=
    (concreteFactsD hP H hLoc).ab_range.mono fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  have hBlock := eventually_blockInputsD Z hP
  obtain ⟨θ₀, hTail, hθ₀⟩ := eventually_tailPackageD Z H hP
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  have hNII := Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp := eventually_GzGpD Z H hP
  have hId : ∀ᶠ T in atTop, (P.atD T).trGtilde T = (concreteDataD P Z).trG T ∧
      (P.atD T).trGtildeSq T = (concreteDataD P Z).trG2 T ∧
      (P.atD T).a T = (concreteDataD P Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atD_trGtilde T hP, Params.atD_trGtildeSq T hP, Params.atD_a T hP⟩
  have hcalE := calE_tendsto_zero P hP.lam_pos hP.lam_le_one (zero_le_one.trans hP.one_le_w)
  refine ⟨?_, ?_, ?_⟩
  · have h := thmD_abstract Z H P hP hlam _ _ _ _ _ hTr hc0 hc ha hBlock θ₀ hTail hθ₀ hNII hGzGp
      hId hcalE
    simpa only [HD, one_div] using h
  · exact thmD_simple_abstract Z H P hP hlam _ _ _ _ _ hTr hc0 hc ha hBlock θ₀ hTail hθ₀ hNII
      hGzGp hId
  · exact thmD_dist_abstract Z H P hP hlam _ _ _ _ _ hTr hc0 hc ha hBlock θ₀ hTail hθ₀ hNII
      hGzGp hId

/-! ## ζ: fixed λ, then λ → 1⁻, then cumulative — NO hypotheses -/

section Zeta

/-- **Theorem D at fixed λ ∈ (0,1)**, Thm-A line, UNCONDITIONAL:
N₀*(T,2T) ≥ (2 − 1/c*(λ) − ε) N(T,2T) for all large T. -/
theorem thmD_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (HD lam - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  exact (thmD_lam_abstract zetaZeroConfig paperInputs_zeta (paramsOf stdProfile lam) hP h1).1

/-- fixed λ, Thm-B line, UNCONDITIONAL: N₀ˢ(T,2T) ≥ (2c*(λ) − 1 − ε) N(T,2T). -/
theorem thmD_simple_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 * cStar lam - 1 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  exact (thmD_lam_abstract zetaZeroConfig paperInputs_zeta (paramsOf stdProfile lam) hP h1).2.1

/-- fixed λ, Thm-C line, UNCONDITIONAL: N_d(T,2T) ≥ (c*(λ) − ε) N(T,2T). -/
theorem thmD_dist_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (cStar lam - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  exact (thmD_lam_abstract zetaZeroConfig paperInputs_zeta (paramsOf stdProfile lam) hP h1).2.2

/-- **Theorem D** [thm:D], UNCONDITIONAL: for every ε > 0 and all large T,
N₀*(T,2T) ≥ (2 − 1/c₁* − ε) N(T,2T), where 2 − 1/c₁* = HD 1 = 3/2 − cot(1/√2)/√2 (= 0.6725…):
at least that proportion of the nontrivial zeros of Mathlib's riemannZeta with T < Im ρ ≤ 2T, counted
with multiplicity, are matched by DISTINCT zeros on the critical line. -/
theorem thmD₀ :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (HD 1 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  eps_form_HD (N := fun T => (Ncount T (2 * T) : ℝ)) (lower := fun T => (N0star T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) fun lam h1 h2 => thmD_lam (by linarith) h2

/-- **Theorem D**, the constant written out: (3/2 − cot(1/√2)/√2 − ε) N(T,2T) ≤ N₀*(T,2T). -/
theorem thmD₀' :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 2 - (Real.sqrt 2)⁻¹ * (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹) - ε)
        * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) := by
  rw [← HD_one]; exact thmD₀

/-- **Theorem D**, simple-zeros line [thm:D], UNCONDITIONAL: N₀ˢ(T,2T) ≥ (2c₁* − 1 − ε) N(T,2T)
(= 0.5065…): at least that proportion are SIMPLE zeros ON the line. -/
theorem thmD₀_simple :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 * cStar 1 - 1 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  eps_form_twoCStar (N := fun T => (Ncount T (2 * T) : ℝ))
    (lower := fun T => (N0simple T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) fun lam h1 h2 => thmD_simple_lam (by linarith) h2

/-- **Theorem D**, distinct-zeros line [thm:D], UNCONDITIONAL: N_d(T,2T) ≥ (c₁* − ε) N(T,2T)
(= 0.7532…). -/
theorem thmD₀_dist :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (cStar 1 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  eps_form_cStar (N := fun T => (Ncount T (2 * T) : ℝ)) (lower := fun T => (Ndist T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) fun lam h1 h2 => thmD_dist_lam (by linarith) h2

/-- **Theorem D**, cumulative, UNCONDITIONAL: liminf_{T→∞} N₀*(T)/N(T) ≥ 2 − 1/c₁*. -/
theorem thmD₀_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (HD 1 - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM (fun _ _ _ => N0star_add' zetaSeam) thmD₀

/-- cumulative simple-zeros line: liminf N₀ˢ(T)/N(T) ≥ 2c₁* − 1. -/
theorem thmD₀_simple_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 * cStar 1 - 1 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM (fun _ _ _ => N0simple_add' zetaSeam)
    thmD₀_simple

/-- cumulative distinct-zeros line: liminf N_d(T)/N(T) ≥ c₁*. -/
theorem thmD₀_dist_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (cStar 1 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T :=
  cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM (fun _ _ _ => Ndist_add' zetaSeam) thmD₀_dist

end Zeta

end ThmD
end Zeta23

end
