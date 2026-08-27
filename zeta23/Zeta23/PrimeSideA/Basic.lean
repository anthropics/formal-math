/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/
import Zeta23.PrimeSideA.Defs


-- Contains: LocalHyps, EventuallyAt, the 𝓜-bilinearity/sup-bound lemmas, the large-T regime
-- lemmas, and all per-grid-point lemmas for [prop:trace].

/-!
# Prime side, part A — paper §5 [sec:prime]:  [prop:trace], [lem:ends], [eq:Msplit], [prop:mumu], [prop:cross]

Seam with `PrimeSideB.lean` ([prop:PP], [thm:traces]): see the header of
`Zeta23/PrimeSideA/Defs.lean`.  Everything here is ζ-free: the zeros never
appear in §5 ("In this section the zeros play no role", §5); `N(T,2T)` enters [prop:trace]
only through [eq:muints] + [eq:RvM], which we take as hypotheses on an abstract real `N`.

## Shape of the results
All error terms are explicit inequalities, uniform in `T`:
  `∃ C, EventuallyAt cϱ lam (fun p F => |lhs p F − main p F| ≤ C * err p)`
where `EventuallyAt cϱ lam P` means: there is `T₀` such that `P p F` holds for every parameter set
`p` with `p.lam = lam`, `T₀ ≤ p.T` and every taper datum `F` satisfying `LocalHyps cϱ p F`.
So `C` and `T₀` may depend on `c_ϱ`, on the constants inside H-Γ/H-cheb, and on `λ` — the paper
has `C` depending on ϱ only and `T₀ = T₀(λ)` (§5.5); ours is the (weaker, sufficient at fixed λ)
reading.  This is a deviation from the paper.

## Hypotheses consumed (all proved elsewhere in the repository; none is a Lean axiom)
* `Zeta23.GammaFacts` (H-Γ [eq:mufacts]+[eq:muints]) and `Zeta23.ChebyshevMertens` (H-cheb
  [lem:cheb]) — Zeta23/Hypotheses.lean, verbatim (fields of `PaperInputs`).
* `LocalHyps cϱ p F` — taper/test-family facts [eq:psidef], [eq:abdef], [eq:gbounds], [eq:Phi2FT],
                      `∫φ̂² = 2πaL`, `Φ(0) = aL`, `∫Φ² = 2πbL`;
                      [lem:poisson] (★); [eq:PiPfacts] for Π_X;
                      parameter regime [eq:wrange], `0<λ≤1`.
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace PrimeSide

/-! ## Hypothesis packages

H-Γ and H-cheb are Zeta23/Hypotheses.lean's `Zeta23.GammaFacts` and `Zeta23.ChebyshevMertens` (about the
concrete `Zeta23.mu` and Λ-sums), taken verbatim.  The taper/test-family facts are packaged here: -/

/-- ψ(r) := min(L, 2/|r|, c_ϱ/(w r²)) [eq:psidef], with the r = 0 guard
(= `Zeta23.Params.psi` / `Taper.psi'` by `rfl` under the bridge).  Majorant for both `φ̂` and `Φ`. -/
def psiA (cϱ : ℝ) (p : Setting) (r : ℝ) : ℝ :=
  if r = 0 then p.L else min p.L (min (2 / |r|) (cϱ / (p.w * r ^ 2)))

/-- The facts about the test family at parameters `p` used in §5, each tagged with
its paper label; `cϱ` is the profile constant `c_ϱ = 4‖ϱ'‖_∞ + 4‖ϱ''‖₁ ≥ 4` of [eq:phinorms]
(= `Zeta23.Params.crho`).  These facts are supplied by Taper.lean / Poisson.lean and
PiFacts.lean: this structure is instantiated elsewhere in the repository (a theorem
`LocalHyps P.crho ⟨T, P.lam, P.w⟩ ⟨P.phiHatR T, P.PhiR T, P.Aphi T, P.g T, P.a T, P.b T⟩` for
valid `P` and large `T`), not assumed. -/
structure LocalHyps (cϱ : ℝ) (p : Setting) (F : LocalFun) : Prop where
  /-- [eq:phinorms] `c_ϱ ≥ 4`. -/
  four_le_cϱ : 4 ≤ cϱ
  /-- `0 < λ ≤ 1` [Notation]. -/
  lam_pos : 0 < p.lam
  lam_le_one : p.lam ≤ 1
  /-- [eq:wrange] `1 ≤ w ≤ L/8` (forces `L ≥ 8`). -/
  one_le_w : 1 ≤ p.w
  w_le : p.w ≤ p.L / 8
  /-- "T is large": `l ≥ 1`, i.e. `T ≥ 2πe`. -/
  one_le_l : 1 ≤ p.l
  /-- φ̂ real-analytic facts: continuity; evenness (φ even) [§2.2 "φ̂ and Φ are real, even, entire"]. -/
  phiHat_cont : Continuous F.phiHat
  phiHat_even : ∀ r, F.phiHat (-r) = F.phiHat r
  /-- [eq:psidef] `|φ̂(r)| ≤ ψ(r) := min(L, 2/|r|, c_ϱ/(w r²))`, split into three division-free bounds. -/
  phiHat_le_L : ∀ r, |F.phiHat r| ≤ p.L
  phiHat_le_inv : ∀ r, |F.phiHat r| * |r| ≤ 2
  phiHat_le_sq : ∀ r, |F.phiHat r| * r ^ 2 ≤ cϱ / p.w
  /-- Integrability consequences of [eq:psidef] (`φ̂² ≤ ψ² ≤ min(L², c_ϱ²/(w²r⁴))`), and
  [eq:psiints] in the packaged form `∫ φ̂(r)²|r| dr ≤ ∫ ψ²|r| = 8 + 8 log(c_ϱL/4w)` (§2.2, used at
  §5.2 "∫ φ̂(r)²|r| dr ≪ log L"). -/
  phiHat_sq_integrable : Integrable (fun r => F.phiHat r ^ 2)
  phiHat_sq_mul_abs_integrable : Integrable (fun r => F.phiHat r ^ 2 * |r|)
  integral_phiHat_sq_mul_abs_le :
    ∫ r, F.phiHat r ^ 2 * |r| ≤ 8 + 8 * Real.log (cϱ * p.L / (4 * p.w))
  /-- also from [eq:psidef]: `φ̂(r)²r² ≤ min(4, (c_ϱ/w)²/r²)`, so `∫ φ̂(r)² r² dr ≤ 8 + 2(c_ϱ/w)²`
  (used for the `|r| > τ_k/2` tails at §5.2 in place of the paper's sharper r⁻⁴ bound). -/
  phiHat_sq_mul_sq_integrable : Integrable (fun r => F.phiHat r ^ 2 * r ^ 2)
  integral_phiHat_sq_mul_sq_le : ∫ r, F.phiHat r ^ 2 * r ^ 2 ≤ 8 + 2 * (cϱ / p.w) ^ 2
  /-- `∫ φ̂(r)² dr = 2π ∫ φ² = 2π a L` [prop:trace proof, §5.2; Plancherel in the paper's
  convention `∫ f ḡ = (2π)⁻¹ ∫ f̂ conj ĝ` + eq:abdef]. -/
  phiHat_sq_integral : ∫ r, F.phiHat r ^ 2 = 2 * π * F.a * p.L
  /-- `φ̂² = Â_φ` on ℝ [§2.2] + Fourier inversion, in the real form used at §5.2:
  `∫ φ̂(r)² cos(ry) dr = 2π A_φ(y)` (`φ̂²` even, `A_φ` even, continuous, supported in `[−L,L]`). -/
  phiHat_sq_fourier : ∀ y, ∫ r, F.phiHat r ^ 2 * Real.cos (r * y) = 2 * π * F.Aphi y
  /-- [eq:gbounds] `(L−2w−|y|)₊ ≤ g(y) ≤ A_φ(y) ≤ (L−|y|)₊`. -/
  g_lower : ∀ y, max (p.L - 2 * p.w - |y|) 0 ≤ F.g y
  g_le_Aphi : ∀ y, F.g y ≤ F.Aphi y
  Aphi_le : ∀ y, F.Aphi y ≤ max (p.L - |y|) 0
  /-- Φ facts: `Φ` is C¹ (indeed entire), even [§2.2]. -/
  Phi_contDiff : ContDiff ℝ 1 F.Phi
  Phi_even : ∀ r, F.Phi (-r) = F.Phi r
  /-- [eq:psidef] `|Φ(r)| ≤ ψ(r)`, three division-free bounds. -/
  Phi_le_L : ∀ r, |F.Phi r| ≤ p.L
  Phi_le_inv : ∀ r, |F.Phi r| * |r| ≤ 2
  Phi_le_sq : ∀ r, |F.Phi r| * r ^ 2 ≤ cϱ / p.w
  /-- Integrability consequences of [eq:psidef] for Φ, and [eq:psiints] packaged as
  `∫ Φ(x)²|x| dx ≤ 8 + 8 log(c_ϱL/4w)` (§5.4 "∫Φ(x)²|x|dx ≪ log L (by (eq:psidef), (eq:psiints))"). -/
  Phi_sq_integrable : Integrable (fun x => F.Phi x ^ 2)
  Phi_sq_mul_abs_integrable : Integrable (fun x => F.Phi x ^ 2 * |x|)
  integral_Phi_sq_mul_abs_le :
    ∫ x, F.Phi x ^ 2 * |x| ≤ 8 + 8 * Real.log (cϱ * p.L / (4 * p.w))
  /-- second moment of `Φ²` (same [eq:psidef] path as the `φ̂` version; needed against the
  `10r²/t` term of `mu_increment_bound` in [prop:mumu]). -/
  Phi_sq_mul_sq_integrable : Integrable (fun x => F.Phi x ^ 2 * x ^ 2)
  integral_Phi_sq_mul_sq_le : ∫ x, F.Phi x ^ 2 * x ^ 2 ≤ 8 + 2 * (cϱ / p.w) ^ 2
  /-- `Φ(0) = aL` [§2.2]. -/
  Phi_zero : F.Phi 0 = F.a * p.L
  /-- `∫_ℝ Φ² = 2π g(0) = 2π b L` [§2.2]. -/
  Phi_sq_integral : ∫ x, F.Phi x ^ 2 = 2 * π * F.b * p.L
  /-- [eq:Phi2FT] `∫_ℝ Φ(x)² e^{ixy} dx = 2π g(y)` (§5.4), real form (`Φ²`, `g` even). -/
  Phi_sq_fourier : ∀ y, ∫ x, F.Phi x ^ 2 * Real.cos (x * y) = 2 * π * F.g y
  /-- [lem:poisson] (★) `Σ_{k∈ℤ} φ̂(τ−τ_k) φ̂(τ'−τ_k) = L Φ(τ−τ')` (§2.2). -/
  poisson : ∀ τ τ', HasSum (fun k : ℤ => F.phiHat (τ - p.tau k) * F.phiHat (τ' - p.tau k))
    (p.L * F.Phi (τ - τ'))
  /-- [eq:abdef] `1 − 2w/L ≤ b ≤ a ≤ 1`. -/
  b_lower : 1 - 2 * p.w / p.L ≤ F.b
  b_le_a : F.b ≤ F.a
  a_le_one : F.a ≤ 1
  /-- [eq:psidef] in majorant form, with the [eq:psiints] integrals (`Ψ₀ = 4 + 2log(c_ϱL/4w)`,
  `∫ψ² ≤ 8L`) — fields match `Zeta23.Params.psi'_integrable / psi'_sq_integrable /
  integral_psi'_Ioi_le / integral_psi'_sq_le` in Zeta23/Taper.lean (consumed by [lem:ends]). -/
  psi_integrable : Integrable (psiA cϱ p)
  psi_sq_integrable : Integrable (fun r => psiA cϱ p r ^ 2)
  integral_psi_Ioi_le : ∫ r in Set.Ioi 0, psiA cϱ p r ≤ 4 + 2 * Real.log (cϱ * p.L / (4 * p.w))
  integral_psi_sq_le : ∫ r, psiA cϱ p r ^ 2 ≤ 8 * p.L
  /-- `|φ̂| ≤ ψ` and `|Φ| ≤ ψ` [eq:psidef] in the majorant form used by [lem:ends]. -/
  phiHat_le_psi : ∀ r, |F.phiHat r| ≤ psiA cϱ p r
  Phi_le_psi : ∀ r, |F.Phi r| ≤ psiA cϱ p r
  /-- Π_X is continuous and [eq:PiPfacts] `|Π_X(τ)| ≤ 3√X/(1+|τ|)` (§2.1), for the concrete
  `Zeta23.PiX X` [eq:Pidef] — via `PiX_bound` (holds for all `X ≥ 1`) and `PiX_continuous`. -/
  PiX_cont : Continuous (Zeta23.PiX p.X)
  PiX_bound : ∀ τ, |Zeta23.PiX p.X τ| ≤ 3 * Real.sqrt p.X / (1 + |τ|)

/-- "For `T ≥ T₀`, uniformly": `P p F` holds for every parameter set `p` at bandwidth ratio `lam`
with `T₀ ≤ p.T` and every functional datum `F` satisfying the local hypotheses. -/
def EventuallyAt (cϱ lam : ℝ) (P : Setting → LocalFun → Prop) : Prop :=
  ∃ T₀ : ℝ, ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₀ ≤ p.T → LocalHyps cϱ p F → P p F

/-! ### Bilinearity and symmetry of 𝓜[·,·] (§5.4: "a symmetric bilinear form (Φ² is even)") -/

section MformLemmas
variable {Φ : ℝ → ℝ} {T : ℝ}

lemma Mform_integrableOn (hΦ : Continuous Φ) {u v : ℝ → ℝ} (hu : Continuous u)
    (hv : Continuous v) :
    IntegrableOn (fun q : ℝ × ℝ => (Φ (q.1 - q.2)) ^ 2 * u q.1 * v q.2)
      ((Set.Icc T (2 * T)) ×ˢ (Set.Icc T (2 * T))) := by
  apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  apply Continuous.continuousOn
  fun_prop

lemma Mform_add_left (hΦ : Continuous Φ) {u v w : ℝ → ℝ} (hu : Continuous u)
    (hv : Continuous v) (hw : Continuous w) :
    Mform Φ T (u + v) w = Mform Φ T u w + Mform Φ T v w := by
  unfold Mform
  rw [← integral_add (Mform_integrableOn hΦ hu hw) (Mform_integrableOn hΦ hv hw)]
  congr 1; funext q; simp only [Pi.add_apply]; ring

lemma Mform_add_right (hΦ : Continuous Φ) {u v w : ℝ → ℝ} (hu : Continuous u)
    (hv : Continuous v) (hw : Continuous w) :
    Mform Φ T w (u + v) = Mform Φ T w u + Mform Φ T w v := by
  unfold Mform
  rw [← integral_add (Mform_integrableOn hΦ hw hu) (Mform_integrableOn hΦ hw hv)]
  congr 1; funext q; simp only [Pi.add_apply]; ring

lemma Mform_const_mul_left (c : ℝ) (u w : ℝ → ℝ) :
    Mform Φ T (fun x => c * u x) w = c * Mform Φ T u w := by
  unfold Mform
  rw [← integral_const_mul]
  congr 1; funext q; ring

lemma Mform_const_mul_right (c : ℝ) (u w : ℝ → ℝ) :
    Mform Φ T w (fun x => c * u x) = c * Mform Φ T w u := by
  unfold Mform
  rw [← integral_const_mul]
  congr 1; funext q; ring

/-- Symmetry `𝓜[u,v] = 𝓜[v,u]`: swap `(τ,τ') ↦ (τ',τ)` on the square and use that `Φ` is even. -/
lemma Mform_comm (hΦe : ∀ r, Φ (-r) = Φ r) (u v : ℝ → ℝ) :
    Mform Φ T u v = Mform Φ T v u := by
  unfold Mform
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  conv_rhs => rw [← integral_prod_swap]
  congr 1; funext q
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [show q.2 - q.1 = -(q.1 - q.2) by ring, hΦe]; ring

/-- The trinomial expansion behind [eq:Msplit]. -/
lemma Mform_trinomial (hΦ : Continuous Φ) (hΦe : ∀ r, Φ (-r) = Φ r) {u v w : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
    Mform Φ T (u + v + w) (u + v + w) =
      Mform Φ T u u + Mform Φ T w w + 2 * Mform Φ T u w + 2 * Mform Φ T u v
        + 2 * Mform Φ T w v + Mform Φ T v v := by
  have huv : Continuous (u + v) := hu.add hv
  have huvw : Continuous (u + v + w) := huv.add hw
  rw [Mform_add_left hΦ huv hw huvw, Mform_add_left hΦ hu hv huvw,
    Mform_add_right hΦ huv hw hu, Mform_add_right hΦ hu hv hu,
    Mform_add_right hΦ huv hw hv, Mform_add_right hΦ hu hv hv,
    Mform_add_right hΦ huv hw hw, Mform_add_right hΦ hu hv hw,
    Mform_comm hΦe v u, Mform_comm hΦe w u, Mform_comm hΦe v w]
  ring

end MformLemmas


/-! ### The "insert sup bounds" estimate for 𝓜[·,·]  (§5.4) -/

section SupBound
variable {Φ : ℝ → ℝ} {T : ℝ}

/-- `∫_S Φ(x−y)² dy ≤ ∫_ℝ Φ²` (translation invariance and `Φ² ≥ 0`); this is
`sup_τ ∫_I Φ(τ−τ')² dτ' ≤ 2πbL` of §5.4. -/
lemma setIntegral_sq_shift_le (hΦint : Integrable (fun x => Φ x ^ 2)) (S : Set ℝ) (x : ℝ) :
    ∫ y in S, Φ (x - y) ^ 2 ≤ ∫ y, Φ y ^ 2 := by
  calc ∫ y in S, Φ (x - y) ^ 2 ≤ ∫ y, Φ (x - y) ^ 2 :=
        setIntegral_le_integral (hΦint.comp_sub_left x)
          (Filter.Eventually.of_forall fun y => sq_nonneg _)
    _ = ∫ y, Φ y ^ 2 := integral_sub_left_eq_self (fun y => Φ y ^ 2) volume x

/-- **Sup-bound for 𝓜** [prop:cross proof, §5.4: "the remaining three bounds follow by inserting
these sup bounds into the definition of 𝓜[·,·] (an integral over a region of τ'-length T)"]:
if `|u| ≤ B_u` and `|v| ≤ B_v` on `I = [T,2T]` then `|𝓜[u,v]| ≤ B_u B_v · T · ∫_ℝ Φ²`. -/
lemma abs_Mform_le (hT : 0 ≤ T) (hΦ : Continuous Φ) {u v : ℝ → ℝ} (hu : Continuous u)
    (hv : Continuous v) (hΦint : Integrable (fun x => Φ x ^ 2)) {Bu Bv : ℝ}
    (hBu : ∀ τ ∈ Set.Icc T (2 * T), |u τ| ≤ Bu) (hBv : ∀ τ ∈ Set.Icc T (2 * T), |v τ| ≤ Bv) :
    |Mform Φ T u v| ≤ Bu * Bv * (T * ∫ x, Φ x ^ 2) := by
  unfold Mform
  set S := Set.Icc T (2 * T) with hS
  have hSm : MeasurableSet S := measurableSet_Icc
  have hTS : T ∈ S := ⟨le_rfl, by linarith⟩
  have hBu0 : 0 ≤ Bu := (abs_nonneg _).trans (hBu T hTS)
  have hBv0 : 0 ≤ Bv := (abs_nonneg _).trans (hBv T hTS)
  have hint := Mform_integrableOn (T := T) hΦ hu hv
  have hint3 : IntegrableOn (fun q : ℝ × ℝ => Φ (q.1 - q.2) ^ 2) (S ×ˢ S) := by
    have := Mform_integrableOn (T := T) hΦ (continuous_const (y := (1:ℝ)))
      (continuous_const (y := (1:ℝ)))
    simpa only [mul_one] using this
  have hint2 : IntegrableOn (fun q : ℝ × ℝ => Φ (q.1 - q.2) ^ 2 * (Bu * Bv)) (S ×ˢ S) :=
    hint3.mul_const _
  calc |∫ q in S ×ˢ S, Φ (q.1 - q.2) ^ 2 * u q.1 * v q.2|
      ≤ ∫ q in S ×ˢ S, |Φ (q.1 - q.2) ^ 2 * u q.1 * v q.2| := abs_integral_le_integral_abs
    _ ≤ ∫ q in S ×ˢ S, Φ (q.1 - q.2) ^ 2 * (Bu * Bv) := by
        apply setIntegral_mono_on hint.abs hint2 (hSm.prod hSm)
        rintro ⟨x, y⟩ ⟨hx, hy⟩
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (hBu x hx) (hBv y hy) (abs_nonneg _) hBu0) (sq_nonneg _)
    _ = (∫ q in S ×ˢ S, Φ (q.1 - q.2) ^ 2) * (Bu * Bv) := integral_mul_const _ _
    _ ≤ (T * ∫ x, Φ x ^ 2) * (Bu * Bv) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hBu0 hBv0)
        rw [Measure.volume_eq_prod, setIntegral_prod _ hint3]
        calc ∫ x in S, ∫ y in S, Φ (x - y) ^ 2
            ≤ ∫ x in S, (∫ y, Φ y ^ 2 : ℝ) := by
              apply integral_mono_of_nonneg
              · exact Filter.Eventually.of_forall fun x =>
                  integral_nonneg fun y => sq_nonneg _
              · rw [hS]; exact integrable_const _
              · exact Filter.Eventually.of_forall fun x => setIntegral_sq_shift_le hΦint S x
          _ = T * ∫ y, Φ y ^ 2 := by
              rw [setIntegral_const, smul_eq_mul, hS, Real.volume_real_Icc,
                max_eq_left (by linarith)]
              ring
    _ = Bu * Bv * (T * ∫ x, Φ x ^ 2) := by ring

end SupBound

lemma PX_continuous (X : ℝ) : Continuous (Zeta23.PX X) := by
  unfold Zeta23.PX
  fun_prop

/-! ### The large-T regime: elementary consequences of the hypotheses -/

section Regime
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

lemma Setting.X_pos (p : Setting) : 0 < p.X := Real.exp_pos _

/-- `l ≥ l₀` once `T ≥ 2π e^{l₀}`. -/
lemma Setting.le_l_of_T {p : Setting} {l₀ : ℝ} (hT : 2 * π * Real.exp l₀ ≤ p.T) : l₀ ≤ p.l := by
  have h2π : (0:ℝ) < 2 * π := by positivity
  have h : Real.exp l₀ ≤ p.T / (2 * π) := by rw [le_div_iff₀ h2π]; linarith
  calc l₀ = Real.log (Real.exp l₀) := (Real.log_exp _).symm
    _ ≤ Real.log (p.T / (2 * π)) := Real.log_le_log (Real.exp_pos _) h
    _ = p.l := rfl

/-- `T ≥ 2π` (in particular `T ≥ 1`, `T > 0`) once `T ≥ 2π e^{l₀}` with `l₀ ≥ 0`. -/
lemma Setting.twopi_le_T {p : Setting} {l₀ : ℝ} (hl₀ : 0 ≤ l₀) (hT : 2 * π * Real.exp l₀ ≤ p.T) :
    2 * π ≤ p.T := by
  have : (1:ℝ) ≤ Real.exp l₀ := Real.one_le_exp hl₀
  nlinarith [Real.pi_pos]

lemma Setting.one_le_T {p : Setting} {l₀ : ℝ} (hl₀ : 0 ≤ l₀) (hT : 2 * π * Real.exp l₀ ≤ p.T) :
    1 ≤ p.T := by
  have := Setting.twopi_le_T hl₀ hT; linarith [Real.pi_gt_three]

/-- `X ≥ x₀` once `T ≥ 2π exp(|x₀|/λ)` (`X = (T/2π)^λ → ∞`; this is the "T ≥ T₀(λ)" of §5). -/
lemma Setting.le_X_of_T {p : Setting} (hlam : 0 < p.lam) {x₀ : ℝ}
    (hT : 2 * π * Real.exp (|x₀| / p.lam) ≤ p.T) : x₀ ≤ p.X := by
  have hl : |x₀| / p.lam ≤ p.l := Setting.le_l_of_T hT
  have h1 : |x₀| ≤ p.lam * p.l := by rwa [div_le_iff₀' hlam] at hl
  calc x₀ ≤ |x₀| := le_abs_self _
    _ ≤ p.lam * p.l := h1
    _ ≤ Real.exp (p.lam * p.l) := by linarith [Real.add_one_le_exp (p.lam * p.l)]
    _ = p.X := rfl

lemma LocalHyps.eight_le_L (hF : LocalHyps cϱ p F) : 8 ≤ p.L := by
  linarith [hF.one_le_w, hF.w_le]

lemma LocalHyps.L_pos (hF : LocalHyps cϱ p F) : 0 < p.L := by linarith [hF.eight_le_L]

lemma LocalHyps.b_pos (hF : LocalHyps cϱ p F) : 0 < F.b := by
  have h1 : 2 * p.w / p.L ≤ 1 / 4 := by
    rw [div_le_iff₀ hF.L_pos]; linarith [hF.w_le]
  linarith [hF.b_lower]

lemma LocalHyps.a_pos (hF : LocalHyps cϱ p F) : 0 < F.a := hF.b_pos.trans_le hF.b_le_a

/-- `∫Φ² = 2πbL ≤ 2πL`. -/
lemma LocalHyps.integral_Phi_sq_le (hF : LocalHyps cϱ p F) : ∫ x, F.Phi x ^ 2 ≤ 2 * π * p.L := by
  rw [hF.Phi_sq_integral]
  have hb1 : F.b ≤ 1 := hF.b_le_a.trans hF.a_le_one
  have hL := hF.L_pos
  calc 2 * π * F.b * p.L = (2 * π * p.L) * F.b := by ring
    _ ≤ (2 * π * p.L) * 1 := by gcongr
    _ = 2 * π * p.L := mul_one _

/-- [eq:PiPfacts] on `I`: `|Π_X| ≤ 3√X/T` (§5.2, §5.4). -/
lemma LocalHyps.PiX_le_on_I (hF : LocalHyps cϱ p F) (hT : 0 < p.T) :
    ∀ τ ∈ Set.Icc p.T (2 * p.T), |Zeta23.PiX p.X τ| ≤ 3 * Real.sqrt p.X / p.T := by
  intro τ hτ
  refine (hF.PiX_bound τ).trans ?_
  apply div_le_div_of_nonneg_left (by positivity) hT
  rw [abs_of_nonneg (by linarith [hτ.1])]; linarith [hτ.1]

/-! ### Window-generic core of the taper hypotheses (paper §7.1 [subsec:MT])

"Nothing in Sections 4–5 used that φ is flat-topped" — except the [eq:gbounds] plateau lower
bound and the [eq:abdef] lower bound on b.  LocalHypsCore is LocalHyps minus exactly those two
facts, with the window-generic replacements g_nonneg and b_ge_half (both hold for the
Montgomery–Taylor window of [thm:D], which does not satisfy LocalHyps).  Surviving field names
are identical to LocalHyps'.  The window-generic §5 results can be re-typed over this
structure; the structure itself is purely additive. -/

structure LocalHypsCore (cϱ : ℝ) (p : Setting) (F : LocalFun) : Prop where
  /-- [eq:phinorms] `c_ϱ ≥ 4`. -/
  four_le_cϱ : 4 ≤ cϱ
  /-- `0 < λ ≤ 1` [Notation]. -/
  lam_pos : 0 < p.lam
  lam_le_one : p.lam ≤ 1
  /-- [eq:wrange] `1 ≤ w ≤ L/8` (forces `L ≥ 8`). -/
  one_le_w : 1 ≤ p.w
  w_le : p.w ≤ p.L / 8
  /-- "T is large": `l ≥ 1`, i.e. `T ≥ 2πe`. -/
  one_le_l : 1 ≤ p.l
  /-- φ̂ real-analytic facts: continuity; evenness (φ even) [§2.2 "φ̂ and Φ are real, even, entire"]. -/
  phiHat_cont : Continuous F.phiHat
  phiHat_even : ∀ r, F.phiHat (-r) = F.phiHat r
  /-- [eq:psidef] `|φ̂(r)| ≤ ψ(r) := min(L, 2/|r|, c_ϱ/(w r²))`, split into three division-free bounds. -/
  phiHat_le_L : ∀ r, |F.phiHat r| ≤ p.L
  phiHat_le_inv : ∀ r, |F.phiHat r| * |r| ≤ 2
  phiHat_le_sq : ∀ r, |F.phiHat r| * r ^ 2 ≤ cϱ / p.w
  /-- Integrability consequences of [eq:psidef] (`φ̂² ≤ ψ² ≤ min(L², c_ϱ²/(w²r⁴))`), and
  [eq:psiints] in the packaged form `∫ φ̂(r)²|r| dr ≤ ∫ ψ²|r| = 8 + 8 log(c_ϱL/4w)` (§2.2, used at
  §5.2 "∫ φ̂(r)²|r| dr ≪ log L"). -/
  phiHat_sq_integrable : Integrable (fun r => F.phiHat r ^ 2)
  phiHat_sq_mul_abs_integrable : Integrable (fun r => F.phiHat r ^ 2 * |r|)
  integral_phiHat_sq_mul_abs_le :
    ∫ r, F.phiHat r ^ 2 * |r| ≤ 8 + 8 * Real.log (cϱ * p.L / (4 * p.w))
  /-- also from [eq:psidef]: `φ̂(r)²r² ≤ min(4, (c_ϱ/w)²/r²)`, so `∫ φ̂(r)² r² dr ≤ 8 + 2(c_ϱ/w)²`
  (used for the `|r| > τ_k/2` tails at §5.2 in place of the paper's sharper r⁻⁴ bound). -/
  phiHat_sq_mul_sq_integrable : Integrable (fun r => F.phiHat r ^ 2 * r ^ 2)
  integral_phiHat_sq_mul_sq_le : ∫ r, F.phiHat r ^ 2 * r ^ 2 ≤ 8 + 2 * (cϱ / p.w) ^ 2
  /-- `∫ φ̂(r)² dr = 2π ∫ φ² = 2π a L` [prop:trace proof, §5.2; Plancherel in the paper's
  convention `∫ f ḡ = (2π)⁻¹ ∫ f̂ conj ĝ` + eq:abdef]. -/
  phiHat_sq_integral : ∫ r, F.phiHat r ^ 2 = 2 * π * F.a * p.L
  /-- `φ̂² = Â_φ` on ℝ [§2.2] + Fourier inversion, in the real form used at §5.2:
  `∫ φ̂(r)² cos(ry) dr = 2π A_φ(y)` (`φ̂²` even, `A_φ` even, continuous, supported in `[−L,L]`). -/
  phiHat_sq_fourier : ∀ y, ∫ r, F.phiHat r ^ 2 * Real.cos (r * y) = 2 * π * F.Aphi y
  /-- window-generic remnant of [eq:gbounds]: `g ≥ 0` and `g ≤ A_φ ≤ (L−|y|)₊`
  (the flat-top plateau lower bound `(L−2w−|y|)₊ ≤ g` is NOT here — see §7.1). -/
  g_nonneg : ∀ y, 0 ≤ F.g y
  g_le_Aphi : ∀ y, F.g y ≤ F.Aphi y
  Aphi_le : ∀ y, F.Aphi y ≤ max (p.L - |y|) 0
  /-- Φ facts: `Φ` is C¹ (indeed entire), even [§2.2]. -/
  Phi_contDiff : ContDiff ℝ 1 F.Phi
  Phi_even : ∀ r, F.Phi (-r) = F.Phi r
  /-- [eq:psidef] `|Φ(r)| ≤ ψ(r)`, three division-free bounds. -/
  Phi_le_L : ∀ r, |F.Phi r| ≤ p.L
  Phi_le_inv : ∀ r, |F.Phi r| * |r| ≤ 2
  Phi_le_sq : ∀ r, |F.Phi r| * r ^ 2 ≤ cϱ / p.w
  /-- Integrability consequences of [eq:psidef] for Φ, and [eq:psiints] packaged as
  `∫ Φ(x)²|x| dx ≤ 8 + 8 log(c_ϱL/4w)` (§5.4 "∫Φ(x)²|x|dx ≪ log L (by (eq:psidef), (eq:psiints))"). -/
  Phi_sq_integrable : Integrable (fun x => F.Phi x ^ 2)
  Phi_sq_mul_abs_integrable : Integrable (fun x => F.Phi x ^ 2 * |x|)
  integral_Phi_sq_mul_abs_le :
    ∫ x, F.Phi x ^ 2 * |x| ≤ 8 + 8 * Real.log (cϱ * p.L / (4 * p.w))
  /-- second moment of `Φ²` (same [eq:psidef] path as the `φ̂` version; needed against the
  `10r²/t` term of `mu_increment_bound` in [prop:mumu]). -/
  Phi_sq_mul_sq_integrable : Integrable (fun x => F.Phi x ^ 2 * x ^ 2)
  integral_Phi_sq_mul_sq_le : ∫ x, F.Phi x ^ 2 * x ^ 2 ≤ 8 + 2 * (cϱ / p.w) ^ 2
  /-- `Φ(0) = aL` [§2.2]. -/
  Phi_zero : F.Phi 0 = F.a * p.L
  /-- `∫_ℝ Φ² = 2π g(0) = 2π b L` [§2.2]. -/
  Phi_sq_integral : ∫ x, F.Phi x ^ 2 = 2 * π * F.b * p.L
  /-- [eq:Phi2FT] `∫_ℝ Φ(x)² e^{ixy} dx = 2π g(y)` (§5.4), real form (`Φ²`, `g` even). -/
  Phi_sq_fourier : ∀ y, ∫ x, F.Phi x ^ 2 * Real.cos (x * y) = 2 * π * F.g y
  /-- [lem:poisson] (★) `Σ_{k∈ℤ} φ̂(τ−τ_k) φ̂(τ'−τ_k) = L Φ(τ−τ')` (§2.2). -/
  poisson : ∀ τ τ', HasSum (fun k : ℤ => F.phiHat (τ - p.tau k) * F.phiHat (τ' - p.tau k))
    (p.L * F.Phi (τ - τ'))
  /-- window-generic remnant of [eq:abdef]: `1/2 ≤ b ≤ a ≤ 1` (the flat-top `1 − 2w/L ≤ b`
  is NOT here; 1/2 suffices for every positivity/division use and holds for the
  Montgomery–Taylor window). -/
  b_ge_half : 1 / 2 ≤ F.b
  b_le_a : F.b ≤ F.a
  a_le_one : F.a ≤ 1
  /-- [eq:psidef] in majorant form, with the [eq:psiints] integrals (`Ψ₀ = 4 + 2log(c_ϱL/4w)`,
  `∫ψ² ≤ 8L`) — fields match `Zeta23.Params.psi'_integrable / psi'_sq_integrable /
  integral_psi'_Ioi_le / integral_psi'_sq_le` in Zeta23/Taper.lean (consumed by [lem:ends]). -/
  psi_integrable : Integrable (psiA cϱ p)
  psi_sq_integrable : Integrable (fun r => psiA cϱ p r ^ 2)
  integral_psi_Ioi_le : ∫ r in Set.Ioi 0, psiA cϱ p r ≤ 4 + 2 * Real.log (cϱ * p.L / (4 * p.w))
  integral_psi_sq_le : ∫ r, psiA cϱ p r ^ 2 ≤ 8 * p.L
  /-- `|φ̂| ≤ ψ` and `|Φ| ≤ ψ` [eq:psidef] in the majorant form used by [lem:ends]. -/
  phiHat_le_psi : ∀ r, |F.phiHat r| ≤ psiA cϱ p r
  Phi_le_psi : ∀ r, |F.Phi r| ≤ psiA cϱ p r
  /-- Π_X is continuous and [eq:PiPfacts] `|Π_X(τ)| ≤ 3√X/(1+|τ|)` (§2.1), for the concrete
  `Zeta23.PiX X` [eq:Pidef] — see `PiX_bound` (holds for all `X ≥ 1`) and `PiX_continuous`. -/
  PiX_cont : Continuous (Zeta23.PiX p.X)
  PiX_bound : ∀ τ, |Zeta23.PiX p.X τ| ≤ 3 * Real.sqrt p.X / (1 + |τ|)


/-- every flat-top taper datum satisfies the window-generic core:
b ≥ 1 − 2w/L ≥ 3/4 ≥ 1/2 ([eq:abdef] + [eq:wrange]), g ≥ 0 (plateau bound). -/
theorem LocalHyps.toCore {cϱ : ℝ} {p : Setting} {F : LocalFun} (hF : LocalHyps cϱ p F) :
    LocalHypsCore cϱ p F where
  four_le_cϱ := hF.four_le_cϱ
  lam_pos := hF.lam_pos
  lam_le_one := hF.lam_le_one
  one_le_w := hF.one_le_w
  w_le := hF.w_le
  one_le_l := hF.one_le_l
  phiHat_cont := hF.phiHat_cont
  phiHat_even := hF.phiHat_even
  phiHat_le_L := hF.phiHat_le_L
  phiHat_le_inv := hF.phiHat_le_inv
  phiHat_le_sq := hF.phiHat_le_sq
  phiHat_sq_integrable := hF.phiHat_sq_integrable
  phiHat_sq_mul_abs_integrable := hF.phiHat_sq_mul_abs_integrable
  integral_phiHat_sq_mul_abs_le := hF.integral_phiHat_sq_mul_abs_le
  phiHat_sq_mul_sq_integrable := hF.phiHat_sq_mul_sq_integrable
  integral_phiHat_sq_mul_sq_le := hF.integral_phiHat_sq_mul_sq_le
  phiHat_sq_integral := hF.phiHat_sq_integral
  phiHat_sq_fourier := hF.phiHat_sq_fourier
  g_nonneg := fun y => le_trans (le_max_right _ _) (hF.g_lower y)
  g_le_Aphi := hF.g_le_Aphi
  Aphi_le := hF.Aphi_le
  Phi_contDiff := hF.Phi_contDiff
  Phi_even := hF.Phi_even
  Phi_le_L := hF.Phi_le_L
  Phi_le_inv := hF.Phi_le_inv
  Phi_le_sq := hF.Phi_le_sq
  Phi_sq_integrable := hF.Phi_sq_integrable
  Phi_sq_mul_abs_integrable := hF.Phi_sq_mul_abs_integrable
  integral_Phi_sq_mul_abs_le := hF.integral_Phi_sq_mul_abs_le
  Phi_sq_mul_sq_integrable := hF.Phi_sq_mul_sq_integrable
  integral_Phi_sq_mul_sq_le := hF.integral_Phi_sq_mul_sq_le
  Phi_zero := hF.Phi_zero
  Phi_sq_integral := hF.Phi_sq_integral
  Phi_sq_fourier := hF.Phi_sq_fourier
  poisson := hF.poisson
  b_ge_half := by
    have h1 : 2 * p.w / p.L ≤ 1 / 4 := by
      rw [div_le_iff₀ hF.L_pos]
      linarith [hF.w_le]
    linarith [hF.b_lower]
  b_le_a := hF.b_le_a
  a_le_one := hF.a_le_one
  psi_integrable := hF.psi_integrable
  psi_sq_integrable := hF.psi_sq_integrable
  integral_psi_Ioi_le := hF.integral_psi_Ioi_le
  integral_psi_sq_le := hF.integral_psi_sq_le
  phiHat_le_psi := hF.phiHat_le_psi
  Phi_le_psi := hF.Phi_le_psi
  PiX_cont := hF.PiX_cont
  PiX_bound := hF.PiX_bound

/-- "uniformly for T ≥ T₀", Core-quantified: stronger than EventuallyAt
(fewer hypotheses on F). -/
def EventuallyAtCore (cϱ lam : ℝ) (P : Setting → LocalFun → Prop) : Prop :=
  ∃ T₀ : ℝ, ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₀ ≤ p.T → LocalHypsCore cϱ p F → P p F

theorem EventuallyAtCore.to_eventuallyAt {cϱ lam : ℝ} {P : Setting → LocalFun → Prop}
    (h : EventuallyAtCore cϱ lam P) : EventuallyAt cϱ lam P := by
  obtain ⟨T₀, hT₀⟩ := h
  exact ⟨T₀, fun p F hl hT hF => hT₀ p F hl hT hF.toCore⟩

/-! Core copies of the LocalHyps helper lemmas (same names under the Core namespace). -/

lemma LocalHypsCore.eight_le_L (hF : LocalHypsCore cϱ p F) : 8 ≤ p.L := by
  linarith [hF.one_le_w, hF.w_le]

lemma LocalHypsCore.L_pos (hF : LocalHypsCore cϱ p F) : 0 < p.L := by
  linarith [hF.eight_le_L]

lemma LocalHypsCore.b_pos (hF : LocalHypsCore cϱ p F) : 0 < F.b := by
  linarith [hF.b_ge_half]

lemma LocalHypsCore.a_pos (hF : LocalHypsCore cϱ p F) : 0 < F.a := hF.b_pos.trans_le hF.b_le_a

lemma LocalHypsCore.integral_Phi_sq_le (hF : LocalHypsCore cϱ p F) :
    ∫ x, F.Phi x ^ 2 ≤ 2 * π * p.L := by
  rw [hF.Phi_sq_integral]
  have hb1 : F.b ≤ 1 := hF.b_le_a.trans hF.a_le_one
  have hL := hF.L_pos
  calc 2 * π * F.b * p.L = (2 * π * p.L) * F.b := by ring
    _ ≤ (2 * π * p.L) * 1 := by gcongr
    _ = 2 * π * p.L := mul_one _

lemma LocalHypsCore.PiX_le_on_I (hF : LocalHypsCore cϱ p F) (hT : 0 < p.T) :
    ∀ τ ∈ Set.Icc p.T (2 * p.T), |Zeta23.PiX p.X τ| ≤ 3 * Real.sqrt p.X / p.T := by
  intro τ hτ
  refine (hF.PiX_bound τ).trans ?_
  apply div_le_div_of_nonneg_left (by positivity) hT
  rw [abs_of_nonneg (by linarith [hτ.1])]
  linarith [hτ.1]

lemma LocalHypsCore.Aphi_nonneg (hF : LocalHypsCore cϱ p F) (y : ℝ) : 0 ≤ F.Aphi y :=
  (hF.g_nonneg y).trans (hF.g_le_Aphi y)

lemma LocalHypsCore.phiHat_sq_mul_integrable_of_bdd (hF : LocalHypsCore cϱ p F) {g : ℝ → ℝ}
    (hg : Continuous g) {c : ℝ} (hc : ∀ x, |g x| ≤ c) :
    Integrable (fun r => F.phiHat r ^ 2 * g r) := by
  have := hF.phiHat_sq_integrable.bdd_mul hg.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hc x))
  simpa only [mul_comm] using this


/-- Window-generic taper facts without the bandwidth cap λ ≤ 1 — the family regime is
λ = L/l ∈ (1, 2) (family window L = log(qT/2π), so L > l).
This regime goes beyond the paper: §5's statements all assume λ ≤ 1; nothing Core-typed is
re-typed here — this is a purely additive split: fields = LocalHypsCore's minus lam_le_one, and
LocalHypsCore.toCoreW below.  Consumed only by the family-average statements. -/
structure LocalHypsCoreW (cϱ : ℝ) (p : Setting) (F : LocalFun) : Prop where
  /-- [eq:phinorms] `c_ϱ ≥ 4`. -/
  four_le_cϱ : 4 ≤ cϱ
  /-- `0 < λ` [Notation] (no upper cap here). -/
  lam_pos : 0 < p.lam
  /-- [eq:wrange] `1 ≤ w ≤ L/8` (forces `L ≥ 8`). -/
  one_le_w : 1 ≤ p.w
  w_le : p.w ≤ p.L / 8
  /-- "T is large": `l ≥ 1`, i.e. `T ≥ 2πe`. -/
  one_le_l : 1 ≤ p.l
  /-- φ̂ real-analytic facts: continuity; evenness (φ even) [§2.2 "φ̂ and Φ are real, even, entire"]. -/
  phiHat_cont : Continuous F.phiHat
  phiHat_even : ∀ r, F.phiHat (-r) = F.phiHat r
  /-- [eq:psidef] `|φ̂(r)| ≤ ψ(r) := min(L, 2/|r|, c_ϱ/(w r²))`, split into three division-free bounds. -/
  phiHat_le_L : ∀ r, |F.phiHat r| ≤ p.L
  phiHat_le_inv : ∀ r, |F.phiHat r| * |r| ≤ 2
  phiHat_le_sq : ∀ r, |F.phiHat r| * r ^ 2 ≤ cϱ / p.w
  /-- Integrability consequences of [eq:psidef] (`φ̂² ≤ ψ² ≤ min(L², c_ϱ²/(w²r⁴))`), and
  [eq:psiints] in the packaged form `∫ φ̂(r)²|r| dr ≤ ∫ ψ²|r| = 8 + 8 log(c_ϱL/4w)` (§2.2, used at
  §5.2 "∫ φ̂(r)²|r| dr ≪ log L"). -/
  phiHat_sq_integrable : Integrable (fun r => F.phiHat r ^ 2)
  phiHat_sq_mul_abs_integrable : Integrable (fun r => F.phiHat r ^ 2 * |r|)
  integral_phiHat_sq_mul_abs_le :
    ∫ r, F.phiHat r ^ 2 * |r| ≤ 8 + 8 * Real.log (cϱ * p.L / (4 * p.w))
  /-- also from [eq:psidef]: `φ̂(r)²r² ≤ min(4, (c_ϱ/w)²/r²)`, so `∫ φ̂(r)² r² dr ≤ 8 + 2(c_ϱ/w)²`
  (used for the `|r| > τ_k/2` tails at §5.2 in place of the paper's sharper r⁻⁴ bound). -/
  phiHat_sq_mul_sq_integrable : Integrable (fun r => F.phiHat r ^ 2 * r ^ 2)
  integral_phiHat_sq_mul_sq_le : ∫ r, F.phiHat r ^ 2 * r ^ 2 ≤ 8 + 2 * (cϱ / p.w) ^ 2
  /-- `∫ φ̂(r)² dr = 2π ∫ φ² = 2π a L` [prop:trace proof, §5.2; Plancherel in the paper's
  convention `∫ f ḡ = (2π)⁻¹ ∫ f̂ conj ĝ` + eq:abdef]. -/
  phiHat_sq_integral : ∫ r, F.phiHat r ^ 2 = 2 * π * F.a * p.L
  /-- `φ̂² = Â_φ` on ℝ [§2.2] + Fourier inversion, in the real form used at §5.2:
  `∫ φ̂(r)² cos(ry) dr = 2π A_φ(y)` (`φ̂²` even, `A_φ` even, continuous, supported in `[−L,L]`). -/
  phiHat_sq_fourier : ∀ y, ∫ r, F.phiHat r ^ 2 * Real.cos (r * y) = 2 * π * F.Aphi y
  /-- window-generic remnant of [eq:gbounds]: `g ≥ 0` and `g ≤ A_φ ≤ (L−|y|)₊`
  (the flat-top plateau lower bound `(L−2w−|y|)₊ ≤ g` is NOT here — see §7.1). -/
  g_nonneg : ∀ y, 0 ≤ F.g y
  g_le_Aphi : ∀ y, F.g y ≤ F.Aphi y
  Aphi_le : ∀ y, F.Aphi y ≤ max (p.L - |y|) 0
  /-- Φ facts: `Φ` is C¹ (indeed entire), even [§2.2]. -/
  Phi_contDiff : ContDiff ℝ 1 F.Phi
  Phi_even : ∀ r, F.Phi (-r) = F.Phi r
  /-- [eq:psidef] `|Φ(r)| ≤ ψ(r)`, three division-free bounds. -/
  Phi_le_L : ∀ r, |F.Phi r| ≤ p.L
  Phi_le_inv : ∀ r, |F.Phi r| * |r| ≤ 2
  Phi_le_sq : ∀ r, |F.Phi r| * r ^ 2 ≤ cϱ / p.w
  /-- Integrability consequences of [eq:psidef] for Φ, and [eq:psiints] packaged as
  `∫ Φ(x)²|x| dx ≤ 8 + 8 log(c_ϱL/4w)` (§5.4 "∫Φ(x)²|x|dx ≪ log L (by (eq:psidef), (eq:psiints))"). -/
  Phi_sq_integrable : Integrable (fun x => F.Phi x ^ 2)
  Phi_sq_mul_abs_integrable : Integrable (fun x => F.Phi x ^ 2 * |x|)
  integral_Phi_sq_mul_abs_le :
    ∫ x, F.Phi x ^ 2 * |x| ≤ 8 + 8 * Real.log (cϱ * p.L / (4 * p.w))
  /-- second moment of `Φ²` (same [eq:psidef] path as the `φ̂` version; needed against the
  `10r²/t` term of `mu_increment_bound` in [prop:mumu]). -/
  Phi_sq_mul_sq_integrable : Integrable (fun x => F.Phi x ^ 2 * x ^ 2)
  integral_Phi_sq_mul_sq_le : ∫ x, F.Phi x ^ 2 * x ^ 2 ≤ 8 + 2 * (cϱ / p.w) ^ 2
  /-- `Φ(0) = aL` [§2.2]. -/
  Phi_zero : F.Phi 0 = F.a * p.L
  /-- `∫_ℝ Φ² = 2π g(0) = 2π b L` [§2.2]. -/
  Phi_sq_integral : ∫ x, F.Phi x ^ 2 = 2 * π * F.b * p.L
  /-- [eq:Phi2FT] `∫_ℝ Φ(x)² e^{ixy} dx = 2π g(y)` (§5.4), real form (`Φ²`, `g` even). -/
  Phi_sq_fourier : ∀ y, ∫ x, F.Phi x ^ 2 * Real.cos (x * y) = 2 * π * F.g y
  /-- [lem:poisson] (★) `Σ_{k∈ℤ} φ̂(τ−τ_k) φ̂(τ'−τ_k) = L Φ(τ−τ')` (§2.2). -/
  poisson : ∀ τ τ', HasSum (fun k : ℤ => F.phiHat (τ - p.tau k) * F.phiHat (τ' - p.tau k))
    (p.L * F.Phi (τ - τ'))
  /-- window-generic remnant of [eq:abdef]: `1/2 ≤ b ≤ a ≤ 1` (the flat-top `1 − 2w/L ≤ b`
  is NOT here; 1/2 suffices for every positivity/division use and holds for the
  Montgomery–Taylor window). -/
  b_ge_half : 1 / 2 ≤ F.b
  b_le_a : F.b ≤ F.a
  a_le_one : F.a ≤ 1
  /-- [eq:psidef] in majorant form, with the [eq:psiints] integrals (`Ψ₀ = 4 + 2log(c_ϱL/4w)`,
  `∫ψ² ≤ 8L`) — fields match `Zeta23.Params.psi'_integrable / psi'_sq_integrable /
  integral_psi'_Ioi_le / integral_psi'_sq_le` in Zeta23/Taper.lean (consumed by [lem:ends]). -/
  psi_integrable : Integrable (psiA cϱ p)
  psi_sq_integrable : Integrable (fun r => psiA cϱ p r ^ 2)
  integral_psi_Ioi_le : ∫ r in Set.Ioi 0, psiA cϱ p r ≤ 4 + 2 * Real.log (cϱ * p.L / (4 * p.w))
  integral_psi_sq_le : ∫ r, psiA cϱ p r ^ 2 ≤ 8 * p.L
  /-- `|φ̂| ≤ ψ` and `|Φ| ≤ ψ` [eq:psidef] in the majorant form used by [lem:ends]. -/
  phiHat_le_psi : ∀ r, |F.phiHat r| ≤ psiA cϱ p r
  Phi_le_psi : ∀ r, |F.Phi r| ≤ psiA cϱ p r
  /-- Π_X is continuous and [eq:PiPfacts] `|Π_X(τ)| ≤ 3√X/(1+|τ|)` (§2.1), for the concrete
  `Zeta23.PiX X` [eq:Pidef] — see `PiX_bound` (holds for all `X ≥ 1`) / `PiX_continuous`. -/
  PiX_cont : Continuous (Zeta23.PiX p.X)
  PiX_bound : ∀ τ, |Zeta23.PiX p.X τ| ≤ 3 * Real.sqrt p.X / (1 + |τ|)


/-- every flat-top taper datum satisfies the window-generic core:
b ≥ 1 − 2w/L ≥ 3/4 ≥ 1/2 ([eq:abdef] + [eq:wrange]), g ≥ 0 (plateau bound). -/
lemma LocalHypsCore.toCoreW {cϱ : ℝ} {p : Setting} {F : LocalFun} (hF : LocalHypsCore cϱ p F) :
    LocalHypsCoreW cϱ p F :=
  ⟨hF.four_le_cϱ, hF.lam_pos, hF.one_le_w, hF.w_le, hF.one_le_l, hF.phiHat_cont, hF.phiHat_even, hF.phiHat_le_L, hF.phiHat_le_inv, hF.phiHat_le_sq, hF.phiHat_sq_integrable, hF.phiHat_sq_mul_abs_integrable, hF.integral_phiHat_sq_mul_abs_le, hF.phiHat_sq_mul_sq_integrable, hF.integral_phiHat_sq_mul_sq_le, hF.phiHat_sq_integral, hF.phiHat_sq_fourier, hF.g_nonneg, hF.g_le_Aphi, hF.Aphi_le, hF.Phi_contDiff, hF.Phi_even, hF.Phi_le_L, hF.Phi_le_inv, hF.Phi_le_sq, hF.Phi_sq_integrable, hF.Phi_sq_mul_abs_integrable, hF.integral_Phi_sq_mul_abs_le, hF.Phi_sq_mul_sq_integrable, hF.integral_Phi_sq_mul_sq_le, hF.Phi_zero, hF.Phi_sq_integral, hF.Phi_sq_fourier, hF.poisson, hF.b_ge_half, hF.b_le_a, hF.a_le_one, hF.psi_integrable, hF.psi_sq_integrable, hF.integral_psi_Ioi_le, hF.integral_psi_sq_le, hF.phiHat_le_psi, hF.Phi_le_psi, hF.PiX_cont, hF.PiX_bound⟩

lemma LocalHypsCoreW.eight_le_L {cϱ : ℝ} {p : Setting} {F : LocalFun}
    (hF : LocalHypsCoreW cϱ p F) : 8 ≤ p.L := by
  linarith [hF.one_le_w, hF.w_le]

lemma LocalHypsCoreW.L_pos {cϱ : ℝ} {p : Setting} {F : LocalFun}
    (hF : LocalHypsCoreW cϱ p F) : 0 < p.L := by
  linarith [hF.eight_le_L]

lemma LocalHypsCoreW.b_pos {cϱ : ℝ} {p : Setting} {F : LocalFun}
    (hF : LocalHypsCoreW cϱ p F) : 0 < F.b := by
  linarith [hF.b_ge_half]

lemma LocalHypsCoreW.a_pos {cϱ : ℝ} {p : Setting} {F : LocalFun}
    (hF : LocalHypsCoreW cϱ p F) : 0 < F.a := hF.b_pos.trans_le hF.b_le_a

lemma LocalHypsCoreW.integral_Phi_sq_le {cϱ : ℝ} {p : Setting} {F : LocalFun}
    (hF : LocalHypsCoreW cϱ p F) : ∫ x, F.Phi x ^ 2 ≤ 2 * π * p.L := by
  rw [hF.Phi_sq_integral]
  have hb1 : F.b ≤ 1 := hF.b_le_a.trans hF.a_le_one
  have hL := hF.L_pos
  calc 2 * π * F.b * p.L = (2 * π * p.L) * F.b := by ring
    _ ≤ (2 * π * p.L) * 1 := by gcongr
    _ = 2 * π * p.L := mul_one _

lemma LocalHypsCoreW.Aphi_nonneg {cϱ : ℝ} {p : Setting} {F : LocalFun}
    (hF : LocalHypsCoreW cϱ p F) (y : ℝ) : 0 ≤ F.Aphi y :=
  (hF.g_nonneg y).trans (hF.g_le_Aphi y)

lemma LocalHypsCoreW.phiHat_sq_mul_integrable_of_bdd {cϱ : ℝ} {p : Setting} {F : LocalFun}
    (hF : LocalHypsCoreW cϱ p F) {g : ℝ → ℝ}
    (hg : Continuous g) {c : ℝ} (hc : ∀ x, |g x| ≤ c) :
    Integrable (fun r => F.phiHat r ^ 2 * g r) := by
  have := hF.phiHat_sq_integrable.bdd_mul hg.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hc x))
  simpa only [mul_comm] using this

/-- H-cheb [eq:cheb1] ⇒ `|P_X(τ)| ≤ (1/π) Σ_{n≤X} Λ(n)/√n ≤ (3/π)√X ≤ √X` for `X ≥ x₀`
([eq:PiPfacts] second half, §2.1; used as `|P_X| ≤ √X` at §5.4). -/
lemma PX_abs_le (hcheb : Zeta23.ChebyshevMertens) :
    ∃ x₀ : ℝ, ∀ X, x₀ ≤ X → ∀ τ, |Zeta23.PX X τ| ≤ Real.sqrt X := by
  obtain ⟨x₀, hx⟩ := hcheb.cheb1b
  refine ⟨x₀, fun X hX τ => ?_⟩
  unfold Zeta23.PX
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi)]
  have hsum : |∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (Λ n : ℝ) / Real.sqrt n * Real.cos (τ * Real.log n)|
      ≤ ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (Λ n : ℝ) / Real.sqrt n := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [abs_mul, abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))]
    calc (Λ n : ℝ) / Real.sqrt n * |Real.cos (τ * Real.log n)|
        ≤ (Λ n : ℝ) / Real.sqrt n * 1 := by
          gcongr
          exact Real.abs_cos_le_one _
      _ = _ := mul_one _
  have h3 : (3:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  calc 1 / Real.pi * |∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (Λ n : ℝ) / Real.sqrt n * Real.cos (τ * Real.log n)|
      ≤ 1 / Real.pi * (3 * Real.sqrt X) := by gcongr; exact hsum.trans (hx X hX)
    _ = (3 / Real.pi) * Real.sqrt X := by ring
    _ ≤ 1 * Real.sqrt X := by
        gcongr
        rw [div_le_one Real.pi_pos]; exact h3
    _ = Real.sqrt X := one_mul _

/-- H-Γ [eq:mufacts] ⇒ for `T ≥ T₀`: `|μ(τ)| ≤ l` on `I = [T,2T]` (the paper's `0 < μ ≤ l on I`,
§5.4; only the two-sided bound is needed). -/
lemma mu_abs_le_l (hΓ : Zeta23.GammaFacts) : ∃ T₀ : ℝ, ∀ p : Setting, T₀ ≤ p.T →
    ∀ τ ∈ Set.Icc p.T (2 * p.T), |Zeta23.mu τ| ≤ p.l := by
  obtain ⟨C, hC⟩ := hΓ.stirling
  refine ⟨2 * π * Real.exp (2 * |C| + 1), fun p hT τ hτ => ?_⟩
  have hl : 2 * |C| + 1 ≤ p.l := Setting.le_l_of_T hT
  have h2π : 2 * π ≤ p.T := Setting.twopi_le_T (by positivity) hT
  have hT1 : 1 ≤ p.T := by linarith [Real.pi_gt_three]
  have hτpos : 0 < τ := by linarith [hτ.1]
  have hτ1 : 1 ≤ |τ| := by rw [abs_of_pos hτpos]; linarith [hτ.1]
  have hst := hC τ hτ1
  rw [abs_of_pos hτpos] at hst
  have hCτ : C / τ ^ 2 ≤ |C| := by
    calc C / τ ^ 2 ≤ |C| / τ ^ 2 := by gcongr; exact le_abs_self _
      _ ≤ |C| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos
          have : 1 ≤ τ := by linarith [hτ.1]
          nlinarith
      _ = |C| := div_one _
  -- log(τ/2π) ≤ log(2T/2π) = l + log 2
  have hlog : Real.log (τ / (2 * π)) ≤ p.l + Real.log 2 := by
    have : Real.log (τ / (2 * π)) ≤ Real.log (2 * p.T / (2 * π)) :=
      Real.log_le_log (by positivity) (by gcongr; exact hτ.2)
    refine this.trans (le_of_eq ?_)
    rw [show 2 * p.T / (2 * π) = 2 * (p.T / (2 * π)) by ring,
      Real.log_mul (by norm_num) (by positivity)]
    simp [Setting.l, Zeta23.l, add_comm]
  have hup : Zeta23.mu τ ≤ p.l := by
    have h1 : Zeta23.mu τ ≤ 1 / (2 * π) * Real.log (τ / (2 * π)) + |C| := by
      linarith [(abs_le.1 hst).2]
    have h2 : 1 / (2 * π) ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left zero_le_one (by norm_num); linarith [Real.pi_gt_three]
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (zero_lt_two' ℝ); linarith
    have h0 : 0 ≤ p.l + Real.log 2 := by
      linarith [abs_nonneg C, Real.log_nonneg (one_le_two : (1:ℝ) ≤ 2)]
    calc Zeta23.mu τ ≤ 1 / (2 * π) * (p.l + Real.log 2) + |C| := by
          have : 1 / (2 * π) * Real.log (τ / (2 * π)) ≤ 1 / (2 * π) * (p.l + Real.log 2) := by
            gcongr
          linarith
      _ ≤ 1 / 2 * (p.l + Real.log 2) + |C| := by gcongr
      _ ≤ p.l := by linarith
  have hlo : -p.l ≤ Zeta23.mu τ := by
    have := hΓ.mu_zero_le τ; have := hΓ.neg_one_lt_mu_zero
    linarith [abs_nonneg C]
  exact abs_le.2 ⟨hlo, hup⟩

end Regime

/-! ### Elementary lemmas for [prop:trace] -/

section TraceLemmas

/-- Telescoping identity behind the Dirichlet-kernel bound (§5.2):
`2 sin(θ/2) Σ_{k<d} cos(α + kθ) = sin(α + dθ − θ/2) − sin(α − θ/2)`. -/
lemma two_sin_mul_sum_cos (α θ : ℝ) (d : ℕ) :
    2 * Real.sin (θ / 2) * ∑ k ∈ Finset.range d, Real.cos (α + k * θ)
      = Real.sin (α + d * θ - θ / 2) - Real.sin (α - θ / 2) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, mul_add, ih, Real.two_mul_sin_mul_cos]
    have h1 : Real.sin (θ / 2 - (α + d * θ)) = -Real.sin (α + d * θ - θ / 2) := by
      rw [← Real.sin_neg]; congr 1; ring
    have h2 : Real.sin (θ / 2 + (α + d * θ)) = Real.sin (α + ((d:ℕ):ℝ) * θ + θ - θ / 2) := by
      congr 1; ring
    rw [h1, h2]; push_cast; ring_nf

/-- §5.2 `|Σ_{k<d} e^{ikhy}| ≤ |sin(hy/2)|⁻¹`, in the division-free real form
`|sin(θ/2)| · |Σ_{k<d} cos(α + kθ)| ≤ 1`. -/
lemma abs_sin_mul_abs_sum_cos_le (α θ : ℝ) (d : ℕ) :
    |Real.sin (θ / 2)| * |∑ k ∈ Finset.range d, Real.cos (α + k * θ)| ≤ 1 := by
  have h := two_sin_mul_sum_cos α θ d
  have h2 : |2 * Real.sin (θ / 2) * ∑ k ∈ Finset.range d, Real.cos (α + k * θ)| ≤ 2 := by
    rw [h]
    refine (abs_sub _ _).trans ?_
    linarith [Real.abs_sin_le_one (α + d * θ - θ / 2), Real.abs_sin_le_one (α - θ / 2)]
  rw [mul_assoc, abs_mul, abs_mul, abs_two] at h2
  linarith

/-- Jordan's inequality on `[0, π]`: for `0 ≤ y ≤ L`, `sin(πy/L) ≥ 2 min(y, L−y)/L` (§5.2:
`|sin(πy/L)|⁻¹ ≤ L/(2 min(y, L−y))`). -/
lemma two_min_div_le_sin {y L : ℝ} (hL : 0 < L) (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    2 * min y (L - y) / L ≤ Real.sin (π * y / L) := by
  rcases le_total y (L - y) with h | h
  · rw [min_eq_left h]
    have hx : π * y / L ≤ π / 2 := by
      rw [div_le_div_iff₀ hL two_pos]; nlinarith [Real.pi_pos]
    calc 2 * y / L = 2 / π * (π * y / L) := by field_simp
      _ ≤ Real.sin (π * y / L) := Real.mul_le_sin (by positivity) hx
  · rw [min_eq_right h]
    have hs : Real.sin (π * y / L) = Real.sin (π * (L - y) / L) := by
      rw [← Real.sin_pi_sub]; congr 1; field_simp
    rw [hs]
    have hLy : 0 ≤ L - y := by linarith
    have hx : π * (L - y) / L ≤ π / 2 := by
      rw [div_le_div_iff₀ hL two_pos]; nlinarith [Real.pi_pos]
    calc 2 * (L - y) / L = 2 / π * (π * (L - y) / L) := by field_simp
      _ ≤ Real.sin (π * (L - y) / L) := Real.mul_le_sin (by positivity) hx

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

lemma LocalHyps.Aphi_nonneg (hF : LocalHyps cϱ p F) (y : ℝ) : 0 ≤ F.Aphi y :=
  ((le_max_right _ _).trans (hF.g_lower y)).trans (hF.g_le_Aphi y)

/-- The P-part pointwise bound of [prop:trace] (§5.2): for `y ≥ log 2`,
`A_φ(y) |Σ_{k<d} cos(τ_k y)| ≤ L²/(2 log 2)`  (using `τ_k = T + kh`, `h = 2π/L`,
`0 ≤ A_φ(y) ≤ (L−y)₊` [eq:gbounds], the Dirichlet-kernel bound and Jordan's inequality;
for `y ≥ L` the left side vanishes). -/
lemma Aphi_mul_sum_cos_le (hF : LocalHypsCore cϱ p F) {y : ℝ} (hy : Real.log 2 ≤ y) :
    |F.Aphi y * ∑ k ∈ Finset.range p.d, Real.cos (p.tau k * y)| ≤ p.L ^ 2 / (2 * Real.log 2) := by
  have hL := hF.L_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (zero_lt_two' ℝ); linarith
  have hA0 := hF.Aphi_nonneg y
  have hRHS : 0 ≤ p.L ^ 2 / (2 * Real.log 2) := by positivity
  have hyabs : |y| = y := abs_of_nonneg (hlog2.le.trans hy)
  rcases le_or_gt p.L y with hyL | hyL
  · -- y ≥ L: A_φ(y) = 0
    have : F.Aphi y = 0 := le_antisymm ((hF.Aphi_le y).trans (by simp [hyabs, hyL])) hA0
    simp [this, hRHS]
  · -- log 2 ≤ y < L
    set m := min y (p.L - y) with hm
    have hy0 : 0 < y := hlog2.trans_le hy
    have hm0 : 0 < m := lt_min hy0 (by linarith)
    -- the sum is Σ cos(α + kθ) with α = Ty, θ = hy, θ/2 = πy/L
    have hsum : ∑ k ∈ Finset.range p.d, Real.cos (p.tau k * y)
        = ∑ k ∈ Finset.range p.d, Real.cos (p.T * y + k * (p.h * y)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Setting.tau]; push_cast; ring_nf
    have hθ : p.h * y / 2 = π * y / p.L := by simp only [Setting.h]; field_simp
    have hdir := abs_sin_mul_abs_sum_cos_le (p.T * y) (p.h * y) p.d
    rw [← hsum, hθ] at hdir
    have hsin : 2 * m / p.L ≤ Real.sin (π * y / p.L) := two_min_div_le_sin hL hy0.le hyL.le
    have hsin0 : 0 < 2 * m / p.L := by positivity
    rw [abs_of_pos (hsin0.trans_le hsin)] at hdir
    -- |Σ| ≤ L/(2m)
    set S := |∑ k ∈ Finset.range p.d, Real.cos (p.tau k * y)| with hS
    have hS0 : 0 ≤ S := abs_nonneg _
    have hS1 : 2 * m / p.L * S ≤ 1 := (mul_le_mul_of_nonneg_right hsin hS0).trans hdir
    have hS2 : 2 * m * S ≤ p.L := by
      have := mul_le_mul_of_nonneg_left hS1 hL.le
      rw [mul_one, ← mul_assoc, mul_div_cancel₀ _ hL.ne'] at this; linarith
    -- |A| ≤ L − y
    have hA1 : F.Aphi y ≤ p.L - y := (hF.Aphi_le y).trans (by simp [hyabs, hyL.le])
    -- key: (L − y)·log 2 ≤ L·m
    have key : (p.L - y) * Real.log 2 ≤ p.L * m := by
      rcases le_total y (p.L - y) with h | h
      · rw [hm, min_eq_left h]; nlinarith
      · rw [hm, min_eq_right h]; nlinarith
    rw [abs_mul, abs_of_nonneg hA0]
    -- A·S ≤ (L−y)·S ≤ (L−y)·L/(2m) ≤ L²/(2 log 2)
    rw [le_div_iff₀ (by positivity)]
    calc F.Aphi y * S * (2 * Real.log 2) ≤ (p.L - y) * S * (2 * Real.log 2) := by gcongr
      _ = ((p.L - y) * Real.log 2) * (2 * S) := by ring
      _ ≤ (p.L * m) * (2 * S) := by gcongr
      _ = p.L * (2 * m * S) := by ring
      _ ≤ p.L * p.L := by gcongr
      _ = p.L ^ 2 := (sq _).symm

/-- Unit-step Riemann sums of a monotone function (Mathlib) rescaled to step `h` and combined:
for `μ` monotone and `≥ 0` on `[T−h, ∞)`, `0 < h ≤ T`, `d = ⌊T/h⌋` (§5.2:
`h Σ_{k=0}^{d−1} μ(τ_k) = ∫_T^{2T} μ + O(h μ(2T))`, `recall T < T + dh ≤ 2T < T + (d+1)h`). -/
lemma riemann_sum_monotone {μ : ℝ → ℝ} {T h : ℝ} (hh : 0 < h) (hhT : h ≤ T)
    (hmono : MonotoneOn μ (Set.Ici (T - h))) (hnonneg : ∀ x, T - h ≤ x → 0 ≤ μ x) :
    |h * ∑ k ∈ Finset.range ⌊T / h⌋₊, μ (T + k * h) - ∫ x in T..(2 * T), μ x|
      ≤ 2 * h * μ (2 * T) := by
  have hT : 0 < T := hh.trans_le hhT
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = ⌊T / h⌋₊ := ⟨_, rfl⟩
  rw [← hd]
  have hdh : (d : ℝ) * h ≤ T := by
    have := Nat.floor_le (div_nonneg hT.le hh.le); rw [← hd] at this
    rwa [le_div_iff₀ hh] at this
  have hdh' : T < (d + 1 : ℝ) * h := by
    have := Nat.lt_floor_add_one (T / h); rw [← hd] at this
    rwa [div_lt_iff₀ hh] at this
  have hd1 : 1 ≤ d := by
    have : (1:ℝ) ≤ T / h := by rw [le_div_iff₀ hh]; linarith
    exact_mod_cast (Nat.one_le_floor_iff _).2 this |>.trans_eq hd.symm
  -- rescaled function
  set f : ℝ → ℝ := fun s => μ (T + h * s) with hf
  have hfmono : ∀ a : ℝ, -1 ≤ a → MonotoneOn f (Set.Ici a) := by
    intro a ha x hx y hy hxy
    apply hmono
    · simp only [Set.mem_Ici] at hx ⊢; nlinarith
    · simp only [Set.mem_Ici] at hy ⊢; nlinarith
    · nlinarith
  have hμint : ∀ a b : ℝ, T - h ≤ a → T - h ≤ b → IntervalIntegrable μ volume a b := by
    intro a b ha hb
    apply MonotoneOn.intervalIntegrable
    exact hmono.mono (by
      intro x hx; simp only [Set.mem_Ici]
      rcases Set.mem_uIcc.1 hx with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith)
  -- change of variables: ∫_0^a f = h⁻¹ ∫_T^{T+ha} μ
  have hcov : ∀ a : ℝ, ∫ s in (0:ℝ)..a, f s = h⁻¹ * ∫ x in T..(T + h * a), μ x := by
    intro a
    have e := intervalIntegral.integral_comp_mul_add (a := 0) (b := a) μ hh.ne' T
    rw [mul_zero, zero_add, smul_eq_mul, show h * a + T = T + h * a by ring] at e
    rw [← e]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hf]; ring_nf
  -- upper bound: h Σ_{k<d} μ(T+kh) ≤ ∫_T^{T+dh} μ ≤ ∫_T^{2T} μ
  have hup : h * ∑ k ∈ Finset.range d, μ (T + k * h) ≤ ∫ x in T..(2 * T), μ x := by
    have h1 := (hfmono 0 (by norm_num)).mono
      (show Set.Icc (0:ℝ) (0 + d) ⊆ Set.Ici 0 from fun x hx => hx.1) |>.sum_le_integral
    simp only [zero_add] at h1
    rw [hcov] at h1
    have h2 : ∑ k ∈ Finset.range d, μ (T + k * h) = ∑ i ∈ Finset.range d, f (i : ℝ) := by
      refine Finset.sum_congr rfl fun k _ => ?_; simp [hf, mul_comm]
    rw [h2]
    have h3 : h * ∑ i ∈ Finset.range d, f (i : ℝ) ≤ ∫ x in T..(T + h * d), μ x := by
      have := mul_le_mul_of_nonneg_left h1 hh.le
      rwa [← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul] at this
    refine h3.trans ?_
    -- ∫_T^{T+hd} ≤ ∫_T^{2T} since μ ≥ 0 on [T+hd, 2T]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hμint T (T + h * d) (by linarith) (by nlinarith))
      (hμint (T + h * d) (2 * T) (by nlinarith) (by linarith))
    rw [← hsplit]
    have : 0 ≤ ∫ x in (T + h * d)..(2 * T), μ x :=
      intervalIntegral.integral_nonneg (by nlinarith) fun x hx => hnonneg x (by nlinarith [hx.1])
    linarith
  -- lower bound
  have hlo : (∫ x in T..(2 * T), μ x) - 2 * h * μ (2 * T)
      ≤ h * ∑ k ∈ Finset.range d, μ (T + k * h) := by
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, (Nat.sub_add_cancel hd1).symm⟩
    have h1 := (hfmono 0 (by norm_num)).mono
      (show Set.Icc (0:ℝ) (0 + d') ⊆ Set.Ici 0 from fun x hx => hx.1) |>.integral_le_sum
    simp only [zero_add] at h1
    rw [hcov] at h1
    -- Σ_{i<d'} f(i+1) ≤ Σ_{k<d'+1} μ(T+kh)  (drop k = 0 term, which is ≥ 0)
    have h2 : ∑ i ∈ Finset.range d', f ((i + 1 : ℕ) : ℝ)
        ≤ ∑ k ∈ Finset.range (d' + 1), μ (T + k * h) := by
      rw [Finset.sum_range_succ']
      have : ∑ i ∈ Finset.range d', f ((i + 1 : ℕ) : ℝ)
          = ∑ k ∈ Finset.range d', μ (T + ((k + 1 : ℕ) : ℝ) * h) := by
        refine Finset.sum_congr rfl fun k _ => ?_; simp [hf, mul_comm]
      rw [this]
      have : 0 ≤ μ (T + ((0:ℕ):ℝ) * h) := hnonneg _ (by simp; linarith)
      linarith
    have h3 : (∫ x in T..(T + h * d'), μ x) ≤ h * ∑ k ∈ Finset.range (d' + 1), μ (T + k * h) := by
      have := mul_le_mul_of_nonneg_left (h1.trans h2) hh.le
      rwa [← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul] at this
    refine le_trans ?_ h3
    -- ∫_T^{2T} μ − ∫_T^{T+hd'} μ = ∫_{T+hd'}^{2T} μ ≤ (2T − T − hd')·μ(2T) ≤ 2h μ(2T)
    push_cast at hdh hdh'
    have hlen : 2 * T - (T + h * d') ≤ 2 * h := by nlinarith
    have hlen0 : T + h * d' ≤ 2 * T := by nlinarith
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hμint T (T + h * d') (by linarith) (by nlinarith))
      (hμint (T + h * d') (2 * T) (by nlinarith) (by linarith))
    rw [← hsplit]
    have hμ2T : 0 ≤ μ (2 * T) := hnonneg _ (by linarith)
    have : ∫ x in (T + h * d')..(2 * T), μ x ≤ 2 * h * μ (2 * T) := by
      calc ∫ x in (T + h * d')..(2 * T), μ x
          ≤ ∫ x in (T + h * d')..(2 * T), μ (2 * T) := by
            apply intervalIntegral.integral_mono_on hlen0
              (hμint _ _ (by nlinarith) (by linarith)) intervalIntegrable_const
            intro x hx
            exact hmono (by simp only [Set.mem_Ici]; nlinarith [hx.1])
              (by simp only [Set.mem_Ici]; linarith) hx.2
        _ = (2 * T - (T + h * d')) * μ (2 * T) := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
        _ ≤ 2 * h * μ (2 * T) := by gcongr
    linarith
  exact abs_le.2 ⟨by linarith, by linarith⟩

end TraceLemmas

/-! ### Analytic lemmas for [prop:trace]: growth and increments of μ, decay of Π_X -/

section TraceAnalytic
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

/-- From H-Γ [eq:mufacts]: a crude global bound `|μ(τ)| ≤ M + |τ|` (used only to control the
`|r| > τ_k/2` tails, §5.2 "|μ(τ_k+r) − μ(τ_k)| ≪ l + log(2+|r|)"). -/
lemma mu_linear_bound (hΓ : Zeta23.GammaFacts) : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ, |Zeta23.mu τ| ≤ M + |τ| := by
  obtain ⟨C, hC⟩ := hΓ.stirling
  obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hΓ.smooth.continuous.continuousOn (s := Set.Icc (-1 : ℝ) 1))
  refine ⟨max M₁ (1 + |C|), le_max_of_le_right (by positivity), fun τ => ?_⟩
  rcases le_or_gt 1 |τ| with h1 | h1
  · -- |τ| ≥ 1: Stirling
    have hst := hC τ h1
    have hx : 0 < |τ| / (2 * π) := by positivity
    have hlog : |Real.log (|τ| / (2 * π))| ≤ |τ| / (2 * π) + 2 * π := by
      rw [abs_le]; constructor
      · have := Real.log_le_sub_one_of_pos (inv_pos.2 hx)
        rw [Real.log_inv] at this
        have : (|τ| / (2 * π))⁻¹ ≤ 2 * π := by
          rw [inv_div, div_le_iff₀ (by linarith : (0:ℝ) < |τ|)]; nlinarith [Real.pi_pos]
        linarith
      · linarith [Real.log_le_sub_one_of_pos hx, Real.pi_pos]
    have hCτ : C / τ ^ 2 ≤ |C| := by
      calc C / τ ^ 2 ≤ |C| / τ ^ 2 := by gcongr; exact le_abs_self _
        _ ≤ |C| / 1 := by
            apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos; nlinarith [sq_abs τ]
        _ = |C| := div_one _
    have h2 : |1 / (2 * π) * Real.log (|τ| / (2 * π))| ≤ 1 + |τ| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * π))]
      calc 1 / (2 * π) * |Real.log (|τ| / (2 * π))| ≤ 1 / (2 * π) * (|τ| / (2 * π) + 2 * π) := by
            gcongr
        _ = |τ| / (2 * π) ^ 2 + 1 := by field_simp
        _ ≤ |τ| / 1 + 1 := by
            gcongr; nlinarith [Real.pi_gt_three]
        _ = 1 + |τ| := by ring
    calc |Zeta23.mu τ| = |(Zeta23.mu τ - 1 / (2 * π) * Real.log (|τ| / (2 * π)))
          + 1 / (2 * π) * Real.log (|τ| / (2 * π))| := by ring_nf
      _ ≤ |Zeta23.mu τ - 1 / (2 * π) * Real.log (|τ| / (2 * π))|
          + |1 / (2 * π) * Real.log (|τ| / (2 * π))| := abs_add_le _ _
      _ ≤ |C| + (1 + |τ|) := add_le_add (hst.trans hCτ) h2
      _ ≤ max M₁ (1 + |C|) + |τ| := by linarith [le_max_right M₁ (1 + |C|)]
  · have := hM₁ τ ⟨by linarith [neg_abs_le τ], by linarith [le_abs_self τ]⟩
    simp only [Real.norm_eq_abs] at this
    linarith [le_max_left M₁ (1 + |C|), abs_nonneg τ]

/-- From H-Γ [eq:mufacts] `μ' ≪ |τ|⁻¹` + the crude bound: for `t ≥ 2` and all `r`,
`|μ(t+r) − μ(t)| ≤ (K|r| + 10r²)/t`.  (§5.2: `≪ |r|/T` for `|r| ≤ τ_k/2` by the mean value
theorem; for `|r| > τ_k/2` we use `2|r|/t > 1` to absorb the crude bound into the `r²/t` term.) -/
lemma mu_increment_bound (hΓ : Zeta23.GammaFacts) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ,
      |Zeta23.mu (t + r) - Zeta23.mu t| ≤ (K * |r| + 10 * r ^ 2) / t := by
  obtain ⟨C₁, hC₁⟩ := hΓ.deriv_bound
  obtain ⟨M, hM0, hM⟩ := mu_linear_bound hΓ
  refine ⟨max (2 * |C₁|) (4 * M), le_max_of_le_right (by positivity), fun t ht r => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [le_div_iff₀ ht0]
  rcases le_or_gt |r| (t / 2) with hr | hr
  · -- mean value theorem on [t/2, 3t/2]
    have hmvt : ‖Zeta23.mu (t + r) - Zeta23.mu t‖ ≤ (2 * |C₁| / t) * ‖(t + r) - t‖ := by
      apply Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Icc (t / 2) (3 * t / 2))
      · intro x _; exact hΓ.smooth.contDiffAt.differentiableAt (by simp)
      · intro x hx
        have hx1 : 1 ≤ |x| := by rw [abs_of_pos (by linarith [hx.1])]; linarith [hx.1]
        calc ‖deriv Zeta23.mu x‖ = |deriv Zeta23.mu x| := Real.norm_eq_abs _
          _ ≤ C₁ / |x| := hC₁ x hx1
          _ ≤ |C₁| / |x| := by gcongr; exact le_abs_self _
          _ ≤ |C₁| / (t / 2) := by
              apply div_le_div_of_nonneg_left (abs_nonneg _) (by linarith)
              rw [abs_of_pos (by linarith [hx.1])]; exact hx.1
          _ = 2 * |C₁| / t := by field_simp
      · exact convex_Icc _ _
      · constructor <;> linarith
      · constructor <;> linarith [le_abs_self r, neg_abs_le r]
    simp only [add_sub_cancel_left, Real.norm_eq_abs] at hmvt
    calc |Zeta23.mu (t + r) - Zeta23.mu t| * t ≤ (2 * |C₁| / t * |r|) * t := by gcongr
      _ = 2 * |C₁| * |r| := by field_simp
      _ ≤ max (2 * |C₁|) (4 * M) * |r| + 10 * r ^ 2 := by
          nlinarith [le_max_left (2 * |C₁|) (4 * M), abs_nonneg r, sq_nonneg r]
  · -- |r| > t/2: crude bound, absorbed using t < 2|r|
    have h1 : |Zeta23.mu (t + r) - Zeta23.mu t| ≤ 2 * M + 5 * |r| := by
      calc |Zeta23.mu (t + r) - Zeta23.mu t| ≤ |Zeta23.mu (t + r)| + |Zeta23.mu t| := abs_sub _ _
        _ ≤ (M + |t + r|) + (M + |t|) := add_le_add (hM _) (hM _)
        _ ≤ (M + (|t| + |r|)) + (M + |t|) := by linarith [abs_add_le t r]
        _ = 2 * M + 2 * |t| + |r| := by ring
        _ ≤ 2 * M + 5 * |r| := by rw [abs_of_pos ht0]; linarith
    calc |Zeta23.mu (t + r) - Zeta23.mu t| * t ≤ (2 * M + 5 * |r|) * t := by gcongr
      _ ≤ (2 * M + 5 * |r|) * (2 * |r|) := by gcongr; linarith
      _ = 4 * M * |r| + 10 * |r| ^ 2 := by ring
      _ = 4 * M * |r| + 10 * r ^ 2 := by rw [sq_abs]
      _ ≤ max (2 * |C₁|) (4 * M) * |r| + 10 * r ^ 2 := by
          nlinarith [le_max_right (2 * |C₁|) (4 * M), abs_nonneg r]

/-- [eq:PiPfacts] shifted (§5.2: `|Π_X(τ)| ≤ 6√X/T for |τ−τ_k| ≤ T/2`, and the tail absorbed via
`(2|r|/t)² > 1`): for `t ≥ 2` and all `r`, `|Π_X(t+r)| ≤ 6√X/t + 12√X r²/t²`. -/
lemma PiX_shift_bound (hF : LocalHypsCore cϱ p F) {t : ℝ} (ht : 2 ≤ t) (r : ℝ) :
    |Zeta23.PiX p.X (t + r)| ≤ 6 * Real.sqrt p.X / t + 12 * Real.sqrt p.X * r ^ 2 / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hsX : 0 ≤ Real.sqrt p.X := Real.sqrt_nonneg _
  have hb := hF.PiX_bound (t + r)
  have hA : 0 ≤ 6 * Real.sqrt p.X / t := by positivity
  have hB : 0 ≤ 12 * Real.sqrt p.X * r ^ 2 / t ^ 2 := by positivity
  rcases le_or_gt |r| (t / 2) with hr | hr
  · refine hb.trans ((le_of_le_of_eq ?_ rfl).trans (le_add_of_nonneg_right hB))
    -- 3√X/(1+|t+r|) ≤ 6√X/t since 1 + |t+r| ≥ t/2
    have : t / 2 ≤ 1 + |t + r| := by
      have : t - |r| ≤ |t + r| := by
        have := abs_sub_abs_le_abs_sub t (-r)
        rw [abs_neg, sub_neg_eq_add, abs_of_pos ht0] at this; linarith
      linarith
    calc 3 * Real.sqrt p.X / (1 + |t + r|) ≤ 3 * Real.sqrt p.X / (t / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by linarith) this
      _ = 6 * Real.sqrt p.X / t := by field_simp; ring
  · refine hb.trans (le_trans ?_ (le_add_of_nonneg_left hA))
    -- 3√X/(1+|t+r|) ≤ 3√X ≤ 12√X r²/t²
    have h1 : 3 * Real.sqrt p.X / (1 + |t + r|) ≤ 3 * Real.sqrt p.X :=
      div_le_self (by positivity) (by linarith [abs_nonneg (t + r)])
    refine h1.trans ?_
    rw [le_div_iff₀ (by positivity)]
    have : t ^ 2 ≤ 4 * r ^ 2 := by nlinarith [abs_nonneg r, sq_abs r]
    nlinarith


lemma LocalHyps.phiHat_sq_mul_integrable_of_bdd (hF : LocalHyps cϱ p F) {g : ℝ → ℝ}
    (hg : Continuous g) {c : ℝ} (hc : ∀ x, |g x| ≤ c) :
    Integrable (fun r => F.phiHat r ^ 2 * g r) := by
  have := hF.phiHat_sq_integrable.bdd_mul hg.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hc x))
  simpa only [mul_comm] using this

/-- `∫ φ̂(r)² sin(ry) dr = 0` (odd integrand; `φ̂` even). -/
lemma integral_phiHat_sq_mul_sin (hF : LocalHypsCore cϱ p F) (y : ℝ) :
    ∫ r, F.phiHat r ^ 2 * Real.sin (r * y) = 0 := by
  have h := integral_neg_eq_self (fun r => F.phiHat r ^ 2 * Real.sin (r * y)) volume
  simp only [hF.phiHat_even, neg_mul, Real.sin_neg, mul_neg, integral_neg] at h
  linarith

/-- §5.2: `∫ φ̂(τ−τ_k)² cos(τy) dτ = 2π A_φ(y) cos(τ_k y)`, after the substitution `τ = t + r`:
`∫ φ̂(r)² cos((t+r)y) dr = 2π A_φ(y) cos(ty)` (from `φ̂² = Â_φ` + inversion, field `phiHat_sq_fourier`). -/
lemma integral_phiHat_sq_mul_cos_shift (hF : LocalHypsCore cϱ p F) (t y : ℝ) :
    ∫ r, F.phiHat r ^ 2 * Real.cos ((t + r) * y) = 2 * π * F.Aphi y * Real.cos (t * y) := by
  have h1 : ∀ r, F.phiHat r ^ 2 * Real.cos ((t + r) * y)
      = Real.cos (t * y) * (F.phiHat r ^ 2 * Real.cos (r * y))
        - Real.sin (t * y) * (F.phiHat r ^ 2 * Real.sin (r * y)) := by
    intro r; rw [add_mul, Real.cos_add]; ring
  simp_rw [h1]
  rw [integral_sub, integral_const_mul, integral_const_mul, hF.phiHat_sq_fourier,
    integral_phiHat_sq_mul_sin hF]
  · ring
  · exact (hF.phiHat_sq_mul_integrable_of_bdd (by fun_prop) (fun x => Real.abs_cos_le_one _)).const_mul _
  · exact (hF.phiHat_sq_mul_integrable_of_bdd (by fun_prop) (fun x => Real.abs_sin_le_one _)).const_mul _

/-- **P-part of [prop:trace] at one grid point** (§5.2):
`G^P_kk = ∫ φ̂(r)² P_X(τ_k+r) dr = −2 Σ_{n≤X} a_n A_φ(y_n) cos(τ_k y_n)`. -/
lemma P_part_eq (hF : LocalHypsCore cϱ p F) (t : ℝ) :
    ∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (t + r)
      = -2 * ∑ n ∈ primeRange p.X, acoef n * F.Aphi (ycoef n) * Real.cos (t * ycoef n) := by
  have h1 : (fun r => F.phiHat r ^ 2 * Zeta23.PX p.X (t + r))
      = fun r => ∑ n ∈ primeRange p.X,
          (-(1 / Real.pi) * acoef n) * (F.phiHat r ^ 2 * Real.cos ((t + r) * ycoef n)) := by
    funext r
    rw [PX_eq, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [h1, integral_finsetSum _ (fun n _ =>
    ((hF.phiHat_sq_mul_integrable_of_bdd (by fun_prop) (fun x => Real.abs_cos_le_one _)).const_mul _))]
  simp_rw [integral_const_mul, integral_phiHat_sq_mul_cos_shift hF]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  field_simp

/-- **μ-part of [prop:trace] at one grid point** (§5.2: `G^μ_kk = 2πaL μ(τ_k) + O(log L/T)`):
for `t ≥ 2`, `|∫ φ̂(r)² μ(t+r) dr − 2πaL·μ(t)| ≤ (K ∫φ̂²|r| + 10 ∫φ̂²r²)/t`, with `K` from
`mu_increment_bound`. -/
lemma mu_part_bound (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p F) {K : ℝ}
    (hK : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ, |Zeta23.mu (t + r) - Zeta23.mu t| ≤ (K * |r| + 10 * r ^ 2) / t)
    {t : ℝ} (ht : 2 ≤ t) :
    |(∫ r, F.phiHat r ^ 2 * Zeta23.mu (t + r)) - 2 * π * F.a * p.L * Zeta23.mu t|
      ≤ (K * (∫ r, F.phiHat r ^ 2 * |r|) + 10 * (∫ r, F.phiHat r ^ 2 * r ^ 2)) / t := by
  have ht0 : 0 < t := by linarith
  obtain ⟨M, hM0, hM⟩ := mu_linear_bound hΓ
  have hmeas : AEStronglyMeasurable (fun r => F.phiHat r ^ 2 * Zeta23.mu (t + r)) volume := by
    have hc : Continuous fun r => F.phiHat r ^ 2 * Zeta23.mu (t + r) := by
      have := hΓ.smooth.continuous; have := hF.phiHat_cont; fun_prop
    exact hc.aestronglyMeasurable
  have hint : Integrable (fun r => F.phiHat r ^ 2 * Zeta23.mu (t + r)) := by
    refine Integrable.mono'
      ((hF.phiHat_sq_integrable.const_mul (M + t)).add hF.phiHat_sq_mul_abs_integrable) hmeas ?_
    refine Filter.Eventually.of_forall fun r => ?_
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    have htr : |t + r| ≤ t + |r| := by
      calc |t + r| ≤ |t| + |r| := abs_add_le _ _
        _ = t + |r| := by rw [abs_of_pos ht0]
    calc F.phiHat r ^ 2 * |Zeta23.mu (t + r)| ≤ F.phiHat r ^ 2 * (M + |t + r|) := by
          gcongr; exact hM _
      _ ≤ F.phiHat r ^ 2 * (M + (t + |r|)) := by gcongr
      _ = (M + t) * F.phiHat r ^ 2 + F.phiHat r ^ 2 * |r| := by ring
  have hconst : 2 * π * F.a * p.L * Zeta23.mu t = ∫ r, F.phiHat r ^ 2 * Zeta23.mu t := by
    rw [integral_mul_const, hF.phiHat_sq_integral]
  rw [hconst, ← integral_sub hint (hF.phiHat_sq_integrable.mul_const _)]
  have hgi : Integrable (fun r => (K * (F.phiHat r ^ 2 * |r|) + 10 * (F.phiHat r ^ 2 * r ^ 2)) / t) :=
    ((hF.phiHat_sq_mul_abs_integrable.const_mul K).add
      (hF.phiHat_sq_mul_sq_integrable.const_mul 10)).div_const t
  rw [← Real.norm_eq_abs]
  calc ‖∫ r, F.phiHat r ^ 2 * Zeta23.mu (t + r) - F.phiHat r ^ 2 * Zeta23.mu t‖
      ≤ ∫ r, (K * (F.phiHat r ^ 2 * |r|) + 10 * (F.phiHat r ^ 2 * r ^ 2)) / t := by
        refine norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall fun r => ?_)
        rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
        calc F.phiHat r ^ 2 * |Zeta23.mu (t + r) - Zeta23.mu t|
            ≤ F.phiHat r ^ 2 * ((K * |r| + 10 * r ^ 2) / t) := by gcongr; exact hK t ht r
          _ = _ := by ring
    _ = (K * (∫ r, F.phiHat r ^ 2 * |r|) + 10 * (∫ r, F.phiHat r ^ 2 * r ^ 2)) / t := by
        rw [integral_div, integral_add (hF.phiHat_sq_mul_abs_integrable.const_mul K)
          (hF.phiHat_sq_mul_sq_integrable.const_mul 10), integral_const_mul, integral_const_mul]

/-- **Π-part of [prop:trace] at one grid point** (§5.2: `|G^Π_kk| ≤ 6√X·2πaL/T + O(√X T⁻³)`):
for `t ≥ 2`, `|∫ φ̂(r)² Π_X(t+r) dr| ≤ (6√X/t)·2πaL + (12√X/t²)·∫φ̂²r²`. -/
lemma Pi_part_bound (hF : LocalHypsCore cϱ p F) {t : ℝ} (ht : 2 ≤ t) :
    |∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (t + r)|
      ≤ (6 * Real.sqrt p.X / t) * (2 * π * F.a * p.L)
        + (12 * Real.sqrt p.X / t ^ 2) * ∫ r, F.phiHat r ^ 2 * r ^ 2 := by
  have hgi : Integrable (fun r => (6 * Real.sqrt p.X / t) * F.phiHat r ^ 2
      + (12 * Real.sqrt p.X / t ^ 2) * (F.phiHat r ^ 2 * r ^ 2)) :=
    (hF.phiHat_sq_integrable.const_mul _).add (hF.phiHat_sq_mul_sq_integrable.const_mul _)
  rw [← Real.norm_eq_abs]
  calc ‖∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (t + r)‖
      ≤ ∫ r, (6 * Real.sqrt p.X / t) * F.phiHat r ^ 2
          + (12 * Real.sqrt p.X / t ^ 2) * (F.phiHat r ^ 2 * r ^ 2) := by
        refine norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall fun r => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
        calc F.phiHat r ^ 2 * |Zeta23.PiX p.X (t + r)|
            ≤ F.phiHat r ^ 2 * (6 * Real.sqrt p.X / t + 12 * Real.sqrt p.X * r ^ 2 / t ^ 2) := by
              gcongr; exact PiX_shift_bound hF ht r
          _ = _ := by ring
    _ = _ := by
        rw [integral_add (hF.phiHat_sq_integrable.const_mul _)
          (hF.phiHat_sq_mul_sq_integrable.const_mul _), integral_const_mul, integral_const_mul,
          hF.phiHat_sq_integral]

/-- Integrability of `φ̂(r)² Π_X(t+r)` (bounded × integrable). -/
lemma Pi_part_integrable (hF : LocalHypsCore cϱ p F) (t : ℝ) :
    Integrable (fun r => F.phiHat r ^ 2 * Zeta23.PiX p.X (t + r)) := by
  refine hF.phiHat_sq_mul_integrable_of_bdd (hF.PiX_cont.comp (continuous_const_add t))
    (c := 3 * Real.sqrt p.X) (fun x => (hF.PiX_bound _).trans ?_)
  exact div_le_self (by positivity) (by linarith [abs_nonneg (t + x)])

/-- Integrability of `φ̂(r)² P_X(t+r)` (bounded × integrable). -/
lemma P_part_integrable (hF : LocalHypsCore cϱ p F) (t : ℝ) :
    Integrable (fun r => F.phiHat r ^ 2 * Zeta23.PX p.X (t + r)) := by
  refine hF.phiHat_sq_mul_integrable_of_bdd ((PX_continuous p.X).comp (continuous_const_add t))
    (c := 1 / Real.pi * ∑ n ∈ primeRange p.X, acoef n) (fun x => ?_)
  simp only [PX_eq]
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi)]
  gcongr
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  have ha : 0 ≤ acoef n := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  rw [abs_mul, abs_of_nonneg ha]
  calc acoef n * |Real.cos ((t + x) * ycoef n)| ≤ acoef n * 1 := by
        gcongr; exact Real.abs_cos_le_one _
    _ = acoef n := mul_one _

/-- Integrability of `φ̂(r)² μ(t+r)` for `t > 0` (`|μ| ≤ M + |τ|` and `∫φ̂²|r| < ∞`). -/
lemma mu_part_integrable (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p F) {t : ℝ} (ht0 : 0 < t) :
    Integrable (fun r => F.phiHat r ^ 2 * Zeta23.mu (t + r)) := by
  obtain ⟨M, hM0, hM⟩ := mu_linear_bound hΓ
  have hmeas : AEStronglyMeasurable (fun r => F.phiHat r ^ 2 * Zeta23.mu (t + r)) volume := by
    have hc : Continuous fun r => F.phiHat r ^ 2 * Zeta23.mu (t + r) := by
      have := hΓ.smooth.continuous; have := hF.phiHat_cont; fun_prop
    exact hc.aestronglyMeasurable
  refine Integrable.mono'
    ((hF.phiHat_sq_integrable.const_mul (M + t)).add hF.phiHat_sq_mul_abs_integrable) hmeas ?_
  refine Filter.Eventually.of_forall fun r => ?_
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  have htr : |t + r| ≤ t + |r| := by
    calc |t + r| ≤ |t| + |r| := abs_add_le _ _
      _ = t + |r| := by rw [abs_of_pos ht0]
  calc F.phiHat r ^ 2 * |Zeta23.mu (t + r)| ≤ F.phiHat r ^ 2 * (M + |t + r|) := by
        gcongr; exact hM _
    _ ≤ F.phiHat r ^ 2 * (M + (t + |r|)) := by gcongr
    _ = (M + t) * F.phiHat r ^ 2 + F.phiHat r ^ 2 * |r| := by ring

/-- **Decomposition of a diagonal entry** (§5.2: `G_kk = ∫ φ̂(τ−τ_k)² ν_X(τ)dτ =: G^μ_kk +
G^Π_kk + G^P_kk according to (eq:nudef)`), after translating `τ = τ_k + r`. -/
lemma GentryA_diag_eq (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p F) (k : ℤ)
    (hk : 0 < p.tau k) :
    GentryA p F k k = (∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r))
      + (∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r))
      + (∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r)) := by
  unfold GentryA
  have htrans : (∫ τ, F.phiHat (τ - p.tau k) * F.phiHat (τ - p.tau k) * Zeta23.nuX p.X τ)
      = ∫ r, F.phiHat r ^ 2 * Zeta23.nuX p.X (p.tau k + r) := by
    rw [← integral_add_right_eq_self _ (p.tau k)]
    congr 1; funext r; simp only [add_sub_cancel_right]; ring_nf
  rw [htrans]
  have hν : ∀ r, F.phiHat r ^ 2 * Zeta23.nuX p.X (p.tau k + r)
      = (F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r) + F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r))
        + F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r) := by
    intro r; simp only [Zeta23.nuX]; ring
  simp_rw [hν]
  have h12 : Integrable (fun r => F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r)
      + F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r)) :=
    (mu_part_integrable hΓ hF hk).add (Pi_part_integrable hF _)
  rw [integral_add h12 (P_part_integrable hF _),
    integral_add (mu_part_integrable hΓ hF hk) (Pi_part_integrable hF _)]


/-- H-Γ ⇒ `μ ≥ 0` far out (Stirling): `∃ τ₀ ≥ 0, μ ≥ 0 on [τ₀, ∞)` (the paper's "μ is positive …
on [T−h, 2T]", §5.2). -/
lemma mu_nonneg_eventually (hΓ : Zeta23.GammaFacts) :
    ∃ τ₀ : ℝ, 0 ≤ τ₀ ∧ ∀ x, τ₀ ≤ x → 0 ≤ Zeta23.mu x := by
  obtain ⟨C, hC⟩ := hΓ.stirling
  refine ⟨2 * π * Real.exp (2 * π * |C|), by positivity, fun x hx => ?_⟩
  have h1 : (1:ℝ) ≤ Real.exp (2 * π * |C|) := Real.one_le_exp (by positivity)
  have hx1 : 1 ≤ x := by nlinarith [Real.pi_gt_three]
  have hx0 : 0 < x := by linarith
  have hst := hC x (by rwa [abs_of_pos hx0])
  rw [abs_of_pos hx0] at hst
  have hlog : 2 * π * |C| ≤ Real.log (x / (2 * π)) := by
    rw [← Real.log_exp (2 * π * |C|)]
    apply Real.log_le_log (Real.exp_pos _)
    rw [le_div_iff₀ (by positivity)]; linarith
  have hCx : C / x ^ 2 ≤ |C| := by
    calc C / x ^ 2 ≤ |C| / x ^ 2 := by gcongr; exact le_abs_self _
      _ ≤ |C| / 1 := by apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos; nlinarith
      _ = |C| := div_one _
  have h2 : |C| ≤ 1 / (2 * π) * Real.log (x / (2 * π)) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]; linarith
  linarith [(abs_le.1 hst).1]

/-- **Sum of the P-parts** (§5.2): `|Σ_{k<d} G^P_kk| ≤ (L²/log 2) Σ_{n≤X} a_n`. -/
lemma sum_P_part_bound (hF : LocalHypsCore cϱ p F) :
    |∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r)|
      ≤ p.L ^ 2 / Real.log 2 * ∑ n ∈ primeRange p.X, acoef n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  simp_rw [P_part_eq hF]
  rw [← Finset.mul_sum, Finset.sum_comm]
  -- now: |-2 * Σ_n Σ_k a_n A(y_n) cos(τ_k y_n)|
  rw [abs_mul, abs_neg, abs_two]
  have hterm : ∀ n ∈ primeRange p.X,
      |∑ k ∈ Finset.range p.d, acoef n * F.Aphi (ycoef n) * Real.cos (p.tau k * ycoef n)|
        ≤ acoef n * (p.L ^ 2 / (2 * Real.log 2)) := by
    intro n hn
    have ha : 0 ≤ acoef n := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    have hfac : ∑ k ∈ Finset.range p.d, acoef n * F.Aphi (ycoef n) * Real.cos (p.tau k * ycoef n)
        = acoef n * (F.Aphi (ycoef n) * ∑ k ∈ Finset.range p.d, Real.cos (p.tau k * ycoef n)) := by
      rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [hfac, abs_mul, abs_of_nonneg ha]
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · -- n = 1: a_1 = 0
      have hn1 : n = 1 := by
        have := (Finset.mem_Ioc.1 hn).1; omega
      subst hn1
      simp [acoef, ArithmeticFunction.vonMangoldt_apply_one]
    · gcongr
      apply Aphi_mul_sum_cos_le hF
      exact Real.log_le_log two_pos (by exact_mod_cast hn2)
  calc 2 * |∑ n ∈ primeRange p.X, ∑ k ∈ Finset.range p.d,
          acoef n * F.Aphi (ycoef n) * Real.cos (p.tau k * ycoef n)|
      ≤ 2 * ∑ n ∈ primeRange p.X,
          |∑ k ∈ Finset.range p.d, acoef n * F.Aphi (ycoef n) * Real.cos (p.tau k * ycoef n)| := by
        gcongr; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ 2 * ∑ n ∈ primeRange p.X, acoef n * (p.L ^ 2 / (2 * Real.log 2)) := by
        gcongr with n hn
        exact hterm n hn
    _ = p.L ^ 2 / Real.log 2 * ∑ n ∈ primeRange p.X, acoef n := by
        rw [← Finset.sum_mul]; field_simp

/-- The grid: `τ_k ∈ [T, 2T]` for `0 ≤ k < d` (§2.2 "τ_0,…,τ_{d−1} ∈ [T,2T)"), and `d ≤ LT/2π`. -/
lemma Setting.d_le (p : Setting) (h : 0 ≤ p.L * p.T) : (p.d : ℝ) ≤ p.L * p.T / (2 * π) :=
  Nat.floor_le (by positivity)

lemma Setting.d_eq_floor (p : Setting) (hL : 0 < p.L) : p.d = ⌊p.T / p.h⌋₊ := by
  simp only [Setting.d, Setting.h]
  congr 1
  field_simp

lemma Setting.tau_natCast (p : Setting) (k : ℕ) : p.tau k = p.T + k * p.h := by
  simp [Setting.tau]

lemma Setting.tau_mem (p : Setting) (hL : 0 < p.L) (hT : 0 ≤ p.T) {k : ℕ} (hk : k ∈ Finset.range p.d) :
    p.T ≤ p.tau k ∧ p.tau k ≤ 2 * p.T := by
  rw [Setting.tau_natCast]
  have hh : 0 < p.h := by simp only [Setting.h]; positivity
  have hk' : (k : ℝ) + 1 ≤ p.d := by exact_mod_cast Finset.mem_range.1 hk
  have hd : (p.d : ℝ) * p.h ≤ p.T := by
    have := p.d_le (by positivity)
    simp only [Setting.h]
    rw [le_div_iff₀ (by positivity)] at this
    calc (p.d : ℝ) * (2 * π / p.L) = (p.d * (2 * π)) / p.L := by ring
      _ ≤ (p.L * p.T) / p.L := by gcongr
      _ = p.T := by field_simp
  constructor
  · nlinarith
  · nlinarith

end TraceAnalytic

end PrimeSide
end Zeta23
