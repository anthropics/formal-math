/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of the paper
"More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/
import Zeta23.PrimeSideA.Defs

/-!
# Kernel lemmas for [prop:PP] (§5.4)

Pure measure-theory / trigonometric-integral / H-MV-application lemmas used by
`Zeta23/PrimeSideB/PP.lean`.

* `sqIntegral_shear`: the substitution `τ = τ' + x` on the square `I×I` (§5.4).
* `intervalIntegral_cos_linear*`: `∫_α^β cos(θt + c) dt` closed forms and the bound `2/|θ|` (§5.4).
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction ComplexConjugate

namespace Zeta23
namespace PrimeSide

/-! ## Elementary facts about the index range `primeRange X = Finset.Ioc 0 ⌊X⌋₊` -/

section Basics

lemma one_le_of_mem_primeRange {X : ℝ} {n : ℕ} (hn : n ∈ primeRange X) : 1 ≤ n :=
  (Finset.mem_Ioc.mp hn).1

lemma cast_le_of_mem_primeRange {X : ℝ} (hX : 0 ≤ X) {n : ℕ} (hn : n ∈ primeRange X) :
    (n : ℝ) ≤ X :=
  (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hX)

lemma log_nonneg_of_mem_primeRange {X : ℝ} {n : ℕ} (hn : n ∈ primeRange X) :
    0 ≤ Real.log n :=
  Real.log_nonneg (by exact_mod_cast one_le_of_mem_primeRange hn)

lemma log_le_of_mem_primeRange {X : ℝ} (hX : 1 ≤ X) {n : ℕ} (hn : n ∈ primeRange X) :
    Real.log n ≤ Real.log X :=
  Real.log_le_log (by exact_mod_cast one_le_of_mem_primeRange hn)
    (cast_le_of_mem_primeRange (by linarith) hn)

lemma a2_nonneg (n : ℕ) : 0 ≤ (Λ n : ℝ) ^ 2 / n := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

lemma acoef_nonneg (n : ℕ) : 0 ≤ acoef n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

/-- a_n² = Λ(n)²/n (§5.4). -/
lemma acoef_sq (n : ℕ) : acoef n ^ 2 = (Λ n : ℝ) ^ 2 / n := by
  unfold acoef; rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- 2n·a_n² = 2Λ(n)² — the MV weight with δ_n = 1/(2n) [eq:deltan]. -/
lemma acoef_sq_mul_two_mul {n : ℕ} (hn : 1 ≤ n) : acoef n ^ 2 * (2 * n) = 2 * (Λ n : ℝ) ^ 2 := by
  rw [acoef_sq]
  have : (0:ℝ) < n := by exact_mod_cast hn
  field_simp

/-- Λ(1) = 0, so a_1 = 0: terms with n = 1 never contribute. -/
lemma acoef_one : acoef 1 = 0 := by simp [acoef, ArithmeticFunction.vonMangoldt_apply_one]

lemma acoef_eq_zero_or_two_le {X : ℝ} {n : ℕ} (hn : n ∈ primeRange X) :
    acoef n = 0 ∨ 2 ≤ n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · left
    have : n = 1 := by have := one_le_of_mem_primeRange hn; omega
    subst this; exact acoef_one
  · exact Or.inr h

end Basics

/-! ## The shear `(τ,τ') ↦ (x,τ') = (τ−τ',τ')` on `I × I`  (§5.4) -/

section Shear
variable {Φ : ℝ → ℝ} {T : ℝ}

/-- The shear `(x, τ') ↦ (x + τ', τ')` of `ℝ²` as a homeomorphism (its inverse is
`(τ, τ') ↦ (τ − τ', τ')`). -/
def shearHomeo : ℝ × ℝ ≃ₜ ℝ × ℝ where
  toFun z := (z.1 + z.2, z.2)
  invFun z := (z.1 - z.2, z.2)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

lemma measurePreserving_shear :
    MeasurePreserving (fun z : ℝ × ℝ => (z.1 + z.2, z.2)) volume volume := by
  have := measurePreserving_add_prod (volume : Measure ℝ) (volume : Measure ℝ)
  rwa [← Measure.volume_eq_prod] at this

/-- The `τ'`-window at offset `x`:  `I ∩ (I − x) = [max(T−x, T), min(2T−x, 2T)]`
(§5.4: "= [T + x⁻, 2T − x⁺] for |x| < T", empty for `|x| > T`). -/
def Ix (T x : ℝ) : Set ℝ := Icc (max (T - x) T) (min (2 * T - x) (2 * T))

lemma measurableSet_Ix (T x : ℝ) : MeasurableSet (Ix T x) := by
  unfold Ix; exact measurableSet_Icc

lemma mem_Ix {T x τ' : ℝ} : τ' ∈ Ix T x ↔ x + τ' ∈ Icc T (2 * T) ∧ τ' ∈ Icc T (2 * T) := by
  simp only [Ix, Set.mem_Icc, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, h2, h4⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, h3⟩, by linarith, h4⟩

/-- **Shear + Fubini** (§5.4 "Substituting τ = τ'+x and noting that for fixed x the variable
τ' ranges over I∩(I−x)"): for continuous `Φ`, `G`,
  `∬_{I×I} Φ(τ−τ')² G(τ,τ') d(τ,τ') = ∫_ℝ Φ(x)² (∫_{I∩(I−x)} G(x+τ', τ') dτ') dx`.
The map `(x,τ') ↦ (x+τ',τ')` preserves Lebesgue measure on `ℝ²`. -/
lemma sqIntegral_shear (hΦ : Continuous Φ) {G : ℝ × ℝ → ℝ} (hG : Continuous G) :
    ∫ q in Icc T (2 * T) ×ˢ Icc T (2 * T), Φ (q.1 - q.2) ^ 2 * G q
      = ∫ x, Φ x ^ 2 * ∫ τ' in Ix T x, G (x + τ', τ') := by
  set S := Icc T (2 * T) with hS
  have hSm : MeasurableSet (S ×ˢ S) := measurableSet_Icc.prod measurableSet_Icc
  set f : ℝ × ℝ → ℝ := fun q => Φ (q.1 - q.2) ^ 2 * G q with hf
  have hfint : IntegrableOn f (S ×ˢ S) := by
    apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    apply Continuous.continuousOn; fun_prop
  have hind : Integrable ((S ×ˢ S).indicator f) := (integrable_indicator_iff hSm).mpr hfint
  have hemb : MeasurableEmbedding (fun z : ℝ × ℝ => (z.1 + z.2, z.2)) :=
    shearHomeo.measurableEmbedding
  have hcomp : Integrable (fun z : ℝ × ℝ => (S ×ˢ S).indicator f (z.1 + z.2, z.2))
      (volume.prod volume) := by
    have := (measurePreserving_shear.integrable_comp_emb hemb).mpr hind
    rwa [Measure.volume_eq_prod] at this
  -- pointwise identification of the sheared integrand
  have hpt : ∀ x τ', (S ×ˢ S).indicator f (x + τ', τ')
      = (Ix T x).indicator (fun τ' => Φ x ^ 2 * G (x + τ', τ')) τ' := by
    intro x τ'
    by_cases h : τ' ∈ Ix T x
    · have h' : (x + τ', τ') ∈ S ×ˢ S := Set.mk_mem_prod (mem_Ix.mp h).1 (mem_Ix.mp h).2
      rw [Set.indicator_of_mem h', Set.indicator_of_mem h, hf]
      simp
    · have h' : (x + τ', τ') ∉ S ×ˢ S := fun hh => h (mem_Ix.mpr ⟨hh.1, hh.2⟩)
      rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]
  calc ∫ q in S ×ˢ S, f q
      = ∫ q, (S ×ˢ S).indicator f q := (integral_indicator hSm).symm
    _ = ∫ z : ℝ × ℝ, (S ×ˢ S).indicator f (z.1 + z.2, z.2) :=
        (measurePreserving_shear.integral_comp hemb _).symm
    _ = ∫ x, ∫ τ', (S ×ˢ S).indicator f (x + τ', τ') := by
        rw [Measure.volume_eq_prod, integral_prod _ hcomp]
    _ = ∫ x, Φ x ^ 2 * ∫ τ' in Ix T x, G (x + τ', τ') := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp_rw [hpt x]
        rw [integral_indicator (measurableSet_Ix T x), integral_const_mul]

/-- The sheared integrand is integrable in `x` (Fubini), so the outer integral above is a genuine
Lebesgue integral. -/
lemma integrable_sq_mul_inner (hΦ : Continuous Φ) {G : ℝ × ℝ → ℝ} (hG : Continuous G) :
    Integrable (fun x => Φ x ^ 2 * ∫ τ' in Ix T x, G (x + τ', τ')) := by
  set S := Icc T (2 * T) with hS
  have hSm : MeasurableSet (S ×ˢ S) := measurableSet_Icc.prod measurableSet_Icc
  set f : ℝ × ℝ → ℝ := fun q => Φ (q.1 - q.2) ^ 2 * G q with hf
  have hfint : IntegrableOn f (S ×ˢ S) := by
    apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    apply Continuous.continuousOn; fun_prop
  have hind : Integrable ((S ×ˢ S).indicator f) := (integrable_indicator_iff hSm).mpr hfint
  have hemb : MeasurableEmbedding (fun z : ℝ × ℝ => (z.1 + z.2, z.2)) :=
    shearHomeo.measurableEmbedding
  have hcomp : Integrable (fun z : ℝ × ℝ => (S ×ˢ S).indicator f (z.1 + z.2, z.2))
      (volume.prod volume) := by
    have := (measurePreserving_shear.integrable_comp_emb hemb).mpr hind
    rwa [Measure.volume_eq_prod] at this
  have hpt : ∀ x τ', (S ×ˢ S).indicator f (x + τ', τ')
      = (Ix T x).indicator (fun τ' => Φ x ^ 2 * G (x + τ', τ')) τ' := by
    intro x τ'
    by_cases h : τ' ∈ Ix T x
    · have h' : (x + τ', τ') ∈ S ×ˢ S := Set.mk_mem_prod (mem_Ix.mp h).1 (mem_Ix.mp h).2
      rw [Set.indicator_of_mem h', Set.indicator_of_mem h, hf]
      simp
    · have h' : (x + τ', τ') ∉ S ×ˢ S := fun hh => h (mem_Ix.mpr ⟨hh.1, hh.2⟩)
      rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]
  have := hcomp.integral_prod_left
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  simp_rw [hpt x]
  rw [integral_indicator (measurableSet_Ix T x), integral_const_mul]

/-- For `T ≥ 0` the window `I∩(I−x)` is empty unless `|x| ≤ T`; so the `x`-integral may be
restricted to `[−T, T]` (§5.4 "which is empty for |x| ≥ T"). -/
lemma Ix_eq_empty (_hT : 0 ≤ T) {x : ℝ} (hx : T < |x|) : Ix T x = ∅ := by
  unfold Ix
  apply Set.Icc_eq_empty
  intro hle
  have h1 : T - x ≤ 2 * T := le_trans (le_max_left _ _) (hle.trans (min_le_right _ _))
  have h2 : T ≤ 2 * T - x := le_trans (le_max_right _ _) (hle.trans (min_le_left _ _))
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h] at hx; linarith
  · rw [abs_of_neg h] at hx; linarith

/-- On `|x| ≤ T` (and `T ≥ 0`) the window is the honest interval `[max(T−x,T), min(2T−x,2T)]`
with left end ≤ right end, of length `T − |x|`. -/
lemma Ix_le (hT : 0 ≤ T) {x : ℝ} (hx : |x| ≤ T) :
    max (T - x) T ≤ min (2 * T - x) (2 * T) := by
  rw [abs_le] at hx
  simp only [max_le_iff, le_min_iff]; refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

lemma Ix_length {x : ℝ} :
    min (2 * T - x) (2 * T) - max (T - x) T = T - |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h, min_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [abs_of_neg h, min_eq_right (by linarith), max_eq_left (by linarith)]; ring

end Shear

/-! ## The inner `τ'`-integrals:  `∫_α^β cos(θt + c) dt`  (§5.4) -/

section CosIntegral

/-- `cos A cos B = (cos(A−B) + cos(A+B))/2` (§5.4, real form of
`P_X(τ)P_X(τ') = (1/2π²) Re Σ a_n a_m [n^{iτ}m^{−iτ'} + n^{iτ}m^{iτ'}]`). -/
lemma cos_mul_cos_eq (A B : ℝ) :
    Real.cos A * Real.cos B = (Real.cos (A - B) + Real.cos (A + B)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- Closed form of `J(θ,c;α,β) := ∫_α^β cos(θt + c) dt`:  `(β−α)cos c` if `θ = 0` (§5.4 "the first
inner integral is T−|x|"), else `[sin(θβ+c) − sin(θα+c)]/θ` (§5.4). -/
def Jker (θ c α β : ℝ) : ℝ :=
  if θ = 0 then (β - α) * Real.cos c else (Real.sin (θ * β + c) - Real.sin (θ * α + c)) / θ

lemma intervalIntegral_cos_linear {θ : ℝ} (hθ : θ ≠ 0) (c α β : ℝ) :
    ∫ t in α..β, Real.cos (θ * t + c) = (Real.sin (θ * β + c) - Real.sin (θ * α + c)) / θ := by
  rw [intervalIntegral.integral_comp_mul_add (fun t => Real.cos t) hθ c, integral_cos,
    smul_eq_mul, inv_mul_eq_div]

lemma intervalIntegral_cos_linear_eq_Jker (θ c α β : ℝ) :
    ∫ t in α..β, Real.cos (θ * t + c) = Jker θ c α β := by
  unfold Jker
  split_ifs with hθ
  · subst hθ; simp [intervalIntegral.integral_const]
  · exact intervalIntegral_cos_linear hθ c α β

lemma Jker_zero (c α β : ℝ) : Jker 0 c α β = (β - α) * Real.cos c := by simp [Jker]

lemma Jker_of_ne {θ : ℝ} (hθ : θ ≠ 0) (c α β : ℝ) :
    Jker θ c α β = (Real.sin (θ * β + c) - Real.sin (θ * α + c)) / θ := by simp [Jker, hθ]

/-- `|J| ≤ 2/|θ|` for `θ ≠ 0` (§5.4 "≤ 2/log(nm)"). -/
lemma abs_Jker_le {θ : ℝ} (hθ : θ ≠ 0) (c α β : ℝ) : |Jker θ c α β| ≤ 2 / |θ| := by
  rw [Jker_of_ne hθ, abs_div]
  gcongr
  calc |Real.sin (θ * β + c) - Real.sin (θ * α + c)|
      ≤ |Real.sin (θ * β + c)| + |Real.sin (θ * α + c)| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
    _ = 2 := by norm_num

/-- `J` as a function of the offset `x` (through `c = xy`, `α = max(T−x,T)`, `β = min(2T−x,2T)`)
is continuous. -/
lemma continuous_Jker_offset (θ y T : ℝ) :
    Continuous fun x : ℝ => Jker θ (x * y) (max (T - x) T) (min (2 * T - x) (2 * T)) := by
  by_cases hθ : θ = 0
  · simp only [Jker, hθ, if_true]; fun_prop
  · simp only [Jker, hθ, if_false]; fun_prop

variable {T : ℝ}

/-- The inner integral of [eq:MPP] in closed form: for `|x| ≤ T`,
`∫_{I∩(I−x)} cos((x+τ')y) cos(τ'y') dτ' = ½ J(y−y', xy) + ½ J(y+y', xy)`. -/
lemma inner_cos_cos (hT : 0 ≤ T) {x : ℝ} (hx : |x| ≤ T) (y y' : ℝ) :
    ∫ τ' in Ix T x, Real.cos ((x + τ') * y) * Real.cos (τ' * y')
      = (Jker (y - y') (x * y) (max (T - x) T) (min (2 * T - x) (2 * T))
          + Jker (y + y') (x * y) (max (T - x) T) (min (2 * T - x) (2 * T))) / 2 := by
  have hle := Ix_le hT hx
  unfold Ix
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
    ← intervalIntegral_cos_linear_eq_Jker, ← intervalIntegral_cos_linear_eq_Jker,
    ← intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro t _
  simp only
  rw [cos_mul_cos_eq]
  congr 2 <;> (congr 1; ring)

end CosIntegral

/-! ## Per-frequency-pair decomposition of `𝓜[cos(·y), cos(·y')]`  ([eq:MPP], §5.4) -/

section PairDecomp
variable {Φ : ℝ → ℝ} {T : ℝ}

/-- The "−" (difference-frequency) inner integral at offset x:  J(y−y', xy; I∩(I−x)). -/
def JmK (T y y' x : ℝ) : ℝ := Jker (y - y') (x * y) (max (T - x) T) (min (2 * T - x) (2 * T))
/-- The "+" (sum-frequency) inner integral at offset x:  J(y+y', xy; I∩(I−x)). -/
def JpK (T y y' x : ℝ) : ℝ := Jker (y + y') (x * y) (max (T - x) T) (min (2 * T - x) (2 * T))

lemma continuous_JmK (T y y' : ℝ) : Continuous (JmK T y y') := by
  unfold JmK; exact continuous_Jker_offset _ _ _
lemma continuous_JpK (T y y' : ℝ) : Continuous (JpK T y y') := by
  unfold JpK; exact continuous_Jker_offset _ _ _

/-- A⁻(y,y') := ∫_{[−T,T]} Φ(x)² J(y−y', xy) dx and A⁺(y,y') := ∫_{[−T,T]} Φ(x)² J(y+y', xy) dx:
the two halves of 𝓜[cos(·y),cos(·y')] ([eq:MPP]: first / second inner integral). -/
def Aminus (Φ : ℝ → ℝ) (T y y' : ℝ) : ℝ := ∫ x in Icc (-T) T, Φ x ^ 2 * JmK T y y' x
def Aplus (Φ : ℝ → ℝ) (T y y' : ℝ) : ℝ := ∫ x in Icc (-T) T, Φ x ^ 2 * JpK T y y' x

lemma not_mem_Icc_neg {x : ℝ} (hx : x ∉ Icc (-T) T) : T < |x| := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · rcases lt_or_ge x 0 with hx0 | hx0
    · rw [abs_of_neg hx0]; linarith
    · rw [abs_of_nonneg hx0]; linarith
  · exact lt_of_lt_of_le h (le_abs_self x)

/-- **[eq:MPP] per pair** (§5.4): for T ≥ 0,
𝓜[cos(·y), cos(·y')] = ½ A⁻(y,y') + ½ A⁺(y,y'). -/
lemma Mform_cos_cos (hT : 0 ≤ T) (hΦ : Continuous Φ) (y y' : ℝ) :
    Mform Φ T (fun τ => Real.cos (τ * y)) (fun τ => Real.cos (τ * y'))
      = (Aminus Φ T y y' + Aplus Φ T y y') / 2 := by
  unfold Mform Aminus Aplus
  have h1 : (fun q : ℝ × ℝ => Φ (q.1 - q.2) ^ 2 * Real.cos (q.1 * y) * Real.cos (q.2 * y'))
      = fun q => Φ (q.1 - q.2) ^ 2 *
          (fun q : ℝ × ℝ => Real.cos (q.1 * y) * Real.cos (q.2 * y')) q := by
    funext q; ring
  rw [h1, sqIntegral_shear hΦ (by fun_prop)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-T) T) ?zero]
  case zero =>
    intro x hx
    rw [Ix_eq_empty hT (not_mem_Icc_neg hx)]; simp
  have h2 : ∀ x ∈ Icc (-T) T,
      Φ x ^ 2 * ∫ τ' in Ix T x, Real.cos ((x + τ') * y) * Real.cos (τ' * y')
        = (Φ x ^ 2 * JmK T y y' x + Φ x ^ 2 * JpK T y y' x) / 2 := by
    intro x hx
    rw [inner_cos_cos hT (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩)]
    unfold JmK JpK; ring
  rw [setIntegral_congr_fun measurableSet_Icc h2, integral_div, integral_add]
  · exact ((hΦ.pow 2).mul (continuous_JmK T y y')).integrableOn_Icc
  · exact ((hΦ.pow 2).mul (continuous_JpK T y y')).integrableOn_Icc

/-! ### The diagonal 𝒟 (§5.4) -/

lemma JmK_diag (T y x : ℝ) : JmK T y y x = (T - |x|) * Real.cos (x * y) := by
  unfold JmK; rw [sub_self, Jker_zero, Ix_length]

/-- **𝒟, per frequency** (§5.4): "For n=m the first inner integral is T−|x|, so by
[eq:Phi2FT] … 𝒟 = (T/π)Σ a_n² g(y_n) + O(…)", "using ∫_{|x|>T}Φ² ≤ ∫Φ²|x|/T":
  |A⁻(y,y) − T ∫_ℝ Φ(x)² cos(xy) dx| ≤ ∫_ℝ Φ(x)²|x| dx. -/
lemma abs_Aminus_diag_sub_le (hT : 0 ≤ T) (hΦ : Continuous Φ)
    (hΦ2 : Integrable fun x => Φ x ^ 2) (hΦabs : Integrable fun x => Φ x ^ 2 * |x|) (y : ℝ) :
    |Aminus Φ T y y - T * ∫ x, Φ x ^ 2 * Real.cos (x * y)| ≤ ∫ x, Φ x ^ 2 * |x| := by
  unfold Aminus
  simp_rw [JmK_diag]
  set f : ℝ → ℝ := fun x => Φ x ^ 2 * ((T - |x|) * Real.cos (x * y)) with hf
  have hA : Integrable ((Icc (-T) T).indicator f) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      ((by fun_prop : Continuous f).integrableOn_Icc)
  have hB : Integrable fun x => T * (Φ x ^ 2 * Real.cos (x * y)) := by
    refine (hΦ2.mul_bdd (c := 1) (by fun_prop) ?_).const_mul T
    exact Filter.Eventually.of_forall fun x => by
      simpa using Real.abs_cos_le_one (x * y)
  rw [← integral_indicator measurableSet_Icc, ← integral_const_mul, ← integral_sub hA hB]
  calc |∫ x, ((Icc (-T) T).indicator f x - T * (Φ x ^ 2 * Real.cos (x * y)))|
      ≤ ∫ x, |(Icc (-T) T).indicator f x - T * (Φ x ^ 2 * Real.cos (x * y))| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, Φ x ^ 2 * |x| := by
        apply integral_mono (hA.sub hB).abs hΦabs
        intro x
        change |(Icc (-T) T).indicator f x - T * (Φ x ^ 2 * Real.cos (x * y))| ≤ Φ x ^ 2 * |x|
        have hc := Real.abs_cos_le_one (x * y)
        have hΦ0 : 0 ≤ Φ x ^ 2 := sq_nonneg _
        by_cases hx : x ∈ Icc (-T) T
        · rw [Set.indicator_of_mem hx, hf]
          simp only
          have : |x| ≤ T := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
          calc |Φ x ^ 2 * ((T - |x|) * Real.cos (x * y)) - T * (Φ x ^ 2 * Real.cos (x * y))|
              = Φ x ^ 2 * |x| * |Real.cos (x * y)| := by
                rw [show Φ x ^ 2 * ((T - |x|) * Real.cos (x * y)) - T * (Φ x ^ 2 * Real.cos (x * y))
                    = -(Φ x ^ 2 * |x| * Real.cos (x * y)) by ring, abs_neg, abs_mul, abs_mul,
                  abs_of_nonneg hΦ0, abs_abs]
            _ ≤ Φ x ^ 2 * |x| * 1 := by gcongr
            _ = Φ x ^ 2 * |x| := mul_one _
        · rw [Set.indicator_of_notMem hx, zero_sub, abs_neg, abs_mul, abs_mul, abs_of_nonneg hT,
            abs_of_nonneg hΦ0]
          have : T < |x| := not_mem_Icc_neg hx
          calc T * (Φ x ^ 2 * |Real.cos (x * y)|) ≤ |x| * (Φ x ^ 2 * 1) := by gcongr
            _ = Φ x ^ 2 * |x| := by ring

/-! ### The sum-frequency terms 𝒪₂ (§5.4) -/

/-- **𝒪₂, per pair** (§5.4: "|∫(nm)^{iτ'}dτ'| ≤ 2/log(nm)"): for y + y' > 0,
|A⁺(y,y')| ≤ (2/(y+y')) ∫_ℝ Φ². -/
lemma abs_Aplus_le (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2) {y y' : ℝ}
    (hyy : 0 < y + y') :
    |Aplus Φ T y y'| ≤ 2 / (y + y') * ∫ x, Φ x ^ 2 := by
  unfold Aplus
  have hne : y + y' ≠ 0 := hyy.ne'
  have hint : IntegrableOn (fun x => Φ x ^ 2 * JpK T y y' x) (Icc (-T) T) :=
    ((hΦ.pow 2).mul (continuous_JpK T y y')).integrableOn_Icc
  calc |∫ x in Icc (-T) T, Φ x ^ 2 * JpK T y y' x|
      ≤ ∫ x in Icc (-T) T, |Φ x ^ 2 * JpK T y y' x| := abs_integral_le_integral_abs
    _ ≤ ∫ x in Icc (-T) T, Φ x ^ 2 * (2 / (y + y')) := by
        apply setIntegral_mono_on hint.abs (hΦ2.integrableOn.mul_const _) measurableSet_Icc
        intro x _
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        have := abs_Jker_le hne (x * y) (max (T - x) T) (min (2 * T - x) (2 * T))
        rw [abs_of_pos hyy] at this
        exact this
    _ = 2 / (y + y') * ∫ x in Icc (-T) T, Φ x ^ 2 := by rw [integral_mul_const]; ring
    _ ≤ 2 / (y + y') * ∫ x, Φ x ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact setIntegral_le_integral hΦ2 (Filter.Eventually.of_forall fun x => sq_nonneg _)

/-! ### The difference-frequency terms 𝒪₁, exact evaluation (§5.4) -/

/-- The four half-line trigonometric moments of Φ² (the paper's α_n^±, §5.4, split into
real and imaginary parts): C⁺(y) = ∫_0^T Φ²cos(xy), S⁺(y) = ∫_0^T Φ²sin(xy),
C⁻(y) = ∫_{−T}^0 Φ²cos(xy), S⁻(y) = ∫_{−T}^0 Φ²sin(xy). -/
def Cp (Φ : ℝ → ℝ) (T y : ℝ) : ℝ := ∫ x in (0:ℝ)..T, Φ x ^ 2 * Real.cos (x * y)
def Sp (Φ : ℝ → ℝ) (T y : ℝ) : ℝ := ∫ x in (0:ℝ)..T, Φ x ^ 2 * Real.sin (x * y)
def Cm (Φ : ℝ → ℝ) (T y : ℝ) : ℝ := ∫ x in (-T)..0, Φ x ^ 2 * Real.cos (x * y)
def Sm (Φ : ℝ → ℝ) (T y : ℝ) : ℝ := ∫ x in (-T)..0, Φ x ^ 2 * Real.sin (x * y)

/-- linearity step: ∫_a^b Φ²[sin(c₁+xy) − sin(c₂+xy')] in terms of the cos/sin moments. -/
lemma integral_sq_mul_sin_sub_sin (hΦ : Continuous Φ) (a b c₁ c₂ y y' : ℝ) :
    ∫ x in a..b, Φ x ^ 2 * (Real.sin (c₁ + x * y) - Real.sin (c₂ + x * y'))
      = (Real.sin c₁ * ∫ x in a..b, Φ x ^ 2 * Real.cos (x * y))
        + (Real.cos c₁ * ∫ x in a..b, Φ x ^ 2 * Real.sin (x * y))
        - ((Real.sin c₂ * ∫ x in a..b, Φ x ^ 2 * Real.cos (x * y'))
          + (Real.cos c₂ * ∫ x in a..b, Φ x ^ 2 * Real.sin (x * y'))) := by
  have e : ∀ x, Φ x ^ 2 * (Real.sin (c₁ + x * y) - Real.sin (c₂ + x * y'))
      = (Real.sin c₁ * (Φ x ^ 2 * Real.cos (x * y)) + Real.cos c₁ * (Φ x ^ 2 * Real.sin (x * y)))
        - (Real.sin c₂ * (Φ x ^ 2 * Real.cos (x * y'))
            + Real.cos c₂ * (Φ x ^ 2 * Real.sin (x * y'))) := by
    intro x; rw [Real.sin_add, Real.sin_add]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  all_goals apply Continuous.intervalIntegrable; fun_prop

/-- **𝒪₁, per pair, exact** (§5.4): for θ := y − y' ≠ 0 and T ≥ 0,
θ·A⁻(y,y') = [sin2θT·C⁻(y) + cos2θT·S⁻(y)] − [sinθT·C⁻(y') + cosθT·S⁻(y')]
           + [sin2θT·C⁺(y') + cos2θT·S⁺(y')] − [sinθT·C⁺(y) + cosθT·S⁺(y)].
(Paper: "n^{ix}(n/m)^{−ix⁺} equals m^{ix} for x>0 and n^{ix} for x<0 …"; we split [−T,T] at 0:
on x ≤ 0 the window is [T−x, 2T], on x ≥ 0 it is [T, 2T−x].) -/
lemma sub_mul_Aminus_eq (hT : 0 ≤ T) (hΦ : Continuous Φ) {y y' : ℝ} (hθ : y - y' ≠ 0) :
    (y - y') * Aminus Φ T y y'
      = (Real.sin ((y - y') * (2 * T)) * Cm Φ T y + Real.cos ((y - y') * (2 * T)) * Sm Φ T y
          - (Real.sin ((y - y') * T) * Cm Φ T y' + Real.cos ((y - y') * T) * Sm Φ T y'))
        + (Real.sin ((y - y') * (2 * T)) * Cp Φ T y' + Real.cos ((y - y') * (2 * T)) * Sp Φ T y'
          - (Real.sin ((y - y') * T) * Cp Φ T y + Real.cos ((y - y') * T) * Sp Φ T y)) := by
  unfold Aminus Cm Sm Cp Sp
  have hcont : Continuous fun x => Φ x ^ 2 * ((y - y') * JmK T y y' x) := by
    have := continuous_JmK T y y'; fun_prop
  rw [← integral_const_mul]
  have e1 : ∀ x, (y - y') * (Φ x ^ 2 * JmK T y y' x) = Φ x ^ 2 * ((y - y') * JmK T y y' x) := by
    intro x; ring
  simp_rw [e1]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -T ≤ T),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  -- left half: x ∈ [−T, 0], window [T−x, 2T]
  have hL : ∫ x in (-T)..0, Φ x ^ 2 * ((y - y') * JmK T y y' x)
      = ∫ x in (-T)..0, Φ x ^ 2 * (Real.sin ((y - y') * (2 * T) + x * y)
          - Real.sin ((y - y') * T + x * y')) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith : -T ≤ 0)] at hx
    simp only
    congr 1
    unfold JmK
    rw [max_eq_left (by linarith [hx.2]), min_eq_right (by linarith [hx.2]), Jker_of_ne hθ,
      mul_div_cancel₀ _ hθ]
    congr 1
    rw [show (y - y') * (T - x) + x * y = (y - y') * T + x * y' by ring]
  -- right half: x ∈ [0, T], window [T, 2T−x]
  have hR : ∫ x in (0:ℝ)..T, Φ x ^ 2 * ((y - y') * JmK T y y' x)
      = ∫ x in (0:ℝ)..T, Φ x ^ 2 * (Real.sin ((y - y') * (2 * T) + x * y')
          - Real.sin ((y - y') * T + x * y)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hT] at hx
    simp only
    congr 1
    unfold JmK
    rw [max_eq_right (by linarith [hx.1]), min_eq_left (by linarith [hx.1]), Jker_of_ne hθ,
      mul_div_cancel₀ _ hθ]
    congr 1
    rw [show (y - y') * (2 * T - x) + x * y = (y - y') * (2 * T) + x * y' by ring]
  rw [hL, hR, integral_sq_mul_sin_sub_sin hΦ, integral_sq_mul_sin_sub_sin hΦ]

/-- Each half-line moment is bounded by ∫_ℝ Φ² (the paper's |α_n^±| ≤ πbL, §5.4; we use the
cruder ≤ ∫Φ² = 2πbL, constants being immaterial). -/
lemma abs_halfMoment_le (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2) {a b : ℝ}
    (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g) (hg1 : ∀ x, |g x| ≤ 1) :
    |∫ x in a..b, Φ x ^ 2 * g x| ≤ ∫ x, Φ x ^ 2 := by
  rw [intervalIntegral.integral_of_le hab]
  calc |∫ x in Ioc a b, Φ x ^ 2 * g x|
      ≤ ∫ x in Ioc a b, |Φ x ^ 2 * g x| := abs_integral_le_integral_abs
    _ ≤ ∫ x in Ioc a b, Φ x ^ 2 := by
        apply setIntegral_mono_on ?_ hΦ2.integrableOn measurableSet_Ioc
        · intro x _
          rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
          calc Φ x ^ 2 * |g x| ≤ Φ x ^ 2 * 1 := by gcongr; exact hg1 x
            _ = Φ x ^ 2 := mul_one _
        · exact (((by fun_prop : Continuous fun x => Φ x ^ 2 * g x).integrableOn_Icc
            (a := a) (b := b)).mono_set Ioc_subset_Icc_self).abs
    _ ≤ ∫ x, Φ x ^ 2 :=
        setIntegral_le_integral hΦ2 (Filter.Eventually.of_forall fun _ => sq_nonneg _)

lemma abs_Cp_le (hT : 0 ≤ T) (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2) (y : ℝ) :
    |Cp Φ T y| ≤ ∫ x, Φ x ^ 2 :=
  abs_halfMoment_le hΦ hΦ2 hT _ (by fun_prop) fun x => Real.abs_cos_le_one _
lemma abs_Sp_le (hT : 0 ≤ T) (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2) (y : ℝ) :
    |Sp Φ T y| ≤ ∫ x, Φ x ^ 2 :=
  abs_halfMoment_le hΦ hΦ2 hT _ (by fun_prop) fun x => Real.abs_sin_le_one _
lemma abs_Cm_le (hT : 0 ≤ T) (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2) (y : ℝ) :
    |Cm Φ T y| ≤ ∫ x, Φ x ^ 2 :=
  abs_halfMoment_le hΦ hΦ2 (by linarith) _ (by fun_prop) fun x => Real.abs_cos_le_one _
lemma abs_Sm_le (hT : 0 ≤ T) (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2) (y : ℝ) :
    |Sm Φ T y| ≤ ∫ x, Φ x ^ 2 :=
  abs_halfMoment_le hΦ hΦ2 (by linarith) _ (by fun_prop) fun x => Real.abs_sin_le_one _

end PairDecomp

/-! ## Applying H-MV on the prime-power frequencies  ([lem:MV], [eq:deltan]; §5.1, §5.4) -/

section MVapply
variable {C : ℝ}

/-- **[eq:deltan]** (§5.1): "consecutive prime powers n<n' satisfy
log(n'/n) ≥ log((n+1)/n) ≥ 1/(2n), so δ_n⁻¹ ≤ 2n" — in the admissible-weight form H-MV wants:
1/(2n) ≤ |log n − log m| for all distinct n, m ≥ 1 (no primality needed). -/
lemma inv_two_mul_le_abs_log_sub {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≠ m) :
    1 / (2 * (n:ℝ)) ≤ |Real.log n - Real.log m| := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  rcases lt_or_gt_of_ne hnm with h | h
  · -- n < m:  log m − log n ≥ 1 − n/m = (m−n)/m ≥ 1/(2n)
    have hm1 : (n:ℝ) + 1 ≤ m := by exact_mod_cast h
    have hlog : 1 - ((m:ℝ) / n)⁻¹ ≤ Real.log ((m:ℝ) / n) :=
      Real.one_sub_inv_le_log_of_pos (by positivity)
    rw [inv_div, Real.log_div hm0.ne' hn0.ne'] at hlog
    have h2 : 1 / (2 * (n:ℝ)) ≤ (m - n) / m := by
      rw [div_le_div_iff₀ (by positivity) hm0]
      nlinarith [mul_nonneg (sub_nonneg.mpr hm1) (by linarith : (0:ℝ) ≤ 2 * n - 1)]
    have h3 : ((m:ℝ) - n) / m = 1 - n / m := by field_simp
    rw [abs_sub_comm, abs_of_nonneg (by
      linarith [Real.log_le_log hn0 (by linarith : (n:ℝ) ≤ m)])]
    linarith
  · -- m < n:  log n − log m ≥ 1 − m/n = (n−m)/n ≥ 1/n ≥ 1/(2n)
    have hm1 : (m:ℝ) + 1 ≤ n := by exact_mod_cast h
    have hlog : 1 - ((n:ℝ) / m)⁻¹ ≤ Real.log ((n:ℝ) / m) :=
      Real.one_sub_inv_le_log_of_pos (by positivity)
    rw [inv_div, Real.log_div hn0.ne' hm0.ne'] at hlog
    have h2 : 1 / (2 * (n:ℝ)) ≤ (n - m) / n := by
      rw [div_le_div_iff₀ (by positivity) hn0]
      nlinarith
    have h3 : ((n:ℝ) - m) / n = 1 - m / n := by field_simp
    rw [abs_of_nonneg (by linarith [Real.log_le_log hm0 (by linarith : (m:ℝ) ≤ n)])]
    linarith

/-- **H-MV on the prime-power frequencies** ([lem:MV] with [eq:deltan], §5.1: "We apply this with
{λ_r} = {log n : n ≤ X a prime power}" — we index by all n ∈ primeRange X, harmless since the weights
will carry a factor Λ(n)): for complex weights x, z, frequencies y_n = log n and admissible spacing
δ_n = 1/(2n),  ‖Σ_{n≠m} x_n conj(z_m)/(y_n−y_m)‖ ≤ C (Σ 2n‖x_n‖²)^{1/2} (Σ 2n‖z_n‖²)^{1/2}. -/
lemma MV_primeRange (hMV : Zeta23.MVHilbert C) (X : ℝ) (x z : ℕ → ℂ) :
    ‖∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        (if n = m then (0:ℂ) else x n * conj (z m) / ((Real.log n - Real.log m : ℝ) : ℂ))‖
      ≤ C * Real.sqrt (∑ n ∈ primeRange X, ‖x n‖ ^ 2 * (2 * n))
          * Real.sqrt (∑ n ∈ primeRange X, ‖z n‖ ^ 2 * (2 * n)) := by
  set S := primeRange X with hS
  have key := hMV S (fun r : S => Real.log ((r:ℕ):ℝ)) (fun r : S => 1 / (2 * ((r:ℕ):ℝ)))
    (fun r => x r) (fun r => z r) ?_ ?_ ?_
  · have e1 : (∑ r : S, ∑ s : S, if r = s then (0:ℂ) else
        x r * conj (z s) / ((Real.log ((r:ℕ):ℝ) - Real.log ((s:ℕ):ℝ) : ℝ) : ℂ))
        = ∑ n ∈ S, ∑ m ∈ S, (if n = m then (0:ℂ) else
            x n * conj (z m) / ((Real.log n - Real.log m : ℝ) : ℂ)) := by
      simp_rw [Subtype.ext_iff]
      rw [Finset.sum_coe_sort S (fun n => ∑ s : S, if n = (s:ℕ) then (0:ℂ) else
            x n * conj (z s) / ((Real.log n - Real.log ((s:ℕ):ℝ) : ℝ) : ℂ))]
      refine Finset.sum_congr rfl fun n _ => ?_
      exact Finset.sum_coe_sort S (fun m => if n = m then (0:ℂ) else
            x n * conj (z m) / ((Real.log n - Real.log m : ℝ) : ℂ))
    have e2 : ∀ (w : ℕ → ℂ), (∑ r : S, ‖w r‖ ^ 2 / (1 / (2 * ((r:ℕ):ℝ))))
        = ∑ n ∈ S, ‖w n‖ ^ 2 * (2 * n) := by
      intro w
      rw [Finset.sum_coe_sort S (fun n => ‖w n‖ ^ 2 / (1 / (2 * (n:ℝ))))]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [div_div_eq_mul_div, div_one]
    rw [e1, e2 x, e2 z] at key
    exact key
  · intro r s hrs
    apply Subtype.ext
    have hr : (0:ℝ) < ((r:ℕ):ℝ) := by exact_mod_cast one_le_of_mem_primeRange r.2
    have hs : (0:ℝ) < ((s:ℕ):ℝ) := by exact_mod_cast one_le_of_mem_primeRange s.2
    have : ((r:ℕ):ℝ) = ((s:ℕ):ℝ) := Real.log_injOn_pos (Set.mem_Ioi.mpr hr) (Set.mem_Ioi.mpr hs) hrs
    exact_mod_cast this
  · intro r
    have hr : (0:ℝ) < ((r:ℕ):ℝ) := by exact_mod_cast one_le_of_mem_primeRange r.2
    positivity
  · intro r s hrs
    exact inv_two_mul_le_abs_log_sub (one_le_of_mem_primeRange r.2)
      (one_le_of_mem_primeRange s.2) (fun h => hrs (Subtype.ext h))

/-- **Real form used for 𝒪₁** (§5.4: "a combination of four sums of the shape
Σ_{n≠m} x_n z̄_m/(y_n−y_m) … for instance the first is Σ_{n≠m}(a_n n^{2iT}) conj(a_m m^{2iT} ᾱ_m^+)/(y_n−y_m)"):
for real weights u, v and a real phase c, both
  Σ_{n≠m} u_n v_m cos(c(y_n−y_m))/(y_n−y_m)  and  Σ_{n≠m} u_n v_m sin(c(y_n−y_m))/(y_n−y_m)
(= Re, Im of the MV bilinear form with x_n = u_n e^{icy_n}, z_m = v_m e^{icy_m}) are bounded by
C (Σ 2n u_n²)^{1/2} (Σ 2n v_n²)^{1/2}. -/
lemma MV_real (hMV : Zeta23.MVHilbert C) (X c : ℝ) (u v : ℕ → ℝ) :
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
        u n * v m * Real.cos (c * (Real.log n - Real.log m)) / (Real.log n - Real.log m))|
      ≤ C * Real.sqrt (∑ n ∈ primeRange X, u n ^ 2 * (2 * n))
          * Real.sqrt (∑ n ∈ primeRange X, v n ^ 2 * (2 * n)) ∧
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
        u n * v m * Real.sin (c * (Real.log n - Real.log m)) / (Real.log n - Real.log m))|
      ≤ C * Real.sqrt (∑ n ∈ primeRange X, u n ^ 2 * (2 * n))
          * Real.sqrt (∑ n ∈ primeRange X, v n ^ 2 * (2 * n)) := by
  set x : ℕ → ℂ := fun n => (u n : ℂ) * Complex.exp ((c * Real.log n : ℝ) * Complex.I) with hx
  set z : ℕ → ℂ := fun n => (v n : ℂ) * Complex.exp ((c * Real.log n : ℝ) * Complex.I) with hz
  have key := MV_primeRange hMV X x z
  have hnx : ∀ n, ‖x n‖ ^ 2 = u n ^ 2 := by
    intro n
    simp only [hx, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have hnz : ∀ n, ‖z n‖ ^ 2 = v n ^ 2 := by
    intro n
    simp only [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  simp_rw [hnx, hnz] at key
  have hprod : ∀ n m, x n * conj (z m)
      = ((u n * v m : ℝ) : ℂ) * Complex.exp ((c * (Real.log n - Real.log m) : ℝ) * Complex.I) := by
    intro n m
    have harg : ((c * Real.log n : ℝ) : ℂ) * Complex.I
        + ((c * Real.log m : ℝ) : ℂ) * (starRingEnd ℂ) Complex.I
        = ((c * (Real.log n - Real.log m) : ℝ) : ℂ) * Complex.I := by
      rw [Complex.conj_I]; push_cast; ring
    simp only [hx, hz, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    rw [mul_mul_mul_comm, ← Complex.exp_add, harg]
    push_cast; ring
  have hre : (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        (if n = m then (0:ℂ) else x n * conj (z m) / ((Real.log n - Real.log m : ℝ) : ℂ))).re
      = ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
        u n * v m * Real.cos (c * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with h
    · simp
    · rw [hprod, Complex.div_ofReal_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have him : (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        (if n = m then (0:ℂ) else x n * conj (z m) / ((Real.log n - Real.log m : ℝ) : ℂ))).im
      = ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
        u n * v m * Real.sin (c * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) := by
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with h
    · simp
    · rw [hprod, Complex.div_ofReal_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  constructor
  · rw [← hre]; exact (Complex.abs_re_le_norm _).trans key
  · rw [← him]; exact (Complex.abs_im_le_norm _).trans key

/-- The size of the MV bound for our weights (§5.4 "each of the four is at most
(3π/2)·πL·Σ_n a_n²/δ_n ≪ L²X"): with u = a and v = a·w (or vice versa), |w| ≤ W,
C (Σ 2n u_n²)^{1/2} (Σ 2n v_n²)^{1/2} ≤ 2 C W Σ_{n≤X} Λ(n)². -/
lemma MV_size_le (hC : 0 ≤ C) (X : ℝ) {w : ℕ → ℝ} {W : ℝ} (hW : 0 ≤ W)
    (hw : ∀ n ∈ primeRange X, |w n| ≤ W) :
    C * Real.sqrt (∑ n ∈ primeRange X, acoef n ^ 2 * (2 * n))
        * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w n) ^ 2 * (2 * n))
      ≤ 2 * C * W * ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 ∧
    C * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w n) ^ 2 * (2 * n))
        * Real.sqrt (∑ n ∈ primeRange X, acoef n ^ 2 * (2 * n))
      ≤ 2 * C * W * ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 := by
  set Λ2 := ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 with hΛ2
  have hΛ2nn : 0 ≤ Λ2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  have h1 : ∑ n ∈ primeRange X, acoef n ^ 2 * (2 * n) = 2 * Λ2 := by
    rw [hΛ2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n hn => acoef_sq_mul_two_mul (one_le_of_mem_primeRange hn)
  have h2 : ∑ n ∈ primeRange X, (acoef n * w n) ^ 2 * (2 * n) ≤ W ^ 2 * (2 * Λ2) := by
    rw [hΛ2, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [mul_pow, mul_comm (acoef n ^ 2), mul_assoc, acoef_sq_mul_two_mul (one_le_of_mem_primeRange hn)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (sq_abs (w n)).symm ▸ pow_le_pow_left₀ (abs_nonneg _) (hw n hn) 2
  have hs1 : Real.sqrt (∑ n ∈ primeRange X, acoef n ^ 2 * (2 * n)) = Real.sqrt (2 * Λ2) := by
    rw [h1]
  have hs2 : Real.sqrt (∑ n ∈ primeRange X, (acoef n * w n) ^ 2 * (2 * n))
      ≤ W * Real.sqrt (2 * Λ2) := by
    calc Real.sqrt (∑ n ∈ primeRange X, (acoef n * w n) ^ 2 * (2 * n))
        ≤ Real.sqrt (W ^ 2 * (2 * Λ2)) := Real.sqrt_le_sqrt h2
      _ = W * Real.sqrt (2 * Λ2) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hW]
  have hsq : Real.sqrt (2 * Λ2) * Real.sqrt (2 * Λ2) = 2 * Λ2 :=
    Real.mul_self_sqrt (by positivity)
  have hsnn : 0 ≤ Real.sqrt (2 * Λ2) := Real.sqrt_nonneg _
  constructor
  · rw [hs1]
    calc C * Real.sqrt (2 * Λ2) * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w n) ^ 2 * (2 * n))
        ≤ C * Real.sqrt (2 * Λ2) * (W * Real.sqrt (2 * Λ2)) := by gcongr
      _ = C * W * (Real.sqrt (2 * Λ2) * Real.sqrt (2 * Λ2)) := by ring
      _ = 2 * C * W * Λ2 := by rw [hsq]; ring
  · rw [hs1]
    calc C * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w n) ^ 2 * (2 * n)) * Real.sqrt (2 * Λ2)
        ≤ C * (W * Real.sqrt (2 * Λ2)) * Real.sqrt (2 * Λ2) := by gcongr
      _ = C * W * (Real.sqrt (2 * Λ2) * Real.sqrt (2 * Λ2)) := by ring
      _ = 2 * C * W * Λ2 := by rw [hsq]; ring

end MVapply

end PrimeSide
end Zeta23
