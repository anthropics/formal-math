/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Zeta23.PrimeSideA.Basic
import Zeta23.PrimeSideB.PPKernel
import Zeta23.PrimeSideB.PPOffDiag

/-!
# Prime side, part B/PP — paper §5 [prop:PP] (§5.4): the term 𝓜[P_X,P_X]

Consumed by `Zeta23/PrimeSideB.lean` ([thm:traces]) through the three results at the bottom of
this file:

* `prop_PP`        [prop:PP] first form (§5.4):
      𝓜[P_X,P_X] = (T/π) Σ_{n≤X} Λ(n)²/n · g(log n) + O(L²X);
* `sum_a2g_lower`, `sum_a2g_upper`  (§5.4, the "Finally" step, from [eq:gbounds]+[eq:cheb2]):
      (L−2w)³/6 − C·L² ≤ Σ_{n≤X} Λ(n)²/n · g(log n) ≤ L³/6 + C·L²,
  which give the paper's second form  𝓜[P_X,P_X] = (TL³/6π)(1+O(w/L)) + O(L²X).

Everything is stated in the abstract prime-side layer (Zeta23/PrimeSideA/Defs.lean +
`LocalHyps`/`EventuallyAt` of Zeta23/PrimeSideA.lean): `p : Setting` = (T, λ, w), `F : LocalFun` =
the taper data (φ̂, Φ, A_φ, g, a, b) subject to `LocalHyps cϱ p F` (the facts [eq:psidef],
[eq:abdef], [eq:gbounds], [eq:Phi2FT], …, each a proof obligation of Zeta23/Taper.lean, not an
axiom).  `P_X` is `Zeta23.PX` [eq:Pdef] of Zeta23/Defs.lean and 𝓜[·,·] is
`Zeta23.PrimeSide.Mform` (§5.4).  Analytic inputs: H-cheb = `Zeta23.ChebyshevMertens` [lem:cheb]
and H-MV = `Zeta23.MVHilbert` [lem:MV] from Zeta23/Hypotheses.lean (fields of `PaperInputs`).

## Proof route (paper §5.4, reorganised for Lean; labels as in the paper)
1. Bilinearity:  𝓜[P_X,P_X] = π⁻² Σ_{n,m≤X} a_n a_m 𝓜[cos(·y_n), cos(·y_m)],  a_n = Λ(n)/√n, y_n = log n.
2. Shear `(τ,τ') ↦ (x,τ') := (τ−τ',τ')` (measure-preserving on ℝ²) + Fubini  (§5.4 "Substituting
   τ = τ'+x … τ' ranges over I∩(I−x) = [T+x⁻, 2T−x⁺]"):
      𝓜[u,v] = ∫_{|x|≤T} Φ(x)² ∫_{max(T,T−x)}^{min(2T,2T−x)} u(τ'+x) v(τ') dτ' dx.
3. cos A cos B = ½cos(A−B) + ½cos(A+B): inner integral = ½J(xy_n, y_n−y_m) + ½J(xy_n, y_n+y_m),
   J(c,θ) := ∫_α^β cos(c+θτ')dτ' = (β−α)cos c (θ=0), = [sin(c+θβ)−sin(c+θα)]/θ (θ≠0), |J| ≤ 2/|θ|.
4. 𝒟 (n=m, "−"):  ½∫_{|x|≤T}Φ²(T−|x|)cos(xy_n) = πT g(y_n) + O(∫Φ²|x|)   by [eq:Phi2FT];
   𝒪₂ (all n,m, "+"):  ≤ (∫Φ²)(Σa_n)²/(2π² log 2) ≪ XL                        by [eq:cheb1];
   𝒪₁ (n≠m, "−"):  an explicit combination of 8 sums Σ_{n≠m} x_n conj(z_m)/(y_n−y_m) with
   |x_n| = a_n, |z_m| ≤ a_m ∫Φ², each ≤ C_MV·(∫Φ²)·Σ a_n²/δ_n with δ_n = 1/(2n) [eq:deltan] ≪ L²X by H-MV
   and [eq:cheb1] (Σ Λ(n)² ≪ X log X).
Constants: the paper's O(L²X) constant (and the λ=1 "18/L" sharpness) is not load-bearing;
we prove ∃ C.
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace PrimeSide

variable {cϱ lam : ℝ}

/-! ## The main-term sum  Σ_{n≤X} a_n² g(y_n) = Σ_{n≤X} Λ(n)²/n · g(log n)   (§5.4) -/

/-- `Σ_{n ≤ X} Λ(n)²/n · g(log n)` — the sum in the first form of [prop:PP] (§5.4), indexed like
`Zeta23.PX` over `primeRange X = Finset.Ioc 0 ⌊X⌋₊` (Λ = 0 off prime powers).  Note `a_n² = Λ(n)²/n`
(§5.4). -/
def sumA2g (X : ℝ) (g : ℝ → ℝ) : ℝ :=
  ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 / n * g (Real.log n)


/-! ## Elementary facts about the index range and `X = e^L` -/

section Basics
variable {p : Setting} {F : LocalFun}

/-- `log X = L` (`X := e^L`). -/
lemma Setting.log_X (p : Setting) : Real.log p.X = p.L := Real.log_exp _

/-- `X = e^L ≥ 1 + L`; with `L ≥ 8` [eq:wrange] this gives `X ≥ 2` and `L ≤ X`. -/
lemma LocalHypsCore.L_add_one_le_X (_hF : LocalHypsCore cϱ p F) : p.L + 1 ≤ p.X :=
  Real.add_one_le_exp _

lemma LocalHypsCore.two_le_X (hF : LocalHypsCore cϱ p F) : 2 ≤ p.X := by
  linarith [hF.L_add_one_le_X, hF.eight_le_L]

lemma LocalHypsCore.L_le_X (hF : LocalHypsCore cϱ p F) : p.L ≤ p.X := by
  linarith [hF.L_add_one_le_X]

end Basics

/-! ## The g-sandwich  (§5.4)

"Finally, by [eq:gbounds] and [eq:cheb2] (note a_n² = Λ(n)²/n),
  (L−2w)³/6 + O(L²) = Σ_{n≤Xe^{−2w}} a_n²(L−2w−y_n) ≤ Σ_{n≤X} a_n² g(y_n) ≤ Σ_{n≤X} a_n²(L−y_n) = L³/6+O(L²)". -/

section Sandwich
variable {p : Setting} {F : LocalFun}

theorem sum_a2g_upper' (hcheb : Zeta23.ChebyshevMertens) (_hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      sumA2g p.X F.g ≤ p.L ^ 3 / 6 + C * p.L ^ 2) := by
  obtain ⟨C, hC⟩ := hcheb.cheb2b
  refine ⟨C, 0, fun p F _ _ hF => ?_⟩
  have hX1 : (1:ℝ) ≤ p.X := by linarith [hF.two_le_X]
  -- Σ a_n² g(y_n) ≤ Σ a_n² (L − y_n)
  have h1 : sumA2g p.X F.g ≤ ∑ n ∈ primeRange p.X, (Λ n : ℝ) ^ 2 / n * (p.L - Real.log n) := by
    unfold sumA2g
    refine Finset.sum_le_sum fun n hn => ?_
    refine mul_le_mul_of_nonneg_left ?_ (a2_nonneg n)
    calc F.g (Real.log n) ≤ F.Aphi (Real.log n) := hF.g_le_Aphi _
      _ ≤ max (p.L - |Real.log n|) 0 := hF.Aphi_le _
      _ = p.L - Real.log n := by
          rw [abs_of_nonneg (log_nonneg_of_mem_primeRange hn), max_eq_left]
          have := log_le_of_mem_primeRange hX1 hn
          rw [p.log_X] at this; linarith
  -- = Σ a_n² (log X − log n) = L³/6 + O(L²)  [eq:cheb2]
  have h2 := hC p.X hF.two_le_X
  rw [p.log_X] at h2
  have h3 := (abs_le.mp h2).2
  unfold primeRange at h1
  linarith

theorem sum_a2g_lower' (hcheb : Zeta23.ChebyshevMertens) (_hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAt cϱ lam (fun p F =>
      (p.L - 2 * p.w) ^ 3 / 6 - C * p.L ^ 2 ≤ sumA2g p.X F.g) := by
  obtain ⟨C, hC⟩ := hcheb.cheb2b
  refine ⟨max C 0, 0, fun p F _ _ hF => ?_⟩
  -- x' := X e^{−2w} = e^{L−2w} ≥ e^6 ≥ 2
  set L' := p.L - 2 * p.w with hL'
  set x' := Real.exp L' with hx'
  have hL'pos : 6 ≤ L' := by have := hF.w_le; have := hF.eight_le_L; rw [hL']; linarith
  have hL'le : L' ≤ p.L := by rw [hL']; linarith [hF.one_le_w]
  have hx'2 : 2 ≤ x' := by linarith [Real.add_one_le_exp L']
  have hx'X : x' ≤ p.X := Real.exp_le_exp.mpr hL'le
  have hlogx' : Real.log x' = L' := Real.log_exp _
  have hsub : primeRange x' ⊆ primeRange p.X := by
    unfold primeRange
    exact Finset.Ioc_subset_Ioc_right (Nat.floor_le_floor hx'X)
  -- Σ_{n≤X} a_n² g(y_n) ≥ Σ_{n≤x'} a_n² g(y_n) ≥ Σ_{n≤x'} a_n² (L−2w−y_n)
  have h1 : ∑ n ∈ primeRange x', (Λ n : ℝ) ^ 2 / n * (Real.log x' - Real.log n)
      ≤ sumA2g p.X F.g := by
    unfold sumA2g
    calc ∑ n ∈ primeRange x', (Λ n : ℝ) ^ 2 / n * (Real.log x' - Real.log n)
        ≤ ∑ n ∈ primeRange x', (Λ n : ℝ) ^ 2 / n * F.g (Real.log n) := by
          refine Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left ?_ (a2_nonneg n)
          calc Real.log x' - Real.log n ≤ max (p.L - 2 * p.w - |Real.log n|) 0 := by
                rw [hlogx', abs_of_nonneg (log_nonneg_of_mem_primeRange hn), hL']
                exact le_max_left _ _
            _ ≤ F.g (Real.log n) := hF.g_lower _
      _ ≤ ∑ n ∈ primeRange p.X, (Λ n : ℝ) ^ 2 / n * F.g (Real.log n) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro n _ _
          have : 0 ≤ F.g (Real.log n) := le_trans (le_max_right _ _) (hF.g_lower _)
          exact mul_nonneg (a2_nonneg n) this
  -- [eq:cheb2] at x':  Σ_{n≤x'} a_n² (log x' − log n) ≥ (log x')³/6 − C (log x')²
  have h2 := hC x' hx'2
  rw [hlogx'] at h2
  have h3 := (abs_le.mp h2).1
  have hCmax : C * L' ^ 2 ≤ max C 0 * p.L ^ 2 := by
    calc C * L' ^ 2 ≤ max C 0 * L' ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
      _ ≤ max C 0 * p.L ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
          exact pow_le_pow_left₀ (by linarith) hL'le 2
  rw [hlogx'] at h1
  unfold primeRange at h1
  linarith

end Sandwich

/-! ## Assembly of [prop:PP]  (§5.4) -/

section Assembly
variable {Φ : ℝ → ℝ} {T : ℝ}

/-- diagonal / off-diagonal split of a double sum ("𝒟 collects the terms n=m …, 𝒪₁ the terms n≠m",
§5.4). -/
lemma sum_sum_eq_diag_add_offdiag (S : Finset ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ n ∈ S, ∑ m ∈ S, f n m
      = ∑ n ∈ S, f n n + ∑ n ∈ S, ∑ m ∈ S, (if n = m then 0 else f n m) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have e : ∀ m, f n m = (if n = m then f n m else 0) + (if n = m then 0 else f n m) := by
    intro m; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun m _ => e m), Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos hn]

/-- **[eq:MPP]** (§5.4): bilinearity in the prime sum, then the per-pair decomposition:
  𝓜[P_X,P_X] = (1/2π²)·( Σ_n a_n² A⁻(y_n,y_n)  +  Σ_{n≠m} a_n a_m A⁻(y_n,y_m)  +  Σ_{n,m} a_n a_m A⁺(y_n,y_m) )
             =        𝒟-part              +          𝒪₁                   +          𝒪₂ . -/
lemma Mform_PX_PX (hT : 0 ≤ T) (hΦ : Continuous Φ) (X : ℝ) :
    Mform Φ T (Zeta23.PX X) (Zeta23.PX X)
      = (1 / (2 * π ^ 2)) *
        ((∑ n ∈ primeRange X, acoef n ^ 2 * Aminus Φ T (Real.log n) (Real.log n))
          + (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
              (if n = m then (0:ℝ) else acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m)))
          + ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
              acoef n * acoef m * Aplus Φ T (Real.log n) (Real.log m)) := by
  -- Step 1: bilinearity  𝓜[P_X,P_X] = π⁻² Σ_{n,m} a_n a_m 𝓜[cos(·y_n), cos(·y_m)]
  have h1 : Mform Φ T (Zeta23.PX X) (Zeta23.PX X) = (1 / π ^ 2) *
      ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, acoef n * acoef m *
        Mform Φ T (fun τ => Real.cos (τ * Real.log n)) (fun τ => Real.cos (τ * Real.log m)) := by
    unfold Mform
    have hpt : ∀ q : ℝ × ℝ, Φ (q.1 - q.2) ^ 2 * Zeta23.PX X q.1 * Zeta23.PX X q.2
        = (1 / π ^ 2) * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, acoef n * acoef m *
            (Φ (q.1 - q.2) ^ 2 * Real.cos (q.1 * Real.log n) * Real.cos (q.2 * Real.log m)) := by
      intro q
      rw [PX_eq, PX_eq]
      simp only [ycoef]
      rw [show ∀ A B : ℝ, Φ (q.1 - q.2) ^ 2 * (-(1 / π) * A) * (-(1 / π) * B)
          = (1 / π ^ 2) * (Φ (q.1 - q.2) ^ 2 * (A * B)) from fun A B => by ring,
        Finset.sum_mul_sum, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    simp_rw [hpt]
    rw [integral_const_mul]
    congr 1
    have hint : ∀ n m : ℕ, Integrable (fun q : ℝ × ℝ => acoef n * acoef m *
        (Φ (q.1 - q.2) ^ 2 * Real.cos (q.1 * Real.log n) * Real.cos (q.2 * Real.log m)))
        (volume.restrict (Icc T (2 * T) ×ˢ Icc T (2 * T))) := fun n m =>
      (Mform_integrableOn hΦ (u := fun τ => Real.cos (τ * Real.log n))
        (v := fun τ => Real.cos (τ * Real.log m)) (by fun_prop) (by fun_prop)).const_mul _
    rw [integral_finsetSum _ (fun n _ => integrable_finsetSum _ (fun m _ => hint n m))]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_finsetSum _ (fun m _ => hint n m)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_const_mul]
  -- Step 2: per pair, 𝓜[cos,cos] = (A⁻+A⁺)/2, and split the A⁻ double sum into n=m / n≠m
  have h2 : ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, acoef n * acoef m *
        Mform Φ T (fun τ => Real.cos (τ * Real.log n)) (fun τ => Real.cos (τ * Real.log m))
      = (1 / 2) * ((∑ n ∈ primeRange X, acoef n ^ 2 * Aminus Φ T (Real.log n) (Real.log n))
          + (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
              (if n = m then (0:ℝ) else acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m)))
          + ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
              acoef n * acoef m * Aplus Φ T (Real.log n) (Real.log m)) := by
    simp_rw [Mform_cos_cos hT hΦ]
    have e : ∀ n m : ℕ, acoef n * acoef m *
        ((Aminus Φ T (Real.log n) (Real.log m) + Aplus Φ T (Real.log n) (Real.log m)) / 2)
        = (1 / 2) * (acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m))
          + (1 / 2) * (acoef n * acoef m * Aplus Φ T (Real.log n) (Real.log m)) := by
      intro n m; ring
    simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [sum_sum_eq_diag_add_offdiag (primeRange X)
      (fun n m => acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m))]
    simp_rw [← sq]
    ring
  rw [h1, h2]
  ring

/-- **𝒟** (§5.4): with [eq:Phi2FT] ∫Φ²cos(xy) = 2πg(y),
  |(1/2π²)Σ_n a_n² A⁻(y_n,y_n) − (T/π) Σ_n a_n² g(y_n)| ≤ (1/2π²)·(Σ_n a_n²)·∫Φ²|x|. -/
lemma diag_estimate (hT : 0 ≤ T) (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2)
    (hΦabs : Integrable fun x => Φ x ^ 2 * |x|) {g : ℝ → ℝ}
    (hFT : ∀ y, ∫ x, Φ x ^ 2 * Real.cos (x * y) = 2 * π * g y) (X : ℝ) :
    |(1 / (2 * π ^ 2)) * (∑ n ∈ primeRange X, acoef n ^ 2 * Aminus Φ T (Real.log n) (Real.log n))
        - T / π * sumA2g X g|
      ≤ (1 / (2 * π ^ 2)) * (∑ n ∈ primeRange X, acoef n ^ 2) * ∫ x, Φ x ^ 2 * |x| := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  have e : (1 / (2 * π ^ 2)) * (∑ n ∈ primeRange X, acoef n ^ 2 * Aminus Φ T (Real.log n) (Real.log n))
        - T / π * sumA2g X g
      = (1 / (2 * π ^ 2)) * ∑ n ∈ primeRange X, acoef n ^ 2 *
          (Aminus Φ T (Real.log n) (Real.log n) - T * ∫ x, Φ x ^ 2 * Real.cos (x * Real.log n)) := by
    unfold sumA2g
    simp_rw [hFT, ← acoef_sq]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    field_simp
  rw [e, abs_mul, abs_of_pos (by positivity), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc |∑ n ∈ primeRange X, acoef n ^ 2 *
          (Aminus Φ T (Real.log n) (Real.log n) - T * ∫ x, Φ x ^ 2 * Real.cos (x * Real.log n))|
      ≤ ∑ n ∈ primeRange X, |acoef n ^ 2 *
          (Aminus Φ T (Real.log n) (Real.log n) - T * ∫ x, Φ x ^ 2 * Real.cos (x * Real.log n))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ primeRange X, acoef n ^ 2 * ∫ x, Φ x ^ 2 * |x| := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_left (abs_Aminus_diag_sub_le hT hΦ hΦ2 hΦabs _) (sq_nonneg _)
    _ = (∑ n ∈ primeRange X, acoef n ^ 2) * ∫ x, Φ x ^ 2 * |x| := by rw [Finset.sum_mul]

/-- **𝒪₂** (§5.4): "|∫(nm)^{iτ'}dτ'| ≤ 2/log(nm) ≤ 2/log 4 for all n,m, so
|𝒪₂| ≤ (1/2π²)(Σ a_n)²·2πbL·2/log4 ≪ XL" — pre-Chebyshev form:
  |Σ_{n,m} a_n a_m A⁺(y_n,y_m)| ≤ (∫Φ²/log 2)·(Σ_n a_n)².   (Terms with n=1 or m=1 vanish as Λ(1)=0;
otherwise y_n + y_m ≥ 2 log 2.) -/
lemma O2_estimate (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2) (X T : ℝ) :
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X, acoef n * acoef m * Aplus Φ T (Real.log n) (Real.log m)|
      ≤ (∫ x, Φ x ^ 2) / Real.log 2 * (∑ n ∈ primeRange X, acoef n) ^ 2 := by
  have hW : 0 ≤ ∫ x, Φ x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hper : ∀ n ∈ primeRange X, ∀ m ∈ primeRange X,
      |acoef n * acoef m * Aplus Φ T (Real.log n) (Real.log m)|
        ≤ acoef n * acoef m * ((∫ x, Φ x ^ 2) / Real.log 2) := by
    intro n hn m hm
    rw [abs_mul, abs_mul, abs_of_nonneg (acoef_nonneg n), abs_of_nonneg (acoef_nonneg m)]
    rcases acoef_eq_zero_or_two_le hn with h0 | hn2
    · simp [h0]
    rcases acoef_eq_zero_or_two_le hm with h0 | hm2
    · simp [h0]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (acoef_nonneg n) (acoef_nonneg m))
    have hyn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
    have hym : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast hm2)
    have hpos : 0 < Real.log n + Real.log m := by linarith
    calc |Aplus Φ T (Real.log n) (Real.log m)|
        ≤ 2 / (Real.log n + Real.log m) * ∫ x, Φ x ^ 2 := abs_Aplus_le hΦ hΦ2 hpos
      _ ≤ 2 / (2 * Real.log 2) * ∫ x, Φ x ^ 2 := by gcongr; linarith
      _ = (∫ x, Φ x ^ 2) / Real.log 2 := by field_simp
  calc |∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
          acoef n * acoef m * Aplus Φ T (Real.log n) (Real.log m)|
      ≤ ∑ n ∈ primeRange X, |∑ m ∈ primeRange X,
          acoef n * acoef m * Aplus Φ T (Real.log n) (Real.log m)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
          |acoef n * acoef m * Aplus Φ T (Real.log n) (Real.log m)| :=
        Finset.sum_le_sum fun n _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
          acoef n * acoef m * ((∫ x, Φ x ^ 2) / Real.log 2) :=
        Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => hper n hn m hm
    _ = (∫ x, Φ x ^ 2) / Real.log 2 * (∑ n ∈ primeRange X, acoef n) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        ring

end Assembly

/-! ## Results consumed by PrimeSideB.lean -/

section Results

/-- **[prop:PP], first form** (§5.4, verbatim):
"𝓜[P_X,P_X] = (T/π) Σ_{n≤X} Λ(n)²/n · g(log n) + O(L²X)".
Here 𝓜[P_X,P_X] = `Mform F.Phi p.T (Zeta23.PX p.X) (Zeta23.PX p.X)` (§5.4, [eq:Pdef]).
Inputs: H-cheb [lem:cheb] and H-MV [lem:MV] (any constant), plus the taper facts `LocalHyps`.
Shape: ∃ C, for T ≥ T₀(λ, cϱ, the H-constants). -/
theorem prop_PP (hcheb : Zeta23.ChebyshevMertens) (hMV : ∃ C : ℝ, 0 < C ∧ Zeta23.MVHilbert C)
    (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |Mform F.Phi p.T (Zeta23.PX p.X) (Zeta23.PX p.X) - p.T / π * sumA2g p.X F.g|
        ≤ C * (p.L ^ 2 * p.X)) := by
  obtain ⟨CMV, hCMV, hMV⟩ := hMV
  obtain ⟨x₀, h1b⟩ := hcheb.cheb1b
  obtain ⟨C1d, h1d⟩ := hcheb.cheb1d
  obtain ⟨C2a, h2a⟩ := hcheb.cheb2a
  -- the constant (depends on cϱ, the H-constants, λ only through T₀)
  refine ⟨(1 / (2 * π ^ 2)) * ((1 / 2 + |C2a|) * (8 + 8 * |cϱ|) + 16 * CMV * (2 * π) * |C1d|
      + 2 * π / Real.log 2 * 9),
    max (2 * π * Real.exp (|x₀| / lam)) 1, fun p F hplam hT hF => ?_⟩
  beta_reduce
  -- regime facts
  have hT1 : 1 ≤ p.T := le_trans (le_max_right _ _) hT
  have hT0 : 0 ≤ p.T := by linarith
  have hX0 : x₀ ≤ p.X := Setting.le_X_of_T (hplam ▸ hlam.1)
    (by rw [hplam]; exact (le_max_left _ _).trans hT)
  have hX2 : 2 ≤ p.X := hF.two_le_X
  have hL8 : 8 ≤ p.L := hF.eight_le_L
  have hL1 : 1 ≤ p.L := by linarith
  have hLX : p.L ≤ p.X := hF.L_le_X
  have hlogX : Real.log p.X = p.L := p.log_X
  have hΦc : Continuous F.Phi := hF.Phi_contDiff.continuous
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set W := ∫ x, F.Phi x ^ 2 with hWdef
  have hW0 : 0 ≤ W := integral_nonneg fun x => sq_nonneg _
  have hWle : W ≤ 2 * π * p.L := hF.integral_Phi_sq_le
  set ΛΦ := ∫ x, F.Phi x ^ 2 * |x| with hΛΦdef
  have hΛΦ0 : 0 ≤ ΛΦ := integral_nonneg fun x => mul_nonneg (sq_nonneg _) (abs_nonneg _)
  -- ∫Φ²|x| ≤ 8 + 8 log(cϱL/4w) ≤ (8 + 8|cϱ|) L
  have hΛΦle : ΛΦ ≤ (8 + 8 * |cϱ|) * p.L := by
    have h1 := hF.integral_Phi_sq_mul_abs_le
    have hc : 4 ≤ cϱ := hF.four_le_cϱ
    have hw : 1 ≤ p.w := hF.one_le_w
    have harg : 0 < cϱ * p.L / (4 * p.w) := by positivity
    have hlog : Real.log (cϱ * p.L / (4 * p.w)) ≤ cϱ * p.L / (4 * p.w) := by
      linarith [Real.log_le_sub_one_of_pos harg]
    have hfrac : cϱ * p.L / (4 * p.w) ≤ |cϱ| * p.L := by
      rw [div_le_iff₀ (by positivity), abs_of_nonneg (by linarith)]
      have hcL : 0 ≤ cϱ * p.L := mul_nonneg (by linarith) (by linarith)
      nlinarith [mul_nonneg hcL (by linarith : (0:ℝ) ≤ 4 * p.w - 1)]
    calc ΛΦ ≤ 8 + 8 * Real.log (cϱ * p.L / (4 * p.w)) := h1
      _ ≤ 8 + 8 * (|cϱ| * p.L) := by linarith
      _ ≤ 8 * p.L + 8 * (|cϱ| * p.L) := by linarith
      _ = (8 + 8 * |cϱ|) * p.L := by ring
  -- Chebyshev inputs at x = X (log X = L)
  have hsuma : ∑ n ∈ primeRange p.X, acoef n ≤ 3 * Real.sqrt p.X := h1b p.X hX0
  have hsuma0 : 0 ≤ ∑ n ∈ primeRange p.X, acoef n := Finset.sum_nonneg fun n _ => acoef_nonneg n
  have hsumΛ2 : ∑ n ∈ primeRange p.X, (Λ n : ℝ) ^ 2 ≤ |C1d| * p.X * p.L := by
    have := h1d p.X hX2
    rw [hlogX] at this
    refine this.trans ?_
    have hXL : 0 ≤ p.X * p.L := mul_nonneg (by linarith) (by linarith)
    calc C1d * p.X * p.L = C1d * (p.X * p.L) := by ring
      _ ≤ |C1d| * (p.X * p.L) := mul_le_mul_of_nonneg_right (le_abs_self _) hXL
      _ = |C1d| * p.X * p.L := by ring
  have hsuma2 : ∑ n ∈ primeRange p.X, acoef n ^ 2 ≤ (1 / 2 + |C2a|) * p.L ^ 2 := by
    have := h2a p.X hX2
    rw [hlogX] at this
    simp_rw [acoef_sq]
    have h3 := (abs_le.mp this).2
    unfold primeRange
    calc ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Λ n : ℝ) ^ 2 / n ≤ p.L ^ 2 / 2 + C2a * p.L := by linarith
      _ ≤ p.L ^ 2 / 2 + |C2a| * p.L ^ 2 := by
          have : C2a * p.L ≤ |C2a| * p.L := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
          have : |C2a| * p.L ≤ |C2a| * p.L ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); nlinarith
          linarith
      _ = (1 / 2 + |C2a|) * p.L ^ 2 := by ring
  -- the three pieces
  have hD := diag_estimate hT0 hΦc hF.Phi_sq_integrable hF.Phi_sq_mul_abs_integrable
    hF.Phi_sq_fourier p.X
  have hO1 := O1_bound hMV hCMV.le hT0 hΦc hF.Phi_sq_integrable p.X
  have hO2 := O2_estimate hΦc hF.Phi_sq_integrable p.X p.T
  rw [Mform_PX_PX hT0 hΦc]
  set D := ∑ n ∈ primeRange p.X, acoef n ^ 2 * Aminus F.Phi p.T (Real.log n) (Real.log n)
  set O1 := ∑ n ∈ primeRange p.X, ∑ m ∈ primeRange p.X,
    (if n = m then (0:ℝ) else acoef n * acoef m * Aminus F.Phi p.T (Real.log n) (Real.log m))
  set O2 := ∑ n ∈ primeRange p.X, ∑ m ∈ primeRange p.X,
    acoef n * acoef m * Aplus F.Phi p.T (Real.log n) (Real.log m)
  have hk : (0:ℝ) < 1 / (2 * π ^ 2) := by positivity
  -- piece bounds in the form  ≤ const · L²X
  have bD : |1 / (2 * π ^ 2) * D - p.T / π * sumA2g p.X F.g|
      ≤ 1 / (2 * π ^ 2) * ((1 / 2 + |C2a|) * (8 + 8 * |cϱ|)) * (p.L ^ 2 * p.X) := by
    refine hD.trans ?_
    rw [mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hk.le
    calc (∑ n ∈ primeRange p.X, acoef n ^ 2) * ΛΦ
        ≤ ((1 / 2 + |C2a|) * p.L ^ 2) * ((8 + 8 * |cϱ|) * p.L) := by
          apply mul_le_mul hsuma2 hΛΦle hΛΦ0 (by positivity)
      _ ≤ ((1 / 2 + |C2a|) * p.L ^ 2) * ((8 + 8 * |cϱ|) * p.X) := by gcongr
      _ = (1 / 2 + |C2a|) * (8 + 8 * |cϱ|) * (p.L ^ 2 * p.X) := by ring
  have bO1 : |1 / (2 * π ^ 2) * O1| ≤ 1 / (2 * π ^ 2) * (16 * CMV * (2 * π) * |C1d|) * (p.L ^ 2 * p.X) := by
    rw [abs_mul, abs_of_pos hk, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hk.le
    calc |O1| ≤ 16 * CMV * W * ∑ n ∈ primeRange p.X, (Λ n : ℝ) ^ 2 := hO1
      _ ≤ 16 * CMV * (2 * π * p.L) * (|C1d| * p.X * p.L) := by
          apply mul_le_mul _ hsumΛ2 (Finset.sum_nonneg fun n _ => sq_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hWle (by positivity)
      _ = 16 * CMV * (2 * π) * |C1d| * (p.L ^ 2 * p.X) := by ring
  have bO2 : |1 / (2 * π ^ 2) * O2| ≤ 1 / (2 * π ^ 2) * (2 * π / Real.log 2 * 9) * (p.L ^ 2 * p.X) := by
    rw [abs_mul, abs_of_pos hk, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hk.le
    calc |O2| ≤ W / Real.log 2 * (∑ n ∈ primeRange p.X, acoef n) ^ 2 := hO2
      _ ≤ (2 * π * p.L) / Real.log 2 * (3 * Real.sqrt p.X) ^ 2 := by
          apply mul_le_mul _ _ (sq_nonneg _) (by positivity)
          · exact div_le_div_of_nonneg_right hWle hlog2.le
          · exact pow_le_pow_left₀ hsuma0 hsuma 2
      _ = 2 * π / Real.log 2 * 9 * (p.L * p.X) := by
          rw [mul_pow, Real.sq_sqrt (by linarith)]; ring
      _ ≤ 2 * π / Real.log 2 * 9 * (p.L ^ 2 * p.X) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hLL : p.L ≤ p.L ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right hLL (by linarith)
  -- combine
  have split : 1 / (2 * π ^ 2) * (D + O1 + O2) - p.T / π * sumA2g p.X F.g
      = (1 / (2 * π ^ 2) * D - p.T / π * sumA2g p.X F.g) + 1 / (2 * π ^ 2) * O1
        + 1 / (2 * π ^ 2) * O2 := by ring
  rw [split]
  calc |(1 / (2 * π ^ 2) * D - p.T / π * sumA2g p.X F.g) + 1 / (2 * π ^ 2) * O1 + 1 / (2 * π ^ 2) * O2|
      ≤ |1 / (2 * π ^ 2) * D - p.T / π * sumA2g p.X F.g| + |1 / (2 * π ^ 2) * O1|
        + |1 / (2 * π ^ 2) * O2| := abs_add_three _ _ _
    _ ≤ 1 / (2 * π ^ 2) * ((1 / 2 + |C2a|) * (8 + 8 * |cϱ|)) * (p.L ^ 2 * p.X)
        + 1 / (2 * π ^ 2) * (16 * CMV * (2 * π) * |C1d|) * (p.L ^ 2 * p.X)
        + 1 / (2 * π ^ 2) * (2 * π / Real.log 2 * 9) * (p.L ^ 2 * p.X) := by gcongr
    _ = (1 / (2 * π ^ 2)) * ((1 / 2 + |C2a|) * (8 + 8 * |cϱ|) + 16 * CMV * (2 * π) * |C1d|
      + 2 * π / Real.log 2 * 9) * (p.L ^ 2 * p.X) := by ring

/-- **[prop:PP], the g-sandwich, lower half** (§5.4, verbatim):
"(L−2w)³/6 + O(L²) = Σ_{n≤Xe^{−2w}} a_n²(L−2w−y_n) ≤ Σ_{n≤X} a_n² g(y_n)",
"by [eq:gbounds] and [eq:cheb2] (note a_n² = Λ(n)²/n)".  One-sided, explicit-slack form. -/
theorem sum_a2g_lower (hcheb : Zeta23.ChebyshevMertens) (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAt cϱ lam (fun p F =>
      (p.L - 2 * p.w) ^ 3 / 6 - C * p.L ^ 2 ≤ sumA2g p.X F.g) :=
  sum_a2g_lower' hcheb hlam

/-- **[prop:PP], the g-sandwich, upper half** (§5.4, verbatim):
"Σ_{n≤X} a_n² g(y_n) ≤ Σ_{n≤X} a_n²(L−y_n) = L³/6 + O(L²)". -/
theorem sum_a2g_upper (hcheb : Zeta23.ChebyshevMertens) (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      sumA2g p.X F.g ≤ p.L ^ 3 / 6 + C * p.L ^ 2) :=
  sum_a2g_upper' hcheb hlam

end Results


end PrimeSide
end Zeta23
