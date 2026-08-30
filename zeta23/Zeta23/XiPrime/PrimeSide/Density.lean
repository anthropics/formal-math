/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization.

Zeta23/XiPrime/PrimeSide/Density.lean — generalised-coefficient prime side: the density
ν = μ + cΠ·Π_X + P_c (XiPrime.nucW), its Gram entries / traces / 𝓜, and the §5 sub-results that
need no new idea: [lem:ends] via the ν-generic lem_ends_nu (NuBound for ν), [eq:Msplit]
(bilinearity), and the three sup-bound cross terms [prop:cross](ii)–(iv).
All statements are non-asymptotic in the coefficients: they hold for every coefficient sequence
c : ℕ → ℂ, with the coefficient size entering only through S₁(c) := Σ_{N≤X} ‖c_N‖/√N.
-/
import Zeta23.XiPrime.Defs
import Zeta23.PrimeSideA

noncomputable section

open Real Filter MeasureTheory Set Finset
open scoped BigOperators

namespace Zeta23
namespace XiPrime

open PrimeSide

/-! ## Gram entries, traces and 𝓜 for the density ν = nucW cPi X c -/

/-- `G_{kl} = ∫ φ̂(τ−τ_k) φ̂(τ−τ_l) ν(τ) dτ` at abstract taper data (= `PrimeSide.GentryNu` for
`ν = nucW cPi p.X c`): the entries of [XF′]'s fixed-coefficient matrix `Mᵀ`. -/
abbrev GentryW (cPi : ℝ) (c : ℕ → ℂ) (p : Setting) (F : LocalFun) (k l : ℤ) : ℝ :=
  GentryNu (nucW cPi p.X c) p F k l

/-- `tr M̃ᵀ = L⁻¹ Σ_{k<d} G_{kk}` (shape of `PrimeSide.trGtA`). -/
def trGtW (cPi : ℝ) (c : ℕ → ℂ) (p : Setting) (F : LocalFun) : ℝ :=
  (p.L)⁻¹ * ∑ k : Fin p.d, GentryW cPi c p F k k

/-- `tr (M̃ᵀ)² = L⁻² Σ_{k,l<d} G_{kl}²` (shape of `PrimeSide.trGt2A`). -/
def trGt2W (cPi : ℝ) (c : ℕ → ℂ) (p : Setting) (F : LocalFun) : ℝ :=
  (p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d, GentryW cPi c p F k l ^ 2

/-- `𝓜 = 𝓜[ν, ν]` (= `PrimeSide.MtotalNu`). -/
abbrev MtotalW (cPi : ℝ) (c : ℕ → ℂ) (p : Setting) (F : LocalFun) : ℝ :=
  MtotalNu (nucW cPi p.X c) p F

/-- `S₁(c; X) := Σ_{1≤N≤X} ‖c_N‖/√N` — the only coefficient quantity the sup-bounds see. -/
def S1 (c : ℕ → ℂ) (X : ℝ) : ℝ := ∑ N ∈ Finset.Ioc 0 ⌊X⌋₊, ‖c N‖ / Real.sqrt N

lemma S1_nonneg (c : ℕ → ℂ) (X : ℝ) : 0 ≤ S1 c X :=
  Finset.sum_nonneg fun _ _ => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

/-! ## P_c: triangle inequality and continuity -/

/-- `|Re c · cos θ + Im c · sin θ| ≤ ‖c‖`. -/
lemma abs_re_cos_add_im_sin_le (z : ℂ) (θ : ℝ) :
    |z.re * Real.cos θ + z.im * Real.sin θ| ≤ ‖z‖ := by
  have h1 : (z.re * Real.cos θ + z.im * Real.sin θ) ^ 2 ≤ ‖z‖ ^ 2 := by
    have hcs := Real.cos_sq_add_sin_sq θ
    have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [hn]
    nlinarith [sq_nonneg (z.re * Real.sin θ - z.im * Real.cos θ)]
  exact abs_le_of_sq_le_sq' h1 (norm_nonneg _) |>.elim (fun h2 h3 => abs_le.2 ⟨h2, h3⟩)

/-- `|P_c(X; τ)| ≤ (1/π) S₁(c; X)` for every τ. -/
theorem Pc_abs_le (X : ℝ) (c : ℕ → ℂ) (τ : ℝ) : |Pc X c τ| ≤ (1 / π) * S1 c X := by
  unfold Pc S1
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / π)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun N _ => ?_)
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right (abs_re_cos_add_im_sin_le _ _) (Real.sqrt_nonneg _)

lemma Pc_continuous (X : ℝ) (c : ℕ → ℂ) : Continuous (Pc X c) := by
  unfold Pc
  fun_prop

lemma nucW_continuous (hΓ : Zeta23.GammaFacts) {X : ℝ} (hX : 0 < X) (cPi : ℝ) (c : ℕ → ℂ) :
    Continuous (nucW cPi X c) := by
  have h1 : Continuous Zeta23.mu := hΓ.smooth.continuous
  have h2 := Zeta23.PiX_continuous hX
  have h3 := Pc_continuous X c
  unfold nucW
  fun_prop

/-! ## [eq:Bdef] for ν: NuBound -/

/-- the ν-version of `B`: `B_c := (l + 4√X) + (3|cΠ − 1| + 1)√X + (1/π) S₁(c; X)`. -/
def BcW (cPi : ℝ) (c : ℕ → ℂ) (p : Setting) : ℝ :=
  Bconst p + (3 * |cPi - 1| + 1) * Real.sqrt p.X + (1 / π) * S1 c p.X

lemma l_le_BcW (cPi : ℝ) (c : ℕ → ℂ) (p : Setting) : p.l ≤ BcW cPi c p := by
  unfold BcW Bconst
  have := S1_nonneg c p.X
  have : 0 ≤ Real.sqrt p.X := Real.sqrt_nonneg _
  nlinarith [abs_nonneg (cPi - 1), Real.pi_pos, mul_nonneg (by positivity : (0:ℝ) ≤ 1 / π) (S1_nonneg c p.X)]

/-- **[eq:Bdef] for ν = μ + cΠ·Π_X + P_c**: for `T ≥ T₀(λ)`, every `c`, every `τ`,
`|ν(τ)| ≤ B_c + log⁺(|τ|/4T)`.  From the ζ bound `nuX_abs_le` (H-Γ + the Chebyshev bound) by
`ν − ν_X = (cΠ−1)Π_X + (P_c − P_X)`. -/
theorem nuBoundW_eventually (hΓ : Zeta23.GammaFacts) {lam : ℝ} (hlam : 0 < lam) (cPi : ℝ) :
    ∃ T₀ : ℝ, ∀ p : Setting, p.lam = lam → T₀ ≤ p.T → ∀ c : ℕ → ℂ,
      NuBound p (BcW cPi c p) (nucW cPi p.X c) := by
  obtain ⟨T₁, hT₁⟩ := nuBound_eventually lam hΓ hlam
  obtain ⟨x₀, hx₀⟩ := PrimeSide.PX_abs_le Zeta23.Cheb.chebyshevMertens
  refine ⟨max T₁ (2 * π * Real.exp (|x₀| / lam)), fun p hplam hT c τ => ?_⟩
  have hνX := hT₁ p hplam ((le_max_left _ _).trans hT) τ
  have hlam0 : 0 < p.lam := hplam ▸ hlam
  have hX : x₀ ≤ p.X := Setting.le_X_of_T hlam0 (by rw [hplam]; exact (le_max_right _ _).trans hT)
  have hX1 : 1 ≤ p.X := by
    have : (0:ℝ) ≤ p.L := by
      have := Setting.le_l_of_T (p := p) (l₀ := |x₀| / lam)
        ((le_max_right _ _).trans hT)
      have hl : 0 ≤ p.l := le_trans (by positivity) this
      show 0 ≤ p.lam * Zeta23.l p.T
      exact mul_nonneg hlam0.le hl
    simpa [Setting.X] using Real.one_le_exp this
  have hPi : |Zeta23.PiX p.X τ| ≤ 3 * Real.sqrt p.X := by
    refine (Zeta23.PiX_abs_le hX1 τ).trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg τ, Real.sqrt_nonneg p.X]
  have hPX : |Zeta23.PX p.X τ| ≤ Real.sqrt p.X := hx₀ _ hX τ
  have hPc := Pc_abs_le p.X c τ
  have e : nucW cPi p.X c τ
      = Zeta23.nuX p.X τ + (cPi - 1) * Zeta23.PiX p.X τ + (Pc p.X c τ - Zeta23.PX p.X τ) := by
    unfold nucW Zeta23.nuX; ring
  rw [e]
  unfold BcW
  calc |Zeta23.nuX p.X τ + (cPi - 1) * Zeta23.PiX p.X τ + (Pc p.X c τ - Zeta23.PX p.X τ)|
      ≤ |Zeta23.nuX p.X τ| + |(cPi - 1) * Zeta23.PiX p.X τ| + |Pc p.X c τ - Zeta23.PX p.X τ| :=
        abs_add_three _ _ _
    _ ≤ (Bconst p + max (Real.log (|τ| / (4 * p.T))) 0) + |cPi - 1| * (3 * Real.sqrt p.X)
        + ((1 / π) * S1 c p.X + Real.sqrt p.X) := by
        refine add_le_add (add_le_add hνX ?_) ?_
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_left hPi (abs_nonneg _)
        · exact (abs_sub _ _).trans (add_le_add hPc hPX)
    _ = _ := by ring

/-! ## [lem:ends] for ν -/

/-- **[lem:ends] for ν = μ + cΠ·Π_X + P_c** (from `lem_ends_nu`): for `T ≥ T₀` and every `c`,
`|tr G̃² − 𝓜| ≤ C · L · l · log l · B_c²`,  `B_c = l + O(√X) + (1/π)Σ‖c_N‖/√N`. -/
theorem lem_ends_W {cϱ lam : ℝ} (hΓ : Zeta23.GammaFacts) (hlam : 0 < lam ∧ lam ≤ 1) (cPi : ℝ) :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (c : ℕ → ℂ), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCore cϱ p F →
      |trGt2W cPi c p F - MtotalW cPi c p F|
        ≤ C * (p.L * p.l * Real.log p.l * BcW cPi c p ^ 2) := by
  obtain ⟨C, T₁, h⟩ := lem_ends_nu cϱ lam
  obtain ⟨T₂, hB⟩ := nuBoundW_eventually hΓ hlam.1 cPi
  refine ⟨C, max T₁ T₂, fun p F c hplam hT hF => ?_⟩
  have hX0 : 0 < p.X := Real.exp_pos _
  exact h p F (BcW cPi c p) (nucW cPi p.X c) hplam ((le_max_left _ _).trans hT) hF
    (nucW_continuous hΓ hX0 cPi c) (hB p hplam ((le_max_right _ _).trans hT) c)
    (l_le_BcW cPi c p)

/-- size of `B_c²` under the crude first-moment hypothesis `S₁ ≤ C₁ √X · l`:
`B_c² ≤ K · l² (1 + X)` with `K = 2(6 + 3|cΠ−1| + C₁)²`. -/
theorem BcW_sq_le {cPi C₁ : ℝ} {c : ℕ → ℂ} {p : Setting} (hl : 1 ≤ p.l) (hX : 1 ≤ p.X)
    (hC₁ : 0 ≤ C₁) (hS : S1 c p.X ≤ C₁ * Real.sqrt p.X * p.l) :
    BcW cPi c p ^ 2 ≤ 2 * (6 + 3 * |cPi - 1| + C₁) ^ 2 * (p.l ^ 2 * (1 + p.X)) := by
  have hπ := Real.pi_gt_three
  have hs1 : 1 ≤ Real.sqrt p.X := by
    rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hX
  have hs0 : 0 ≤ Real.sqrt p.X := Real.sqrt_nonneg _
  set s := Real.sqrt p.X
  set A := |cPi - 1|
  have hA : 0 ≤ A := abs_nonneg _
  -- B_c ≤ (6 + 3A + C₁) · l · (1 + s)
  have hB : BcW cPi c p ≤ (6 + 3 * A + C₁) * (p.l * (1 + s)) := by
    unfold BcW Bconst
    have h1 : (1 / π) * S1 c p.X ≤ C₁ * s * p.l := by
      calc (1 / π) * S1 c p.X ≤ 1 * S1 c p.X := by
            apply mul_le_mul_of_nonneg_right _ (S1_nonneg _ _)
            rw [div_le_iff₀ (by linarith)]; linarith
        _ ≤ C₁ * s * p.l := by rw [one_mul]; exact hS
    have h2 : p.l + 4 * s + (3 * A + 1) * s + C₁ * s * p.l ≤ (6 + 3 * A + C₁) * (p.l * (1 + s)) := by
      nlinarith [mul_nonneg hA hs0, mul_nonneg hA (by linarith : (0:ℝ) ≤ p.l),
        mul_nonneg (mul_nonneg hA hs0) (by linarith : (0:ℝ) ≤ p.l - 1),
        mul_nonneg hs0 (by linarith : (0:ℝ) ≤ p.l - 1)]
    show Zeta23.l p.T + 4 * Real.sqrt p.X + (3 * A + 1) * Real.sqrt p.X + 1 / π * S1 c p.X ≤ _
    change p.l + 4 * s + (3 * A + 1) * s + 1 / π * S1 c p.X ≤ _
    linarith
  have hB0 : 0 ≤ BcW cPi c p := le_trans (by linarith) (l_le_BcW cPi c p)
  have hsq : (1 + s) ^ 2 ≤ 2 * (1 + p.X) := by
    have : s ^ 2 = p.X := Real.sq_sqrt (by linarith)
    nlinarith [sq_nonneg (1 - s)]
  calc BcW cPi c p ^ 2 ≤ ((6 + 3 * A + C₁) * (p.l * (1 + s))) ^ 2 :=
        pow_le_pow_left₀ hB0 hB 2
    _ = (6 + 3 * A + C₁) ^ 2 * p.l ^ 2 * (1 + s) ^ 2 := by ring
    _ ≤ (6 + 3 * A + C₁) ^ 2 * p.l ^ 2 * (2 * (1 + p.X)) := by gcongr
    _ = _ := by ring

/-! ## [eq:Msplit] for ν -/

/-- **[eq:Msplit] for ν = μ + cΠ·Π_X + P_c**: the six-term bilinear expansion, with the pole
weight riding on the Π-terms. -/
theorem eq_Msplit_W {cϱ : ℝ} (hΓ : Zeta23.GammaFacts) (cPi : ℝ) (c : ℕ → ℂ) (p : Setting)
    (F : LocalFun) (hF : LocalHypsCore cϱ p F) :
    MtotalW cPi c p F =
      Mform F.Phi p.T Zeta23.mu Zeta23.mu + Mform F.Phi p.T (Pc p.X c) (Pc p.X c)
        + 2 * Mform F.Phi p.T Zeta23.mu (Pc p.X c)
        + 2 * (cPi * Mform F.Phi p.T Zeta23.mu (Zeta23.PiX p.X))
        + 2 * (cPi * Mform F.Phi p.T (Pc p.X c) (Zeta23.PiX p.X))
        + cPi ^ 2 * Mform F.Phi p.T (Zeta23.PiX p.X) (Zeta23.PiX p.X) := by
  have hΦ := hF.Phi_contDiff.continuous
  have hμ : Continuous Zeta23.mu := hΓ.smooth.continuous
  have hPiC : Continuous (fun τ => cPi * Zeta23.PiX p.X τ) := continuous_const.mul hF.PiX_cont
  have hP := Pc_continuous p.X c
  have hν : nucW cPi p.X c = Zeta23.mu + (fun τ => cPi * Zeta23.PiX p.X τ) + Pc p.X c := by
    funext τ; simp [nucW]
  show Mform F.Phi p.T (nucW cPi p.X c) (nucW cPi p.X c) = _
  rw [hν, Mform_trinomial hΦ hF.Phi_even hμ hPiC hP]
  have e1 : Mform F.Phi p.T Zeta23.mu (fun τ => cPi * Zeta23.PiX p.X τ)
      = cPi * Mform F.Phi p.T Zeta23.mu (Zeta23.PiX p.X) := by
    rw [show (fun τ => cPi * Zeta23.PiX p.X τ) = fun τ => cPi * (Zeta23.PiX p.X) τ from rfl,
      Mform_const_mul_right]
  have e2 : Mform F.Phi p.T (Pc p.X c) (fun τ => cPi * Zeta23.PiX p.X τ)
      = cPi * Mform F.Phi p.T (Pc p.X c) (Zeta23.PiX p.X) := by
    rw [show (fun τ => cPi * Zeta23.PiX p.X τ) = fun τ => cPi * (Zeta23.PiX p.X) τ from rfl,
      Mform_const_mul_right]
  have e3 : Mform F.Phi p.T (fun τ => cPi * Zeta23.PiX p.X τ) (fun τ => cPi * Zeta23.PiX p.X τ)
      = cPi ^ 2 * Mform F.Phi p.T (Zeta23.PiX p.X) (Zeta23.PiX p.X) := by
    rw [show (fun τ => cPi * Zeta23.PiX p.X τ) = fun τ => cPi * (Zeta23.PiX p.X) τ from rfl,
      Mform_const_mul_right, Mform_const_mul_left]
    ring
  rw [e1, e2, e3]

/-! ## [prop:cross] (ii)–(iv) for ν: the sup-bound terms -/

/-- **[prop:cross](iii) for P_c**: `|𝓜[P_c, Π_X]| ≤ 6 S₁(c) · L √X` (sup bounds `|P_c| ≤ S₁/π`,
`|Π_X| ≤ 3√X/T` on `I`, `∫Φ² ≤ 2πL`). -/
theorem cross_PcPi_le {cϱ : ℝ} {p : Setting} {F : LocalFun} (hF : LocalHypsCore cϱ p F)
    (hT : 0 < p.T) (c : ℕ → ℂ) :
    |Mform F.Phi p.T (Pc p.X c) (Zeta23.PiX p.X)| ≤ 6 * S1 c p.X * (p.L * Real.sqrt p.X) := by
  have hπ := Real.pi_pos
  have hP : ∀ τ ∈ Set.Icc p.T (2 * p.T), |Pc p.X c τ| ≤ (1 / π) * S1 c p.X :=
    fun τ _ => Pc_abs_le p.X c τ
  have hPi := hF.PiX_le_on_I hT
  have h := abs_Mform_le hT.le hF.Phi_contDiff.continuous (Pc_continuous p.X c) hF.PiX_cont
    hF.Phi_sq_integrable hP hPi
  have hX0 := hF.integral_Phi_sq_le
  have hS := S1_nonneg c p.X
  calc |Mform F.Phi p.T (Pc p.X c) (Zeta23.PiX p.X)|
      ≤ (1 / π) * S1 c p.X * (3 * Real.sqrt p.X / p.T) * (p.T * ∫ x, F.Phi x ^ 2) := h
    _ ≤ (1 / π) * S1 c p.X * (3 * Real.sqrt p.X / p.T) * (p.T * (2 * π * p.L)) := by gcongr
    _ = 6 * S1 c p.X * (p.L * Real.sqrt p.X) := by field_simp <;> ring

end XiPrime
end Zeta23
