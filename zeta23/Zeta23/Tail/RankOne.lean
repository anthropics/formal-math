/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/RankOne.lean — the linear-algebra step of [prop:tail] (the paper §4.2):
eigenvalue bounds for a (possibly infinite) sum of rank-one matrices m_ρ u_ρ u_ρᵀ.


Paper, verbatim (proof of [prop:tail]): "Since E = ∑_{γ∉I'} m_ρ u_ρ u_ρᵀ and
‖uuᵀ‖ = ‖u‖₂², ‖E‖ ≤ ∑_{γ∉I'} m_ρ ‖u_ρ‖₂²  [eq:Enormsum]" … "The trace-norm bound follows
from the same chain, since ‖uuᵀ‖₁ = ‖u‖₂² as well".

Design (avoiding Schatten-norm machinery): the trace norm of a Hermitian
matrix is DEFINED here as traceNorm hE := ∑ᵢ |λᵢ(E)|, and the operator-norm bound is
delivered in the shape RHLinalg.weyl_posIndexAbove_le consumes, namely ∀ i, |λᵢ(E)| ≤ θ.
Both follow from one inequality, traceNorm hE ≤ ∑_ρ c_ρ ‖u_ρ‖₂², proved directly in the
eigenbasis: λᵢ = vᵢ* E vᵢ = ∑_ρ c_ρ ⟨vᵢ,u_ρ⟩⟨v̄ᵢ,u_ρ⟩, |⟨vᵢ,u_ρ⟩⟨v̄ᵢ,u_ρ⟩| ≤ (|⟨vᵢ,u_ρ⟩|² +
|⟨vᵢ,ū_ρ⟩|²)/2, and Parseval ∑ᵢ|⟨vᵢ,w⟩|² = ‖w‖² for the unitary eigenvector matrix.
NOTE u_ρ u_ρᵀ (Matrix.vecMulVec u u), NOT u_ρ u_ρ*: the u_ρ = (φ̂(γ_ρ − τ_k))_k are complex
for off-line zeros and the paper's E is complex-symmetric termwise; Hermitian-ness of the
total (from the ρ ↦ 1−ρ̄ symmetry) is taken as the hypothesis hE.
-/
import Zeta23.LinAlg.Sylvester
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace Zeta23
namespace Tail

open RHLinalg

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Trace norm ‖E‖₁ of a Hermitian matrix, DEFINED as ∑ᵢ |λᵢ(E)| (= sum of singular values
for Hermitian E). Paper: "the trace norm ‖Ê‖₁" in [prop:tail]; consumed in
[prop:zeroside-rank] via |tr Ê| ≤ ‖Ê‖₁ and ‖Ê‖_F ≤ ‖Ê‖₁ (both proved below). -/
def traceNorm {E : Matrix n n ℂ} (hE : E.IsHermitian) : ℝ := ∑ i, |hE.eigenvalues i|

omit [DecidableEq n] in
lemma traceNorm_def [DecidableEq n] {E : Matrix n n ℂ} (hE : E.IsHermitian) :
    traceNorm hE = ∑ i, |hE.eigenvalues i| := rfl

lemma traceNorm_nonneg {E : Matrix n n ℂ} (hE : E.IsHermitian) : 0 ≤ traceNorm hE :=
  sum_nonneg fun _ _ => abs_nonneg _

/-- |tr E| ≤ ‖E‖₁ (used in [prop:zeroside-rank]: "|tr Ê| ≤ ‖Ê‖₁"). -/
lemma abs_rtrace_le_traceNorm {E : Matrix n n ℂ} (hE : E.IsHermitian) :
    |rtrace E| ≤ traceNorm hE := by
  rw [rtrace_eq_sum_eigenvalues hE]
  exact abs_sum_le_sum_abs _ _

/-- ‖E‖_F² ≤ ‖E‖₁² (used in [prop:zeroside-rank]: "‖Â‖_F ≤ ‖Ĝ‖_F + ‖Ê‖_F ≤ ‖Ĝ‖_F + ‖Ê‖₁"). -/
lemma frobSq_le_traceNorm_sq {E : Matrix n n ℂ} (hE : E.IsHermitian) :
    frobSq E ≤ (traceNorm hE) ^ 2 := by
  rw [frobSq_hermitian_eq_sum_sq_eigenvalues hE, traceNorm]
  calc ∑ i, hE.eigenvalues i ^ 2 = ∑ i, |hE.eigenvalues i| ^ 2 := by simp [sq_abs]
    _ ≤ (∑ i, |hE.eigenvalues i|) ^ 2 :=
      sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg _)

/-- Every |λᵢ(E)| is at most ‖E‖₁ (so a trace-norm bound is also an operator-norm bound in
the shape RHLinalg.weyl_posIndexAbove_le wants). -/
lemma abs_eigenvalues_le_traceNorm {E : Matrix n n ℂ} (hE : E.IsHermitian) (i : n) :
    |hE.eigenvalues i| ≤ traceNorm hE :=
  single_le_sum (f := fun i => |hE.eigenvalues i|) (fun _ _ => abs_nonneg _) (mem_univ i)

/-- ab ≤ (a² + b²)/2. -/
private lemma mul_le_half_sq_add_sq (a b : ℝ) : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- **[eq:Enormsum], trace-norm form.** If a Hermitian matrix E is the convergent sum
∑_ρ c_ρ · u_ρ u_ρᵀ (c_ρ ≥ 0, u_ρ ∈ ℂⁿ, vecMulVec u u = u uᵀ — no conjugation) and
∑_ρ c_ρ ‖u_ρ‖₂² converges to S, then ‖E‖₁ = ∑ᵢ|λᵢ(E)| ≤ S.
Paper: "‖uuᵀ‖ = ‖u‖₂²" and "‖uuᵀ‖₁ = ‖u‖₂² as well". -/
theorem traceNorm_le_of_hasSum_vecMulVec {ι : Type*} {E : Matrix n n ℂ}
    (hE : E.IsHermitian) (c : ι → ℝ) (hc : ∀ ρ, 0 ≤ c ρ) (u : ι → n → ℂ) {S : ℝ}
    (hS : HasSum (fun ρ => c ρ * ∑ k, ‖u ρ k‖ ^ 2) S)
    (hEsum : HasSum (fun ρ => ((c ρ : ℝ) : ℂ) • vecMulVec (u ρ) (u ρ)) E) :
    traceNorm hE ≤ S := by
  set U : Matrix n n ℂ := (hE.eigenvectorUnitary : Matrix n n ℂ) with hU
  -- coordinates of u_ρ and ū_ρ in the eigenbasis
  set α : n → ι → ℂ := fun i ρ => (star U *ᵥ u ρ) i with hα
  set β : n → ι → ℂ := fun i ρ => (star U *ᵥ star (u ρ)) i with hβ
  -- Step 1: entrywise HasSum for E.
  have hEkl : ∀ k l, HasSum (fun ρ => ((c ρ : ℝ) : ℂ) * (u ρ k * u ρ l)) (E k l) := by
    intro k l
    have := (Pi.hasSum.mp (Pi.hasSum.mp hEsum k)) l
    simpa only [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul] using this
  -- Step 2: λᵢ = vᵢ* E vᵢ = ∑_ρ c_ρ αᵢρ · conj(βᵢρ), vᵢ = i-th column of U.
  have hlam : ∀ i, HasSum (fun ρ => ((c ρ : ℝ) : ℂ) * (α i ρ * star (β i ρ)))
      ((hE.eigenvalues i : ℝ) : ℂ) := by
    intro i
    have hv : (fun k => U k i) = (hE.eigenvectorBasis i).ofLp := by
      funext k; exact hE.eigenvectorUnitary_apply k i
    have hEv : E *ᵥ (fun k => U k i) = ((hE.eigenvalues i : ℝ) : ℂ) • (fun k => U k i) := by
      have h := hE.mulVec_eigenvectorBasis i
      rw [← hv] at h
      rw [h]
      funext k
      simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
    have hvv : star (fun k => U k i) ⬝ᵥ (fun k => U k i) = 1 := by
      have h1 := Matrix.UnitaryGroup.star_mul_self hE.eigenvectorUnitary
      have := congrFun (congrFun h1 i) i
      simpa [hU, Matrix.mul_apply, Matrix.star_apply, dotProduct] using this
    have hquad : star (fun k => U k i) ⬝ᵥ (E *ᵥ fun k => U k i)
        = ((hE.eigenvalues i : ℝ) : ℂ) := by
      rw [hEv, dotProduct_smul, hvv, smul_eq_mul, mul_one]
    have hexp : star (fun k => U k i) ⬝ᵥ (E *ᵥ fun k => U k i)
        = ∑ k, star (U k i) * ∑ l, E k l * U l i := by
      simp only [dotProduct, mulVec, Pi.star_apply]
    have h2 : HasSum (fun ρ => ∑ k, star (U k i) *
        ∑ l, (((c ρ : ℝ) : ℂ) * (u ρ k * u ρ l)) * U l i)
        (∑ k, star (U k i) * ∑ l, E k l * U l i) := by
      apply hasSum_sum; intro k _
      apply HasSum.mul_left
      apply hasSum_sum; intro l _
      exact (hEkl k l).mul_right _
    rw [← hexp, hquad] at h2
    convert h2 using 1
    funext ρ
    simp only [hα, hβ, mulVec, dotProduct, Matrix.star_apply, Pi.star_apply, star_sum, star_mul',
      star_star]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  -- Step 3: the majorant Fᵢρ := c_ρ (|αᵢρ|² + |βᵢρ|²)/2, with ∑ᵢ Fᵢρ = c_ρ ‖u_ρ‖² (Parseval).
  set F : n → ι → ℝ := fun i ρ => c ρ * ((‖α i ρ‖ ^ 2 + ‖β i ρ‖ ^ 2) / 2) with hF
  have hF_sum : ∀ ρ, ∑ i, F i ρ = c ρ * ∑ k, ‖u ρ k‖ ^ 2 := by
    intro ρ
    simp only [hF, hα, hβ]
    rw [← mul_sum, ← sum_div, sum_add_distrib, sum_normSq_unitary_mulVec hE (u ρ),
      sum_normSq_unitary_mulVec hE (star (u ρ))]
    congr 1
    simp only [Pi.star_apply, norm_star]
    ring
  have hF_nonneg : ∀ i ρ, 0 ≤ F i ρ := fun i ρ => by
    have := hc ρ; simp only [hF]; positivity
  have hF_summable : ∀ i, Summable (F i) := by
    intro i
    refine Summable.of_nonneg_of_le (hF_nonneg i) (fun ρ => ?_) hS.summable
    rw [← hF_sum ρ]
    exact single_le_sum (f := fun j => F j ρ) (fun j _ => hF_nonneg j ρ) (mem_univ i)
  -- Step 4: |λᵢ| ≤ ∑' ρ, Fᵢρ.
  have hbound : ∀ i, |hE.eigenvalues i| ≤ ∑' ρ, F i ρ := by
    intro i
    have h := HasSum.norm_le_of_bounded (hlam i) (hF_summable i).hasSum (fun ρ => ?_)
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using h
    · rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg (hc ρ)]
      simp only [hF]
      exact mul_le_mul_of_nonneg_left (mul_le_half_sq_add_sq _ _) (hc ρ)
  -- Step 5: sum over i and swap the finite sum with the series.
  calc traceNorm hE = ∑ i, |hE.eigenvalues i| := rfl
    _ ≤ ∑ i, ∑' ρ, F i ρ := sum_le_sum fun i _ => hbound i
    _ = ∑' ρ, ∑ i, F i ρ := (Summable.tsum_finsetSum (fun i _ => hF_summable i)).symm
    _ = ∑' ρ, c ρ * ∑ k, ‖u ρ k‖ ^ 2 := tsum_congr hF_sum
    _ = S := hS.tsum_eq

/-- **[eq:Enormsum], operator-norm form** (the shape RHLinalg.weyl_posIndexAbove_le wants):
under the same hypotheses every eigenvalue satisfies |λᵢ(E)| ≤ S, i.e. ‖E‖ ≤ S.
Paper: "‖E‖ ≤ ∑_{γ∉I'} m_ρ ‖u_ρ‖₂²". -/
theorem abs_eigenvalues_le_of_hasSum_vecMulVec {ι : Type*} {E : Matrix n n ℂ}
    (hE : E.IsHermitian) (c : ι → ℝ) (hc : ∀ ρ, 0 ≤ c ρ) (u : ι → n → ℂ) {S : ℝ}
    (hS : HasSum (fun ρ => c ρ * ∑ k, ‖u ρ k‖ ^ 2) S)
    (hEsum : HasSum (fun ρ => ((c ρ : ℝ) : ℂ) • vecMulVec (u ρ) (u ρ)) E) (i : n) :
    |hE.eigenvalues i| ≤ S :=
  (abs_eigenvalues_le_traceNorm hE i).trans
    (traceNorm_le_of_hasSum_vecMulVec hE c hc u hS hEsum)

end Tail
end Zeta23
