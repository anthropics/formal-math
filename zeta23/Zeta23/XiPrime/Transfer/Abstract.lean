/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization.

Zeta23/XiPrime/Transfer/Abstract.lean — ξ′ trace transfer [XF′ Lemma 5.1 + Lemma 6.1]: the
matrix-algebra and elementary-sum lemmas, with NO reference to ξ′, φ̂ or the prime side.

Contents (all over `Matrix n n ℂ`, `n` a Fintype, with RHLinalg.rtrace / frobSq):
  A. entrywise bounds ⇒ |tr| and ‖·‖_F² bounds; the Hadamard scaling ‖Δ∘Q‖_F ≤ (max|Δ|)‖Q‖_F.
  B. "Minkowski for a series of matrices": if the partial sums Σ_{r<R} S_r converge entrywise to D
     and Σ_r ‖S_r‖_F ≤ B then ‖D‖_F² ≤ B²  ([XF′ Lemma 6.1]: ‖M − Mᵀ‖_F ≤ Σ_r 0.38^r ‖Q^{(r)}‖_F).
  C. Abel summation with monotone bounded weights ([XF′ Lemma 6.1], trace part: the weights
     δ_k^r = (½ log(τ_k/T))^r are monotone in k).
  D. the lattice sum Σ_{l<d} min(1, ((k−l)h)⁻²)² ≤ 64(1 + 1/h)  ([XF′ Lemma 5.1]: "for fixed k,
     Σ_l min(1, |(l−k)h|⁻³) ≪ 1/h = L/2π").
  E. the three-matrix bookkeeping G = Mᵀ + D + E ⇒ the two inequalities of XiTraceTransfer with
     explicit losses.
-/
import Zeta23.Assembly
import Mathlib.Algebra.BigOperators.Module

noncomputable section

open Finset Filter Topology RHLinalg

namespace Zeta23
namespace XiPrime
namespace Transfer

variable {n : Type*} [Fintype n]

/-! ### A. Entrywise bounds -/

lemma abs_rtrace_le_sum_norm_diag (A : Matrix n n ℂ) : |rtrace A| ≤ ∑ i, ‖A i i‖ := by
  unfold rtrace
  simp only [Matrix.trace, Matrix.diag_apply, map_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  exact RCLike.abs_re_le_norm (A i i)

lemma frobSq_le_of_norm_le (A : Matrix n n ℂ) (B : n → n → ℝ) (h : ∀ i j, ‖A i j‖ ≤ B i j) :
    frobSq A ≤ ∑ i, ∑ j, B i j ^ 2 := by
  rw [Assembly.frobSq_eq_sum_norm_sq]
  gcongr with i _ j _
  exact h i j

/-- the Hadamard (entrywise) product with a real matrix of entries bounded by θ scales ‖·‖_F² by
at most θ². -/
lemma frobSq_hadamard_le (Δ : n → n → ℝ) (Q : Matrix n n ℂ) {θ : ℝ}
    (hΔ : ∀ i j, |Δ i j| ≤ θ) :
    frobSq (fun i j => (Δ i j : ℂ) * Q i j) ≤ θ ^ 2 * frobSq Q := by
  -- Lean 4.33: `rw` can no longer instantiate `?A : Matrix n n ℂ` with a bare lambda (type defeq only by delta);
  -- `erw` matches at default transparency.
  erw [Assembly.frobSq_eq_sum_norm_sq, Assembly.frobSq_eq_sum_norm_sq, mul_sum]
  refine sum_le_sum fun i _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun j _ => ?_
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
  have := hΔ i j
  have h0 : 0 ≤ |Δ i j| := abs_nonneg _
  gcongr

lemma sqrt_frobSq_hadamard_le (Δ : n → n → ℝ) (Q : Matrix n n ℂ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hΔ : ∀ i j, |Δ i j| ≤ θ) :
    Real.sqrt (frobSq (fun i j => (Δ i j : ℂ) * Q i j)) ≤ θ * Real.sqrt (frobSq Q) := by
  have h := frobSq_hadamard_le Δ Q hΔ
  calc Real.sqrt (frobSq (fun i j => (Δ i j : ℂ) * Q i j))
      ≤ Real.sqrt (θ ^ 2 * frobSq Q) := Real.sqrt_le_sqrt h
    _ = θ * Real.sqrt (frobSq Q) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hθ]

/-! ### B. Minkowski for a series of matrices, via partial sums -/

section Frob
open scoped Matrix.Norms.Frobenius

/-- If ‖S_r‖_F ≤ s_r with Σ_{r<R} s_r ≤ B for every R, and the partial sums Σ_{r<R} S_r converge to D
entrywise, then ‖D‖_F² ≤ B². -/
theorem frobSq_le_of_tendsto_partialSums (D : Matrix n n ℂ) (S : ℕ → Matrix n n ℂ) (s : ℕ → ℝ)
    (hs0 : ∀ r, 0 ≤ s r) (hS : ∀ r, frobSq (S r) ≤ s r ^ 2) {B : ℝ}
    (hB : ∀ R, ∑ r ∈ range R, s r ≤ B)
    (hlim : ∀ i j, Tendsto (fun R => ∑ r ∈ range R, S r i j) atTop (𝓝 (D i j))) :
    frobSq D ≤ B ^ 2 := by
  have hB0 : 0 ≤ B := by simpa using hB 0
  have hR : ∀ R, frobSq (∑ r ∈ range R, S r) ≤ B ^ 2 := by
    intro R
    rw [Assembly.frobSq_eq_norm_sq]
    have h1 : ‖∑ r ∈ range R, S r‖ ≤ ∑ r ∈ range R, s r := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun r _ => ?_)
      rw [Assembly.norm_eq_sqrt_frobSq]
      exact (Real.sqrt_le_sqrt (hS r)).trans (le_of_eq (Real.sqrt_sq (hs0 r)))
    exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans (hB R)) 2
  have hlim2 : Tendsto (fun R => frobSq (∑ r ∈ range R, S r)) atTop (𝓝 (frobSq D)) := by
    have e : ∀ M : Matrix n n ℂ, frobSq M = ∑ i, ∑ j, ‖M i j‖ ^ 2 :=
      fun M => Assembly.frobSq_eq_sum_norm_sq M
    simp only [e]
    refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => ?_
    have : Tendsto (fun R => (∑ r ∈ range R, S r) i j) atTop (𝓝 (D i j)) := by
      simp only [Matrix.sum_apply]; exact hlim i j
    exact (this.norm).pow 2
  exact le_of_tendsto' hlim2 hR

end Frob

/-! ### C. Abel summation with monotone bounded weights -/

/-- If 0 ≤ w_k ≤ W is monotone and every partial sum |Σ_{k<K} q_k| (K ≤ d) is at most B, then
|Σ_{k<d} w_k q_k| ≤ 2WB. -/
theorem abs_sum_mul_le_of_monotone (d : ℕ) (w q : ℕ → ℝ) {W B : ℝ}
    (hw0 : ∀ k, 0 ≤ w k) (hwW : ∀ k, w k ≤ W) (hmono : Monotone w)
    (hq : ∀ K ≤ d, |∑ k ∈ range K, q k| ≤ B) :
    |∑ k ∈ range d, w k * q k| ≤ 2 * W * B := by
  have hB0 : 0 ≤ B := by simpa using hq 0 (Nat.zero_le _)
  have hW0 : 0 ≤ W := (hw0 0).trans (hwW 0)
  have habel := Finset.sum_range_by_parts w q d
  simp only [smul_eq_mul] at habel
  rw [habel]
  have h1 : |w (d - 1) * ∑ k ∈ range d, q k| ≤ W * B := by
    rw [abs_mul, abs_of_nonneg (hw0 _)]
    exact mul_le_mul (hwW _) (hq d le_rfl) (abs_nonneg _) hW0
  have h2 : |∑ i ∈ range (d - 1), (w (i + 1) - w i) * ∑ k ∈ range (i + 1), q k| ≤ W * B := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have h3 : ∀ i ∈ range (d - 1),
        |(w (i + 1) - w i) * ∑ k ∈ range (i + 1), q k| ≤ (w (i + 1) - w i) * B := by
      intro i hi
      have hi' : i + 1 ≤ d := by
        have := Finset.mem_range.1 hi; omega
      rw [abs_mul, abs_of_nonneg (sub_nonneg.2 (hmono (Nat.le_succ i)))]
      exact mul_le_mul_of_nonneg_left (hq _ hi') (sub_nonneg.2 (hmono (Nat.le_succ i)))
    refine (sum_le_sum h3).trans ?_
    rw [← sum_mul, Finset.sum_range_sub]
    have : w (d - 1) - w 0 ≤ W := by linarith [hw0 0, hwW (d - 1)]
    exact mul_le_mul_of_nonneg_right this hB0
  calc |w (d - 1) * ∑ k ∈ range d, q k
        - ∑ i ∈ range (d - 1), (w (i + 1) - w i) * ∑ k ∈ range (i + 1), q k|
      ≤ |w (d - 1) * ∑ k ∈ range d, q k|
        + |∑ i ∈ range (d - 1), (w (i + 1) - w i) * ∑ k ∈ range (i + 1), q k| := abs_sub _ _
    _ ≤ W * B + W * B := add_le_add h1 h2
    _ = 2 * W * B := by ring

/-! ### D. The lattice sum  Σ_l min(1, ((k−l)h)⁻²)² ≪ 1/h -/

/-- telescoping: Σ_{m<R} 1/((m+1)h+1)² ≤ 1/h. -/
lemma sum_inv_affine_sq_le {h : ℝ} (hh : 0 < h) (R : ℕ) :
    ∑ m ∈ range R, 1 / (((m:ℝ) + 1) * h + 1) ^ 2 ≤ 1 / h := by
  have key : ∀ R : ℕ, ∑ m ∈ range R, 1 / (((m:ℝ) + 1) * h + 1) ^ 2
      ≤ 1 / h - 1 / (h * ((R:ℝ) * h + 1)) := by
    intro R
    induction R with
    | zero => simp
    | succ R ih =>
      rw [Finset.sum_range_succ]
      have hR0 : (0:ℝ) ≤ R := Nat.cast_nonneg R
      have hA : 0 < (R:ℝ) * h + 1 := by positivity
      have hB : 0 < ((R:ℝ) + 1) * h + 1 := by positivity
      have step : 1 / (((R:ℝ) + 1) * h + 1) ^ 2
          ≤ 1 / (h * ((R:ℝ) * h + 1)) - 1 / (h * ((((R + 1 : ℕ) : ℝ)) * h + 1)) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        ring_nf
        nlinarith [mul_pos hh hA, mul_pos hh hB, sq_nonneg h, mul_nonneg (mul_pos hh hh).le hR0]
      push_cast at step ⊢
      linarith
  have hR : 0 ≤ 1 / (h * ((R:ℝ) * h + 1)) := by positivity
  linarith [key R]

/-- Σ_{m<R} 1/(m h+1)² ≤ 1 + 1/h. -/
lemma sum_inv_affine_sq_le' {h : ℝ} (hh : 0 < h) (R : ℕ) :
    ∑ m ∈ range R, 1 / ((m:ℝ) * h + 1) ^ 2 ≤ 1 + 1 / h := by
  cases R with
  | zero => simp; positivity
  | succ R =>
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, zero_add, one_pow, div_one]
    linarith [sum_inv_affine_sq_le hh R]

/-- pointwise: 1/max(1, x²) ≤ 4/(|x|+1)². -/
lemma inv_max_one_sq_le (x : ℝ) : 1 / max 1 (x ^ 2) ≤ 4 / (|x| + 1) ^ 2 := by
  have hx := abs_nonneg x
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  rcases le_or_gt (|x|) 1 with h | h
  · calc (|x| + 1) ^ 2 ≤ (1 + 1) ^ 2 := by gcongr
      _ = 4 * 1 := by norm_num
      _ ≤ 4 * max 1 (x ^ 2) := by gcongr; exact le_max_left _ _
  · calc (|x| + 1) ^ 2 ≤ (|x| + |x|) ^ 2 := by gcongr
      _ = 4 * x ^ 2 := by rw [← sq_abs x]; ring
      _ ≤ 4 * max 1 (x ^ 2) := by gcongr; exact le_max_right _ _

/-- **the lattice sum**: for h > 0 and any k < d,
Σ_{l<d} (1/max(1, ((k−l)h)²))² ≤ 8(1 + 1/h). -/
theorem lattice_sum_le {h : ℝ} (hh : 0 < h) (d k : ℕ) (hk : k < d) :
    ∑ l ∈ range d, (1 / max 1 ((((k:ℝ) - l) * h) ^ 2)) ^ 2 ≤ 8 * (1 + 1 / h) := by
  -- (1/max)^2 ≤ 1/max ≤ 4/(|k-l|h+1)^2
  have hpt : ∀ l : ℕ, (1 / max 1 ((((k:ℝ) - l) * h) ^ 2)) ^ 2
      ≤ 4 / ((|(k:ℝ) - l| * h + 1)) ^ 2 := by
    intro l
    have h1 : 1 / max 1 ((((k:ℝ) - l) * h) ^ 2) ≤ 1 :=
      div_le_one_of_le₀ (le_max_left _ _) (by positivity)
    have h0 : 0 ≤ 1 / max 1 ((((k:ℝ) - l) * h) ^ 2) := by positivity
    calc (1 / max 1 ((((k:ℝ) - l) * h) ^ 2)) ^ 2
        ≤ 1 / max 1 ((((k:ℝ) - l) * h) ^ 2) := by nlinarith
      _ ≤ 4 / (|((k:ℝ) - l) * h| + 1) ^ 2 := inv_max_one_sq_le _
      _ = 4 / ((|(k:ℝ) - l| * h + 1)) ^ 2 := by rw [abs_mul, abs_of_pos hh]
  refine (sum_le_sum fun l _ => hpt l).trans ?_
  -- split range d = range k ∪ Ico k d
  rw [← Finset.sum_range_add_sum_Ico _ hk.le]
  have hleft : ∑ l ∈ range k, 4 / ((|(k:ℝ) - l| * h + 1)) ^ 2 ≤ 4 * (1 + 1 / h) := by
    have e : ∑ l ∈ range k, 4 / ((|(k:ℝ) - l| * h + 1)) ^ 2
        = ∑ m ∈ range k, 4 * (1 / ((((m:ℝ) + 1)) * h + 1) ^ 2) := by
      rw [← Finset.sum_range_reflect]
      refine sum_congr rfl fun m hm => ?_
      have hm' := Finset.mem_range.1 hm
      have : ((k - 1 - m : ℕ) : ℝ) = (k:ℝ) - 1 - m := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
      rw [this, show (k:ℝ) - ((k:ℝ) - 1 - m) = m + 1 by ring,
        abs_of_nonneg (by positivity)]
      ring
    rw [e, ← mul_sum]
    have := sum_inv_affine_sq_le hh k
    nlinarith
  have hright : ∑ l ∈ Ico k d, 4 / ((|(k:ℝ) - l| * h + 1)) ^ 2 ≤ 4 * (1 + 1 / h) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have e : ∑ m ∈ range (d - k), 4 / ((|(k:ℝ) - ((k + m : ℕ) : ℝ)| * h + 1)) ^ 2
        = ∑ m ∈ range (d - k), 4 * (1 / (((m:ℝ)) * h + 1) ^ 2) := by
      refine sum_congr rfl fun m _ => ?_
      push_cast
      rw [show (k:ℝ) - (k + m) = -m by ring, abs_neg, abs_of_nonneg (Nat.cast_nonneg m)]
      ring
    rw [e, ← mul_sum]
    have := sum_inv_affine_sq_le' hh (d - k)
    nlinarith
  linarith

/-! ### E. Three-matrix bookkeeping -/

section Frob2
open scoped Matrix.Norms.Frobenius

/-- G = M + D + E ⇒ tr G − tr M = tr D + tr E. -/
lemma rtrace_sub_of_decomp {G M D E : Matrix n n ℂ} (h : G = M + D + E) :
    rtrace G - rtrace M = rtrace D + rtrace E := by
  rw [h, rtrace_add, rtrace_add]; ring

/-- G = M + D + E, ‖D‖_F² ≤ ε_D² N, ‖E‖_F² ≤ ε_E² N ⇒ with η := ε_D + ε_E,
‖G‖_F² ≤ (1 + η)‖M‖_F² + (η + η²) N   (from ‖G‖_F ≤ ‖M‖_F + η√N and 2‖M‖_F√N ≤ ‖M‖_F² + N). -/
theorem frobSq_le_of_decomp {G M D E : Matrix n n ℂ} (h : G = M + D + E) {N εD εE : ℝ}
    (hN : 0 ≤ N) (hεD : 0 ≤ εD) (hεE : 0 ≤ εE)
    (hD : frobSq D ≤ εD ^ 2 * N) (hE : frobSq E ≤ εE ^ 2 * N) :
    frobSq G ≤ (1 + (εD + εE)) * frobSq M + ((εD + εE) + (εD + εE) ^ 2) * N := by
  set η := εD + εE with hη
  have hη0 : 0 ≤ η := add_nonneg hεD hεE
  have hm0 : 0 ≤ ‖M‖ := norm_nonneg _
  have hsN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hsN2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN
  have hDn : ‖D‖ ≤ εD * Real.sqrt N := by
    rw [Assembly.norm_eq_sqrt_frobSq]
    calc Real.sqrt (frobSq D) ≤ Real.sqrt (εD ^ 2 * N) := Real.sqrt_le_sqrt hD
      _ = εD * Real.sqrt N := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hεD]
  have hEn : ‖E‖ ≤ εE * Real.sqrt N := by
    rw [Assembly.norm_eq_sqrt_frobSq]
    calc Real.sqrt (frobSq E) ≤ Real.sqrt (εE ^ 2 * N) := Real.sqrt_le_sqrt hE
      _ = εE * Real.sqrt N := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hεE]
  have hG : ‖G‖ ≤ ‖M‖ + η * Real.sqrt N := by
    rw [h]
    calc ‖M + D + E‖ ≤ ‖M + D‖ + ‖E‖ := norm_add_le _ _
      _ ≤ ‖M‖ + ‖D‖ + ‖E‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖M‖ + εD * Real.sqrt N + εE * Real.sqrt N := by gcongr
      _ = ‖M‖ + η * Real.sqrt N := by rw [hη]; ring
  rw [Assembly.frobSq_eq_norm_sq, Assembly.frobSq_eq_norm_sq]
  have hG2 : ‖G‖ ^ 2 ≤ (‖M‖ + η * Real.sqrt N) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hG 2
  have amgm : 2 * ‖M‖ * Real.sqrt N ≤ ‖M‖ ^ 2 + N := by
    nlinarith [sq_nonneg (‖M‖ - Real.sqrt N)]
  nlinarith [mul_nonneg hη0 (sub_nonneg.2 amgm), mul_nonneg hη0 hm0]

end Frob2

end Transfer
end XiPrime
end Zeta23
