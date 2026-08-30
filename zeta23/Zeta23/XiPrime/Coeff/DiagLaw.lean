/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Coeff/DiagLaw.lean — (H3), the diagonal law  [XF′ Lemma 7.1].

  ∀ ε > 0 ∃ T₀ ∀ T ≥ T₀ ∀ y ∈ [0, l(T)]:  | Σ_{N≤e^y} ‖C(N;Λ⋆(T))‖²/N − l(T)²·∫₀^{y/l} D₁ | ≤ ε·l(T)²
for any T-indexed parameter with Re Λ⋆(T) = l(T)/2 and |Im Λ⋆(T)| ≤ 1 (covers L_T = l/2 + iπ/4 and the real l/2).
Assembly (K-truncation): S = Σ_{k≤K} S_sf,k + R with
  S_sf,k  from Coeff/MainTerm (squarefree evaluation + k-fold Mertens induction),
  0 ≤ R ≤ non-squarefree part (Coeff/NonSquarefree, O_K(l)) + k-tail (Coeff/Upper + Coeff/Tail, ≤ ε·l²),
  ∫ D₁ = ∫ D1trunc K + tail (Certificate/D1).
-/
import Zeta23.XiPrime.Coeff.Upper
import Zeta23.XiPrime.Coeff.MainTerm.Squarefree
import Zeta23.XiPrime.Coeff.MainTerm.Asymp
import Zeta23.XiPrime.Coeff.NonSquarefree
import Zeta23.XiPrime.Coeff.PrimeSums
import Zeta23.XiPrime.Coeff.Param
import Zeta23.XiPrime.Coeff.Tail

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Omega ArithmeticFunction.omega
open Finset Real

noncomputable section

namespace Zeta23
namespace XiPrime

/-! ### the partition of the diagonal sum -/

/-- the ω = k squarefree layer:  Σ_{N ≤ e^y, N squarefree, ω(N) = k} ‖C(N;Λ⋆)‖²/N. -/
def sfPart (Λs : ℂ) (k : ℕ) (y : ℝ) : ℝ :=
  ∑ N ∈ (Ioc 0 ⌊Real.exp y⌋₊).filter (fun N => Squarefree N ∧ ω N = k), ‖xiCoeff Λs N‖ ^ 2 / N

/-- the remainder layer:  N not squarefree, or ω(N) > K. -/
def bPart (Λs : ℂ) (K : ℕ) (y : ℝ) : ℝ :=
  ∑ N ∈ (Ioc 0 ⌊Real.exp y⌋₊).filter (fun N => ¬ (Squarefree N ∧ ω N ≤ K)), ‖xiCoeff Λs N‖ ^ 2 / N

lemma sfPart_nonneg (Λs : ℂ) (k : ℕ) (y : ℝ) : 0 ≤ sfPart Λs k y :=
  sum_nonneg fun N _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg N)

lemma bPart_nonneg (Λs : ℂ) (K : ℕ) (y : ℝ) : 0 ≤ bPart Λs K y :=
  sum_nonneg fun N _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg N)

/-- S(y) = Σ_{k ≤ K} sfPart k + bPart K. -/
lemma diag_split (Λs : ℂ) (K : ℕ) (y : ℝ) :
    ∑ N ∈ Ioc 0 ⌊Real.exp y⌋₊, ‖xiCoeff Λs N‖ ^ 2 / N
      = (∑ k ∈ range (K + 1), sfPart Λs k y) + bPart Λs K y := by
  rw [← sum_filter_add_sum_filter_not (Ioc 0 ⌊Real.exp y⌋₊) (fun N => Squarefree N ∧ ω N ≤ K)]
  congr 1
  unfold sfPart
  rw [← sum_fiberwise_of_maps_to (g := fun N => ω N) (t := range (K + 1))
    (fun N hN => mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hN).2.2))]
  refine sum_congr rfl fun k hk => ?_
  have hkK : k ≤ K := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [filter_filter]
  congr 1
  ext N
  simp only [mem_filter]
  constructor
  · rintro ⟨hN, ⟨hsf, _⟩, hk⟩; exact ⟨hN, hsf, hk⟩
  · rintro ⟨hN, hsf, hk⟩; exact ⟨hN, ⟨hsf, hk ▸ hkK⟩, hk⟩

/-- the k = 0 layer is empty of mass: N squarefree with ω N = 0 means N = 1, and C(1) = 0. -/
lemma sfPart_zero (Λs : ℂ) (y : ℝ) : sfPart Λs 0 y = 0 := by
  unfold sfPart
  refine sum_eq_zero fun N hN => ?_
  obtain ⟨-, hsf, h0⟩ := mem_filter.mp hN
  have hN1 : N ≤ 1 := ArithmeticFunction.cardDistinctFactors_eq_zero.mp h0
  have hN0 : N ≠ 0 := Squarefree.ne_zero hsf
  have : N = 1 := by omega
  subst this
  simp

/-! ### the remainder layer is small:  bPart ≤ C_K·(1+l) + (tail)·l² -/

/-- N in the remainder layer with Λ^{∗m}(N) ≠ 0 for some m ≤ K is not squarefree. -/
lemma not_squarefree_of_bLayer {N K m : ℕ} (hm : m ≤ K)
    (hB : ¬ (Squarefree N ∧ ω N ≤ K)) (hne : (Λ ^ m) N ≠ 0) : ¬ Squarefree N := by
  intro hsf
  have h := lamPow_apply_squarefree hsf m
  rw [h] at hne
  split_ifs at hne with hω
  · exact hB ⟨hsf, hω ▸ hm⟩
  · exact hne rfl

/-- N in the remainder layer (K ≥ 1) with Λ(N) ≠ 0 is not squarefree. -/
lemma not_squarefree_of_bLayer_lam {N K : ℕ} (hK : 1 ≤ K)
    (hB : ¬ (Squarefree N ∧ ω N ≤ K)) (hne : Λ N ≠ 0) : ¬ Squarefree N :=
  not_squarefree_of_bLayer hK hB (by rwa [pow_one])

/-- **the remainder bound.**  For K ≥ 1 there are constants C_i such that for x := ‖Λ⋆‖⁻¹ with x·y ≤ 4, 32eK·x ≤ 1,
  we have the bound used downstream:
  bPart ≤ 2Cdef + 2y²·(TAIL_K(x,y,X) + Σ_{i<K} 2^{i+1}x^{2(i+1)}y^{i+1}·C_i(1+y)^i). -/
theorem bPart_le (K : ℕ) (hK : 1 ≤ K) :
    ∃ Cn : ℕ → ℝ, (∀ i, 0 ≤ Cn i) ∧ ∀ (Λs : ℂ) (y : ℝ), 0 ≤ y → ‖Λs‖⁻¹ * y ≤ 4 →
      32 * Real.exp 1 * KM ≤ ‖Λs‖ →
      bPart Λs K y ≤ 2 * Cdef + 2 * y ^ 2 *
        ((∑ i ∈ (range ⌊Real.exp y⌋₊).filter (fun i => K ≤ i),
            2 ^ (i + 1) * ‖Λs‖⁻¹ ^ (2 * (i + 1)) * y ^ (i + 1) * Sdiv (Λ ^ (i + 1)) y)
         + ∑ i ∈ range K, 2 ^ (i + 1) * ‖Λs‖⁻¹ ^ (2 * (i + 1)) * y ^ (i + 1) * (Cn i * (1 + y) ^ i)) := by
  choose Cn hCn0 hCn using fun i : ℕ => Nsf_le_poly (i + 1) (Nat.succ_le_succ (Nat.zero_le i))
  refine ⟨Cn, hCn0, fun Λs y hy hxy hbig => ?_⟩
  set X : ℕ := ⌊Real.exp y⌋₊ with hX
  set x : ℝ := ‖Λs‖⁻¹ with hxdef
  have hΛpos : 0 < ‖Λs‖ := lt_of_lt_of_le (mul_pos (by positivity) KM_pos) hbig
  have hx : 0 ≤ x := by positivity
  set B := (Ioc 0 X).filter (fun N => ¬ (Squarefree N ∧ ω N ≤ K)) with hBdef
  have hBsub : B ⊆ Ioc 0 X := filter_subset _ _
  -- (1) ‖C‖² ≤ 2Λ² + 2log²N F², and log N ≤ y on the range
  have hstep1 : bPart Λs K y ≤ 2 * (∑ N ∈ B, Λ N ^ 2 / N) + 2 * y ^ 2 * ∑ N ∈ B, Fmaj x N ^ 2 / N := by
    have hb : bPart Λs K y = ∑ N ∈ B, ‖xiCoeff Λs N‖ ^ 2 / N := by unfold bPart; rw [← hX, ← hBdef]
    rw [hb]
    calc ∑ N ∈ B, ‖xiCoeff Λs N‖ ^ 2 / N
        ≤ ∑ N ∈ B, (2 * (Λ N ^ 2 / N) + 2 * (y ^ 2 * (Fmaj x N ^ 2 / N))) := sum_le_sum fun N hN => ?_
      _ = 2 * (∑ N ∈ B, Λ N ^ 2 / N) + 2 * (y ^ 2 * ∑ N ∈ B, Fmaj x N ^ 2 / N) := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
      _ = _ := by ring
    have hN' := hBsub hN
    have hlogN : Real.log N ≤ y := log_le_of_mem_Ioc_floor_exp hN'
    have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have hN0 : (0:ℝ) ≤ (N:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg N)
    have h := norm_xiCoeff_sq_le Λs N
    have hlog2 : Real.log N ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hlog0 hlogN 2
    calc ‖xiCoeff Λs N‖ ^ 2 / N = ‖xiCoeff Λs N‖ ^ 2 * (N:ℝ)⁻¹ := div_eq_mul_inv _ _
      _ ≤ (2 * Λ N ^ 2 + 2 * Real.log N ^ 2 * Fmaj x N ^ 2) * (N:ℝ)⁻¹ := mul_le_mul_of_nonneg_right h hN0
      _ ≤ (2 * Λ N ^ 2 + 2 * y ^ 2 * Fmaj x N ^ 2) * (N:ℝ)⁻¹ := by gcongr
      _ = 2 * (Λ N ^ 2 / N) + 2 * (y ^ 2 * (Fmaj x N ^ 2 / N)) := by ring
  -- (2) the Λ² part: supported on non-squarefree N
  have hΛ2 : ∑ N ∈ B, Λ N ^ 2 / N ≤ Cdef := by
    calc ∑ N ∈ B, Λ N ^ 2 / N = ∑ N ∈ B.filter (fun N => Λ N ≠ 0), Λ N ^ 2 / N := by
          refine (sum_filter_of_ne fun N _ h => ?_).symm
          intro h0; apply h; rw [h0]; simp
      _ ≤ ∑ N ∈ (Ioc 0 X).filter (fun N => ¬ Squarefree N), Λ N ^ 2 / N := by
          refine sum_le_sum_of_subset_of_nonneg ?_ fun N _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg N)
          intro N hN
          obtain ⟨hNB, hne⟩ := mem_filter.mp hN
          obtain ⟨hNI, hB⟩ := mem_filter.mp hNB
          exact mem_filter.mpr ⟨hNI, not_squarefree_of_bLayer_lam hK hB hne⟩
      _ ≤ Cdef := sum_not_squarefree_vonMangoldt_sq_div_le X
  -- (3) the F² part: dyadic Cauchy–Schwarz, swap, split at K
  have hF : ∑ N ∈ B, Fmaj x N ^ 2 / N
      ≤ (∑ i ∈ (range X).filter (fun i => K ≤ i), 2 ^ (i + 1) * x ^ (2 * (i + 1)) * y ^ (i + 1) * Sdiv (Λ ^ (i + 1)) y)
        + ∑ i ∈ range K, 2 ^ (i + 1) * x ^ (2 * (i + 1)) * y ^ (i + 1) * (Cn i * (1 + y) ^ i) := by
    -- pointwise
    have hpt : ∀ N ∈ B, Fmaj x N ^ 2 / N
        ≤ ∑ i ∈ range X, 2 ^ (i + 1) * x ^ (2 * (i + 1)) * y ^ (i + 1) * ((Λ ^ (i + 1)) N / N) := by
      intro N hN
      have hN' := hBsub hN
      have hNX : N ≤ X := (mem_Ioc.mp hN').2
      have hΩ : Ω N ≤ X := (cardFactors_le_self N).trans hNX
      have hlogN : Real.log N ≤ y := log_le_of_mem_Ioc_floor_exp hN'
      have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
      rw [Fmaj_eq_sum_range_of_le x hΩ, div_eq_mul_inv]
      calc (∑ i ∈ range X, x ^ (i + 1) * (Λ ^ (i + 1)) N) ^ 2 * (N:ℝ)⁻¹
          ≤ (∑ i ∈ range X, 2 ^ (i + 1) * (x ^ (i + 1) * (Λ ^ (i + 1)) N) ^ 2) * (N:ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right (sq_sum_range_le_sum_two_pow_mul_sq X _) (by positivity)
        _ = ∑ i ∈ range X, 2 ^ (i + 1) * x ^ (2 * (i + 1)) * ((Λ ^ (i + 1)) N * (Λ ^ (i + 1)) N) * (N:ℝ)⁻¹ := by
            rw [sum_mul]; refine sum_congr rfl fun i _ => by ring
        _ ≤ ∑ i ∈ range X, 2 ^ (i + 1) * x ^ (2 * (i + 1)) * (y ^ (i + 1) * (Λ ^ (i + 1)) N) * (N:ℝ)⁻¹ := by
            refine sum_le_sum fun i _ => ?_
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine mul_le_mul_of_nonneg_right ?_ (lamPow_nonneg _ _)
            exact (lamPow_le_log_pow _ _).trans (pow_le_pow_left₀ hlog0 hlogN _)
        _ = _ := sum_congr rfl fun i _ => by ring
    -- swap and split
    have hswap : ∑ N ∈ B, ∑ i ∈ range X, 2 ^ (i + 1) * x ^ (2 * (i + 1)) * y ^ (i + 1) * ((Λ ^ (i + 1)) N / N)
        = ∑ i ∈ range X, 2 ^ (i + 1) * x ^ (2 * (i + 1)) * y ^ (i + 1) * ∑ N ∈ B, (Λ ^ (i + 1)) N / N := by
      rw [sum_comm]
      exact sum_congr rfl fun i _ => by rw [← mul_sum]
    have hcoef : ∀ i, 0 ≤ 2 ^ (i + 1) * x ^ (2 * (i + 1)) * y ^ (i + 1) := fun i => by positivity
    -- inner sums: ≤ Sdiv always; ≤ Nsf (i+1) y when i+1 ≤ K
    have hinner_all : ∀ i, ∑ N ∈ B, (Λ ^ (i + 1)) N / N ≤ Sdiv (Λ ^ (i + 1)) y := fun i =>
      sum_le_sum_of_subset_of_nonneg hBsub fun N _ _ => div_nonneg (lamPow_nonneg _ _) (Nat.cast_nonneg N)
    have hinner_nsf : ∀ i, i < K → ∑ N ∈ B, (Λ ^ (i + 1)) N / N ≤ Cn i * (1 + y) ^ i := by
      intro i hi
      have h1 : ∑ N ∈ B, (Λ ^ (i + 1)) N / N ≤ Nsf (i + 1) y := by
        calc ∑ N ∈ B, (Λ ^ (i + 1)) N / N = ∑ N ∈ B.filter (fun N => (Λ ^ (i + 1)) N ≠ 0), (Λ ^ (i + 1)) N / N := by
              refine (sum_filter_of_ne fun N _ h => ?_).symm
              intro h0; apply h; rw [h0, zero_div]
          _ ≤ Nsf (i + 1) y := by
              unfold Nsf SdivP
              refine sum_le_sum_of_subset_of_nonneg ?_ fun N _ _ => div_nonneg (lamPow_nonneg _ _) (Nat.cast_nonneg N)
              intro N hN
              obtain ⟨hNB, hne⟩ := mem_filter.mp hN
              obtain ⟨hNI, hB⟩ := mem_filter.mp hNB
              exact mem_filter.mpr ⟨hNI, not_squarefree_of_bLayer (by omega) hB hne⟩
      have h2 := hCn i y hy
      simp only [Nat.add_sub_cancel] at h2
      exact h1.trans h2
    calc ∑ N ∈ B, Fmaj x N ^ 2 / N
        ≤ ∑ N ∈ B, ∑ i ∈ range X, 2 ^ (i + 1) * x ^ (2 * (i + 1)) * y ^ (i + 1) * ((Λ ^ (i + 1)) N / N) := sum_le_sum hpt
      _ = ∑ i ∈ range X, 2 ^ (i + 1) * x ^ (2 * (i + 1)) * y ^ (i + 1) * ∑ N ∈ B, (Λ ^ (i + 1)) N / N := hswap
      _ = (∑ i ∈ (range X).filter (fun i => K ≤ i), 2 ^ (i + 1) * x ^ (2 * (i + 1)) * y ^ (i + 1) * ∑ N ∈ B, (Λ ^ (i + 1)) N / N)
          + ∑ i ∈ (range X).filter (fun i => ¬ K ≤ i), 2 ^ (i + 1) * x ^ (2 * (i + 1)) * y ^ (i + 1) * ∑ N ∈ B, (Λ ^ (i + 1)) N / N :=
          (sum_filter_add_sum_filter_not _ _ _).symm
      _ ≤ (∑ i ∈ (range X).filter (fun i => K ≤ i), 2 ^ (i + 1) * x ^ (2 * (i + 1)) * y ^ (i + 1) * Sdiv (Λ ^ (i + 1)) y)
          + ∑ i ∈ (range X).filter (fun i => ¬ K ≤ i), 2 ^ (i + 1) * x ^ (2 * (i + 1)) * y ^ (i + 1) * (Cn i * (1 + y) ^ i) := by
          refine add_le_add (sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hinner_all i) (hcoef i))
            (sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hinner_nsf i ?_) (hcoef i))
          exact not_le.mp (mem_filter.mp hi).2
      _ ≤ (∑ i ∈ (range X).filter (fun i => K ≤ i), 2 ^ (i + 1) * x ^ (2 * (i + 1)) * y ^ (i + 1) * Sdiv (Λ ^ (i + 1)) y)
          + ∑ i ∈ range K, 2 ^ (i + 1) * x ^ (2 * (i + 1)) * y ^ (i + 1) * (Cn i * (1 + y) ^ i) := by
          refine add_le_add le_rfl (sum_le_sum_of_subset_of_nonneg ?_ ?_)
          · intro i hi
            obtain ⟨-, hi2⟩ := mem_filter.mp hi
            exact mem_range.mpr (not_le.mp hi2)
          · intro i _ _
            exact mul_nonneg (hcoef i) (mul_nonneg (hCn0 i) (pow_nonneg (by linarith) i))
  -- (4) combine
  have h2y : 0 ≤ 2 * y ^ 2 := by positivity
  calc bPart Λs K y ≤ 2 * (∑ N ∈ B, Λ N ^ 2 / N) + 2 * y ^ 2 * ∑ N ∈ B, Fmaj x N ^ 2 / N := hstep1
    _ ≤ 2 * Cdef + 2 * y ^ 2 * _ := add_le_add (by linarith) (mul_le_mul_of_nonneg_left hF h2y)

lemma abs_sub_le_of_three (a b c : ℝ) : |a + b - c| ≤ |a| + |b| + |c| := by
  calc |a + b - c| ≤ |a + b| + |c| := abs_sub _ _
    _ ≤ |a| + |b| + |c| := by linarith [abs_add_le a b]

/-! ### the squarefree layers ω = k ≥ 2:  sfPart k = l²·d_k·(y/l)^{2k+2} + O_k(1+l) -/

/-- d_k := 4^k (k−1)!/((k+1)(2k)!)  — the coefficient of s^{2k+2} in ∫₀ˢ D_{1,k}  (k ≥ 1; d₁ = 1). -/
def dcoef (k : ℕ) : ℝ := (4:ℝ) ^ k * ((k - 1).factorial : ℝ) / ((k + 1) * ((2 * k).factorial : ℝ))

/-- the scaling identity  (4/l²)^n · y^{2n+2} = l² · 4^n · (y/l)^{2n+2}. -/
lemma pow_scaling_identity (l y : ℝ) (hl : l ≠ 0) (n : ℕ) :
    (4 / l ^ 2) ^ n * y ^ (2 * n + 2) = l ^ 2 * (4 ^ n * (y / l) ^ (2 * n + 2)) := by
  rw [div_pow, div_pow, show l ^ (2 * n + 2) = (l ^ 2) ^ n * l ^ 2 by rw [← pow_mul, ← pow_add]]
  have h1 : (l ^ 2) ^ n ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hl)
  have h2 : l ^ 2 ≠ 0 := pow_ne_zero _ hl
  field_simp

/-- squarefree N with ω N = 1 is prime, and conversely. -/
lemma squarefree_and_omega_one_iff {N : ℕ} : (Squarefree N ∧ ω N = 1) ↔ N.Prime := by
  constructor
  · rintro ⟨hsf, h1⟩
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp
      (ArithmeticFunction.cardDistinctFactors_eq_one_iff.mp h1)
    have hk1 : k = 1 := by
      by_contra hne
      have hk2 : 2 ≤ k := by omega
      have : p * p ∣ p ^ k := ⟨p ^ (k - 2), by rw [← pow_two, ← pow_add]; congr 1; omega⟩
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsf p this))
    subst hk1; simpa using hp
  · intro hp
    exact ⟨hp.prime.squarefree, ArithmeticFunction.cardDistinctFactors_apply_prime hp⟩

/-- the non-(sf ∧ ω = k) part of Σ (Λlog)^{∗k}(N) log²N/N is ≤ y^{k+2}·Nsf k y. -/
lemma lamLogPow_offlayer_le (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    ∑ N ∈ (Ioc 0 ⌊Real.exp y⌋₊).filter (fun N => ¬ (Squarefree N ∧ ω N = k)),
        (lamLog ^ k) N * Real.log N ^ 2 / N
      ≤ y ^ (k + 2) * Nsf k y := by
  set X := ⌊Real.exp y⌋₊ with hX
  have hpt : ∀ N ∈ (Ioc 0 X).filter (fun N => ¬ (Squarefree N ∧ ω N = k)),
      (lamLog ^ k) N * Real.log N ^ 2 / N
        ≤ y ^ (k + 2) * (if ¬ Squarefree N then (Λ ^ k) N / N else 0) := by
    intro N hN
    obtain ⟨hNI, hB⟩ := mem_filter.mp hN
    have hlogN : Real.log N ≤ y := log_le_of_mem_Ioc_floor_exp hNI
    have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    by_cases hsf : Squarefree N
    · -- then (lamLog^k) N = 0 (else ω N = k)
      have h0 : (lamLog ^ k) N = 0 := by
        rw [lamLogPow_apply_squarefree hsf k]
        split_ifs with hω
        · exact absurd ⟨hsf, hω⟩ hB
        · rfl
      rw [h0, if_neg (not_not_intro hsf)]; simp
    · rw [if_pos hsf]
      calc (lamLog ^ k) N * Real.log N ^ 2 / N
          ≤ (Real.log N ^ k * (Λ ^ k) N) * Real.log N ^ 2 / N :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (lamLogPow_le k N) (sq_nonneg _))
              (Nat.cast_nonneg N)
        _ = Real.log N ^ (k + 2) * ((Λ ^ k) N / N) := by ring
        _ ≤ y ^ (k + 2) * ((Λ ^ k) N / N) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlog0 hlogN _)
              (div_nonneg (lamPow_nonneg _ _) (Nat.cast_nonneg N))
  calc _ ≤ ∑ N ∈ (Ioc 0 X).filter (fun N => ¬ (Squarefree N ∧ ω N = k)),
          y ^ (k + 2) * (if ¬ Squarefree N then (Λ ^ k) N / N else 0) := sum_le_sum hpt
    _ ≤ ∑ N ∈ Ioc 0 X, y ^ (k + 2) * (if ¬ Squarefree N then (Λ ^ k) N / N else 0) := by
        refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun N _ _ => ?_
        refine mul_nonneg (pow_nonneg hy _) ?_
        split_ifs
        · exact le_rfl
        · exact div_nonneg (lamPow_nonneg _ _) (Nat.cast_nonneg N)
    _ = y ^ (k + 2) * Nsf k y := by
        rw [← mul_sum]; congr 1
        unfold Nsf SdivP
        rw [sum_filter]

/-- **the layer ω = k ≥ 2.**  With a := (‖Λ⋆‖²)⁻¹ (so a ≤ 4/l² and |a^k − (4/l²)^k| ≤ k(4/l²)^{k+1} by Coeff/Param):
  |sfPart Λ⋆ k y − l²·d_k·(y/l)^{2k+2}| ≤ C_k·(1+l)  for 0 ≤ y ≤ l, l ≥ 2. -/
theorem sfPart_asymp (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, ∀ (l : ℝ), 2 ≤ l → ∀ (Λs : ℂ), Λs.re = l / 2 → |Λs.im| ≤ 1 →
      ∀ y : ℝ, 0 ≤ y → y ≤ l →
        |sfPart Λs k y - l ^ 2 * (dcoef k * (y / l) ^ (2 * k + 2))| ≤ C * (1 + l) := by
  obtain ⟨CW, hW⟩ := Wk_asymp k (by omega)
  obtain ⟨CN, hCN0, hCN⟩ := Nsf_le_poly k (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hj1 : j + 2 - 1 = j + 1 := by omega
  set r : ℝ := (((j + 1).factorial : ℝ) ^ 2) / ((j + 2).factorial : ℝ) with hr
  set mk : ℝ := ((j + 2 : ℕ) : ℝ) / ((((j + 2 : ℕ) : ℝ) + 1) * ((2 * (j + 2)).factorial : ℝ)) with hmk
  have hr0 : 0 ≤ r := by positivity
  have hmk0 : 0 ≤ mk := by positivity
  -- the constant
  refine ⟨(16:ℝ) ^ (j + 2) * r * |CW| + (j + 2) * 4 ^ (j + 3) * r * mk
      + 4 ^ (j + 2) * 2 ^ (j + 1) * r * CN + 1, ?_⟩
  intro l hl Λs hre him y hy hyl
  have hl0 : 0 < l := by linarith
  have hlne : l ≠ 0 := hl0.ne'
  have hl1 : 1 ≤ l := by linarith
  have hΛ0 : Λs ≠ 0 := by
    intro h; rw [h] at hre; simp at hre; linarith
  have hpow := pow_scaling_identity l y hlne (j + 2)
  set a : ℝ := (‖Λs‖ ^ 2)⁻¹ with ha
  set b : ℝ := 4 / l ^ 2 with hb
  have hbl : b * l ^ 2 = 4 := by rw [hb]; field_simp
  have ha0 : 0 ≤ a := by positivity
  have ha4 : a ≤ b := inv_normSq_param_le hl hre him
  have hak : |a ^ (j + 2) - b ^ (j + 2)| ≤ (j + 2 : ℕ) * b ^ (j + 2 + 1) :=
    inv_normSq_pow_param hl hre him (j + 2)
  have h4l : 0 ≤ b := by positivity
  set X := ⌊Real.exp y⌋₊ with hX
  set g : ℕ → ℝ := fun N => (lamLog ^ (j + 2)) N * Real.log N ^ 2 / N with hg
  have hg0 : ∀ N, 0 ≤ g N := fun N => div_nonneg (mul_nonneg (lamLogPow_nonneg _ _) (sq_nonneg _)) (Nat.cast_nonneg N)
  -- step 1: sfPart = a^k r Σ_{layer} g
  have hstep1 : sfPart Λs (j + 2) y
      = a ^ (j + 2) * r * ∑ N ∈ (Ioc 0 X).filter (fun N => Squarefree N ∧ ω N = j + 2), g N := by
    unfold sfPart
    rw [← hX, mul_sum]
    refine sum_congr rfl fun N hN => ?_
    obtain ⟨-, hsf, hω⟩ := mem_filter.mp hN
    rw [norm_sq_xiCoeff_squarefree hsf (by omega) Λs hΛ0, hω, hj1]
    simp only [hg, hr, ha]
    ring
  -- step 2: layer sum = all − off-layer
  have hsplit : ∑ N ∈ (Ioc 0 X).filter (fun N => Squarefree N ∧ ω N = j + 2), g N
      = (∑ N ∈ Ioc 0 X, g N) - ∑ N ∈ (Ioc 0 X).filter (fun N => ¬ (Squarefree N ∧ ω N = j + 2)), g N := by
    rw [eq_sub_iff_add_eq]; exact sum_filter_add_sum_filter_not _ _ _
  set Wv := ∑ N ∈ Ioc 0 X, g N with hWv
  set E := ∑ N ∈ (Ioc 0 X).filter (fun N => ¬ (Squarefree N ∧ ω N = j + 2)), g N with hE
  have hE0 : 0 ≤ E := sum_nonneg fun N _ => hg0 N
  have hEle : E ≤ y ^ (j + 2 + 2) * (CN * (1 + y) ^ (j + 1)) := by
    have h1 := lamLogPow_offlayer_le (j + 2) hy
    rw [← hX] at h1
    have h2 := hCN y hy
    rw [hj1] at h2
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (pow_nonneg hy _))
  have hWmain : |Wv - mk * y ^ (2 * (j + 2) + 2)| ≤ CW * (1 + y) ^ (2 * (j + 2) + 1) := by
    have := hW y hy
    rw [Wk_def, ← hX] at this
    exact this
  -- step 3: the identities  r·mk·4^k = d_k  and  b^k y^{2k+2} = l²·4^k·(y/l)^{2k+2}
  have hcoef : r * mk * 4 ^ (j + 2) = dcoef (j + 2) := by
    simp only [hr, hmk, dcoef]
    rw [hj1]
    have hfac : ((j + 2).factorial : ℝ) = ((j:ℝ) + 2) * ((j + 1).factorial : ℝ) := by
      rw [Nat.factorial_succ (j + 1)]; push_cast; ring
    rw [hfac]
    have hf0 : ((j + 1).factorial : ℝ) ≠ 0 := by positivity
    have hf1 : ((2 * (j + 2)).factorial : ℝ) ≠ 0 := by positivity
    have hj2 : (j:ℝ) + 2 ≠ 0 := by positivity
    have hj3 : (j:ℝ) + 2 + 1 ≠ 0 := by positivity
    push_cast
    field_simp
  have hmain_id : b ^ (j + 2) * r * (mk * y ^ (2 * (j + 2) + 2))
      = l ^ 2 * (dcoef (j + 2) * (y / l) ^ (2 * (j + 2) + 2)) := by
    rw [← hcoef]
    calc b ^ (j + 2) * r * (mk * y ^ (2 * (j + 2) + 2))
        = r * mk * (b ^ (j + 2) * y ^ (2 * (j + 2) + 2)) := by ring
      _ = r * mk * (l ^ 2 * (4 ^ (j + 2) * (y / l) ^ (2 * (j + 2) + 2))) := by rw [hpow]
      _ = _ := by ring
  -- step 4: decomposition of the difference
  have hdecomp : sfPart Λs (j + 2) y - l ^ 2 * (dcoef (j + 2) * (y / l) ^ (2 * (j + 2) + 2))
      = a ^ (j + 2) * r * (Wv - mk * y ^ (2 * (j + 2) + 2))
        + (a ^ (j + 2) - b ^ (j + 2)) * r * (mk * y ^ (2 * (j + 2) + 2))
        - a ^ (j + 2) * r * E := by
    rw [hstep1, hsplit, ← hmain_id]; ring
  rw [hdecomp]
  -- step 5: bound the three terms
  have hy1 : 1 + y ≤ 2 * l := by linarith
  have hy1' : 0 ≤ 1 + y := by linarith
  have hT1 : |a ^ (j + 2) * r * (Wv - mk * y ^ (2 * (j + 2) + 2))| ≤ (16:ℝ) ^ (j + 2) * r * |CW| * (1 + l) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ha0 _), abs_of_nonneg hr0]
    have h16 : b ^ (j + 2) * (2 * l) ^ (2 * (j + 2)) = (16:ℝ) ^ (j + 2) := by
      rw [pow_mul, ← mul_pow]
      congr 1
      calc b * (2 * l) ^ 2 = 4 * (b * l ^ 2) := by ring
        _ = 16 := by rw [hbl]; norm_num
    calc a ^ (j + 2) * r * |Wv - mk * y ^ (2 * (j + 2) + 2)|
        ≤ b ^ (j + 2) * r * (CW * (1 + y) ^ (2 * (j + 2) + 1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha0 ha4 _) hr0) hWmain (abs_nonneg _)
            (mul_nonneg (pow_nonneg h4l _) hr0)
      _ ≤ b ^ (j + 2) * r * (|CW| * ((2 * l) ^ (2 * (j + 2)) * (1 + l))) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (pow_nonneg h4l _) hr0)
          rw [pow_succ]
          exact mul_le_mul (le_abs_self CW) (mul_le_mul (pow_le_pow_left₀ hy1' hy1 _) (by linarith) hy1'
            (pow_nonneg (by linarith) _)) (mul_nonneg (pow_nonneg hy1' _) hy1') (abs_nonneg _)
      _ = (b ^ (j + 2) * (2 * l) ^ (2 * (j + 2))) * r * |CW| * (1 + l) := by ring
      _ = (16:ℝ) ^ (j + 2) * r * |CW| * (1 + l) := by rw [h16]
  have hT2 : |(a ^ (j + 2) - b ^ (j + 2)) * r * (mk * y ^ (2 * (j + 2) + 2))|
      ≤ (j + 2) * 4 ^ (j + 3) * r * mk * (1 + l) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hr0, abs_of_nonneg (mul_nonneg hmk0 (pow_nonneg hy _))]
    have h4 : b ^ (j + 2 + 1) * l ^ (2 * (j + 2) + 2) = (4:ℝ) ^ (j + 3) := by
      rw [show 2 * (j + 2) + 2 = 2 * (j + 2 + 1) by ring, pow_mul, ← mul_pow, hbl]
    calc |a ^ (j + 2) - b ^ (j + 2)| * r * (mk * y ^ (2 * (j + 2) + 2))
        ≤ ((j + 2 : ℕ) * b ^ (j + 2 + 1)) * r * (mk * l ^ (2 * (j + 2) + 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hak hr0)
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hyl _) hmk0)
            (mul_nonneg hmk0 (pow_nonneg hy _))
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h4l _)) hr0)
      _ = (j + 2 : ℕ) * (b ^ (j + 2 + 1) * l ^ (2 * (j + 2) + 2)) * r * mk := by ring
      _ = (j + 2) * 4 ^ (j + 3) * r * mk := by rw [h4]; push_cast; ring
      _ ≤ (j + 2) * 4 ^ (j + 3) * r * mk * (1 + l) :=
          le_mul_of_one_le_right (by positivity) (by linarith)
  have hT3 : |a ^ (j + 2) * r * E| ≤ 4 ^ (j + 2) * 2 ^ (j + 1) * r * CN * (1 + l) := by
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha0 _) hr0) hE0)]
    have h42 : b ^ (j + 2) * (l ^ (j + 2 + 2) * (2 * l) ^ (j + 1)) = 4 ^ (j + 2) * 2 ^ (j + 1) * l := by
      have : l ^ (j + 2 + 2) * (2 * l) ^ (j + 1) = 2 ^ (j + 1) * ((l ^ 2) ^ (j + 2) * l) := by
        rw [mul_pow, ← pow_mul]; ring
      rw [this, show (4:ℝ) ^ (j + 2) = (b * l ^ 2) ^ (j + 2) by rw [hbl], mul_pow]
      ring
    calc a ^ (j + 2) * r * E
        ≤ b ^ (j + 2) * r * (y ^ (j + 2 + 2) * (CN * (1 + y) ^ (j + 1))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha0 ha4 _) hr0) hEle hE0
            (mul_nonneg (pow_nonneg h4l _) hr0)
      _ ≤ b ^ (j + 2) * r * (l ^ (j + 2 + 2) * (CN * (2 * l) ^ (j + 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (pow_nonneg h4l _) hr0)
          exact mul_le_mul (pow_le_pow_left₀ hy hyl _) (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hy1' hy1 _) hCN0) (mul_nonneg hCN0 (pow_nonneg hy1' _)) (pow_nonneg hl0.le _)
      _ = (b ^ (j + 2) * (l ^ (j + 2 + 2) * (2 * l) ^ (j + 1))) * r * CN := by ring
      _ = 4 ^ (j + 2) * 2 ^ (j + 1) * r * CN * l := by rw [h42]; ring
      _ ≤ 4 ^ (j + 2) * 2 ^ (j + 1) * r * CN * (1 + l) := by
          refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hsum3 := add_le_add (add_le_add hT1 hT2) hT3
  calc |a ^ (j + 2) * r * (Wv - mk * y ^ (2 * (j + 2) + 2))
        + (a ^ (j + 2) - b ^ (j + 2)) * r * (mk * y ^ (2 * (j + 2) + 2))
        - a ^ (j + 2) * r * E|
      ≤ |a ^ (j + 2) * r * (Wv - mk * y ^ (2 * (j + 2) + 2))|
        + |(a ^ (j + 2) - b ^ (j + 2)) * r * (mk * y ^ (2 * (j + 2) + 2))|
        + |a ^ (j + 2) * r * E| := abs_sub_le_of_three _ _ _
    _ ≤ (16:ℝ) ^ (j + 2) * r * |CW| * (1 + l) + (j + 2) * 4 ^ (j + 3) * r * mk * (1 + l)
        + 4 ^ (j + 2) * 2 ^ (j + 1) * r * CN * (1 + l) := hsum3
    _ = ((16:ℝ) ^ (j + 2) * r * |CW| + (j + 2) * 4 ^ (j + 3) * r * mk
        + 4 ^ (j + 2) * 2 ^ (j + 1) * r * CN) * (1 + l) := by ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right (by linarith) (by linarith)

end XiPrime
end Zeta23
