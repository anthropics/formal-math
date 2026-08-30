/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/PairCeiling/Signed.lean — the SIGNED-edge form of the ceiling: when the certificate has r(1) ≥ 0 and the law's edge
discrepancy D(1) ≥ 0 (an open-band law's free closed-band atom makes D(1) = Σ_j s_j − 1/2 positive), the edge term −r(1)·D(1) of the
signed second integration by parts (Stability.abel_ibp_second) is ≤ 0 and is DROPPED, rather than bounded by |r(1)|·|D(1)|:
      c₀ + ∫₀¹ r(x)·x dx ≤ p + |r′(1)|·|E(1)| + M·∫₀¹|r″|.
For near-CUE laws (NearCUE.lean) and the N = 256 law (LawN256.lean, with a kernel-checked certificate that D(1) ≥ 0) this yields
      v ≤ p + (1/(6N²) + τ/(2N))·(|r′(1)| + ∫₀¹|r″|),        N = 256:  v ≤ p + 2.5431316·10⁻⁶·(|r′(1)| + ∫₀¹|r″|).
-/
import Zeta23.PairCeiling.CeilingLaw256

open scoped BigOperators Interval
open MeasureTheory Set Finset

noncomputable section

namespace Zeta23
namespace PairCeiling

variable {s : ℕ → ℝ} {N : ℕ}

/-- **signed ceiling**: r(1) ≥ 0 and D(1) ≥ 0 kill the edge term. -/
theorem ceiling_signed (hN : 0 < N) {r g h : ℝ → ℝ} {T : Set ℝ} (hT : T.Countable) {M p₁ c₀ : ℝ}
    (hr : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt r (g x) x) (hg : ContinuousOn g (Icc (0:ℝ) 1))
    (hgh : ∀ x ∈ Ioo (0:ℝ) 1 \ T, HasDerivAt g (h x) x) (hh : IntervalIntegrable h volume 0 1)
    (hM : ∀ x ∈ Icc (0:ℝ) 1, |Efun s N x| ≤ M)
    (hr1 : 0 ≤ r 1) (hD1 : 0 ≤ Dfun s N 1)
    (hvalid : c₀ + ∑ j ∈ Finset.Icc 1 N, s j * r ((j:ℝ)/N) ≤ p₁) :
    c₀ + ∫ x in (0:ℝ)..1, r x * x ≤ p₁ + |g 1| * |Efun s N 1| + M * ∫ x in (0:ℝ)..1, |h x| := by
  have hid := abel_ibp_second (s := s) hN hT hr hg hgh hh
  have hE := continuousOn_Efun (s := s) hN
  have hhE : IntervalIntegrable (fun x => h x * Efun s N x) volume 0 1 :=
    hh.mul_continuousOn (by rwa [Set.uIcc_of_le zero_le_one])
  have h3 : |∫ x in (0:ℝ)..1, h x * Efun s N x| ≤ M * ∫ x in (0:ℝ)..1, |h x| := by
    calc |∫ x in (0:ℝ)..1, h x * Efun s N x|
        ≤ ∫ x in (0:ℝ)..1, |h x| * M := by
          refine intervalIntegral.abs_integral_le_integral_abs (by norm_num) |>.trans ?_
          refine intervalIntegral.integral_mono_on (by norm_num) hhE.abs (hh.abs.mul_const _) ?_
          intro x hx
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hM x hx) (abs_nonneg _)
      _ = M * ∫ x in (0:ℝ)..1, |h x| := by rw [intervalIntegral.integral_mul_const]; ring
  have hedge : 0 ≤ r 1 * Dfun s N 1 := mul_nonneg hr1 hD1
  have hgE : g 1 * Efun s N 1 ≤ |g 1| * |Efun s N 1| := by
    rw [← abs_mul]; exact le_abs_self _
  have hint : -(∫ x in (0:ℝ)..1, h x * Efun s N x) ≤ M * ∫ x in (0:ℝ)..1, |h x| := (neg_le_abs _).trans h3
  linarith

/-- **signed ceiling for a near-CUE law.** -/
theorem ceiling_nearCUE_signed (hN : 0 < N) (S : ℕ → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (hS : NearCUE S N τ)
    (hD1 : 0 ≤ Dfun (massOf S N) N 1)
    {r g h : ℝ → ℝ} {T : Set ℝ} (hT : T.Countable) {c₀ p : ℝ}
    (hr : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt r (g x) x) (hg : ContinuousOn g (Icc (0:ℝ) 1))
    (hgh : ∀ x ∈ Ioo (0:ℝ) 1 \ T, HasDerivAt g (h x) x) (hh : IntervalIntegrable h volume 0 1)
    (hr1 : 0 ≤ r 1)
    (hvalid : c₀ + ∑ j ∈ Finset.Icc 1 N, massOf S N j * r ((j:ℝ)/N) ≤ p) :
    c₀ + ∫ x in (0:ℝ)..1, r x * x
      ≤ p + (1 / (6 * (N : ℝ) ^ 2) + τ / (2 * N)) * |g 1| + (1 / (6 * (N : ℝ) ^ 2) + τ / (2 * N)) * ∫ x in (0:ℝ)..1, |h x| := by
  have hM := abs_Efun_le_of_nearCUE hN hτ hS
  have h0 := ceiling_signed hN hT hr hg hgh hh hM hr1 hD1 hvalid
  have hE1 := abs_Efun_one_le_of_nearCUE hN hτ hS
  have hb : 0 ≤ |g 1| := abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hE1 hb]

/-! ## the sign certificate D(1) ≥ 0 from the enclosures -/

/-- integer check: 2·Σlo ≥ K·N, i.e. T_N/N ≥ 1/2. -/
def edgeNonneg (d : RowCertData) : Bool := decide ((d.K : ℤ) * d.N ≤ 2 * sumLo d.encl) && decide (0 < d.K) && decide (0 < d.N)
  && decide (d.encl.length = d.N)

theorem D1_nonneg_of_edgeNonneg (d : RowCertData) (hc : edgeNonneg d = true) (S : ℕ → ℝ) (hS : EnclOK d.K S 0 d.encl) :
    0 ≤ Dfun (massOf S d.N) d.N 1 := by
  simp only [edgeNonneg, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hle, hK⟩, hN⟩, hlen⟩ := hc
  have hNr : (0 : ℝ) < d.N := by exact_mod_cast hN
  have hKr : (0 : ℝ) < d.K := by exact_mod_cast hK
  obtain ⟨hlo, _⟩ := sums_sound (S := S) d.encl 0 hS
  rw [hlen] at hlo
  have eT : ∑ i ∈ Finset.range d.N, S (0 + i + 1) = T S d.N := by simp [T]
  rw [eT] at hlo
  have hle' : (d.K : ℝ) * d.N ≤ 2 * (sumLo d.encl : ℝ) := by exact_mod_cast hle
  rw [Dfun_one hN, Csum_massOf, sub_nonneg, div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) hNr]
  nlinarith

/-- the N = 256 law's edge discrepancy is nonnegative (kernel evaluation). -/
theorem LawN256_edge : edgeNonneg LawN256 = true := by decide +kernel

/-- **SIGNED CEILING AT THE N = 256 LAW**: for certificates with r(1) ≥ 0 the edge term vanishes —
      c₀ + ∫₀¹ r(x)·x dx ≤ p + 2.5431316·10⁻⁶·|r′(1)| + 2.5431316·10⁻⁶·∫₀¹|r″|. -/
theorem ceiling_law256_signed (S : ℕ → ℝ) (hS : EnclOK LawN256.K S 0 LawN256.encl)
    {r g h : ℝ → ℝ} {T : Set ℝ} (hT : T.Countable) {c₀ p : ℝ}
    (hr : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt r (g x) x) (hg : ContinuousOn g (Icc (0:ℝ) 1))
    (hgh : ∀ x ∈ Ioo (0:ℝ) 1 \ T, HasDerivAt g (h x) x) (hh : IntervalIntegrable h volume 0 1)
    (hr1 : 0 ≤ r 1)
    (hvalid : c₀ + ∑ j ∈ Finset.Icc 1 256, massOf S 256 j * r ((j:ℝ)/256) ≤ p) :
    c₀ + ∫ x in (0:ℝ)..1, r x * x ≤ p + 2.5431316e-6 * |g 1| + 2.5431316e-6 * ∫ x in (0:ℝ)..1, |h x| := by
  obtain ⟨hrows, _⟩ := lawN256_rows S hS
  have hD1 : 0 ≤ Dfun (massOf S 256) 256 1 := by
    have h := D1_nonneg_of_edgeNonneg LawN256 LawN256_edge S hS
    have eN : LawN256.N = 256 := rfl
    simp only [eN] at h
    exact h
  have h0 := ceiling_nearCUE_signed (N := 256) (by norm_num) S (by positivity) hrows hD1 hT hr hg hgh hh hr1 hvalid
  have hc : (1 / (6 * (256 : ℝ) ^ 2) + ((3 : ℝ) / 10 ^ 40) / (2 * 256)) ≤ 2.5431316e-6 := by norm_num
  have hb : 0 ≤ |g 1| := abs_nonneg _
  have hI : 0 ≤ ∫ x in (0:ℝ)..1, |h x| := intervalIntegral.integral_nonneg zero_le_one fun x _ => abs_nonneg _
  push_cast at h0
  nlinarith [mul_le_mul_of_nonneg_right hc hb, mul_le_mul_of_nonneg_right hc hI]

end PairCeiling
end Zeta23

end
