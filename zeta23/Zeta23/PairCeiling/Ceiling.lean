/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/PairCeiling/Ceiling.lean — the CEILING THEOREM in certificate language:
if a pair (c₀, r) satisfies the certificate inequality at ONE configuration whose form-factor measure has masses s_j at j/N
and whose fraction of simple points is p₁ — i.e. c₀ + Σ_j s_j r(j/N) ≤ p₁ — then its VALUE v = c₀ + ∫₀¹ r(k)k dk obeys
      v ≤ p₁ + |r(1)|·|D(1)| + |r′(1)|·|E(1)| + (sup|E|)·∫₀¹|r″|,
and the parametrised corollary with numeric bounds.  (The configuration-specific numbers for an instance come from
NumericCert.lean + Bridge.lean, or from RowCert.lean + NearCUE.lean; the N = 256 law is assembled in CeilingLaw256.lean.)
-/
import Zeta23.PairCeiling.Stability

open scoped BigOperators Interval
open MeasureTheory Set intervalIntegral

noncomputable section

namespace Zeta23
namespace PairCeiling

variable {s : ℕ → ℝ} {N : ℕ}

/-- **CEILING (abstract form).** Validity of the certificate at the configuration (masses s at j/N, simple fraction p₁)
bounds the certificate's value by p₁ plus the stability error. -/
theorem ceiling_of_valid_at (hN : 0 < N) {r g h : ℝ → ℝ} {T : Set ℝ} (hT : T.Countable) {M p₁ c₀ : ℝ}
    (hr : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt r (g x) x) (hg : ContinuousOn g (Icc (0:ℝ) 1))
    (hgh : ∀ x ∈ Ioo (0:ℝ) 1 \ T, HasDerivAt g (h x) x) (hh : IntervalIntegrable h volume 0 1)
    (hM : ∀ x ∈ Icc (0:ℝ) 1, |Efun s N x| ≤ M)
    (hvalid : c₀ + ∑ j ∈ Finset.Icc 1 N, s j * r ((j:ℝ)/N) ≤ p₁) :
    c₀ + ∫ x in (0:ℝ)..1, r x * x
      ≤ p₁ + (|r 1| * |Dfun s N 1| + |g 1| * |Efun s N 1| + M * ∫ x in (0:ℝ)..1, |h x|) := by
  have hst := ceiling_stability hN hT hr hg hgh hh hM
  have : ∫ x in (0:ℝ)..1, r x * x ≤ ∑ j ∈ Finset.Icc 1 N, s j * r ((j:ℝ)/N)
      + (|r 1| * |Dfun s N 1| + |g 1| * |Efun s N 1| + M * ∫ x in (0:ℝ)..1, |h x|) := by
    have := neg_abs_le (∑ j ∈ Finset.Icc 1 N, s j * r ((j:ℝ)/N) - ∫ x in (0:ℝ)..1, r x * x)
    linarith
  linarith

/-- **CEILING (parametrised corollary).** With numeric bounds |D(1)| ≤ d₁, |E(1)| ≤ e₁, sup|E| ≤ M for the configuration
and |r(1)| ≤ a, |r′(1)| ≤ b, ∫₀¹|r″| ≤ c for the certificate:  v ≤ p₁ + d₁·a + e₁·b + M·c. -/
theorem ceiling_numeric (hN : 0 < N) {r g h : ℝ → ℝ} {T : Set ℝ} (hT : T.Countable)
    {M p₁ c₀ d₁ e₁ a b c : ℝ}
    (hr : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt r (g x) x) (hg : ContinuousOn g (Icc (0:ℝ) 1))
    (hgh : ∀ x ∈ Ioo (0:ℝ) 1 \ T, HasDerivAt g (h x) x) (hh : IntervalIntegrable h volume 0 1)
    (hM : ∀ x ∈ Icc (0:ℝ) 1, |Efun s N x| ≤ M)
    (hD1 : |Dfun s N 1| ≤ d₁) (hE1 : |Efun s N 1| ≤ e₁)
    (ha : |r 1| ≤ a) (hb : |g 1| ≤ b) (hc : ∫ x in (0:ℝ)..1, |h x| ≤ c)
    (hvalid : c₀ + ∑ j ∈ Finset.Icc 1 N, s j * r ((j:ℝ)/N) ≤ p₁) :
    c₀ + ∫ x in (0:ℝ)..1, r x * x ≤ p₁ + d₁ * a + e₁ * b + M * c := by
  have h0 := ceiling_of_valid_at hN hT hr hg hgh hh hM hvalid
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 ⟨le_rfl, zero_le_one⟩)
  have hint0 : 0 ≤ ∫ x in (0:ℝ)..1, |h x| :=
    intervalIntegral.integral_nonneg zero_le_one fun x _ => abs_nonneg _
  have h1 : |r 1| * |Dfun s N 1| ≤ d₁ * a := by
    calc |r 1| * |Dfun s N 1| ≤ a * d₁ := mul_le_mul ha hD1 (abs_nonneg _) ((abs_nonneg _).trans ha)
      _ = d₁ * a := mul_comm _ _
  have h2 : |g 1| * |Efun s N 1| ≤ e₁ * b := by
    calc |g 1| * |Efun s N 1| ≤ b * e₁ := mul_le_mul hb hE1 (abs_nonneg _) ((abs_nonneg _).trans hb)
      _ = e₁ * b := mul_comm _ _
  have h3 : M * ∫ x in (0:ℝ)..1, |h x| ≤ M * c := mul_le_mul_of_nonneg_left hc hM0
  linarith

end PairCeiling
end Zeta23

end
