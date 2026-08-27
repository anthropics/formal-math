/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/PairCeiling/CeilingLaw256.lean — THEOREM 1′ instantiated at the N = 256 law of LawN256.lean, with NO hypothesis beyond
EnclOK: for every grid form factor S inside the kernel-checked enclosures — in particular the law's own — and every certificate (c₀, r),
r ∈ C¹[0,1] with r′ =: g differentiable off a countable set with integrable derivative h, that is valid against the law,
c₀ + Σ_{j=1}^{256} (S(j)/256)·r(j/256) ≤ p, one has
      c₀ + ∫₀¹ r(x)·x dx ≤ p + 0.82395317·|r(1)| + (1/(6·256²) + τ/512)·(|r′(1)| + ∫₀¹|r″|),   τ = 3·10⁻⁴⁰,
and 1/(6·256²) + τ/512 < 2.5431316·10⁻⁶.  With p = p₀ = 0.68182868746… (the law's simple-point fraction; validity configuration-by-
configuration averaged over the law's weights) and r(1) = 0 this is the bound 0.6818287 + 2.55·10⁻⁶·(|r′(1)| + V(r′)).
-/
import Zeta23.PairCeiling.LawN256

open scoped BigOperators Interval
open MeasureTheory Set

noncomputable section

namespace Zeta23
namespace PairCeiling

/-- **the row certificate of the N = 256 law, unpacked**: near-CUE rows with τ = 3·10⁻⁴⁰ and |D(1)| ≤ 0.82395317. -/
theorem lawN256_rows (S : ℕ → ℝ) (hS : EnclOK LawN256.K S 0 LawN256.encl) :
    NearCUE S 256 ((3 : ℝ) / 10 ^ 40) ∧ |Dfun (massOf S 256) 256 1| ≤ (82395317 : ℝ) / 10 ^ 8 := by
  obtain ⟨_, h1, h2⟩ := cert_of_checkRows LawN256 LawN256_check S hS
  have eN : LawN256.N = 256 := rfl
  have etn : LawN256.tn = 3 := rfl
  have etd : LawN256.td = 10 ^ 40 := rfl
  have edn : LawN256.dn = 82395317 := rfl
  have edd : LawN256.dd = 10 ^ 8 := rfl
  simp only [eN, etn, etd, edn, edd, Nat.cast_ofNat, Nat.cast_pow] at h1 h2
  exact ⟨h1, h2⟩

/-- **CEILING AT THE N = 256 LAW (Theorem 1′ instance, exact constants).** -/
theorem ceiling_law256 (S : ℕ → ℝ) (hS : EnclOK LawN256.K S 0 LawN256.encl)
    {r g h : ℝ → ℝ} {T : Set ℝ} (hT : T.Countable) {c₀ p : ℝ}
    (hr : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt r (g x) x) (hg : ContinuousOn g (Icc (0:ℝ) 1))
    (hgh : ∀ x ∈ Ioo (0:ℝ) 1 \ T, HasDerivAt g (h x) x) (hh : IntervalIntegrable h volume 0 1)
    (hvalid : c₀ + ∑ j ∈ Finset.Icc 1 256, massOf S 256 j * r ((j:ℝ)/256) ≤ p) :
    c₀ + ∫ x in (0:ℝ)..1, r x * x
      ≤ p + (82395317 : ℝ) / 10 ^ 8 * |r 1|
          + (1 / (6 * (256 : ℝ) ^ 2) + ((3 : ℝ) / 10 ^ 40) / (2 * 256)) * |g 1|
          + (1 / (6 * (256 : ℝ) ^ 2) + ((3 : ℝ) / 10 ^ 40) / (2 * 256)) * ∫ x in (0:ℝ)..1, |h x| := by
  obtain ⟨hrows, hD1⟩ := lawN256_rows S hS
  have := ceiling_nearCUE (N := 256) (by norm_num) S (by positivity) hrows hD1 hT hr hg hgh hh hvalid
  push_cast at this
  exact this

/-- **the same with decimal constants**: v ≤ p + 0.82395317·|r(1)| + 2.5431316·10⁻⁶·|r′(1)| + 2.5431316·10⁻⁶·∫₀¹|r″|. -/
theorem ceiling_law256_decimal (S : ℕ → ℝ) (hS : EnclOK LawN256.K S 0 LawN256.encl)
    {r g h : ℝ → ℝ} {T : Set ℝ} (hT : T.Countable) {c₀ p : ℝ}
    (hr : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt r (g x) x) (hg : ContinuousOn g (Icc (0:ℝ) 1))
    (hgh : ∀ x ∈ Ioo (0:ℝ) 1 \ T, HasDerivAt g (h x) x) (hh : IntervalIntegrable h volume 0 1)
    (hvalid : c₀ + ∑ j ∈ Finset.Icc 1 256, massOf S 256 j * r ((j:ℝ)/256) ≤ p) :
    c₀ + ∫ x in (0:ℝ)..1, r x * x
      ≤ p + 0.82395317 * |r 1| + 2.5431316e-6 * |g 1| + 2.5431316e-6 * ∫ x in (0:ℝ)..1, |h x| := by
  have h0 := ceiling_law256 S hS hT hr hg hgh hh hvalid
  have hc : (1 / (6 * (256 : ℝ) ^ 2) + ((3 : ℝ) / 10 ^ 40) / (2 * 256)) ≤ 2.5431316e-6 := by norm_num
  have hd : (82395317 : ℝ) / 10 ^ 8 = 0.82395317 := by norm_num
  have ha : 0 ≤ |r 1| := abs_nonneg _
  have hb : 0 ≤ |g 1| := abs_nonneg _
  have hI : 0 ≤ ∫ x in (0:ℝ)..1, |h x| := intervalIntegral.integral_nonneg zero_le_one fun x _ => abs_nonneg _
  rw [hd] at h0
  nlinarith [mul_le_mul_of_nonneg_right hc hb, mul_le_mul_of_nonneg_right hc hI]

end PairCeiling
end Zeta23

end
