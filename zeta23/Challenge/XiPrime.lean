/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Challenge/XiPrime.lean — CHALLENGE: the zeros of ξ′.
Trusted vocabulary: ChallengeDeps.XiPrime (ξ, ξ′, its zero-counting functions) over Mathlib.
-/
import Mathlib

/-
The definitions below are inlined character-for-character from ChallengeDeps/XiPrime.lean
(the trusted Mathlib-only definition layer, which continues to exist for the Solution build), so
that this module's ONLY import is Mathlib. The anonymous `section` scopes that file's
`open`s to the inlined definitions, leaving the elaboration context of the statements below exactly
as it was when this module imported the definition layer. The comparator identifies constants by
name and requires each definition to elaborate identically to its Solution-side namesake. The block
is the COMPLETE definition layer (all 8 definitions of ChallengeDeps/XiPrime.lean): elaborating the
layer as a whole keeps any auxiliary lemmas it generates named identically on both sides.
-/
section
open scoped BigOperators
open Complex Set

noncomputable section

namespace XiPrime

/-- ξ(s) := s(s−1)/2 · Λ₀(s) + 1/2  (= ½ s(s−1) π^{-s/2} Γ(s/2) ζ(s) for s ∉ {0,1}; entire). -/
def xi (s : ℂ) : ℂ := s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2

/-- ξ′ := the complex derivative of ξ (an entire function; [XF′ §0] writes F := (ξ′)′/ξ′). -/
def xiDeriv : ℂ → ℂ := deriv xi

/-- ρ₁ is a zero of ξ′:  ξ′(ρ₁) = 0 — ALL zeros, NO real-part condition. -/
def IsXiDerivZero (ρ : ℂ) : Prop := xiDeriv ρ = 0

/-- m_{ρ₁} := multiplicity of ρ₁ as a zero of ξ′ = analytic order of ξ′ at ρ₁ (ℕ∞ → ℕ via toNat). -/
def xiDerivMult (ρ : ℂ) : ℕ := (analyticOrderAt xiDeriv ρ).toNat

/-- {ρ₁ : ξ′(ρ₁) = 0, T₁ < Im ρ₁ ≤ T₂}  (ALL zeros in the height window; positive ordinates, NOT |Im|).
This set is finite — every zero of ξ′ lies in the open critical strip (the first challenge statement) and the zeros of
the entire function ξ′ are isolated — so the finite sums and cardinalities below are genuine counts (Lean's `finsum`
and `Set.ncard` would return 0 on an infinite set). -/
def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsXiDerivZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- N_{ξ′}(T₁,T₂) := number of zeros of ξ′ with T₁ < Im ≤ T₂ (any real part), COUNTED WITH MULTIPLICITY. -/
def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, xiDerivMult ρ

/-- N_{d,ξ′}(T₁,T₂) := number of DISTINCT zeros of ξ′ with T₁ < Im ≤ T₂ (any real part). -/
def Ndist (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂).ncard

/-- N^{s}_{0,ξ′}(T₁,T₂) := #{ρ₁ : T₁ < Im ρ₁ ≤ T₂, Re ρ₁ = 1/2, m_{ρ₁} = 1}: SIMPLE zeros of ξ′ ON the
critical line (each such point counted once — it is simple). -/
def N0simple (T₁ T₂ : ℝ) : ℕ :=
  (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | xiDerivMult ρ = 1}).ncard

end XiPrime

end
end

noncomputable section

/-- **Every zero of ξ′ lies in the open critical strip 0 < Re s < 1** (ξ(s) = ½s(s−1)π^{−s/2}Γ(s/2)ζ(s)). -/
theorem xiPrime_zeros_in_open_critical_strip :
    ∀ ρ : ℂ, XiPrime.xiDeriv ρ = 0 → 0 < ρ.re ∧ ρ.re < 1 := by
  sorry

/-- **Re ξ′/ξ(s) > 0 whenever Re s ≥ 1.** -/
theorem xiPrime_over_xi_re_pos :
    ∀ s : ℂ, 1 ≤ s.re → 0 < (XiPrime.xiDeriv s / XiPrime.xi s).re := by
  sorry

/-- **At least 85.838% of the zeros of ξ′ are simple and on the critical line; at least 92.919% are
distinct** — for all large T, counting the zeros ρ of ξ′ with T < Im ρ ≤ 2T (ANY real part) with
multiplicity in the denominator. -/
theorem xiPrime_simple_zeros_on_critical_line :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.85838 : ℝ) * (XiPrime.Ncount T (2 * T) : ℝ) ≤ (XiPrime.N0simple T (2 * T) : ℝ) ∧
      (0.92919 : ℝ) * (XiPrime.Ncount T (2 * T) : ℝ) ≤ (XiPrime.Ndist T (2 * T) : ℝ) := by
  sorry

/-- the same for the windows 0 < Im ρ ≤ T (cumulative counts). -/
theorem xiPrime_simple_zeros_on_critical_line_cumulative :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.85838 : ℝ) * (XiPrime.Ncount 0 T : ℝ) ≤ (XiPrime.N0simple 0 T : ℝ) ∧
      (0.92919 : ℝ) * (XiPrime.Ncount 0 T : ℝ) ≤ (XiPrime.Ndist 0 T : ℝ) := by
  sorry

/-- the same with the near-optimal quartic window: **at least 86.864% simple and on the critical line, at least 93.432%
distinct**, for all large T, zeros of ξ′ with T < Im ρ ≤ 2T counted with multiplicity in the denominator. -/
theorem xiPrime_simple_zeros_on_critical_line_quartic :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.86864 : ℝ) * (XiPrime.Ncount T (2 * T) : ℝ) ≤ (XiPrime.N0simple T (2 * T) : ℝ) ∧
      (0.93432 : ℝ) * (XiPrime.Ncount T (2 * T) : ℝ) ≤ (XiPrime.Ndist T (2 * T) : ℝ) := by
  sorry

/-- the quartic-window percentages for the cumulative windows 0 < Im ρ ≤ T: **at least 86.864% simple and on the
critical line, at least 93.432% distinct**, for all large T. -/
theorem xiPrime_simple_zeros_on_critical_line_quartic_cumulative :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.86864 : ℝ) * (XiPrime.Ncount 0 T : ℝ) ≤ (XiPrime.N0simple 0 T : ℝ) ∧
      (0.93432 : ℝ) * (XiPrime.Ncount 0 T : ℝ) ≤ (XiPrime.Ndist 0 T : ℝ) := by
  sorry
