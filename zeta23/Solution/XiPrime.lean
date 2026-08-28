/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ChallengeDeps.XiPrime
import Zeta23.XiPrime.ExplicitFormula.ZeroFree
import Zeta23.XiPrime.Final

noncomputable section

/-- **Every zero of ξ′ lies in the open critical strip 0 < Re s < 1** (ξ(s) = ½s(s−1)π^{−s/2}Γ(s/2)ζ(s)). -/
theorem xiPrime_zeros_in_open_critical_strip :
    ∀ ρ : ℂ, XiPrime.xiDeriv ρ = 0 → 0 < ρ.re ∧ ρ.re < 1 :=
  Zeta23.XiPrime.xiDerivZerosInStrip_holds

/-- **Re ξ′/ξ(s) > 0 whenever Re s ≥ 1.** -/
theorem xiPrime_over_xi_re_pos :
    ∀ s : ℂ, 1 ≤ s.re → 0 < (XiPrime.xiDeriv s / XiPrime.xi s).re :=
  fun _ hs => Zeta23.XiPrime.re_logDeriv_xi_pos hs

/-- **At least 85.838% of the zeros of ξ′ are simple and on the critical line; at least 92.919% are
distinct** — for all large T, counting the zeros ρ of ξ′ with T < Im ρ ≤ 2T (ANY real part) with
multiplicity in the denominator. -/
theorem xiPrime_simple_zeros_on_critical_line :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.85838 : ℝ) * (XiPrime.Ncount T (2 * T) : ℝ) ≤ (XiPrime.N0simple T (2 * T) : ℝ) ∧
      (0.92919 : ℝ) * (XiPrime.Ncount T (2 * T) : ℝ) ≤ (XiPrime.Ndist T (2 * T) : ℝ) :=
  Zeta23.XiPrime.xiDeriv_simple_on_line

/-- the same for the windows 0 < Im ρ ≤ T (cumulative counts). -/
theorem xiPrime_simple_zeros_on_critical_line_cumulative :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.85838 : ℝ) * (XiPrime.Ncount 0 T : ℝ) ≤ (XiPrime.N0simple 0 T : ℝ) ∧
      (0.92919 : ℝ) * (XiPrime.Ncount 0 T : ℝ) ≤ (XiPrime.Ndist 0 T : ℝ) :=
  Zeta23.XiPrime.xiDeriv_simple_on_line_cumulative

/-- the same with the near-optimal quartic window: **at least 86.864% simple and on the critical line, at least 93.432%
distinct**, for all large T, zeros of ξ′ with T < Im ρ ≤ 2T counted with multiplicity in the denominator. -/
theorem xiPrime_simple_zeros_on_critical_line_quartic :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.86864 : ℝ) * (XiPrime.Ncount T (2 * T) : ℝ) ≤ (XiPrime.N0simple T (2 * T) : ℝ) ∧
      (0.93432 : ℝ) * (XiPrime.Ncount T (2 * T) : ℝ) ≤ (XiPrime.Ndist T (2 * T) : ℝ) :=
  Zeta23.XiPrime.xiDeriv_simple_on_line_quartic_std

/-- the quartic-window percentages for the cumulative windows 0 < Im ρ ≤ T: **at least 86.864% simple and on the
critical line, at least 93.432% distinct**, for all large T. -/
theorem xiPrime_simple_zeros_on_critical_line_quartic_cumulative :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.86864 : ℝ) * (XiPrime.Ncount 0 T : ℝ) ≤ (XiPrime.N0simple 0 T : ℝ) ∧
      (0.93432 : ℝ) * (XiPrime.Ncount 0 T : ℝ) ≤ (XiPrime.Ndist 0 T : ℝ) :=
  Zeta23.XiPrime.xiDeriv_simple_on_line_quartic_cumulative_std
