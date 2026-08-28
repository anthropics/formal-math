/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Solution.lean — the UNTRUSTED comparator solution module: the seventeen statements of Challenge.lean,
byte-identical, each PROVED by delegating to the Zeta23 library:

  A        →  Zeta23.thmA₀ / thmA₀_cumulative (Zeta23/Final.lean, re-exported with English names by
              Zeta23/Unconditional.lean);
  B, C     →  Zeta23.thmB₀_mult / thmC₀_mult (+ cumulative)                (Zeta23/FinalMult.lean);
  D        →  Zeta23.ThmD.thmD₀                                            (Zeta23/ThmD/Final.lean);
              thmD₀_simple_mult / thmD₀_dist_mult (+ cumulative; constants HD 1 = 2 − 1/cStar 1 and
              GD 1 = 3/2 − (cStar 1)⁻¹/2)                                   (Zeta23/ThmD/Mult.lean);
  E        →  Zeta23.ThmE.thmE_A₀ (Zeta23/ThmE/Final.lean); thmE_B₀_mult / thmE_C₀_mult
              (Zeta23/ThmE/Mult.lean);
  D for χ  →  Zeta23.ThmDE.thmE_D₀ (Zeta23/ThmDE/Final.lean); thmE_D₀_simple_mult / thmE_D₀_dist_mult
              (Zeta23/ThmDE/Mult.lean).

The challenge's counting functions (ChallengeDeps.lean, inlined verbatim in Challenge.lean) are
character-for-character the Zeta23 ones (Zeta23/Statement.lean §1, Zeta23/ThmE/Statement.lean §1) in a
different namespace, so each delegation typechecks by definitional unfolding in the kernel. The only
mathematics proved HERE is the identity `cStar_one_eq_cMT`: Zeta23 carries the Theorem-D constant as
`Zeta23.ThmD.cStar 1` (= √2·sin ϑ/(cos ϑ + ϑ·sin ϑ) at ϑ = 1/√2, a division-safe form) and
`Zeta23.ThmD.HD 1 = 2 − 1/cStar 1`, `Zeta23.ThmD.GD 1 = 3/2 − (cStar 1)⁻¹/2`, while the challenge
states the paper's displayed closed form c₁* = √2·tan ϑ/(1 + ϑ·tan ϑ), ϑ = 1/√2.

Nothing in this file is part of the trusted base: comparator re-checks that every theorem below has
exactly the statement of its Challenge namesake and uses only the permitted axioms.
-/
import ChallengeDeps
import Zeta23.Unconditional
import Zeta23.FinalMult
import Zeta23.ThmD.Final
import Zeta23.ThmD.Mult
import Zeta23.ThmE.Final
import Zeta23.ThmE.Mult
import Zeta23.ThmDE.Final
import Zeta23.ThmDE.Mult

noncomputable section

/-- The Zeta23 library's Theorem-D constant `cStar 1` (division-safe sin/cos form) equals the
challenge's `cMT` (the paper's tan form at ϑ = 1/√2): by Zeta23's own `cStar_eq_tan_form` and
unfolding `Zeta23.ThmD.theta 1 = 1 / Real.sqrt 2`. -/
theorem cStar_one_eq_cMT : Zeta23.ThmD.cStar 1 = cMT := by
  rw [Zeta23.ThmD.cStar_eq_tan_form zero_le_one le_rfl]
  unfold cMT Zeta23.ThmD.theta
  rfl

theorem two_thirds_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  Zeta23.thmA₀

theorem two_thirds_on_critical_line_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  Zeta23.thmA₀_cumulative

theorem two_thirds_simple_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  Zeta23.thmB₀_mult

theorem two_thirds_simple_on_critical_line_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  Zeta23.thmB₀_mult_cumulative

theorem five_sixths_distinct :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (5 / 6 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  Zeta23.thmC₀_mult

theorem five_sixths_distinct_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (5 / 6 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T :=
  Zeta23.thmC₀_mult_cumulative

theorem montgomery_taylor_on_critical_line :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - 1 / cMT - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) := by
  have h := @Zeta23.ThmD.thmD₀
  simp only [Zeta23.ThmD.HD, cStar_one_eq_cMT] at h
  exact h

theorem montgomery_taylor_simple_on_critical_line_mult :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - 1 / cMT - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  have h := @Zeta23.ThmD.thmD₀_simple_mult
  simp only [Zeta23.ThmD.HD, cStar_one_eq_cMT] at h
  exact h

theorem montgomery_taylor_simple_on_critical_line_mult_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - 1 / cMT - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  have h := @Zeta23.ThmD.thmD₀_simple_mult_cumulative
  simp only [Zeta23.ThmD.HD, cStar_one_eq_cMT] at h
  exact h

theorem montgomery_taylor_distinct_mult :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 2 - cMT⁻¹ / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) := by
  have h := @Zeta23.ThmD.thmD₀_dist_mult
  simp only [Zeta23.ThmD.GD, cStar_one_eq_cMT] at h
  exact h

theorem montgomery_taylor_distinct_mult_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 2 - cMT⁻¹ / 2 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T := by
  have h := @Zeta23.ThmD.thmD₀_dist_mult_cumulative
  simp only [Zeta23.ThmD.GD, cStar_one_eq_cMT] at h
  exact h

theorem dirichlet_two_thirds_on_critical_line
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0starL χ T (2 * T) :=
  Zeta23.ThmE.thmE_A₀ hq hχ

theorem dirichlet_two_thirds_simple_on_critical_line
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0simpleL χ T (2 * T) :=
  Zeta23.ThmE.thmE_B₀_mult hq hχ

theorem dirichlet_five_sixths_distinct
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (5 / 6 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ NdistL χ T (2 * T) :=
  Zeta23.ThmE.thmE_C₀_mult hq hχ

theorem dirichlet_montgomery_taylor_on_critical_line
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - 1 / cMT - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0starL χ T (2 * T) := by
  have h := Zeta23.ThmDE.thmE_D₀ (χ := χ) hq hχ
  simp only [Zeta23.ThmD.HD, cStar_one_eq_cMT] at h
  exact h

theorem dirichlet_montgomery_taylor_simple_on_critical_line_mult
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - 1 / cMT - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0simpleL χ T (2 * T) := by
  have h := Zeta23.ThmDE.thmE_D₀_simple_mult (χ := χ) hq hχ
  simp only [Zeta23.ThmD.HD, cStar_one_eq_cMT] at h
  exact h

theorem dirichlet_montgomery_taylor_distinct_mult
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 2 - cMT⁻¹ / 2 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ NdistL χ T (2 * T) := by
  have h := Zeta23.ThmDE.thmE_D₀_dist_mult (χ := χ) hq hχ
  simp only [Zeta23.ThmD.GD, cStar_one_eq_cMT] at h
  exact h

end
