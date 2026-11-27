/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Challenge/SextupleA1275.lean — TRUSTED comparator challenge module for the
refined sextuple (six-translate) improvement of the simple critical-line
proportion at `A = 51/4000`.

The coefficient `0.6727837118` is strictly below the exact endpoint
`(6·B_MT − 10π·B₆)/(6 − 51/4000) = 0.67278371…` with `B₆ = 1094977/5000000000`,
and strictly above the baseline sextuple endpoint `0.67275562…` (`A₆ = 1/80`).
`N0simple` counts simple on-line zeros; the denominator `Ncount` counts all
zeros with multiplicity.
Proof: Solution.SextupleA1275.  Config: comparator/config-sextuple-a1275.json.

The four `sorry`s are deliberate (challenge side).
-/
import Mathlib

/-
The definitions below are inlined character-for-character from comparator/ChallengeDeps.lean
(the trusted Mathlib-only definition layer, which continues to exist for the Solution build), so
that this module's ONLY import is Mathlib. The anonymous `section` scopes ChallengeDeps.lean's
`open`s to the inlined definitions, leaving the elaboration context of the statements below exactly
as it was when this module imported the definition layer. The comparator identifies constants by
name and requires each definition to elaborate identically to its Solution-side namesake. The block
is the COMPLETE definition layer, not just the constants these statements mention: elaborating the
layer as a whole is what keeps the auxiliary lemmas it generates (e.g. N0star._proof_1, which later
definitions reuse) named identically on the challenge and solution sides.
-/
section
open scoped BigOperators ComplexConjugate
open Complex Set

noncomputable section

/-! ## 1. Nontrivial zeros of ζ and the counting functions (Theorems A–D) -/

/-- ρ is a nontrivial zero of the Riemann zeta function: ζ(ρ) = 0 with 0 < Re ρ < 1 (the open
critical strip). Every zero in the strip is "nontrivial" in the usual sense (it is neither a trivial
zero −2(n+1), of real part ≤ −2, nor the pole s = 1); the converse — that every zero other than the
trivial ones lies in the open strip — is classical and is not needed to state the theorems. -/
def IsNontrivialZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- m_ρ, the multiplicity of ρ: the order of vanishing of ζ at ρ, via Mathlib's `analyticOrderAt`
(ℕ∞-valued; `toNat` sends ⊤ to 0, so `1 ≤ zeroMult ρ` encodes both "ζ is not locally identically
zero at ρ" and "ρ is a zero"). -/
def zeroMult (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat

/-- The nontrivial zeros with ordinate in the window (T₁, T₂]: {ρ | ζ(ρ) = 0, 0 < Re ρ < 1,
T₁ < Im ρ ≤ T₂}. (Positive-ordinate window, not |Im ρ|.) -/
def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsNontrivialZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- N(T₁,T₂): the number of nontrivial zeros with T₁ < Im ρ ≤ T₂, counted WITH multiplicity
(`∑ᶠ` is Mathlib's finite sum; that the window contains finitely many zeros is proved on the
solution side, not assumed). -/
def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeroMult ρ

/-- N_d(T₁,T₂): the number of nontrivial zeros with T₁ < Im ρ ≤ T₂, each distinct zero counted
once. -/
def Ndist (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂).ncard

/-- N₀*(T₁,T₂): the number of DISTINCT zeros ON the critical line Re ρ = 1/2 with
T₁ < Im ρ ≤ T₂. This is what Theorems A and D bound from below. -/
def N0star (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}).ncard

/-- N₀ˢ(T₁,T₂): the number of SIMPLE zeros (multiplicity exactly 1) ON the critical line with
T₁ < Im ρ ≤ T₂. -/
def N0simple (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1}).ncard

/-! ## 2. The same for a Dirichlet L-function L(s,χ) (Theorem E)

`χ.LFunction` is Mathlib's `DirichletCharacter.LFunction χ : ℂ → ℂ`, the analytic continuation of
L(s,χ) (for a character χ mod q, `q ≠ 0`). -/

section Dirichlet

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- ρ is a nontrivial zero of L(s,χ): L(ρ,χ) = 0 with 0 < Re ρ < 1. -/
def IsNontrivialZeroL (ρ : ℂ) : Prop := χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- m_ρ: the order of vanishing of L(·,χ) at ρ (via `analyticOrderAt`, as for ζ). -/
def zeroMultL (ρ : ℂ) : ℕ := (analyticOrderAt χ.LFunction ρ).toNat

/-- the nontrivial zeros of L(·,χ) with T₁ < Im ρ ≤ T₂. -/
def zerosInL (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsNontrivialZeroL χ ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- N_χ(T₁,T₂): nontrivial zeros of L(s,χ) with T₁ < Im ρ ≤ T₂, with multiplicity. -/
def NcountL (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosInL χ T₁ T₂, zeroMultL χ ρ
/-- N_{d,χ}(T₁,T₂): distinct zeros. -/
def NdistL (T₁ T₂ : ℝ) : ℕ := (zerosInL χ T₁ T₂).ncard
/-- N*_{0,χ}(T₁,T₂): on the line, distinct. -/
def N0starL (T₁ T₂ : ℝ) : ℕ := (zerosInL χ T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}).ncard
/-- N^s_{0,χ}(T₁,T₂): on the line and simple. -/
def N0simpleL (T₁ T₂ : ℝ) : ℕ :=
  (zerosInL χ T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMultL χ ρ = 1}).ncard

end Dirichlet

/-! ## 3. The Montgomery–Taylor constant of Theorem D -/

/-- c₁* := √2·tan ϑ / (1 + ϑ·tan ϑ) at ϑ = 1/√2 — the paper's closed form for the optimal-window
constant c*_λ = √2·tan ϑ/(1 + ϑ·tan ϑ), ϑ = λ/√2, at λ = 1. Numerically c₁* = 0.7532960…
(= 2·tan(1/√2)/(√2 + tan(1/√2)); 1/c₁* = 1/2 + 2^{-1/2}·cot(2^{-1/2}) is the Montgomery–Taylor
constant). Theorem D's proportions here are 2 − 1/c₁* = 0.67250… (for N₀* and N₀ˢ) and
(3 − 1/c₁*)/2 = 0.83625… (for N_d); the decimals are NOT part of the formal statements. -/
def cMT : ℝ :=
  Real.sqrt 2 * Real.tan (1 / Real.sqrt 2) / (1 + 1 / Real.sqrt 2 * Real.tan (1 / Real.sqrt 2))

end
end

noncomputable section

/-- Refined sextuple simple-and-on-line endpoint in dyadic windows, ε-form. -/
theorem sextuple_a1275_simple_on_critical_line_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6727837118 / 10 ^ 10 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        N0simple T (2 * T) := by
  sorry

/-- Refined sextuple simple-and-on-line endpoint in cumulative windows, ε-form. -/
theorem sextuple_a1275_simple_on_critical_line_cumulative_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6727837118 / 10 ^ 10 : ℝ) - ε) * (Ncount 0 T : ℝ) ≤
        N0simple 0 T := by
  sorry

/-- Fixed coefficient `0.6727837118` in dyadic windows. -/
theorem sextuple_a1275_simple_on_critical_line_6727837118 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6727837118 / 10 ^ 10 : ℝ) * (Ncount T (2 * T) : ℝ) ≤
        N0simple T (2 * T) := by
  sorry

/-- Fixed coefficient `0.6727837118` in cumulative windows. -/
theorem sextuple_a1275_simple_on_critical_line_cumulative_6727837118 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6727837118 / 10 ^ 10 : ℝ) * (Ncount 0 T : ℝ) ≤
        N0simple 0 T := by
  sorry
