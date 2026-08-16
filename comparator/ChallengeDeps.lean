/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ChallengeDeps.lean — the TRUSTED definition layer for the comparator challenge
(see comparator/README.md).

Everything the zeta and Dirichlet challenge statements mention is defined HERE, from Mathlib alone:
the nontrivial zeros of Mathlib's `riemannZeta` (resp. of Mathlib's `DirichletCharacter.LFunction χ`),
their multiplicity via Mathlib's `analyticOrderAt`, the standard counting functions of the
critical-line literature, and the Montgomery–Taylor constant c₁* of Theorem D, written out in
closed form. This module imports NOTHING from Zeta23/. A reader auditing WHAT is claimed needs to
read only this file and the applicable challenge file (trusting Mathlib and the Lean kernel); the proofs
live in the Zeta23 library and are checked against these statements by github.com/leanprover/comparator
(statement equality + axiom audit + kernel replay), via the corresponding Solution module.

Every `def` line of §1 is character-for-character the one in Zeta23/Statement.lean §1, and every `def`
of §2 the one in Zeta23/ThmE/Statement.lean §1 (docstrings are reworded for a reader without the rest
of the repository). The copies live
in the root namespace (Zeta23's live in `Zeta23` / `Zeta23.ThmE`) so that Solution.lean can import both this
module and the Zeta23 development without name clashes.
-/
import Mathlib

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

/-- N₀(T₁,T₂): the zeros ON the critical line Re ρ = 1/2 with T₁ < Im ρ ≤ T₂, with multiplicity.
(Used by the simple-or-on-line statements in `Challenge/Union.lean`.) -/
def N0 (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}, zeroMult ρ

/-- N₀*(T₁,T₂): the number of DISTINCT zeros ON the critical line Re ρ = 1/2 with
T₁ < Im ρ ≤ T₂. This is what Theorems A and D bound from below. -/
def N0star (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}).ncard

/-- N₀ˢ(T₁,T₂): the number of SIMPLE zeros (multiplicity exactly 1) ON the critical line with
T₁ < Im ρ ≤ T₂. -/
def N0simple (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1}).ncard

/-- Nˢ(T₁,T₂): the number of simple zeros with T₁ < Im ρ ≤ T₂ (anywhere in the strip).
(Used by the simple-or-on-line statements in `Challenge/Union.lean`.) -/
def Nsimple (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | zeroMult ρ = 1}).ncard

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
/-- N_{0,χ}(T₁,T₂): on the line, with multiplicity. (Not used by the statements; kept for parity.) -/
def N0L (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosInL χ T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}, zeroMultL χ ρ
/-- N*_{0,χ}(T₁,T₂): on the line, distinct. -/
def N0starL (T₁ T₂ : ℝ) : ℕ := (zerosInL χ T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}).ncard
/-- N^s_{0,χ}(T₁,T₂): on the line and simple. -/
def N0simpleL (T₁ T₂ : ℝ) : ℕ :=
  (zerosInL χ T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMultL χ ρ = 1}).ncard
/-- N^s_χ(T₁,T₂): simple zeros. (Not used by the statements; kept for parity.) -/
def NsimpleL (T₁ T₂ : ℝ) : ℕ := (zerosInL χ T₁ T₂ ∩ {ρ | zeroMultL χ ρ = 1}).ncard

end Dirichlet

/-! ## 3. The Montgomery–Taylor constant of Theorem D -/

/-- c₁* := √2·tan ϑ / (1 + ϑ·tan ϑ) at ϑ = 1/√2 — the paper's closed form for the optimal-window
constant c*_λ = √2·tan ϑ/(1 + ϑ·tan ϑ), ϑ = λ/√2, at λ = 1. Numerically c₁* = 0.7532960…
(= 2·tan(1/√2)/(√2 + tan(1/√2)); 1/c₁* = 1/2 + 2^{-1/2}·cot(2^{-1/2}) is the Montgomery–Taylor
constant). Theorem D's three proportions are 2 − 1/c₁* = 0.67250…, 2c₁* − 1 = 0.50659… and
c₁* = 0.75329…; the decimals are NOT part of the formal statements. -/
def cMT : ℝ :=
  Real.sqrt 2 * Real.tan (1 / Real.sqrt 2) / (1 + 1 / Real.sqrt 2 * Real.tan (1 / Real.sqrt 2))

end
