/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/Statement.lean — Theorem E (Dirichlet L-functions): statement layer against Mathlib's
`DirichletCharacter.LFunction`.

Canonical text: the paper §7.2 [subsec:dirichlet], [thm:E], verbatim:
"Let χ be a primitive character modulo q>1, and let N_χ(T₁,T₂), N^s_{0,χ}, N_{d,χ} count the nontrivial
 zeros of L(s,χ) with T₁<γ≤T₂ as in §1; N_χ(T,2T) = (T/2π)log(qT/2π) + O(T).
 THEOREM E. Fix q and a primitive χ mod q. For fixed 0<λ≤1 and T ≥ T₀(λ,q),
 N*_{0,χ}(T,2T) ≥ (H(λ)−o(1))N_χ(T,2T), N^s_{0,χ}(T,2T) ≥ (2F(λ)−1−o(1))N_χ(T,2T) and
 N_{d,χ}(T,2T) ≥ (F(λ)−o(1))N_χ(T,2T); in particular at least (2/3−o(1))N_χ(T,2T) of the zeros of
 L(s,χ) with T<γ≤2T are on the critical line, at least (1/2−o(1))N_χ(T,2T) are simple and on the
 line, and at least (3/4−o(1))N_χ(T,2T) are distinct. Theorem D holds likewise."

This is the only file of the Theorem E development that mentions Mathlib's Dirichlet L-functions.
Mathlib provides: `DirichletCharacter.LFunction χ : ℂ → ℂ` (entire for χ ≠ 1,
`differentiable_LFunction`), `IsPrimitive`, `completedLFunction` with the functional equation
`IsPrimitive.completedLFunction_one_sub` (χ ↔ χ⁻¹, `rootNumber`), `gammaFactor` (parity), and
non-vanishing on Re s ≥ 1 (`LFunction_ne_zero_of_one_le_re`).  Structure mirrors `Zeta23/Statement.lean`:
(1) nontrivial zeros / multiplicity / the six counts; (2) the seam facts `LSeam χ` (classical facts
about L(s,χ), discharged from Mathlib elsewhere in the repository — [thm:E] proof (ii)) and the
abstract `ZeroConfig`; (3) the parameters (parity κ, coefficients χ(n)) for the ε-form statements
of Theorem E (fixed λ ∈ (0,1), then 2/3, 1/2, 3/4), which are proved in Zeta23/ThmE/Final.lean.
-/
import Zeta23.ThmE.Hypotheses
import Zeta23.Defs.Counting
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Analytic.Order

open scoped BigOperators ComplexConjugate
open Complex Set

noncomputable section

namespace Zeta23
namespace ThmE

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-! ## 1. Nontrivial zeros of L(s,χ) and multiplicity, against Mathlib -/

/-- ρ is a nontrivial zero of L(s,χ): L(ρ,χ) = 0 with 0 < Re ρ < 1  ("count the nontrivial zeros
of L(s,χ) … as in §1"; [thm:E] proof (ii): "all zeros have 0<β<1"). -/
def IsNontrivialZeroL (ρ : ℂ) : Prop := χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- m_ρ: the order of vanishing of L(·,χ) at ρ (analytic order; toNat sends ⊤ to 0, so
1 ≤ zeroMultL χ ρ encodes "not locally identically zero" and "is a zero"). -/
def zeroMultL (ρ : ℂ) : ℕ := (analyticOrderAt χ.LFunction ρ).toNat

/-- {ρ nontrivial zero of L(·,χ) : T₁ < γ ≤ T₂}, γ = Im ρ. -/
def zerosInL (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsNontrivialZeroL χ ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- N_χ(T₁,T₂), with multiplicity. -/
def NcountL (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosInL χ T₁ T₂, zeroMultL χ ρ
/-- N_{d,χ}(T₁,T₂): distinct zeros. -/
def NdistL (T₁ T₂ : ℝ) : ℕ := (zerosInL χ T₁ T₂).ncard
/-- N_{0,χ}(T₁,T₂): on the line, with multiplicity. -/
def N0L (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosInL χ T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}, zeroMultL χ ρ
/-- N*_{0,χ}(T₁,T₂): on the line, distinct. -/
def N0starL (T₁ T₂ : ℝ) : ℕ := (zerosInL χ T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}).ncard
/-- N^s_{0,χ}(T₁,T₂): on the line and simple. -/
def N0simpleL (T₁ T₂ : ℝ) : ℕ :=
  (zerosInL χ T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMultL χ ρ = 1}).ncard
/-- N^s_χ(T₁,T₂): simple zeros. -/
def NsimpleL (T₁ T₂ : ℝ) : ℕ := (zerosInL χ T₁ T₂ ∩ {ρ | zeroMultL χ ρ = 1}).ncard

/-! ## 2. The seam: the zeros of L(s,χ) as an abstract ZeroConfig  ([thm:E] proof (ii)) -/

/-- Classical facts about L(s,χ), χ primitive mod q > 1, needed to instantiate `Zeta23.ZeroConfig` —
obligations discharged from Mathlib elsewhere in the repository, not inputs of the paper.
[thm:E] proof (ii), verbatim:
"the multiset of zeros of L(s,χ) is invariant under ρ ↦ 1−ρ̄ with multiplicities (functional equation
χ ↔ χ̄ composed with conj L(conj s,χ) = L(s,χ̄))".  (The γ ↦ −γ symmetry fails for complex χ; the
abstract layer does not use it — the local count in `RiemannVonMangoldtChi` is two-sided instead.) -/
structure LSeam : Prop where
  one_le_mult : ∀ ρ, IsNontrivialZeroL χ ρ → 1 ≤ zeroMultL χ ρ
  reflect_zero : ∀ ρ, IsNontrivialZeroL χ ρ → IsNontrivialZeroL χ (reflect ρ)
  mult_reflect : ∀ ρ, IsNontrivialZeroL χ ρ → zeroMultL χ (reflect ρ) = zeroMultL χ ρ
  finite_window : ∀ T₁ T₂ : ℝ,
    ({ρ | IsNontrivialZeroL χ ρ} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite

variable {χ}

/-- The nontrivial zeros of L(s,χ) with multiplicities, as an abstract zero configuration
(carrier := exactly the nontrivial zeros, mult := exactly the analytic order). -/
def LZeros (hs : LSeam χ) : ZeroConfig where
  carrier := {ρ | IsNontrivialZeroL χ ρ}
  mult := zeroMultL χ
  one_le_mult := hs.one_le_mult
  strip := fun _ h => ⟨h.2.1.le, h.2.2.le⟩
  reflect_mem := hs.reflect_zero
  mult_reflect := hs.mult_reflect
  finite_window := hs.finite_window

section seam_rfl
variable (hs : LSeam χ) (T₁ T₂ : ℝ)

@[simp] lemma LZeros_carrier : (LZeros hs).carrier = {ρ | IsNontrivialZeroL χ ρ} := rfl
@[simp] lemma LZeros_mult : (LZeros hs).mult = zeroMultL χ := rfl
@[simp] lemma LZeros_simple : (LZeros hs).simple = {ρ | zeroMultL χ ρ = 1} := rfl

lemma LZeros_window : (LZeros hs).window T₁ T₂ = zerosInL χ T₁ T₂ := by
  ext ρ; simp [ZeroConfig.window, zerosInL]

@[simp] lemma LZeros_N : (LZeros hs).N T₁ T₂ = NcountL χ T₁ T₂ := by
  simp [ZeroConfig.N, NcountL, LZeros_window]
@[simp] lemma LZeros_Nd : (LZeros hs).Nd T₁ T₂ = NdistL χ T₁ T₂ := by
  simp [ZeroConfig.Nd, NdistL, LZeros_window]
@[simp] lemma LZeros_N0star : (LZeros hs).N0star T₁ T₂ = N0starL χ T₁ T₂ := by
  simp [ZeroConfig.N0star, N0starL, LZeros_window, ZeroConfig.onLine]
@[simp] lemma LZeros_N0s : (LZeros hs).N0s T₁ T₂ = N0simpleL χ T₁ T₂ := by
  simp [ZeroConfig.N0s, N0simpleL, LZeros_window, ZeroConfig.onLine]

/-- [eq:trivialchain] for L(s,χ), from the abstract `ZeroConfig.trivial_chain`. -/
theorem trivial_chainL (hs : LSeam χ) (T₁ T₂ : ℝ) :
    N0simpleL χ T₁ T₂ ≤ N0starL χ T₁ T₂ ∧ N0starL χ T₁ T₂ ≤ N0L χ T₁ T₂ ∧
      N0L χ T₁ T₂ ≤ NcountL χ T₁ T₂ ∧ N0simpleL χ T₁ T₂ ≤ NsimpleL χ T₁ T₂ ∧
      NsimpleL χ T₁ T₂ ≤ NdistL χ T₁ T₂ ∧ NdistL χ T₁ T₂ ≤ NcountL χ T₁ T₂ := by
  have h := (LZeros hs).trivial_chain T₁ T₂
  simpa only [ZeroConfig.N0s, ZeroConfig.N0star, ZeroConfig.N0, ZeroConfig.N, ZeroConfig.Ns,
    ZeroConfig.Nd, LZeros_window, ZeroConfig.onLine, LZeros_simple, LZeros_mult, N0simpleL, N0starL,
    N0L, NcountL, NsimpleL, NdistL] using h

end seam_rfl

/-! ## 3. Theorem E — parameters  ([thm:E]; ε-forms at fixed λ ∈ (0,1), then 2/3, 1/2, 3/4)

The parity is κ := (1−χ(−1))/2, i.e. κ = 0 for χ even and κ = 1 for χ odd, and the coefficient
sequence is c n := χ(n) (n : ℕ cast into ZMod q). The hypotheses are those of `PaperInputsChi`
(Zeta23/ThmE/Hypotheses.lean) at these parameters, for the configuration `LZeros hs`. -/

variable (χ)

open scoped Classical in
/-- κ = (1−χ(−1))/2 as a natural number: 0 if χ is even, 1 if χ is odd. -/
def parity : ℕ := if χ.Even then 0 else 1

/-- the coefficient character values n ↦ χ(n). -/
def coeff : ℕ → ℂ := fun n => χ (n : ZMod q)

-- The four Theorem E statements (thmE_A_lam, thmE_A, thmE_B, thmE_C) are theorems in
-- Zeta23/ThmE/Final.lean, together with the zero-hypothesis forms thmE_A₀/thmE_B₀/thmE_C₀.


end ThmE
end Zeta23
