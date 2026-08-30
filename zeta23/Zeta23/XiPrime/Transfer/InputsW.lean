/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization.

Z′ (Hardy W) analogue, TRACE TRANSFER: the coefficient INPUT proposition of
the W analogue of [XF′ Lemma 6.1] (produced by theorem wReexpansion).

`Reexpansion` with ONE change, in the field `expand`: the base point is the REAL
parameter ½ l(T) (= Defs.L2star at τ⋆ = T; [XF′ §9.3(ii)]: "C(N; ½ l) (REAL parameter, no phase)") instead of
L_T = ½l + iπ/4.  With L_{2⋆}(τ⋆_{kl}) = ½ log(τ⋆/2π) = ½ l + δ_{kl}, δ_{kl} = ½ log(τ⋆_{kl}/T) ∈ [0, ½ log 2] ⊆ [0, 1/2]
exactly as for ξ′, the expansion is on δ ∈ Icc 0 (1/2).  This is the right
sentence for F = wCoeffFamily (F.c T N = xiCoeff ((l T / 2 : ℝ) : ℂ) N by rfl).
-/
import Zeta23.XiPrime.Transfer.Inputs

noncomputable section

open Finset Filter Real
open scoped BigOperators

namespace Zeta23
namespace XiPrime

/-- **The re-expansion input for the Z′ coefficients** [XF′ §6 at the real base ½l; §9.3(ii)].
Provided by the theorem `wReexpansion : ∃ e ρ₀ A T₀, 0 ≤ ρ₀ ∧ ReexpansionW wCoeffFamily e ρ₀ A T₀`,
with e T r N = Σ_{j<Ω(N)} binom(−(j+1), r) (½l)^{−(j+1)−r} [(Λ·log)∗Λ^{∗j}](N).  Constants are T-uniform; sums over
N ∈ Finset.Ioc 0 ⌊x⌋₊ for 2 ≤ x ≤ e^{l(T)}; 0 ≤ A is not carried (derivable from H3). -/
structure ReexpansionW (F : CoeffFamily) (e : ℝ → ℕ → ℕ → ℂ) (ρ₀ A T₀ : ℝ) : Prop where
  /-- C(N; ½l + δ) − c^{(T)}_N = Σ_{r≥1} e_r(N) δ^r  on δ ∈ [0, 1/2]  (absolutely convergent: |δ| < ½l once l > 1). -/
  expand : ∀ T : ℝ, T₀ ≤ T → ∀ δ : ℝ, δ ∈ Set.Icc (0:ℝ) (1 / 2) → ∀ N : ℕ,
    HasSum (fun r : ℕ => e T (r + 1) N * (δ : ℂ) ^ (r + 1))
      (xiCoeff (((l T / 2 : ℝ) : ℂ) + δ) N - F.c T N)
  /-- e_r(1) = 0. -/
  e_one : ∀ T : ℝ, ∀ r : ℕ, e T r 1 = 0
  /-- (H1)_r: Σ_{N≤x} |e_r(N)| N^{−1/2} ≤ A (ρ₀/l)^r √x · l. -/
  H1 : ∀ T : ℝ, T₀ ≤ T → ∀ r : ℕ, 1 ≤ r → ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp (l T) →
    (∑ N ∈ Finset.Ioc 0 ⌊x⌋₊, ‖e T r N‖ / Real.sqrt N) ≤ A * (ρ₀ / l T) ^ r * Real.sqrt x * l T
  /-- (H2)_r: Σ_{N≤x} |e_r(N)|² ≤ A (ρ₀/l)^{2r} x l². -/
  H2 : ∀ T : ℝ, T₀ ≤ T → ∀ r : ℕ, 1 ≤ r → ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp (l T) →
    (∑ N ∈ Finset.Ioc 0 ⌊x⌋₊, ‖e T r N‖ ^ 2) ≤ A * (ρ₀ / l T) ^ (2 * r) * x * l T ^ 2
  /-- (H3)_r: Σ_{N≤x} |e_r(N)|²/N ≤ A (ρ₀/l)^{2r} l² (1 + log x). -/
  H3 : ∀ T : ℝ, T₀ ≤ T → ∀ r : ℕ, 1 ≤ r → ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp (l T) →
    (∑ N ∈ Finset.Ioc 0 ⌊x⌋₊, ‖e T r N‖ ^ 2 / N) ≤ A * (ρ₀ / l T) ^ (2 * r) * l T ^ 2 * (1 + Real.log x)

end XiPrime
end Zeta23
