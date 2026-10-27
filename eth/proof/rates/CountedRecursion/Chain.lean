/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.ChainLabel
public import CountedRecursion.CrudeBounds
public import ClauseBound.Gen.PartA
public import CountedRecursion.PartAPrinted
import Mathlib.Tactic

/-! # The chain: from one depth to the next
With X_j = K_j(Λ_j + 𝔅_j): X_j ≤ X_{j+1}^{c+5} (`chainBase`: the last of the crude bounds in the
proof of Theorem A(b), «K(L + B') ≤ Ξ^{c+5}», at the bounds for λ and B),
and the exponents of 2 (`chainExponent`): the bound for K_j²Λ_j of `chainLabel`, multiplied by e_j ∈
[0, 1], with e_{j+1} = (ρ + 3ζ_j)e_j + 3/K_j and K_{j+1}² = g_j⁴. -/

public section

namespace ExplicitCost

open Levels.Gen Printed

/-- X_{j+1} is the Ξ of the callers of the depth j + 1. -/
theorem baseAt_succ (ρ : ℝ) (c x₀ l lam B j : ℕ) : baseAt ρ c x₀ l lam B (j + 1) = xiAt ρ c x₀ l lam B j := rfl

/-- `ChainBaseFrom`. -/
theorem chainBaseFrom : ChainBaseFrom := by
  intro hL hC ρ c x₀ l lam B j hN hj
  obtain ⟨-, -, h3, -⟩ := hL ρ c x₀ l lam B j hN hj
  have h := (hC c x₀ j (lamAt ρ c x₀ l lam B (j + 1)) (bitsAt ρ c x₀ l lam B (j + 1)) (lamAt ρ c x₀ l lam B j) hN.x₀_ge (one_le_lamAt hN (by omega)) (one_le_bitsAt hN (by omega)) h3).2.2
  rw [← bitsAt_of_lt ρ c x₀ lam B hj] at h
  exact h

/-- `ChainBase`. -/
theorem chainBase : ChainBase := chainBaseFrom chainLabel crudeBounds

/-- The arithmetic of `ChainExponent`. -/
theorem exponent_real {e0 r G4 Λ cc lg k2 kk x : ℝ} (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) (hkk : 0 < kk) (hcl : 0 ≤ cc / 4 * G4 * lg) (hk2 : 0 ≤ k2) (h : x ≤ r * (G4 * Λ) + cc / 4 * G4 * lg + k2) :
    e0 * x + 3 * (G4 * Λ) / kk ≤ (r * e0 + 3 / kk) * G4 * Λ + cc / 4 * G4 * lg + k2 := by
  have h1 := mul_le_mul_of_nonneg_left h he0
  have h2 : e0 * (cc / 4 * G4 * lg) ≤ cc / 4 * G4 * lg := by nlinarith
  have h3 : e0 * k2 ≤ k2 := by nlinarith
  have e : (r * e0 + 3 / kk) * G4 * Λ = e0 * (r * (G4 * Λ)) + 3 * (G4 * Λ) / kk := by
    field_simp
  rw [e]
  nlinarith

/-- `ChainExponentFrom`. -/
theorem chainExponentFrom : ChainExponentFrom := by
  intro hL hA ρ c x₀ l lam B j hN hj
  obtain ⟨-, -, -, h4⟩ := hL ρ c x₀ l lam B j hN hj
  have he0 : 0 ≤ e ρ x₀ j := le_trans (by have := hN.rho_ge; positivity) (hA.e_ge ρ x₀ j hN.rho_ge hN.rho_lt hN.x₀_ge)
  have he1 : e ρ x₀ j ≤ 1 := by
    have h1 := hA.e_le ρ x₀ j hN.rho_ge hN.rho_lt hN.x₀_ge
    have h2 : ρ ^ j ≤ 1 := pow_le_one₀ (by linarith [hN.rho_ge]) hN.rho_lt.le
    linarith
  have hK : (0 : ℝ) < K x₀ j := by exact_mod_cast K_pos x₀ j
  have hlg := GeneralPieces.DefGenPieces.logb_nonneg (one_le_lamAt hN (by omega : j + 1 ≤ l))
  have eK : (K x₀ (j + 1) : ℝ) ^ 2 = (g x₀ j : ℝ) ^ 4 := by exact_mod_cast K_succ_sq x₀ j
  have h := exponent_real (kk := K x₀ j) he0 he1 hK (by positivity) (by positivity) h4
  rw [eK]
  have ee : e ρ x₀ (j + 1) = (ρ + 3 * zeta j) * e ρ x₀ j + 3 / K x₀ j := rfl
  rw [ee]
  linarith

/-- `ChainExponent`. -/
theorem chainExponent : ChainExponent := chainExponentFrom chainLabel partAPrinted

end ExplicitCost
