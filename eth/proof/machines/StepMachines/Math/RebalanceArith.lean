/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Arithmetic for the size bound of the rebalancing. A network on g nodes, each with
at most 2^P states and P label bits, with U label bits over all ordered pairs and B-bit weights, is
merged into an
instance of the problem on K nodes with β ≤ 1 + U/K² + gP/K³ bits per edge. From this bound on β
follows β ≤ 3gP. The size bound takes
natural numbers with S' ≤ S + c₁(sc+P+B)^{c₁}, sc' ≤ c₁(sc+P) and Stot ≤ c₁(sc+P+B)^{c₁} + S' +
A(sc'+B'+β)^A to Stot ≤ S + A'(sc+P+B)^{A'}. -/

namespace Groundwork.RebalanceArith

/-- β ≤ 3gP. -/
public theorem beta_le {K g P U β : ℕ} (hK : 1 ≤ K) (hg : 1 ≤ g) (hP : 1 ≤ P) (hU : U ≤ g * P)
    (hβ : K ^ 3 * β ≤ K ^ 3 + K * U + g * P) : β ≤ 3 * (g * P) := by
  have hK3 : 1 ≤ K ^ 3 := Nat.one_le_pow _ _ hK
  have h1 : K * U ≤ K ^ 3 * U := Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) K)
  have h2 : g * P ≤ K ^ 3 * (g * P) := Nat.le_mul_of_pos_left _ hK3
  have h3 : K ^ 3 * β ≤ K ^ 3 * (1 + U + g * P) := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
    omega
  have h4 : β ≤ 1 + U + g * P := Nat.le_of_mul_le_mul_left h3 hK3
  have h5 : 1 ≤ g * P := Nat.mul_pos hg hP
  omega

/-- The sizes in the rebalancing. Here S, S', sc, sc' and Stot are natural numbers tied only by the
hypotheses: S' ≤ S + c₁(sc+P+B)^{c₁}, sc' ≤ c₁(sc+P) and Stot ≤ c₁(sc+P+B)^{c₁} + S' +
A(sc'+B'+β)^A. Then Stot exceeds S by at most a polynomial in sc + P + B. -/
public theorem size_le {K g : ℕ} (A c₁ d : ℕ) (hK : 2 ≤ K) (hKg : K ≤ g) :
    ∃ A' : ℕ, ∀ P B U β B' S S' sc sc' Stot : ℕ, 1 ≤ P → U ≤ g * P → K ^ 3 * β ≤ K ^ 3 + K * U + g * P →
      B' ≤ d * (P + B) → S' ≤ S + c₁ * (sc + P + B) ^ c₁ → sc' ≤ c₁ * (sc + P) →
      Stot ≤ c₁ * (sc + P + B) ^ c₁ + S' + A * (sc' + B' + β) ^ A → Stot ≤ S + A' * (sc + P + B) ^ A' := by
  refine ⟨2 * c₁ + A * (c₁ + (d + 3 * g)) ^ A + A, fun P B U β B' S S' sc sc' Stot hP hU hβ hB' hS' hsc' hS => ?_⟩
  obtain ⟨A', hA'⟩ : ∃ A' : ℕ, A' = 2 * c₁ + A * (c₁ + (d + 3 * g)) ^ A + A := ⟨_, rfl⟩
  rw [← hA']
  have hb := beta_le (by omega) (by omega) hP hU hβ
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = sc + P + B := ⟨_, rfl⟩
  rw [← hZ] at hS' hS ⊢
  have hZ1 : 1 ≤ Z := by omega
  have hbase : sc' + B' + β ≤ (c₁ + (d + 3 * g)) * Z := by
    have e1 : (c₁ + (d + 3 * g)) * Z =
        c₁ * (sc + P) + c₁ * B + d * (P + B) + 3 * (g * P) + 3 * (g * B) + (d + 3 * g) * sc := by
      rw [hZ]; ring
    omega
  have h1 : (sc' + B' + β) ^ A ≤ (c₁ + (d + 3 * g)) ^ A * Z ^ A' :=
    calc (sc' + B' + β) ^ A ≤ ((c₁ + (d + 3 * g)) * Z) ^ A := Nat.pow_le_pow_left hbase A
      _ = (c₁ + (d + 3 * g)) ^ A * Z ^ A := Nat.mul_pow ..
      _ ≤ (c₁ + (d + 3 * g)) ^ A * Z ^ A' := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hZ1 (by omega))
  have h2 : Z ^ c₁ ≤ Z ^ A' := Nat.pow_le_pow_right hZ1 (by omega)
  have h3 : A * (sc' + B' + β) ^ A ≤ A * (c₁ + (d + 3 * g)) ^ A * Z ^ A' := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ h1
  have h4 : c₁ * Z ^ c₁ ≤ c₁ * Z ^ A' := Nat.mul_le_mul_left _ h2
  have h5 : A' * Z ^ A' = 2 * (c₁ * Z ^ A') + A * (c₁ + (d + 3 * g)) ^ A * Z ^ A' + A * Z ^ A' := by rw [hA']; ring
  omega

end Groundwork.RebalanceArith
