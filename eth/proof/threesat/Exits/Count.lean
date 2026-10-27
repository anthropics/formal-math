/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Exits.AlgDefs
import Exits.Level
import Eight.ViaGrouping.Count
import ToTuring.Poly.Comb
import Mathlib.Tactic.Positivity

/-! # Procedure Count with line 6, and «Cost» for it

Algorithm 1, line 6: «if m = 0 then return 1». Proof of Theorem 2: «If m = 0 the number is 2^n; let
m ≥ 1.» … «So, with the preparation, Z is computed in time O(2^{δ'm}) plus a polynomial in n».
* `stCountNil`: on the formula without clauses Count returns 1 in one step, at every level.
* `COUNT_polyTimeSteps`: the steps of Count take polynomial time, if those of the algorithm for
  networks and of Clique(ℓ) do.
* `stCountCostOf`: «Cost» for Count, from Lemma 1 for Network(ℓ), the polynomial-time steps of the
  algorithm of Lemma 1, and the bound for Clique(ℓ). For m = 0: one step, and the number of
  satisfying assignments of the formula without clauses is 1 (`Eight.numSat_nil`). For m ≥ 1: the
  paragraph «Cost», which is generic in the algorithm for networks
  (`Eight.ViaGrouping.count_cost_of`, proof/networks/Eight/ViaGrouping/Count.lean). The test of line
  6 costs no step of its own and one unit of size.
`COUNT_polyTimeSteps` is a step inside the proof of `stCountCostOf`, not a statement of
AlgDefs.lean. -/

public section

namespace Exits

open Groundwork Groundwork.Prog Groundwork.Stepped Paper Eight Eight.SecNetworks Eight.ViaGrouping

/-- **Line 6 of Algorithm 1**: «if m = 0 then return 1». On the formula without clauses Count
returns 1 in one step, at every level. -/
theorem stCountNil : StCountNil := fun _ => ⟨_, ite_runs_true rfl (const_runs (1 : ℤ) ([] : Formula))⟩

/-- The steps of Count, at the level ℓ, take polynomial time, if the algorithm for networks keeps
polynomial-time steps and Clique(ℓ) has them. (Section 6: «Z is computed in time O(2^{δ'm}) plus a
polynomial in n». The bound on the number of steps bounds the time only together with this.) -/
theorem COUNT_polyTimeSteps (hKp : StKeeps) (hC : StClique) (ℓ : ℕ) : PolyTimeSteps (COUNT ℓ) := by
  obtain ⟨h⟩ : Nonempty (IsPolyT ((NETWORK ℓ).app (satProcs (levelG ℓ) 3))) := count_isPolyT (hKp (levelK ℓ) (levelG ℓ) (CLIQUE ℓ) (hC ℓ).1) (levelG ℓ) 3
  have := IsPolyT.const (α := Formula) (1 : ℤ)
  exact ⟨IsPolyT.ite (by fun_prop)⟩

/-- **Section 6, «Cost», for Count**: «So, with the preparation, Z is computed in time O(2^{δ'm})
plus a polynomial in n». From Lemma 1 for Network(ℓ), the polynomial-time steps of the algorithm of
Lemma 1, and the bound for Clique(ℓ). -/
theorem stCountCostOf : StCountCostOf := by
  intro hL hKp hC δ' ℓ hδ' h1 hK hE
  refine ⟨COUNT_polyTimeSteps hKp hC ℓ, ?_⟩
  obtain ⟨A₀, hA₀⟩ := ViaGrouping.count_cost_of hδ' h1 (zero_lt_levelG ℓ) hK
    (hL (levelK ℓ) (δ' / 12) (CLIQUE ℓ) (two_le_levelK ℓ) (by positivity) ((hC ℓ).2.mono hE))
  have hA : (A₀ : ℝ) ≤ ((A₀ + 5 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right A₀ 5
  refine ⟨A₀ + 5, fun Φ hΦ => ?_⟩
  cases hemp : Φ.isEmpty with
  | true =>
    -- «if m = 0 then return 1»
    obtain rfl : Φ = [] := List.isEmpty_iff.1 hemp
    have s0 : size ([] : Formula) = 1 := rfl
    have s1 : size (1 : ℤ) ≤ 2 := by
      rw [size_int]
      exact Nat.succ_le_succ (Nat.size_le.2 (by norm_num))
    have h5 : (1 : ℝ) ≤ ((A₀ + 5 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ A₀ + 5)
    refine ⟨1, ?_, ?_⟩
    · rw [numSat_nil, Nat.cast_one]
      refine (ite_runs_true rfl (const_runs (1 : ℤ) ([] : Formula))).mono le_rfl ?_
      rw [s0, one_pow, mul_one]
      omega
    · rw [List.length_nil, Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one, Nat.cast_one]
      exact h5
  | false =>
    -- «let m ≥ 1»: line 8
    obtain ⟨T, hrun, hT⟩ := hA₀ Φ hΦ
    have hs1 : 1 ≤ size Φ := by rw [size_list]; omega
    have h2 : size Φ ^ A₀ ≤ size Φ ^ (A₀ + 5) := Nat.pow_le_pow_right hs1 (by omega)
    have h3 : 1 ≤ size Φ ^ (A₀ + 5) := Nat.one_le_pow _ _ hs1
    refine ⟨T, (ite_runs_false hemp hrun).mono le_rfl ?_, hT.trans (mul_le_mul_of_nonneg_right hA (by positivity))⟩
    calc A₀ * size Φ ^ A₀ + 1 ≤ A₀ * size Φ ^ (A₀ + 5) + 5 * size Φ ^ (A₀ + 5) := Nat.add_le_add (Nat.mul_le_mul_left _ h2) (by omega)
      _ = (A₀ + 5) * size Φ ^ (A₀ + 5) := (Nat.add_mul _ _ _).symm

end Exits
