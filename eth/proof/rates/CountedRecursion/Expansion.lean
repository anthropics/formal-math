/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.PatternPsi
public import Printed.Coding
public import ClauseBound.Gen.RateAux
import Mathlib.Tactic

/-! # The expansion over the patterns

Proof of Theorem A (b), the step from ℓ to ℓ + 1: d^{|ℛ|}Z = Σ_ι Z_ι over the |𝓘|^{|ℛ|} ≤ Ξ^{cg⁴/4}
functions ι : ℛ → 𝓘, and each Z_ι is the value of the row network and of the column network.
* `expansion : Expansion`: by `Printed.stCliqueValue` (the clique of Definition 3 has the value of
  the plain picture, one string for each edge), `ClauseBound.Alg.GridNet.ZW_mul_eq_sum` (clause (a)
  of Definition 7 at every rectangle of the grid) and `ClauseBound.Alg.GridNet.value_gridN` (either
  network has the value of the term).
* `patternsFew : PatternsFew`: |ℛ| ≤ g⁴/4, |𝓘| ≤ (2λ)^c and 2λ ≤ Ξ. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-- **d^{|ℛ|}Z = Σ_ι Z_ι over the |𝓘|^{|ℛ|} functions ι : ℛ → 𝓘, and each Z_ι is the value of the
row network and of the column network.** -/
theorem expansion : Expansion := by
  intro ρ c x₀ D hS g lam W tr hg hlam
  have hC := cutsOK_piecesOf hS hlam [()]
  have hpos := card_I_pos hS.is hlam
  have hK : 2 ≤ g * g := by nlinarith
  have hA : ∀ x y u v, ∑ i ∈ range (#(D.fam lam).I - 1 + 1), (D.fam lam).A (indexAt D lam i) x y u v = (D.fam lam).d * Pieces.cross x y u v := by
    intro x y u v
    rw [Nat.sub_add_cancel hpos, sum_indexAt D lam fun i => (D.fam lam).A i x y u v, hS.is.sum lam hlam]
  have h := ZW_mul_eq_sum g g lam (listTables (g * g) W) (fun j => (D.fam lam).A (indexAt D lam j)) (#(D.fam lam).I - 1) (D.fam lam).d hA
  rw [Nat.sub_add_cancel hpos] at h
  rw [stCliqueValue (g * g) lam W hK hlam]
  refine h.trans (Finset.sum_congr rfl fun y _ => ?_)
  exact (value_gridN hC g g (tr y) y _).symm

/-- **There are |𝓘|^{|ℛ|} ≤ Ξ^{cg⁴/4} functions ι**: the inequality, raised to the fourth power; and |ℛ|
≤ g⁴/4. -/
theorem patternsFew : PatternsFew := by
  intro ρ c x₀ D hS g lam B hg hlam hB
  have h4 := ClauseBound.Gen.Rate.four_nRect_le g
  refine ⟨h4, ?_⟩
  have hX : 2 * lam ≤ Xi g lam B := by
    unfold Xi
    have h1 : 4 ≤ g ^ 2 := by nlinarith
    nlinarith
  calc (#(D.fam lam).I ^ nRectG g g) ^ 4 = #(D.fam lam).I ^ (4 * nRectG g g) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ ((2 * lam) ^ c) ^ (4 * nRectG g g) := Nat.pow_le_pow_left (hS.is.card lam hlam) _
    _ ≤ ((2 * lam) ^ c) ^ (g ^ 4) := Nat.pow_le_pow_right (Nat.pow_pos (by omega)) h4
    _ = (2 * lam) ^ (c * g ^ 4) := by rw [← pow_mul]
    _ ≤ Xi g lam B ^ (c * g ^ 4) := Nat.pow_le_pow_left hX _

end ExplicitCost
