/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Net.SizeP

/-! # Step 3, «The parameters», last sentence: the case m ≤ n̄

«If m ≤ n̄, the list is empty and there are only clauses: … every test costs at most one bit, so U ≤
2(k − 1)n̄ ≤ 2kn, and P = 2⌈n/g⌉(1 + Δ) and B = 1 will do.» With the empty list of checks no object
is an
incidence. So at most ⌈n/g⌉·Δ objects touch a node, W_a is 0, 1 or −1, and the number of all tests
is at most (k − 1)·m. -/

public section

namespace VariableBound.Net.SizeSmall

open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (qv occ)

variable {k g n Δ : ℕ}

/-- With the empty list of checks, at most ⌈n/g⌉·Δ objects touch a node, if g > 0, ψ is well formed
(`WfD`) and every variable occurs in at most Δ clauses. -/
theorem length_tch_le {ψ : Fml} (hg : 0 < g) (hW : WfD k n (ψ, [])) (hΔ : ∀ v, (occ ψ v).length ≤ Δ) (a : ℕ) : (tch g n (ψ, []) a).length ≤ qv g n * Δ := by
  have h := SizeP.length_tch_le (D := (ψ, [])) hg hW hΔ (c := 0) (fun e _ => by simp [colD]) a
  simpa using h

/-- With the empty list of checks, |W_a| ≤ 2^1 for every node, profile, flag and word: condition (ii)
with B = 1. (In fact W_a is 0, 1 or −1.) -/
theorem abs_WD_le (ψ : Fml) (y : ℕ) (fl : Bool) (a : ℕ) (z : List Bool) : |WD g n (ψ, []) y fl a z| ≤ 2 ^ 1 := by
  unfold WD
  split_ifs
  · cases fl <;> simp
  · simp

/-- With the empty list of checks, the number of all tests is at most (k − 1)·m, for ψ well formed
(`WfD`); as every test costs at most one bit, U ≤ 2(k − 1)·m. -/
theorem U_le {ψ : Fml} (hW : WfD k n (ψ, [])) (y : ℕ) (fl : Bool) : (netDN g (ctx g n (ψ, []) y fl)).U ≤ 2 * (k - 1) * ψ.length := by
  have h0 := Tests.sum_length_tst_le (g := g) hW 0
  have h1 := Tests.sum_length_tst_le (g := g) hW 1
  rw [Tests.card_kind_zero hW] at h0
  rw [Tests.card_kind_one hW] at h1
  simp only [List.map_nil, List.sum_nil, Nat.mul_zero, Nat.add_zero] at h0 h1
  have hc : ∀ a b, capD g n (ψ, []) y a b ≤ (tst g n (ψ, []) a b 0).length + (tst g n (ψ, []) a b 1).length := by
    intro a b
    rw [Tests.capD_eq, sum_range_succ, sum_range_succ, sum_range_zero, Nat.zero_add]
    exact Nat.add_le_add (SizeP.cw_le _ _) (SizeP.cw_le _ _)
  rw [Tests.U_eq, Nat.mul_assoc]
  refine Nat.mul_le_mul_left 2 ?_
  refine (sum_le_sum fun b _ => sum_le_sum fun a _ => hc a b).trans ?_
  simp only [sum_add_distrib]
  omega

/-- Step 3, «The parameters», the case m ≤ n̄ as printed: for g > 0, the empty list of checks, ψ
well formed (`WfD`) with at most n̄ clauses, every variable in at most Δ of them, and an admissible
profile y, the
network of y satisfies conditions (i) and (ii) of the definition of a network with P = 2⌈n/g⌉(1 + Δ)
and B = 1, and U ≤ 2(k − 1)n̄. That the profile is admissible is not used. -/
theorem stSmall : StSmall := by
  intro k g n Δ nb M ψ fl y hg hW hΔ hm _
  refine ⟨SizeP.sized_netDN (fun a _ => ?_) (fun a _ => ?_) fun a _ z => abs_WD_le ψ y fl a z, ?_⟩
  · have := length_tch_le hg hW hΔ a
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · have := length_tch_le hg hW hΔ a
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · exact (U_le hW y fl).trans (Nat.mul_le_mul_left _ hm)

end VariableBound.Net.SizeSmall
