/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import KSatFreeCodeStatement
import Mathlib.Tactic

/-! # After Definition 6: «A k-CNF is also a (k+1)-CNF, so s_k ≤ s_{k+1}. Hence s_∞ = lim_{k→∞} s_k, and ETH is the same as s_3 > 0.»

The sentences are quoted from the paper; the statements are in KSatFreeCodeStatement.lean.
* `sameMachine`, `increasing`: «A k-CNF is also a (k+1)-CNF, so s_k ≤ s_{k+1}». A machine that
  decides (k+1)-SAT decides k-SAT in the same time, because the code does not depend on k; so the
  infimum for k is taken over more numbers δ.
* `henceForEverySequence`: the paper's «Hence», for every nondecreasing sequence in [0, ∞].
* `limitAndEth`: «Hence s_∞ = lim_{k→∞} s_k, and ETH is the same as s_3 > 0», from the two before.
* `supOneGivesPositive`, `sethGivesSomeK`: in the proof of Corollary 5, «s_∞ = 1 gives s_k > 0 for
  some k».
None of these proofs uses that the numbers s_k are 0. -/

public section

namespace SatFree

open scoped NNReal ENNReal

/-- «A k-CNF is also a (k+1)-CNF»: a machine that decides (k+1)-SAT decides k-SAT, in the same time. -/
theorem sameMachine : SameMachine := fun k _ _ h n φ hφ => h n φ ⟨fun C hC => (hφ.1 C hC).trans (Nat.le_succ k), hφ.2⟩

/-- «so s_k ≤ s_{k+1}.» -/
theorem increasing : Increasing := fun k =>
  le_iInf₂ fun δ hδ => iInf₂_le δ (by
    obtain ⟨M, c, hfin, h⟩ := hδ
    exact ⟨M, c, hfin, sameMachine k M _ h⟩)

/-- The paper's «Hence», for every nondecreasing sequence u in [0, ∞]: it tends to sup_{k≥3} u_k,
and u_k > 0 for all k ≥ 3 exactly if u_3 > 0. -/
theorem henceForEverySequence : HenceForEverySequence := fun u hu => by
  have hm : Monotone u := monotone_nat_of_le_succ hu
  have hs : (⨆ (k : ℕ) (_ : 3 ≤ k), u k) = ⨆ k : ℕ, u k :=
    le_antisymm (iSup₂_le fun k _ => le_iSup u k)
      (iSup_le fun k => (hm (le_max_left k 3)).trans (le_iSup₂ (f := fun (k : ℕ) (_ : 3 ≤ k) => u k) (max k 3) (le_max_right k 3)))
  refine ⟨?_, fun h => h 3 le_rfl, fun h k hk => h.trans_le (hm hk)⟩
  rw [hs]
  exact tendsto_atTop_iSup hm

/-- «Hence s_∞ = lim_{k→∞} s_k, and ETH is the same as s_3 > 0.» -/
theorem limitAndEth : LimitAndEth := henceForEverySequence s increasing

/-- For every sequence u in [0, ∞]: if sup_{k≥3} u_k = 1 then u_k > 0 for some k ≥ 3. -/
theorem supOneGivesPositive : SupOneGivesPositive := fun u h => by
  by_contra hc
  have h0 : (⨆ (k : ℕ) (_ : 3 ≤ k), u k) = 0 := by
    simp only [ENNReal.iSup_eq_zero]
    exact fun k hk => nonpos_iff_eq_zero.1 (not_lt.1 fun h' => hc ⟨k, hk, h'⟩)
  rw [h0] at h
  exact zero_ne_one h

/-- «s_∞ = 1 gives s_k > 0 for some k». -/
theorem sethGivesSomeK : SethGivesSomeK := fun h => supOneGivesPositive s h

end SatFree
