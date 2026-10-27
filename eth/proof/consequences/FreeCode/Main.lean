/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import KSatFreeCodeStatement
public import FreeCode.Defs
import FreeCode.Reader
import FreeCode.Order
import FreeCode.Random
import FreeCode.Behind
import FreeCode.Brute
import FreeCode.Tied
import ToTuring.Machine.EndTM
import Mathlib.Tactic

/-! # The sentences of KSatFreeCodeStatement.lean that rest on machines

After Definition 6: «Trying all assignments gives s_k ≤ 1, so s_∞ ≤ 1.» Corollary 5: «s_k = 0 for
every k ≥ 3. Hence s_∞ = 0, and both ETH and SETH are false.» After Definition 6, on randomized
algorithms: «and Corollary 5 holds under each of these conventions.»
* `codeReadable`: from the reader `FreeCode.readFree`, which returns n and the formula on the code
  followed by any bits.
* `bruteForce`, `atMostOne`: from `FreeCode.stBrute`. c·(n+2)^c·2^n is at most C·2^{(1+ε)n} for
  every ε > 0, so s_k ≤ 1 + ε.
* `FreeCode.allZeroFrom`, `allZero`: Corollary 5, first with the two tied statements as hypotheses,
  then applied to their proofs: s_3 = 0 from `FreeCode.StTiedThree` (Theorem 2), s_k = 0 for k > 3
  from `FreeCode.StTied` (the reduction).
* `allZeroRandomized`: from `randomnessHelps` and `allZero`.
The other sentences are in proof/consequences/FreeCode/Order.lean and Random.lean. -/

public section

namespace SatFree

open Groundwork FreeCode
open scoped NNReal ENNReal

/-- A formula is determined by the same formula with numbers as variables. -/
theorem toN_injective {n : ℕ} : Function.Injective (Decode.toN (n := n)) := by
  unfold Decode.toN
  refine List.map_injective_iff.2 (List.map_injective_iff.2 fun a b e => ?_)
  exact Prod.ext (Fin.ext (Prod.mk.inj e).1) (Prod.mk.inj e).2

/-- The code determines the number of variables and the formula, and it tells where it ends:
whatever bits follow it can be read off. -/
theorem codeReadable : CodeReadable := by
  refine ⟨fun n n' φ ψ u v h => ?_, fun n φ ψ u v h => ?_⟩
  · have h1 := readFree_enc_append φ u
    rw [h, readFree_enc_append ψ v] at h1
    have h2 := congrArg (fun p : List Unit × Prog.Fml => p.1.length) h1
    simpa using h2.symm
  · have h1 := readFree_enc_append φ u
    rw [h, readFree_enc_append ψ v] at h1
    have h3 : φ = ψ := toN_injective (congrArg Prod.snd h1).symm
    subst h3
    exact ⟨rfl, List.append_cancel_left h⟩

/-- «Trying all assignments»: one machine decides k-SAT for every k, within c·(n+2)^c·2^n steps,
with c depending on k. -/
theorem bruteForce : BruteForce := by
  obtain ⟨_, M, _, -, -, hfin, -, -, -, h⟩ := stBrute
  exact ⟨M, hfin, h⟩

/-- By exhaustive search, k-SAT is in time O(2^{(1+ε)n}) for every ε > 0. -/
theorem inTime_one_add (k : ℕ) {ε : ℝ≥0} (hε : 0 < ε) : InTime k (1 + ε) := by
  obtain ⟨M, hfin, h⟩ := bruteForce
  obtain ⟨c, hc⟩ := h k
  obtain ⟨C₁, hC₁⟩ := exists_pow_le c (ε := (ε : ℝ)) hε
  refine ⟨M, c * C₁, hfin, decidesTM_mono (fun n => Nat.le_floor ?_) hc⟩
  have h1 : (2 : ℝ) ^ (((1 + ε : ℝ≥0) : ℝ) * n) = (2 : ℝ) ^ ((ε : ℝ) * n) * (2 : ℝ) ^ n := by
    rw [← Real.rpow_natCast 2 n, ← Real.rpow_add two_pos]
    congr 1
    push_cast
    ring
  rw [h1]
  push_cast
  calc (c : ℝ) * ((n : ℝ) + 2) ^ c * (2 : ℝ) ^ n ≤ (c : ℝ) * (C₁ * (2 : ℝ) ^ ((ε : ℝ) * n)) * (2 : ℝ) ^ n := by
        have := hC₁ n
        gcongr
    _ = (c : ℝ) * C₁ * ((2 : ℝ) ^ ((ε : ℝ) * n) * (2 : ℝ) ^ n) := by ring

/-- «Trying all assignments gives s_k ≤ 1, so s_∞ ≤ 1.» -/
theorem atMostOne : AtMostOne := by
  have h : ∀ k : ℕ, s k ≤ 1 := fun k => by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    calc s k ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) := iInf₂_le (1 + ε) (inTime_one_add k hε)
      _ = 1 + (ε : ℝ≥0∞) := by simp
  exact ⟨h, iSup₂_le fun k _ => h k⟩

/-- If k-SAT is in time O(2^{δn}) for every δ > 0, then s_k = 0. -/
theorem s_eq_zero_of {k : ℕ} (h : ∀ δ : ℝ≥0, 0 < δ → InTime k δ) : s k = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  exact iInf₂_le ε (h ε hε)

end SatFree

namespace FreeCode

open SatFree
open scoped NNReal ENNReal

/-- **Corollary 5 from the two tied statements**, which are hypotheses here: «s_k = 0 for every k ≥ 3.
Hence s_∞ = 0, and both ETH and SETH are false», for the numbers s_k defined with the code that does
not depend on k. At k = 3 the Turing machine is that of `StTiedThree` («Theorem 2 gives s_3 = 0»),
at k > 3 that of `StTied` (the reduction); then the general `SatFree.s_eq_zero_of`. Nothing else is
known of the machines. -/
theorem allZeroFrom : StTiedThree → StTied → SatFree.AllZero := fun hT3 hT => by
  -- «s_k = 0 for every k ≥ 3»
  have hs : ∀ k : ℕ, 3 ≤ k → s k = 0 := fun k hk => s_eq_zero_of fun δ hδ => by
    rcases Nat.eq_or_lt_of_le hk with rfl | -
    · obtain ⟨_, _, _, M, c, _, -, -, hfin, -, -, -, h⟩ := hT3 (δ : ℝ) hδ
      exact ⟨M, c, hfin, h⟩
    · obtain ⟨_, _, _, _, M, c, _, -, -, hfin, -, -, -, h⟩ := hT k hk (δ : ℝ) hδ
      exact ⟨M, c, hfin, h⟩
  -- «Hence s_∞ = 0»: s_∞ is the supremum of the s_k, k ≥ 3.
  have hInf : sInfty = 0 := by
    unfold sInfty
    simp only [ENNReal.iSup_eq_zero]
    exact hs
  refine ⟨hs, hInf, fun h => ?_, fun h => ?_⟩
  · -- «Theorem 2 gives s_3 = 0, which is the negation of ETH»
    have := h 3 le_rfl
    rw [hs 3 le_rfl] at this
    exact lt_irrefl _ this
  · -- SETH is the statement s_∞ = 1, and 0 ≠ 1.
    have h' : sInfty = 1 := h
    rw [hInf] at h'
    exact zero_ne_one h'

end FreeCode

namespace SatFree

open Groundwork FreeCode
open scoped NNReal ENNReal

/-- **Corollary 5**: «s_k = 0 for every k ≥ 3. Hence s_∞ = 0, and both ETH and SETH are false», for
the numbers s_k defined with the code that does not depend on k. It is `FreeCode.allZeroFrom`
applied to `FreeCode.stTiedThree` (Theorem 2) and `FreeCode.stTied` (the reduction). -/
theorem allZero : AllZero := FreeCode.allZeroFrom stTiedThree stTied

/-- «and Corollary 5 holds under each of these conventions»: with randomized algorithms with error
at most p, for every p ≥ 0, s_k = 0 for every k ≥ 3. -/
theorem allZeroRandomized : AllZeroRandomized := fun p hp k hk =>
  le_antisymm ((randomnessHelps p hp k).trans (le_of_eq (allZero.1 k hk))) bot_le

end SatFree
