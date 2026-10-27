/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Coding.Occ
public import Coding.Padding
import all StepMachines.Prog.CountNet
import Eight.ViaGrouping.SatPsi
import Eight.SecProof_Network

/-! # The printed network of Φ: Definition 2, small values, the count

For `Coding.occNet g Φ`, the network of Section 6, with one bit per occurrence:
* `stOccNetIs`: «The network of Φ is the following network on [g] with P = 6m̄ and B = 1 …
  Definition 2 holds: Σ_{b ≠ a} c_{a,b} ≤ 2·3m̄ = P», except condition (iii) of Definition 2, which
  `Net.Is` does not contain. The bound on the row sums is taken from the padded network `wordNet`,
  which has the same numbers c_{a,b} (`capF_eq`).
* `stOccNetSmall`: «Their length is at most 3m̄ ≤ P», «all values are 0 or 1».
* `stOccNetCountsOf`, `stOccNetCounts`: «Hence Z is the number of assignments of the variables
  occurring in Φ that satisfy Φ», so Φ is satisfiable if and only if Z > 0, carried over from the
  padded network of Φ, whose value `Eight.network_value_eq` gives, since padding does not change the
  value.
* `stRowSumReached`: the footnote «P is taken as large as 6m̄ because Σ_{b ≠ a} c_{a,b} can reach
  6m̄». `import all StepMachines.Prog.CountNet` gives access to `boole_congr`, which is not public. -/

public section

namespace Coding

open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping

variable {g : ℕ} {Φ : Fml}

/-- There are at most 3 occurrences for each clause. -/
theorem length_occIn_le (h3 : ∀ C ∈ Φ, C.length ≤ 3) (e₀ r : ℕ) : (occIn Φ e₀ r).length ≤ 3 * r := by
  induction r generalizing e₀ with
  | zero => simp [occIn]
  | succ r ih =>
    have e : occIn Φ e₀ (r + 1) = ((List.range (Φ.getD e₀ []).length).map fun j => (e₀, j)) ++ occIn Φ (e₀ + 1) r := by
      simp only [occIn, List.range'_succ, List.flatMap_cons]
    have h1 := length_getD_le h3 e₀
    have h2 := ih (e₀ + 1)
    rw [e, List.length_append, List.length_map, List.length_range]
    omega

/-- [p] is 0 or 1. -/
theorem boole_zero_or_one (p : Prop) [Decidable p] : (if p then (1 : ℤ) else 0) = 0 ∨ (if p then (1 : ℤ) else 0) = 1 := by split_ifs <;> simp

/-- |[p]| < 2^B with B = 1, as condition (ii) of Definition 2 asks. -/
theorem abs_boole_lt (p : Prop) [Decidable p] : |if p then (1 : ℤ) else 0| < 2 ^ 1 := by split_ifs <;> norm_num

/-- «Their length is at most 3m̄ ≤ P» and «all values are 0 or 1» (Section 6). -/
theorem stOccNetSmall : StOccNetSmall := by
  intro g Φ h3
  exact ⟨fun a => length_occIn_le h3 _ _, fun _ _ => boole_zero_or_one _, fun _ _ _ _ => boole_zero_or_one _, fun _ _ _ _ => boole_zero_or_one _⟩

/-- «The network of Φ is the following network on [g] with P = 6m̄ and B = 1 … Definition 2 holds:
Σ_{b ≠ a} c_{a,b} ≤ 2·3m̄ = P» (Section 6): the printed network satisfies Definition 2 except
condition (iii), with P = 6m̄ and B = 1, for m ≥ 1. -/
theorem stOccNetIs : StOccNetIs := by
  intro g Φ hg hΦ h3
  have hμ : 0 < mu g Φ := by
    have h1 := le_mul_mu hg Φ
    have h2 : 0 < Φ.length := List.length_pos_iff.2 hΦ
    rcases Nat.eq_zero_or_pos (mu g Φ) with h | h
    · rw [h, Nat.mul_zero] at h1
      omega
    · exact h
  refine ⟨by omega, le_rfl, fun a z hz => mem_words.1 hz, fun a => ?_, fun a b _ z _ z' _ => boole_congr eq_comm, fun a b => congrArg List.length (testsBetween_comm a.val b.val), fun a b _ z _ z' _ => ?_, fun a => ?_,
    fun _ _ _ => abs_boole_lt _, fun _ _ _ _ _ _ _ => abs_boole_lt _, fun _ _ _ _ _ _ _ => abs_boole_lt _⟩
  · have := length_occIn_le h3 (a.val * mu g Φ) (mu g Φ)
    change (occIn Φ (a.val * mu g Φ) (mu g Φ)).length ≤ 6 * mu g Φ
    omega
  · change (if restrict g Φ a.val b.val z = restrict g Φ b.val a.val z' then (1 : ℤ) else 0)
      = ∑ θ ∈ words (testsBetween g Φ a.val b.val).length, (if restrict g Φ a.val b.val z = θ then (1 : ℤ) else 0) * (if restrict g Φ b.val a.val z' = θ then 1 else 0)
    rw [Finset.sum_eq_single (restrict g Φ a.val b.val z)]
    · rw [if_pos rfl, one_mul]
      exact boole_congr eq_comm
    · intro θ _ hne
      rw [if_neg (Ne.symm hne), zero_mul]
    · intro h
      exact absurd (mem_words.2 (List.length_map _)) h
  · have h := (sized_wordNet (k := 3) (φ := Φ) hg 0).sum_c a
    have e : ∑ b ∈ univ.erase a, (occNet g Φ).c a b = ∑ b ∈ univ.erase a, (wordNet g 3 Φ).c a b := Finset.sum_congr rfl fun b _ => (capF_eq hg h3 a.val b.val).symm
    rw [e]
    omega

/-- **«Hence Z is the number of assignments of the variables occurring in Φ that satisfy Φ», so Φ is
satisfiable if and only if Z > 0** (Section 6), for the printed network, from its two hypotheses:
the padded network of Φ is the printed one with padding (`StOccNet`), and padding does not change
the value (`StPaddingValue`). -/
theorem stOccNetCountsOf : StOccNetCountsOf := by
  intro HO HP g Φ hg h3
  have hv : (occNet g Φ).value = (Eight.numSat Φ : ℤ) := by
    rw [← (HP g _ _ _ (HO g Φ hg h3)).1, (satNet_isNetworkP hg 3 Φ).2.1]
    exact Eight.network_value_eq hg Φ h3
  refine ⟨hv, ?_⟩
  rw [hv, Nat.cast_pos]
  exact Eight.numSat_pos_iff Φ

/-- **«Hence Z is the number of assignments of the variables occurring in Φ that satisfy Φ», so Φ is
satisfiable if and only if Z > 0** (Section 6), for the printed network. -/
theorem stOccNetCounts : StOccNetCounts := stOccNetCountsOf stOccNet stPaddingValue

/-- «P is taken as large as 6m̄ because Σ_{b ≠ a} c_{a,b} can reach 6m̄» (Section 6, footnote):
three clauses on three variables, one clause in each cluster; the middle cluster has three tests to
each of the other two. -/
theorem stRowSumReached : StRowSumReached := by
  have hmu : mu 3 sixExample = 1 := by decide
  have h0 : (testsBetween 3 sixExample 1 0).length = 3 := by decide
  have h2 : (testsBetween 3 sixExample 1 2).length = 3 := by decide
  have hs : univ.erase (1 : Fin 3) = {0, 2} := by decide
  have h3 : ∀ C ∈ sixExample, C.length ≤ 3 := by decide
  refine ⟨hmu, ?_, ?_⟩
  · rw [hs, Finset.sum_pair (by decide), hmu]
    change (testsBetween 3 sixExample 1 0).length + (testsBetween 3 sixExample 1 2).length = 6 * 1
    rw [h0, h2]
  · rw [hs, Finset.sum_pair (by decide), hmu]
    change capF 3 3 sixExample 1 0 + capF 3 3 sixExample 1 2 = 6 * 1
    rw [capF_eq (by norm_num) h3, capF_eq (by norm_num) h3, h0, h2]

end Coding
