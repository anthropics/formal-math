/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSatRate.Interfaces

/-! # The formula of a leaf as `countM` gets it

`PaddedDescent.F.StCountM` (proof/rates/PaddedDescent/F/Interfaces.lean) asks of a formula that no
clause is empty and that every variable occurs in a bounded number of clauses. The side list of a
node of the counting tree (proof/consequences/CountKSat/Defs.lean), the set 𝒩 of Appendix C, gets
the clauses {¬ω} for the literals ω of the chosen set H at every step to the second recursive call.
Nothing proved in this development excludes that the same literal comes again and again, so
there is no such bound for the side list as it stands.
`leafM x` (proof/consequences/CountKSatRate/Defs.lean) keeps of the side list only the clauses of
one literal, each of them once. This file proves `spec`: at a leaf, as `StTreeK` describes it,
`leafM x` has at most as many clauses as `leafF x`, its clauses have 1 to k literals on variables
below n, every variable occurs in at most c + 2 of them if it occurs in at most c clauses of the
main list x.1, and it has
as many satisfying assignments on n variables as `leafF x`. -/

namespace CountKSatRate.Leaf

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F
open PaddedDescent.F.Mark (occ nSat WfL)

/-- The clauses of `sideU X` are the clauses of X of one literal. -/
theorem mem_sideU {X : PFml} {C : PCl} : C ∈ sideU X ↔ C ∈ X ∧ C.length = 1 := by
  simp [sideU, List.mem_dedup, List.mem_filter]

/-- `sideU X` is not longer than X. -/
theorem length_sideU_le (X : PFml) : (sideU X).length ≤ X.length :=
  (List.dedup_sublist _).length_le.trans (List.length_filter_le _ _)

/-- A variable occurs in at most two clauses of `sideU X`: the clause v and the clause ¬v. -/
theorem length_occ_sideU_le (X : PFml) (v : ℕ) : (occ (sideU X) v).length ≤ 2 := by
  have hnd : (occ (sideU X) v).Nodup := (List.nodup_dedup _).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  refine (Finset.card_le_card (t := {[(v, true)], [(v, false)]}) ?_).trans Finset.card_le_two
  intro C hC
  rw [List.mem_toFinset, occ, List.mem_filter, mem_sideU] at hC
  obtain ⟨⟨-, h1⟩, h2⟩ := hC
  obtain ⟨⟨a, b⟩, rfl⟩ := List.length_eq_one_iff.1 h1
  obtain rfl : a = v := by simpa using h2
  cases b <;> simp

/-- An assignment satisfies `leafM x` exactly if it satisfies `leafF x`: the clauses left out are of
the form xᵢ ∨ ¬xᵢ. -/
theorem sat_leafM_iff {n : ℕ} {x : CNode} (hs : ∀ C ∈ x.2, C ∈ taut n ∨ ∃ l, C = [l]) (a : ℕ → Bool) :
    (∀ C ∈ leafM x, ∃ l ∈ C, a l.1 = l.2) ↔ ∀ C ∈ leafF x, ∃ l ∈ C, a l.1 = l.2 := by
  constructor
  · intro h C hC
    rcases List.mem_append.1 hC with hC | hC
    · rcases hs C hC with ht | ⟨l, rfl⟩
      · obtain ⟨i, -, rfl⟩ := List.mem_map.1 ht
        cases hi : a i
        · exact ⟨(i, false), by simp, hi⟩
        · exact ⟨(i, true), by simp, hi⟩
      · exact h _ (List.mem_append_left _ (mem_sideU.2 ⟨hC, rfl⟩))
    · exact h C (List.mem_append_right _ hC)
  · intro h C hC
    rcases List.mem_append.1 hC with hC | hC
    · exact h C (List.mem_append_left _ (mem_sideU.1 hC).1)
    · exact h C (List.mem_append_right _ hC)

/-- What `PaddedDescent.F.StCountM` asks of a formula holds of `leafM x`, and its count is that of
`leafF x`. The hypotheses are what `StTreeK` says of a leaf. -/
public theorem spec {k n c : ℕ} {x : CNode} (hk : 1 ≤ k) (h1 : ∀ C ∈ x.1, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n)
    (ho : ∀ v, (occ x.1 v).length ≤ c) (hs : ∀ C ∈ x.2, (C ∈ taut n ∨ ∃ l, C = [l]) ∧ ∀ l ∈ C, l.1 < n) :
    (leafM x).length ≤ (leafF x).length ∧ WfL k n [leafM x] ∧ (∀ v, (occ (leafM x) v).length ≤ c + 2) ∧ nSat n (leafM x) = cntN n (leafF x) := by
  refine ⟨?_, ?_, fun v => ?_, ?_⟩
  · rw [leafM, leafF, List.length_append, List.length_append]
    exact Nat.add_le_add_right (length_sideU_le x.2) _
  · intro y hy C hC
    rw [List.mem_singleton.1 hy] at hC
    rcases List.mem_append.1 hC with hC | hC
    · obtain ⟨h2, h3⟩ := mem_sideU.1 hC
      exact ⟨fun e => by simp [e] at h3, h3 ▸ hk, (hs C h2).2⟩
    · exact h1 C hC
  · rw [leafM, occ, List.filter_append, List.length_append]
    have h1 := length_occ_sideU_le x.2 v
    have h2 := ho v
    rw [occ] at h1 h2
    omega
  · unfold nSat cntN
    congr 1
    exact Finset.filter_congr fun σ _ => sat_leafM_iff (fun C hC => (hs C hC).1) _

end CountKSatRate.Leaf
