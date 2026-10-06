/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Spec.Sec3.Problems
public import ThreeSumApsp.Spec.Sec3.Theorem17.Chunks
public import ThreeSumApsp.Spec.Sec3.Theorem17.Parameters

/-!
# The number of chunks, on lists and on sets of pairs (proof of Theorem 17)

The routines work with lists of places: `classIdx` lists the places `a n + b` of the pairs of a
class, and the table `chunkTab` has one entry for each chunk.  The paper's class `W_ϱ` is a set of
pairs (`residueClass`).  The map `(a, b) ↦ a n + b` is a bijection between the set and the list, so
both have the same number of elements (`length_classIdx_eq_card`), and the table has as many entries
as there are chunks "in all" (`length_chunkTab_eq_totalChunks`).  The instance is
`triOf n AB BC AC`, whose weights `w(a,b)` are read from the list `AB`, row by row.
-/

public section

namespace ThreeSumApsp.Spec

variable (n : ℕ) {p : ℕ} (AB BC AC : List ℤ)

/-- The list of the places of a class has one entry for each pair of the class `W_ϱ`. -/
theorem length_classIdx_eq_card (hp : p ≠ 0) (ϱ : Fin p) :
    (classIdx n (residList p AB) ϱ).length = ((triOf n AB BC AC).residueClass p ϱ).card := by
  have hnodup : (classIdx n (residList p AB) ϱ).Nodup := List.nodup_range.filter _
  have hmem : ∀ q : Fin n × Fin n,
      pairIndex q ∈ (classIdx n (residList p AB) ϱ).toFinset ↔
        q ∈ (triOf n AB BC AC).residueClass p ϱ := fun q => by
    rw [List.mem_toFinset, mem_classIdx, getD_residList, TriangleInstance.residueClass,
      Finset.mem_filter, ← resid_eq_iff hp _ ϱ.isLt, and_iff_right (Finset.mem_univ q)]
    exact and_iff_right (Nat.mul_add_lt_mul q.1.isLt q.2.isLt)
  rw [← List.toFinset_card_of_nodup hnodup]
  refine (Finset.card_bij (fun q _ => pairIndex q) (fun q hq => (hmem q).2 hq)
    (fun q _ q' _ h => ?_) fun x hx => ?_).symm
  · obtain ⟨hrow, hcol⟩ := Nat.mul_add_inj_of_lt q.2.isLt q'.2.isLt h
    exact Prod.ext (Fin.ext hrow) (Fin.ext hcol)
  · obtain ⟨a, ha, b, hb, rfl⟩ :=
    Nat.exists_eq_mul_add_of_lt_mul (mem_classIdx.1 (List.mem_toFinset.1 hx)).1
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), (hmem _).1 hx, rfl⟩

/-- The table has one entry for each chunk. -/
theorem length_chunkTab_eq_totalChunks (hp : p ≠ 0) {D : ℕ} (hD : 1 ≤ D)
    (hcap : 1 ≤ queryCapNat n D) :
    (chunkTab n p (queryCapNat n D) (residList p AB)).length =
      (triOf n AB BC AC).totalChunks D p := by
  rw [length_chunkTab, List.sum_map_range, Finset.sum_range, TriangleInstance.totalChunks]
  refine Finset.sum_congr rfl fun ϱ _ => ?_
  rw [← queryCapNat_eq n hD, numChunks_eq _ hcap, ← length_classIdx_eq_card n AB BC AC hp ϱ]

end ThreeSumApsp.Spec
