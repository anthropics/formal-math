/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.InstanceFacts
public import ThreeSumApsp.Sec3.Theorem17.Witnesses

/-!
# The host of Theorem 17: failed scans and false positives

Proof of Theorem 17: "distinct scans contain distinct false positives, so there are at most F(p)
failed scans" (`HostData.sum_fails_le`).  An accepted query pair `(a, b)` of an instance whose scan
fails has a vertex `c` in the piece of the instance with `p ∣ S(a,b,c)` and `S(a,b,c) ≠ 0`
(`exists_false_positive`); such a triple is a false positive of `p`, and `F(p)` is their number.
Different pairs (instance, query pair) give different triples (`Valid.eq_of_place_eq`): `c`
determines the piece; `(a, b)` determines the place `a n + b`; the place determines the position in
the list of all pairs, which has no repetition; and the position determines the chunk.

The statement `theorem_17` is about the reduction on finite sets, and there the same sentences are
`TriangleInstance.exists_isFalsePositive_of_mem_failedScans`,
`TriangleInstance.eq_of_mem_acceptedPairs` and `TriangleInstance.card_failedScans_le`.  The two
proofs run in parallel.  They share `F(p)` and the counting step, which is stated for any family of
scans (`TriangleInstance.card_le_F_of_distinct_scans`).
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec Finset

namespace HostData

variable {X : HostData}

/-- Two query pairs at the same place, of instances with the same piece, are the same. -/
theorem Valid.eq_of_place_eq (hv : X.Valid) {t t' i i' : ℕ} (ht : t < X.m) (ht' : t' < X.m)
    (hi : i < X.w t) (hi' : i' < X.w t') (hplace : X.place t i = X.place t' i')
    (hpiece : t / X.chunkCount = t' / X.chunkCount) : t = t' ∧ i = i' := by
  have hlen := hv.length_sortedIdx
  have hend := hv.lo_add_le ht
  have hend' := hv.lo_add_le ht'
  -- The list of all pairs has no repetition, so the two pairs stand at the same position in it.
  have hpos : X.lo t + i = X.lo t' + i' := by
    rw [place, place, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      at hplace
    exact (List.Nodup.getElem_inj_iff (sortedIdx_nodup X.n X.p X.RAB)).1 hplace
  -- A position lies in one chunk only.
  have hchunk : ∀ s (hs : s % X.chunkCount < (chunkTab X.n X.p X.cap X.RAB).length),
      (chunkTab X.n X.p X.cap X.RAB)[s % X.chunkCount] = X.chunk s := fun s hs =>
    (List.getD_eq_getElem _ _ hs).symm
  have hmod : t % X.chunkCount = t' % X.chunkCount :=
    chunkTab_unique hv.cap_pos (j := X.lo t + i) (mod_chunkCount_lt ht) (mod_chunkCount_lt ht')
      (hchunk t _ ▸ ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi _⟩)
      (hchunk t' _ ▸ hpos ▸ ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi' _⟩)
  obtain rfl : t = t' := by
    rw [← Nat.div_add_mod t X.chunkCount, ← Nat.div_add_mod t' X.chunkCount, hpiece, hmod]
  exact ⟨rfl, by omega⟩

/-- Proof of Theorem 17: "A failed scan [...] contains a c ∈ C_k with S(a,b,c) ≡ 0 (mod p) but
S(a,b,c) ≠ 0". -/
theorem exists_false_positive (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t)
    (hacc : X.acc t i = true) (hhit : X.hit t i = false) :
    ∃ c < X.len t, (X.p : ℤ) ∣ X.sumAt (X.rowOf t i) (X.colOf t i) (X.c0 t + c) ∧
      X.sumAt (X.rowOf t i) (X.colOf t i) (X.c0 t + c) ≠ 0 := by
  obtain ⟨c, hc, hdvd⟩ := (acc_iff hv ht hi).1 hacc
  refine ⟨c, hc, hdvd, fun hzero => ?_⟩
  rw [(hit_iff hi).2 ⟨c, hc, hzero⟩] at hhit
  exact absurd hhit (by decide)

/-- A vertex of the piece of an instance determines the number of the piece. -/
theorem c0_add_div {t c : ℕ} (hc : c < X.len t) : (X.c0 t + c) / X.q = t / X.chunkCount := by
  rw [c0, Nat.mul_add_div_of_lt (hc.trans_le (X.len_le t))]

/-- The length of a filtered range, as the size of a set. -/
private theorem length_filter_range (k : ℕ) (f : ℕ → Bool) :
    ((List.range k).filter f).length = #{i ∈ range k | f i = true} := by
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _), List.toFinset_filter,
    List.toFinset_range]

/-- Proof of Theorem 17: "distinct scans contain distinct false positives, so there are at most F(p)
failed scans". -/
theorem sum_fails_le (hv : X.Valid) :
    ∑ t ∈ range X.m, X.fails t ≤ (triOf X.n X.AB X.BC X.AC).F X.p := by
  -- The failed scans, as a set of pairs (instance, query pair).
  set failed : Finset (Σ _ : ℕ, ℕ) :=
    (range X.m).sigma fun t => {i ∈ range (X.w t) | (X.acc t i && !X.hit t i) = true} with hfailed
  have hcard : ∑ t ∈ range X.m, X.fails t = failed.card := by
    rw [hfailed, Finset.card_sigma]
    exact Finset.sum_congr rfl fun t _ => length_filter_range _ _
  have hmem : ∀ z ∈ failed,
      z.1 < X.m ∧ z.2 < X.w z.1 ∧ X.acc z.1 z.2 = true ∧ X.hit z.1 z.2 = false := by
    intro z hz
    simpa [hfailed, and_assoc] using hz
  rw [hcard]
  -- The scan `z` contains the triples of its query pair and a vertex of its piece.
  refine TriangleInstance.card_le_F_of_distinct_scans _ failed
    (fun z τ => τ.1.val = X.rowOf z.1 z.2 ∧ τ.2.1.val = X.colOf z.1 z.2 ∧
      ∃ c < X.len z.1, τ.2.2.val = X.c0 z.1 + c) (fun z hz => ?_) ?_
  · obtain ⟨ht, hi, hacc, hhit⟩ := hmem z hz
    obtain ⟨c, hc, hdvd, hne⟩ := exists_false_positive hv ht hi hacc hhit
    have hpiece := hv.piece_le ht
    exact ⟨(⟨_, hv.rowOf_lt ht hi⟩, ⟨_, hv.colOf_lt ht hi⟩, ⟨X.c0 z.1 + c, by omega⟩),
      ⟨rfl, rfl, c, hc, rfl⟩, hne, hdvd⟩
  · rintro τ z hz z' hz' ⟨hrow, hcol, c, hc, hvertex⟩ ⟨hrow', hcol', c', hc', hvertex'⟩
    obtain ⟨ht, hi, -, -⟩ := hmem z hz
    obtain ⟨ht', hi', -, -⟩ := hmem z' hz'
    have hplace : X.place z.1 z.2 = X.place z'.1 z'.2 := by
      rw [← rowOf_mul_add_colOf, ← rowOf_mul_add_colOf, ← hrow, ← hcol, hrow', hcol']
    have hpiece : z.1 / X.chunkCount = z'.1 / X.chunkCount := by
      rw [← c0_add_div hc, ← c0_add_div hc', ← hvertex, hvertex']
    obtain ⟨ht_eq, hi_eq⟩ := hv.eq_of_place_eq ht ht' hi hi' hplace hpiece
    exact Sigma.ext ht_eq (heq_of_eq hi_eq)

end HostData

end Light.Sec3
