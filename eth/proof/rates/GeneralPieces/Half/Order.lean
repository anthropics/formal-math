/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Half.List
public import ClauseBound.Inst.HalfEnc

/-! # The pieces with ρ = 1/√2 as programs: a string stands for the partition with its number in the lexicographic list

In the proof of the theorem on pieces with ρ = 1/√2, μ(x) is the partition of h with number x in the
lexicographic list of the partitions of h, written as nonincreasing sequences. The programs read the
string x as a number, first bit lowest, and take the entry with that number of the list
`ClauseBound.Part.partsOf h`. That list is strictly increasing in the lexicographic order
(`pairwise_partsLe`), so the
number of an entry is the number of partitions that come before it (`lexNum_partsOf`), and the
partitions of the programs are those of Appendix B (`isMu`). Also: the number h of Appendix B is
that of
the programs (`hOf_eq`). -/

public section

namespace GeneralPieces.Half

open AppHalfPieces Finset ClauseBound.Part GeneralPieces.Ring Groundwork ClauseBound.Alg ClauseBound.Inst.Half

/-- The list of the partitions of E into parts of size at most k is strictly increasing in the
lexicographic order. -/
theorem pairwise_partsLe (E k : ℕ) : (partsLe E k).Pairwise (· < ·) := by
  induction E using Nat.strong_induction_on generalizing k with
  | _ E ihE =>
    induction k with
    | zero =>
      rw [partsLe_zero_right]
      split_ifs <;> simp
    | succ k ihk =>
      rw [partsLe_succ, List.pairwise_append]
      refine ⟨ihk, ?_, ?_⟩
      · split_ifs with hk
        · rw [List.pairwise_map]
          exact (ihE (E - (k + 1)) (by omega) (k + 1)).imp fun h => List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, h⟩)
        · exact List.Pairwise.nil
      · intro a ha b hb
        split_ifs at hb with hk
        · obtain ⟨L, _, rfl⟩ := List.mem_map.1 hb
          cases a with
          | nil => exact List.nil_lt_cons _ _
          | cons n a' =>
            have := (((mem_partsLe E k _).1 ha).2.1 n List.mem_cons_self).2
            exact List.cons_lt_cons_iff.2 (Or.inl (by omega))
        · exact absurd hb List.not_mem_nil

/-- A nonincreasing list of positive integers is its partition written as a nonincreasing sequence. -/
theorem desc_ptn {L : List ℕ} (hL : ClauseBound.Boson.Pos L) (hs : L.Pairwise (· ≥ ·)) : desc (ptn L) = L := by
  have h : desc (ptn L) = (toN (ptn L)).sort (· ≥ ·) := rfl
  rw [h, toN_ptn hL]
  exact List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _) hs (Multiset.coe_eq_coe.1 (Multiset.sort_eq _ _))

theorem coe_desc (ν : Ptn) : ((desc ν : List ℕ) : Multiset ℕ) = toN ν := Multiset.sort_eq _ _

theorem pos_desc (ν : Ptn) : ClauseBound.Boson.Pos (desc ν) := fun n hn => by
  have h1 : n ∈ toN ν := by rw [← coe_desc]; exact Multiset.mem_coe.2 hn
  exact Nat.pos_of_ne_zero fun h0 => zero_notMem_toN ν (h0 ▸ h1)

/-- A partition is the partition of its nonincreasing sequence. -/
theorem ptn_desc (ν : Ptn) : ptn (desc ν) = ν := toN_injective (by rw [toN_ptn (pos_desc ν), coe_desc])

/-- The nonincreasing sequence of a partition of h is in the list. -/
theorem desc_mem_partsOf {h : ℕ} {ν : Ptn} (hν : ν ∈ ptns h) : desc ν ∈ partsOf h :=
  mem_partsOf.2 ⟨by rw [← Multiset.sum_coe, coe_desc, sum_toN]; exact (mem_ptns h ν).1 hν, pos_desc ν, Multiset.pairwise_sort _ _⟩

/-- The entry number k of the list of the partitions of h has the number k in the lexicographic
list. -/
theorem lexNum_partsOf (h k : ℕ) (hk : k < (partsOf h).length) : lexNum h (ptn (partsOf h)[k]) = k := by
  have hm : ∀ L ∈ partsOf h, L.sum = h ∧ ClauseBound.Boson.Pos L ∧ L.Pairwise (· ≥ ·) := fun L hL => mem_partsOf.1 hL
  have hd : ∀ j (hj : j < (partsOf h).length), desc (ptn (partsOf h)[j]) = (partsOf h)[j] := fun j hj =>
    desc_ptn (hm _ (List.getElem_mem hj)).2.1 (hm _ (List.getElem_mem hj)).2.2
  have hlt := List.pairwise_iff_getElem.1 (pairwise_partsLe h h)
  have hset : {ν ∈ ptns h | desc ν < desc (ptn (partsOf h)[k])} = (((partsOf h).take k).map ptn).toFinset := by
    ext ν
    rw [Finset.mem_filter, List.mem_toFinset, List.mem_map, hd k hk]
    constructor
    · rintro ⟨hν, hl⟩
      obtain ⟨j, hj, e⟩ := List.getElem_of_mem (desc_mem_partsOf hν)
      refine ⟨desc ν, List.mem_take_iff_getElem.2 ⟨j, ?_, e⟩, ptn_desc ν⟩
      rw [lt_min_iff]
      refine ⟨?_, hj⟩
      by_contra hkj
      rcases Nat.lt_or_ge k j with h1 | h1
      · have h2 : (partsOf h)[k] < (partsOf h)[j] := hlt k j hk hj h1
        rw [e] at h2
        exact lt_asymm h2 hl
      · have h2 : j = k := by omega
        subst h2
        rw [e] at hl
        exact lt_irrefl _ hl
    · rintro ⟨L, hL, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.1 hL
      rw [lt_min_iff] at hj
      have hmj := hm _ (List.getElem_mem hj.2)
      exact ⟨(mem_ptns h _).2 (by rw [wt_ptn hmj.2.1, hmj.1]), by rw [hd j hj.2]; exact hlt j k hj.2 hk hj.1⟩
  have hnd : (((partsOf h).take k).map ptn).Nodup := by
    refine List.Nodup.map_on (fun L hL L' hL' e => ?_) ((nodup_partsOf h).sublist (List.take_sublist _ _))
    have h1 := hm L (List.mem_of_mem_take hL)
    have h2 := hm L' (List.mem_of_mem_take hL')
    rw [← desc_ptn h1.2.1 h1.2.2, e, desc_ptn h2.2.1 h2.2.2]
  rw [lexNum, hset, List.toFinset_card_of_nodup hnd, List.length_map, List.length_take, min_eq_left hk.le]

/-- A string read as an integer, first bit lowest, is the number that the programs read. -/
theorem val_eq {lam : ℕ} (x : Pieces.Bits lam) : AppHalfPieces.val x = ofWord (bitsOf x) := by
  induction lam with
  | zero => simp [AppHalfPieces.val, bitsOf, ofWord]
  | succ n ih =>
    have h := ih fun i => x i.succ
    rw [bitsOf] at h
    rw [AppHalfPieces.val, Fin.sum_univ_succ, bitsOf, List.ofFn_succ, ofWord, ← h, AppHalfPieces.val, Finset.mul_sum]
    congr 1
    · cases x 0 <;> simp
    · refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp [pow_succ, mul_comm]

/-- The partition that the programs read from the string x is the partition of h with number x in
the lexicographic list. -/
theorem isMu {lam h : ℕ} (hp : 2 ^ lam ≤ Partitions.p h) : IsMu lam h fun x => ptn (ell h x) := by
  intro x
  have hk : ofWord (bitsOf x) < (partsOf h).length := by
    rw [length_partsOf]
    exact (ofWord_bitsOf_lt x).trans_le hp
  have he : ell h x = (partsOf h)[ofWord (bitsOf x)] := by
    rw [ell, encF, allTab_getD (by omega)]
    exact List.getD_eq_getElem _ _ hk
  have hm := mem_partsOf.1 (List.getElem_mem hk)
  dsimp only
  rw [he, val_eq]
  exact ⟨(mem_ptns h _).2 (by rw [wt_ptn hm.2.1, hm.1]), lexNum_partsOf h _ hk⟩

/-- The least h ≥ 2 with p(h) ≥ 2^λ: the number h of Appendix B is the number of the programs. -/
theorem hOf_eq (lam : ℕ) : AppHalfPieces.hOf lam = ClauseBound.Part.hOf lam := by
  have hmem : ClauseBound.Part.hOf lam ∈ {h | 2 ≤ h ∧ 2 ^ lam ≤ Partitions.p h} := ⟨two_le_hOf lam, two_pow_le_p_hOf lam⟩
  refine le_antisymm (Nat.sInf_le hmem) ?_
  have h1 : AppHalfPieces.hOf lam ∈ {h | 2 ≤ h ∧ 2 ^ lam ≤ Partitions.p h} := Nat.sInf_mem ⟨_, hmem⟩
  unfold ClauseBound.Part.hOf
  exact Nat.find_min' _ h1

end GeneralPieces.Half
