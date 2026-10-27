/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Inst.HalfIfc

/-! # The encoding of the strings by partitions

A string x of λ bits stands for the partition number x in the list of the partitions of h, which is
entry h of the table of the partitions of 0, …, W. If p(h) ≥ 2^λ and h ≤ W, that entry
exists: it is a list of positive parts with sum h that occurs in the flattened table (`encF_mem`,
`encF_ok`, `encF_mem_flatten`), and different strings stand for different partitions, also as
multisets (`encF_inj`). The flattened table has the three properties that the tables of matrices
need (`flatOK_allTab`). The last theorem, `stEnc`, collects the facts on the encoding for W = 4h. -/

public section

namespace ClauseBound.Inst.Half

open Groundwork ClauseBound.Alg

variable {lam h W : ℕ}

/-- The number written by a string of λ bits is below 2^λ. -/
theorem ofWord_bitsOf_lt (x : Pieces.Bits lam) : ofWord (bitsOf x) < 2 ^ lam := by
  have h1 := ofWord_lt (bitsOf x)
  rwa [bitsOf, List.length_ofFn] at h1

/-- Different strings write different numbers. -/
theorem ofWord_bitsOf_inj {x v : Pieces.Bits lam} (e : ofWord (bitsOf x) = ofWord (bitsOf v)) : x = v := by
  have h1 := toWord_ofWord (bitsOf x)
  have h2 := toWord_ofWord (bitsOf v)
  rw [e, show (bitsOf x).length = (bitsOf v).length by rw [bitsOf, bitsOf, List.length_ofFn, List.length_ofFn], h2] at h1
  exact List.ofFn_injective h1.symm

/-- The number written by a string is a position in the list of the partitions of h. -/
theorem ofWord_bitsOf_lt_length (hW : h ≤ W) (hp : 2 ^ lam ≤ Partitions.p h) (x : Pieces.Bits lam) :
    ofWord (bitsOf x) < ((allTab W).getD h []).length := by
  rw [length_allTab_getD hW]
  exact (ofWord_bitsOf_lt x).trans_le hp

/-- The partition of a string is the entry at that position. -/
theorem encF_eq_getElem (hW : h ≤ W) (hp : 2 ^ lam ≤ Partitions.p h) (x : Pieces.Bits lam) :
    encF (allTab W) h (bitsOf x) = ((allTab W).getD h [])[ofWord (bitsOf x)]'(ofWord_bitsOf_lt_length hW hp x) :=
  List.getD_eq_getElem _ _ _

/-- The partition of a string is in the list of the partitions of h. -/
theorem encF_mem (hW : h ≤ W) (hp : 2 ^ lam ≤ Partitions.p h) (x : Pieces.Bits lam) :
    encF (allTab W) h (bitsOf x) ∈ (allTab W).getD h [] := by
  rw [encF_eq_getElem hW hp x]
  exact List.getElem_mem _

/-- The partition of a string has positive parts and the sum h. -/
theorem encF_ok (hW : h ≤ W) (hp : 2 ^ lam ≤ Partitions.p h) (x : Pieces.Bits lam) :
    ClauseBound.Boson.Pos (encF (allTab W) h (bitsOf x)) ∧ (encF (allTab W) h (bitsOf x)).sum = h := by
  have h1 := (mem_allTab_getD hW).1 (encF_mem hW hp x)
  exact ⟨h1.2.1, h1.1⟩

/-- The partition of a string is in the flattened table. -/
theorem encF_mem_flatten (hW : h ≤ W) (hp : 2 ^ lam ≤ Partitions.p h) (x : Pieces.Bits lam) :
    encF (allTab W) h (bitsOf x) ∈ (allTab W).flatten := by
  have h1 := (mem_allTab_getD hW).1 (encF_mem hW hp x)
  exact mem_flatten_allTab.2 ⟨h1.1.trans_le hW, h1.2.1, h1.2.2⟩

/-- Different strings stand for different partitions, also as multisets. -/
theorem encF_inj (hW : h ≤ W) (hp : 2 ^ lam ≤ Partitions.p h) (x v : Pieces.Bits lam)
    (e : (encF (allTab W) h (bitsOf x) : Multiset ℕ) = encF (allTab W) h (bitsOf v)) : x = v := by
  rw [encF_eq_getElem hW hp x, encF_eq_getElem hW hp v] at e
  have h1 := nodup_map_coe_allTab_getD hW
  have hx := ofWord_bitsOf_lt_length hW hp x
  have hv := ofWord_bitsOf_lt_length hW hp v
  have h2 : (((allTab W).getD h []).map fun L : List ℕ => (L : Multiset ℕ))[ofWord (bitsOf x)]'(by rw [List.length_map]; exact hx)
      = (((allTab W).getD h []).map fun L : List ℕ => (L : Multiset ℕ))[ofWord (bitsOf v)]'(by rw [List.length_map]; exact hv) := by
    rw [List.getElem_map, List.getElem_map]
    exact e
  exact ofWord_bitsOf_inj (h1.getElem_inj_iff.1 h2)

/-- The list of all partitions of 0, …, W, written as nonincreasing lists: different lists are
different multisets, erasing a part leads to a listed partition, and all sums are at most W. -/
theorem flatOK_allTab (W : ℕ) : FlatOK W (allTab W).flatten where
  inj π hπ σ hσ e :=
    (Multiset.coe_eq_coe.1 e).eq_of_pairwise' (mem_flatten_allTab.1 hπ).2.2 (mem_flatten_allTab.1 hσ).2.2
  erase π hπ l hl := by
    obtain ⟨h1, h2, h3⟩ := mem_flatten_allTab.1 hπ
    refine mem_flatten_allTab.2 ⟨?_, fun n hn => h2 n (List.mem_of_mem_erase hn), h3.sublist List.erase_sublist⟩
    have := List.sum_erase hl
    omega
  sum_le π hπ := (mem_flatten_allTab.1 hπ).1

/-- The encoding with the table of the partitions of 0, …, 4h, in the form in which the
specification of the pieces uses it. -/
theorem stEnc : StEnc := fun _ h _ hp =>
  ⟨fun x => ⟨(encF_ok (by omega) hp x).1, (encF_ok (by omega) hp x).2, encF_mem_flatten (by omega) hp x⟩,
    fun x v e => encF_inj (W := 4 * h) (by omega) hp x v e⟩

end ClauseBound.Inst.Half
