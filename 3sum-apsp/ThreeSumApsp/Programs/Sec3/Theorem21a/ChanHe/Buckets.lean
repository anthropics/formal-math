/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Contracts
public import ThreeSumApsp.Sec3.Theorem21a.ChanHe.Recursion
public import ThreeSumApsp.Spec.Sec3.Theorem21a.NodeArray
public import ThreeSumApsp.Spec.Sec3.Theorem21a.Passes

/-!
# 3SUM from Convolution-3SUM: remainders, counts, collisions, heavy elements

Four routines of the reduction of [CH20, Theorem 5.1] (for Theorem 21(a)).
They hash a set of integers modulo M.

* resid writes the remainders of the elements of a set (`resid_spec`).
* tally adds the remainders to a table of counts, or removes them from it (`tally_spec`).
* coll returns the number of colliding ordered pairs (`coll_spec`): by `coll_eq_list` it is the sum,
  over the elements, of the size of the element's bucket minus 1.
* heavy extracts the elements that are not alone in their bucket (`heavy_spec`,
  `heavyList_toFinset`).

In the statements the modulus is Mo, since in a program text M (…) reads a cell of the memory.
`keys M L` is the list of the remainders x % M of the numbers of L, as natural numbers, and `SegN`
is `Seg` for a list of natural numbers.

coll and heavy begin and end in the same way: resid writes the remainders to the free pointer, tally
counts them (`Counted`), a loop reads the counts, and tally removes them, so that the table holds
zeros again.  The three calls are `BucketPre.resid_meets`, `count_meets` and `uncount_meets`.
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec.ChanHeArray Finset

variable {lim : Limits} {P : Program}

/-! ## resid -/

namespace Resid

/-- The local variables of resid: the arguments len, s, sg, M, key, fr, the counter i, and the
remainder. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Src : ℕ := 1
@[inherit_doc Len] abbrev Sign : ℕ := 2
@[inherit_doc Len] abbrev Modulus : ℕ := 3
@[inherit_doc Len] abbrev Key : ℕ := 4
@[inherit_doc Len] abbrev Free : ℕ := 5
@[inherit_doc Len] abbrev Idx : ℕ := 6
@[inherit_doc Len] abbrev Rem : ℕ := 7

end Resid

open Resid in
/-- resid(len, s, sg, M, key, fr): for i < len, mem[key + i] := emod(sg * mem[s + i], M, fr). -/
def residBody (pEmod : ℕ) : Stmt :=
  .for Idx (v Len) (
    .call pEmod [v Sign *' M (v Src +' v Idx), v Modulus, v Free] Rem ;;
    .store (v Key +' v Idx) (v Rem))

/-- What is allowed for resid covers what emod needs one level of calls further down. -/
theorem emodNeed_ok {len V Mo fr d : ℕ} (h : (residNeed len V Mo).Ok lim fr d) :
    (emodNeed V Mo).Ok lim fr (d + 1) := by
  refine h.mono ?_ le_rfl le_rfl
  have hlen : 1 ≤ (len + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  -- 4 V + 4 M + 16 ≤ 64 (M + 1) (V + 1) ≤ 64 (len + 1)² (M + 1) (V + 1)
  calc 4 * V + 4 * Mo + 16 ≤ 64 * 1 * (Mo + 1) * (V + 1) := by nlinarith [Nat.zero_le (V * Mo)]
    _ ≤ 64 * (len + 1) ^ 2 * (Mo + 1) * (V + 1) := by gcongr

/-- The memory before round i of resid: the first i remainders are written, and below the free
pointer no cell outside the len cells from key has changed. -/
def ResidInv (μ : ℕ → ℤ) (fr key Mo : ℕ) (sg : ℤ) (L : List ℤ) (i : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ j (hj : j < L.length), j < i → μ' (key + j) = (sg * L[j]) % (Mo : ℤ)) ∧
    KeptBut μ μ' fr key L.length

/-- A round of resid: emod has changed no cell below the free pointer, and remainder number i is
written. -/
theorem ResidInv.succ {μ μ' μ'' : ℕ → ℤ} {fr key Mo i : ℕ} {sg : ℤ} {L : List ℤ}
    (h : ResidInv μ fr key Mo sg L i μ') (hi : i < L.length) (hkey : key + L.length ≤ fr)
    (hkept : Kept μ' μ'' fr) :
    ResidInv μ fr key Mo sg L (i + 1)
      (Function.update μ'' (key + i) ((sg * L[i]) % (Mo : ℤ))) := by
  refine ⟨fun j hj hji => ?_, (h.2.then hkept fun b hb => ⟨hb, hb.1⟩).write (by omega) _⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hji with hji | rfl
  · rw [Function.update_of_ne (by omega), hkept _ (by omega), h.1 j hj hji]
  · exact Function.update_self ..

/-- **resid** meets its specification. -/
theorem resid_spec {p pEmod : ℕ} (hP : P[p]? = some (residBody pEmod))
    (hEmod : EmodSpec lim P pEmod) : ResidSpec lim P p := by
  intro d fr V Mo s key sg L μ hM hsg hL hseg hs hkey hap hok
  refine ⟨_, hP, ?_⟩
  have hw := hok.space
  have hcells := hok.cells
  have hdepth := hok.depth
  have hword := (emodNeed_ok hok).word
  simp only [residNeed, emodNeed] at hword hdepth
  -- for i < len; the local Rem holds anything
  refine Ends.forShape (fun i (r : ℤ) μ' => ⟨frame [L.length, s, sg, Mo, key, fr, i, r], μ'⟩)
    (ResidInv μ fr key Mo sg L) L.length (tEmod V + 15) 0
    ⟨fun j _ hj => absurd hj (by omega), .refl⟩ ?round ?done
    (first := by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl)
    (hT := by simp [tResid]; ring_nf; omega)
  case round =>
    intro i r μ' hi inv
    -- The number is still in its cell, and its product with the sign is at most V in absolute
    -- value; habs: |sg * x| = |sg| * |x|.
    have hread : μ' (s + i) = L[i] := by
      rw [inv.2 _ (by omega), hseg i hi]
    have hprod : |sg * L[i]| ≤ (V : ℤ) := by
      rcases hsg with rfl | rfl <;> simpa using hL.getElem hi
    have habs := abs_mul sg L[i]
    -- r := emod(sg * mem[s + i], M, fr)
    refine Ends.callToThen (hEmod (d + 1) fr V Mo (sg * L[i]) μ' hM hprod (emodNeed_ok hok)) ?_
      (by simp [Limits.Addr, abs_le, hread]; omega)
    rintro _ μ'' ⟨rfl, hkept⟩
    -- mem[key + i] := r
    light_store (key + i) ((sg * L[i]) % (Mo : ℤ))
    exact ⟨_, _, rfl, inv.succ hi hkey hkept⟩
  case done =>
    rintro r μ' ⟨written, kept⟩
    exact ⟨fun j hj => (written j (by simpa using hj) (by simpa using hj)).trans (by simp), kept⟩

/-! ## tally -/

namespace Tally

/-- The local variables of tally: the arguments len, key, cnt, δ, and the counter i. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Key : ℕ := 1
@[inherit_doc Len] abbrev Count : ℕ := 2
@[inherit_doc Len] abbrev Delta : ℕ := 3
@[inherit_doc Len] abbrev Idx : ℕ := 4

end Tally

open Tally in
/-- tally(len, key, cnt, δ): for i < len, mem[cnt + mem[key + i]] += δ. -/
def tallyBody : Stmt :=
  .for Idx (v Len) (
    .store (v Count +' M (v Key +' v Idx)) (M (v Count +' M (v Key +' v Idx)) +' v Delta))

/-- The memory before round i of tally: the first i keys have been counted, and no cell outside the
count table has changed. -/
def TallyInv (μ : ℕ → ℤ) (cnt cap : ℕ) (δ : ℤ) (K : List ℕ) (i : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ r < cap, μ' (cnt + r) = μ (cnt + r) + δ * ((K.take i).count r : ℤ)) ∧ SameOutside μ μ' cnt cap

/-- A round of tally counts the key number i. -/
theorem TallyInv.succ {μ μ' : ℕ → ℤ} {cnt cap i : ℕ} {δ : ℤ} {K : List ℕ}
    (h : TallyInv μ cnt cap δ K i μ') (hi : i < K.length) (hk : K[i] < cap) :
    TallyInv μ cnt cap δ K (i + 1) (Function.update μ' (cnt + K[i]) (μ' (cnt + K[i]) + δ)) := by
  refine ⟨fun r hr => ?_, h.2.write (by omega) _⟩
  rw [List.count_take_succ K r hi]
  by_cases hrk : K[i] = r
  · subst hrk
    rw [Function.update_self, h.1 _ hk, if_pos rfl]
    push_cast
    ring
  · rw [Function.update_of_ne (by omega), h.1 r hr, if_neg hrk, Nat.add_zero]

/-- **tally** meets its specification. -/
theorem tally_spec {p : ℕ} (hP : P[p]? = some tallyBody) : TallySpec lim P p := by
  intro d key cnt cap δ K μ hK hδ hseg hap hbd hkey hcnt hw hword
  refine ⟨_, hP, ?_⟩
  -- for i < len
  refine Ends.forFrame (TallyInv μ cnt cap δ K) K.length ⟨fun r _ => by simp, .refl⟩
    ?round ?done (hT := by simp [tTally]; omega)
  case round =>
    intro i μ' hi inv
    have hk : K[i] < cap := hK _ (List.getElem_mem hi)
    -- The key is still in its cell, and the count that is changed is at most len + i in absolute
    -- value.
    have hread : μ' (key + i) = (K[i] : ℕ) := by
      rw [inv.2 _ (by omega), SegN.getElem hseg hi]
    have hcount : (K.take i).count K[i] ≤ i := List.count_le_length.trans (by simp)
    have hcell := inv.1 _ hk
    have hold := abs_le.1 (hbd _ hk)
    -- mem[cnt + mem[key + i]] += δ
    refine Ends.storeTo (cnt + K[i]) (μ' (cnt + K[i]) + δ) ⟨rfl, inv.succ hi hk⟩ ?_
    rcases hδ with rfl | rfl <;> simp [Limits.Addr, abs_le, hread] <;> omega
  case done =>
    exact fun μ' inv => ⟨fun r hr => (inv.1 r hr).trans (by rw [List.take_length]), inv.2⟩

/-! ## The pure side: buckets, collisions and heavy elements from the list of the remainders -/

/-- The number of colliding pairs, from the list of the remainders. -/
theorem coll_eq_list {L : List ℤ} (hL : L.Nodup) {Mo : ℕ} (hM : 1 ≤ Mo) :
    (coll L.toFinset Mo : ℤ)
      = ((keys Mo L).map fun q => ((keys Mo L).count q : ℤ) - 1).sum := by
  rw [coll_eq_sum, List.sum_toFinset _ hL]
  have h : ∀ x ∈ L, ((#(bucket L.toFinset Mo (x % (Mo : ℤ))) - 1 : ℕ) : ℤ)
      = ((keys Mo L).count (x % (Mo : ℤ)).toNat : ℤ) - 1 := by
    intro x hx
    rw [← Int.natCast_toNat_emod hM x, card_bucket hM hL]
    have : 1 ≤ (keys Mo L).count (x % (Mo : ℤ)).toNat :=
      List.count_pos_iff.2 (List.mem_map.2 ⟨x, hx, rfl⟩)
    rw [Int.natCast_toNat_emod hM x]
    omega
  rw [Nat.cast_list_sum, List.map_map]
  conv_rhs => rw [keys, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun x hx => h x hx)

/-- An element is heavy exactly if its bucket has at least two elements. -/
theorem mem_heavy_iff {S : Finset ℤ} {Mo : ℕ} {x : ℤ} (hx : x ∈ S) :
    x ∈ heavy S Mo ↔ 2 ≤ #(bucket S Mo (x % (Mo : ℤ))) := by
  have hxb : x ∈ bucket S Mo (x % (Mo : ℤ)) := by simp [bucket, hx]
  constructor
  · intro h
    obtain ⟨-, y, hy, hne, hdvd⟩ := Finset.mem_filter.1 h
    have hyb : y ∈ bucket S Mo (x % (Mo : ℤ)) := by
      simp only [bucket, Finset.mem_filter]
      exact ⟨hy, ((natCast_dvd_sub_iff_emod_eq Mo x y).1 hdvd).symm⟩
    exact Finset.one_lt_card.2 ⟨y, hyb, x, hxb, hne⟩
  · intro h
    obtain ⟨y, hy, hne⟩ := Finset.exists_mem_ne h x
    obtain ⟨hyS, hyr⟩ := Finset.mem_filter.1 hy
    exact Finset.mem_filter.2 ⟨hx, y, hyS, hne, (natCast_dvd_sub_iff_emod_eq Mo x y).2 hyr.symm⟩

/-- The heavy elements, as a sublist. -/
def heavyList (Mo : ℕ) (L : List ℤ) : List ℤ :=
  L.filter fun x => decide (2 ≤ (keys Mo L).count (x % (Mo : ℤ)).toNat)

/-- The sublist consists of the heavy elements. -/
theorem heavyList_toFinset {L : List ℤ} (hL : L.Nodup) {Mo : ℕ} (hM : 1 ≤ Mo) :
    (heavyList Mo L).toFinset = heavy L.toFinset Mo := by
  ext x
  simp only [heavyList, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hx, h⟩
    rw [mem_heavy_iff (List.mem_toFinset.2 hx), ← Int.natCast_toNat_emod hM x, card_bucket hM hL]
    exact h
  · intro h
    have hx : x ∈ L := List.mem_toFinset.1 (heavy_subset _ _ h)
    refine ⟨hx, ?_⟩
    rw [mem_heavy_iff (List.mem_toFinset.2 hx), ← Int.natCast_toNat_emod hM x,
      card_bucket hM hL] at h
    exact h

/-! ## What coll and heavy share: the remainders are counted, used, and removed from the table -/

/-- What coll and heavy assume: the list L at s, a count table of zeros with a cell for each
remainder, both below the free pointer and apart, and the limits. -/
structure BucketPre (lim : Limits) (μ : ℕ → ℤ) (d fr V Mo s cnt cap : ℕ) (L : List ℤ) : Prop where
  modulus_pos : 1 ≤ Mo
  modulus_le : Mo ≤ cap
  bounded : AbsLe L V
  list : Seg μ s L
  zero : ZeroAt μ cnt cap
  belowList : s + L.length ≤ fr
  belowTable : cnt + cap ≤ fr
  apart : Apart s L.length cnt cap
  ok : (collNeed L.length V Mo).Ok lim fr d

/-- Between the two calls of tally: the remainders stand at the free pointer, and the table holds
how often each of them occurs. -/
structure Counted (μ : ℕ → ℤ) (fr cnt cap : ℕ) (K : List ℕ) : Prop where
  keys : SegN μ fr K
  counts : ∀ q < cap, μ (cnt + q) = (K.count q : ℤ)

/-- What the need provides: a sum of len counts, which is at most len², and a few more fit in a
word. -/
theorem sq_add_le_word {n V Mo : ℕ} (h : ((wordNeed n V Mo : ℕ) : ℤ) ≤ lim.word) :
    (n : ℤ) * n + 4 * n + 17 ≤ lim.word := by
  have hMV : 1 ≤ (Mo + 1) * (V + 1) := Nat.mul_pos (by omega) (by omega)
  have hle : n * n + 4 * n + 17 ≤ wordNeed n V Mo :=
    calc n * n + 4 * n + 17 ≤ 64 * (n + 1) ^ 2 * 1 := by nlinarith
      _ ≤ 64 * (n + 1) ^ 2 * ((Mo + 1) * (V + 1)) := Nat.mul_le_mul_left _ hMV
      _ = wordNeed n V Mo := by unfold wordNeed; ring
  exact le_trans (by exact_mod_cast hle) h

/-- A table that held zeros and holds zeros again has not changed. -/
theorem sameOn_of_zeroAt {R : ℕ → Prop} {μ μ' : ℕ → ℤ} {cnt cap : ℕ}
    (h : SameOn (fun b => R b ∧ Outside cnt cap b) μ μ') (hz : ZeroAt μ cnt cap)
    (hz' : ZeroAt μ' cnt cap) : SameOn R μ μ' := fun b hb => by
  by_cases hin : Outside cnt cap b
  · exact h b ⟨hb, hin⟩
  · obtain ⟨q, rfl⟩ : ∃ q, b = cnt + q := ⟨b - cnt, by omega⟩
    rw [hz q (by omega), hz' q (by omega)]

/-- What is counted stays counted if neither the remainders nor the table change. -/
theorem Counted.of_sameOutside {μ μ' : ℕ → ℤ} {fr cnt cap a n : ℕ} {K : List ℕ}
    (h : Counted μ fr cnt cap K) (hs : SameOutside μ μ' a n) (hfr : a + n ≤ fr)
    (hap : Apart a n cnt cap) :
    Counted μ' fr cnt cap K :=
  ⟨h.keys.of_sameOutside hs (Or.inr hfr),
    fun q hq => (hs _ (by omega)).trans (h.counts q hq)⟩

/-- What coll and heavy are given, in the form in which they use it: the set is a list without
repetitions. -/
theorem BucketMem.exists_pre {μ : ℕ → ℤ} {d fr V Mo s len cnt cap : ℕ} {S : Finset ℤ}
    (h : BucketMem μ fr V Mo s len cnt cap S) (hok : (collNeed len V Mo).Ok lim fr d) :
    ∃ L : List ℤ, L.length = len ∧ L.Nodup ∧ L.toFinset = S ∧
      BucketPre lim μ d fr V Mo s cnt cap L := by
  obtain ⟨L, rfl, hseg, hnd, rfl⟩ := h.set
  exact ⟨L, rfl, hnd, rfl, h.modulus_pos, h.modulus_le,
    fun x hx => h.bdd x (List.mem_toFinset.2 hx), hseg, h.zero, h.belowSet, h.belowTable, h.apart,
    hok⟩

namespace BucketPre

variable {μ μ₁ : ℕ → ℤ} {d fr V Mo s cnt cap pResid pTally : ℕ} {L : List ℤ} {K : List ℕ}

/-- resid(len, s, sg, M, fr, fr + len) writes the remainders of the numbers sg · x to the free
pointer. -/
theorem resid_meets (C : BucketPre lim μ d fr V Mo s cnt cap L) (hResid : ResidSpec lim P pResid)
    {sg : ℤ} (hsg : sg = 1 ∨ sg = -1) :
    Meets lim P pResid (d + 1) [L.length, s, sg, Mo, fr, (fr + L.length : ℕ)] μ (tResid L.length V)
      fun _ μ₁ => SegN μ₁ fr (keys Mo (L.map (sg * ·))) ∧ Kept μ μ₁ fr := by
  have hlist := C.belowList
  refine (hResid (d + 1) (fr + L.length) V Mo s fr sg L μ C.modulus_pos hsg C.bounded C.list
    (by omega) le_rfl (Or.inl hlist) (C.ok.mono le_rfl ?_ ?_)).mono le_rfl ?_
  · simp only [residNeed, collNeed]
    omega
  · simp only [residNeed, collNeed]
    omega
  · rintro _ μ₁ ⟨written, kept⟩
    refine ⟨?_, kept.mono fun b hb => ⟨by omega, Or.inl hb⟩⟩
    rwa [SegN, map_cast_keys C.modulus_pos, List.map_map]

/-- resid(len, s, 1, M, fr, fr + len) writes the remainders of the numbers of L to the free
pointer. -/
theorem keys_meets (C : BucketPre lim μ d fr V Mo s cnt cap L) (hResid : ResidSpec lim P pResid) :
    Meets lim P pResid (d + 1) [L.length, s, 1, Mo, fr, (fr + L.length : ℕ)] μ (tResid L.length V)
      fun _ μ₁ => SegN μ₁ fr (keys Mo L) ∧ Kept μ μ₁ fr := by
  simpa using C.resid_meets hResid (Or.inl rfl)

/-- tally(len, fr, cnt, δ), run on the remainders K at the free pointer, adds δ times the number of
occurrences of q in K to cell q of the table.  Of the hypotheses of `TallySpec` only the bound on
the table is left. -/
theorem tally_meets (C : BucketPre lim μ d fr V Mo s cnt cap L) (hTally : TallySpec lim P pTally)
    (hlen : K.length = L.length) (hlt : ∀ q ∈ K, q < Mo) {δ : ℤ} (hδ : δ = 1 ∨ δ = -1)
    (hkeys : SegN μ₁ fr K) (hbd : ∀ q < cap, |μ₁ (cnt + q)| ≤ (L.length : ℤ)) :
    Meets lim P pTally (d + 1) [L.length, fr, cnt, δ] μ₁ (tTally L.length) fun _ μ₂ =>
      (∀ q < cap, μ₂ (cnt + q) = μ₁ (cnt + q) + δ * (K.count q : ℤ)) ∧
        SameOutside μ₁ μ₂ cnt cap := by
  have hcells := C.ok.cells
  have htable := C.belowTable
  have hword := sq_add_le_word C.ok.word
  have hsq : (0 : ℤ) ≤ (L.length : ℤ) * L.length := by positivity
  simp only [collNeed] at hcells
  have h := hTally (d + 1) fr cnt cap δ K μ₁ (fun q hq => (hlt q hq).trans_le C.modulus_le) hδ hkeys
    (Or.inr htable)
  rw [hlen] at h
  exact h hbd (by omega) (by omega) C.ok.space (by omega)

/-- tally(len, fr, cnt, 1) counts the remainders. -/
theorem count_meets (C : BucketPre lim μ d fr V Mo s cnt cap L) (hTally : TallySpec lim P pTally)
    (hlen : K.length = L.length) (hlt : ∀ q ∈ K, q < Mo) (hkeys : SegN μ₁ fr K)
    (kept : Kept μ μ₁ fr) :
    Meets lim P pTally (d + 1) [L.length, fr, cnt, 1] μ₁ (tTally L.length) fun _ μ₂ =>
      Counted μ₂ fr cnt cap K ∧ KeptBut μ μ₂ fr cnt cap := by
  have htable := C.belowTable
  have hzero : ZeroAt μ₁ cnt cap := fun q hq => (kept _ (by omega)).trans (C.zero q hq)
  refine (C.tally_meets hTally hlen hlt (Or.inl rfl) hkeys fun q hq => by simp [hzero q hq]).mono
    le_rfl ?_
  rintro _ μ₂ ⟨counts, same⟩
  exact ⟨⟨hkeys.of_sameOutside same (Or.inr htable),
    fun q hq => by rw [counts q hq, hzero q hq]; ring⟩, kept.then same fun b hb => hb⟩

/-- tally(len, fr, cnt, -1) removes the remainders from the table. -/
theorem uncount_meets (C : BucketPre lim μ d fr V Mo s cnt cap L) (hTally : TallySpec lim P pTally)
    (hlen : K.length = L.length) (hlt : ∀ q ∈ K, q < Mo) (h : Counted μ₁ fr cnt cap K) :
    Meets lim P pTally (d + 1) [L.length, fr, cnt, -1] μ₁ (tTally L.length) fun _ μ₂ =>
      ZeroAt μ₂ cnt cap ∧ SameOutside μ₁ μ₂ cnt cap := by
  refine (C.tally_meets hTally hlen hlt (Or.inr rfl) h.keys fun q hq => ?_).mono le_rfl ?_
  · rw [h.counts q hq, abs_of_nonneg (by positivity), ← hlen]
    exact_mod_cast List.count_le_length
  · rintro _ μ₂ ⟨counts, same⟩
    exact ⟨fun q hq => by rw [counts q hq, h.counts q hq]; ring, same⟩

end BucketPre

/-! ## coll -/

namespace Coll

/-- The local variables of coll: the arguments len, s, M, cnt, fr, the results of the calls, which
are not used, the counter i, and the sum.  Local 0 also takes the result. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Result : ℕ := 0
@[inherit_doc Len] abbrev Src : ℕ := 1
@[inherit_doc Len] abbrev Modulus : ℕ := 2
@[inherit_doc Len] abbrev Count : ℕ := 3
@[inherit_doc Len] abbrev Free : ℕ := 4
@[inherit_doc Len] abbrev Res : ℕ := 5
@[inherit_doc Len] abbrev Idx : ℕ := 6
@[inherit_doc Len] abbrev Total : ℕ := 7

end Coll

open Coll in
/-- The part of coll that adds up: sum := 0; for i < len, sum += mem[cnt + mem[fr + i]] - 1. -/
def collSum : Stmt :=
  .set Total (k 0) ;;
  .for Idx (v Len) (.set Total (v Total +' M (v Count +' M (v Free +' v Idx)) -' k 1))

open Coll in
/-- coll(len, s, M, cnt, fr) writes the remainders to fr, counts them, adds up, removes them from
the table, and returns the sum. -/
def collBody (pResid pTally : ℕ) : Stmt :=
  .call pResid [v Len, v Src, k 1, v Modulus, v Free, v Free +' v Len] Res ;;
  .call pTally [v Len, v Free, v Count, k 1] Res ;;
  collSum ;;
  .call pTally [v Len, v Free, v Count, k 0 -' k 1] Res ;;
  .set Result (v Total)

/-- The sum over the first `i` remainders. -/
def collPart (K : List ℕ) (i : ℕ) : ℤ := ((K.take i).map fun q => (K.count q : ℤ) - 1).sum

/-- The sum over the first i + 1 remainders is that over the first i, plus the term of remainder
i. -/
theorem collPart_succ (K : List ℕ) {i : ℕ} (hi : i < K.length) :
    collPart K (i + 1) = collPart K i + ((K.count K[i] : ℤ) - 1) := by
  unfold collPart
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.map_append, List.sum_append]
  simp

/-- The sum over the first `i` remainders lies between 0 and `i` times the number of remainders. -/
theorem collPart_bounds (K : List ℕ) :
    ∀ i, i ≤ K.length → 0 ≤ collPart K i ∧ collPart K i ≤ (i : ℤ) * (K.length : ℤ) := by
  intro i
  induction i with
  | zero => intro _; simp [collPart]
  | succ i ih =>
    intro hi
    obtain ⟨hlow, hhigh⟩ := ih (by omega)
    have hone : 1 ≤ K.count K[i] := List.count_pos_iff.2 (List.getElem_mem _)
    have hlen : K.count K[i] ≤ K.length := List.count_le_length
    rw [collPart_succ K (by omega)]
    push_cast
    exact ⟨by omega, by nlinarith⟩

/-- **The loop of coll** leaves the sum over all remainders in the local Total and writes no
cell. -/
theorem collSum_ends {d V s Mo cnt cap fr : ℕ} {r : ℤ} {μ₀ μ : ℕ → ℤ} {L : List ℤ}
    (C : BucketPre lim μ₀ d fr V Mo s cnt cap L) (counted : Counted μ fr cnt cap (keys Mo L)) :
    Ends lim P d collSum ⟨frame [L.length, s, Mo, cnt, fr, r], μ⟩ (20 * L.length + 10) fun σ' =>
      σ' = ⟨frame [L.length, s, Mo, cnt, fr, r, L.length, collPart (keys Mo L) L.length], μ⟩ := by
  have hw := C.ok.space
  have hword := sq_add_le_word C.ok.word
  have hcells := C.ok.cells
  have htable := C.belowTable
  simp only [collNeed] at hcells
  have hn := length_keys Mo L
  have hK : ∀ q ∈ keys Mo L, q < cap := fun q hq =>
    (keys_lt C.modulus_pos _ q hq).trans_le C.modulus_le
  clear C
  generalize keys Mo L = K at *
  generalize L.length = n at *
  have hsq : (0 : ℤ) ≤ (n : ℤ) * n := by positivity
  -- sum := 0
  light_set 0
  -- for i < len
  refine Ends.for (fun i σ => σ = ⟨frame [n, s, Mo, cnt, fr, r, i, collPart K i], μ⟩) n 12
    ?start ?round ?done ?bound
  case start => simp [update_frame_setLocal, collPart]
  case done => exact fun _ _ hσ => hσ
  case bound =>
    rintro i _ - - rfl
    simp
  case round =>
    rintro i _ hi - rfl
    have hiK : i < K.length := by omega
    have hq : K[i] < cap := hK _ (List.getElem_mem hiK)
    -- The two cells that the round reads, and the bounds on the old and the new sum.
    have hkey : μ (fr + i) = (K[i] : ℕ) := counted.keys.getElem hiK
    have hcount := counted.counts _ hq
    have hone : 1 ≤ K.count K[i] := List.count_pos_iff.2 (List.getElem_mem _)
    have hlen : K.count K[i] ≤ n := hn ▸ List.count_le_length
    obtain ⟨hlow, hhigh⟩ := collPart_bounds K i hiK.le
    have hhigh' : collPart K i ≤ (n : ℤ) * n :=
      hhigh.trans (hn ▸ mul_le_mul_of_nonneg_right (by exact_mod_cast hiK.le) (by positivity))
    -- sum += mem[cnt + mem[fr + i]] - 1
    refine Ends.setTo (collPart K (i + 1)) ⟨by simp, by rw [update_frame_setLocal]; rfl⟩ ?_
    rw [collPart_succ K hiK]
    simp [Limits.Addr, abs_le, hkey, hcount]
    omega

/-- **coll** meets its specification. -/
theorem coll_spec {p pResid pTally : ℕ} (hP : P[p]? = some (collBody pResid pTally))
    (hResid : ResidSpec lim P pResid) (hTally : TallySpec lim P pTally) : CollSpec lim P p := by
  intro d fr V Mo s len cnt cap S μ hmem hok
  obtain ⟨L, rfl, hnd, rfl, C⟩ := hmem.exists_pre hok
  refine ⟨_, hP, ?_⟩
  have hM := C.modulus_pos
  have hw := hok.space
  have hword := sq_add_le_word hok.word
  have hcells := hok.cells
  have hdepth := hok.depth
  have hsq : (0 : ℤ) ≤ (L.length : ℤ) * L.length := by positivity
  simp only [collNeed] at hcells hdepth
  -- resid(len, s, 1, M, fr, fr + len)
  light_call (C.keys_meets hResid) using tColl with _ μ₁ ⟨hkeys, kept₁⟩
  -- tally(len, fr, cnt, 1)
  light_call (C.count_meets hTally (length_keys Mo L) (keys_lt hM L) hkeys kept₁)
    using tColl with r μ₂ ⟨counted, kept₂⟩
  -- the sum
  light_piece (collSum_ends C counted) using tColl with _ rfl
  -- tally(len, fr, cnt, -1)
  light_call (C.uncount_meets hTally (length_keys Mo L) (keys_lt hM L) counted)
    using tColl with _ μ₃ ⟨zero₃, same₃⟩
  -- return the sum
  refine Ends.setTo (coll L.toFinset Mo : ℤ)
    ⟨by simp, sameOn_of_zeroAt (kept₂.then same₃ fun b hb => ⟨hb, hb.2⟩) C.zero zero₃⟩ ?_
    (by simp [tColl]; omega)
  rw [coll_eq_list hnd hM, collPart, ← length_keys Mo L, List.take_length]
  simp

/-! ## heavy -/

namespace Heavy

/-- The local variables of heavy: the arguments len, s, M, out, cnt, fr, the results of the calls,
which are not used, the counter i, and the number j of elements written.  Local 0 also takes the
result. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Result : ℕ := 0
@[inherit_doc Len] abbrev Src : ℕ := 1
@[inherit_doc Len] abbrev Modulus : ℕ := 2
@[inherit_doc Len] abbrev Out : ℕ := 3
@[inherit_doc Len] abbrev Count : ℕ := 4
@[inherit_doc Len] abbrev Free : ℕ := 5
@[inherit_doc Len] abbrev Res : ℕ := 6
@[inherit_doc Len] abbrev Idx : ℕ := 7
@[inherit_doc Len] abbrev Written : ℕ := 8

end Heavy

open Heavy in
/-- A round of the loop of heavy: if 1 < mem[cnt + mem[fr + i]] then mem[out + j] := mem[s + i] and
j := j + 1. -/
def heavyRound : Stmt :=
  .ite (k 1 <' M (v Count +' M (v Free +' v Idx)))
    (.store (v Out +' v Written) (M (v Src +' v Idx)) ;; .set Written (v Written +' k 1)) .skip

open Heavy in
/-- The part of heavy that copies: j := 0; a round for each i < len. -/
def heavyCopy : Stmt :=
  .set Written (k 0) ;;
  .for Idx (v Len) heavyRound

open Heavy in
/-- heavy(len, s, M, out, cnt, fr) writes the remainders to fr, counts them, copies the heavy
elements, removes the remainders from the table, and returns the number of heavy elements. -/
def heavyBody (pResid pTally : ℕ) : Stmt :=
  .call pResid [v Len, v Src, k 1, v Modulus, v Free, v Free +' v Len] Res ;;
  .call pTally [v Len, v Free, v Count, k 1] Res ;;
  heavyCopy ;;
  .call pTally [v Len, v Free, v Count, k 0 -' k 1] Res ;;
  .set Result (v Written)

/-- The test of heavy: the remainder of `x` occurs at least twice among the remainders. -/
def isHeavy (Mo : ℕ) (L : List ℤ) (x : ℤ) : Bool :=
  decide (2 ≤ (keys Mo L).count (x % (Mo : ℤ)).toNat)

/-- The heavy elements among the first `i` elements of the list. -/
abbrev heavyPart (Mo : ℕ) (L : List ℤ) (i : ℕ) : List ℤ := Spec.passList (isHeavy Mo L) id L i

/-- The heavy elements among all elements of the list are the list of the heavy elements. -/
theorem heavyPart_length (Mo : ℕ) (L : List ℤ) : heavyPart Mo L L.length = heavyList Mo L := by
  rw [heavyPart, Spec.passList_length, List.map_id]
  rfl

/-- The state before round i of the loop of heavy: the heavy elements among the first i elements
are written, and no cell outside the output has changed. -/
def HeavyInv (μ : ℕ → ℤ) (s Mo out cnt fr : ℕ) (r : ℤ) (L : List ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ,
    σ = ⟨frame [L.length, s, Mo, out, cnt, fr, r, i, (heavyPart Mo L i).length], μ'⟩ ∧
      Seg μ' out (heavyPart Mo L i) ∧ SameOutside μ μ' out L.length

/-- **A round of the loop of heavy** copies element i if it is heavy.  μ₀ is the memory at the start
of heavy (of C only the layout and the limits are used), μ the memory at the start of the loop.  The
conclusion has the form that `Ends.for` asks of a round. -/
theorem heavyRound_ends {d V s Mo out cnt cap fr i : ℕ} {r : ℤ} {μ₀ μ : ℕ → ℤ} {L : List ℤ}
    (C : BucketPre lim μ₀ d fr V Mo s cnt cap L) (counted : Counted μ fr cnt cap (keys Mo L))
    (hL : Seg μ s L) (O : HeavyOut fr s cnt cap out L.length) (hi : i < L.length) {σ : State}
    (hσ : HeavyInv μ s Mo out cnt fr r L i σ) :
    Ends lim P d heavyRound σ 22 fun σ' => σ'.loc Heavy.Idx = i ∧
      HeavyInv μ s Mo out cnt fr r L (i + 1)
        { σ' with loc := Function.update σ'.loc Heavy.Idx ((i : ℤ) + 1) } := by
  obtain ⟨μ', rfl, written, same⟩ := hσ
  have hcells := C.ok.cells
  light_facts C O C.ok
  simp only [collNeed] at hcells
  have hiK : i < (keys Mo L).length := by rwa [length_keys]
  have hq : (keys Mo L)[i] < Mo := keys_lt C.modulus_pos _ _ (List.getElem_mem hiK)
  have hqi : (keys Mo L)[i] = (L[i] % (Mo : ℤ)).toNat := by simp [keys]
  -- The three cells that the round reads have not changed.
  have hkey : μ' (fr + i) = ((keys Mo L)[i] : ℕ) :=
    (same _ (Or.inr (by omega))).trans (counted.keys.getElem hiK)
  have hcount : μ' (cnt + (keys Mo L)[i]) = ((keys Mo L).count (keys Mo L)[i] : ℤ) :=
    (same _ (by omega)).trans (counted.counts _ (by omega))
  have hread : μ' (s + i) = L[i] := (same _ (by omega)).trans (hL i hi)
  have hj : (heavyPart Mo L i).length ≤ i := Spec.length_passList_le _ _ _ _
  -- if 1 < mem[cnt + mem[fr + i]]
  refine Ends.iteLast (fun hheavy => ?_) (fun hlight => ?_)
    (by light_side [hkey])
  · have htwo : 2 ≤ (keys Mo L).count (keys Mo L)[i] :=
      Nat.succ_le_of_lt (by simpa [hkey, hcount] using hheavy)
    have hsucc : heavyPart Mo L (i + 1) = heavyPart Mo L i ++ [L[i]] :=
      Spec.passList_succ_of id hi (by simpa [isHeavy, ← hqi] using htwo)
    -- mem[out + j] := mem[s + i]
    light_store (out + (heavyPart Mo L i).length) L[i] using hread
    -- j := j + 1
    light_set ((heavyPart Mo L (i + 1)).length : ℤ) using hsucc
    exact ⟨by simp, Function.update μ' (out + (heavyPart Mo L i).length) L[i],
        by rw [update_frame_setLocal]; rfl, hsucc ▸ written.snoc _,
        same.update ⟨by omega, by omega⟩ _⟩
  · have hnottwo : ¬ 2 ≤ (keys Mo L).count (keys Mo L)[i] := fun htwo =>
      hlight (by simpa [hkey, hcount] using Nat.lt_of_succ_le htwo)
    have hsucc : heavyPart Mo L (i + 1) = heavyPart Mo L i :=
      Spec.passList_succ_of_not id hi (by simpa [isHeavy, ← hqi] using hnottwo)
    exact Ends.skip
      ⟨by simp, μ', by rw [update_frame_setLocal, hsucc]; rfl, hsucc ▸ written, same⟩

/-- **The loop of heavy** writes the heavy elements and leaves their number in the local Written. -/
theorem heavyCopy_ends {d V s Mo out cnt cap fr : ℕ} {r : ℤ} {μ₀ μ : ℕ → ℤ} {L : List ℤ}
    (C : BucketPre lim μ₀ d fr V Mo s cnt cap L) (counted : Counted μ fr cnt cap (keys Mo L))
    (hL : Seg μ s L) (O : HeavyOut fr s cnt cap out L.length) :
    Ends lim P d heavyCopy ⟨frame [L.length, s, Mo, out, cnt, fr, r], μ⟩ (30 * L.length + 10)
      (HeavyInv μ s Mo out cnt fr r L L.length) := by
  have hword := sq_add_le_word C.ok.word
  have hsq : (0 : ℤ) ≤ (L.length : ℤ) * L.length := by positivity
  -- j := 0
  light_set 0
  -- for i < len
  refine Ends.for (HeavyInv μ s Mo out cnt fr r L) L.length 22 ?start ?round ?done ?bound
  case start => exact ⟨μ, by simp [update_frame_setLocal], by simp, .refl⟩
  case round => exact fun i σ hi _ hσ => heavyRound_ends C counted hL O hi hσ
  case done => exact fun _ _ hσ => hσ
  case bound =>
    rintro i _ - - ⟨μ', rfl, -⟩
    simp

/-- **heavy** meets its specification. -/
theorem heavy_spec {p pResid pTally : ℕ} (hP : P[p]? = some (heavyBody pResid pTally))
    (hResid : ResidSpec lim P pResid) (hTally : TallySpec lim P pTally) : HeavySpec lim P p := by
  intro d fr V Mo s len out cnt cap S μ hmem O hok
  obtain ⟨L, rfl, hnd, rfl, C⟩ := hmem.exists_pre hok
  refine ⟨_, hP, ?_⟩
  have hout := O.below
  have hapc := O.apartTable
  have hM := C.modulus_pos
  light_facts C hok
  have hword := sq_add_le_word hok.word
  have hcells := hok.cells
  have hdepth := hok.depth
  have hsq : (0 : ℤ) ≤ (L.length : ℤ) * L.length := by positivity
  simp only [collNeed] at hcells hdepth
  -- resid(len, s, 1, M, fr, fr + len)
  light_call (C.keys_meets hResid) using tHeavy with _ μ₁ ⟨hkeys, kept₁⟩
  -- tally(len, fr, cnt, 1)
  light_call (C.count_meets hTally (length_keys Mo L) (keys_lt hM L) hkeys kept₁)
    using tHeavy with r μ₂ ⟨counted, kept₂⟩
  have hseg₂ : Seg μ₂ s L := C.list.keep
  -- the heavy elements are copied
  light_piece (heavyCopy_ends C counted hseg₂ O) using tHeavy with _ ⟨μ₃, rfl, written, same₃⟩
  rw [heavyPart_length] at written
  -- tally(len, fr, cnt, -1)
  light_call (C.uncount_meets hTally (length_keys Mo L) (keys_lt hM L)
    (counted.of_sameOutside same₃ hout hapc)) using tHeavy with _ μ₄ ⟨zero₄, same₄⟩
  have hnd' : (heavyList Mo L).Nodup := hnd.filter _
  have hcard : #(heavy L.toFinset Mo) = (heavyList Mo L).length := by
    rw [← heavyList_toFinset hnd hM, List.toFinset_card_of_nodup hnd']
  have hle : (heavyList Mo L).length ≤ L.length := List.length_filter_le _ _
  -- return the number of heavy elements
  refine Ends.setTo (#(heavy L.toFinset Mo) : ℤ) ⟨by simp,
    ⟨heavyList Mo L, hcard.symm, written.keep,
      hnd', heavyList_toFinset hnd hM⟩, ?_⟩ (by simp [hcard, heavyPart_length])
    (by simp [tHeavy]; omega)
  exact sameOn_of_zeroAt ((kept₂.then same₃ fun b hb => ⟨⟨hb.1.1, hb.2⟩, hb.1.2⟩).then same₄
    fun b hb => ⟨hb, hb.2⟩) C.zero zero₄

end Light.Sec3.ChanHe
