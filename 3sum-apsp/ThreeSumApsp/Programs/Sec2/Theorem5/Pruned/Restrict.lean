/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

/-!
# Restricting an array on a set of codes to a subset (step (4) of Pruned, Section 2.4.2)

pick walks once through an increasing list of codes (big), which has a value for each of its codes,
and through an increasing list of some of these codes (small).  It writes the values of the codes of
the second list, or adds them to what is there.

* The lists.  `PickInv` says where the walk stands.  If the two heads agree, the value is taken and
  both lists advance (`PickInv.hit`); if not, the head of the large list is skipped
  (`PickInv.miss`).
* The memory.  `PickMem` says which cells of the destination are finished; `PickMem.write` finishes
  one more.
* The program.  `pickTake_ends` treats the round in which a value is taken, `pickBody_ends` the
  loop, for both modes.  `pickSet_entry` and `pickAdd_entry` are the results for the callers: a call
  of procedure `pPick` does what `PickSetSpec` (writing) or `PickAddSpec` (adding) says, in at most
  `cPick` steps for each entry of the two lists.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## The program -/

namespace PickLocal

/-- The small list. -/
abbrev PSUB : ℕ := 0
/-- The length of the small list. -/
abbrev NSUB : ℕ := 1
/-- The large list. -/
abbrev PU : ℕ := 2
/-- The values of the codes of the large list. -/
abbrev PVAL : ℕ := 4
/-- The destination. -/
abbrev PDST : ℕ := 5
/-- The mode: 0 for writing, otherwise adding. -/
abbrev ADD : ℕ := 6
/-- The position i in the small list. -/
abbrev CI : ℕ := 7
/-- The position j in the large list. -/
abbrev CJ : ℕ := 8

end PickLocal

open PickLocal

/-- The two heads agree: the value is written or added, and both lists advance. -/
def pickTake : Stmt :=
  .ite (v ADD =' k 0)
    (.store (v PDST +' v CI) (M (v PVAL +' v CJ)))
    (.store (v PDST +' v CI) (M (v PDST +' v CI) +' M (v PVAL +' v CJ))) ;;
  .set CI (v CI +' k 1) ;;
  .set CJ (v CJ +' k 1)

/-- pick(pSub, nSub, pU, nU, pVal, pDst, add).  The length nU of the large list, local 3, is not
read: the large list cannot end before the small one. -/
def pickBody : Stmt :=
  .set CI (k 0) ;;
  .set CJ (k 0) ;;
  .while (v CI <' v NSUB) (
    .ite (M (v PU +' v CJ) =' M (v PSUB +' v CI)) pickTake (.set CJ (v CJ +' k 1)))

/-- The constant of the running time. -/
def cPick : ℕ := 40

/-! ## The lists -/

section Lists

variable {big small : List ℕ} {vals : List ℤ} {i j : ℕ}

/-- The state of the walk: position i in the small list, position j in the large one. -/
structure PickInv (big : List ℕ) (vals : List ℤ) (small : List ℕ) (i j : ℕ) : Prop where
  i_le : i ≤ small.length
  j_le : j ≤ big.length
  sub : ∀ x ∈ small.drop i, x ∈ big.drop j
  eq : Spec.restrictList (big.drop j) (vals.drop j) (small.drop i)
    = (Spec.restrictList big vals small).drop i

/-- Before the walk. -/
theorem PickInv.zero (h : ∀ x ∈ small, x ∈ big) : PickInv big vals small 0 0 :=
  ⟨Nat.zero_le _, Nat.zero_le _, by simpa using h, by simp⟩

/-- As long as the small list is not exhausted, neither is the large one. -/
theorem PickInv.lt (h : PickInv big vals small i j) (hi : i < small.length) : j < big.length := by
  have hmem := h.sub small[i] (by rw [List.drop_eq_getElem_cons hi]; exact List.mem_cons_self)
  by_contra hj
  rw [List.drop_eq_nil_of_le (by omega)] at hmem
  simp at hmem

/-- The two heads agree: the value is taken. -/
theorem PickInv.hit (h : PickInv big vals small i j) (hlen : vals.length = big.length)
    (hs : small.Pairwise (· < ·)) (hi : i < small.length) (hj : j < big.length)
    (hb : big[j] = small[i]) :
    PickInv big vals small (i + 1) (j + 1) ∧ i < (Spec.restrictList big vals small).length ∧
      (Spec.restrictList big vals small).getD i 0 = vals.getD j 0 := by
  have hjv : j < vals.length := by omega
  have hsmall := List.drop_eq_getElem_cons hi
  have hbig := List.drop_eq_getElem_cons hj
  have heq := h.eq
  rw [hsmall, hbig, List.drop_eq_getElem_cons hjv, Spec.restrictList, if_pos hb] at heq
  have hip : i < (Spec.restrictList big vals small).length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (show (Spec.restrictList big vals small).length ≤ i by omega)]
      at heq
    simp at heq
  rw [List.drop_eq_getElem_cons hip] at heq
  obtain ⟨hhead, htail⟩ := List.cons.inj heq
  refine ⟨⟨hi, hj, fun x hx => ?_, htail⟩, hip, ?_⟩
  · -- A later number of the small list is larger than the common head.
    have hx' : x ∈ big.drop j := h.sub x (by rw [hsmall]; exact List.mem_cons_of_mem _ hx)
    have hsorted : (small.drop i).Pairwise (· < ·) := hs.sublist (List.drop_sublist _ _)
    rw [hsmall] at hsorted
    have hlt := (List.pairwise_cons.1 hsorted).1 x hx
    rw [hbig] at hx'
    exact (List.mem_cons.1 hx').resolve_left (by omega)
  · rw [List.getD_eq_getElem _ _ hip, List.getD_eq_getElem _ _ hjv, hhead]

/-- The two heads differ: the head of the large list is skipped. -/
theorem PickInv.miss (h : PickInv big vals small i j) (hlen : vals.length = big.length)
    (hbs : big.Pairwise (· < ·)) (hs : small.Pairwise (· < ·)) (hi : i < small.length)
    (hj : j < big.length) (hb : big[j] ≠ small[i]) : PickInv big vals small i (j + 1) := by
  have hjv : j < vals.length := by omega
  have hsmall := List.drop_eq_getElem_cons hi
  have hbig := List.drop_eq_getElem_cons hj
  have heq := h.eq
  rw [hsmall, hbig, List.drop_eq_getElem_cons hjv, Spec.restrictList, if_neg hb, ← hsmall] at heq
  have hbsorted : (big.drop j).Pairwise (· < ·) := hbs.sublist (List.drop_sublist _ _)
  have hssorted : (small.drop i).Pairwise (· < ·) := hs.sublist (List.drop_sublist _ _)
  rw [hbig] at hbsorted
  rw [hsmall] at hssorted
  -- The head of the small list comes later in the large list, so it is larger than the head there.
  have hhead : small[i] ∈ big.drop (j + 1) := by
    have hmem := h.sub small[i] (by rw [hsmall]; exact List.mem_cons_self)
    rw [hbig] at hmem
    exact (List.mem_cons.1 hmem).resolve_left fun hx => hb hx.symm
  have hlt : big[j] < small[i] := (List.pairwise_cons.1 hbsorted).1 _ hhead
  refine ⟨h.i_le, hj, fun x hx => ?_, heq⟩
  have hx' := h.sub x hx
  rw [hbig] at hx'
  refine (List.mem_cons.1 hx').resolve_left fun hxb => ?_
  rw [hsmall] at hx
  rcases List.mem_cons.1 hx with hxs | hxs
  · omega
  · have := (List.pairwise_cons.1 hssorted).1 x hxs
    omega

/-- pick gives at most one value for each number of the small list. -/
theorem length_restrictList_le : ∀ (big : List ℕ) (vals : List ℤ) (small : List ℕ),
    (Spec.restrictList big vals small).length ≤ small.length
  | [], _, _ => by simp [Spec.restrictList]
  | _ :: _, [], _ => by simp [Spec.restrictList]
  | _ :: _, _ :: _, [] => by simp [Spec.restrictList]
  | b :: bs, a :: as, s :: ss => by
    rw [Spec.restrictList]
    split_ifs
    · have := length_restrictList_le bs as ss
      simp only [List.length_cons]
      omega
    · exact length_restrictList_le bs as (s :: ss)

end Lists

/-! ## The memory -/

variable {lim : Limits} {P : Program} {d pDst add i j n : ℕ} {res : List ℤ} {μ μ' : ℕ → ℤ}
  {x : PickArgs}

/-- What cell i of the destination holds in the end: entry i of the list res, added to what the cell
held if add is not 0. -/
def pickTarget (add : ℕ) (μ : ℕ → ℤ) (pDst : ℕ) (res : List ℤ) (i : ℕ) : ℤ :=
  (if add = 0 then 0 else μ (pDst + i)) + res.getD i 0

/-- The first i of the n cells of the destination are finished, and nothing else has changed. -/
structure PickMem (add : ℕ) (μ μ' : ℕ → ℤ) (pDst n : ℕ) (res : List ℤ) (i : ℕ) : Prop where
  done : ∀ i' < i, μ' (pDst + i') = pickTarget add μ pDst res i'
  todo : ∀ i', i ≤ i' → μ' (pDst + i') = μ (pDst + i')
  rest : SameOutside μ μ' pDst n

/-- One more cell is finished. -/
theorem PickMem.write (h : PickMem add μ μ' pDst n res i) (hi : i < n) :
    PickMem add μ (Function.update μ' (pDst + i) (pickTarget add μ pDst res i)) pDst n res
      (i + 1) := by
  refine ⟨fun i' hi' => ?_, fun i' hi' => ?_, h.rest.update ⟨by omega, by omega⟩ _⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt | rfl
    · rw [Function.update_of_ne (by omega)]
      exact h.done i' hlt
    · exact Function.update_self _ _ _
  · rw [Function.update_of_ne (by omega)]
    exact h.todo i' (by omega)

/-- The small list lies above the destination, so it can be read at any time. -/
theorem PickPre.readSub (pl : PickPre lim μ x)
    (mem : PickMem add μ μ' x.pDst x.small.length res i) (hi : i < x.small.length) :
    μ' (x.pSub + i) = (x.small[i] : ℕ) := by
  have := pl.dst_sub
  exact (mem.rest _ (Or.inr (by omega))).trans (pl.small.getElem hi)

/-- The large list lies above the destination, so it can be read at any time. -/
theorem PickPre.readBig (pl : PickPre lim μ x)
    (mem : PickMem add μ μ' x.pDst x.small.length res i) (hj : j < x.big.length) :
    μ' (x.pU + j) = (x.big[j] : ℕ) := by
  have := pl.dst_big
  exact (mem.rest _ (Or.inr (by omega))).trans (pl.big.getElem hj)

/-- The values lie above the destination, so they can be read at any time. -/
theorem PickPre.readVal (pl : PickPre lim μ x)
    (mem : PickMem add μ μ' x.pDst x.small.length res i) (hj : j < x.big.length) :
    μ' (x.pVal + j) = x.values.getD j 0 := by
  have := pl.dst_val
  have hjv : j < x.values.length := pl.len ▸ hj
  rw [mem.rest _ (Or.inr (by omega)), pl.values j hjv, List.getD_eq_getElem _ _ hjv]

/-! ## The walk -/

/-- The state of the loop. -/
abbrev pickState (x : PickArgs) (add i j : ℕ) (μ' : ℕ → ℤ) : State :=
  ⟨frame (x.vals add ++ [(i : ℤ), (j : ℤ)]), μ'⟩

/-- The invariant of the loop. -/
def PickLoop (x : PickArgs) (add : ℕ) (μ : ℕ → ℤ) (σ : State) : Prop :=
  ∃ (i j : ℕ) (μ' : ℕ → ℤ), σ = pickState x add i j μ' ∧
    PickInv x.big x.values x.small i j ∧
    PickMem add μ μ' x.pDst x.small.length (Spec.restrictList x.big x.values x.small) i

/-- What is left of the large list. -/
def pickRest (big : List ℕ) (σ : State) : ℕ := big.length - (σ.loc CJ).toNat

/-- What a round that starts in σ achieves: the invariant holds again, and less is left. -/
def PickNext (x : PickArgs) (add : ℕ) (μ : ℕ → ℤ) (σ σ' : State) : Prop :=
  PickLoop x add μ σ' ∧ pickRest x.big σ' < pickRest x.big σ

/-- The sums that are formed in the mode that adds fit in a word. -/
def PickFits (lim : Limits) (add : ℕ) (μ : ℕ → ℤ) (pDst : ℕ) (res : List ℤ) : Prop :=
  add ≠ 0 → ∀ i < res.length, |μ (pDst + i) + res.getD i 0| ≤ lim.word

/-- The round in which the two heads agree. -/
theorem pickTake_ends (std : Std lim) (pl : PickPre lim μ x)
    (hfits : PickFits lim add μ x.pDst (Spec.restrictList x.big x.values x.small))
    (inv : PickInv x.big x.values x.small i j)
    (mem : PickMem add μ μ' x.pDst x.small.length (Spec.restrictList x.big x.values x.small) i)
    (hi : i < x.small.length) (hb : x.big[j]'(inv.lt hi) = x.small[i]) :
    Ends lim P d pickTake (pickState x add i j μ') 25
      (PickNext x add μ
        (pickState x add i j μ')) := by
  light_facts std pl
  have hj := inv.lt hi
  have hreadV := pl.readVal mem hj
  have hreadD : μ' (x.pDst + i) = μ (x.pDst + i) := mem.todo i le_rfl
  obtain ⟨inv', hip, hval⟩ := inv.hit pl.len pl.small_sorted hi hj hb
  -- i := i + 1; j := j + 1
  have htail : Ends lim P d (.set CI (v CI +' k 1) ;; .set CJ (v CJ +' k 1))
      (pickState x add i j (Function.update μ' (x.pDst + i)
        (pickTarget add μ x.pDst (Spec.restrictList x.big x.values x.small) i))) 8
      (PickNext x add μ
        (pickState x add i j μ')) := by
    refine Ends.setToThen (i + 1 : ℕ) ?_
    refine Ends.setTo (j + 1 : ℕ) ?_
    exact ⟨⟨i + 1, j + 1, _, rfl, inv', mem.write hi⟩, by simp [pickRest]; omega⟩
  unfold pickTake
  -- if add = 0
  refine Ends.iteThen (fun h0 => ?_) (fun h0 => ?_)
  · replace h0 : add = 0 := by simpa using h0
    rw [pickTarget, if_pos h0, zero_add, hval] at htail
    -- dst[i] := val[j]
    light_store (x.pDst + i) (x.values.getD j 0) using hreadV
    exact htail.mono (by light_time) fun _ h => h
  · replace h0 : add ≠ 0 := by simpa using h0
    obtain ⟨hlow, hhigh⟩ := abs_le.mp (hfits h0 i hip)
    rw [pickTarget, if_neg h0, hval] at htail
    simp only [hval, List.getD_eq_getElem?_getD] at hlow hhigh
    -- dst[i] := dst[i] + val[j]
    light_store (x.pDst + i) (μ (x.pDst + i) + x.values.getD j 0) using hreadV, hreadD
    exact htail.mono (by light_time) fun _ h => h

/-- **The walk**, for both modes. -/
theorem pickBody_ends (std : Std lim) (pl : PickPre lim μ x)
    (add : ℕ) (hfits : PickFits lim add μ x.pDst (Spec.restrictList x.big x.values x.small)) :
    Ends lim P d pickBody ⟨frame (x.vals add), μ⟩
      (39 * x.big.length + 8) fun σ' =>
        (∀ i < x.small.length, σ'.mem (x.pDst + i)
          = pickTarget add μ x.pDst (Spec.restrictList x.big x.values x.small) i) ∧
        SameOutside μ σ'.mem x.pDst x.small.length := by
  light_facts std pl
  unfold pickBody
  -- i := 0; j := 0
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  -- while i < nSub
  refine Ends.whileVariant (PickLoop x add μ) (pickRest x.big) 35
    ?start (fun _ _ => ⟨trivial, trivial⟩) ?round ?done (by simp [pickRest]; omega)
  case start =>
    exact ⟨0, 0, μ, rfl, PickInv.zero pl.sub, fun _ h => absurd h (by omega), fun _ _ => rfl,
      .refl⟩
  case round =>
    rintro _ ⟨i, j, μ', rfl, inv, mem⟩ hi
    replace hi : i < x.small.length := by simpa using hi
    have hj := inv.lt hi
    have hreadS := pl.readSub mem hi
    have hreadU := pl.readBig mem hj
    -- if big[j] = small[i]
    refine Ends.iteLast (fun hb => ?_) (fun hb => ?_) (by light_side)
    · exact pickTake_ends std pl hfits inv mem hi (by simpa [hreadS, hreadU] using hb)
    · replace hb : x.big[j] ≠ x.small[i] := by simpa [hreadS, hreadU] using hb
      -- j := j + 1
      light_set (j + 1 : ℕ)
      exact ⟨⟨i, j + 1, μ', rfl,
        inv.miss pl.len pl.big_sorted pl.small_sorted hi hj hb, mem⟩, by simp [pickRest]; omega⟩
  case done =>
    rintro _ ⟨i, j, μ', rfl, inv, mem⟩ hi
    replace hi : ¬ i < x.small.length := by simpa using hi
    exact ⟨fun i' hi' => mem.done i' (by omega), mem.rest⟩

/-! ## The two results for the callers -/

/-- **pick, writing**: a call with add = 0 writes the values of the codes of the small list to pDst
and changes no other cell, in at most cPick (small.length + big.length + 1) steps. -/
theorem pickSet_entry (std : Std lim) (hP : P[pPick]? = some pickBody) {c : ℕ} (hc : cPick ≤ c) :
    PickSetSpec lim P c := by
  intro x μ pl d _
  refine .mono_const (.of_body hP
    ((pickBody_ends std pl 0 fun h => absurd rfl h).mono (by unfold cPick; omega) ?_)) hc
  rintro σ' ⟨hcells, hrest⟩
  refine ⟨fun i hi => ?_, hrest⟩
  rw [hcells i (lt_of_lt_of_le hi (length_restrictList_le _ _ _)), pickTarget, if_pos rfl, zero_add,
    List.getD_eq_getElem _ _ hi]

/-- **pick, adding**: a call with add = 1 adds the values of the codes of the small list to the
cells from pDst on and changes no other cell, in at most cPick (small.length + big.length + 1)
steps. -/
theorem pickAdd_entry (std : Std lim) (hP : P[pPick]? = some pickBody) {c : ℕ} (hc : cPick ≤ c) :
    PickAddSpec lim P c := by
  intro x acc μ pl hacc hlen hword d _
  have hle := length_restrictList_le x.big x.values x.small
  refine .mono_const (.of_body hP
    ((pickBody_ends std pl 1 fun _ i hi => ?_).mono (by unfold cPick; omega) ?_)) hc
  · have hia : i < acc.length := by omega
    have hsum := hword _ (List.getElem_mem (l := List.zipWith (· + ·) acc _) (n := i)
      (by simp; omega))
    rwa [List.getElem_zipWith, ← hacc i hia, ← List.getD_eq_getElem _ 0 hi] at hsum
  · rintro σ' ⟨hcells, hrest⟩
    refine ⟨fun i hi => ?_, hrest⟩
    have hi' : i < acc.length ∧ i < (Spec.restrictList x.big x.values x.small).length := by
      simpa using hi
    rw [hcells i (by omega), pickTarget, if_neg (by omega), List.getElem_zipWith, hacc i hi'.1,
      List.getD_eq_getElem _ _ hi'.2]

end Light.Sec2
