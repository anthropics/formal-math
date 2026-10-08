/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts

/-!
# Inserting a string into a trie (Lemma 29)

"inserting them into the trie also takes O(L) operations per box, and adds at most L vertices per
box."  New vertices are taken from the end of the part of the trie area that is in use, whose length
is kept in the cell fp.  No routine relies on what the free part of the area holds: the eleven cells
of a new vertex are cleared.  Addresses are relative to the base of the area, so the models are
`Spec.trieNew` and `Spec.trieInsert`.

1. `Ends.clearLoop` is the rule for the loop that clears cells.  `TrieMem.new` and `TrieMem.set`
   say what the trie area holds after a new vertex has been cleared and after a cell has been
   written.
2. `newRoot_spec`: a new vertex as a root.
3. `alloc_spec`: a new vertex as a child.  `Insertion.child` is the array after the test for the
   child, and `Insertion.Progress.step` says that the insertion goes on from the child in that
   array.
4. `insert_spec`: the loop goes down one level in each round (`Insertion.Inv`,
   `Insertion.round_spec`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Clearing cells -/

/-- Writes 0 into the cells from the address in local x up to, and not including, the address in
local y. -/
def clearLoop (x y : ℕ) : Stmt :=
  .while (v x <' v y) (
    .store (v x) (k 0) ;;
    .set x (v x +' k 1))

/-- **The rule for clearLoop.**  The loop clears the n cells from a and changes no local but x. -/
theorem Ends.clearLoop (hs : Std lim) {x y a n T : ℕ} {loc μ : ℕ → ℤ} {Q : State → Prop}
    (hxy : y ≠ x) (hx : loc x = a) (hy : loc y = (a + n : ℕ)) (ha : a + n < lim.space)
    (done : Q ⟨Function.update loc x ((a + n : ℕ) : ℤ), wrote μ a (fun _ => 0) n⟩)
    (hT : n * 11 + 4 ≤ T := by light_time) : Ends lim P d (clearLoop x y) ⟨loc, μ⟩ T Q := by
  light_facts hs
  refine Ends.whileBlock (fun j σ => σ = ⟨Function.update loc x ((a + j : ℕ) : ℤ),
    wrote μ a (fun _ => 0) j⟩) n ?start ?round ?done hT
  case start => rw [wrote_zero, Nat.add_zero, ← hx, Function.update_eq_self]
  case round =>
    rintro j _ hj rfl
    have haddr : ((a : ℤ) + j).toNat = a + j := by omega
    refine ⟨by simp, by simp [hxy, hy]; omega, by light_side, ?_⟩
    rw [← wrote_succ]
    simp [haddr, add_assoc]
  case done =>
    rintro _ rfl
    exact ⟨by simp, by simp [hxy, hy], done⟩

/-- The cells that have been cleared. -/
private theorem seg_wrote_zero (μ : ℕ → ℤ) (a n : ℕ) :
    Seg (wrote μ a (fun _ => 0) n) a (List.replicate n 0) := fun i hi => by
  rw [wrote_done (by simpa using hi), List.getElem_replicate]

/-! ## The trie area -/

section

variable {μ μ₁ : ℕ → ℤ} {tr cap fp : ℕ} {T : List ℤ}

/-- The trie area after a new vertex has been cleared behind the part in use and the free pointer
has been moved. -/
theorem TrieMem.new (h : TrieMem μ tr cap fp T) (hcap : T.length + 11 ≤ cap) :
    TrieMem (Function.update (wrote μ (tr + T.length) (fun _ => 0) 11) fp ((T.length + 11 : ℕ) : ℤ))
        tr cap fp (trieNew T) ∧
      SameOutsideTrie μ
        (Function.update (wrote μ (tr + T.length) (fun _ => 0) 11) fp ((T.length + 11 : ℕ) : ℤ))
        tr cap fp := by
  have hfp := h.fp_out
  have hsame : SameOutside μ (wrote μ (tr + T.length) (fun _ => 0) 11) (tr + T.length) 11 :=
    sameOutside_wrote le_rfl
  refine ⟨⟨?_, ?_, ?_, hfp⟩, fun b ⟨hb, hbfp⟩ => ?_⟩
  · refine Seg.update_out (seg_append.2
      ⟨h.seg.keep, seg_wrote_zero _ _ _⟩) ?_ _
    rw [List.length_append, List.length_replicate]
    omega
  · rw [Function.update_self, length_trieNew]
  · rw [length_trieNew]
    exact hcap
  · rw [Function.update_of_ne hbfp]
    exact hsame b (by omega)

/-- Writing into a cell of the part of the trie area that is in use. -/
theorem TrieMem.set (h : TrieMem μ tr cap fp T) {q : ℕ} (hq : q < T.length) (x : ℤ) :
    TrieMem (Function.update μ (tr + q) x) tr cap fp (T.set q x) ∧
      SameOutsideTrie μ (Function.update μ (tr + q) x) tr cap fp := by
  have hfp := h.fp_out
  have hcap := h.le_cap
  refine ⟨⟨h.seg.update_in hq x, ?_, by simpa using hcap, hfp⟩,
    fun b hb => Function.update_of_ne (by omega) _ _⟩
  rw [Function.update_of_ne (by omega), h.free, List.length_set]

end

/-! ## A new root -/

namespace NewRoot

/-- The local variables of newRoot: the arguments (the base of the trie area and the address of the
free pointer), the address of the new vertex, and the two ends of its cells in the memory.  Local 0
also takes the result. -/
abbrev Area : ℕ := 0
@[inherit_doc Area] abbrev Result : ℕ := 0
@[inherit_doc Area] abbrev Free : ℕ := 1
@[inherit_doc Area] abbrev New : ℕ := 2
@[inherit_doc Area] abbrev From : ℕ := 3
@[inherit_doc Area] abbrev Upto : ℕ := 4

end NewRoot

open NewRoot in
/-- newRoot(area, free): take a new vertex from the end of the part in use, clear its cells, move
the free pointer, and return the address of the vertex. -/
def newRootBody : Stmt :=
  .set New (M (v Free)) ;;
  .set From (v Area +' v New) ;;
  .set Upto (v From +' k 11) ;;
  clearLoop From Upto ;;
  .store (v Free) (v New +' k 11) ;;
  .set Result (v New)

/-- **newRoot** appends a new vertex to the array, and returns its address. -/
theorem newRoot_spec (hP : P[Proc.newRoot]? = some newRootBody) (hs : Std lim) :
    NewRootSpec lim P := by
  intro tr cap fp T μ hT hcap htr hfp
  refine fun d _ => ⟨newRootBody, hP, ?_⟩
  have hfree := hT.free
  light_facts hs
  unfold tNewRoot
  -- new := mem[free]; from := area + new; upto := from + 11
  light_set T.length using hfree
  light_set (tr + T.length : ℕ)
  light_set (tr + T.length + 11 : ℕ)
  -- clear the cells of the new vertex
  refine Ends.next _ (Ends.clearLoop hs (a := tr + T.length) (n := 11) (by decide) rfl rfl
    (by omega) ?_ (hT := le_rfl))
  rw [update_frame_setLocal]
  -- mem[free] := new + 11
  light_store fp (T.length + 11 : ℕ)
  -- return new
  light_set T.length
  exact ⟨rfl, hT.new hcap⟩

/-! ## A new child -/

namespace Insertion

/-- The local variables of insert: the arguments (the base of the trie area, the root, which becomes
the current vertex, the address of the string, its length, the value, the address of the free
pointer), the level, the address of the cell with the pointer to the child, and, for a new vertex,
its address and the two ends of its cells in the memory. -/
abbrev Area : ℕ := 0
@[inherit_doc Area] abbrev Vertex : ℕ := 1
@[inherit_doc Area] abbrev Key : ℕ := 2
@[inherit_doc Area] abbrev Len : ℕ := 3
@[inherit_doc Area] abbrev Value : ℕ := 4
@[inherit_doc Area] abbrev Free : ℕ := 5
@[inherit_doc Area] abbrev Level : ℕ := 6
@[inherit_doc Area] abbrev Cell : ℕ := 7
@[inherit_doc Area] abbrev New : ℕ := 8
@[inherit_doc Area] abbrev From : ℕ := 9
@[inherit_doc Area] abbrev Upto : ℕ := 10

end Insertion

open Insertion

/-- A new vertex as the child in the current cell. -/
def allocStmt : Stmt :=
  .set New (M (v Free)) ;;
  .store (v Cell) (v New) ;;
  .set From (v Area +' v New) ;;
  .set Upto (v From +' k 11) ;;
  clearLoop From Upto ;;
  .store (v Free) (v New +' k 11)

/-- The time of allocStmt. -/
def tAlloc : ℕ := 144

/-- The new vertex becomes the child in the cell q.  Only the last three locals change. -/
private theorem alloc_spec (hs : Std lim) {tr cap fp q p key L i : ℕ} {val x₈ x₉ x₁₀ : ℤ}
    {T : List ℤ} {μ : ℕ → ℤ} (hT : TrieMem μ tr cap fp T) (hq : q < T.length)
    (hcap : T.length + 11 ≤ cap)
    (htr : tr + cap < lim.space) (hfp : fp < lim.space) :
    Ends lim P d allocStmt ⟨frame [tr, p, key, L, val, fp, i, (tr + q : ℕ), x₈, x₉, x₁₀], μ⟩
      tAlloc
      fun σ' => ∃ (y₈ y₉ y₁₀ : ℤ) (μ' : ℕ → ℤ),
        σ' = ⟨frame [tr, p, key, L, val, fp, i, (tr + q : ℕ), y₈, y₉, y₁₀], μ'⟩ ∧
          TrieMem μ' tr cap fp (trieNew (T.set q T.length)) ∧ SameOutsideTrie μ μ' tr cap fp := by
  have hfree := hT.free
  light_facts hs
  obtain ⟨hset, hsame⟩ := hT.set hq (T.length : ℤ)
  have hnew := hset.new (by rw [List.length_set]; exact hcap)
  rw [List.length_set] at hnew
  unfold tAlloc
  -- new := mem[free]
  light_set T.length using hfree
  -- mem[cell] := new
  light_store (tr + q) T.length
  -- from := area + new; upto := from + 11
  light_set (tr + T.length : ℕ)
  light_set (tr + T.length + 11 : ℕ)
  -- clear the cells of the new vertex
  refine Ends.next _ (Ends.clearLoop hs (a := tr + T.length) (n := 11) (by decide) rfl rfl
    (by omega) ?_ (hT := le_rfl))
  rw [update_frame_setLocal]
  -- mem[free] := new + 11
  light_store fp (T.length + 11 : ℕ)
  exact ⟨_, _, _, _, rfl, hnew.1, hsame.trans hnew.2⟩

/-! ## Insertion -/

/-- One round: find the cell with the pointer to the child, make a new child if there is none, and
go down to the child. -/
def insertRound : Stmt :=
  .set Cell (v Area +' v Vertex +' M (v Key +' v Level)) ;;
  .ite (M (v Cell) =' k 0) allocStmt .skip ;;
  .set Vertex (M (v Cell))

/-- insert(area, root, key, len, value, free): go down the string, making new children where there
are none, and write the value into the vertex that is reached. -/
def insertBody : Stmt :=
  Stmt.for Level (v Len) insertRound ;;
  .store (v Area +' v Vertex) (v Value)

namespace Insertion

/-- The pointer to a new child, read back from the array. -/
private theorem getD_trieNew_set {T : List ℤ} {q : ℕ} (hq : q < T.length) (x : ℤ) :
    (trieNew (T.set q x)).getD q 0 = x := by
  rw [trieNew, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hq),
    List.getElem?_set_self hq]
  rfl

/-- The array after the test for the child in the cell q: a new vertex has been appended if there
was no child. -/
def child (T : List ℤ) (q : ℕ) : List ℤ :=
  if T.getD q 0 = 0 then trieNew (T.set q T.length) else T

/-- After i levels the array is Ti and the current vertex p: what is left is the insertion of the
rest of the string from p. -/
structure Progress (T : List ℤ) (root : ℕ) (kl : List ℕ) (val : ℤ) (i : ℕ) (Ti : List ℤ) (p : ℕ) :
    Prop where
  ok : InsertOK Ti p (kl.drop i)
  eq : trieInsert T root kl val = trieInsert Ti p (kl.drop i) val
  /-- Each level has added at most one vertex. -/
  len : Ti.length ≤ T.length + 11 * i

section

variable {T Ti : List ℤ} {root i p : ℕ} {kl : List ℕ} {val : ℤ}

/-- The current vertex lies inside the array. -/
theorem Progress.inside (h : Progress T root kl val i Ti p) : p + 11 ≤ Ti.length := by
  have hok := h.ok
  generalize kl.drop i = rest at hok
  cases rest with
  | nil => exact hok.2
  | cons x rest => exact hok.2.1

/-- One level down: in the array with the child, the pointer to the child is positive, and the
insertion goes on from the child. -/
theorem Progress.step (h : Progress T root kl val i Ti p) (hi : i < kl.length)
    (hsym : kl[i] < 11) :
    0 < (child Ti (p + kl[i])).getD (p + kl[i]) 0 ∧
      Progress T root kl val (i + 1) (child Ti (p + kl[i]))
        ((child Ti (p + kl[i])).getD (p + kl[i]) 0).toNat := by
  have hin := h.inside
  have hlen := h.len
  have hok := h.ok
  have heq := h.eq
  rw [List.drop_eq_getElem_cons hi] at hok heq
  rw [trieInsert] at heq
  obtain ⟨hpos, -, hbranch⟩ := hok
  unfold child
  by_cases hz : Ti.getD (p + kl[i]) 0 = 0
  · -- there is no child: a new vertex at the end of the array
    rw [if_pos hz] at hbranch heq ⊢
    rw [getD_trieNew_set (by omega), Int.toNat_natCast]
    exact ⟨by omega, hbranch, heq, by rw [length_trieNew, List.length_set]; omega⟩
  · -- the child exists
    rw [if_neg hz] at hbranch heq ⊢
    exact ⟨hbranch.1, hbranch.2, heq, by omega⟩

end

/-- Before round i: the area holds an array Ti, the current vertex is p, and what is left is as
`Progress` says; outside the trie area nothing has changed. -/
def Inv (x : InsertArgs) (μ : ℕ → ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (Ti : List ℤ) (p : ℕ) (x₇ x₈ x₉ x₁₀ : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.tr, p, x.key, x.kl.length, x.val, x.fp, i, x₇, x₈, x₉, x₁₀], μ'⟩ ∧
      Progress x.T x.root x.kl x.val i Ti p ∧ TrieMem μ' x.tr x.cap x.fp Ti ∧
        SameOutsideTrie μ μ' x.tr x.cap x.fp

section

variable {x : InsertArgs} {i p q : ℕ} {x₇ x₈ x₉ x₁₀ : ℤ} {Ti : List ℤ} {μ μ' : ℕ → ℤ}

/-- The time of a round: the cell, the test, a new vertex, and the step down. -/
def tRound : ℕ := tAlloc + 17

/-- The end of a round, once the area holds the array with the child: vertex := mem[cell].  The
conclusion has the form that the rule for counting loops asks for: the loop itself then raises the
level. -/
private theorem down_spec (C : InsertPre lim μ x) {t : ℕ} (ht : 3 ≤ t)
    (hq : q < Ti.length) (hchild : 0 < (child Ti q).getD q 0)
    (hnext : Progress x.T x.root x.kl x.val (i + 1) (child Ti q) ((child Ti q).getD q 0).toNat)
    (hmem : TrieMem μ' x.tr x.cap x.fp (child Ti q))
    (hsame : SameOutsideTrie μ μ' x.tr x.cap x.fp) :
    Ends lim P d (.set Vertex (M (v Cell)))
      ⟨frame [x.tr, p, x.key, x.kl.length, x.val, x.fp, i, (x.tr + q : ℕ), x₈, x₉, x₁₀], μ'⟩ t
      fun σ' => σ'.loc Level = i ∧ Inv x μ (i + 1)
        { σ' with loc := Function.update σ'.loc Level ((i : ℤ) + 1) } := by
  light_facts C hmem
  have hq' : q < (child Ti q).length := by
    unfold child
    split_ifs
    · rw [length_trieNew, List.length_set]
      omega
    · exact hq
  have hread := hmem.seg.getD hq' 0
  generalize (child Ti q).getD q 0 = c at hchild hnext hread
  light_set (c.toNat : ℕ) using hread
  exact ⟨rfl, _, _, _, _, _, _, _, by rw [update_frame_setLocal]; rfl, hnext, hmem, hsame⟩

/-- One round goes down one level, with a new child if there was none. -/
private theorem round_spec (hs : Std lim) (C : InsertPre lim μ x) (hi : i < x.kl.length)
    (hprog : Progress x.T x.root x.kl x.val i Ti p) (hmem : TrieMem μ' x.tr x.cap x.fp Ti)
    (hsame : SameOutsideTrie μ μ' x.tr x.cap x.fp) :
    Ends lim P d insertRound
      ⟨frame [x.tr, p, x.key, x.kl.length, x.val, x.fp, i, x₇, x₈, x₉, x₁₀], μ'⟩ tRound
      fun σ' => σ'.loc Level = i ∧ Inv x μ (i + 1)
        { σ' with loc := Function.update σ'.loc Level ((i : ℤ) + 1) } := by
  have hroom := C.room
  have harea := C.area_in
  have hin := hprog.inside
  light_facts C hmem hprog hs
  have hsym : x.kl[i] < 11 := C.digits _ (List.getElem_mem hi)
  obtain ⟨hchild, hnext⟩ := hprog.step hi hsym
  have hcell : μ' (x.key + i) = (x.kl[i] : ℕ) :=
    (hsame _ ⟨by omega, by omega⟩).trans (C.seg.getElem hi)
  have hq : p + x.kl[i] < Ti.length := by omega
  unfold tRound
  -- cell := area + vertex + mem[key + level]
  light_set (x.tr + (p + x.kl[i]) : ℕ) using hcell
  generalize p + x.kl[i] = q at hchild hnext hq ⊢
  have hptr : μ' (x.tr + q) = Ti.getD q 0 := hmem.seg.getD hq 0
  -- if mem[cell] = 0
  refine Ends.iteThen (fun hz => ?_) (fun hz => ?_) (by light_side)
  · -- there is no child: a new vertex
    have hz' : Ti.getD q 0 = 0 := by
      rw [← hptr]
      simpa using hz
    refine Ends.next _ ((alloc_spec hs hmem hq (by omega) harea C.free_in).mono le_rfl ?_)
    rintro _ ⟨y₈, y₉, y₁₀, μ₂, rfl, hmem₂, hsame₂⟩
    exact down_spec C (by light_time) hq hchild hnext (by rw [child, if_pos hz']; exact hmem₂)
      (hsame.trans hsame₂)
  · -- the child exists
    have hz' : Ti.getD q 0 ≠ 0 := by
      rw [← hptr]
      simpa using hz
    refine Ends.next 0 (Ends.skip ?_)
    exact down_spec C (by light_time) hq hchild hnext (by rw [child, if_neg hz']; exact hmem)
      hsame

end

end Insertion

/-- **insert** stores the value for the string: the area then holds `Spec.trieInsert`. -/
theorem insert_spec (hP : P[Proc.insert]? = some insertBody) (hs : Std lim) :
    InsertSpec lim P := by
  intro x μ pre d _
  refine .of_body hP ?_
  rw [InsertArgs.vals, ← pre.len]
  light_facts hs pre
  unfold tInsert
  -- for level < len
  refine Ends.next _ (Ends.for (Inv x μ) x.kl.length tRound ?start ?round
    ?done ?bound (hT := le_rfl)) (by simp [tRound, tAlloc]; omega)
  case start =>
    exact ⟨x.T, x.root, 0, 0, 0, 0, μ, by rw [update_frame_setLocal, ← frame_append_zeros _ 4]; rfl,
      ⟨pre.walk, rfl, by omega⟩, pre.trie, .refl⟩
  case bound =>
    rintro i _ - - ⟨Ti, p, x₇, x₈, x₉, x₁₀, μ', rfl, -⟩
    simp
  case round =>
    rintro i _ hi - ⟨Ti, p, x₇, x₈, x₉, x₁₀, μ', rfl, hprog, hmem, hsame⟩
    exact round_spec hs pre hi hprog hmem hsame
  case done =>
    rintro _ - ⟨Ti, p, x₇, x₈, x₉, x₁₀, μ', rfl, hprog, hmem, hsame⟩
    have hin := hprog.inside
    have hle := hmem.le_cap
    obtain ⟨hset, hsame'⟩ := hmem.set (q := p) (by omega) x.val
    have heq := hprog.eq
    rw [List.drop_length, trieInsert] at heq
    simp only [tRound, tAlloc]
    -- mem[area + vertex] := value
    light_store (x.tr + p) x.val
    exact ⟨heq ▸ hset, hsame.trans hsame'⟩

end Light.Sec4
