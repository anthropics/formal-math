/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Picks

/-!
# States with named values
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree

section Names

variable {ν : Type} [DecidableEq ν] (nm : ν → List Bool)

open Classical in
/-- Values by path from values by name. -/
noncomputable def byPath (st : ν → Tree) : List Bool → Tree := fun p =>
  if h : ∃ x, nm x = p then st h.choose else .nil

variable {nm} (hnm : Function.Injective nm)

include hnm

theorem byPath_nm (st : ν → Tree) (x : ν) : byPath nm st (nm x) = st x := by
  have h : ∃ y, nm y = nm x := ⟨x, rfl⟩
  rw [byPath, dif_pos h, hnm h.choose_spec]

theorem update_byPath (st : ν → Tree) (x : ν) (v : Tree) :
    Function.update (byPath nm st) (nm x) v = byPath nm (Function.update st x v) := by
  classical
  funext p
  by_cases h : ∃ y, nm y = p
  · obtain ⟨y, rfl⟩ := h
    rw [byPath_nm hnm, Function.update_apply, Function.update_apply, byPath_nm hnm]
    simp only [hnm.eq_iff]
  · rw [Function.update_of_ne]
    · rw [byPath, dif_neg h, byPath, dif_neg h]
    · rintro rfl
      exact h ⟨x, rfl⟩

/-- An option: assignments to names. -/
def optT (nm : ν → List Bool) (o : List (ν × Tree)) : Tree := listT (o.map fun a => .cons (ofBits (nm a.1)) a.2)

/-- Assign. -/
def upds (st : ν → Tree) (o : List (ν × Tree)) : ν → Tree := o.foldl (fun st a => Function.update st a.1 a.2) st

theorem assignS_byPath (st : ν → Tree) (o : List (ν × Tree)) :
    assignS (byPath nm st) (optT nm o) = byPath nm (upds st o) := by
  unfold assignS optT upds
  rw [toList_listT]
  induction o generalizing st with
  | nil => rfl
  | cons a o ih =>
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, hd_cons, tl_cons, path_ofBits, update_byPath hnm, ih]

theorem exec_pick {m : ℕ} {st : ν → Tree} {x : ν} {tab : Tree} {opts : List (List (ν × Tree))}
    (h : (tget (st x).path tab).toList = opts.map (optT nm)) :
    (DStep.pick (nm x) tab).exec m (byPath nm st) = opts.map fun o => byPath nm (upds st o) := by
  rw [DStep.exec, byPath_nm hnm, h, List.map_map]
  exact List.map_congr_left fun o _ => assignS_byPath hnm st o

theorem exec_op {m : ℕ} {st : ν → Tree} {x y z : ν} {φ : Tree} :
    (DStep.op (nm x) (nm y) (nm z) φ).exec m (byPath nm st) =
      [byPath nm (Function.update st z (tget (st y).path (tget (st x).path φ)))] := by
  rw [DStep.exec, byPath_nm hnm, byPath_nm hnm, update_byPath hnm]

theorem exec_bits {m : ℕ} {st : ν → Tree} {x y : ν} :
    (DStep.bits (nm x) (nm y)).exec m (byPath nm st) = if st x = .nil then [byPath nm st] else
      (allBits m).map fun u => byPath nm (Function.update st y (ofBits u.reverse)) := by
  rw [DStep.exec, byPath_nm hnm]
  split_ifs
  · rfl
  · exact List.map_congr_left fun u _ => update_byPath hnm st y _

end Names

section Tries

/-- A trie with given entries. -/
def mkTrie (l : List (List Bool × Tree)) : Tree := l.foldr (fun a t => tset a.1 a.2 t) .nil

/-- A trie for a function on a finite type. -/
noncomputable def trieOf {α : Type} [Fintype α] (code : α → List Bool) (f : α → Tree) : Tree :=
  mkTrie ((Finset.univ : Finset α).toList.map fun a => (code a, f a))

theorem tget_trieOf {α : Type} [Fintype α] {code : α → List Bool} (hc : Function.Injective code) (f : α → Tree) (a : α) :
    tget (code a) (trieOf code f) = f a := by
  have : ∀ l : List α, a ∈ l → tget (code a) (mkTrie (l.map fun a => (code a, f a))) = f a := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih =>
      intro h
      rw [List.map_cons, mkTrie, List.foldr_cons, tget_tset]
      by_cases hab : a = b
      · subst hab
        simp
      · rw [if_neg fun h => hab (hc h)]
        exact ih ((List.mem_cons.1 h).resolve_left hab)
  exact this _ (Finset.mem_toList.2 (Finset.mem_univ a))

theorem size_tset (p : List Bool) (v t : Tree) : (tset p v t).size ≤ t.size + v.size + 4 * p.length + 4 := by
  induction p generalizing t with
  | nil =>
    have := size_tl_le t
    simp only [tset, Tree.size, List.length_nil]
    omega
  | cons b p ih =>
    cases t with
    | nil =>
      cases b
      · have := ih .nil
        simp only [tset, tl_nil, hd_nil, Tree.size, List.length_cons] at this ⊢
        omega
      · have := ih .nil
        simp only [tset, tl_nil, hd_nil, Tree.size, List.length_cons] at this ⊢
        omega
    | cons a t =>
      cases t with
      | nil =>
        cases b
        · have := ih .nil
          simp only [tset, tl_nil, hd_nil, tl_cons, hd_cons, Tree.size, List.length_cons] at this ⊢
          omega
        · have := ih .nil
          simp only [tset, tl_nil, hd_nil, tl_cons, hd_cons, Tree.size, List.length_cons] at this ⊢
          omega
      | cons l r =>
        cases b
        · have := ih l
          simp only [tset, tl_cons, hd_cons, Tree.size, List.length_cons] at this ⊢
          omega
        · have := ih r
          simp only [tset, tl_cons, hd_cons, Tree.size, List.length_cons] at this ⊢
          omega

theorem size_trieOf_le {α : Type} [Fintype α] {code : α → List Bool} {f : α → Tree} {L s : ℕ}
    (hL : ∀ a, (code a).length ≤ L) (hs : ∀ a, (f a).size ≤ s) :
    (trieOf code f).size ≤ Fintype.card α * (s + 4 * L + 4) + 1 := by
  have : ∀ l : List α, (mkTrie (l.map fun a => (code a, f a))).size ≤ l.length * (s + 4 * L + 4) + 1 := by
    intro l
    induction l with
    | nil => simp [mkTrie, Tree.size]
    | cons a l ih =>
      have h1 := size_tset (code a) (f a) (mkTrie (l.map fun a => (code a, f a)))
      have h2 := hL a
      have h3 := hs a
      rw [List.map_cons, mkTrie, List.foldr_cons]
      rw [mkTrie] at ih h1
      simp only [List.length_cons]
      rw [add_mul, one_mul]
      omega
  have h := this (Finset.univ : Finset α).toList
  rwa [Finset.length_toList, Finset.card_univ] at h

end Tries

section Folds

variable {ν ι : Type} [DecidableEq ν] [DecidableEq ι]

/-- The state after assignments for all `i`: every name belongs to at most one `i`. -/
theorem foldl_upds {own : ν → Option ι} {o : ι → List (ν × Tree)} {v : ν → Tree}
    (ho : ∀ i, ∀ a ∈ o i, own a.1 = some i ∧ a.2 = v a.1) (hall : ∀ i x, own x = some i → ∃ a ∈ o i, a.1 = x)
    (s : List ι) (st : ν → Tree) :
    s.foldl (fun st i => upds st (o i)) st = fun x => match own x with
      | none => st x
      | some i => if i ∈ s then v x else st x := by
  classical
  have one : ∀ (l : List (ν × Tree)) (st : ν → Tree) (x : ν), (∀ a ∈ l, a.2 = v a.1) →
      upds st l x = if ∃ a ∈ l, a.1 = x then v x else st x := by
    intro l
    induction l with
    | nil =>
      intro st x _
      simp [upds]
    | cons b l ih =>
      intro st x hl
      have h1 := ih (Function.update st b.1 b.2) x fun a ha => hl a (List.mem_cons_of_mem _ ha)
      rw [upds, List.foldl_cons]
      rw [upds] at h1
      rw [h1]
      by_cases hx : ∃ a ∈ l, a.1 = x
      · rw [if_pos hx, if_pos]
        obtain ⟨a, ha, h⟩ := hx
        exact ⟨a, List.mem_cons_of_mem _ ha, h⟩
      · rw [if_neg hx]
        by_cases hb : b.1 = x
        · rw [if_pos ⟨b, List.mem_cons_self, hb⟩, ← hb, Function.update_self]
          exact hl b List.mem_cons_self
        · rw [if_neg, Function.update_of_ne (Ne.symm hb)]
          rintro ⟨a, ha, h⟩
          rcases List.mem_cons.1 ha with rfl | ha
          · exact hb h
          · exact hx ⟨a, ha, h⟩
  induction s generalizing st with
  | nil =>
    funext x
    cases own x <;> simp
  | cons i s ih =>
    rw [List.foldl_cons, ih]
    funext x
    have h1 := one (o i) st x fun a ha => (ho i a ha).2
    have h2 : (∃ a ∈ o i, a.1 = x) ↔ own x = some i := by
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact (ho i a ha).1
      · exact hall i x
    rw [h1]
    cases hx : own x with
    | none => simp [h2, hx]
    | some j =>
      by_cases hj : j = i
      · subst hj
        simp [h2, hx]
      · have : ¬ (some j = some i) := fun h => hj (Option.some.inj h)
        simp only [h2, hx, this, if_false, List.mem_cons, hj, false_or]

end Folds

end Nc.Dl
