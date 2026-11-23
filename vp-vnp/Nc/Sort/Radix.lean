/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Radix sort and the check of neighbours

Records are pairs of a flag (false: entry of the table, true: lookup) and a key of n letters. After one pass
for every letter, records with equal keys are neighbours, in the original order. So every lookup has the key of
an entry of the table before it if and only if, after sorting, every lookup has the same key as the record
before it.
-/

set_option linter.unusedSectionVars false

namespace Nc.Sort

variable {n : ℕ} {B : Type*} [DecidableEq B]

/-- A record: a flag and a key. -/
abbrev Rc (n : ℕ) (B : Type*) := Bool × (Fin n → B)

/-- One pass: distribute by letter j, collect. -/
def pass (bs : List B) (j : Fin n) (l : List (Rc n B)) : List (Rc n B) :=
  bs.flatMap fun b => l.filter fun r => r.2 j = b

/-- The list after the first j passes. -/
def srt (bs : List B) (l : List (Rc n B)) : ℕ → List (Rc n B)
  | 0 => l
  | j + 1 => if h : j < n then pass bs ⟨j, h⟩ (srt bs l j) else srt bs l j

/-- The keys of length j, in the order of the sort. -/
def keys (bs : List B) : ℕ → List (List B)
  | 0 => [[]]
  | j + 1 => bs.flatMap fun b => (keys bs j).map fun k => k ++ [b]

theorem mem_keys {bs : List B} (hbs : ∀ b, b ∈ bs) (j : ℕ) (k : List B) : k ∈ keys bs j ↔ k.length = j := by
  induction j generalizing k with
  | zero => simp [keys]
  | succ j ih =>
    simp only [keys, List.mem_flatMap, List.mem_map, ih]
    constructor
    · rintro ⟨b, -, k, rfl, rfl⟩
      simp
    · intro h
      rcases List.eq_nil_or_concat k with rfl | ⟨k', b, rfl⟩
      · simp at h
      · exact ⟨b, hbs b, k', by simpa using h, by simp⟩

theorem keys_nodup {bs : List B} (hn : bs.Nodup) (j : ℕ) : (keys bs j).Nodup := by
  induction j with
  | zero => simp [keys]
  | succ j ih =>
    rw [keys, List.nodup_flatMap]
    refine ⟨fun b _ => ih.map fun a b h => by simpa using h, ?_⟩
    refine List.Pairwise.imp ?_ hn
    intro b b' hne
    rw [Function.onFun, List.disjoint_left]
    intro k hk hk'
    simp only [List.mem_map] at hk hk'
    obtain ⟨a, -, rfl⟩ := hk
    obtain ⟨a', -, h⟩ := hk'
    have := List.append_inj' h rfl
    simp at this
    exact hne this.2.symm

theorem srt_eq (bs : List B) (l : List (Rc n B)) (j : ℕ) (hj : j ≤ n) :
    srt bs l j = (keys bs j).flatMap fun k => l.filter fun r => (List.ofFn r.2).take j = k := by
  induction j with
  | zero => simp [srt, keys]
  | succ j ih =>
    have hlt : j < n := hj
    rw [srt, dif_pos hlt, ih hlt.le, pass, keys, List.flatMap_assoc]
    refine List.flatMap_congr fun b _ => ?_
    rw [List.filter_flatMap, List.flatMap_map]
    refine List.flatMap_congr fun k hk => ?_
    rw [List.filter_filter]
    refine List.filter_congr fun r _ => ?_
    have h1 : (List.ofFn r.2).take (j + 1) = (List.ofFn r.2).take j ++ [r.2 ⟨j, hlt⟩] := by
      rw [List.take_succ_eq_append_getElem (by simpa using hlt)]
      simp
    rw [h1]
    by_cases e1 : (List.ofFn r.2).take j = k
    · subst e1; simp
    · have : ¬ ((List.ofFn r.2).take j ++ [r.2 ⟨j, hlt⟩] = k ++ [b]) := by
        intro h
        exact e1 (List.append_inj' h rfl).1
      simp [e1, this]

/-- The check of neighbours. -/
def chk : Option (Fin n → B) → List (Rc n B) → Prop
  | _, [] => True
  | p, r :: l => (r.1 = false ∨ p = some r.2) ∧ chk (some r.2) l

/-- The first record of the list is an entry of the table. -/
def headOk : List (Rc n B) → Prop
  | [] => True
  | r :: _ => r.1 = false

theorem chk_same (k : Fin n → B) (g l : List (Rc n B)) (hg : ∀ r ∈ g, r.2 = k) :
    chk (some k) (g ++ l) ↔ chk (some k) l := by
  induction g with
  | nil => rfl
  | cons r g ih =>
    have : r.2 = k := hg r (by simp)
    rw [List.cons_append, chk, this]
    simp [ih fun r hr => hg r (by simp [hr])]

theorem chk_groups (K : List (Fin n → B)) (hK : K.Nodup) (g : (Fin n → B) → List (Rc n B))
    (hg : ∀ k, ∀ r ∈ g k, r.2 = k) (p : Option (Fin n → B)) (hp : ∀ k ∈ K, p ≠ some k) :
    chk p (K.flatMap g) ↔ ∀ k ∈ K, headOk (g k) := by
  induction K generalizing p with
  | nil => simp [chk]
  | cons k K ih =>
    rw [List.nodup_cons] at hK
    rw [List.flatMap_cons, List.forall_mem_cons]
    rcases hgk : g k with _ | ⟨r, g'⟩
    · rw [List.nil_append, ih hK.2 p fun k' hk' => hp k' (by simp [hk'])]
      simp [headOk]
    · have hr : r.2 = k := hg k r (by simp [hgk])
      have hpk := hp k (by simp)
      rw [List.cons_append, chk, hr, chk_same k _ _ fun r' hr' => hg k r' (by simp [hgk, hr']),
        ih hK.2 (some k) fun k' hk' h => hK.1 (by
          have := Option.some_injective _ h
          rwa [this])]
      simp [headOk, hpk]

theorem flatMap_pmap_eq {α β γ : Type*} {P : α → Prop} (f : ∀ a, P a → β) (g : β → List γ)
    (g' : α → List γ) (l : List α) (H : ∀ a ∈ l, P a) (h : ∀ a (ha : P a), g (f a ha) = g' a) :
    (l.pmap f H).flatMap g = l.flatMap g' := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.pmap_cons, List.flatMap_cons, List.flatMap_cons, h, ih]

theorem chk_srt {bs : List B} (hbs : ∀ b, b ∈ bs) (hn : bs.Nodup) (l : List (Rc n B)) :
    chk none (srt bs l n) ↔ ∀ k, headOk (l.filter fun r => r.2 = k) := by
  have e : srt bs l n = ((keys bs n).pmap (fun k (hk : k.length = n) => fun i : Fin n => k.get (i.cast hk.symm))
      fun k hk => (mem_keys hbs n k).1 hk).flatMap fun k => l.filter fun r => r.2 = k := by
    rw [srt_eq bs l n le_rfl]
    symm
    refine flatMap_pmap_eq _ _ _ _ _ fun k hk => List.filter_congr fun r _ => ?_
    have : r.2 = (fun i : Fin n => k.get (i.cast hk.symm)) ↔ (List.ofFn r.2).take n = k := by
      rw [List.take_of_length_le (by simp)]
      subst hk
      constructor
      · intro h
        rw [h]
        exact List.ofFn_get k
      · intro h
        funext i
        have h2 : (List.ofFn r.2).get (i.cast (by simp)) = r.2 i := by simp
        rw [← h2, List.get_of_eq h]
        rfl
    simp only [this]
  rw [e, chk_groups]
  · constructor
    · intro h k
      refine h k ?_
      rw [List.mem_pmap]
      refine ⟨List.ofFn k, (mem_keys hbs _ _).2 (by simp), ?_⟩
      funext i
      simp
    · intro h k _
      exact h k
  · refine List.Nodup.pmap ?_ (keys_nodup hn n)
    intro a ha b hb h
    refine List.ext_get (by rw [ha, hb]) fun i h1 h2 => ?_
    have := congrFun h ⟨i, ha ▸ h1⟩
    simpa using this
  · intro k r hr
    simpa using (List.mem_filter.1 hr).2
  · intro k _
    simp

/-- First the table, then the lookups: the check succeeds if and only if every lookup is in the table. -/
theorem chk_table {bs : List B} (hbs : ∀ b, b ∈ bs) (hn : bs.Nodup) (T L : List (Fin n → B)) :
    chk none (srt bs (T.map (fun x => (false, x)) ++ L.map fun x => (true, x)) n) ↔ ∀ x ∈ L, x ∈ T := by
  rw [chk_srt hbs hn]
  have h1 : ∀ k, (T.map (fun x => ((false, x) : Rc n B)) ++ L.map fun x => (true, x)).filter
      (fun r => r.2 = k) = (T.filter (· = k)).map (fun x => (false, x)) ++
        (L.filter (· = k)).map fun x => (true, x) := by
    intro k
    rw [List.filter_append, List.filter_map, List.filter_map]
    rfl
  simp only [h1]
  constructor
  · intro h x hx
    have := h x
    by_contra hT
    have e : T.filter (· = x) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha
      simp only [decide_eq_true_eq]
      rintro rfl
      exact hT ha
    have hx' : x ∈ L.filter (· = x) := by simp [hx]
    rw [e] at this
    rcases hL : L.filter (· = x) with _ | ⟨a, l⟩
    · rw [hL] at hx'; simp at hx'
    · rw [hL] at this
      simp [headOk] at this
  · intro h k
    rcases hT : T.filter (· = k) with _ | ⟨a, l⟩
    · have : L.filter (· = k) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        simp only [decide_eq_true_eq]
        rintro rfl
        have := h a ha
        have h2 : a ∈ T.filter (· = a) := by simp [this]
        rw [hT] at h2
        simp at h2
      simp [this, headOk]
    · simp [headOk]

theorem sum_filter [Fintype B] (j : Fin n) (l : List (Rc n B)) :
    ∑ b, (l.filter fun r => r.2 j = b).length = l.length := by
  induction l with
  | nil => simp
  | cons r l ih =>
    have : ∀ b, ((r :: l).filter fun r => r.2 j = b).length =
        (if r.2 j = b then 1 else 0) + (l.filter fun r => r.2 j = b).length := by
      intro b
      rw [List.filter_cons]
      by_cases h : r.2 j = b
      · simp [h, add_comm]
      · simp [h]
    simp only [this, Finset.sum_add_distrib, ih]
    simp [add_comm]

theorem length_pass [Fintype B] {bs : List B} (hbs : ∀ b, b ∈ bs) (hn : bs.Nodup) (j : Fin n)
    (l : List (Rc n B)) : (pass bs j l).length = l.length := by
  rw [pass, List.length_flatMap, ← List.sum_toFinset _ hn]
  have : bs.toFinset = Finset.univ := by ext b; simp [hbs]
  rw [this, sum_filter]

theorem length_srt [Fintype B] {bs : List B} (hbs : ∀ b, b ∈ bs) (hn : bs.Nodup)
    (l : List (Rc n B)) (j : ℕ) : (srt bs l j).length = l.length := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [srt]
    split_ifs with h
    · rw [length_pass hbs hn, ih]
    · exact ih

end Nc.Sort
