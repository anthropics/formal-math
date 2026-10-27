/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsifyWidthK.Interfaces
import all StepMachines.Math.SparsifyProg
import Mathlib.Data.List.Nodup

/-! # The program of the sparsification of a k-CNF follows the rule on finite sets

`pickK` (`SparsifyWidthK/DefsProg.lean`) works on lists of lists of literals; the rule `Rule` and
the leaves `Leaf` (`SparsifyWidthK/Defs.lean`) are stated for finite sets of
finite sets. A list s in normal form (`NF s`: no literal twice in a clause, no clause twice as a
set) is read as the set `toFin s`. This file proves:
* `overP` and `minusP` compute `over` and set difference, and the list of petals is in normal form;
* the masks pick exactly the sublists of a clause of at most k literals, so every subset of a clause
  is among the candidate hearts;
* the pairs (j, h) are tried with j upwards and, for each j, h downwards; so where `pickK` answers,
  `Rule` holds, and where it does not, `Leaf` holds;
* `rootP ψ` is in normal form and stands for the inclusion-minimal clauses of ψ (two lemmas of
  `StepMachines/Math/SparsifyProg.lean`).
Together these are `stRefines : StRefines`, one of the interface statements of
`SparsifyWidthK/Interfaces.lean`. -/

namespace WidthK.Refine

open Finset Groundwork Groundwork.Sparsify WidthK.Prog

/-! ### Lists in normal form as sets of sets -/

/-- The members of `toFin s` are the clauses of s, read as sets. -/
theorem mem_toFin {s : PFml} {X : Finset PLit} : X ∈ toFin s ↔ ∃ C ∈ s, C.toFinset = X := by
  simp [toFin]

/-- A list in normal form has as many clauses as its set of sets has members. -/
theorem card_toFin {s : PFml} (hs : NF s) : (toFin s).card = s.length := by
  rw [toFin, List.toFinset_card_of_nodup hs.2, List.length_map]

/-- Dropping clauses keeps the normal form. -/
theorem NF_filter {s : PFml} (hs : NF s) (p : PCl → Bool) : NF (s.filter p) :=
  ⟨fun C hC => hs.1 C (List.mem_filter.1 hC).1, (hs.2.sublist (List.filter_sublist.map _))⟩

/-- `subP D C` tests inclusion of the sets of literals. -/
theorem subP_iff' (D C : PCl) : subP D C = true ↔ D.toFinset ⊆ C.toFinset := by
  rw [subP_iff]; simp [Finset.subset_iff]

/-- `overP s j H` lists the clauses of size j that contain H: it computes `over`. -/
theorem toFin_overP {s : PFml} (hs : ∀ C ∈ s, C.Nodup) (j : ℕ) (H : PCl) :
    toFin (overP s j H) = Sparsify.over (toFin s) j H.toFinset := by
  ext X
  simp only [mem_toFin, overP, Sparsify.over, List.mem_filter, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq, subP_iff']
  constructor
  · rintro ⟨C, ⟨hC, hj, hH⟩, rfl⟩
    exact ⟨⟨C, hC, rfl⟩, by rw [List.toFinset_card_of_nodup (hs C hC), hj], hH⟩
  · rintro ⟨⟨C, hC, rfl⟩, hj, hH⟩
    exact ⟨C, ⟨hC, by rw [← hj, List.toFinset_card_of_nodup (hs C hC)], hH⟩, rfl⟩

/-- The number that the search compares with the threshold is the number of clauses of size j over
H. -/
theorem length_overP {s : PFml} (hs : NF s) (j : ℕ) (H : PCl) :
    (overP s j H).length = (Sparsify.over (toFin s) j H.toFinset).card := by
  rw [← toFin_overP hs.1, overP, card_toFin (NF_filter hs _)]

/-- `minusP H C` computes the set difference C ∖ H. -/
theorem toFinset_minusP (H C : PCl) : (minusP H C).toFinset = C.toFinset \ H.toFinset := by
  ext a
  simp [minusP]

/-- The second component of the answer of `tryP` stands for the petals. -/
theorem toFin_petals {s : PFml} (hs : ∀ C ∈ s, C.Nodup) (j : ℕ) (H : PCl) :
    toFin ((overP s j H).map (minusP H)) = (Sparsify.over (toFin s) j H.toFinset).image fun C => C \ H.toFinset := by
  rw [← toFin_overP hs]
  ext X
  simp only [mem_toFin, List.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨C, hC, rfl⟩, rfl⟩
    exact ⟨_, ⟨C, hC, rfl⟩, (toFinset_minusP H C).symm⟩
  · rintro ⟨_, ⟨C, hC, rfl⟩, rfl⟩
    exact ⟨_, ⟨C, hC, rfl⟩, toFinset_minusP H C⟩

/-- The list of petals is in normal form: different clauses over H stay different without H. -/
theorem NF_petals {s : PFml} (hs : NF s) (j : ℕ) (H : PCl) : NF ((overP s j H).map (minusP H)) := by
  refine ⟨?_, ?_⟩
  · intro Q hQ
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hQ
    exact (hs.1 C (List.mem_filter.1 hC).1).filter _
  · rw [List.map_map, overP]
    have h1 := (NF_filter hs (fun C => decide (C.length = j) && subP H C)).2
    rw [List.nodup_map_iff_inj_on ((NF_filter hs _).2.of_map _)] at h1 ⊢
    intro C hC D hD hCD
    apply h1 C hC D hD
    simp only [Function.comp, toFinset_minusP] at hCD
    have hC' : H.toFinset ⊆ C.toFinset := by
      have := (List.mem_filter.1 hC).2
      simp only [Bool.and_eq_true, subP_iff'] at this
      exact this.2
    have hD' : H.toFinset ⊆ D.toFinset := by
      have := (List.mem_filter.1 hD).2
      simp only [Bool.and_eq_true, subP_iff'] at this
      exact this.2
    rw [← Finset.sdiff_union_of_subset hC', ← Finset.sdiff_union_of_subset hD', hCD]


/-! ### The masks and the candidate hearts -/

theorem maskP_nil_left (C : PCl) : maskP [] C = [] := by simp [maskP]
theorem maskP_nil_right (m : List Bool) : maskP m [] = [] := by simp [maskP]
theorem maskP_cons_true (m : List Bool) (a : PLit) (C : PCl) : maskP (true :: m) (a :: C) = a :: maskP m C := by
  simp [maskP]
theorem maskP_cons_false (m : List Bool) (a : PLit) (C : PCl) : maskP (false :: m) (a :: C) = maskP m C := by
  simp [maskP]

/-- A mask picks a sublist. -/
theorem maskP_sublist (m : List Bool) (C : PCl) : (maskP m C).Sublist C := by
  induction C generalizing m with
  | nil => rw [maskP_nil_right]
  | cons a C ih =>
    cases m with
    | nil => rw [maskP_nil_left]; exact List.nil_sublist _
    | cons b m =>
      cases b
      · rw [maskP_cons_false]; exact (ih m).cons _
      · rw [maskP_cons_true]; exact (ih m).cons_cons _

/-- Every sublist of a clause of at most k literals is picked by one of the masks of length k. -/
theorem exists_mask {k : ℕ} {C H : PCl} (hC : C.length ≤ k) (hH : H.Sublist C) : ∃ m ∈ masks k, maskP m C = H := by
  induction k generalizing C H with
  | zero =>
    obtain rfl := List.length_eq_zero_iff.1 (Nat.le_zero.1 hC)
    obtain rfl := List.sublist_nil.1 hH
    exact ⟨[], by simp [masks], maskP_nil_left _⟩
  | succ k ih =>
    cases C with
    | nil =>
      obtain rfl := List.sublist_nil.1 hH
      obtain ⟨m, hm, -⟩ := ih (C := []) (H := []) (Nat.zero_le _) (List.Sublist.refl _)
      exact ⟨false :: m, by simp only [masks, List.mem_flatMap]; exact ⟨m, hm, by simp⟩, maskP_nil_right _⟩
    | cons a C =>
      have hC' : C.length ≤ k := by simpa using hC
      cases hH with
      | cons _ h =>
        obtain ⟨m, hm, e⟩ := ih hC' h
        exact ⟨false :: m, by simp only [masks, List.mem_flatMap]; exact ⟨m, hm, by simp⟩, by rw [maskP_cons_false, e]⟩
      | cons_cons _ h =>
        obtain ⟨m, hm, e⟩ := ih hC' h
        exact ⟨true :: m, by simp only [masks, List.mem_flatMap]; exact ⟨m, hm, by simp⟩, by rw [maskP_cons_true, e]⟩

/-- The candidate hearts are exactly the sublists of length h of the clauses of length j. -/
theorem mem_heartsP {k : ℕ} {s : PFml} {j h : ℕ} {H : PCl} (hj : j ≤ k) :
    H ∈ heartsP k s j h ↔ ∃ C ∈ s, C.length = j ∧ H.Sublist C ∧ H.length = h := by
  simp only [heartsP, List.mem_flatMap, List.mem_filter, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨C, ⟨hC, hCj⟩, ⟨m, -, rfl⟩, hh⟩
    exact ⟨C, hC, hCj, maskP_sublist m C, hh⟩
  · rintro ⟨C, hC, hCj, hsub, hh⟩
    obtain ⟨m, hm, e⟩ := exists_mask (hCj.le.trans hj) hsub
    exact ⟨C, ⟨hC, hCj⟩, ⟨m, hm, e⟩, hh⟩

/-! ### The order of the search -/

/-- The pairs that are tried: 1 ≤ h < j ≤ k. -/
theorem mem_pairsK {k : ℕ} {jh : ℕ × ℕ} : jh ∈ pairsK k ↔ 0 < jh.2 ∧ jh.2 < jh.1 ∧ jh.1 ≤ k := by
  obtain ⟨j, h⟩ := jh
  simp only [pairsK, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter, List.mem_reverse, decide_eq_true_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨j', hj', h', ⟨h1, h2⟩, rfl, rfl⟩
    exact ⟨h2, h1, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨j, by omega, h, ⟨h2, h1⟩, rfl, rfl⟩

/-- The pair x = (j', h') comes before y = (j, h) in the search: j' < j, or j' = j and h' > h. -/
def Before (x y : ℕ × ℕ) : Prop := x.1 < y.1 ∨ (x.1 = y.1 ∧ y.2 < x.2)

/-- `pairsK k` lists its pairs in the order `Before`. -/
theorem pairwise_pairsK (k : ℕ) : (pairsK k).Pairwise Before := by
  rw [pairsK, List.pairwise_flatMap]
  refine ⟨fun j _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    refine List.Pairwise.filter _ ?_
    rw [List.pairwise_reverse]
    exact (List.pairwise_lt_range (n := j)).imp fun {a b} hab => Or.inr ⟨rfl, hab⟩
  · refine (List.pairwise_lt_range (n := k + 1)).imp fun {a b} hab x hx y hy => ?_
    obtain ⟨_, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨_, -, rfl⟩ := List.mem_map.1 hy
    exact Or.inl hab

/-- If `(l.filterMap f).head?` is `some b`, then b is the result of f at some entry of l, and f has
no result at the entries before it. -/
theorem head?_filterMap_eq_some {α β : Type*} {f : α → Option β} {l : List α} {b : β}
    (h : (l.filterMap f).head? = some b) : ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ f a = some b ∧ ∀ x ∈ l₁, f x = none := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    cases hf : f a with
    | some c =>
      rw [List.filterMap_cons_some hf, List.head?_cons, Option.some.injEq] at h
      exact ⟨[], a, l, rfl, h ▸ hf, by simp⟩
    | none =>
      rw [List.filterMap_cons_none hf] at h
      obtain ⟨l₁, a', l₂, e, h1, h2⟩ := ih h
      refine ⟨a :: l₁, a', l₂, by rw [e]; rfl, h1, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hf
      · exact h2 x hx

/-- If `(l.filterMap f).head?` is `none`, then f has no result at any entry of l. -/
theorem head?_filterMap_eq_none {α β : Type*} {f : α → Option β} {l : List α}
    (h : (l.filterMap f).head? = none) : ∀ x ∈ l, f x = none := by
  rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff] at h
  exact h

/-- An answer of `pickK` is the answer of `tryP` at some pair, and `tryP` has no answer at the pairs
that come before it. -/
theorem pickK_some {θ : ℕ → ℕ} {k : ℕ} {s : PFml} {HP : PCl × PFml} (h : pickK θ k s = some HP) :
    ∃ jh ∈ pairsK k, tryP θ k s jh = some HP ∧ ∀ x ∈ pairsK k, Before x jh → tryP θ k s x = none := by
  obtain ⟨l₁, jh, l₂, e, h1, h2⟩ := head?_filterMap_eq_some h
  refine ⟨jh, by rw [e]; simp, h1, fun x hx hb => ?_⟩
  have hp := pairwise_pairsK k
  rw [e] at hx hp
  rw [List.pairwise_append, List.pairwise_cons] at hp
  rcases List.mem_append.1 hx with hx | hx
  · exact h2 x hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · rcases hb with hb | hb <;> omega
    · have := hp.2.1.1 x hx
      rcases hb with hb | hb <;> rcases this with h' | h' <;> omega

/-- Where `pickK` has no answer, `tryP` has none at any pair. -/
theorem pickK_none {θ : ℕ → ℕ} {k : ℕ} {s : PFml} (h : pickK θ k s = none) : ∀ x ∈ pairsK k, tryP θ k s x = none :=
  head?_filterMap_eq_none h

/-! ### The search finds the rule -/

/-- An answer of `tryP` at the pair (j, h) is a heart of size h for the clauses of size j, without
repeated literals, with its petals. -/
theorem tryP_some {θ : ℕ → ℕ} {k : ℕ} {s : PFml} {jh : ℕ × ℕ} {HP : PCl × PFml} (hs : NF s) (hjh : jh ∈ pairsK k)
    (h : tryP θ k s jh = some HP) :
    HP.1.Nodup ∧ HP.1.toFinset.card = jh.2 ∧ Heart θ (toFin s) jh.1 HP.1.toFinset ∧
      HP.2 = (overP s jh.1 HP.1).map (minusP HP.1) := by
  obtain ⟨h0, h1, h2⟩ := mem_pairsK.1 hjh
  obtain ⟨H, hH, rfl⟩ := Option.map_eq_some_iff.1 h
  have hp := List.find?_some hH
  obtain ⟨C, hC, -, hsub, hlen⟩ := (mem_heartsP h2).1 (List.mem_of_find?_eq_some hH)
  have hnd : H.Nodup := (hs.1 C hC).sublist hsub
  have hcard : H.toFinset.card = jh.2 := by rw [List.toFinset_card_of_nodup hnd, hlen]
  refine ⟨hnd, hcard, ⟨?_, ?_, ?_⟩, rfl⟩
  · rw [← Finset.card_pos, hcard]; exact h0
  · rw [hcard]; exact h1
  · rw [hcard, ← length_overP hs]; simpa using hp

/-- Where `tryP` has no answer at (j, h), no set of size h is a heart for the clauses of size j. The
threshold is at least 1, so a
heart lies inside some clause and is among the candidates. -/
theorem tryP_none {θ : ℕ → ℕ} {k : ℕ} {s : PFml} {jh : ℕ × ℕ} (hθ : ∀ r, 1 ≤ r → 1 ≤ θ r) (hs : NF s)
    (hjh : jh ∈ pairsK k) (h : tryP θ k s jh = none) :
    ∀ H : Finset PLit, H.card = jh.2 → ¬ Heart θ (toFin s) jh.1 H := by
  obtain ⟨h0, h1, h2⟩ := mem_pairsK.1 hjh
  rintro H hcard ⟨-, -, hle⟩
  rw [tryP, Option.map_eq_none_iff] at h
  have hpos : 0 < (Sparsify.over (toFin s) jh.1 H).card := lt_of_lt_of_le (hθ _ (by omega)) hle
  obtain ⟨X, hX⟩ := Finset.card_pos.1 hpos
  obtain ⟨hXs, hXj, hHX⟩ := Finset.mem_filter.1 hX
  obtain ⟨C, hC, rfl⟩ := mem_toFin.1 hXs
  have hCj : C.length = jh.1 := by rw [← hXj, List.toFinset_card_of_nodup (hs.1 C hC)]
  have e : (C.filter (· ∈ H)).toFinset = H := by
    ext a
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.1 (hHX h), h⟩⟩
  have hlen : (C.filter (· ∈ H)).length = jh.2 := by
    rw [← hcard, ← e, List.toFinset_card_of_nodup ((hs.1 C hC).filter _), e]
  have hmem : C.filter (· ∈ H) ∈ heartsP k s jh.1 jh.2 := (mem_heartsP h2).2 ⟨C, hC, hCj, List.filter_sublist, hlen⟩
  have := List.find?_eq_none.1 h _ hmem
  rw [length_overP hs, e, ← hcard] at this
  simp only [decide_eq_true_eq] at this
  exact this hle

/-- The same for a set H of any size: H is not a heart for size j if `tryP` has no answer at (j, |H|). -/
theorem not_heart_of_none {θ : ℕ → ℕ} {k : ℕ} {s : PFml} {j : ℕ} {H : Finset PLit} (hθ : ∀ r, 1 ≤ r → 1 ≤ θ r) (hs : NF s)
    (hj : j ≤ k) (h : (j, H.card) ∈ pairsK k → tryP θ k s (j, H.card) = none) : ¬ Heart θ (toFin s) j H := by
  intro hh
  have hm : (j, H.card) ∈ pairsK k := mem_pairsK.2 ⟨Finset.card_pos.2 hh.1, hh.2.1, hj⟩
  exact tryP_none hθ hs hm (h hm) H rfl hh

/-- An answer of `pickK` satisfies `Rule`: smallest clause size that has a heart, then a heart of
the largest size. -/
theorem rule_of_pickK {θ : ℕ → ℕ} {k : ℕ} {s : PFml} {HP : PCl × PFml} (hθ : ∀ r, 1 ≤ r → 1 ≤ θ r) (hs : NF s)
    (h : pickK θ k s = some HP) :
    ∃ j, HP.1.Nodup ∧ Rule θ k (toFin s) j HP.1.toFinset ∧ HP.2 = (overP s j HP.1).map (minusP HP.1) := by
  obtain ⟨jh, hjh, h1, h2⟩ := pickK_some h
  obtain ⟨hnd, hcard, hheart, hP⟩ := tryP_some hs hjh h1
  obtain ⟨-, -, hk⟩ := mem_pairsK.1 hjh
  refine ⟨jh.1, hnd, ⟨hk, hheart, ?_, ?_⟩, hP⟩
  · intro j' hj' H'
    exact not_heart_of_none hθ hs (by omega) fun hm => h2 _ hm (Or.inl hj')
  · intro H' hH'
    exact not_heart_of_none hθ hs hk fun hm => h2 _ hm (Or.inr ⟨rfl, by rw [← hcard]; exact hH'⟩)

/-- Where `pickK` has no answer, no clause size up to k has a heart. -/
theorem leaf_of_pickK {θ : ℕ → ℕ} {k : ℕ} {s : PFml} (hθ : ∀ r, 1 ≤ r → 1 ≤ θ r) (hs : NF s)
    (h : pickK θ k s = none) : Leaf θ k (toFin s) :=
  fun _ hj _ => not_heart_of_none hθ hs hj fun hm => pickK_none h _ hm

/-! ### The root -/

/-- `rootP ψ` stands for the inclusion-minimal clauses of ψ (`toFinset_rootP` of
`StepMachines/Math/SparsifyProg.lean`). -/
theorem toFin_rootP (ψ : PFml) : toFin (rootP ψ) = red (toFin ψ) := toFinset_rootP ψ

/-- `rootP ψ` is in normal form (from `nodeP_root` of `StepMachines/Math/SparsifyProg.lean`). -/
theorem NF_rootP (ψ : PFml) : NF (rootP ψ) := by
  have h := nodeP_root 0 ψ
  exact ⟨h.1, h.2.1⟩

/-! ### The statement of the interface -/

/-- If the thresholds θ 1, θ 2, … are at least 1, then `pickK θ k` follows the rule on finite sets,
its petals are in normal form, and
`rootP` gives the inclusion-minimal clauses in normal form. -/
public theorem refines {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ r → 1 ≤ θ r) (k : ℕ) : Refines θ k where
  some := by
    intro s H P hs h
    obtain ⟨j, hnd, hrule, hP⟩ := rule_of_pickK hθ hs h
    dsimp only at hnd hrule hP
    refine ⟨j, hrule, ?_, ?_, hnd⟩
    · rw [hP, toFin_petals hs.1]; rfl
    · rw [hP]; exact NF_petals hs j H
  none := fun _ hs h => leaf_of_pickK hθ hs h
  nf_root := NF_rootP
  toFin_root := toFin_rootP

/-- `StRefines`, one of the interface statements of `SparsifyWidthK/Interfaces.lean`. -/
public theorem stRefines : StRefines := fun _ k hθ => refines (fun r _ => hθ r) k

end WidthK.Refine
