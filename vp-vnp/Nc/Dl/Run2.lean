/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Dl.Run

/-!
# The runs of the dealing program, II
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

variable {B : Type} [CommRing B] {A : Type} [CommRing A] {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {K A' E U0 U1 ub mm D pS : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} (C : Codes S M U0 U1 D pS) {m : ℕ}

section Conv

variable (tab : SlpTab P grp D pS)

/-- Indices of phase 7. -/
abbrev Ix7 (M : Sys A (K + K + A') E) (U0 U1 : ℕ) := Fin E ⊕ Option (Fin E) ⊕ G.Uid (K + K) U0 M.N U1

/-- Names of phase 7. -/
def nm7 : Ix7 M U0 U1 → NmT S M U0 U1 pS
  | .inl x => .num x
  | .inr (.inl c) => .cond c
  | .inr (.inr id) => .cut id

theorem nm7_inj : Function.Injective (nm7 : Ix7 M U0 U1 → NmT S M U0 U1 pS) := by
  rintro (x | c | id) (x' | c' | id') h <;> simp only [nm7, reduceCtorEq, Nm.num.injEq, Nm.cond.injEq, Nm.cut.injEq] at h <;>
    rw [h]

/-- A step of phase 7. -/
noncomputable def step7 : Ix7 M U0 U1 → DStep
  | .inl x => C.un (.slp (tab.knum x)) (.num x) fun d => num d
  | .inr (.inl c) => C.un (.slp (tab.kcond c)) (.cond c) fun d => bit (decide (d.1 = 1))
  | .inr (.inr id) => C.un (.slp (tab.kcut id)) (.cut id) fun d => bit (decide (d.1 = 1))

/-- Values of phase 7. -/
def v7 (x : NN K U0 × (M.N → Fin U1)) : Ix7 M U0 U1 → Tree
  | .inl y => num (tab.fn (tab.knum y) x)
  | .inr (.inl c) => bit (decide ((tab.fn (tab.kcond c) x : ℕ) = 1))
  | .inr (.inr id) => bit (decide ((tab.fn (tab.kcut id) x : ℕ) = 1))

/-- Phase 7: numbers and conditions. -/
noncomputable def steps7 : List DStep := (univ : Finset (Ix7 M U0 U1)).toList.map (step7 C tab)

open Classical in
theorem phase7 (x : NN K U0 × (M.N → Fin U1)) {st : NmT S M U0 U1 pS → Tree} (hz : st .zero = .nil)
    (hs : ∀ k, st (.slp k) = C.dt (tab.fn k x)) :
    execAll m (steps7 C tab) (byPath C.nm st) = [byPath C.nm fun y =>
      if h : ∃ a : Ix7 M U0 U1, nm7 a = y then v7 tab x h.choose else st y] := by
  refine phase_det C nm7 nm7_inj (v7 tab x)
    (fun st => st .zero = .nil ∧ ∀ k, st (.slp k) = C.dt (tab.fn k x)) ⟨hz, hs⟩ (fun a st hst => ?_)
    (fun a st hst => ⟨?_, fun k => ?_⟩) _ (fun a => Finset.mem_toList.2 (Finset.mem_univ a))
  · obtain ⟨hz, hs⟩ := hst
    rcases a with y | c | id
    · exact exec_un hz (hs _)
    · exact exec_un hz (hs _)
    · exact exec_un hz (hs _)
  · rw [Function.update_of_ne (by rcases a with y | c | id <;> simp [nm7])]
    exact hst.1
  · rw [Function.update_of_ne (by rcases a with y | c | id <;> simp [nm7])]
    exact hst.2 k

end Conv

section Checks

/-- Phase 8: checks. -/
noncomputable def steps8 : List DStep :=
  (((univ : Finset (Option S × Fin (K + K))).toList.map fun a => C.nm (.row a.1 a.2)) ++
    ((univ : Finset (Option (Fin E))).toList.map fun c => C.nm (.cond c))).map DStep.check

theorem phase8_pos {st : NmT S M U0 U1 pS → Tree} (h1 : ∀ s p, st (.row s p) ≠ .nil) (h2 : ∀ c, st (.cond c) ≠ .nil) :
    execAll m (steps8 C) (byPath C.nm st) = [byPath C.nm st] := by
  refine execAll_checks_pos fun p hp => ?_
  rw [List.mem_append, List.mem_map, List.mem_map] at hp
  rcases hp with ⟨a, -, rfl⟩ | ⟨c, -, rfl⟩
  · rw [byPath_nm C.nm_inj]; exact h1 _ _
  · rw [byPath_nm C.nm_inj]; exact h2 _

theorem phase8_neg {st : NmT S M U0 U1 pS → Tree} (h : (∃ s p, st (.row s p) = .nil) ∨ ∃ c, st (.cond c) = .nil) :
    execAll m (steps8 C) (byPath C.nm st) = [] := by
  refine execAll_checks_neg ?_
  rcases h with ⟨s, p, h⟩ | ⟨c, h⟩
  · refine ⟨C.nm (.row s p), List.mem_append_left _ (List.mem_map.2 ⟨(s, p), Finset.mem_toList.2 (Finset.mem_univ _), rfl⟩), ?_⟩
    rw [byPath_nm C.nm_inj]; exact h
  · refine ⟨C.nm (.cond c), List.mem_append_right _ (List.mem_map.2 ⟨c, Finset.mem_toList.2 (Finset.mem_univ _), rfl⟩), ?_⟩
    rw [byPath_nm C.nm_inj]; exact h

end Checks

section Bits

/-- A content from a bit list. -/
def wOf (ub : ℕ) (u : List Bool) : UW ub := some fun j => u.reverse.getD j false

theorem length_allBits {n : ℕ} {u : List Bool} (h : u ∈ allBits n) : u.length = n := by
  induction n generalizing u with
  | zero => simp [allBits] at h; simp [h]
  | succ n ih =>
    simp only [allBits, List.mem_append, List.mem_map] at h
    rcases h with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ <;> simp [ih hv]

theorem mem_allBits {n : ℕ} {u : List Bool} (h : u.length = n) : u ∈ allBits n := by
  induction n generalizing u with
  | zero => simp [allBits, List.eq_nil_of_length_eq_zero h]
  | succ n ih =>
    cases u with
    | nil => simp at h
    | cons b u =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [allBits, List.mem_append, List.mem_map]
      cases b
      · exact Or.inr ⟨u, ih h, rfl⟩
      · exact Or.inl ⟨u, ih h, rfl⟩

theorem nodup_allBits (n : ℕ) : (allBits n).Nodup := by
  induction n with
  | zero => simp [allBits]
  | succ n ih =>
    rw [allBits, List.nodup_append]
    refine ⟨ih.map fun a b h => by simpa using h, ih.map fun a b h => by simpa using h, ?_⟩
    intro a ha b hb hab
    rw [List.mem_map] at ha hb
    obtain ⟨u, -, rfl⟩ := ha
    obtain ⟨u', -, rfl⟩ := hb
    simp at hab

theorem uwBits_wOf {u : List Bool} (h : u.length = ub) : uwBits (wOf ub u) = u.reverse := by
  unfold wOf uwBits
  apply List.ext_getElem
  · simp [h]
  · intro k h1 h2
    rw [List.getElem_ofFn, List.getD_eq_getElem _ _ h2]

theorem wOf_inj {u u' : List Bool} (h : u.length = ub) (h' : u'.length = ub) (e : wOf ub u = wOf ub u') : u = u' := by
  have := congrArg uwBits e
  rw [uwBits_wOf h, uwBits_wOf h'] at this
  exact List.reverse_injective this

theorem exists_wOf {w : UW ub} (h : w ≠ none) : ∃ u ∈ allBits ub, wOf ub u = w := by
  obtain ⟨v, rfl⟩ := Option.ne_none_iff_exists'.1 h
  refine ⟨(List.ofFn v).reverse, mem_allBits (by simp), ?_⟩
  unfold wOf
  congr 1
  funext j
  rw [List.reverse_reverse, List.getD_eq_getElem _ _ (by simp)]
  simp

/-- Options for a content. -/
def optsB (ub : ℕ) (c : Bool) : List (UW ub) := if c then (allBits ub).map (wOf ub) else [none]

theorem nodup_optsB (c : Bool) : (optsB ub c).Nodup := by
  unfold optsB
  cases c
  · simp
  · simp only [if_true]
    refine List.Nodup.map_on (fun u hu u' hu' h => ?_) (nodup_allBits ub)
    exact wOf_inj (length_allBits hu) (length_allBits hu') h

theorem mem_optsB {c : Bool} {w : UW ub} : w ∈ optsB ub c ↔ (w ≠ none ↔ c = true) := by
  unfold optsB
  cases c
  · simp
  · simp only [if_true, List.mem_map, iff_true]
    constructor
    · rintro ⟨u, -, rfl⟩
      exact Option.some_ne_none _
    · intro h
      exact exists_wOf h

/-- Phase 9: contents of cut units. -/
noncomputable def steps9 : List DStep := (univ : Finset (G.Uid (K + K) U0 M.N U1)).toList.map fun id =>
  DStep.bits (C.nm (.cut id)) (C.nm (.cont id))

/-- Write a content. -/
def ov9 (id : G.Uid (K + K) U0 M.N U1) (w : UW ub) (st : NmT S M U0 U1 pS → Tree) : NmT S M U0 U1 pS → Tree :=
  match w with
  | none => st
  | some v => Function.update st (.cont id) (ofBits (List.ofFn v))

theorem ov9_some (id : G.Uid (K + K) U0 M.N U1) (v : Fin ub → Bool) (st : NmT S M U0 U1 pS → Tree) :
    ov9 id (some v : UW ub) st = Function.update st (.cont id) (ofBits (List.ofFn v)) := rfl

theorem foldl_ov9 (b : G.Uid (K + K) U0 M.N U1 → UW ub) (s : List (G.Uid (K + K) U0 M.N U1))
    (st : NmT S M U0 U1 pS → Tree) :
    (∀ id ∈ s, ∀ v, b id = some v → (s.foldl (fun st id => ov9 id (b id) st) st) (.cont id) = ofBits (List.ofFn v)) ∧
    ∀ y, (∀ id, y ≠ .cont id) → (s.foldl (fun st id => ov9 id (b id) st) st) y = st y := by
  induction s using List.reverseRecOn generalizing st with
  | nil => exact ⟨fun id h => absurd h (by simp), fun _ _ => rfl⟩
  | append_singleton s id ih =>
    obtain ⟨h1, h2⟩ := ih st
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨fun id' hid' v hv => ?_, fun y hy => ?_⟩
    · by_cases h : id' = id
      · subst h
        rw [hv, ov9_some, Function.update_self]
      · have h3 : id' ∈ s := by
          rw [List.mem_append, List.mem_singleton] at hid'
          exact hid'.resolve_right h
        rw [← h1 id' h3 v hv]
        cases b id with
        | none => rfl
        | some w =>
          rw [ov9_some, Function.update_of_ne]
          intro h4
          exact h (by simpa using h4)
    · rw [← h2 y hy]
      cases b id with
      | none => rfl
      | some w => exact Function.update_of_ne (hy id) _ _

theorem phase9 {st : NmT S M U0 U1 pS → Tree} {cut : G.Uid (K + K) U0 M.N U1 → Bool}
    (hc : ∀ id, st (.cut id) = bit (cut id)) (Φ : (List Bool → Tree) → B) :
    ((execAll ub (steps9 C) (byPath C.nm st)).map Φ).sum = ∑ b : G.Uid (K + K) U0 M.N U1 → UW ub,
      if ∀ id, b id ≠ none ↔ cut id = true then
        Φ (byPath C.nm ((univ : Finset (G.Uid (K + K) U0 M.N U1)).toList.foldl (fun st id => ov9 id (b id) st) st))
      else 0 := by
  classical
  rw [steps9, execAll_choices (opts := fun id => optsB ub (cut id)) (L := byPath C.nm) (ov := ov9)
    (good := fun st => ∀ id, st (.cut id) = bit (cut id)) (fun id st hst => ?_) (fun id st w hw hst id' => ?_)
    (Finset.nodup_toList _) hc (fun _ => none), sum_funs_univ _ fun id => nodup_optsB (cut id)]
  · refine Finset.sum_congr rfl fun b _ => ?_
    have key : (∀ id, b id ∈ optsB ub (cut id)) ↔ ∀ id, b id ≠ none ↔ cut id = true := forall_congr' fun id => mem_optsB
    by_cases h : ∀ id, b id ≠ none ↔ cut id = true
    · rw [if_pos h, if_pos (key.2 h)]
    · rw [if_neg h, if_neg fun h' => h (key.1 h')]
  · rw [exec_bits C.nm_inj, hst]
    unfold optsB
    cases cut id
    · rfl
    · simp only [if_true, List.map_map]
      rw [if_neg (by simp [bit, one])]
      refine List.map_congr_left fun u hu => ?_
      have h1 := uwBits_wOf (length_allBits hu)
      simp only [Function.comp_apply, wOf, ov9]
      rw [wOf] at h1
      simp only [uwBits] at h1
      rw [h1]
  · rw [← hst id']
    cases w with
    | none => rfl
    | some v => exact Function.update_of_ne (show (Nm.cut id' : NmT S M U0 U1 pS) ≠ .cont id by simp) _ _

end Bits

end Nc.Dl
