/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Defs

/-!
# Walks in a tower
-/

namespace Nc.Tow

open Finset

namespace Tower

variable {h b D J r : ℕ} {T : Tower h b D J r} {j : ℕ}

theorem step_ends (e : T.Ed j) {c : T.X j} (hc : T.e0 e = c ∨ T.e1 e = c) :
    s(T.e0 e, T.e1 e) = s(c, T.step e c) := by
  unfold step
  by_cases h0 : T.e0 e = c
  · rw [if_pos h0, h0]
  · have h1 : T.e1 e = c := hc.resolve_left h0
    rw [if_neg h0, h1, Sym2.eq_swap]

theorem step_ne (e : T.Ed j) {c : T.X j} (hc : T.e0 e = c ∨ T.e1 e = c) : c ≠ T.step e c := by
  intro heq
  have h1 := step_ends e hc
  rw [← heq, Sym2.eq_iff] at h1
  have := T.e_ne e
  rcases h1 with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> exact this (h2.trans h3.symm)

theorem step_mem (e : T.Ed j) {c : T.X j} (hc : T.e0 e = c ∨ T.e1 e = c) :
    T.e0 e = T.step e c ∨ T.e1 e = T.step e c := by
  have h1 := step_ends e hc
  rw [Sym2.eq_iff] at h1
  rcases h1 with ⟨_, h3⟩ | ⟨h2, _⟩
  · exact Or.inr h3
  · exact Or.inl h2

theorem step_step (e : T.Ed j) {c : T.X j} (hc : T.e0 e = c ∨ T.e1 e = c) : T.step e (T.step e c) = c := by
  have h1 := step_ends e hc
  have h2 := step_ends e (step_mem e hc)
  rw [h1, Sym2.eq_iff] at h2
  rcases h2 with ⟨h3, h4⟩ | ⟨h3, _⟩
  · exact h4.symm.trans h3.symm
  · exact h3.symm

/-- The chamber after `s` steps. -/
def nodeAt (c : T.X j) (l : List (T.Ed j)) (s : ℕ) : T.X j := (l.take s).foldl (fun c e => T.step e c) c

theorem nodeAt_cons (c : T.X j) (e : T.Ed j) (l : List (T.Ed j)) (s : ℕ) :
    nodeAt c (e :: l) (s + 1) = nodeAt (T.step e c) l s := rfl

theorem walk_end {c c' : T.X j} {l : List (T.Ed j)} (hw : T.Walk c l c') : nodeAt c l l.length = c' := by
  induction l generalizing c with
  | nil => exact hw
  | cons e l ih =>
    rw [List.length_cons, nodeAt_cons]
    exact ih hw.2

theorem walk_step {c c' : T.X j} {l : List (T.Ed j)} (hw : T.Walk c l c') {s : ℕ} {e : T.Ed j}
    (he : l[s]? = some e) : (T.e0 e = nodeAt c l s ∨ T.e1 e = nodeAt c l s) ∧
      nodeAt c l (s + 1) = T.step e (nodeAt c l s) := by
  induction l generalizing c s with
  | nil => simp at he
  | cons e' l ih =>
    cases s with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      subst he
      exact ⟨hw.1, rfl⟩
    | succ s =>
      simp only [List.getElem?_cons_succ] at he
      rw [nodeAt_cons, nodeAt_cons]
      exact ih hw.2 he

theorem walk_append {c c' c'' : T.X j} {l l' : List (T.Ed j)} (h1 : T.Walk c l c') (h2 : T.Walk c' l' c'') :
    T.Walk c (l ++ l') c'' := by
  induction l generalizing c with
  | nil =>
    have : c = c' := h1
    subst this
    exact h2
  | cons e l ih => exact ⟨h1.1, ih h1.2⟩

theorem walk_reverse {c c' : T.X j} {l : List (T.Ed j)} (h1 : T.Walk c l c') : T.Walk c' l.reverse c := by
  induction l generalizing c with
  | nil => exact h1.symm
  | cons e l ih =>
    rw [List.reverse_cons]
    refine walk_append (ih h1.2) ⟨step_mem e h1.1, ?_⟩
    exact step_step e h1.1

end Tower

namespace Routes

variable {h b D J r : ℕ} {T : Tower h b D J r} {m Uu : ℕ} (R : Routes T m Uu)

/-- The path from `c` to `c'` by way of `γ`. -/
def path (c c' γ : T.X 0) : List (T.Ed 0) := R.rt c γ ++ (R.rt c' γ).reverse

theorem path_walk (c c' γ : T.X 0) : T.Walk c (R.path c c' γ) c' :=
  Tower.walk_append (R.walk c γ) (Tower.walk_reverse (R.walk c' γ))

theorem length_path (c c' γ : T.X 0) : (R.path c c' γ).length ≤ 2 * m := by
  rw [path, List.length_append, List.length_reverse]
  have := R.len c γ
  have := R.len c' γ
  omega

theorem exists_end (c c' γ : T.X 0) : ∃ s, Tower.nodeAt c (R.path c c' γ) s = c' :=
  ⟨_, Tower.walk_end (R.path_walk c c' γ)⟩

/-- The number of steps until the end is reached for the first time. -/
def pl (c c' γ : T.X 0) : ℕ := Nat.find (R.exists_end c c' γ)

/-- The chamber after `s` steps. -/
def pn (c c' γ : T.X 0) (s : ℕ) : T.X 0 := Tower.nodeAt c (R.path c c' γ) s

theorem pn_pl (c c' γ : T.X 0) : R.pn c c' γ (R.pl c c' γ) = c' := Nat.find_spec (R.exists_end c c' γ)

theorem pn_ne (c c' γ : T.X 0) {s : ℕ} (hs : s < R.pl c c' γ) : R.pn c c' γ s ≠ c' :=
  Nat.find_min (R.exists_end c c' γ) hs

theorem pl_le (c c' γ : T.X 0) : R.pl c c' γ ≤ (R.path c c' γ).length :=
  Nat.find_min' _ (Tower.walk_end (R.path_walk c c' γ))

theorem pl_pos {c c' : T.X 0} (hne : c ≠ c') (γ : T.X 0) : 0 < R.pl c c' γ := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  have := R.pn_pl c c' γ
  rw [h0] at this
  exact hne this

/-- The edge of step `s`. -/
theorem exists_edge (c c' γ : T.X 0) {s : ℕ} (hs : s < R.pl c c' γ) :
    ∃ e, (R.path c c' γ)[s]? = some e ∧ s(T.e0 e, T.e1 e) = s(R.pn c c' γ s, R.pn c c' γ (s + 1)) ∧
      R.pn c c' γ s ≠ R.pn c c' γ (s + 1) := by
  have hlt : s < (R.path c c' γ).length := lt_of_lt_of_le hs (R.pl_le c c' γ)
  refine ⟨(R.path c c' γ)[s], List.getElem?_eq_getElem hlt, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := Tower.walk_step (R.path_walk c c' γ) (List.getElem?_eq_getElem hlt)
    unfold pn
    rw [h2]
    exact Tower.step_ends _ h1
  · obtain ⟨h1, h2⟩ := Tower.walk_step (R.path_walk c c' γ) (List.getElem?_eq_getElem hlt)
    unfold pn
    rw [h2]
    exact Tower.step_ne _ h1

end Routes

end Nc.Tow
