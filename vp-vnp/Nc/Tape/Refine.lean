/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Common refinement of two factorisations of a word

Two sequences of words have the same concatenation if and only if there is a matrix of words with staircase
support whose rows concatenate to the first sequence and whose columns concatenate to the second; the matrix
is unique.
-/

namespace Nc

variable {Γ : Type*} {K : ℕ}

/-- Concatenation. -/
def cat (A : Fin K → List Γ) : List Γ := (List.ofFn A).flatten

theorem cat_succ (A : Fin (K + 1) → List Γ) : cat A = A 0 ++ cat fun i => A i.succ := by
  simp [cat, List.ofFn_succ]

theorem cat_eq_nil {A : Fin K → List Γ} : cat A = [] ↔ ∀ i, A i = [] := by
  induction K with
  | zero => simp [cat]
  | succ K ih =>
    rw [cat_succ, List.append_eq_nil_iff, ih, Fin.forall_fin_succ]

theorem cat_eq_cons {A : Fin K → List Γ} {a : Γ} {W : List Γ} (h : cat A = a :: W) :
    ∃ i l, (∀ j < i, A j = []) ∧ A i = a :: l ∧ cat (Function.update A i l) = W := by
  induction K with
  | zero => simp [cat] at h
  | succ K ih =>
    rw [cat_succ] at h
    rcases hA : A 0 with _ | ⟨b, l⟩
    · rw [hA, List.nil_append] at h
      obtain ⟨i, l, h1, h2, h3⟩ := ih h
      refine ⟨i.succ, l, ?_, h2, ?_⟩
      · intro j hj
        refine Fin.cases (fun _ => hA) (fun j hj => h1 j (by simpa using hj)) j hj
      · rw [cat_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm, hA, List.nil_append, ← h3]
        congr 1
        funext j
        by_cases e : j = i
        · subst e; simp
        · rw [Function.update_of_ne e, Function.update_of_ne (fun h => e (Fin.succ_injective _ h))]
    · rw [hA, List.cons_append, List.cons.injEq] at h
      refine ⟨0, l, fun j hj => absurd hj (Fin.not_lt_zero j), by rw [hA, h.1], ?_⟩
      rw [cat_succ, Function.update_self, ← h.2]
      congr 2

theorem cat_of_cons {A : Fin K → List Γ} {a : Γ} {i : Fin K} {l : List Γ} (h1 : ∀ j < i, A j = [])
    (h2 : A i = a :: l) : cat A = a :: cat (Function.update A i l) := by
  induction K with
  | zero => exact i.elim0
  | succ K ih =>
    rw [cat_succ, cat_succ]
    by_cases e : i = 0
    · subst e
      rw [h2, Function.update_self, List.cons_append]
      congr 3
    · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 e
      rw [Function.update_of_ne (Ne.symm e), h1 0 (Fin.succ_pos i'), List.nil_append, List.nil_append]
      rw [ih (A := fun j => A j.succ) (i := i') (fun j hj => h1 _ (by simpa using hj)) h2]
      congr 2
      funext j
      by_cases e' : j = i'
      · subst e'; simp
      · rw [Function.update_of_ne e', Function.update_of_ne (fun h => e' (Fin.succ_injective _ h))]

/-- Staircase support. -/
def Stair (X : Fin K → Fin K → List Γ) : Prop :=
  ∀ a a' b b', X a b ≠ [] → X a' b' ≠ [] → a < a' → b ≤ b'

/-- `X` is a common refinement of `A` (rows) and `B` (columns). -/
structure IsRef (A B : Fin K → List Γ) (X : Fin K → Fin K → List Γ) : Prop where
  stair : Stair X
  row : ∀ a, cat (X a) = A a
  col : ∀ b, cat (fun a => X a b) = B b

/-- Replace one entry. -/
def upd (X : Fin K → Fin K → List Γ) (a b : Fin K) (l : List Γ) : Fin K → Fin K → List Γ :=
  fun a' b' => if a' = a ∧ b' = b then l else X a' b'

theorem upd_row (X : Fin K → Fin K → List Γ) (a b : Fin K) (l : List Γ) :
    upd X a b l a = Function.update (X a) b l := by
  funext b'
  by_cases e : b' = b
  · subst e; simp [upd]
  · simp [upd, e]

theorem upd_row_ne (X : Fin K → Fin K → List Γ) (a b : Fin K) (l : List Γ) {a' : Fin K} (h : a' ≠ a) :
    upd X a b l a' = X a' := by
  funext b'; simp [upd, h]

theorem upd_col (X : Fin K → Fin K → List Γ) (a b : Fin K) (l : List Γ) :
    (fun a' => upd X a b l a' b) = Function.update (fun a' => X a' b) a l := by
  funext a'
  by_cases e : a' = a
  · subst e; simp [upd]
  · simp [upd, e]

theorem upd_col_ne (X : Fin K → Fin K → List Γ) (a b : Fin K) (l : List Γ) {b' : Fin K} (h : b' ≠ b) :
    (fun a' => upd X a b l a' b') = fun a' => X a' b' := by
  funext a'; simp [upd, h]

/-- The first letter of a refinement. -/
theorem IsRef.first {A B : Fin K → List Γ} {X : Fin K → Fin K → List Γ} (h : IsRef A B X) {a : Fin K}
    {c : Γ} {l : List Γ} (h1 : ∀ j < a, A j = []) (h2 : A a = c :: l) :
    ∃ b x m, X a b = c :: x ∧ (∀ j < b, B j = []) ∧ B b = c :: m ∧
      IsRef (Function.update A a l) (Function.update B b m) (upd X a b x) := by
  obtain ⟨b, x, hx1, hx2, hx3⟩ := cat_eq_cons ((h.row a).trans h2)
  have hrow : ∀ j < a, ∀ b', X j b' = [] := fun j hj b' => cat_eq_nil.1 ((h.row j).trans (h1 j hj)) b'
  have hcol : ∀ j < b, ∀ a', X a' j = [] := by
    intro j hj a'
    rcases lt_trichotomy a' a with h' | h' | h'
    · exact hrow a' h' j
    · subst h'; exact hx1 j hj
    · by_contra hne
      exact absurd (h.stair a a' b j (by simp [hx2]) hne h') (not_le.2 hj)
  have hB := cat_of_cons (A := fun a' => X a' b) (i := a) (l := x) (fun j hj => hrow j hj b) hx2
  rw [h.col b] at hB
  refine ⟨b, x, _, hx2, fun j hj => ?_, hB, ?_, ?_, ?_⟩
  · rw [← h.col j]; exact cat_eq_nil.2 fun a' => hcol j hj a'
  · intro a₁ a₂ b₁ b₂ n1 n2 hlt
    have key : ∀ a' b', upd X a b x a' b' ≠ [] → X a' b' ≠ [] := by
      intro a' b' hn
      by_cases e : a' = a ∧ b' = b
      · obtain ⟨rfl, rfl⟩ := e; simp [hx2]
      · simpa [upd, e] using hn
    exact h.stair _ _ _ _ (key _ _ n1) (key _ _ n2) hlt
  · intro a'
    by_cases e : a' = a
    · subst e; rw [upd_row, Function.update_self, hx3]
    · rw [upd_row_ne _ _ _ _ e, Function.update_of_ne e, h.row]
  · intro b'
    by_cases e : b' = b
    · subst e; rw [upd_col, Function.update_self]
    · rw [upd_col_ne _ _ _ _ e, Function.update_of_ne e, h.col]

theorem IsRef.cat_eq {A B : Fin K → List Γ} {X : Fin K → Fin K → List Γ} (h : IsRef A B X) :
    cat A = cat B := by
  generalize hW : cat A = W
  induction W generalizing A B X with
  | nil =>
    symm
    rw [cat_eq_nil] at hW ⊢
    intro b
    rw [← h.col b, cat_eq_nil]
    intro a
    exact cat_eq_nil.1 ((h.row a).trans (hW a)) b
  | cons c W ih =>
    obtain ⟨a, l, h1, h2, h3⟩ := cat_eq_cons hW
    obtain ⟨b, x, m, -, hb, hB, href⟩ := h.first h1 h2
    rw [cat_of_cons hb hB, ← ih href h3]

theorem IsRef.unique {A B : Fin K → List Γ} {X Y : Fin K → Fin K → List Γ} (h : IsRef A B X)
    (h' : IsRef A B Y) : X = Y := by
  generalize hW : cat A = W
  induction W generalizing A B X Y with
  | nil =>
    rw [cat_eq_nil] at hW
    funext a b
    rw [cat_eq_nil.1 ((h.row a).trans (hW a)) b, cat_eq_nil.1 ((h'.row a).trans (hW a)) b]
  | cons c W ih =>
    obtain ⟨a, l, h1, h2, h3⟩ := cat_eq_cons hW
    obtain ⟨b, x, m, hx, hb, hB, href⟩ := h.first h1 h2
    obtain ⟨b', y, m', hy, hb', hB', href'⟩ := h'.first h1 h2
    have eb : b = b' := by
      rcases lt_trichotomy b b' with e | e | e
      · rw [hb' b e] at hB; simp at hB
      · exact e
      · rw [hb b' e] at hB'; simp at hB'
    subst eb
    rw [hB] at hB'
    obtain rfl : m = m' := by simpa using hB'
    have := ih href href' h3
    funext a' b'
    by_cases e : a' = a ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := e
      have h4 := congrFun (congrFun this a') b'
      simp only [upd, and_self, if_true] at h4
      rw [hx, hy, h4]
    · have h4 := congrFun (congrFun this a') b'
      simpa [upd, e] using h4

theorem IsRef.exists {A B : Fin K → List Γ} (h : cat A = cat B) : ∃ X, IsRef A B X := by
  generalize hW : cat A = W
  induction W generalizing A B with
  | nil =>
    have hB : cat B = [] := h ▸ hW
    rw [cat_eq_nil] at hW hB
    refine ⟨fun _ _ => [], fun _ _ _ _ h => absurd rfl h, fun a => ?_, fun b => ?_⟩
    · rw [hW, cat_eq_nil]; exact fun _ => rfl
    · rw [hB, cat_eq_nil]; exact fun _ => rfl
  | cons c W ih =>
    obtain ⟨a, l, h1, h2, h3⟩ := cat_eq_cons hW
    obtain ⟨b, m, g1, g2, g3⟩ := cat_eq_cons (h ▸ hW)
    obtain ⟨X, hX⟩ := ih (h3.trans g3.symm) h3
    have hrow : ∀ j < a, ∀ b', X j b' = [] := fun j hj b' =>
      cat_eq_nil.1 ((hX.row j).trans (by rw [Function.update_of_ne hj.ne, h1 j hj])) b'
    have hcol : ∀ j < b, ∀ a', X a' j = [] := fun j hj a' =>
      cat_eq_nil.1 ((hX.col j).trans (by rw [Function.update_of_ne hj.ne, g1 j hj])) a'
    refine ⟨upd X a b (c :: X a b), ?_, ?_, ?_⟩
    · have key : ∀ a' b', upd X a b (c :: X a b) a' b' ≠ [] → (a' = a ∧ b' = b) ∨ X a' b' ≠ [] := by
        intro a' b' hn
        by_cases e : a' = a ∧ b' = b
        · exact Or.inl e
        · exact Or.inr (by simpa [upd, e] using hn)
      have key2 : ∀ a' b', upd X a b (c :: X a b) a' b' ≠ [] → a ≤ a' ∧ b ≤ b' := by
        intro a' b' hn
        rcases key a' b' hn with ⟨rfl, rfl⟩ | hne
        · exact ⟨le_rfl, le_rfl⟩
        · exact ⟨not_lt.1 fun h => hne (hrow _ h _), not_lt.1 fun h => hne (hcol _ h _)⟩
      intro a₁ a₂ b₁ b₂ n1 n2 hlt
      rcases key a₁ b₁ n1 with ⟨rfl, rfl⟩ | m1
      · exact (key2 _ _ n2).2
      · rcases key a₂ b₂ n2 with ⟨rfl, rfl⟩ | m2
        · exact absurd (key2 _ _ n1).1 (not_le.2 hlt)
        · exact hX.stair _ _ _ _ m1 m2 hlt
    · intro a'
      by_cases e : a' = a
      · subst e
        rw [upd_row, cat_of_cons (a := c) (i := b) (l := X a' b), Function.update_idem,
          Function.update_eq_self, hX.row, Function.update_self, h2]
        · intro j hj; rw [Function.update_of_ne hj.ne]; exact hcol j hj a'
        · simp
      · rw [upd_row_ne _ _ _ _ e, hX.row, Function.update_of_ne e]
    · intro b'
      by_cases e : b' = b
      · subst e
        rw [upd_col, cat_of_cons (i := a) (l := X a b') (a := c), Function.update_idem]
        · rw [Function.update_eq_self (f := fun a' => X a' b') a, hX.col, Function.update_self, g2]
        · intro j hj; rw [Function.update_of_ne hj.ne]; exact hrow j hj b'
        · simp
      · rw [upd_col_ne _ _ _ _ e, hX.col, Function.update_of_ne e]

end Nc
