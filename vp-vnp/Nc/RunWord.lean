/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tape.Run

/-!
# Places of letters in runs and in the code of the inputs
-/

set_option linter.unusedSectionVars false

namespace Nc

section Emit

variable {Γ S J : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]

theorem emit_appendR (o o' : List (Letter S J Γ)) (z : Ch S J) : emit (o ++ o') z = emit o z ++ emit o' z := by
  unfold emit
  rw [List.reduceOption_append, proj_append]

@[simp] theorem emit_nil (z : Ch S J) : emit ([] : List (Letter S J Γ)) z = [] := rfl

@[simp] theorem emit_none (z : Ch S J) : emit ([none] : List (Letter S J Γ)) z = [] := rfl

theorem emit_some (z z' : Ch S J) (γ : Γ) :
    emit ([some (z', γ)] : List (Letter S J Γ)) z = if z' = z then [γ] else [] := by
  unfold emit
  rw [List.reduceOption_cons_of_some, List.reduceOption_nil, proj_cons, proj_nil]

theorem emit_length_le (o : List (Letter S J Γ)) (z : Ch S J) : (emit o z).length ≤ o.length := by
  induction o with
  | nil => simp
  | cons a o ih =>
    rw [← List.singleton_append, emit_appendR, List.length_append, List.length_append]
    have : (emit [a] z).length ≤ 1 := by
      rcases a with _ | ⟨z', γ⟩
      · simp
      · rw [emit_some]
        split_ifs <;> simp
    simpa using Nat.add_le_add this ih

/-- The letter that is emitted at a step sits at the place counted before the step. -/
theorem emit_getElem (o : List (Letter S J Γ)) (z : Ch S J) (τ : ℕ) (γ : Γ) (h : o[τ]? = some (some (z, γ))) :
    (emit o z)[(emit (o.take τ) z).length]? = some γ := by
  have hτ : τ < o.length := (List.getElem?_eq_some_iff.1 h).1
  have ho : o = o.take τ ++ ([some (z, γ)] ++ o.drop (τ + 1)) := by
    conv_lhs => rw [← List.take_append_drop τ o, List.drop_eq_getElem_cons hτ]
    rw [(List.getElem?_eq_some_iff.1 h).2]
    rfl
  conv_lhs => rw [ho]
  rw [emit_appendR, emit_appendR, emit_some, if_pos rfl, List.take_append_of_le_length (by simp; omega),
    List.take_take, min_self, List.getElem?_append_right le_rfl, Nat.sub_self]
  rfl

/-- Every letter of a channel is emitted at some step. -/
theorem exists_emit (o : List (Letter S J Γ)) (z : Ch S J) (p : ℕ) (hp : p < (emit o z).length) :
    ∃ τ γ, τ < o.length ∧ o[τ]? = some (some (z, γ)) ∧ (emit (o.take τ) z).length = p := by
  induction o using List.reverseRecOn with
  | nil => simp at hp
  | append_singleton o a ih =>
    by_cases h : p < (emit o z).length
    · obtain ⟨τ, γ, h1, h2, h3⟩ := ih h
      refine ⟨τ, γ, by simp; omega, ?_, ?_⟩
      · rw [List.getElem?_append_left h1, h2]
      · rw [List.take_append_of_le_length h1.le, h3]
    · rw [emit_appendR, List.length_append] at hp
      rcases a with _ | ⟨z', γ⟩
      · simp at hp
        omega
      · rw [emit_some] at hp
        split_ifs at hp with hz
        · subst hz
          refine ⟨o.length, γ, by simp, by simp, ?_⟩
          rw [List.take_append_of_le_length le_rfl, List.take_length]
          simp at hp
          omega
        · simp at hp
          omega

end Emit

section Code

variable {Γ : Type*}

/-- The words one after the other, each followed by a separator. -/
def wordOf (v : List (List Γ)) : List (Option Γ) := v.flatMap fun l => l.map some ++ [none]

theorem wordOf_cons (l : List Γ) (v : List (List Γ)) : wordOf (l :: v) = l.map some ++ none :: wordOf v := by
  simp [wordOf]

theorem wordOf_append (v v' : List (List Γ)) : wordOf (v ++ v') = wordOf v ++ wordOf v' := by
  simp [wordOf]

theorem length_wordOf (v : List (List Γ)) : (wordOf v).length = (v.map List.length).sum + v.length := by
  induction v with
  | nil => rfl
  | cons l v ih =>
    rw [wordOf_cons]
    simp [ih]
    omega

variable {n : ℕ}

/-- The place of the first letter of word `k`. -/
def base (u : Fin n → List Γ) (k : ℕ) : ℕ := (wordOf ((List.ofFn u).take k)).length

@[simp] theorem base_zero (u : Fin n → List Γ) : base u 0 = 0 := by simp [base, wordOf]

theorem base_succ (u : Fin n → List Γ) (k : Fin n) : base u (k + 1) = base u k + (u k).length + 1 := by
  unfold base
  rw [List.take_add_one, wordOf_append, List.length_append]
  simp [wordOf]
  omega

theorem ofFn_split (u : Fin n → List Γ) (k : Fin n) :
    List.ofFn u = (List.ofFn u).take k ++ u k :: (List.ofFn u).drop (k + 1) := by
  have hk : (k : ℕ) < (List.ofFn u).length := by simp
  conv_lhs => rw [← List.take_append_drop k (List.ofFn u), List.drop_eq_getElem_cons hk]
  simp

theorem wordOf_getElem (u : Fin n → List Γ) (k : Fin n) (p : ℕ) :
    (wordOf (List.ofFn u))[base u k + p]? =
      ((u k).map some ++ none :: wordOf ((List.ofFn u).drop (k + 1)))[p]? := by
  conv_lhs => rw [ofFn_split u k]
  rw [wordOf_append, wordOf_cons, List.getElem?_append_right (by simp [base])]
  simp [base]

theorem base_add_lt (u : Fin n → List Γ) (k : Fin n) :
    base u k + (u k).length < (wordOf (List.ofFn u)).length := by
  conv_rhs => rw [ofFn_split u k]
  rw [wordOf_append, wordOf_cons, List.length_append, List.length_append, List.length_cons, List.length_map]
  unfold base
  omega

theorem eq_of_prefix (l m : List Γ) (r : List (Option Γ))
    (h : ∀ p ≤ m.length, (l.map some ++ none :: r)[p]? = (m.map some ++ [none])[p]?) : l = m := by
  induction m generalizing l with
  | nil =>
    cases l with
    | nil => rfl
    | cons a l =>
      have := h 0 (by simp)
      simp at this
  | cons b m ih =>
    have h0 := h 0 (by simp)
    cases l with
    | nil => simp at h0
    | cons a l =>
      simp at h0
      subst h0
      rw [ih l fun p hp => ?_]
      have := h (p + 1) (by simpa using hp)
      simpa using this

/-- A code that is read at all places of `v` is the code of `v`. -/
theorem eq_of_read (u v : Fin n → List Γ)
    (h : ∀ k : Fin n, ∀ p ≤ (v k).length,
      (wordOf (List.ofFn u))[base v k + p]? = ((v k).map some ++ [none])[p]?) : u = v := by
  have key : ∀ m : ℕ, ∀ k : Fin n, k.1 = m → u k = v k := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rintro k rfl
      have hb : base u k = base v k := by
        unfold base
        congr 2
        apply List.ext_getElem
        · simp
        · intro i h1 h2
          simp only [List.getElem_take, List.getElem_ofFn]
          simp only [List.length_take, List.length_ofFn] at h1
          exact ih i (by omega) _ rfl
      refine eq_of_prefix (u k) (v k) (wordOf ((List.ofFn u).drop (k + 1))) fun p hp => ?_
      rw [← wordOf_getElem, hb, h k p hp]
  exact funext fun k => key k k rfl

/-- The one-hot code of the inputs. -/
def code [DecidableEq Γ] (N : ℕ) (u : Fin n → List Γ) (b : Fin N × Option Γ) : Bool :=
  decide ((wordOf (List.ofFn u))[b.1.1]? = some b.2)

end Code

end Nc
