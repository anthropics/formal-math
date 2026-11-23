/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tape.Hat

/-!
# Words, loops, and phases on disjoint channels
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {Z Γ : Type*} [Fintype Z] [DecidableEq Z] [Fintype Γ] [DecidableEq Γ]

/-- The series of one word. -/
def Series.word {Ω : Type*} [DecidableEq Ω] (w : List Ω) : Series F Ω := fun o => if o = w then 1 else 0

theorem RatLe.word {Ω : Type*} [DecidableEq Ω] (w : List Ω) :
    RatLe (2 * w.length + 1) (Series.word w : Series F Ω) := by
  induction w with
  | nil => exact RatLe.one
  | cons a w ih =>
    have h := (RatLe.letter (F := F) a).mul ih
    have e : Series.mul (Series.letter a) (Series.word w) = (Series.word (a :: w) : Series F Ω) := by
      funext o
      cases o with
      | nil => simp [Series.mul, Series.letter, Series.word]
      | cons b o =>
        rw [Series.mul, List.length_cons, Finset.sum_range_succ', Finset.sum_range_succ']
        have : ∀ k, Series.letter (F := F) a ((b :: o).take (k + 1 + 1)) *
            Series.word w ((b :: o).drop (k + 1 + 1)) = if k + 1 ≤ o.length then 0 else
            Series.letter (F := F) a ((b :: o).take (k + 1 + 1)) *
            Series.word w ((b :: o).drop (k + 1 + 1)) := by
          intro k
          split_ifs with hk
          · obtain ⟨c, o, rfl⟩ : ∃ c o', o = c :: o' := by
              cases o with
              | nil => simp at hk
              | cons c o => exact ⟨c, o, rfl⟩
            simp [Series.letter]
          · rfl
        rw [Finset.sum_congr rfl fun k _ => this k]
        rw [Finset.sum_congr rfl (g := fun _ => (0 : F)) (fun k hk => by
          rw [if_pos (by have := Finset.mem_range.1 hk; omega)])]
        simp only [Finset.sum_const_zero, zero_add]
        by_cases hb : b = a
        · subst hb
          by_cases ho : o = w <;> simp [Series.letter, Series.word, ho]
        · simp [Series.letter, Series.word, hb]
    rw [e] at h
    exact h.mono (by simp; omega)

theorem hat_word (w : List (Z × Γ)) (v : Z → List Γ) :
    hat (Series.word w : Series F (Z × Γ)) v = if v = proj w then 1 else 0 := by
  simp only [hat, Series.word, Finset.sum_ite_eq', mem_fib]
  by_cases h : v = proj w
  · simp [h]
  · simp [h, Ne.symm h]

section Loop

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The body of a loop: one of finitely many words, with weights. -/
def Series.body (wd : κ → List (Z × Γ)) (c : κ → F) : Series F (Z × Γ) :=
  ∑ k, c k • Series.word (wd k)

theorem RatLe.body (wd : κ → List (Z × Γ)) (c : κ → F) :
    RatLe (∑ k, (2 * (wd k).length + 1)) (Series.body wd c) :=
  RatLe.sum _ _ _ fun k _ => (RatLe.word (wd k)).smul (c k)

theorem hat_body (wd : κ → List (Z × Γ)) (c : κ → F) (v : Z → List Γ) :
    hat (Series.body wd c) v = ∑ k, if v = proj (wd k) then c k else 0 := by
  rw [Series.body, hat_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hat_smul, hat_word]
  simp

end Loop

section Phases

end Phases

end Nc
