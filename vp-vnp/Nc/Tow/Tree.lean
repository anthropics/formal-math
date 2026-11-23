/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Load4

/-!
# The tree of the tower plan
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset

/-- The first index with the smallest value. -/
theorem exists_im {h : ℕ} (hh : 0 < h) (f : Fin h → ℕ) : ∃ i, (∀ i', f i ≤ f i') ∧ ∀ i' < i, ¬ ∀ i'', f i' ≤ f i'' := by
  classical
  obtain ⟨i0, -, hi0⟩ := exists_min_image (univ : Finset (Fin h)) f ⟨⟨0, hh⟩, mem_univ _⟩
  have hex : ∃ k : ℕ, ∃ hk : k < h, ∀ i', f ⟨k, hk⟩ ≤ f i' := ⟨i0, i0.2, fun i' => hi0 i' (mem_univ _)⟩
  obtain ⟨hk, h1⟩ := Nat.find_spec hex
  exact ⟨⟨Nat.find hex, hk⟩, h1, fun i' hi' hcon => Nat.find_min hex hi' ⟨i'.2, hcon⟩⟩

/-- The first index with the smallest value. -/
noncomputable def im {h : ℕ} (hh : 0 < h) (f : Fin h → ℕ) : Fin h := (exists_im hh f).choose

theorem im_unique {h : ℕ} (hh : 0 < h) (f : Fin h → ℕ) {i : Fin h} (h1 : ∀ i', f i ≤ f i')
    (h2 : ∀ i' < i, ¬ ∀ i'', f i' ≤ f i'') : i = im hh f := by
  obtain ⟨h3, h4⟩ := (exists_im hh f).choose_spec
  rcases lt_trichotomy i (im hh f) with hlt | heq | hlt
  · exact absurd h1 (h4 i hlt)
  · exact heq
  · exact absurd h3 (h2 _ hlt)

variable {h b D J r m AA : ℕ} {T : Tower h b D J r} (hh : 0 < h) (ch : Fin AA ↪ T.X 0)

/-- Loads by levels. -/
def lev (L : Tg T m AA → ℕ) (j : ℕ) : T.Ed j → ℕ := fun e => if hj : j < J + 1 then L (.edge ⟨j, hj⟩ e) else 0

variable (Lf : ∀ j, T.Ed j → ℕ)

/-- The type that is chosen at a level. -/
noncomputable def imin (j : ℕ) : Fin h := im hh fun i => ∑ e : T.Ed j, if T.ty e = i then Lf j e ^ 2 else 0

theorem isMin_iff (L : Tg T m AA → ℕ) (j : Fin (J + 1)) (i : Fin h) : IsMin L j i ↔ i = imin hh (lev L) j.1 := by
  have e1 : (fun i => ∑ e : T.Ed j.1, if T.ty e = i then lev L j.1 e ^ 2 else 0) = sqs L j := by
    funext i
    unfold sqs lev
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [dif_pos j.2]
  unfold imin
  rw [e1]
  constructor
  · rintro ⟨h1, h2⟩
    exact im_unique hh _ h1 h2
  · rintro rfl
    exact (exists_im hh (sqs L j)).choose_spec

/-- The parent of a chamber. -/
noncomputable def hostj {j : ℕ} (c : T.X j) : T.X (j + 1) := T.host (imin hh Lf j) (T.vx (imin hh Lf j) c)

/-- Units between a chamber and its parent. -/
def fb (j : ℕ) (c : T.X j) : ℕ := T.bet (Lf j) c

variable {hh Lf}

/-- A chamber has at most `b` children. -/
theorem card_children {j : ℕ} (hj : j < J) (c' : T.X (j + 1)) :
    (univ.filter fun c : T.X j => hostj hh Lf c = c').card ≤ b := by
  refine le_trans ?_ T.card_fl.le
  rw [← card_univ (α := T.Fl)]
  refine card_le_card_of_injOn (fun c => T.co (imin hh Lf j) c) (fun _ _ => mem_coe.2 (mem_univ _)) ?_
  intro c hc c'' hc'' heq
  have h1 := (mem_filter.1 (mem_coe.1 hc)).2
  have h2 := (mem_filter.1 (mem_coe.1 hc'')).2
  have h3 := T.host_inj hj _ (h1.trans h2.symm)
  exact (T.vx_co hj.le (imin hh Lf j)).1 (Prod.ext h3 heq)

theorem nd_cases (ν : Nd T) : ν = none ∨ ∃ (j : ℕ) (hj : j ≤ J) (c : T.X j), ν = nd T j hj c := by
  rcases ν with _ | ⟨j, c⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨j.1, Nat.le_of_lt_succ j.2, c, rfl⟩

/-- A function on the nodes. -/
def onN (f : ∀ j, T.X j → ℕ) (f0 : ℕ) : Nd T → ℕ
  | none => f0
  | some ⟨j, c⟩ => f j.1 c

theorem onN_nd (f : ∀ j, T.X j → ℕ) (f0 : ℕ) {j : ℕ} (hj : j ≤ J) (c : T.X j) : onN f f0 (nd T j hj c) = f j c := rfl

end Nc.Tow
