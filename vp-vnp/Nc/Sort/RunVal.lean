/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Sort.Runs

/-!
# The value of a program given by its runs
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J] {X : Type*}

/-- The run puts the same word on both sides of every tape, and the inputs are u. -/
def Mt (em : X → Ch S J → List Γ) (u : J → List Γ) (x : X) : Prop :=
  (∀ s, em x (.tp s false) = em x (.tp s true)) ∧ ∀ j, em x (.inp j) = u j

theorem Mt.eq_tup {em : X → Ch S J → List Γ} {u : J → List Γ} {x : X} (h : Mt em u x) :
    em x = tup (fun s => em x (.tp s true)) u := by
  funext z
  match z with
  | .tp s false => exact h.1 s
  | .tp s true => rfl
  | .inp j => exact h.2 j

theorem Mt.of_tup {em : X → Ch S J → List Γ} {u : J → List Γ} {x : X} {W : S → List Γ}
    (h : em x = tup W u) : Mt em u x ∧ (fun s => em x (.tp s true)) = W := by
  refine ⟨⟨fun s => ?_, fun j => ?_⟩, ?_⟩
  · rw [h]; rfl
  · rw [h]; rfl
  · funext s; rw [h]; rfl

theorem IsRuns.val_eq {P : Series F (Ch S J × Γ)} {em : X → Ch S J → List Γ} {wt : X → F}
    (h : IsRuns P em wt) (t : ℕ) (u : J → List Γ) (R : Finset X)
    (hR : ∀ x, x ∈ R ↔ Mt em u x ∧ ∑ s, (em x (.tp s true)).length ≤ t) :
    val t P u = ∑ x ∈ R, wt x := by
  classical
  rw [val, ← Finset.sum_fiberwise_of_maps_to (s := R) (t := contents S Γ t)
    (g := fun x s => em x (.tp s true))]
  · refine Finset.sum_congr rfl fun W hW => ?_
    refine h.of_fib _ fun x => ?_
    rw [Finset.mem_filter, hR]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rw [h1.eq_tup, h3]
    · intro h1
      obtain ⟨h2, h3⟩ := Mt.of_tup h1
      refine ⟨⟨h2, ?_⟩, h3⟩
      rw [mem_contents, ← h3] at hW
      exact hW
  · intro x hx
    rw [mem_contents]
    exact ((hR x).1 hx).2

theorem IsRuns.exists_mt {P : Series F (Ch S J × Γ)} {em : X → Ch S J → List Γ} {wt : X → F}
    (h : IsRuns P em wt) {u : J → List Γ} {W : S → List Γ} (hW : hat P (tup W u) ≠ 0) :
    ∃ x, Mt em u x ∧ (fun s => em x (.tp s true)) = W := by
  obtain ⟨x, hx, -⟩ := h.exists_run hW
  exact ⟨x, Mt.of_tup hx⟩

theorem IsRuns.bdd {P : Series F (Ch S J × Γ)} {em : X → Ch S J → List Γ} {wt : X → F}
    (h : IsRuns P em wt) {u : J → List Γ} {t : ℕ}
    (ht : ∀ x, Mt em u x → ∑ s, (em x (.tp s true)).length ≤ t) : Bdd t P u := by
  intro W hW
  obtain ⟨x, hx, rfl⟩ := h.exists_mt hW
  exact ht x hx

end Nc
