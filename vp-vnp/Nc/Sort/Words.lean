/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Sort.Runs

/-!
# Words on several channels; codes; choices of letters
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc

open Finset

section Codes

variable {κ Γ : Type*}

theorem flatMap_inj {f : κ → List Γ} (hne : ∀ a, f a ≠ [])
    (hf : ∀ a b u v, f a ++ u = f b ++ v → a = b) :
    Function.Injective fun l : List κ => l.flatMap f := by
  intro l
  induction l with
  | nil =>
    rintro (_ | ⟨b, l'⟩) h
    · rfl
    · simp only [List.flatMap_nil, List.flatMap_cons] at h
      exact absurd (List.append_eq_nil_iff.1 h.symm).1 (hne b)
  | cons a l ih =>
    rintro (_ | ⟨b, l'⟩) h
    · simp only [List.flatMap_nil, List.flatMap_cons] at h
      exact absurd (List.append_eq_nil_iff.1 h).1 (hne a)
    · simp only [List.flatMap_cons] at h
      obtain rfl := hf a b _ _ h
      rw [ih (List.append_cancel_left h)]

theorem flatten_ofFn_single {k : ℕ} (i : Fin k) (w : Fin k → List Γ) (h : ∀ j, j ≠ i → w j = []) :
    (List.ofFn w).flatten = w i := by
  have h1 : (List.ofFn w).flatten = (List.finRange k).flatMap fun j => if j = i then w j else [] := by
    rw [List.ofFn_eq_map, ← List.flatMap_def]
    refine List.flatMap_congr fun j _ => ?_
    by_cases e : j = i
    · simp [e]
    · simp [e, h j e]
  rw [h1]
  exact flatMap_ite_eq _ (List.nodup_finRange k) i (List.mem_finRange i) w

theorem flatten_ofFn_nil {k : ℕ} (w : Fin k → List Γ) (h : ∀ j, w j = []) : (List.ofFn w).flatten = [] := by
  rw [List.flatten_eq_nil_iff]
  intro l hl
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl
  exact h j

end Codes

variable {F : Type*} [CommRing F] {Z Γ : Type*} [Fintype Z] [DecidableEq Z] [Fintype Γ] [DecidableEq Γ]

/-- The word w on every channel of zs. -/
def on (zs : Finset Z) (w : List Γ) : Z → List Γ := fun z => if z ∈ zs then w else []

theorem on_append (zs : Finset Z) (w w' : List Γ) (z : Z) : on zs w z ++ on zs w' z = on zs (w ++ w') z := by
  unfold on; split_ifs <;> simp

theorem flatMap_on {κ : Type*} (zs : Finset Z) (f : κ → List Γ) (l : List κ) (z : Z) :
    (l.flatMap fun k => on zs (f k) z) = on zs (l.flatMap f) z := by
  unfold on
  split_ifs
  · rfl
  · simp

theorem sum_on (zs : Finset Z) (w : List Γ) : ∑ z, (on zs w z).length = zs.card * w.length := by
  unfold on
  simp only [apply_ite List.length, List.length_nil]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul]

namespace Runs

/-- Choose a letter and write it on the channels of zs. -/
theorem letter {κ : Type*} [Fintype κ] (zs : Finset Z) (f : κ → Γ) (c : κ → F) :
    Runs (Fintype.card κ * (2 * zs.card + 1)) (fun k => on zs [f k]) c := by
  refine (pick (fun k => on zs [f k]) c).mono ?_
  simp [sum_on]

/-- A fixed word on the channels of zs. -/
theorem word (zs : Finset Z) (w : List Γ) :
    Runs (2 * (zs.card * w.length) + 1) (fun _ : Unit => on zs w) (fun _ => (1 : F)) := by
  refine (const (on zs w)).mono ?_
  rw [sum_on]

end Runs

end Nc
