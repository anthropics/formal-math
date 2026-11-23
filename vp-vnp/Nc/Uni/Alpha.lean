/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Sort.RunVal
import Nc.Sort.Words

/-!
# Letters and tapes of the universal program; loops over letters
-/

set_option linter.unusedSectionVars false

namespace Nc

open Finset

section Star

variable {F : Type*} [CommRing F] {Z Γ : Type*} [Fintype Z] [DecidableEq Z] [Fintype Γ] [DecidableEq Γ]

/-- Any word over a set of letters, written on the channels of zs. -/
theorem Runs.wordstar {κ : Type*} [Fintype κ] (zs : Finset Z) (hz : zs.Nonempty) (f : κ → Γ) :
    Runs (Fintype.card κ * (2 * zs.card + 1) + 1) (fun l : List κ => on zs (l.map f)) (fun _ => (1 : F)) := by
  obtain ⟨z₀, hz₀⟩ := hz
  have h := (Runs.letter (F := F) zs f fun _ => 1).kstar fun k => ⟨z₀, by simp [on, hz₀]⟩
  refine h.congr (Equiv.refl _) (fun l z => ?_) fun l => by simp
  rw [Equiv.refl_apply, flatMap_on]
  congr 1
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, ih, List.map_cons]; rfl

end Star

end Nc

namespace Nc.Uni

/-- Letters: bits, end of a word, modes, kinds of records, columns of records, mark, end of a record, flags, end of a
block. -/
inductive Sy (M K : Type) where
  | bit (x : Bool)
  | semi
  | md (m : M)
  | kd (k : K)
  | col (c : Fin 4 → Bool)
  | mark
  | dot
  | flag (f : Bool)
  | bar
  deriving DecidableEq, Fintype

/-- Letters of records. -/
abbrev Bl (K : Type) := K ⊕ (Fin 4 → Bool)

variable {M K : Type}

/-- Letters of records as letters. -/
def be : Bl K → Sy M K
  | .inl k => .kd k
  | .inr c => .col c

/-- Letters of records and the mark. -/
def ol : Option (Bl K) → Sy M K
  | none => .mark
  | some b => be b

theorem ol_inj : Function.Injective (ol : Option (Bl K) → Sy M K) := by
  rintro (_ | (a | a)) (_ | (b | b)) h <;> simp [ol, be] at h <;> simp [h]

theorem ol_ne_dot (o : Option (Bl K)) : (ol o : Sy M K) ≠ .dot := by
  rcases o with _ | (a | a) <;> simp [ol, be]

theorem ol_ne_bar (o : Option (Bl K)) : (ol o : Sy M K) ≠ .bar := by
  rcases o with _ | (a | a) <;> simp [ol, be]

/-- Tapes: registers, modes, counter, fresh addresses, lookups, the list, buckets, copies. -/
inductive Tp (K : Type) where
  | rg (i : Fin 5)
  | md
  | cp
  | fr
  | lk
  | ls
  | bk (b : Bl K)
  | cm (k : Bool)
  deriving DecidableEq, Fintype

/-- Channels. -/
abbrev Zc (K : Type) := Ch (Tp K) Unit

end Nc.Uni
