/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Lib.Bool
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod

/-! Polynomial time: tables. Every function on a finite type whose equality can be tested is
polynomial-time, because it is a
finite chain of tests "is the argument this element?" with constant answers. `table₁`, `table₂`,
`table₃` take one to three
arguments; `table₃` serves, for instance, for functions of a few Booleans. -/

@[expose] public section

namespace Groundwork.PolyT

variable {α β γ δ ε ζ : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε] [Enc ζ]

/-- The table of F on the elements of the list l, read from the left; d is the answer when the
argument is not in l. -/
def lookup [DecidableEq β] (F : β → γ) (d : γ) (l : List β) (y : β) : γ :=
  l.foldr (fun b r => if y = b then F b else r) d

omit [Enc β] [Enc γ] in
/-- On the elements of the list the table gives F. -/
theorem lookup_eq [DecidableEq β] (F : β → γ) (d : γ) {l : List β} {y : β} (h : y ∈ l) : lookup F d l y = F y := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    by_cases e : y = b
    · simp [lookup, e]
    · have := ih ((List.mem_cons.1 h).resolve_left e)
      simpa [lookup, e] using this

/-- Reading a table is polynomial-time: the list is fixed, so this is a fixed chain of tests. -/
theorem lookup_polyT [DecidableEq β] [EqT β] (F : β → γ) (d : γ) (l : List β) : PolyT (lookup F d l) := by
  induction l with
  | nil => exact const d
  | cons b l ih => exact ite' (decide_eq id' (const b)) (const (F b)) ih

/-- Every function on a finite type with a polynomial-time equality test is polynomial-time. -/
theorem table [Finite β] [DecidableEq β] [EqT β] (F : β → γ) : PolyT F := by
  obtain ⟨l, -, hl⟩ := Finite.exists_univ_list β
  rcases isEmpty_or_nonempty β with h | ⟨⟨y₀⟩⟩
  · obtain ⟨P, c, -⟩ := (id' : PolyT fun y : β => y)
    exact ⟨P, c, fun y => isEmptyElim y, fun y => isEmptyElim y⟩
  · exact (lookup_polyT F (F y₀) l).congr fun y => lookup_eq F _ (hl y)

/-- A table after a polynomial-time argument. -/
theorem table₁ [Finite β] [DecidableEq β] [EqT β] (F : β → ζ) {f : α → β} (hf : PolyT f) : PolyT fun x => F (f x) :=
  comp (table F) hf

/-- A table with two arguments. -/
theorem table₂ [Finite β] [DecidableEq β] [EqT β] [Finite γ] [DecidableEq γ] [EqT γ] (F : β → γ → ζ) {f : α → β} {g : α → γ}
    (hf : PolyT f) (hg : PolyT g) : PolyT fun x => F (f x) (g x) :=
  table₁ (fun t : β × γ => F t.1 t.2) (prodMk hf hg)

/-- A table with three arguments. -/
theorem table₃ [Finite β] [DecidableEq β] [EqT β] [Finite γ] [DecidableEq γ] [EqT γ] [Finite δ] [DecidableEq δ] [EqT δ]
    (F : β → γ → δ → ζ) {f : α → β} {g : α → γ} {h : α → δ} (hf : PolyT f) (hg : PolyT g) (hh : PolyT h) :
    PolyT fun x => F (f x) (g x) (h x) :=
  table₂ (fun (b : β) (t : γ × δ) => F b t.1 t.2) hf (prodMk hg hh)

end Groundwork.PolyT
