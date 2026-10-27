/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Lib.List2
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.ProdSigma

/-! Polynomial time for lists: membership, duplicates, longest prefix passing a test, products of
lists. -/

@[expose] public section

namespace Groundwork.PolyT

variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

/-- Membership in the form `elem`. The test `==` may be any lawful one: on pairs, options and lists
it is not the one made
from `DecidableEq`. -/
@[fun_prop] theorem elem [DecidableEq β] [EqT β] [BEq β] [LawfulBEq β] {b : α → β} {l : α → List β} (hb : PolyT b)
    (hl : PolyT l) : PolyT (fun x => (l x).elem (b x)) := by
  have h : PolyT (fun x => (l x).any fun e => decide (b x = e)) := by fun_prop
  exact h.congr fun x => by rw [Bool.eq_iff_iff]; simp

/-- Membership in the form `contains`. -/
@[fun_prop] theorem contains [DecidableEq β] [EqT β] [BEq β] [LawfulBEq β] {b : α → β} {l : α → List β} (hb : PolyT b)
    (hl : PolyT l) : PolyT (fun x => (l x).contains (b x)) :=
  elem hb hl

/-- Membership in the form `decide (b ∈ l)`. `BEq` and `LawfulBEq` are needed because the instance
`Decidable (b ∈ l)` of Lean's
core library is built from them. -/
@[fun_prop] theorem decide_mem [DecidableEq β] [EqT β] [BEq β] [LawfulBEq β] {b : α → β} {l : α → List β} (hb : PolyT b)
    (hl : PolyT l) : PolyT (fun x => decide (b x ∈ l x)) :=
  (elem hb hl).congr fun x => by simp

/-- Removal of duplicates: a fold from the right that adds an element unless the result already has
it. -/
@[fun_prop] theorem dedup [DecidableEq β] [EqT β] {l : α → List β} (hl : PolyT l) :
    PolyT (fun x => (l x).dedup) := by
  obtain ⟨s, hs, _, hls⟩ := len_bound hl
  have h : PolyT (fun x => (l x).foldr (fun e c => bif c.elem e then c else e :: c) []) := by
    refine foldr_add (g := fun _ e c => bif c.elem e then c else e :: c) hl (const []) (by fun_prop)
      ⟨fun n => s n + 2, hs.add (PB.const 2), ?_⟩
    intro x c e he
    have := (len_le_of_mem he).trans (hls x)
    cases c.elem e
    · simp only [cond_false, len_cons]
      omega
    · simp
  exact h.congr fun x => by induction l x with
    | nil => rfl
    | cons e r ih =>
      rw [List.foldr_cons, ih]
      by_cases he : e ∈ r.dedup
      · rw [List.dedup_cons_of_mem' he]
        simp [he]
      · rw [List.dedup_cons_of_notMem' he]
        simp [he]

/-- The longest prefix whose elements pass a test; the test may depend on the input `x`. -/
@[fun_prop] theorem takeWhile {f : α → β → Bool} {l : α → List β} (hf : PolyT fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    PolyT (fun x => (l x).takeWhile (f x)) := by
  obtain ⟨s, hs, _, hls⟩ := len_bound hl
  have h : PolyT (fun x => (l x).foldr (fun e c => bif f x e then e :: c else []) []) := by
    refine foldr_add (g := fun x e c => bif f x e then e :: c else []) hl (const [])
      (cond' (comp₂ hf (by fun_prop) (by fun_prop)) (by fun_prop) (by fun_prop))
      ⟨fun n => s n + 2, hs.add (PB.const 2), ?_⟩
    intro x c e he
    have := (len_le_of_mem he).trans (hls x)
    cases f x e
    · simp only [cond_false, len_nil]
      omega
    · simp only [cond_true, len_cons]
      omega
  exact h.congr fun x => by induction l x with
    | nil => rfl
    | cons e r ih => cases hfe : f x e <;> simp [ih, hfe]

/-- The list without its longest prefix whose elements pass a test. -/
@[fun_prop] theorem dropWhile {f : α → β → Bool} {l : α → List β} (hf : PolyT fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    PolyT (fun x => (l x).dropWhile (f x)) :=
  (drop (length (takeWhile hf hl)) hl).congr fun x => by induction l x with
    | nil => rfl
    | cons e r ih => cases hfe : f x e <;> simp [ih, hfe]

/-- The list of all pairs of an element of the first list and an element of the second. -/
@[fun_prop] theorem product {l : α → List β} {l' : α → List γ} (hl : PolyT l) (hl' : PolyT l') :
    PolyT (fun x => (l x).product (l' x)) := by
  have h : PolyT (fun x => (l x).flatMap fun a => (l' x).map (Prod.mk a)) := by fun_prop
  exact h.congr fun _ => rfl

/-- The product of two lists in the notation ×ˢ. -/
@[fun_prop] theorem sprod {l : α → List β} {l' : α → List γ} (hl : PolyT l) (hl' : PolyT l') :
    PolyT (fun x => l x ×ˢ l' x) :=
  product hl hl'

end Groundwork.PolyT
