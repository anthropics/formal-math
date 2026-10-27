/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Lib.Bool

/-! Polynomial time for lists: reverse, append, foldr, map, filter, all, any, flatMap, filterMap,
find?. Each lemma tagged
`fun_prop` says that one function of `List` preserves `PolyT`. Everything comes from the fold. -/

@[expose] public section

namespace Groundwork.PolyT

variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

/-- The length of the result of a polynomial-time function has a monotone polynomial bound. -/
theorem len_bound {f : α → β} (hf : PolyT f) : ∃ t, PB t ∧ Monotone t ∧ ∀ x, len (f x) ≤ t (len x) := by
  obtain ⟨_, t, ht, hm, _, hlen⟩ := hf.elim
  exact ⟨t, ht, hm, hlen⟩

/-- A function of the context and of a member of a polynomial-time list has values of polynomial
length. -/
theorem len_bound_mem {f : α → β → γ} {l : α → List β} (hf : PolyT fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    ∃ b, PB b ∧ ∀ x, ∀ e ∈ l x, len (f x e) ≤ b (len x) := by
  obtain ⟨t, ht, hm, hft⟩ := len_bound hf
  obtain ⟨s, hs, _, hls⟩ := len_bound hl
  refine ⟨fun n => t (n + s n + 2), ht.comp ((PB.id'.add hs).add (PB.const 2)), fun x e he => ?_⟩
  refine (hft (x, e)).trans (hm ?_)
  rw [len_pair]
  have := (len_le_of_mem he).trans (hls x)
  omega

/-- A two-argument function after polynomial-time arguments. -/
theorem comp₂ {f : α → β → γ} {a : δ → α} {b : δ → β} (hf : PolyT fun p : α × β => f p.1 p.2) (ha : PolyT a)
    (hb : PolyT b) : PolyT fun x => f (a x) (b x) :=
  PolyT.comp (f := fun p : α × β => f p.1 p.2) (g := fun x => (a x, b x)) hf (prodMk ha hb)

omit [Enc β] in
private theorem foldl_cons_eq (l acc : List β) : l.foldl (fun c e => e :: c) acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons e l ih => simp [ih]

/-- Pushing the members of one list, first to last, on another. -/
theorem reverseAppend {l l' : α → List β} (hl : PolyT l) (hl' : PolyT l') :
    PolyT (fun x => (l x).reverse ++ l' x) := by
  obtain ⟨s, hs, _, hls⟩ := len_bound hl
  have h : PolyT (fun x => (l x).foldl (fun c e => e :: c) (l' x)) := by
    refine foldl_add (g := fun _ c e => e :: c) hl hl' (by fun_prop) ⟨fun n => s n + 2, hs.add (PB.const 2), ?_⟩
    intro x c e he
    have := (len_le_of_mem he).trans (hls x)
    simp only [len_cons]
    omega
  exact h.congr fun x => foldl_cons_eq _ _

@[fun_prop] theorem reverse {l : α → List β} (hl : PolyT l) :
    PolyT (fun x => (l x).reverse) :=
  (reverseAppend hl (const [])).congr fun x => by simp

@[fun_prop] theorem append {l l' : α → List β} (hl : PolyT l) (hl' : PolyT l') :
    PolyT (fun x => l x ++ l' x) :=
  (reverseAppend (reverse hl) hl').congr fun x => by simp

/-- The fold from the right when the fold of every suffix of the list has length at most t(len x). -/
theorem foldr {l : α → List ε} {a : α → γ} {g : α → ε → γ → γ} (hl : PolyT l) (ha : PolyT a)
    (hg : PolyT fun p : α × ε × γ => g p.1 p.2.1 p.2.2)
    (hB : ∃ t, PB t ∧ ∀ x (k : ℕ), len (((l x).drop k).foldr (g x) (a x)) ≤ t (len x)) :
    PolyT (fun x => (l x).foldr (g x) (a x)) := by
  obtain ⟨t, ht, hB⟩ := hB
  have hg' : PolyT fun p : α × γ × ε => g p.1 p.2.2 p.2.1 :=
    PolyT.comp (f := fun p : α × ε × γ => g p.1 p.2.1 p.2.2) (g := fun p : α × γ × ε => (p.1, p.2.2, p.2.1)) hg
      (by fun_prop)
  have h : PolyT (fun x => (l x).reverse.foldl (fun c e => g x e c) (a x)) := by
    refine foldl (g := fun x c e => g x e c) (reverse hl) ha hg' ⟨t, ht, fun x k => ?_⟩
    rw [List.take_reverse, List.foldl_reverse]
    exact hB x _
  exact h.congr fun x => by rw [List.foldl_reverse]

/-- The fold from the right when every step adds at most b(len x) to the length. -/
theorem foldr_add {l : α → List ε} {a : α → γ} {g : α → ε → γ → γ} (hl : PolyT l) (ha : PolyT a)
    (hg : PolyT fun p : α × ε × γ => g p.1 p.2.1 p.2.2)
    (hB : ∃ b, PB b ∧ ∀ x c, ∀ e ∈ l x, len (g x e c) ≤ len c + b (len x)) :
    PolyT (fun x => (l x).foldr (g x) (a x)) := by
  obtain ⟨b, hb, hB⟩ := hB
  have hg' : PolyT fun p : α × γ × ε => g p.1 p.2.2 p.2.1 :=
    PolyT.comp (f := fun p : α × ε × γ => g p.1 p.2.1 p.2.2) (g := fun p : α × γ × ε => (p.1, p.2.2, p.2.1)) hg
      (by fun_prop)
  have h : PolyT (fun x => (l x).reverse.foldl (fun c e => g x e c) (a x)) :=
    foldl_add (g := fun x c e => g x e c) (reverse hl) ha hg'
      ⟨b, hb, fun x c e he => hB x c e (List.mem_reverse.1 he)⟩
  exact h.congr fun x => by rw [List.foldl_reverse]

@[fun_prop] theorem map {f : α → β → γ} {l : α → List β} (hf : PolyT fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    PolyT (fun x => (l x).map (f x)) := by
  obtain ⟨b, hb, hfb⟩ := len_bound_mem hf hl
  have h : PolyT (fun x => (l x).foldr (fun e c => f x e :: c) []) := by
    refine foldr_add (g := fun x e c => f x e :: c) hl (const [])
      (cons' (comp₂ hf (by fun_prop) (by fun_prop)) (by fun_prop)) ⟨fun n => b n + 2, hb.add (PB.const 2), ?_⟩
    intro x c e he
    have := hfb x e he
    simp only [len_cons]
    omega
  exact h.congr fun x => by induction l x with
    | nil => rfl
    | cons e r ih => simp [ih]

@[fun_prop] theorem filter {f : α → β → Bool} {l : α → List β} (hf : PolyT fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    PolyT (fun x => (l x).filter (f x)) := by
  obtain ⟨s, hs, _, hls⟩ := len_bound hl
  have h : PolyT (fun x => (l x).foldr (fun e c => bif f x e then e :: c else c) []) := by
    refine foldr_add (g := fun x e c => bif f x e then e :: c else c) hl (const [])
      (cond' (comp₂ hf (by fun_prop) (by fun_prop)) (by fun_prop) (by fun_prop))
      ⟨fun n => s n + 2, hs.add (PB.const 2), ?_⟩
    intro x c e he
    have := (len_le_of_mem he).trans (hls x)
    cases f x e
    · simp
    · simp only [cond_true, len_cons]
      omega
  exact h.congr fun x => by induction l x with
    | nil => rfl
    | cons e r ih => cases hfe : f x e <;> simp [ih, hfe]

@[fun_prop] theorem all {f : α → β → Bool} {l : α → List β} (hf : PolyT fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    PolyT (fun x => (l x).all (f x)) := by
  have h : PolyT (fun x => (l x).foldr (fun e c => f x e && c) true) := by
    refine foldr_add (g := fun x e c => f x e && c) hl (const true)
      (and' (comp₂ hf (by fun_prop) (by fun_prop)) (by fun_prop)) ⟨fun _ => 0, PB.const 0, ?_⟩
    intro x c e _
    simp [len_bool]
  exact h.congr fun x => by induction l x with
    | nil => rfl
    | cons e r ih => simp [ih]

@[fun_prop] theorem any {f : α → β → Bool} {l : α → List β} (hf : PolyT fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    PolyT (fun x => (l x).any (f x)) := by
  have h : PolyT (fun x => (l x).foldr (fun e c => f x e || c) false) := by
    refine foldr_add (g := fun x e c => f x e || c) hl (const false)
      (or' (comp₂ hf (by fun_prop) (by fun_prop)) (by fun_prop)) ⟨fun _ => 0, PB.const 0, ?_⟩
    intro x c e _
    simp [len_bool]
  exact h.congr fun x => by induction l x with
    | nil => rfl
    | cons e r ih => simp [ih]

@[fun_prop] theorem flatMap {f : α → β → List γ} {l : α → List β} (hf : PolyT fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    PolyT (fun x => (l x).flatMap (f x)) := by
  obtain ⟨b, hb, hfb⟩ := len_bound_mem hf hl
  have h : PolyT (fun x => (l x).foldr (fun e c => f x e ++ c) []) := by
    refine foldr_add (g := fun x e c => f x e ++ c) hl (const [])
      (append (comp₂ hf (by fun_prop) (by fun_prop)) (by fun_prop)) ⟨b, hb, ?_⟩
    intro x c e he
    have := hfb x e he
    have := len_append (f x e) c
    omega
  exact h.congr fun x => by induction l x with
    | nil => rfl
    | cons e r ih => simp [ih]

@[fun_prop] theorem filterMap {f : α → β → Option γ} {l : α → List β} (hf : PolyT fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    PolyT (fun x => (l x).filterMap (f x)) := by
  obtain ⟨b, hb, hfb⟩ := len_bound_mem hf hl
  have h : PolyT (fun x => (l x).foldr (fun e c => (f x e).elim c fun y => y :: c) []) := by
    refine foldr_add (g := fun x e c => (f x e).elim c fun y => y :: c) hl (const [])
      (optionElim (f := fun (p : α × β × List γ) y => y :: p.2.2) (comp₂ hf (by fun_prop) (by fun_prop)) (by fun_prop)
        (by fun_prop)) ⟨b, hb, ?_⟩
    intro x c e he
    have := hfb x e he
    cases hfe : f x e with
    | none => simp
    | some y =>
      rw [hfe, len_some] at this
      simp only [Option.elim_some, len_cons]
      omega
  exact h.congr fun x => by induction l x with
    | nil => rfl
    | cons e r ih => cases hfe : f x e <;> simp [ih, hfe]

@[fun_prop] theorem find? {f : α → β → Bool} {l : α → List β} (hf : PolyT fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    PolyT (fun x => (l x).find? (f x)) := by
  obtain ⟨s, hs, _, hls⟩ := len_bound hl
  have h : PolyT (fun x => (l x).foldr (fun e c => bif f x e then some e else c) none) := by
    refine foldr_add (g := fun x e c => bif f x e then some e else c) hl (const none)
      (cond' (comp₂ hf (by fun_prop) (by fun_prop)) (by fun_prop) (by fun_prop))
      ⟨fun n => s n + 4, hs.add (PB.const 4), ?_⟩
    intro x c e he
    have := (len_le_of_mem he).trans (hls x)
    cases f x e
    · simp
    · simp only [cond_true, len_some]
      omega
  exact h.congr fun x => by induction l x with
    | nil => rfl
    | cons e r ih => cases hfe : f x e <;> simp [ih, hfe]

end Groundwork.PolyT
