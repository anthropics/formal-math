/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Poly.Spec
public import ToTuring.Lib.Int
public import StepMachines.Prog.NetProg

/-! Certificates that functions of the program that merges the nodes of a network on [g] into K
groups (the grouping of Lemma 1) are polynomial-time (`PolyT`). `Unary f` says
that f is polynomial-time even with its value written in unary. Certificates of helper functions are
stated for arbitrary
polynomial-time arguments, so that the tactic `fun_prop` can use them; those that need the
hypothesis `Np.Keeps` are found by
`fun_prop (disch := assumption)`. -/

@[expose] public section

namespace Groundwork.Prog.NetE

/-! ### General list and number functions -/

theorem le_foldr_max {l : List ℕ} {k : ℕ} (h : k ∈ l) : k ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem foldr_max_mem {l : List ℕ} (h : l ≠ []) : l.foldr max 0 ∈ l := by
  induction l with
  | nil => exact absurd rfl h
  | cons a l ih =>
    rw [List.foldr_cons]
    by_cases hl : l = []
    · subst hl; simp
    · rcases max_choice a (l.foldr max 0) with e | e
      · rw [e]; exact List.mem_cons_self
      · rw [e]; exact List.mem_cons_of_mem _ (ih hl)

theorem foldr_max_eq (l : List ℕ) : l.foldr max 0 = (l.find? fun m => l.all fun k => decide (k ≤ m)).getD 0 := by
  by_cases hl : l = []
  · subst hl; rfl
  · cases h : l.find? fun m => l.all fun k => decide (k ≤ m) with
    | none =>
      have := List.find?_eq_none.1 h _ (foldr_max_mem hl)
      simp only [List.all_eq_true, decide_eq_true_eq, not_forall] at this
      obtain ⟨k, hk, h'⟩ := this
      exact absurd (le_foldr_max hk) h'
    | some m =>
      have h1 := List.find?_some h
      have h2 := List.mem_of_find?_eq_some h
      simp only [List.all_eq_true, decide_eq_true_eq] at h1
      exact le_antisymm (h1 _ (foldr_max_mem hl)) (le_foldr_max h2)

variable {α β : Type} [Enc α] [Enc β]

/-- The largest number of a list. -/
theorem foldr_max_polyT {l : α → List ℕ} (hl : PolyT l) : PolyT fun x => (l x).foldr max 0 := by
  have h : PolyT fun x => ((l x).find? fun m => (l x).all fun k => decide (k ≤ m)).getD 0 := by fun_prop
  exact h.congr fun x => (foldr_max_eq (l x)).symm

theorem flatMap_replicate_unit {β : Type} (f : β → ℕ) (l : List β) :
    (l.flatMap fun b => List.replicate (f b) ()) = List.replicate (l.map f).sum () := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [List.flatMap_cons, ih, List.map_cons, List.sum_cons, List.replicate_add]

/-- A sum of unary numbers over a polynomial-time list is unary. -/
theorem unary_sum_map {f : α → β → ℕ} {l : α → List β} (hf : Unary fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    Unary fun a => ((l a).map (f a)).sum := by
  unfold Unary at *
  have h : PolyT fun a => (l a).flatMap fun b => List.replicate (f a b) () := PolyT.flatMap hf hl
  exact h.congr fun a => flatMap_replicate_unit _ _

/-! ### The functions of the program -/

variable (K g : ℕ)

@[fun_prop] theorem col_polyT {x a : α → ℕ} (hx : PolyT x) (ha : PolyT a) : PolyT fun t => col K (x t) (a t) := by
  unfold col; fun_prop

@[fun_prop] theorem members_polyT {x G : α → ℕ} (hx : PolyT x) (hG : PolyT G) :
    PolyT fun t => members K g (x t) (G t) := by
  unfold members; fun_prop

@[fun_prop] theorem prs_polyT {x G G' : α → ℕ} (hx : PolyT x) (hG : PolyT G) (hG' : PolyT G') :
    PolyT fun t => prs K g (x t) (G t) (G' t) := by
  unfold prs; fun_prop

variable {C : Type} [Enc C] {Np : PNet C}

section

variable (h : Np.Keeps)
include h

/-- The lengths of the states, in binary. -/
@[fun_prop] theorem n_polyT {c : α → C} {a : α → ℕ} (hc : PolyT c) (ha : PolyT a) : PolyT fun t => Np.n (c t) (a t) :=
  PolyT.comp (g := fun t => (c t, a t)) h.n.poly (by fun_prop)

/-- The lengths of the labels, in binary. -/
@[fun_prop] theorem cap_polyT {c : α → C} {a b : α → ℕ} (hc : PolyT c) (ha : PolyT a) (hb : PolyT b) :
    PolyT fun t => Np.cap (c t) (a t) (b t) :=
  PolyT.comp (g := fun t => (c t, a t, b t)) h.cap.poly (by fun_prop)

@[fun_prop] theorem stLens_polyT {c : α → C} {x G : α → ℕ} (hc : PolyT c) (hx : PolyT x) (hG : PolyT G) :
    PolyT fun t => stLens K g Np (c t) (x t) (G t) := by
  unfold stLens; fun_prop (disch := assumption)

theorem stLen_unary : Unary (fun p : C × ℕ × ℕ => stLen K g Np p.1 p.2.1 p.2.2) :=
  unary_sum_map (f := fun (p : C × ℕ × ℕ) a => Np.n p.1 a) (l := fun p => members K g p.2.1 p.2.2)
    (h.n.comp (h := fun q : (C × ℕ × ℕ) × ℕ => (q.1.1, q.2)) (by fun_prop)) (by fun_prop)

@[fun_prop] theorem zAt_polyT {c : α → C} {x G a : α → ℕ} {z : α → List Bool} (hc : PolyT c) (hx : PolyT x) (hG : PolyT G)
    (hz : PolyT z) (ha : PolyT a) : PolyT fun t => zAt K g Np (c t) (x t) (G t) (z t) (a t) := by
  unfold zAt; fun_prop (disch := assumption)

theorem nStates_polyT : PolyT (nStates K g Np) :=
  PolyT.two_pow ((stLen_unary K g h).comp (h := fun u : X0 C => (u.1.1, u.1.2, u.2.1)) (by fun_prop))

@[fun_prop] theorem zOf_polyT : PolyT (zOf K g Np) :=
  PolyT.toWord' (n := fun u : X0 C × ℕ => stLen K g Np u.1.1.1 u.1.1.2 u.1.2.1) (y := fun u => u.2)
    ((stLen_unary K g h).comp (h := fun u : X0 C × ℕ => (u.1.1.1, u.1.1.2, u.1.2.1)) (by fun_prop)) (by fun_prop)

@[fun_prop] theorem zA_polyT {u : α → X0 C × ℕ} {a : α → ℕ} (hu : PolyT u) (ha : PolyT a) :
    PolyT fun t => zA K g Np (u t) (a t) := by
  unfold zA; fun_prop (disch := assumption)

theorem qW_polyT : PolyT (qW K g Np) := by
  unfold qW; fun_prop (disch := assumption)

@[fun_prop] theorem lbLens_polyT {c : α → C} {x G G' : α → ℕ} (hc : PolyT c) (hx : PolyT x) (hG : PolyT G)
    (hG' : PolyT G') : PolyT fun t => lbLens K g Np (c t) (x t) (G t) (G' t) := by
  unfold lbLens; fun_prop (disch := assumption)

@[fun_prop] theorem lbLen_polyT {c : α → C} {x G G' : α → ℕ} (hc : PolyT c) (hx : PolyT x) (hG : PolyT G)
    (hG' : PolyT G') : PolyT fun t => lbLen K g Np (c t) (x t) (G t) (G' t) := by
  unfold lbLen; fun_prop (disch := assumption)

@[fun_prop] theorem lAt_polyT {c : α → C} {x G G' : α → ℕ} {θ : α → List Bool} {p : α → ℕ × ℕ} (hc : PolyT c)
    (hx : PolyT x) (hG : PolyT G) (hG' : PolyT G') (hθ : PolyT θ) (hp : PolyT p) :
    PolyT fun t => lAt K g Np (c t) (x t) (G t) (G' t) (θ t) (p t) := by
  unfold lAt; fun_prop (disch := assumption)

theorem rowSum_unary : Unary (fun p : C × ℕ => rowSum g Np p.1 p.2) :=
  unary_sum_map (f := fun (p : C × ℕ) b => Np.cap p.1 p.2 b) (l := fun p => (List.range g).filter fun b => b != p.2)
    (h.cap.comp (h := fun q : (C × ℕ) × ℕ => (q.1.1, q.1.2, q.2)) (by fun_prop)) (by fun_prop)

theorem Uc_unary : Unary (Uc g Np) :=
  unary_sum_map (f := fun (c : C) a => rowSum g Np c a) (l := fun _ => List.range g) (rowSum_unary g h) (by fun_prop)

@[fun_prop] theorem Pc_polyT : PolyT (Pc g Np) :=
  foldr_max_polyT (PolyT.map (f := fun (c : C) a => rowSum g Np c a) (rowSum_unary g h).poly (by fun_prop))

@[fun_prop] theorem betaC_polyT : PolyT (betaC K g Np) := by
  have := (Uc_unary g h).poly
  unfold betaC Colouring.beta; fun_prop (disch := assumption)

omit h [Enc C] in
theorem Pc_le_Uc (Np : PNet C) (c : C) : Pc g Np c ≤ Uc g Np c := by
  unfold Pc Uc
  generalize (List.range g).map (rowSum g Np c) = l
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.foldr_cons, List.sum_cons]; omega

theorem validB_polyT : PolyT (validB K g Np) := by
  unfold validB; fun_prop (disch := assumption)

@[fun_prop] theorem labOf_polyT {u : α → X0 C} {a b : α → ℕ} (hu : PolyT u) (ha : PolyT a) (hb : PolyT b) :
    PolyT fun t => labOf K g Np (u t) (a t) (b t) := by
  unfold labOf; fun_prop (disch := assumption)

end

theorem isOne_polyT : PolyT (isOne K g : (X0 C × ℕ) × ℕ → Bool) := by unfold isOne; fun_prop

theorem isW_polyT : PolyT (isW g : (X0 C × ℕ) × ℕ → Bool) := by unfold isW; fun_prop

theorem isPsi_polyT : PolyT (isPsi K g : (X0 C × ℕ) × ℕ → Bool) := by unfold isPsi; fun_prop

theorem nPairs_polyT : PolyT (nPairs g : X0 C × ℕ → ℕ) := by unfold nPairs; fun_prop

theorem nCol_polyT : PolyT (nCol K g : C → ℕ) := by unfold nCol; fun_prop

theorem zeroOf_polyT : PolyT (zeroOf : C → ℤ) := by unfold zeroOf; fun_prop

/-- The label with number u.2 of the pair with number u.1.2. -/
def capWord (g : ℕ) (Np : PNet C) (u : ((X0 C × ℕ) × ℕ) × ℕ) : List Bool :=
  toWord (Np.cap u.1.1.1.1.1 (u.1.2 / g) (u.1.2 % g)) u.2

section

variable (h : Np.Keeps)
include h

theorem qF_polyT : PolyT (qF K g Np) := by
  unfold qF; fun_prop (disch := assumption)

@[fun_prop] theorem capWord_polyT : PolyT (capWord g Np) :=
  PolyT.toWord' (n := fun u : ((X0 C × ℕ) × ℕ) × ℕ => Np.cap u.1.1.1.1.1 (u.1.2 / g) (u.1.2 % g)) (y := fun u => u.2)
    (h.cap.comp (h := fun u : ((X0 C × ℕ) × ℕ) × ℕ => (u.1.1.1.1.1, u.1.2 / g, u.1.2 % g)) (by fun_prop)) (by fun_prop)

end

end Groundwork.Prog.NetE
