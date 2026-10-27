/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Lib.List1

/-! Polynomial time for lists: heads and tails, flatten, zip, options, and equality of lists.
Every lemma tagged `fun_prop` says that the operation it is named after preserves `PolyT`. -/

@[expose] public section

namespace Groundwork.PolyT

variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

@[fun_prop] theorem flatten {l : α → List (List β)} (hl : PolyT l) :
    PolyT (fun x => (l x).flatten) :=
  (flatMap (f := fun _ b => b) (by fun_prop) hl).congr fun x => by simp

@[fun_prop] theorem isEmpty {l : α → List β} (hl : PolyT l) :
    PolyT (fun x => (l x).isEmpty) :=
  (listCases (d := fun _ => true) (f := fun _ _ _ => false) hl (by fun_prop) (by fun_prop)).congr
    fun x => by cases l x <;> rfl

@[fun_prop] theorem head? {l : α → List β} (hl : PolyT l) :
    PolyT (fun x => (l x).head?) :=
  (listCases (d := fun _ => none) (f := fun _ e _ => some e) hl (by fun_prop) (by fun_prop)).congr
    fun x => by cases l x <;> rfl

@[fun_prop] theorem headD {l : α → List β} {d : α → β} (hl : PolyT l) (hd : PolyT d) :
    PolyT (fun x => (l x).headD (d x)) :=
  (listCases (d := d) (f := fun _ e _ => e) hl hd (by fun_prop)).congr
    fun x => by cases l x <;> rfl

@[fun_prop] theorem tail {l : α → List β} (hl : PolyT l) :
    PolyT (fun x => (l x).tail) :=
  (listCases (d := fun _ => []) (f := fun _ _ r => r) hl (by fun_prop) (by fun_prop)).congr
    fun x => by cases l x <;> rfl

@[fun_prop] theorem getLast? {l : α → List β} (hl : PolyT l) :
    PolyT (fun x => (l x).getLast?) :=
  (head? (reverse hl)).congr fun x => by simp

/-- One step of the zip: the state holds what is left of the second list and the pairs made so far,
last pair first. -/
def zipStep (s : List γ × List (β × γ)) (e : β) : List γ × List (β × γ) :=
  match s.1 with
  | [] => s
  | c :: r => (r, (e, c) :: s.2)

/-- The step of the zip is polynomial-time. -/
theorem zipStep_poly : PolyT fun p : (List γ × List (β × γ)) × β => zipStep p.1 p.2 :=
  (listCases (l := fun p : (List γ × List (β × γ)) × β => p.1.1) (d := fun p => p.1)
    (f := fun p c r => (r, (p.2, c) :: p.1.2)) (by fun_prop) (by fun_prop) (by fun_prop)).congr
    fun p => by rcases p with ⟨⟨_ | ⟨c, r⟩, acc⟩, e⟩ <;> rfl

omit [Enc β] [Enc γ] in
/-- What the fold of the step computes. -/
theorem foldl_zipStep (l : List β) (r : List γ) (acc : List (β × γ)) :
    l.foldl zipStep (r, acc) = (r.drop l.length, (l.zip r).reverse ++ acc) := by
  induction l generalizing r acc with
  | nil => simp
  | cons e l ih =>
    cases r with
    | nil => simpa [zipStep] using ih [] acc
    | cons c r => simpa [zipStep] using ih r ((e, c) :: acc)

/-- The zip is a fold of `zipStep`, then a reversal. -/
@[fun_prop] theorem zip {l : α → List β} {l' : α → List γ} (hl : PolyT l) (hl' : PolyT l') :
    PolyT (fun x => (l x).zip (l' x)) := by
  obtain ⟨_, t, ht, -, -, hlen⟩ := hl.elim
  have h : PolyT fun x => (l x).foldl zipStep (l' x, ([] : List (β × γ))) :=
    foldl_add (g := fun _ => zipStep) hl (by fun_prop)
      (comp (g := fun p : α × (List γ × List (β × γ)) × β => (p.2.1, p.2.2)) zipStep_poly (by fun_prop))
      ⟨fun n => t n + 2, ht.add (PB.const 2), by
        rintro x ⟨_ | ⟨c, r⟩, acc⟩ e he
        · exact Nat.le_add_right _ _
        · have h1 := len_le_of_mem he
          have h2 := hlen x
          change len (r, (e, c) :: acc) ≤ len (c :: r, acc) + (t (len x) + 2)
          rw [len_pair, len_pair, len_cons, len_cons, len_pair]
          omega⟩
  exact (reverse (snd h)).congr fun x => by simp [foldl_zipStep]

@[fun_prop] theorem optionMap {f : α → β → γ} {o : α → Option β} (hf : PolyT fun p : α × β => f p.1 p.2) (ho : PolyT o) :
    PolyT (fun x => (o x).map (f x)) :=
  (optionElim (d := fun _ => none) (f := fun x b => some (f x b)) ho (by fun_prop) (by fun_prop)).congr
    fun x => by cases o x <;> rfl

@[fun_prop] theorem optionBind {f : α → β → Option γ} {o : α → Option β} (hf : PolyT fun p : α × β => f p.1 p.2) (ho : PolyT o) :
    PolyT (fun x => (o x).bind (f x)) :=
  (optionElim (d := fun _ => none) (f := f) ho (by fun_prop) hf).congr
    fun x => by cases o x <;> rfl

@[fun_prop] theorem optionGetD {o : α → Option β} {d : α → β} (ho : PolyT o) (hd : PolyT d) :
    PolyT (fun x => (o x).getD (d x)) :=
  (optionElim (d := d) (f := fun _ b => b) ho hd (by fun_prop)).congr
    fun x => by cases o x <;> rfl

@[fun_prop] theorem optionIsSome {o : α → Option β} (ho : PolyT o) :
    PolyT (fun x => (o x).isSome) :=
  (optionElim (d := fun _ => false) (f := fun _ _ => true) ho (by fun_prop) (by fun_prop)).congr
    fun x => by cases o x <;> rfl

@[fun_prop] theorem optionIsNone {o : α → Option β} (ho : PolyT o) :
    PolyT (fun x => (o x).isNone) :=
  (optionElim (d := fun _ => true) (f := fun _ _ => false) ho (by fun_prop) (by fun_prop)).congr
    fun x => by cases o x <;> rfl

/-- One step of the comparison of two lists: the state holds "equal so far" and what is left of the
second list. -/
def eqStep [DecidableEq β] (s : Bool × List β) (e : β) : Bool × List β :=
  match s.2 with
  | [] => (false, [])
  | c :: r => (s.1 && decide (e = c), r)

/-- The step of the comparison is polynomial-time. -/
theorem eqStep_poly [DecidableEq β] [EqT β] : PolyT fun p : (Bool × List β) × β => eqStep p.1 p.2 :=
  (listCases (l := fun p : (Bool × List β) × β => p.1.2) (d := fun _ => (false, []))
    (f := fun p c r => (p.1.1 && decide (p.2 = c), r)) (by fun_prop) (by fun_prop) (by fun_prop)).congr
    fun p => by rcases p with ⟨⟨b, _ | ⟨c, r⟩⟩, e⟩ <;> rfl

omit [Enc β] in
/-- What the fold of the step computes. -/
theorem foldl_eqStep [DecidableEq β] (l r : List β) (b : Bool) :
    ((l.foldl eqStep (b, r)).1 && (l.foldl eqStep (b, r)).2.isEmpty) = (b && decide (l = r)) := by
  induction l generalizing r b with
  | nil => cases r <;> simp
  | cons e l ih =>
    cases r with
    | nil => simpa [eqStep] using ih [] false
    | cons c r => simpa [eqStep, Bool.and_assoc] using ih r (b && decide (e = c))

/-- Equality of lists is polynomial-time if equality of their elements is: a fold of `eqStep`. -/
instance [DecidableEq β] [EqT β] : EqT (List β) := ⟨by
  have hb : ∀ b : Bool, len b = 1 := fun _ => rfl
  have h : PolyT fun p : List β × List β => p.1.foldl eqStep (true, p.2) :=
    foldl_add (g := fun _ => eqStep) (by fun_prop) (by fun_prop)
      (comp (g := fun p : (List β × List β) × (Bool × List β) × β => (p.2.1, p.2.2)) eqStep_poly (by fun_prop))
      ⟨fun _ => 0, PB.const 0, by
        rintro x ⟨b, _ | ⟨c, r⟩⟩ e -
        · change len (false, ([] : List β)) ≤ len (b, ([] : List β)) + 0
          rw [len_pair, len_pair, hb, hb]
        · change len (b && decide (e = c), r) ≤ len (b, c :: r) + 0
          rw [len_pair, len_pair, len_cons, hb, hb]
          omega⟩
  exact (and' (fst h) (isEmpty (snd h))).congr fun p => by simpa using foldl_eqStep p.1 p.2 true⟩

end Groundwork.PolyT
