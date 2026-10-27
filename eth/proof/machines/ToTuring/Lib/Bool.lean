/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Closure.Fold
public import ToTuring.EncLemmas

/-! Closure lemmas for `PolyT`: if the arguments are computed in polynomial time, then so are
Boolean operations on them,
`decide` of propositions built from them with logical connectives, and equality tests (class `EqT`).
The lemmas are tagged for `fun_prop`, and each
is named after the function that it certifies. -/

@[expose] public section

namespace Groundwork.PolyT

variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

@[fun_prop] theorem and' {f g : α → Bool} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x && g x) := by
  exact (cond' hf hg (const false)).congr fun x => by cases f x <;> rfl

@[fun_prop] theorem or' {f g : α → Bool} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x || g x) := by
  exact (cond' hf (const true) hg).congr fun x => by cases f x <;> rfl

@[fun_prop] theorem not' {f : α → Bool} (hf : PolyT f) :
    PolyT (fun x => !f x) := by
  exact (cond' hf (const false) (const true)).congr fun x => by cases f x <;> rfl

@[fun_prop] theorem xor' {f g : α → Bool} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x ^^ g x) := by
  exact (cond' hf (not' hg) hg).congr fun x => by cases f x <;> cases g x <;> rfl

@[fun_prop] theorem toNat' {f : α → Bool} (hf : PolyT f) :
    PolyT (fun x => (f x).toNat) := by
  exact (cond' hf (const 1) (const 0)).congr fun x => by cases f x <;> rfl

@[fun_prop] theorem decide_eq_true {f : α → Bool} (hf : PolyT f) :
    PolyT (fun x => decide (f x = true)) := by
  exact hf.congr fun x => by cases f x <;> rfl

@[fun_prop] theorem decide_eq_false {f : α → Bool} (hf : PolyT f) :
    PolyT (fun x => decide (f x = false)) := by
  exact (not' hf).congr fun x => by cases f x <;> rfl

@[fun_prop] theorem decide_and {p q : α → Prop} [DecidablePred p] [DecidablePred q] (hp : PolyT fun x => decide (p x))
    (hq : PolyT fun x => decide (q x)) :
    PolyT (fun x => decide (p x ∧ q x)) := by
  exact (and' hp hq).congr fun x => (Bool.decide_and _ _).symm

@[fun_prop] theorem decide_or {p q : α → Prop} [DecidablePred p] [DecidablePred q] (hp : PolyT fun x => decide (p x))
    (hq : PolyT fun x => decide (q x)) :
    PolyT (fun x => decide (p x ∨ q x)) := by
  exact (or' hp hq).congr fun x => (Bool.decide_or _ _).symm

@[fun_prop] theorem decide_not {p : α → Prop} [DecidablePred p] (hp : PolyT fun x => decide (p x)) :
    PolyT (fun x => decide (¬ p x)) := by
  exact (not' hp).congr fun x => (_root_.decide_not (p := p x)).symm

/-- Equality on β can be tested in polynomial time. -/
class EqT (β : Type) [Enc β] [DecidableEq β] : Prop where
  eq : PolyT fun p : β × β => decide (p.1 = p.2)

@[fun_prop] theorem decide_eq [DecidableEq β] [EqT β] {f g : α → β} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => decide (f x = g x)) := by
  exact comp EqT.eq (prodMk hf hg)

@[fun_prop] theorem decide_ne [DecidableEq β] [EqT β] {f g : α → β} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => decide (f x ≠ g x)) := by
  exact decide_not (decide_eq hf hg)

/-- `==` in polynomial time. The `BEq` instance is a separate argument, lawful but not necessarily
the one made from
`DecidableEq`: the instances of Lean's core library on pairs, options and lists are not. `EqT` is
stated with `DecidableEq`. -/
@[fun_prop] theorem beq' [DecidableEq β] [EqT β] [BEq β] [LawfulBEq β] {f g : α → β} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x == g x) := by
  exact (decide_eq hf hg).congr fun x => (beq_eq_decide _ _).symm

/-- `!=` in polynomial time (`BEq` as for `beq'`). -/
@[fun_prop] theorem bne' [DecidableEq β] [EqT β] [BEq β] [LawfulBEq β] {f g : α → β} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x != g x) := by
  exact (not' (beq' hf hg)).congr fun _ => rfl

instance : EqT Bool :=
  ⟨(not' (xor' (fst id') (snd id'))).congr fun p => by rcases p with ⟨_ | _, _ | _⟩ <;> rfl⟩
instance : EqT Unit := ⟨(const true).congr fun _ => rfl⟩
instance [DecidableEq β] [DecidableEq γ] [EqT β] [EqT γ] : EqT (β × γ) :=
  ⟨(and' (decide_eq (fst (fst id')) (fst (snd id'))) (decide_eq (snd (fst id')) (snd (snd id')))).congr fun p => by
    rw [← Bool.decide_and]; exact decide_eq_decide.2 Prod.ext_iff.symm⟩
instance [DecidableEq β] [EqT β] : EqT (Option β) :=
  ⟨(optionElim (o := fun p : Option β × Option β => p.1) (d := fun p => p.2.elim true fun _ => false)
      (f := fun p a => p.2.elim false fun b => decide (a = b)) (fst id')
      (optionElim (f := fun _ _ => false) (snd id') (const true) (const false))
      (optionElim (o := fun q : (Option β × Option β) × β => q.1.2) (f := fun q b => decide (q.2 = b)) (snd (fst id'))
        (const false) (decide_eq (snd (fst id')) (snd id')))).congr fun p => by
    rcases p with ⟨_ | a, _ | b⟩ <;> simp⟩
instance [DecidableEq β] [DecidableEq γ] [EqT β] [EqT γ] : EqT (β ⊕ γ) :=
  ⟨(sumElim (s := fun p : (β ⊕ γ) × (β ⊕ γ) => p.1)
      (f := fun p a => p.2.elim (fun b => decide (a = b)) fun _ => false)
      (g := fun p a => p.2.elim (fun _ => false) fun b => decide (a = b)) (fst id')
      (sumElim (s := fun q : ((β ⊕ γ) × (β ⊕ γ)) × β => q.1.2) (f := fun q b => decide (q.2 = b)) (g := fun _ _ => false)
        (snd (fst id')) (decide_eq (snd (fst id')) (snd id')) (const false))
      (sumElim (s := fun q : ((β ⊕ γ) × (β ⊕ γ)) × γ => q.1.2) (f := fun _ _ => false) (g := fun q b => decide (q.2 = b))
        (snd (fst id')) (const false) (decide_eq (snd (fst id')) (snd id')))).congr fun p => by
    rcases p with ⟨a | a, b | b⟩ <;> simp⟩

end Groundwork.PolyT
