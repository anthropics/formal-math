/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.PolyT
public import ToTuring.EncLemmas

/-! Closure of the class `PolyT` under identity, constants, composition, pairing, projections and
the constructors of
Option, sums and lists. Every public lemma is in the form that the tactic `fun_prop` uses. -/

@[expose] public section

namespace Groundwork.PolyT

open TM Enc

variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

/-! The operations of the machine on the words of values. -/

section ops
variable (M A B N : List Sym)

private theorem dropW (x : α) : dropF.Within (st (wd x ++ M) A B N) (len x + 1) (st M A B N) :=
  dropF_within (toV x) M A B N

private theorem dupW (x : α) :
    dupF.Within (st (wd x ++ M) A B N) (3 * len x + 3) (st (wd x ++ (wd x ++ M)) A B N) :=
  dupF_within (toV x) M A B N

private theorem swapW (x : α) (y : β) :
    swapF.Within (st (wd x ++ (wd y ++ M)) A B N) (2 * (len x + len y) + 4) (st (wd y ++ (wd x ++ M)) A B N) :=
  swapF_within (toV x) (toV y) M A B N

private theorem consW (x : α) (y : β) :
    consF.Within (st (wd x ++ (wd y ++ M)) A B N) (2 * (len x + len y) + 6) (st (wd (x, y) ++ M) A B N) :=
  consF_within (toV x) (toV y) M A B N

private theorem unconsW (x : α) (y : β) :
    unconsF.Within (st (wd (x, y) ++ M) A B N) (2 * (len x + len y) + 6) (st (wd x ++ (wd y ++ M)) A B N) :=
  unconsF_within (toV x) (toV y) M A B N

end ops

/-- a·t + b is below a polynomial if t is. -/
private theorem pb_lin (a b : ℕ) {t : ℕ → ℕ} (ht : PB t) : PB fun n => a * t n + b :=
  ((PB.const a).mul ht).add (PB.const b)

@[fun_prop] theorem id' : PolyT (fun x : α => x) :=
  PolyT.of (pushW []) (PB.const 1) PB.id' (fun x M A B N => pushW_within (wd x ++ M) A B N []) fun _ => le_rfl
/-- Drop x; push the word of b. -/
@[fun_prop] theorem const (b : β) : PolyT (fun _ : α => b) :=
  PolyT.of (dropF.seq (pushW (wd b))) (t := fun n => n + 1 + 1) (s := fun _ => len b)
    ((PB.id'.add (PB.const 1)).add (PB.const 1)) (PB.const _)
    (fun x M A B N => (dropW M A B N x).seq (pushW_within M A B N (wd b))) fun _ => le_rfl
/-- Run the fragment of g, then that of f. -/
@[fun_prop] theorem comp {f : β → γ} {g : α → β} (hf : PolyT f) (hg : PolyT g) : PolyT (fun x => f (g x)) := by
  obtain ⟨P, t, ht, mt, hP, lP⟩ := hf.elim
  obtain ⟨Q, s, hs, -, hQ, lQ⟩ := hg.elim
  refine PolyT.of (Q.seq P) (t := fun n => s n + t (s n)) (s := fun n => t (s n)) (hs.add (ht.comp hs)) (ht.comp hs)
    (fun x M A B N => ?_) fun x => ?_
  · exact (hQ x M A B N).seq ((hP (g x) M A B N).mono (mt (lQ x)))
  · exact (lP (g x)).trans (mt (lQ x))
/-- Duplicate x; f on the copy on top; exchange; g on x, now on top; exchange; make the pair. -/
@[fun_prop] theorem prodMk {f : α → β} {g : α → γ} (hf : PolyT f) (hg : PolyT g) : PolyT (fun x => (f x, g x)) := by
  obtain ⟨P, t, ht, -, hP, lP⟩ := hf.elim
  obtain ⟨Q, s, hs, -, hQ, lQ⟩ := hg.elim
  refine PolyT.of (((((dupF.seq P).seq swapF).seq Q).seq swapF).seq consF)
    (t := fun n => (3 * n + 3) + t n + (2 * (t n + n) + 4) + s n + (2 * (s n + t n) + 4) + (2 * (t n + s n) + 6))
    (s := fun n => t n + s n + 2)
    ((((((pb_lin 3 3 PB.id').add ht).add (pb_lin 2 4 (ht.add PB.id'))).add hs).add (pb_lin 2 4 (hs.add ht))).add
      (pb_lin 2 6 (ht.add hs)))
    ((ht.add hs).add (PB.const 2)) (fun x M A B N => ?_) fun x => ?_
  · have h := (((((dupW M A B N x).seq (hP x (wd x ++ M) A B N)).seq (swapW M A B N (f x) x)).seq
      (hQ x (wd (f x) ++ M) A B N)).seq (swapW M A B N (g x) (f x))).seq (consW M A B N (f x) (g x))
    refine h.mono ?_
    have h1 := lP x
    have h2 := lQ x
    omega
  · have h1 := lP x
    have h2 := lQ x
    rw [len_pair]
    omega

private theorem fst0 : PolyT (fun p : β × γ => p.1) := by
  refine PolyT.of ((unconsF.seq swapF).seq dropF) (t := fun n => (2 * n + 6) + (2 * n + 4) + (n + 1)) (s := fun n => n)
    (((pb_lin 2 6 PB.id').add (pb_lin 2 4 PB.id')).add (PB.id'.add (PB.const 1))) PB.id' ?_ ?_
  · rintro ⟨a, b⟩ M A B N
    have h := ((unconsW M A B N a b).seq (swapW M A B N a b)).seq (dropW (wd a ++ M) A B N b)
    refine h.mono ?_
    have h1 := len_pair a b
    omega
  · rintro ⟨a, b⟩
    have h1 := len_pair a b
    change len a ≤ len (a, b)
    omega

private theorem snd0 : PolyT (fun p : β × γ => p.2) := by
  refine PolyT.of (unconsF.seq dropF) (t := fun n => (2 * n + 6) + (n + 1)) (s := fun n => n)
    ((pb_lin 2 6 PB.id').add (PB.id'.add (PB.const 1))) PB.id' ?_ ?_
  · rintro ⟨a, b⟩ M A B N
    have h := (unconsW M A B N a b).seq (dropW (wd b ++ M) A B N a)
    refine h.mono ?_
    have h1 := len_pair a b
    omega
  · rintro ⟨a, b⟩
    have h1 := len_pair a b
    change len b ≤ len (a, b)
    omega

@[fun_prop] theorem fst {f : α → β × γ} (hf : PolyT f) : PolyT (fun x => (f x).1) :=
  comp fst0 hf
@[fun_prop] theorem snd {f : α → β × γ} (hf : PolyT f) : PolyT (fun x => (f x).2) :=
  comp snd0 hf

/-! Constructors. Each of them is written as a pair. -/
@[fun_prop] theorem some' {f : α → β} (hf : PolyT f) : PolyT (fun x => some (f x)) :=
  of_wd (prodMk hf (const ())) id (fun _ => rfl) fun _ => rfl
@[fun_prop] theorem inl' {f : α → β} (hf : PolyT f) : PolyT (fun x => (Sum.inl (f x) : β ⊕ γ)) :=
  of_wd (prodMk (const false) hf) id (fun _ => rfl) fun _ => rfl
@[fun_prop] theorem inr' {f : α → γ} (hf : PolyT f) : PolyT (fun x => (Sum.inr (f x) : β ⊕ γ)) :=
  of_wd (prodMk (const true) hf) id (fun _ => rfl) fun _ => rfl
@[fun_prop] theorem cons' {f : α → β} {l : α → List β} (hf : PolyT f) (hl : PolyT l) : PolyT (fun x => f x :: l x) :=
  of_wd (prodMk hf hl) id (fun _ => rfl) fun _ => rfl

end Groundwork.PolyT
