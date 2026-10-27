/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Enc
public import ToTuring.TM.Ops
public import ToTuring.Bound
public import Mathlib.Tactic.FunProp

/-! Polynomial time on Mathlib's multi-stack machines, defined here from Mathlib alone. `PolyT f`:
some fragment turns the word
of x, on top of the main stack, into the word of f x, within c·(len x + 1)^c steps, and leaves alone
whatever lies beneath it
and on the other three stacks. Because of this frame all fragments can share the same stacks, and
closure under composition,
pairing, case distinction and folds is proved by gluing fragments. `PolyT` is a proposition: the
fragment is hidden under an
existential quantifier, so the proposition `PolyT f` names no fragment; fragments are defined in TM/
and Closure/, glued
together in the proofs of the closure lemmas, and assembled into one machine by `exists_tm`.

What is not asked: nothing is ever decoded, the fragment must behave correctly only on words of
values, and the tree of a
value (`Enc`) need not determine the value. For the states of a computation, the encoding is chosen
by whoever proves
`IsPolyT`. None of this can weaken the end theorem, which does not mention `PolyT`: `Sat3.InTimeTM`
is about one of Mathlib's
machines, started on the bits of `Sat3.enc φ`. `exists_tm` (Machine/Host.lean) builds that machine
out of the fragments and
proves that it runs to the output bit within a polynomial times the number of steps of the stepped
computation, whatever
encoding was chosen: the machine itself writes the word of the input from the raw bits, it reads the
answer off the word of
an optional bit, which does determine the bit, and `Carried` ties the length of the words of the
states to the size in which
the files of proof/machines/StepMachines/ bound them. -/

@[expose] public section

namespace Groundwork

open TM

/-- f is computed in polynomial time on top of the main stack: for some constant c, one fragment
turns the word of x, with
any M beneath it on the main stack and any contents A, B, N of the other three stacks, into the word
of f x with the same M,
A, B, N, in at most c·(len x + 1)^c steps; and the word of f x has at most c·(len x + 1)^c symbols.
The definition says
nothing about words that are not words of values. -/
@[fun_prop] def PolyT {α β : Type} [Enc α] [Enc β] (f : α → β) : Prop :=
  ∃ (P : Fr) (c : ℕ),
    (∀ (x : α) (M A B N : List Sym), ∃ n ≤ c * (len x + 1) ^ c,
      P.Runs none (st (wd x ++ M) A B N) n (st (wd (f x) ++ M) A B N)) ∧
    ∀ x, len (f x) ≤ c * (len x + 1) ^ c

/-- How to prove PolyT: a fragment, a polynomial bound on its steps, a polynomial bound on the
length of the result. -/
theorem PolyT.of {α β : Type} [Enc α] [Enc β] {f : α → β} (P : Fr) {t s : ℕ → ℕ} (ht : PB t) (hs : PB s)
    (h : ∀ (x : α) (M A B N : List Sym), P.Within (st (wd x ++ M) A B N) (t (len x)) (st (wd (f x) ++ M) A B N))
    (hl : ∀ x, len (f x) ≤ s (len x)) : PolyT f := by
  obtain ⟨c, hc⟩ := ht
  obtain ⟨c', hc'⟩ := hs
  refine ⟨P, c + c', fun x M A B N => ?_, fun x => ?_⟩
  · obtain ⟨n, hn, hr⟩ := h x M A B N
    exact ⟨n, (hn.trans (hc _)).trans (PB.bound_le (Nat.le_add_right _ _) (Nat.le_add_right _ _)), hr⟩
  · exact ((hl x).trans (hc' _)).trans (PB.bound_le (Nat.le_add_left _ _) (Nat.le_add_left _ _))

/-- How to use PolyT: one monotone polynomial bound for the steps and for the length of the result. -/
theorem PolyT.elim {α β : Type} [Enc α] [Enc β] {f : α → β} (h : PolyT f) : ∃ (P : Fr) (t : ℕ → ℕ), PB t ∧ Monotone t ∧
    (∀ (x : α) (M A B N : List Sym), P.Within (st (wd x ++ M) A B N) (t (len x)) (st (wd (f x) ++ M) A B N)) ∧
    ∀ x, len (f x) ≤ t (len x) := by
  obtain ⟨P, c, h1, h2⟩ := h
  exact ⟨P, fun n => c * (n + 1) ^ c, (PB.mono_bound c).1, (PB.mono_bound c).2, h1, h2⟩

/-- PolyT passes to a function with the same values. -/
theorem PolyT.congr {α β : Type} [Enc α] [Enc β] {f g : α → β} (h : PolyT f) (e : ∀ x, f x = g x) : PolyT g := by
  obtain rfl : f = g := funext e
  exact h

/-- Only words matter: if φ keeps the words of the inputs, and the words of g's values are those of
f ∘ φ, then g is
polynomial-time, computed by the same fragment as f. The types may differ. -/
theorem PolyT.of_wd {α β α' β' : Type} [Enc α] [Enc β] [Enc α'] [Enc β'] {f : α → β} (hf : PolyT f) {g : α' → β'}
    (φ : α' → α) (hφ : ∀ x, wd (φ x) = wd x) (hg : ∀ x, wd (g x) = wd (f (φ x))) : PolyT g := by
  obtain ⟨P, c, h1, h2⟩ := hf
  refine ⟨P, c, fun x M A B N => ?_, fun x => ?_⟩
  · have := h1 (φ x) M A B N
    simpa only [len, hφ, hg] using this
  · have := h2 (φ x)
    simpa only [len, hφ, hg] using this

/-- The number f x is computed in polynomial time in unary: as a list of that length. -/
def Unary {α : Type} [Enc α] (f : α → ℕ) : Prop := PolyT fun x => List.replicate (f x) ()

/-- Every part of the stepped computation M is polynomial-time, and the words of its states are at
most linear in their size. This
does not bound the number of steps that M takes; that bound comes from the files of
proof/machines/StepMachines/. The class holds
data, the encoding of the states; so theorems that assert it say `Nonempty (IsPolyT M)`. -/
class IsPolyT {α β : Type} [Enc α] [Enc β] (M : Stepped α β) where
  [enc : Enc M.σ]
  [carried : Carried M.σ]
  init : PolyT M.init
  step : PolyT M.step
  out : PolyT M.out

instance {α β : Type} [Enc α] [Enc β] (M : Stepped α β) [h : IsPolyT M] : Enc M.σ := h.enc
instance {α β : Type} [Enc α] [Enc β] (M : Stepped α β) [h : IsPolyT M] : Carried M.σ := h.carried

end Groundwork
