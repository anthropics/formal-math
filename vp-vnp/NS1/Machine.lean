/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Sum machines

Data are binary trees. A program is a formula of a small functional language; it is applied to a tree. A formula may
guess a bit, reject, multiply the weight of the run by a fixed constant `θ` of the ring `A` (named by a list of
bits), or by a constant that is *only named* (`mul`); the names are kept in the *bill* of the run. `run a b` applies
the program that is the value of `a` to the value of `b`. Every step costs 1.

`Ev θ F x l`: all runs of the formula `F` at the tree `x` stop, and `l` is the list of the accepting runs.
-/

namespace NS1

/-- Binary trees. -/
inductive Tree where
  /-- the empty tree -/
  | nil
  /-- a tree with two subtrees -/
  | cons (a b : Tree)
  deriving DecidableEq

namespace Tree

/-- First subtree. -/
def hd : Tree → Tree
  | nil => nil
  | cons a _ => a

/-- Second subtree. -/
def tl : Tree → Tree
  | nil => nil
  | cons _ b => b

/-- The number of nodes. -/
def size : Tree → ℕ
  | nil => 1
  | cons a b => a.size + b.size + 1

/-- The length of a tree as a list. -/
def len : Tree → ℕ
  | nil => 0
  | cons _ b => b.len + 1

/-- A tree as a list of bits. -/
def path : Tree → List Bool
  | nil => []
  | cons a b => decide (a ≠ nil) :: b.path

/-- A tree as a list of trees. -/
def toList : Tree → List Tree
  | nil => []
  | cons a b => a :: b.toList

/-- The number `k` as a tree. -/
def num : ℕ → Tree
  | 0 => nil
  | k + 1 => cons nil (num k)

/-- The bit 1. -/
def one : Tree := cons nil nil

/-- A bit. -/
def bit (b : Bool) : Tree := if b then one else nil

/-- A list of bits as a tree. -/
def ofBits : List Bool → Tree
  | [] => nil
  | b :: w => cons (bit b) (ofBits w)

@[simp] theorem hd_cons (a b : Tree) : (cons a b).hd = a := rfl
@[simp] theorem tl_cons (a b : Tree) : (cons a b).tl = b := rfl
@[simp] theorem hd_nil : nil.hd = nil := rfl
@[simp] theorem tl_nil : nil.tl = nil := rfl
@[simp] theorem len_num (k : ℕ) : (num k).len = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [num, len, ih]

theorem size_pos (x : Tree) : 0 < x.size := by cases x <;> simp [size]

theorem size_hd_le (x : Tree) : x.hd.size ≤ x.size := by
  cases x with
  | nil => exact le_rfl
  | cons a b => simp only [hd, size]; omega

theorem size_tl_le (x : Tree) : x.tl.size ≤ x.size := by
  cases x with
  | nil => exact le_rfl
  | cons a b => simp only [tl, size]; omega

@[simp] theorem path_ofBits (w : List Bool) : (ofBits w).path = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [ofBits, path, ih]
    cases b <;> simp [bit, one]

theorem bit_ne_nil {b : Bool} : bit b ≠ nil ↔ b = true := by cases b <;> simp [bit, one]

theorem size_ofBits (w : List Bool) : (ofBits w).size ≤ 4 * w.length + 1 := by
  induction w with
  | nil => simp [ofBits, size]
  | cons b w ih =>
    have : (bit b).size ≤ 3 := by cases b <;> simp [bit, one, size]
    simp only [ofBits, size, List.length_cons]
    omega

end Tree

open _root_.NS1.Tree

/-- Formulas. -/
inductive Fm where
  /-- a fixed tree -/
  | quote (c : Tree)
  /-- the argument -/
  | id
  /-- first subtree -/
  | hd (a : Fm)
  /-- second subtree -/
  | tl (a : Fm)
  /-- a tree with two given subtrees -/
  | cons (a b : Fm)
  /-- if the value of `a` is not empty then `b` else `c` -/
  | ite (a b c : Fm)
  /-- apply the program that is the value of `a` to the value of `b` -/
  | run (a b : Fm)
  /-- guess a bit -/
  | guess
  /-- reject -/
  | fail
  /-- multiply the weight by the constant of `A` that is named by the value of `a` -/
  | theta (a : Fm)
  /-- multiply the weight by the constant that is named by the value of `a` -/
  | mul (a : Fm)

namespace Fm

/-- Formulas as trees. -/
def code : Fm → Tree
  | quote c => .cons (num 0) c
  | id => .cons (num 1) .nil
  | hd a => .cons (num 2) a.code
  | tl a => .cons (num 3) a.code
  | cons a b => .cons (num 4) (.cons a.code b.code)
  | ite a b c => .cons (num 5) (.cons a.code (.cons b.code c.code))
  | run a b => .cons (num 6) (.cons a.code b.code)
  | guess => .cons (num 7) .nil
  | fail => .cons (num 8) .nil
  | theta a => .cons (num 9) a.code
  | mul a => .cons (num 10) a.code

/-- Every tree is read as a formula. -/
def ofTree : Tree → Fm
  | .nil => quote .nil
  | .cons o a =>
    match o.len with
    | 0 => quote a
    | 1 => id
    | 2 => hd (ofTree a)
    | 3 => tl (ofTree a)
    | 4 => cons (ofTree a.hd) (ofTree a.tl)
    | 5 => ite (ofTree a.hd) (ofTree a.tl.hd) (ofTree a.tl.tl)
    | 6 => run (ofTree a.hd) (ofTree a.tl)
    | 7 => guess
    | 8 => fail
    | 9 => theta (ofTree a)
    | 10 => mul (ofTree a)
    | _ => fail
  termination_by x => x.size
  decreasing_by
    all_goals
      have h1 := size_hd_le a
      have h2 := size_tl_le a
      have h3 := size_hd_le a.tl
      have h4 := size_tl_le a.tl
      simp only [Tree.size]
      omega

theorem ofTree_code (F : Fm) : ofTree F.code = F := by
  induction F with
  | quote c => rw [code, ofTree]; rfl
  | id => rw [code, ofTree]; rfl
  | hd a ih => rw [code, ofTree]; simp [ih]
  | tl a ih => rw [code, ofTree]; simp [ih]
  | cons a b iha ihb => rw [code, ofTree]; simp [iha, ihb]
  | ite a b c iha ihb ihc => rw [code, ofTree]; simp [iha, ihb, ihc]
  | run a b iha ihb => rw [code, ofTree]; simp [iha, ihb]
  | guess => rw [code, ofTree]; simp
  | fail => rw [code, ofTree]; simp
  | theta a ih => rw [code, ofTree]; simp [ih]
  | mul a ih => rw [code, ofTree]; simp [ih]

end Fm

variable {A : Type} [CommRing A]

/-- An accepting run: its cost, its weight, the names of the constants it wants, its value. -/
structure Run (A : Type) where
  /-- number of steps -/
  cost : ℕ
  /-- weight -/
  th : A
  /-- names of constants that the run multiplies by -/
  bill : List (List Bool)
  /-- value -/
  out : Tree

namespace Run

/-- One run after the other. -/
def seq (r s : Run A) : Run A := ⟨r.cost + s.cost, r.th * s.th, r.bill ++ s.bill, s.out⟩

/-- One more step, with value `o`. -/
def tick (r : Run A) (o : Tree) : Run A := ⟨r.cost + 1, r.th, r.bill, o⟩

/-- A run without guesses and weights. -/
def det (k : ℕ) (o : Tree) : Run A := ⟨k, 1, [], o⟩

end Run

/-- All runs of the formula at the tree stop; the list of the accepting runs. -/
inductive Ev (θ : List Bool → A) : Fm → Tree → List (Run A) → Prop
  | quote (c x : Tree) : Ev θ (.quote c) x [.det 1 c]
  | id (x : Tree) : Ev θ .id x [.det 1 x]
  | hd {a : Fm} {x : Tree} {l : List (Run A)} : Ev θ a x l → Ev θ (.hd a) x (l.map fun r => r.tick r.out.hd)
  | tl {a : Fm} {x : Tree} {l : List (Run A)} : Ev θ a x l → Ev θ (.tl a) x (l.map fun r => r.tick r.out.tl)
  | cons {a b : Fm} {x : Tree} {la lb : List (Run A)} : Ev θ a x la → Ev θ b x lb →
      Ev θ (.cons a b) x (la.flatMap fun r => lb.map fun s => (r.seq s).tick (.cons r.out s.out))
  | ite {a b c : Fm} {x : Tree} {la : List (Run A)} {L : Run A → List (Run A)} : Ev θ a x la →
      (∀ r ∈ la, r.out ≠ .nil → Ev θ b x (L r)) → (∀ r ∈ la, r.out = .nil → Ev θ c x (L r)) →
      Ev θ (.ite a b c) x (la.flatMap fun r => (L r).map fun s => (r.seq s).tick s.out)
  | run {a b : Fm} {x : Tree} {la lb : List (Run A)} {L : Run A → Run A → List (Run A)} : Ev θ a x la → Ev θ b x lb →
      (∀ r ∈ la, ∀ s ∈ lb, Ev θ (Fm.ofTree r.out) s.out (L r s)) →
      Ev θ (.run a b) x (la.flatMap fun r => lb.flatMap fun s => (L r s).map fun t => ((r.seq s).seq t).tick t.out)
  | guess (x : Tree) : Ev θ .guess x [.det 1 .nil, .det 1 Tree.one]
  | fail (x : Tree) : Ev θ .fail x []
  | theta {a : Fm} {x : Tree} {l : List (Run A)} : Ev θ a x l →
      Ev θ (.theta a) x (l.map fun r => ⟨r.cost + 1, r.th * θ r.out.path, r.bill, .nil⟩)
  | mul {a : Fm} {x : Tree} {l : List (Run A)} : Ev θ a x l →
      Ev θ (.mul a) x (l.map fun r => ⟨r.cost + 1, r.th, r.bill ++ [r.out.path], .nil⟩)

variable {θ : List Bool → A}

/-- The list of the accepting runs is determined. -/
theorem Ev.unique {F : Fm} {x : Tree} {l l' : List (Run A)} (h : Ev θ F x l) (h' : Ev θ F x l') : l = l' := by
  induction h generalizing l' with
  | quote c x => cases h'; rfl
  | id x => cases h'; rfl
  | hd _ ih => cases h' with | hd h => rw [ih h]
  | tl _ ih => cases h' with | tl h => rw [ih h]
  | cons _ _ iha ihb => cases h' with | cons ha hb => rw [iha ha, ihb hb]
  | ite _ _ _ iha ihb ihc =>
    cases h' with
    | ite ha hb hc =>
      obtain rfl := iha ha
      refine List.flatMap_congr fun r hr => ?_
      by_cases h : r.out = .nil
      · rw [ihc r hr h (hc r hr h)]
      · rw [ihb r hr h (hb r hr h)]
  | run _ _ _ iha ihb ih =>
    cases h' with
    | run ha hb h =>
      obtain rfl := iha ha
      obtain rfl := ihb hb
      refine List.flatMap_congr fun r hr => List.flatMap_congr fun s hs => ?_
      rw [ih r hr s hs (h r hr s hs)]
  | guess x => cases h'; rfl
  | fail x => cases h'; rfl
  | theta _ ih => cases h' with | theta h => rw [ih h]
  | mul _ ih => cases h' with | mul h => rw [ih h]

variable (θ) in
/-- All runs stop. -/
def Hl (F : Fm) (x : Tree) : Prop := ∃ l, Ev θ F x l

open Classical in
variable (θ) in
/-- The accepting runs (if all runs stop). -/
noncomputable def evl (F : Fm) (x : Tree) : List (Run A) := if h : Hl θ F x then h.choose else []

theorem Hl.ev {F : Fm} {x : Tree} (h : Hl θ F x) : Ev θ F x (evl θ F x) := by
  rw [evl, dif_pos h]
  exact h.choose_spec

theorem Ev.hl {F : Fm} {x : Tree} {l : List (Run A)} (h : Ev θ F x l) : Hl θ F x := ⟨l, h⟩

theorem Ev.evl {F : Fm} {x : Tree} {l : List (Run A)} (h : Ev θ F x l) : evl θ F x = l := h.hl.ev.unique h

theorem Ev.run' {a b : Fm} {x : Tree} {la lb : List (Run A)} (ha : Ev θ a x la) (hb : Ev θ b x lb)
    (h : ∀ r ∈ la, ∀ s ∈ lb, Hl θ (Fm.ofTree r.out) s.out) : Ev θ (.run a b) x
      (la.flatMap fun r => lb.flatMap fun s => (NS1.evl θ (Fm.ofTree r.out) s.out).map fun t =>
        ((r.seq s).seq t).tick t.out) :=
  .run ha hb fun r hr s hs => (h r hr s hs).ev

/-- A run without guesses and weights. -/
def Dt (θ : List Bool → A) (F : Fm) (x o : Tree) (k : ℕ) : Prop := Ev θ F x [.det k o]

theorem Dt.quote (c x : Tree) : Dt θ (.quote c) x c 1 := Ev.quote c x

theorem Dt.id (x : Tree) : Dt θ .id x x 1 := Ev.id x

theorem Dt.hd {a : Fm} {x o : Tree} {k : ℕ} (h : Dt θ a x o k) : Dt θ (.hd a) x o.hd (k + 1) := Ev.hd h

theorem Dt.tl {a : Fm} {x o : Tree} {k : ℕ} (h : Dt θ a x o k) : Dt θ (.tl a) x o.tl (k + 1) := Ev.tl h

theorem Dt.cons {a b : Fm} {x o p : Tree} {k j : ℕ} (ha : Dt θ a x o k) (hb : Dt θ b x p j) :
    Dt θ (.cons a b) x (.cons o p) (k + j + 1) := by
  have := Ev.cons ha hb
  simpa [Dt, Run.det, Run.seq, Run.tick] using this

/-- Weights and costs of runs after a step without guesses. -/
def Run.delay (k : ℕ) (r : Run A) : Run A := ⟨k + r.cost, r.th, r.bill, r.out⟩

theorem Ev.ite_true {a b c : Fm} {x o : Tree} {k : ℕ} {l : List (Run A)} (ha : Dt θ a x o k) (ho : o ≠ .nil)
    (hb : Ev θ b x l) : Ev θ (.ite a b c) x (l.map (Run.delay (k + 1))) := by
  have := Ev.ite (c := c) (L := fun _ => l) ha (fun r _ _ => hb) (fun r hr h => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact absurd h ho)
  convert this using 1
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine List.map_congr_left fun r _ => ?_
  simp [Run.delay, Run.det, Run.seq, Run.tick]
  omega

theorem Ev.ite_false {a b c : Fm} {x : Tree} {k : ℕ} {l : List (Run A)} (ha : Dt θ a x .nil k)
    (hc : Ev θ c x l) : Ev θ (.ite a b c) x (l.map (Run.delay (k + 1))) := by
  have := Ev.ite (b := b) (L := fun _ => l) ha (fun r hr h => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact absurd rfl h) (fun r _ _ => hc)
  convert this using 1
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine List.map_congr_left fun r _ => ?_
  simp [Run.delay, Run.det, Run.seq, Run.tick]
  omega

theorem Ev.run_det {a b : Fm} {x p d : Tree} {k j : ℕ} {l : List (Run A)} (ha : Dt θ a x p k) (hb : Dt θ b x d j)
    (h : Ev θ (Fm.ofTree p) d l) : Ev θ (.run a b) x (l.map (Run.delay (k + j + 1))) := by
  have := Ev.run (L := fun _ _ => l) ha hb (fun r hr s hs => by
    simp only [List.mem_singleton] at hr hs
    subst hr hs
    exact h)
  convert this using 1
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine List.map_congr_left fun r _ => ?_
  simp [Run.delay, Run.det, Run.seq, Run.tick]
  omega

/-- `let`: apply `body` to the value of `e`. -/
def lett (e body : Fm) : Fm := .run (.quote body.code) e

theorem Ev.lett {e body : Fm} {x : Tree} {le : List (Run A)} (he : Ev θ e x le)
    (h : ∀ s ∈ le, Hl θ body s.out) : Ev θ (lett e body) x
      (le.flatMap fun s => (NS1.evl θ body s.out).map fun t => ⟨s.cost + t.cost + 2, s.th * t.th, s.bill ++ t.bill, t.out⟩) := by
  have := Ev.run' (Dt.quote (θ := θ) body.code x) he (fun r hr s hs => by
    simp only [List.mem_singleton] at hr
    subst hr
    simp only [Run.det, Fm.ofTree_code]
    exact h s hs)
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at this
  refine Eq.mp ?_ this
  unfold NS1.lett
  congr 1
  refine List.flatMap_congr fun s _ => ?_
  simp only [Run.det, Fm.ofTree_code]
  refine List.map_congr_left fun r _ => ?_
  simp only [Run.seq, Run.tick, one_mul, List.nil_append, Run.mk.injEq, and_true]
  omega

end NS1
