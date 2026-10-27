/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Fuel
public import StepMachines.Prog.Brute
public import StepMachines.Prog.Spec

/-! # Tables, instances and networks as data

Explicit tables, instances as data, networks given by plain functions. -/

@[expose] public section

namespace PaddedDescent.F

open Groundwork Groundwork.Prog

/-- The tables of an instance on K nodes with ℓ-bit labels: K rows; row v has 2^((K−1)ℓ) entries. -/
abbrev Tab := List (List ℤ)

/-- An instance as data: (ℓ in unary, tables). The number K of nodes is not stored; it is known from
the level. -/
abbrev PInst := U × Tab

/-- One step of the schedule, «g·g nodes → K nodes»: (K, g), both in unary. -/
abbrev Lvl := U × U

/-- The entry at the query q = (v, labels): the labels (the empty word at v itself) are written one
after the other and read as a number. -/
def look (T : Tab) (q : IQ) : ℤ := (T.getD q.1 []).getD (ofWord q.2.flatten) 0

/-- The instance that a table stands for. -/
def instOf {K : ℕ} (T : Tab) : Inst (Fin K) (List Bool) := fun v θ => look T (v.1, List.ofFn θ)

/-- The sum Z of an instance given as data, on K nodes. -/
def zval (K : ℕ) (I : PInst) : ℤ := Inst.ZW I.1.length [] (instOf (K := K) I.2)

/-- The labels at v written by the word w of (K−1)·ℓ bits. -/
def unflat (K ℓ v : ℕ) (w : List Bool) : List (List Bool) :=
  (List.range K).map fun u => if u = v then [] else block ℓ (if u < v then u else u - 1) w

/-- The table of the function F of queries. -/
def tabulate (pad : U) (K ℓ : ℕ) (F : IQ → ℤ) : Tab :=
  (List.range K).map fun v => (rng pad (2 ^ ((K - 1) * ℓ))).map fun i => F (v, unflat K ℓ v (toWord ((K - 1) * ℓ) i))

/-- I is an instance on K nodes with label length between 1 and Λ and entries of absolute value at
most 2^B. -/
structure WF (K Λ B : ℕ) (I : PInst) : Prop where
  lam_pos : 1 ≤ I.1.length
  lam_le : I.1.length ≤ Λ
  rows : I.2.length = K
  row_len : ∀ r ∈ I.2, r.length = 2 ^ ((K - 1) * I.1.length)
  abs_le : ∀ r ∈ I.2, ∀ z ∈ r, z.natAbs ≤ 2 ^ B

/-- A machine that has its answer at once and calls all its states small. Only used to quote the
value theorems of
StepMachines/Prog/NetVal.lean, which take a `PNet`. -/
def freeM {α β : Type} (f : α → β) : Stepped α β where
  σ := α
  sz := ⟨fun _ => 0⟩
  init := id
  step := id
  out a := some (f a)

/-- A network given by plain functions. -/
structure FNet (C : Type) where
  n : C → ℕ → ℕ
  cap : C → ℕ → ℕ → ℕ
  W : C × WQ → ℤ
  f : C × FQ → ℤ

def FNet.toP {C : Type} (F : FNet C) : PNet C := ⟨F.n, F.cap, freeM F.W, freeM F.f⟩

end PaddedDescent.F
