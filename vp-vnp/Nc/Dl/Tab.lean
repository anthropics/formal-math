/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Dl.Names
import Nc.Grp.Script
import Nc.Cut.Slp

/-!
# Tables of the dealing program

Names of the values that the dealing program computes, and the steps that compute them.
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut

/-- Names of values. -/
inductive Nm (K E pS : ℕ) (S N Id : Type) where
  /-- empty -/
  | zero
  /-- part of the input -/
  | part (κ : Fin K)
  /-- state -/
  | q (a : Fin (K + 1))
  /-- flags of a row -/
  | flag (s : Option S) (p : Fin (K + K))
  /-- row data -/
  | rd (s : Option S) (p : Fin (K + K))
  /-- is the row valid? -/
  | row (s : Option S) (p : Fin (K + K))
  /-- keys of units written -/
  | kR (a b : Fin (K + K))
  /-- keys of units read -/
  | kC (a b : Fin (K + K))
  /-- instructions for diagonal units -/
  | dg (a : Fin (K + K))
  /-- number of units as a digit -/
  | dn (a b : Fin (K + K))
  /-- outcome as a digit -/
  | dO (ν : N)
  /-- keys of new units -/
  | ch (ν : N) (d : Bool)
  /-- value of a step of the straight-line program -/
  | slp (k : Fin pS)
  /-- number of units of a move -/
  | num (x : Fin E)
  /-- conditions -/
  | cond (x : Option (Fin E))
  /-- is the unit cut? -/
  | cut (id : Id)
  /-- content of a cut unit -/
  | cont (id : Id)
  deriving DecidableEq

variable {A : Type} [CommRing A] {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {K A' E U0 U1 ub mm D pS : ℕ} {M : Sys A (K + K + A') E}

/-- Numbers of units at the beginning. -/
abbrev NN (K U0 : ℕ) := Fin (K + K) → Fin (K + K) → Fin (U0 + 1)

/-- The straight-line program of a plan: digits `Fin D`; the numbers of units and the outcomes are inputs. -/
structure SlpTab (P : G.Plan M U0 U1) (grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm) (D pS : ℕ) where
  /-- the functions -/
  fn : ℕ → NN K U0 × (M.N → Fin U1) → Fin D
  /-- inputs -/
  inp : (Fin (K + K) × Fin (K + K)) ⊕ M.N → NN K U0 × (M.N → Fin U1) → Fin D
  inpN : ∀ a b x, (inp (.inl (a, b)) x : ℕ) = x.1 a b
  inpO : ∀ ν x, (inp (.inr ν) x : ℕ) = x.2 ν
  step : ∀ k < pS, IsSlpStep inp fn k
  /-- is a unit current in the end? -/
  kcur : G.Uid (K + K) U0 M.N U1 → Fin pS
  hcur : ∀ id x, (fn (kcur id) x : ℕ) = if id ∈ P.cur x.1 x.2 E then 1 else 0
  /-- is a unit cut? -/
  kcut : G.Uid (K + K) U0 M.N U1 → Fin pS
  hcut : ∀ id x, (fn (kcut id) x : ℕ) =
    if id ∈ P.cur x.1 x.2 E ∧ grp x.1 x.2 (G.hold0 M.np id) ≠ grp x.1 x.2 (G.hold1 M.np id) then 1 else 0
  /-- is a unit given in a slot? -/
  kcons : M.Z → G.Uid (K + K) U0 M.N U1 → Fin pS
  hcons : ∀ z id x, (fn (kcons z id) x : ℕ) = if id ∈ P.cons x.1 x.2 z then 1 else 0
  /-- number of units of a move -/
  knum : Fin E → Fin pS
  hnum : ∀ y x, (fn (knum y) x : ℕ) = P.num x.1 x.2 y
  /-- conditions: the outcome of a move is good; the numbers of units are valid -/
  kcond : Option (Fin E) → Fin pS
  /-- validity -/
  valid : NN K U0 → Prop
  hgood : ∀ y x, (fn (kcond (some y)) x : ℕ) = 1 ↔ P.good x.1 x.2 y
  hvalid : ∀ x, (fn (kcond none) x : ℕ) = 1 ↔ valid x.1
  /-- groups -/
  kgrp : Fin (K + K + A') → Fin pS
  hgrp : ∀ p x, (fn (kgrp p) x : ℕ) = grp x.1 x.2 p

/-- Codes of names, digits and row data, keys of units. -/
structure Codes (S : Type) (M : Sys A (K + K + A') E) (U0 U1 D pS : ℕ) where
  /-- names -/
  nm : Nm K E pS S M.N (G.Uid (K + K) U0 M.N U1) → List Bool
  nm_inj : Function.Injective nm
  /-- digits -/
  dc : Fin D → List Bool
  dc_inj : Function.Injective dc
  /-- row data -/
  rc : RowData (K + K) → List Bool
  rc_inj : Function.Injective rc
  /-- keys of copies of units -/
  key : Grp.Cell M U0 U1 → List Bool
  /-- keys of second copies -/
  dkey : Fin (K + K) × Fin U0 → List Bool

variable {P : G.Plan M U0 U1} {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm}

namespace Codes

variable (C : Codes S M U0 U1 D pS)

/-- Abbreviation. -/
abbrev NmT (S : Type) (M : Sys A (K + K + A') E) (U0 U1 pS : ℕ) := Nm K E pS S M.N (G.Uid (K + K) U0 M.N U1)

/-- A digit as a tree. -/
def dt (d : Fin D) : Tree := ofBits (C.dc d)

/-- Unary operation on digits: `dst := f (value of x)`. -/
noncomputable def un (x dst : NmT S M U0 U1 pS) (f : Fin D → Tree) : DStep :=
  .op (C.nm x) (C.nm .zero) (C.nm dst) (trieOf C.dc fun d => .cons (f d) .nil)

/-- Binary operation on digits. -/
noncomputable def bin (x y dst : NmT S M U0 U1 pS) (f : Fin D → Fin D → Fin D) : DStep :=
  .op (C.nm x) (C.nm y) (C.nm dst) (trieOf C.dc fun d => trieOf C.dc fun d' => C.dt (f d d'))

/-- Constant. -/
def con (dst : NmT S M U0 U1 pS) (t : Tree) : DStep :=
  .op (C.nm .zero) (C.nm .zero) (C.nm dst) (.cons (.cons t .nil) .nil)

variable {C} {m : ℕ} {st : NmT S M U0 U1 pS → Tree}

theorem exec_un {x dst : NmT S M U0 U1 pS} {f : Fin D → Tree} {d : Fin D} (hz : st .zero = .nil) (hx : st x = C.dt d) :
    (C.un x dst f).exec m (byPath C.nm st) = [byPath C.nm (Function.update st dst (f d))] := by
  rw [un, exec_op C.nm_inj, hz, hx, dt, path_ofBits, tget_trieOf C.dc_inj]
  rfl

theorem exec_bin {x y dst : NmT S M U0 U1 pS} {f : Fin D → Fin D → Fin D} {d d' : Fin D} (hx : st x = C.dt d)
    (hy : st y = C.dt d') :
    (C.bin x y dst f).exec m (byPath C.nm st) = [byPath C.nm (Function.update st dst (C.dt (f d d')))] := by
  rw [bin, exec_op C.nm_inj, hx, hy, dt, dt, path_ofBits, path_ofBits, tget_trieOf C.dc_inj, tget_trieOf C.dc_inj]

theorem exec_con {dst : NmT S M U0 U1 pS} {t : Tree} (hz : st .zero = .nil) :
    (C.con dst t).exec m (byPath C.nm st) = [byPath C.nm (Function.update st dst t)] := by
  rw [con, exec_op C.nm_inj, hz]
  rfl

end Codes

end Nc.Dl
