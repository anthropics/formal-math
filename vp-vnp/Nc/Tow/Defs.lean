/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Towers, routes: interface

A tower: levels of chambers `X j`, typed edges `Ed j`, vertices `V j i` of type `i` (all with the local
structure `Fl`, `Nr`), coverings `X j → X (j + 1)` of degree `D`, and hosts.
-/

namespace Nc.Tow

open Finset

/-- A tower of coverings, `J` steps, with `h` types. -/
structure Tower (h b D J r : ℕ) where
  /-- chambers -/
  X : ℕ → Type
  /-- typed edges -/
  Ed : ℕ → Type
  /-- vertices of type `i` -/
  V : ℕ → Fin h → Type
  /-- the chambers at a vertex -/
  Fl : Type
  /-- the near pairs at a vertex -/
  Nr : Type
  [fX : ∀ j, Fintype (X j)]
  [dX : ∀ j, DecidableEq (X j)]
  [fE : ∀ j, Fintype (Ed j)]
  [dE : ∀ j, DecidableEq (Ed j)]
  [fV : ∀ j i, Fintype (V j i)]
  [dV : ∀ j i, DecidableEq (V j i)]
  [fF : Fintype Fl]
  [dF : DecidableEq Fl]
  [fN : Fintype Nr]
  [dN' : DecidableEq Nr]
  /-- the ends of an edge -/
  e0 : ∀ {j}, Ed j → X j
  /-- the ends of an edge -/
  e1 : ∀ {j}, Ed j → X j
  e_ne : ∀ {j} (e : Ed j), e0 e ≠ e1 e
  /-- the type of an edge -/
  ty : ∀ {j}, Ed j → Fin h
  card_ed : ∀ j ≤ J, ∀ i, 2 * (univ.filter fun e : Ed j => ty e = i).card = r * Fintype.card (X j)
  deg : ∀ j ≤ J, ∀ (c : X j) i, (univ.filter fun e : Ed j => ty e = i ∧ (e0 e = c ∨ e1 e = c)).card ≤ r
  /-- the vertex of a chamber -/
  vx : ∀ {j} i, X j → V j i
  /-- the place of a chamber at its vertex -/
  co : ∀ {j} (i : Fin h), X j → Fl
  vx_co : ∀ {j}, j ≤ J → ∀ i, Function.Bijective fun c : X j => (vx i c, co i c)
  card_fl : Fintype.card Fl = b
  /-- the ends of a near pair -/
  cN : Nr → Fl
  /-- the ends of a near pair -/
  dN : Nr → Fl
  n_ne : ∀ ν, cN ν ≠ dN ν
  /-- the edges of types other than `i` are the near pairs at the vertices of type `i` -/
  nr : ∀ {j}, j ≤ J → ∀ i, {e : Ed j // ty e ≠ i} ≃ V j i × Nr
  nr_vx0 : ∀ {j} (hj : j ≤ J) i (e : {e : Ed j // ty e ≠ i}), vx i (e0 e.1) = (nr hj i e).1
  nr_vx1 : ∀ {j} (hj : j ≤ J) i (e : {e : Ed j // ty e ≠ i}), vx i (e1 e.1) = (nr hj i e).1
  nr_co : ∀ {j} (hj : j ≤ J) i (e : {e : Ed j // ty e ≠ i}),
    s(co i (e0 e.1), co i (e1 e.1)) = s(cN (nr hj i e).2, dN (nr hj i e).2)
  /-- the covering -/
  π : ∀ {j}, X j → X (j + 1)
  /-- the covering on edges -/
  πE : ∀ {j}, Ed j → Ed (j + 1)
  /-- the covering on vertices -/
  πV : ∀ {j} {i}, V j i → V (j + 1) i
  π_ends : ∀ {j}, j < J → ∀ e : Ed j, s(e0 (πE e), e1 (πE e)) = s(π (e0 e), π (e1 e))
  π_ty : ∀ {j}, j < J → ∀ e : Ed j, ty (πE e) = ty e
  card_X : ∀ j < J, Fintype.card (X j) = D * Fintype.card (X (j + 1))
  fibre : ∀ {j}, j < J → ∀ ē : Ed (j + 1), (univ.filter fun e : Ed j => πE e = ē).card ≤ D
  π_vx : ∀ {j}, j < J → ∀ i (c : X j), vx i (π c) = πV (vx i c)
  π_co : ∀ {j}, j < J → ∀ i (c : X j), co i (π c) = co i c
  /-- hosts -/
  host : ∀ {j} i, V j i → X (j + 1)
  host_inj : ∀ {j}, j < J → ∀ i, Function.Injective (host i : V j i → X (j + 1))
  host_vx : ∀ {j}, j < J → ∀ i (v : V j i), vx i (host i v) = πV v

attribute [instance] Tower.fX Tower.dX Tower.fE Tower.dE Tower.fV Tower.dV Tower.fF Tower.dF Tower.fN Tower.dN'

namespace Tower

variable {h b D J r : ℕ} (T : Tower h b D J r)

/-- The other end of an edge. -/
def step {j : ℕ} (e : T.Ed j) (c : T.X j) : T.X j := if T.e0 e = c then T.e1 e else T.e0 e

/-- The list of edges is a walk from `c` to `c'`. -/
def Walk {j : ℕ} : T.X j → List (T.Ed j) → T.X j → Prop
  | c, [], c' => c = c'
  | c, e :: l, c' => (T.e0 e = c ∨ T.e1 e = c) ∧ Walk (T.step e c) l c'

end Tower

/-- Routes: a walk from every chamber of `X 0` to every other one, at most `m` steps, in which every edge is used at
most `Uu` times in all. -/
structure Routes {h b D J r : ℕ} (T : Tower h b D J r) (m Uu : ℕ) where
  /-- the route -/
  rt : T.X 0 → T.X 0 → List (T.Ed 0)
  walk : ∀ c c', T.Walk c (rt c c') c'
  len : ∀ c c', (rt c c').length ≤ m
  use : ∀ e : T.Ed 0, ∑ c, ∑ c', (rt c c').count e ≤ Uu

end Nc.Tow
