/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Field.Rat

/-! # Parity checks (pure mathematics; imports Mathlib only): definitions of Step 1 of Appendix D (σ_i, η, good checks, tuples of marks), and statements on a choice of the checks by conditional expectations that differs from its Step 2

Abstract setting: X is the finite set of assignments ξ, E the finite set of clauses, V ξ the set of
clauses that ξ violates. Nothing else about formulas is used. Checks are numbered
0, …, r − 1 (Appendix D of the paper: 1, …, r). -/

@[expose] public section

namespace ParityChecks

open Finset

variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]

/-- [q even]. -/
def ev (q : ℕ) : ℤ := if Even q then 1 else 0

/-- σ₀ = 1, σ_i = (−1)^i·2^{i−1} for i ≥ 1. -/
def sig (i : ℕ) : ℤ := if i = 0 then 1 else (-1) ^ i * 2 ^ (i - 1)

/-- η(ξ): inclusion–exclusion over the violated clauses, cut off at nb marks. -/
def eta (V : X → Finset E) (nb : ℕ) (ξ : X) : ℤ := ∑ S ∈ (V ξ).powerset with #S ≤ nb, (-1) ^ #S

/-- The checks are good: every ξ that violates more than nb clauses violates an odd number of
clauses of some check. -/
def Good (V : X → Finset E) (nb r : ℕ) (Λ : ℕ → Finset E) : Prop := ∀ ξ, nb < #(V ξ) → ∃ j < r, Odd #(Λ j ∩ V ξ)

/-- The tuples (S_j), j ∈ J, with S_j ⊆ Λ_j ∩ V(ξ) and at most M marks in all (S_j = ∅ for j < r
outside J). -/
def tuples (V : X → Finset E) (r : ℕ) (Λ : ℕ → Finset E) (J : Finset (Fin r)) (M : ℕ) (ξ : X) : Finset (Fin r → Finset E) :=
  (Fintype.piFinset fun j : Fin r => if j ∈ J then (Λ j ∩ V ξ).powerset else {∅}).filter fun S => ∑ j, #(S j) ≤ M

/-! ## The potential. A state: the checks before j are complete, Λ j is the part of check j chosen so far, D the clauses not yet decided for check j, later checks are empty. p = 1/nb. -/

section Potential

variable (V : X → Finset E) (nb r : ℕ)

/-- ω(ξ) = C(|V(ξ)|, nb + 1). -/
def omega (ξ : X) : ℕ := (#(V ξ)).choose (nb + 1)

/-- p = 1/nb. -/
def pr : ℚ := 1 / nb

/-- The number of clauses not yet decided for check j'. -/
def undRow (j : ℕ) (D : Finset E) (j' : ℕ) : ℕ := if j' < j then 0 else if j' = j then #D else Fintype.card E

/-- The number of checks for which the clause e is not yet decided. -/
def undCol (j : ℕ) (D : Finset E) (e : E) : ℕ := (r - 1 - j) + if e ∈ D then 1 else 0

def Upar (j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) : ℚ :=
  (5 / 8) ^ (r - 1 - j) * ∑ ξ, (omega V nb ξ : ℚ) * (∏ j' ∈ range j, (ev #(Λ j' ∩ V ξ) : ℚ)) *
    (1 / 2 * (1 + (-1) ^ #(Λ j ∩ V ξ) * (1 - 2 * pr nb) ^ #(D ∩ V ξ)))

def Uinc (j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) : ℚ :=
  ((∑ j' ∈ range r, #(Λ j') : ℕ) + pr nb * (∑ j' ∈ range r, undRow j D j' : ℕ)) / (8 * pr nb * Fintype.card E * r)

def Urow (j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) : ℚ :=
  1 / (8 * r) * ∑ j' ∈ range r, (2 : ℚ) ^ #(Λ j') / (1 + pr nb) ^ (Fintype.card E - undRow j D j')

def Ucol (j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) : ℚ :=
  1 / (8 * Fintype.card E) * ∑ e : E, (2 : ℚ) ^ #{j' ∈ range r | e ∈ Λ j'} / (1 + pr nb) ^ (r - undCol r j D e)

/-- The potential. -/
def Ups (j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) : ℚ := Upar V nb r j Λ D + Uinc nb r j Λ D + Urow nb r j Λ D + Ucol nb r j Λ D

/-- Υ_par with (1 − 2p)^u replaced by Σ_{i ≤ i₀} (−2p)^i·C(u,i). -/
def tUpar (i₀ j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) : ℚ :=
  (5 / 8) ^ (r - 1 - j) * ∑ ξ, (omega V nb ξ : ℚ) * (∏ j' ∈ range j, (ev #(Λ j' ∩ V ξ) : ℚ)) *
    (1 / 2 * (1 + (-1) ^ #(Λ j ∩ V ξ) * ∑ i ∈ range (i₀ + 1), (-2 * pr nb) ^ i * ((#(D ∩ V ξ)).choose i : ℚ)))

/-- A = Σ_ξ ω(ξ)·∏_{j'<j} [|V_{j'}(ξ)| even]. -/
def Aint (j : ℕ) (Λ : ℕ → Finset E) : ℤ := ∑ ξ, (omega V nb ξ : ℤ) * ∏ j' ∈ range j, ev #(Λ j' ∩ V ξ)

/-- B_i = Σ_ξ ω(ξ)·C(|D ∩ V(ξ)|, i)·(−1)^{|V_j(ξ)|}·∏_{j'<j} [|V_{j'}(ξ)| even]. -/
def Bint (i j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) : ℤ :=
  ∑ ξ, (omega V nb ξ : ℤ) * ((#(D ∩ V ξ)).choose i : ℤ) * (-1) ^ #(Λ j ∩ V ξ) * ∏ j' ∈ range j, ev #(Λ j' ∩ V ξ)

/-- A state in order. -/
structure IsState (j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) : Prop where
  j_lt : j < r
  later : ∀ j', j < j' → Λ j' = ∅
  disj : Disjoint (Λ j) D

/-- The clause e is put into check j. -/
def putIn (j : ℕ) (Λ : ℕ → Finset E) (e : E) : ℕ → Finset E := Function.update Λ j (insert e (Λ j))

end Potential

/-- Choice of the checks clause by clause, by a potential of four terms (factor 5/8, p = 1/nb); Step
2 of Appendix D instead uses Lemma 13. These are properties of the potential; no algorithm that
makes the choices is stated here. -/
structure ChoiceByPotential : Prop where
  /-- all four terms are nonnegative -/
  nonneg : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E) (D : Finset E), 2 ≤ nb →
    0 ≤ Upar V nb r j Λ D ∧ 0 ≤ Uinc nb r j Λ D ∧ 0 ≤ Urow nb r j Λ D ∧ 0 ≤ Ucol nb r j Λ D
  /-- ½(1 + (1 − 2p)^v) < 5/8 for v > nb -/
  five_eighths : ∀ nb v : ℕ, 2 ≤ nb → nb < v → 1 / 2 * (1 + (1 - 2 * pr nb) ^ v) < 5 / 8
  /-- at the start the potential is at most 1/2 -/
  start : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r : ℕ), 2 ≤ nb → 1 ≤ r → 1 ≤ Fintype.card E →
    (5 / 8 : ℚ) ^ r * (Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ) ≤ 1 / 8 → Ups V nb r 0 (fun _ => ∅) univ ≤ 1 / 2
  /-- one decision: p·Υ^in + (1 − p)·Υ^out = Υ -/
  martingale : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) (e : E),
    2 ≤ nb → IsState r j Λ D → e ∈ D →
    pr nb * Ups V nb r j (putIn j Λ e) (D.erase e) + (1 - pr nb) * Ups V nb r j Λ (D.erase e) = Ups V nb r j Λ D
  /-- from one check to the next the potential does not grow -/
  boundary : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E),
    2 ≤ nb → IsState r j Λ ∅ → j + 1 < r → Ups V nb r (j + 1) Λ univ ≤ Ups V nb r j Λ ∅
  /-- what Υ < 1 gives -/
  structure_ : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E) (D : Finset E),
    2 ≤ nb → 1 ≤ Fintype.card E → IsState r j Λ D → Ups V nb r j Λ D < 1 →
    ((∑ j' ∈ range r, #(Λ j') : ℕ) : ℚ) < 8 * pr nb * Fintype.card E * r ∧
    (∀ j' < r, (2 : ℚ) ^ #(Λ j') < 8 * r * (1 + pr nb) ^ Fintype.card E) ∧
    ∀ e : E, (2 : ℚ) ^ #{j' ∈ range r | e ∈ Λ j'} < 8 * Fintype.card E * (1 + pr nb) ^ r
  /-- in the final state Υ < 1 makes the checks good -/
  final : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r : ℕ) (Λ : ℕ → Finset E),
    2 ≤ nb → IsState r (r - 1) Λ ∅ → Ups V nb r (r - 1) Λ ∅ < 1 → Good V nb r Λ
  /-- the error of the truncated series carries over to the potential -/
  approx : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r i₀ j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) (ε : ℚ),
    (∀ u ≤ Fintype.card E, |(1 - 2 * pr nb) ^ u - ∑ i ∈ range (i₀ + 1), (-2 * pr nb) ^ i * (u.choose i : ℚ)| ≤ ε) →
    |tUpar V nb r i₀ j Λ D - Upar V nb r j Λ D| ≤ 1 / 2 * ε * (Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ)
  /-- the truncated potential through the integers A and B_i -/
  compute : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r i₀ j : ℕ) (Λ : ℕ → Finset E) (D : Finset E),
    tUpar V nb r i₀ j Λ D = (5 / 8) ^ (r - 1 - j) * (1 / 2) * ((Aint V nb j Λ : ℚ) + ∑ i ∈ range (i₀ + 1), (-2 * pr nb) ^ i * (Bint V nb i j Λ D : ℚ))
  /-- A and B_i are small -/
  abs_le : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb i j : ℕ) (Λ : ℕ → Finset E) (D : Finset E),
    |Aint V nb j Λ| ≤ (Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ) ∧
    |Bint V nb i j Λ D| ≤ (Fintype.card X * (Fintype.card E).choose (nb + 1) * (Fintype.card E).choose i : ℕ)

end ParityChecks
