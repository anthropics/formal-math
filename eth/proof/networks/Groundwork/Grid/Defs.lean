/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import NetworkStatements
public import Groundwork.Net.Defs
public import Groundwork.Net.Calculus
public import Groundwork.Cross.Cuts
public import Mathlib.Algebra.Polynomial.Coeff

/-! One level of the recursion (the grid, its rectangles and the merged rows, as in the proof of
Proposition 3), definitions only: the clique on a grid with rows in a type ρ (not the
constant ρ), columns in γ and labels in α, written with half-edges; a function G of the four ends at
every rectangle; the
network obtained by merging every row into one node, for any factorisation («cut») of the functions
G top|bottom; the
transposed grid, which turns columns into rows; and the patterns ι that index the terms Z_ι. -/

@[expose] public section

namespace Groundwork.Grid

open Finset

variable {J ρ γ α τ : Type}

/-- A rectangle ((a,b),(i,i')): rows a < b, columns i < i' (the inequalities are in Ω). -/
abbrev Rect (ρ γ : Type) := (ρ × ρ) × (γ × γ)

/-- The set of rectangles. -/
def Ω (ρ γ : Type) [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] : Finset (Rect ρ γ) :=
  univ.filter fun ω => ω.1.1 < ω.1.2 ∧ ω.2.1 < ω.2.2

/-- Half-edge labellings: ℓ w w' is the copy held by w of the label of the edge {w,w'}. -/
abbrev Half (ρ γ α : Type) := ρ × γ → ρ × γ → α

/-- G at the four ends x, y (top), u, v (bottom) of the two diagonals of the rectangle ω. -/
def app (G : α → α → α → α → ℤ) (ℓ : Half ρ γ α) (ω : Rect ρ γ) : ℤ :=
  G (ℓ (ω.1.1, ω.2.1) (ω.1.2, ω.2.2)) (ℓ (ω.1.1, ω.2.2) (ω.1.2, ω.2.1))
    (ℓ (ω.1.2, ω.2.1) (ω.1.1, ω.2.2)) (ℓ (ω.1.2, ω.2.2) (ω.1.1, ω.2.1))

/-- The instance carried to the grid along e; it vanishes unless the entry at the node itself is d. -/
def onGrid [DecidableEq α] (R : Inst J α) (d : α) (e : J ≃ ρ × γ) : Inst (ρ × γ) α :=
  fun w h => if h w = d then R (e.symm w) (fun v => h (e v)) else 0

/-- A state of a row: z i w' is the half-edge from the node of the row in column i towards w'. -/
abbrev RowSt (ρ γ α : Type) := γ → ρ × γ → α

/-- A label of two rows: the labels of the vertical edges between them, and a label in τ for each of
their rectangles. -/
abbrev RowLab (γ α τ : Type) := (γ → α) × (γ × γ → τ)

/-- A factorisation top|bottom of a function of the four ends: G x y u v = Σ_{θ ∈ lab} top x y θ ·
bot u v θ (see Factors),
and the number of bits charged for it. -/
structure Cut (α τ : Type) where
  lab : Finset τ
  top : α → α → τ → ℤ
  bot : α → α → τ → ℤ
  cap : ℕ

/-- The cut C is a factorisation of G. -/
def Cut.Factors (C : Cut α τ) (G : α → α → α → α → ℤ) : Prop :=
  ∀ x y u v, G x y u v = ∑ θ ∈ C.lab, C.top x y θ * C.bot u v θ

/-- The grid transposed: the instance. -/
def trInst (R : Inst (ρ × γ) α) : Inst (γ × ρ) α := fun w h => R w.swap fun w' => h w'.swap

/-- The grid transposed: the functions at the rectangles. Transposing exchanges the ends y (top
right) and u (bottom left). -/
def trG (G : Rect ρ γ → α → α → α → α → ℤ) : Rect γ ρ → α → α → α → α → ℤ :=
  fun ω x y u v => G (ω.2, ω.1) x u y v

section
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]

/-- Σ_ℓ ∏_w R_w(ℓ(w,·)) · (equalities of the edges inside a row) · (equalities of the edges inside a
column)
· ∏_ω G_ω(x,y,u,v). The sum is over all ℓ, the entries ℓ w w included; for an instance made by
`onGrid`, R vanishes unless
ℓ w w is the default label, so that these entries add nothing. -/
def ZG (R : Inst (ρ × γ) α) (G : Rect ρ γ → α → α → α → α → ℤ) : ℤ :=
  ∑ ℓ : Half ρ γ α, (∏ w, R w (ℓ w)) *
    ((∏ a, ∏ q ∈ pairs γ, if ℓ (a, q.1) (a, q.2) = ℓ (a, q.2) (a, q.1) then 1 else 0) *
     (∏ i, ∏ p ∈ pairs ρ, if ℓ (p.1, i) (p.2, i) = ℓ (p.2, i) (p.1, i) then 1 else 0) *
     ∏ ω ∈ Ω ρ γ, app (G ω) ℓ ω)

/-- The weight of row a: its tensors and the equalities of the edges inside it. -/
def rowW (R : Inst (ρ × γ) α) (a : ρ) (z : RowSt ρ γ α) : ℤ :=
  (∏ i, R (a, i) (z i)) * ∏ q ∈ pairs γ, if z q.1 (a, q.2) = z q.2 (a, q.1) then 1 else 0

/-- The interaction of rows a < b (z the state of a, z' that of b): the equalities of the vertical
edges and the functions G
of their rectangles. -/
def rowΨ (G : Rect ρ γ → α → α → α → α → ℤ) (a b : ρ) (z z' : RowSt ρ γ α) : ℤ :=
  (∏ i, if z i (b, i) = z' i (a, i) then 1 else 0) *
    ∏ k : γ × γ with k.1 < k.2,
      G ((a, b), k) (z k.1 (b, k.2)) (z k.2 (b, k.1)) (z' k.1 (a, k.2)) (z' k.2 (a, k.1))

/-- The label set of rows a < b. -/
def rowΘ (C : Rect ρ γ → Cut α τ) (t₀ : τ) (a b : ρ) : Finset (RowLab γ α τ) :=
  univ ×ˢ tuples (fun k : γ × γ => k.1 < k.2) (fun k => (C ((a, b), k)).lab) t₀

/-- The factor of rows a < b on the side of a. -/
def rowTop (C : Rect ρ γ → Cut α τ) (a b : ρ) (z : RowSt ρ γ α) (θ : RowLab γ α τ) : ℤ :=
  (∏ i, if z i (b, i) = θ.1 i then 1 else 0) *
    ∏ k : γ × γ with k.1 < k.2, (C ((a, b), k)).top (z k.1 (b, k.2)) (z k.2 (b, k.1)) (θ.2 k)

/-- The factor of rows a < b on the side of b. -/
def rowBot (C : Rect ρ γ → Cut α τ) (a b : ρ) (z' : RowSt ρ γ α) (θ : RowLab γ α τ) : ℤ :=
  (∏ i, if z' i (a, i) = θ.1 i then 1 else 0) *
    ∏ k : γ × γ with k.1 < k.2, (C ((a, b), k)).bot (z' k.1 (a, k.2)) (z' k.2 (a, k.1)) (θ.2 k)

/-- All rows merged: the row network. L is the number of bits of α, used in the table of capacities
only:
c_ab = (number of columns)·L for the vertical edges, plus the bits charged for the rectangles on
rows a, b. -/
def rowNet (R : Inst (ρ × γ) α) (C : Rect ρ γ → Cut α τ) (t₀ : τ) (L : ℕ) :
    Network ρ (RowSt ρ γ α) (RowLab γ α τ) where
  S _ := univ
  W := rowW R
  Θ a b := if a < b then rowΘ C t₀ a b else ∅
  f a b z θ := if a < b then rowTop C a b z θ else rowBot C b a z θ
  c a b := Fintype.card γ * L + ∑ k : γ × γ with k.1 < k.2, (C ((min a b, max a b), k)).cap

end

/-! ### The patterns ι of the terms Z_ι -/

section
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ]

/-- The patterns ι: a number in {0,…,λ} for every rectangle (0 off the rectangles). -/
def Pat (ρ γ : Type) [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] (n : ℕ) : Finset (Rect ρ γ → ℕ) :=
  tuples (fun ω => ω ∈ Ω ρ γ) (fun _ => range (n + 1)) 0

end

end Groundwork.Grid
