/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.CountNet
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic

/-! # Marks and layers, part 1: the sums

The clauses of a formula are divided into layers. For an assignment σ and a layer L let v be the
number of clauses of L that σ violates. The alternating sum
Σ_j (−1)^j·C(v, j) is 1 if v = 0 and 0 otherwise; cut off at j ≤ w it is still that if v ≤ w. If
every assignment that satisfies the later layers
violates at most w clauses of a layer (`Good`), the product of the cut-off sums over the layers is 1
at the satisfying assignments and 0 elsewhere.
This file has definitions only. -/

@[expose] public section

namespace PaddedDescent.F.Mark

open Groundwork Groundwork.Prog

/-- A clause: a list of literals (variable, the value that makes the literal true). -/
abbrev Cl := List (ℕ × Bool)

/-- σ makes every literal of C false. -/
def vio (σ : ℕ → Bool) (C : Cl) : Bool := C.all fun l => σ l.1 != l.2

/-- The number of clauses of L that σ violates. -/
def nvio (σ : ℕ → Bool) (L : Fml) : ℕ := L.countP (vio σ)

/-- Σ_{j ≤ w} C(v, j). -/
def Tpl (w v : ℕ) : ℤ := ∑ j ∈ Finset.range (w + 1), (v.choose j : ℤ)

/-- Σ_{j ≤ w} (−1)^j·C(v, j). -/
def Tsg (w v : ℕ) : ℤ := ∑ j ∈ Finset.range (w + 1), (-1) ^ j * (v.choose j : ℤ)

/-- An assignment of the variables below n, continued by false. -/
def ext {n : ℕ} (σ : Fin n → Bool) (x : ℕ) : Bool := if h : x < n then σ ⟨x, h⟩ else false

/-- The sum that one evaluation computes: the first layer without signs, the others with signs, all
cut off at w. -/
def trunc (n w : ℕ) (Ls : List Fml) : ℤ :=
  ∑ σ : Fin n → Bool, Tpl w (nvio (ext σ) (Ls.headD [])) * (Ls.tail.map fun L => Tsg w (nvio (ext σ) L)).prod

/-- Every assignment that satisfies the later layers violates at most w clauses of a layer. -/
def Good (n w : ℕ) : List Fml → Prop
  | [] => True
  | Λ :: rest => (∀ σ : Fin n → Bool, (∀ L ∈ rest, nvio (ext σ) L = 0) → nvio (ext σ) Λ ≤ w) ∧ Good n w rest

/-- The number of assignments of the variables below n that satisfy ψ. -/
def nSat (n : ℕ) (ψ : Fml) : ℕ := (Finset.univ.filter fun σ : Fin n → Bool => ∀ C ∈ ψ, ∃ l ∈ C, ext σ l.1 = l.2).card

/-- The clauses of x in which the variable v occurs. -/
def occ (x : Fml) (v : ℕ) : Fml := x.filter fun C => C.any fun l => l.1 == v

/-! ### The choice of the layers, for any evaluation function ev in place of `trunc n w` -/

/-- Is the clause C put into layer i? When ev is `trunc n w` and both lists are good, the difference
of the two evaluations is the sum, over the assignments
that satisfy the later layers and violate C, of 2^(number of violated clauses of layer i). -/
def dropE (ev : List Fml → ℤ) (w : ℕ) (Ls : List Fml) (C : Cl) (i : ℕ) : Bool :=
  decide ((ev ((C :: Ls.getD i []) :: Ls.drop (i + 1)) - ev (Ls.drop i)) * ((2 ^ ((Ls.drop i).flatten.length + 3) : ℕ) : ℤ) ≤
    ((3 ^ (Ls.drop (i + 1)).flatten.length * 2 ^ w : ℕ) : ℤ))

/-- Ls with the clause C added to layer i. -/
def placeAt (Ls : List Fml) (C : Cl) (i : ℕ) : List Fml := Ls.take i ++ (C :: Ls.getD i []) :: Ls.drop (i + 1)

/-- C goes into the first layer whose test holds, else into the last. -/
def placeE (ev : List Fml → ℤ) (w : ℕ) (Ls : List Fml) (C : Cl) : List Fml :=
  placeAt Ls C (((List.range (Ls.length - 1)).find? (dropE ev w Ls C)).getD (Ls.length - 1))

/-- The clauses of ψ, placed one after the other into R + 1 layers. -/
def layersE (ev : List Fml → ℤ) (w R : ℕ) (ψ : Fml) : List Fml := ψ.foldl (placeE ev w) (List.replicate (R + 1) [])

/-- The lists of layers on which the choice of the layers of ψ uses the evaluation: good, at most R +
2 layers, and their clauses are clauses of ψ, counted
with repetition. -/
def Asked (n w R : ℕ) (ψ : Fml) (Ls : List Fml) : Prop := Good n w Ls ∧ Ls.length ≤ R + 2 ∧ Ls.flatten.Subperm ψ

end PaddedDescent.F.Mark
