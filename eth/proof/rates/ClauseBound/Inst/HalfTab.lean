/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Inst.RecArith
public import ClauseBound.Boson.Half
public import ClauseBound.Boson.KF

/-! # The matrices of the operators as tables: definitions

A monomial is written as a list of its parts. `flat` is a list of such lists (in the use: all
partitions of 0, …, W as nonincreasing lists). The matrix of an operator, restricted to the
listed monomials, is a table: a list of integers with the entry for (π, σ) at the position (index of
π)·(length of flat) + (index of σ). The index r of a[r] is not stored: an entry
can only be different from 0 for r = (weight of π) − (weight of σ), and the table holds the entry
for this r. The tables are built part by part, with the recursion that defines a[r];
after each round the table is cut off by `cap` according to `pad`, a padding string of ones given
beside the input (as in Appendix E of the paper). Numbers that are lengths of loops are cut off at
W. Definitions only. -/

@[expose] public section

namespace ClauseBound.Inst.Half

open Groundwork PaddedDescent.F ClauseBound.Inst.Rec

/-- The coefficient `ClauseBound.Boson.bet n r`, for n ≤ W. -/
def betF (W n : ℕ) (r : ℤ) : ℤ := if r = 0 then 0 else chooseZ (r - 1) (min n W - 1)

/-- The table of a function of two listed monomials. -/
def tab (flat : List (List ℕ)) (f : List ℕ → List ℕ → ℤ) : List ℤ := flat.flatMap fun π => flat.map fun σ => f π σ

/-- The entry of a table for (π, σ). -/
def lookT (flat : List (List ℕ)) (T : List ℤ) (π σ : List ℕ) : ℤ := T.getD (flat.idxOf π * flat.length + flat.idxOf σ) 0

/-- The entry for (π, σ) of the normally ordered product of the series of t_n with the family whose
table is T. -/
def nopE (W n : ℕ) (flat : List (List ℕ)) (T : List ℤ) (π σ : List ℕ) : ℤ :=
  (π.dedup.map fun l : ℕ => betF W n (l : ℤ) * lookT flat T (π.erase l) σ).sum +
    (σ.dedup.map fun k : ℕ => betF W n (-(k : ℤ)) * ((k : ℤ) * (σ.count k : ℤ) * lookT flat T π (σ.erase k))).sum

/-- The table of the identity. -/
def oneT (flat : List (List ℕ)) : List ℤ := tab flat fun π σ => if π = σ then 1 else 0

/-- The table of a[·]. -/
def tabOp (pad : U) (W : ℕ) (flat : List (List ℕ)) (a : List ℕ) : List ℤ :=
  a.reverse.foldl (fun T n => cap pad [] (tab flat (nopE W n flat T))) (cap pad [] (oneT flat))

/-- The tables of the parts of weight 0, …, h of the empty product. -/
def kfInit (h : ℕ) (flat : List (List ℕ)) : List (List ℤ) :=
  (List.range (h + 1)).map fun w => if w = 0 then oneT flat else tab flat fun _ _ => 0

/-- One more factor (−1)^{n−1}·y_n: from the tables S of the parts of weight 0, …, h of a^μ to those
of a^{n :: μ}. -/
def kfStep (W h n : ℕ) (flat : List (List ℕ)) (S : List (List ℤ)) : List (List ℤ) :=
  (List.range (h + 1)).map fun w => tab flat fun π σ =>
    sumR (min n W) fun j =>
      if j + 1 ≤ w then sgnZ ((n - 1 : ℕ) : ℤ) * chooseZ (n : ℤ) (j + 1) * nopE W (j + 1) flat (S.getD (w - (j + 1)) []) π σ else 0

/-- The tables of (the part of weight w of a^μ)[·], w = 0, …, h. -/
def tabKF (pad : U) (W : ℕ) (flat : List (List ℕ)) (h : ℕ) (μ : List ℕ) : List (List ℤ) :=
  μ.reverse.foldl (fun S n => cap pad [] (kfStep W h n flat S)) (cap pad [] (kfInit h flat))

/-- z_ν. -/
def zzF (ν : List ℕ) : ℕ := (ν.dedup.map fun k => ((k ^ ν.count k * factN (ν.count k) : ℕ) : ℤ)).prod.natAbs

/-- `ClauseBound.Boson.topK μx h i r` at (π, σ). -/
def topF (pad : U) (W : ℕ) (flat : List (List ℕ)) (h : ℕ) (μx : List ℕ) (i : ℕ) (r : ℤ) (π σ : List ℕ) : ℤ :=
  if r = (π.sum : ℤ) - σ.sum then
    sgnZ i * sumR (h + 1) fun w => chooseZ ((w : ℤ) + h) i * lookT flat ((tabKF pad W flat h μx).getD w []) π σ
  else 0

/-- `ClauseBound.Boson.botK μv h r` at (π, σ). -/
def botF (pad : U) (W : ℕ) (flat : List (List ℕ)) (h : ℕ) (μv : List ℕ) (r : ℤ) (π σ : List ℕ) : ℤ :=
  if r = (π.sum : ℤ) - σ.sum then ((factN h / zzF μv : ℕ) : ℤ) * lookT flat (tabOp pad W flat μv) π σ else 0

/-- What the tables need of the list of monomials: different lists are different monomials, the list
is closed under erasing a part, and all weights are at most W. -/
structure FlatOK (W : ℕ) (flat : List (List ℕ)) : Prop where
  inj : ∀ π ∈ flat, ∀ σ ∈ flat, (π : Multiset ℕ) = σ → π = σ
  erase : ∀ π ∈ flat, ∀ l ∈ π, π.erase l ∈ flat
  sum_le : ∀ π ∈ flat, π.sum ≤ W

/-- The table T holds the matrices of the family F: the entry for (π, σ) is that of F r with r =
(weight of π) − (weight of σ). -/
def Rep (flat : List (List ℕ)) (T : List ℤ) (F : ℤ → ClauseBound.Boson.Ker) : Prop :=
  ∀ π ∈ flat, ∀ σ ∈ flat, lookT flat T π σ = F ((π.sum : ℤ) - σ.sum) π σ

/-- A length of the pad that suffices for the table of a[·]: Δ listed monomials, L parts. -/
def padOp (W Δ L : ℕ) : ℕ := Δ ^ 2 * (3 * ((4 * W + 1) * L) + 10) + 2

/-- A length of the pad that suffices for the tables of the parts of weight 0, …, h of a^μ: Δ listed
monomials, μ has the sum s and L parts. -/
def padKF (W Δ h s L : ℕ) : ℕ := (h + 1) * (Δ ^ 2 * (3 * (s + (4 * W + 1) * L)  + 10) + 4) + 2

end ClauseBound.Inst.Half
