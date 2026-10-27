/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Math.SparsifyProg
public import StepMachines.Math.SparsifyTree

/-! # The sparsification of a k-CNF as plain functions on List (List (ℕ × Bool)): definitions

The small functions `overP`, `addP`, `minusP`, `rootP` are those of
`StepMachines/Math/SparsifyProg.lean`. The thresholds θ and the width k are fixed
before the input is seen. That these functions carry out the rule of `SparsifyWidthK/Defs.lean` is
proved in `SparsifyWidthK/Refine.lean`; that they are polynomial-time, in
`SparsifyWidthK/Poly/Sparsify.lean`. -/

@[expose] public section

namespace WidthK.Prog

open Groundwork.Sparsify

/-- The sublist of C picked by the mask m (positions beyond the length of m are dropped). -/
def maskP (m : List Bool) (C : PCl) : PCl := ((C.zip m).filter fun p => p.2).map fun p => p.1

/-- All lists of k truth values. The list does not depend on the input. -/
def masks : ℕ → List (List Bool)
  | 0 => [[]]
  | k + 1 => (masks k).flatMap fun m => [false :: m, true :: m]

/-- The sublists of length h of the clauses of length j: the candidate hearts. -/
def heartsP (k : ℕ) (s : PFml) (j h : ℕ) : PFml :=
  (s.filter fun C => decide (C.length = j)).flatMap fun C =>
    ((masks k).map fun m => maskP m C).filter fun H => decide (H.length = h)

/-- The pairs (j, h) with 1 ≤ h < j ≤ k, in the order of the search: j upwards, for each j the size
h of the heart downwards.
The list does not depend on the input. -/
def pairsK (k : ℕ) : List (ℕ × ℕ) :=
  (List.range (k + 1)).flatMap fun j => ((List.range j).reverse.filter fun h => decide (0 < h)).map fun h => (j, h)

/-- The first heart of size h in clauses of size j that lies in at least θ (j - h) of them, with its
petals. -/
def tryP (θ : ℕ → ℕ) (k : ℕ) (s : PFml) (jh : ℕ × ℕ) : Option (PCl × PFml) :=
  ((heartsP k s jh.1 jh.2).find? fun H => decide (θ (jh.1 - jh.2) ≤ (overP s jh.1 H).length)).map fun H =>
    (H, (overP s jh.1 H).map (minusP H))

/-- The rule: smallest j, then largest heart. none at a leaf. -/
def pickK (θ : ℕ → ℕ) (k : ℕ) (s : PFml) : Option (PCl × PFml) := ((pairsK k).filterMap (tryP θ k s)).head?

/-- The light child (the heart added) and the heavy child (the petals added); none at a leaf. -/
def stepK (θ : ℕ → ℕ) (k : ℕ) (s : PFml) : Option (PFml × PFml) :=
  (pickK θ k s).map fun HP => (addP [HP.1] s, addP HP.2 s)

/-- The clauses as a finite set of finite sets. -/
def toFin (s : PFml) : Finset (Finset PLit) := (s.map List.toFinset).toFinset

/-- Normal form: no literal twice in a clause, and no two clauses with the same set of literals. -/
def NF (s : PFml) : Prop := (∀ C ∈ s, C.Nodup) ∧ (s.map List.toFinset).Nodup

end WidthK.Prog
