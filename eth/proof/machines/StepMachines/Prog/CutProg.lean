/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.SideBasics
public import StepMachines.Math.CutWord

/-! One rectangle as a procedure: the part of the cut of the piece A_i on one side, evaluated
literally. The top part is
a loop over the λ positions; the bottom part a loop over all 2^λ sets of positions, with a loop over
the positions inside.
The input holds all that is needed and nothing of the grid; λ is the length of the word x. -/

@[expose] public section

namespace Groundwork.Prog

open Finset Stepped
open Groundwork.Grid (sideCnt topTerm botTerm cutW)

/-- ((top?, i), (x, y, w)): the side, the number i of A_i, the words of the two ends on this side,
the name of the label
(one value of the index summed over across the cut). -/
abbrev CutQ : Type := (Bool × ℕ) × (List Bool × List Bool × List Bool)

/-- λ, the length of the word x. -/
def cutLen (q : CutQ) : ℕ := q.2.1.length

/-- Does w name a label? -/
def cutValid (tr : Bool) (q : CutQ) : Bool := validW q.2.1.length (sideCnt tr q.2.1.length q.1.2) q.2.2.2

/-- Is the top part asked for? -/
def cutTop (q : CutQ) : Bool := q.1.1

/-- One factor of the top part; the input comes with the counter of the loop over the positions. -/
def topE (tr : Bool) (p : CutQ × ℕ) : ℤ := topTerm tr p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2

/-- The number 2^λ of sets of positions. -/
def cutPow (q : CutQ) : ℕ := 2 ^ q.2.1.length

/-- Does the set of positions encoded by the counter have exactly i elements? -/
def cutPop (p : CutQ × ℕ) : Bool := decide ((toWord p.1.2.1.length p.2).count true = p.1.1.2)

/-- λ again, inside the loop over the sets. -/
def cutLen' (p : CutQ × ℕ) : ℕ := p.1.2.1.length

/-- One factor of the bottom part; the input comes with the two loop counters: the set of positions,
then the position. -/
def botE (tr : Bool) (p : (CutQ × ℕ) × ℕ) : ℤ := botTerm tr p.1.1.2.1 p.1.1.2.2.1 p.1.1.2.2.2 p.1.2 p.2

/-- The part of the cut on one side. -/
def cutP (tr : Bool) : Stepped CutQ ℤ :=
  ite (cutValid tr)
    (ite cutTop (prodRange cutLen (ofFun (topE tr)))
      (sumRange cutPow (ite cutPop (prodRange cutLen' (ofFun (botE tr))) (const 0))))
    (const 0)

end Groundwork.Prog
