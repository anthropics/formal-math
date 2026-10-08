/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.TimeClaims.Sec3.Definitions

/-!
# "Is solved in time T", read as a statement about programs of the light language

The light language (`Light.Stmt`, `Light.Program`) is a small language with assignments to numbered
locals, loads and stores, `if`, `while` and calls of numbered procedures; a compiler turns its
programs into programs of the word RAM.

The deductions between running-time claims are made for an arbitrary reading `M : DetTimeModel` of
the sentence "is solved by a deterministic algorithm in time T".  Here the sentence is read as: some
procedure of some program of the light language solves the task within that many steps, and its need
(`Light.Need`: the largest number that it forms, the cells that it uses, the depth of its calls) is
polynomially bounded.
-/

@[expose] public section

namespace Light

open ThreeSumApsp ThreeSumApsp.WordRam

/-- The reading of "is solved in time T" by programs of the light language. -/
noncomputable def lightModel : DetTimeModel where
  thinProduct := ThinSolvedIn
  lopCount := LopSolvedIn lopCountTask
  lopDetect := LopSolvedIn lopDetectTask
  exactTriangle := SolvedIn etTask
  negativeTriangle := SolvedIn ntTask
  convolution3SUM := SolvedIn c3Task
  threeSum := SolvedIn s3Task
  minPlusProduct := SolvedIn mpTask
  apsp := SolvedIn apTask

end Light
