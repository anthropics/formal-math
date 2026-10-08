/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.LibraryContracts
public import ThreeSumApsp.Programs.Sec2.Theorem5.Pruned.Recursion
public import ThreeSumApsp.Programs.Sec2.Theorem5.Pruned.Restrict
public import ThreeSumApsp.Programs.Sec2.Theorem5.Pruned.Slices
public import ThreeSumApsp.Programs.Sec2.Theorem5.Pruned.Union

/-!
# The pruned recursion with its helpers

Let a program hold the bodies of fill, segBounds, union, pick and pruned as its procedures number
pFill, pSegBounds, pUnion, pPick and pPruned.  Then a call of pruned does what PrunedSpec says: it
writes the values of Pruned (Section 2.4.2) at the codes of its list to out, changes no cell but
these and its stack, and takes at most 5500 steps for each call of the recursion and for each code
passed to a call.  The proof puts the specifications of the four helpers into PrunedCtx.entry.
-/

public section

namespace Light.Sec2

open ThreeSumApsp

/-- **pruned** does what PrunedSpec says, in at most 5500 prunedWork steps.  Here
5500 = 50 · 70 + 2000, and 70 is the largest of the constants in the times of the four helpers. -/
theorem pruned_entry {lim : Limits} {P : Program} (std : Std lim)
    (hFill : P[pFill]? = some fillBody) (hSeg : P[pSegBounds]? = some segBoundsBody)
    (hUnion : P[pUnion]? = some unionBody) (hPick : P[pPick]? = some pickBody)
    (hPruned : P[pPruned]? = some prunedBody) : PrunedSpec lim P 5500 :=
  PrunedCtx.entry (h := 70)
    { std := std
      body := hPruned
      fill := fill_entry std hFill (by norm_num)
      segBounds := segBounds_entry std hSeg (by norm_num [cSegBounds])
      union := union_entry std hUnion le_rfl
      pickSet := pickSet_entry std hPick (by norm_num [cPick])
      pickAdd := pickAdd_entry std hPick (by norm_num [cPick]) }

end Light.Sec2
