/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Bits
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Distinct
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Grid
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Host
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.LibraryContracts
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Modulus
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.NodeArray
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Parameters
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Prepare
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Reduction
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.TimeBound

/-!
# The program of the reduction from 3SUM to Convolution-3SUM, assembled

The procedures of the reduction are appended to the program of an arbitrary solver of
Convolution-3SUM. Each of them meets its specification because the procedures that it calls meet
theirs; the last one, the host, solves 3SUM (`isHost_s3`).  That the answer is right comes from
`core_spec`, through `threeSum_iff_trees`.  With the arithmetic of `claim_CH20_Theorem_5_1_of_host`
this gives [CH20, Theorem 5.1] (Theorem 21(a)) for programs of the light language
(`claim_CH20_Theorem_5_1`).
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp

namespace Proc

/-- The places of the procedures in the list `chBodies`. -/
abbrev emod : ℕ := 0
@[inherit_doc emod] abbrev log2 : ℕ := 1
@[inherit_doc emod] abbrev clog2 : ℕ := 2
@[inherit_doc emod] abbrev sqrt : ℕ := 3
@[inherit_doc emod] abbrev sieve : ℕ := 4
@[inherit_doc emod] abbrev half : ℕ := 5
@[inherit_doc emod] abbrev merge : ℕ := 6
@[inherit_doc emod] abbrev copy : ℕ := 7
@[inherit_doc emod] abbrev fill : ℕ := 8
@[inherit_doc emod] abbrev sort : ℕ := 9
@[inherit_doc emod] abbrev resid : ℕ := 10
@[inherit_doc emod] abbrev tally : ℕ := 11
@[inherit_doc emod] abbrev coll : ℕ := 12
@[inherit_doc emod] abbrev heavy : ℕ := 13
@[inherit_doc emod] abbrev search : ℕ := 14
@[inherit_doc emod] abbrev modulus : ℕ := 15
@[inherit_doc emod] abbrev nodeArray : ℕ := 16
@[inherit_doc emod] abbrev nodes : ℕ := 17
@[inherit_doc emod] abbrev distinct : ℕ := 18
@[inherit_doc emod] abbrev twice : ℕ := 19
@[inherit_doc emod] abbrev zeroThree : ℕ := 20
@[inherit_doc emod] abbrev bits : ℕ := 21
@[inherit_doc emod] abbrev pick : ℕ := 22
@[inherit_doc emod] abbrev round : ℕ := 23
@[inherit_doc emod] abbrev row : ℕ := 24
@[inherit_doc emod] abbrev grid : ℕ := 25
@[inherit_doc emod] abbrev params : ℕ := 26
@[inherit_doc emod] abbrev prep : ℕ := 27
@[inherit_doc emod] abbrev core : ℕ := 28
@[inherit_doc emod] abbrev host : ℕ := 29

end Proc

/-- The procedures of the reduction, for a solver of Convolution-3SUM that is procedure number pC3
of a program with o procedures: the procedure at the place i of this list gets the number o + i.
The places have the names `Proc.emod`, …, `Proc.host`, in the order of the list. -/
def chBodies (κ pC3 o : ℕ) : Program :=
  [emodBody,
    log2Body,
    clog2Body,
    sqrtBody,
    sieveBody,
    halfBody,
    mergeBody,
    copyBody,
    fillBody,
    sortBody (o + Proc.sort) (o + Proc.half) (o + Proc.merge) (o + Proc.copy),
    residBody (o + Proc.emod),
    tallyBody,
    collBody (o + Proc.resid) (o + Proc.tally),
    heavyBody (o + Proc.resid) (o + Proc.tally),
    searchBody (o + Proc.coll),
    modulusBody (o + Proc.search) (o + Proc.coll),
    nodeArrayBody (o + Proc.resid) (o + Proc.tally),
    nodesBody (o + Proc.nodes) (o + Proc.modulus) (o + Proc.nodeArray) pC3 (o + Proc.heavy),
    distinctBody,
    twiceBody,
    zeroThreeBody,
    bitsBody,
    pickBody,
    roundBody (o + Proc.pick) (o + Proc.nodes),
    rowBody (o + Proc.round),
    gridBody (o + Proc.row),
    paramsBody (o + Proc.log2) (o + Proc.clog2) (o + Proc.sqrt),
    prepBody (o + Proc.sieve) (o + Proc.fill) (o + Proc.copy) (o + Proc.sort) (o + Proc.distinct)
      (o + Proc.bits),
    coreBody (o + Proc.params) (o + Proc.prep) (o + Proc.grid) (o + Proc.twice) (o + Proc.zeroThree)
      (o + Proc.nodes),
    hostBody κ (o + Proc.core)]

/-- **The host**: from every solver of Convolution-3SUM, the procedures of the reduction make a
solver of 3SUM. -/
theorem isHost_s3 (κ : ℕ) : IsHost c3Task s3Task (chTime κ) (chNeed κ) := by
  refine ⟨fun P₀ pC3 T r hsol => ⟨chBodies κ pC3 P₀.length, P₀.length + Proc.host,
    hostBody κ (P₀.length + Proc.core), ?_,
    fun R lim d x μ fr hpre hok => ?_⟩, fun r hr => polyNeed_chNeed κ r hr⟩
  · have := getElem?_append_append (P₀ := P₀) (B := chBodies κ pC3 P₀.length) [] (i := Proc.host)
      rfl
    rwa [List.append_nil] at this
  rw [List.append_assoc]
  have L : ∀ {i : ℕ} {body : Stmt}, (chBodies κ pC3 P₀.length)[i]? = some body →
      (P₀ ++ (chBodies κ pC3 P₀.length ++ R))[P₀.length + i]? = some body :=
    fun h => getElem?_append_append R h
  have hEmod : EmodSpec lim (P₀ ++ (chBodies κ pC3 P₀.length ++ R)) P₀.length :=
    emodSpec_of (L (i := Proc.emod) rfl)
  have hLog2 := log2Spec_of (lim := lim) (L (i := Proc.log2) rfl)
  have hClog2 := clog2Spec_of (lim := lim) (L (i := Proc.clog2) rfl)
  have hPrimes := primesSpec_of (lim := lim) (L (i := Proc.sieve) rfl)
  have hSort :=
    sortSpec_of (lim := lim) ⟨L (i := Proc.sort) rfl, L (i := Proc.half) rfl,
      L (i := Proc.merge) rfl, L (i := Proc.copy) rfl⟩
  have hResid := resid_spec (L (i := Proc.resid) rfl) hEmod
  have hTally := tally_spec (lim := lim) (L (i := Proc.tally) rfl)
  have hColl := coll_spec (L (i := Proc.coll) rfl) hResid hTally
  have hHeavy := heavy_spec (L (i := Proc.heavy) rfl) hResid hTally
  have hModulus := modulusSpec_of (L (i := Proc.modulus) rfl) (L (i := Proc.search) rfl) hColl
  have hArray := nodeArray_spec (L (i := Proc.nodeArray) rfl) hResid hTally
  have hNodes := nodes_spec ⟨hsol, L (i := Proc.nodes) rfl, hModulus, hArray, hHeavy⟩
  have hDistinct := distinct_spec (lim := lim) (L (i := Proc.distinct) rfl)
  have hTwice := twice_spec (lim := lim) (L (i := Proc.twice) rfl)
  have hZero := zeroThree_spec (lim := lim) (L (i := Proc.zeroThree) rfl)
  have hBits := bits_spec (lim := lim) (L (i := Proc.bits) rfl)
  have hPick := pick_spec (lim := lim) (L (i := Proc.pick) rfl)
  have hRound := round_spec (L (i := Proc.round) rfl) hPick hNodes
  have hRow := row_spec (L (i := Proc.row) rfl) hRound
  have hGrid := grid_spec (L (i := Proc.grid) rfl) hRow
  have hParams := params_spec (L (i := Proc.params) rfl) hLog2 hClog2 (L (i := Proc.sqrt) rfl)
  have hPrep :=
    prep_spec (L (i := Proc.prep) rfl) hPrimes (L (i := Proc.fill) rfl) (L (i := Proc.copy) rfl)
      hSort hDistinct hBits
  have hCore := core_spec (L (i := Proc.core) rfl) hParams hPrep hGrid hTwice hZero hNodes
  exact host_spec hCore hpre hok

/-- [CH20, Theorem 5.1] for programs of the light language: 3SUM from Convolution-3SUM. -/
theorem claim_CH20_Theorem_5_1 : Claim.CH20_Theorem_5_1 lightModel :=
  claim_CH20_Theorem_5_1_of_host isHost_s3

end Light.Sec3.ChanHe
