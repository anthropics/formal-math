/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsifyThenCount.Defs
import VariableBound.Cert.Top
import UniformInK.Cert.Top
import ClauseBound.ParityChecks.CertTopOL
import ClauseBound.Alg.Decode

/-! # The function `ADG Θ` is polynomial-time for every family of thresholds Θ that serves

`stCertDG : StepSparsify.StCertWalkSG → StepSparsify.StCertNoTaut → VariableBound.StCertCountD → StCertDG`.
The lemmas on the parameters and on the plan are taken from
proof/variables/VariableBound/Cert/Top.lean. Three
points are particular to this function. The walk has the thresholds Θ k s. Its certificate (a
hypothesis, `StepSparsify.StCertWalkSG`) asks for the precision s in unary instead of τ in binary; s
is the length of a list of units that is
computed in polynomial time. The root of the tree is the formula without the clauses that contain a
variable together with its negation, and deleting them is polynomial-time by the hypothesis
`StepSparsify.StCertNoTaut`. The exponent function
`VariableBound.eD` is the one of proof/variables/VariableBound; `eD_polyT` proves its certificate
with no hypothesis on a walk. -/

public section

namespace SparsifyThenCount

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound VariableBound.CertTop SparsificationLemma

/-- The plan, as a function of the input, is polynomial-time, if the solver, `pick` and `slU` are. -/
theorem planD_polyT {Idx : Type} [Enc Idx] (S : Solver Idx) (hP : S.Poly) {pick : U → U × Idx} {slU : U → U} (hpick : PolyT pick) (hsl : PolyT slU) :
    PolyT (planD S pick slU) := by
  have hd0 : PolyT fmlOf := Decode.stCertDecM.2
  have hk0 : Unary kU := Unary.of_length Decode.stCertDecM.1
  have hn0 : Unary nU := Unary.of_length hd0.fst
  have hlv0 : PolyT fun x : List Bool => pick (root17 (nU x)) := PolyT.comp hpick (root17_polyT hn0)
  exact planAtD_polyT S hP hk0 hn0 hlv0.snd (Unary.of_length (PolyT.comp hsl hlv0.fst))

/-- The exponent function of the input for the bound in n is polynomial-time, if the solver, `pick`
and `slU` are. -/
theorem eD_polyT {Idx : Type} [Enc Idx] (S : Solver Idx) (hP : S.Poly) {pick : U → U × Idx} {slU : U → U} (hpick : PolyT pick) (hsl : PolyT slU) :
    PolyT (eD S pick slU) := by
  have hn0 : Unary nU := Unary.of_length (PolyT.fst Decode.stCertDecM.2)
  unfold eD
  exact PolyT.optionGetD (planD_polyT S hP hpick hsl) hn0.poly

/-- For thresholds that serve, the function `ADG Θ` of (input, pad) is polynomial-time if the
solver, `pick` and `slU` are; given the certificates of the walk (`StepSparsify.StCertWalkSG`), of
the deletion of the clauses that contain a variable
together with its negation (`StepSparsify.StCertNoTaut`) and of the count of one sparse formula by
Steps 1 to 4 (`VariableBound.StCertCountD`). -/
theorem stCertDG (hW : StepSparsify.StCertWalkSG) (hN : StepSparsify.StCertNoTaut) (hC : StCertCountD) : StCertDG := by
  intro Θ Lc hΘ Idx _ S hP pick slU hpick hsl
  have hd0 : PolyT fmlOf := Decode.stCertDecM.2
  have hk0 : Unary kU := Unary.of_length Decode.stCertDecM.1
  have hn0 : Unary nU := Unary.of_length hd0.fst
  have hlv0 : PolyT fun x : List Bool => pick (root17 (nU x)) := PolyT.comp hpick (root17_polyT hn0)
  have hi0 : PolyT (idxU pick) := hlv0.snd
  have hs0 : Unary (precU pick slU) := Unary.of_length (PolyT.comp hsl hlv0.fst)
  have hpl : PolyT (planD S pick slU) := planD_polyT S hP hpick hsl
  have hd : PolyT fun p : List Bool × U => fmlOf p.1 := PolyT.comp hd0 PolyT.id'.fst
  have hp : PolyT fun p : List Bool × U => p.2 := by fun_prop
  have hn : Unary fun p : List Bool × U => nU p.1 := hn0.comp PolyT.id'.fst
  have hs : Unary fun p : List Bool × U => precU pick slU p.1 := hs0.comp PolyT.id'.fst
  have hkc0 : Unary fun x : List Bool => kcU (kU x) (nU x) := kcU_unary hk0 hn0.poly
  have hkc : Unary fun p : List Bool × U => kcU (kU p.1) (nU p.1) := hkc0.comp PolyT.id'.fst
  have hkp : Unary fun p : List Bool × U => 2 ^ kcU (kU p.1) (nU p.1) :=
    (powKcU_unary hk0 hn0).comp (h := fun p : List Bool × U => p.1) PolyT.id'.fst
  have hl := leafM_polyT
  have hk1 : Unary fun q : (List Bool × U) × CNode => kcU (kU q.1.1) (nU q.1.1) := hkc.comp (h := fun q : (List Bool × U) × CNode => q.1) (by fun_prop)
  have hn1 : Unary fun q : (List Bool × U) × CNode => nU q.1.1 := hn.comp (h := fun q : (List Bool × U) × CNode => q.1) (by fun_prop)
  have hs1 : Unary fun q : (List Bool × U) × CNode => precU pick slU q.1.1 := hs.comp (h := fun q : (List Bool × U) × CNode => q.1) (by fun_prop)
  have hD1 := blockU_unary hk1 hn1 hs1
  have hi1 : PolyT fun q : (List Bool × U) × CNode => idxU pick q.1.1 := PolyT.comp (g := fun q : (List Bool × U) × CNode => q.1.1) hi0 (by fun_prop)
  have hv : PolyT fun q : (List Bool × U) × CNode =>
      valD S (kcU (kU q.1.1) (nU q.1.1)) q.1.2 (idxU pick q.1.1) (fmlOf q.1.1).1.length (precU pick slU q.1.1) q.2 := by
    have hg : PolyT fun q : (List Bool × U) × CNode => (List.replicate (kcU (kU q.1.1) (nU q.1.1)) (), q.1.2, idxU pick q.1.1,
        (List.replicate (nU q.1.1) (), List.replicate (blockU (kcU (kU q.1.1) (nU q.1.1)) (nU q.1.1) (precU pick slU q.1.1)) ()), leafM q.2) :=
      PolyT.prodMk hk1 (PolyT.prodMk (by fun_prop) (PolyT.prodMk hi1 (PolyT.prodMk (PolyT.prodMk hn1 hD1) (by fun_prop))))
    refine (PolyT.comp (hC Idx S hP) hg).congr fun q => ?_
    simp only [List.length_replicate]
    rfl
  have hroot : PolyT fun p : List Bool × U => rootC ((fmlOf p.1).1, noTaut (fmlOf p.1).2) :=
    PolyT.comp rootC_polyT (PolyT.prodMk hd.fst (PolyT.comp hN hd.snd))
  have hnum : PolyT fun p : List Bool × U => numDG Θ S (kcU (kU p.1) (nU p.1)) (idxU pick p.1) (precU pick slU p.1) (fmlOf p.1) p.2 := by
    unfold numDG
    exact PolyT.cond' (PolyT.comp hasNil_polyT hd.snd) (PolyT.const 0)
      (hW Θ Lc hΘ _ (fun p : List Bool × U => kcU (kU p.1) (nU p.1)) (fun p => precU pick slU p.1) (fun p => p.2)
        (fun p => valD S (kcU (kU p.1) (nU p.1)) p.2 (idxU pick p.1) (fmlOf p.1).1.length (precU pick slU p.1))
        (fun p => rootC ((fmlOf p.1).1, noTaut (fmlOf p.1).2)) hkc hkp hs hp hv hroot)
  have hbr : PolyT bruteU := by
    have h := bruteN_polyT_aux hd (pad := fun p : List Bool × U => p.2) hp
    unfold bruteU
    exact h
  have hno : PolyT fun p : List Bool × U => (planD S pick slU p.1).isNone := PolyT.optionIsNone (PolyT.comp hpl PolyT.id'.fst)
  unfold ADG
  exact PolyT.comp outW_polyT (PolyT.prodMk hd (PolyT.cond' hno hbr hnum))

end SparsifyThenCount
