/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.HandOver
public import Eight.ViaGrouping.LevelEnd
public import ToTuring.Poly.GridSide
import Mathlib.Tactic

/-! # The algorithm of the proof of Proposition 3 has polynomial-time steps
The counterpart of `Eight.ViaGrouping.stLevelKeepsP_of`
(proof/networks/Eight/ViaGrouping/LevelCert.lean) for `levelMachine`.
The certificates of the plain functions (the number of functions ι, the choice of the network, the
division, P_a, c_{a,a'}, Ψ_{a,a'}, f_{a,a'}, the check and the queries of W_a) are used here as
lemmas, such as `Eight.Level.Cert.numPat8_polyT` and `Eight.Level.Cert.factor_polyT`;
those of the constructions are in proof/machines/QueryMachines/Poly.lean; that of `networkOn` is in
proof/threesat/Printed/HandOver.lean. That the machine of Lemma 1 has polynomial-time steps is a
hypothesis here (`StGroupingPoly`). -/

public section

namespace Printed

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine

/-- λ is given in unary. -/
theorem lamOf_unary : Unary fun c : List Unit × List Unit => c.1.length := Unary.of_length (by fun_prop)

/-- B is given in unary. -/
theorem bitsOf_unary : Unary fun c : List Unit × List Unit => c.2.length := Unary.of_length (by fun_prop)

/-- The weight of a row or column, computed with queries to the tables, has polynomial-time steps. -/
theorem sideWQ_poly (g : ℕ) (tr : Bool) : (sideWQ g tr fun c : List Unit × List Unit => c.1.length).PolyTimeSteps := by
  have hl := lamOf_unary
  have i0 : IsPolyQ (askTable : QueryMachine TableQuery ℤ ((List Unit × List Unit) × IQ) ℤ) := IsPolyQ.query (by unfold toTable; fun_prop)
  have i1 := IsPolyQ.mapIn (sideQuery_polyT (lam := fun c : List Unit × List Unit => c.1.length) g tr hl.poly) (askTable : QueryMachine TableQuery ℤ ((List Unit × List Unit) × IQ) ℤ)
  have i2 := IsPolyQ.prodRange (N := sideG g) (QueryMachine.mapIn (sideQuery g tr fun c : List Unit × List Unit => c.1.length) askTable) (sideG_polyT g)
  have i3 : IsPolyQ (QueryMachine.const 0 : QueryMachine TableQuery ℤ (((List Unit × List Unit) × ℕ) × WQ) ℤ) := IsPolyQ.const 0
  exact ⟨IsPolyQ.ite (sideChk_polyT (lam := fun c : List Unit × List Unit => c.1.length) g tr hl.poly) _ _⟩

/-- A machine for networks with polynomial-time steps, on the row network or the column network of
ι. -/
theorem networkOn_gridProcs_poly (g : ℕ) (tr : Bool) (NM : NetMachine) (hN : NM.PolyTimeSteps) : (networkOn g NM (gridProcs g tr)).PolyTimeSteps := by
  have hl := lamOf_unary
  have hb := bitsOf_unary
  have hl1 : Unary fun c : (List Unit × List Unit) × ℕ => c.1.1.length := hl.comp (h := fun c : (List Unit × List Unit) × ℕ => c.1) PolyT.id'.fst
  have hb1 : Unary fun c : (List Unit × List Unit) × ℕ => c.1.2.length := hb.comp (h := fun c : (List Unit × List Unit) × ℕ => c.1) PolyT.id'.fst
  refine networkOn_poly g NM (gridProcs g tr) hN ?_ ?_ ?_ ?_ ?_ (sideWQ_poly g tr) ?_ ?_
  · exact (Unary.const (g ^ 3)).mul hl1
  · exact (((Unary.const g).mul hb1).add ((Unary.const (g ^ 2)).mul hl1)).add (Unary.const 1)
  · exact (Unary.const (nMemb g g tr * (g * g))).mul (hl.comp (h := fun p : ((List Unit × List Unit) × ℕ) × ℕ => p.1.1) PolyT.id'.fst.fst)
  · exact CertGridG.capG_unary Eight.stKeeps (Unary.const g) (Unary.const g) (PolyT.const tr) (Unary.const 0)
      (hl.comp (h := fun p : ((List Unit × List Unit) × ℕ) × ℕ × ℕ => p.1.1) PolyT.id'.fst.fst) PolyT.id'.fst.snd PolyT.id'.snd.fst PolyT.id'.snd.snd
  · have i0 := IsPolyT.const (α := Unit) true
    have i1 := IsPolyT.mapIn (M := (Stepped.const true : Stepped Unit Bool)) (f := fun _ : ((List Unit × List Unit) × ℕ) × WQ => ()) (by fun_prop)
    exact ⟨IsPolyQ.lift _⟩
  · have i0 : IsPolyT (Stepped.ofFun fun x : ((List Unit × List Unit) × ℕ) × PsiQ => gridPsi g tr x.1.1.1.length x.1.2 x.2) := IsPolyT.ofFun (stPsiPoly g tr (List Unit × List Unit) (fun c => c.1.length) hl)
    exact ⟨IsPolyQ.lift _⟩
  · have i0 : IsPolyT (Stepped.ofFun fun x : ((List Unit × List Unit) × ℕ) × FQ => gridFf eightF [] g g tr 0 x.1.1.1.length x.1.2 x.2) := IsPolyT.ofFun (Eight.Level.Cert.factor_polyT (lam := fun c : List Unit × List Unit => c.1.length) Eight.stKeeps g tr hl)
    exact ⟨IsPolyQ.lift _⟩

/-- The loop over ι has polynomial-time steps. -/
theorem levelLoop_poly (g : ℕ) (NM : NetMachine) (hN : NM.PolyTimeSteps) :
    (QueryMachine.sumRange (numPat8 g fun c : List Unit × List Unit => c.1.length)
      (QueryMachine.ite (useRowP g fun c : List Unit × List Unit => c.1.length) (networkOn g NM (gridProcs g false)) (networkOn g NM (gridProcs g true)))).PolyTimeSteps := by
  have hl := lamOf_unary
  obtain ⟨i1⟩ := networkOn_gridProcs_poly g false NM hN
  obtain ⟨i2⟩ := networkOn_gridProcs_poly g true NM hN
  have i3 := IsPolyQ.ite (Eight.Level.Cert.useRowP_polyT (lam := fun c : List Unit × List Unit => c.1.length) Eight.stKeeps g hl) (networkOn g NM (gridProcs g false)) (networkOn g NM (gridProcs g true))
  exact ⟨IsPolyQ.sumRange _ (Eight.Level.Cert.numPat8_polyT (lam := fun c : List Unit × List Unit => c.1.length) g hl)⟩

/-- The division at the end has polynomial-time steps. -/
theorem levelDiv_poly (g : ℕ) :
    (QueryMachine.lift (Stepped.ofFun fun p : (List Unit × List Unit) × ℤ => p.2 / ((2 ^ (tOf p.1.1.length * nRect g) : ℕ) : ℤ)) : QueryMachine TableQuery ℤ ((List Unit × List Unit) × ℤ) ℤ).PolyTimeSteps := by
  have i5 := IsPolyT.ofFun (Eight.Level.Cert.div_polyT (lam := fun c : List Unit × List Unit => c.1.length) g lamOf_unary)
  exact ⟨IsPolyQ.lift _⟩

/-- The machine of Proposition 3 has polynomial-time steps if M has. The hypothesis: the machine of
Lemma 1 has polynomial-time steps if M has. -/
theorem stLevelPoly_of (hG : StGroupingPoly) : StLevelPoly := by
  intro K g M hM
  obtain ⟨i1⟩ := levelLoop_poly g _ (hG K g M hM)
  obtain ⟨i2⟩ := levelDiv_poly g
  exact ⟨IsPolyQ.bind _ _⟩

end Printed
