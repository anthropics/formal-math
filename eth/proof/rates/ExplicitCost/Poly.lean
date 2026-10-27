/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ExplicitCost.EntryDefs
public import QueryMachines.Poly
public import PaddedDescent.F.CertNet
import Mathlib.Tactic

/-! # One certificate for the machine that reads K and g

`entryPoly : EntryPoly`. The certificates of the constructions are those of
proof/machines/QueryMachines/Poly.lean; those of the plain functions, jointly in K, g and the input,
are those of proof/rates/PaddedDescent/F/CertNet.lean. Here: the numbers P_a and c_{a,b} are lengths
of lists in the input (`keepsU_askedData`), K and g are lengths of lists in the input
(`kOf_unary`, `gOf_unary`), and the two queries (b, z_b) and ((a, b), (z_a, z_b)) jointly in K and g
(`qMb_joint`, `qPsi_joint`). -/

@[expose] public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed PaddedDescent.F.CertNet

variable {α : Type} [Enc α]

/-! ## The plain functions -/

/-- The numbers P_a and c_{a,b} are given in unary: they are lengths of lists in the input. -/
theorem keepsU_askedData : KeepsU askedData.under.toPaperNetwork where
  n := Unary.of_length (w := fun p : DataInput × ℕ => p.1.2.2.1.getD p.2 []) (by fun_prop)
  cap := Unary.of_length (w := fun p : DataInput × ℕ × ℕ => (p.1.2.2.2.getD p.2.1 []).getD p.2.2 []) (by fun_prop)

/-- K is given in unary. -/
theorem kOf_unary {u : α → X0 DataInput} (hu : PolyT u) : Unary fun t => kOf (u t) :=
  Unary.of_length (w := fun t => (u t).1.1.1.1) (by fun_prop)

/-- g is given in unary. -/
theorem gOf_unary {u : α → X0 DataInput} (hu : PolyT u) : Unary fun t => gOf (u t) :=
  Unary.of_length (w := fun t => (u t).1.1.1.2) (by fun_prop)

/-- The query (b, z_b), jointly in K, g and the input. -/
theorem qMb_joint {C : Type} [HasSize C] [Enc C] {Np : Procs C} (h : KeepsU Np.toPaperNetwork) {K g : α → ℕ} {u : α → (X0 C × ℕ) × ℕ} (hK : PolyT K) (hg : Unary g) (hu : PolyT u) :
    PolyT fun t => qMb (K t) (g t) Np (u t) := by
  have := hg.poly
  unfold qMb; fun_prop (disch := assumption)

/-- The query ((a, b), (z_a, z_b)), jointly in K, g and the input. -/
theorem qPsi_joint {C : Type} [HasSize C] [Enc C] {Np : Procs C} (h : KeepsU Np.toPaperNetwork) {K g : α → ℕ} {u : α → (X0 C × ℕ) × ℕ} (hK : PolyT K) (hg : Unary g) (hu : PolyT u) :
    PolyT fun t => qPsi (K t) (g t) Np (u t) := by
  have := hg.poly
  unfold qPsi; fun_prop (disch := assumption)

/-- The test whether the answer is not 0 is polynomial-time. -/
theorem isYes_polyT : PolyT fun v : ℤ => decide (v ≠ 0) :=
  (by fun_prop : PolyT fun v : ℤ => decide (0 < v.natAbs)).congr fun _ => decide_eq_decide.2 Int.natAbs_pos

/-- The query (a, z_a) with the K and g of the input. -/
theorem qW_data : PolyT fun u : (X0 DataInput × ℕ) × ℕ => qW (kOf u.1.1) (gOf u.1.1) askedData.under.toPaperNetwork u :=
  qW2 keepsU_askedData (kOf_unary (by fun_prop)).poly (gOf_unary (by fun_prop)) (by fun_prop)

/-- The query ((a, b), (z_a, θ_{a,b})) with the K and g of the input. -/
theorem qF_data : PolyT fun u : (X0 DataInput × ℕ) × ℕ => qF (kOf u.1.1) (gOf u.1.1) askedData.under.toPaperNetwork u :=
  qF2 keepsU_askedData (kOf_unary (by fun_prop)).poly (gOf_unary (by fun_prop)) (by fun_prop)

/-- The query (b, z_b) with the K and g of the input. -/
theorem qMb_data : PolyT fun u : (X0 DataInput × ℕ) × ℕ => qMb (kOf u.1.1) (gOf u.1.1) askedData.under u :=
  qMb_joint keepsU_askedData (kOf_unary (by fun_prop)).poly (gOf_unary (by fun_prop)) (by fun_prop)

/-- The query ((a, b), (z_a, z_b)) with the K and g of the input. -/
theorem qPsi_data : PolyT fun u : (X0 DataInput × ℕ) × ℕ => qPsi (kOf u.1.1) (gOf u.1.1) askedData.under u :=
  qPsi_joint keepsU_askedData (kOf_unary (by fun_prop)).poly (gOf_unary (by fun_prop)) (by fun_prop)

/-! ## The machines -/

/-- The test for membership: one query. -/
@[instance_reducible] def memCert : QueryMachine.IsPolyQ askedData.mem :=
  haveI := QueryMachine.IsPolyQ.query (A := ℤ) (h := fun x : DataInput × WQ => (Sum.inl x.2 : NetQuery)) (by fun_prop)
  QueryMachine.IsPolyQ.mapOut (QueryMachine.query fun x : DataInput × WQ => (Sum.inl x.2 : NetQuery)) isYes_polyT

/-- W_a: one query. -/
@[instance_reducible] def wCert : QueryMachine.IsPolyQ askedData.W :=
  QueryMachine.IsPolyQ.query (A := ℤ) (h := fun x : DataInput × WQ => (Sum.inr (Sum.inl x.2) : NetQuery)) (by fun_prop)

/-- Ψ_{a,b}: one query. -/
@[instance_reducible] def psiCert : QueryMachine.IsPolyQ askedData.Ψ :=
  QueryMachine.IsPolyQ.query (A := ℤ) (h := fun x : DataInput × PsiQ => (Sum.inr (Sum.inr (Sum.inl x.2)) : NetQuery)) (by fun_prop)

/-- f_{a,b}: one query. -/
@[instance_reducible] def fCert : QueryMachine.IsPolyQ askedData.f :=
  QueryMachine.IsPolyQ.query (A := ℤ) (h := fun x : DataInput × FQ => (Sum.inr (Sum.inr (Sum.inr x.2)) : NetQuery)) (by fun_prop)

/-- [z_a ∈ S_a]·W_a(z_a). -/
@[instance_reducible] def wDataCert : QueryMachine.IsPolyQ wData :=
  haveI := memCert
  haveI := wCert
  haveI := QueryMachine.IsPolyQ.mapIn qW_data askedData.mem
  haveI := QueryMachine.IsPolyQ.mapIn qW_data askedData.W
  QueryMachine.IsPolyQ.gated _ _

/-- [z_a ∈ S_a][z_b ∈ S_b]·Ψ_{a,b}(z_a, z_b). -/
@[instance_reducible] def psiDataCert : QueryMachine.IsPolyQ psiData :=
  haveI := memCert
  haveI := psiCert
  haveI := QueryMachine.IsPolyQ.mapIn qW_data askedData.mem
  haveI := QueryMachine.IsPolyQ.mapIn qMb_data askedData.mem
  haveI := QueryMachine.IsPolyQ.mapIn qPsi_data askedData.Ψ
  haveI := QueryMachine.IsPolyQ.gated (QueryMachine.mapIn (fun u : (X0 DataInput × ℕ) × ℕ => qMb (kOf u.1.1) (gOf u.1.1) askedData.under u) askedData.mem)
    (QueryMachine.mapIn (fun u : (X0 DataInput × ℕ) × ℕ => qPsi (kOf u.1.1) (gOf u.1.1) askedData.under u) askedData.Ψ)
  QueryMachine.IsPolyQ.gated _ _

/-- [z_a ∈ S_a]·f_{a,b}(z_a, θ_{a,b}). -/
@[instance_reducible] def fDataCert : QueryMachine.IsPolyQ fData :=
  haveI := memCert
  haveI := fCert
  haveI := QueryMachine.IsPolyQ.mapIn qW_data askedData.mem
  haveI := QueryMachine.IsPolyQ.mapIn qF_data askedData.f
  QueryMachine.IsPolyQ.gated _ _

/-- One factor of a term. -/
@[instance_reducible] def termDataCert : QueryMachine.IsPolyQ termData :=
  haveI := wDataCert
  haveI := psiDataCert
  haveI := fDataCert
  haveI := QueryMachine.IsPolyQ.ite (p := fun u : (X0 DataInput × ℕ) × ℕ => isPsi (kOf u.1.1) (gOf u.1.1) u)
    (isPsi2 (kOf_unary (by fun_prop)).poly (gOf_unary (by fun_prop)).poly (by fun_prop)) psiData fData
  haveI := QueryMachine.IsPolyQ.ite (p := fun u : (X0 DataInput × ℕ) × ℕ => isW (gOf u.1.1) u) (isW2 (gOf_unary (by fun_prop)).poly (by fun_prop)) wData
    (QueryMachine.ite (fun u : (X0 DataInput × ℕ) × ℕ => isPsi (kOf u.1.1) (gOf u.1.1) u) psiData fData)
  haveI : QueryMachine.IsPolyQ (QueryMachine.const 1 : QueryMachine NetQuery ℤ ((X0 DataInput × ℕ) × ℕ) ℤ) := QueryMachine.IsPolyQ.const 1
  QueryMachine.IsPolyQ.ite (isOne2 (kOf_unary (by fun_prop)).poly (gOf_unary (by fun_prop)).poly (by fun_prop)) _ _

/-- One entry. -/
@[instance_reducible] def entryDataCert : QueryMachine.IsPolyQ entryData :=
  haveI := termDataCert
  haveI := QueryMachine.IsPolyQ.prodRange (N := fun v : X0 DataInput × ℕ => nPairs (gOf v.1) v) termData
    (by have := (gOf_unary (u := fun v : X0 DataInput × ℕ => v.1) (by fun_prop)).poly; unfold nPairs; fun_prop)
  haveI := QueryMachine.IsPolyQ.sumRange (N := fun u : X0 DataInput => nStates (kOf u) (gOf u) askedData.under.toPaperNetwork u)
    (QueryMachine.prodRange (fun v : X0 DataInput × ℕ => nPairs (gOf v.1) v) termData)
    (nStates2 keepsU_askedData (kOf_unary (by fun_prop)).poly (gOf_unary (by fun_prop)) (by fun_prop))
  haveI : QueryMachine.IsPolyQ (QueryMachine.const 0 : QueryMachine NetQuery ℤ (X0 DataInput) ℤ) := QueryMachine.IsPolyQ.const 0
  QueryMachine.IsPolyQ.ite (validB2 keepsU_askedData (kOf_unary (by fun_prop)) (gOf_unary (by fun_prop)) (by fun_prop)) _ _

/-- **One certificate**: the machine that reads K and g from its input has polynomial-time steps. -/
theorem entryPoly : EntryPoly := ⟨entryDataCert⟩

end ExplicitCost
