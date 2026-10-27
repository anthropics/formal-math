/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSatStatement
public import CountKSat.Interfaces
public import ToTuring.PolyT
public import CountKSat.InOut
public import CountKSat.Value
public import CountKSat.StepCount
public import CountKSat.Walk
public import CountKSat.ProgC
public import CountKSat.Poly
public import CountKSat.Top.Count
public import StepMachines.Prog.BruteE
public import StepMachines.Prog.NetProg
public import StepMachines.Prog.NetRun
public import StepMachines.Prog.NetVal
public import StepMachines.Math.RebalanceArith
public import StepMachines.Prog.GridLoop
public import StepMachines.Prog.SidePresents
public import StepMachines.Prog.Sat
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import StepMachines.Math.SparsifyCount
public import NetworkStatements
public import Mathlib.Algebra.Polynomial.Coeff
public import ToTuring.Poly.Spec
public import ToTuring.Poly.Brute
public import ToTuring.Poly.NetFun
public import ToTuring.Poly.Basic
public import ToTuring.Poly.Range
public import ToTuring.Poly.Comb
public import ToTuring.Poly.GridSide
public import ToTuring.Poly.Count
public import ToTuring.Poly.Sat
public import ToTuring.Machine.EndTM
public import SparsifyWidthK.Thresholds

/-! # The counting engine

The machine for #k-SAT of proof/consequences/CountKSat/ is `Stepped.mapIn dU (…)`: a reader `dU` of
the input word, followed by a machine cut into steps whose input is the pair (N in unary, formula
with natural
numbers as variables). This file takes that second machine out (`engine`) and shows that it is
polynomial-time when its parts are (`isPolyT_engine`). It also holds `reaches_of_mapIn`
and `runs_of_mapIn`, which turn a run of `Stepped.mapIn f M` into a run of `M`, and `exists_toN`,
which writes a formula whose variables are below N as `Decode.toN φ` for a formula φ
on N variables. With these, a reduction to #k-SAT only has to produce the pair (N in unary,
formula). -/

@[expose] public section

namespace GraphProblems

open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat

/-- The counting machine of `proof/consequences/CountKSat/Defs.lean` without its reader. -/
def engine (step : CNode → Option (CNode × CNode)) (M : Stepped Fml ℤ) : Stepped (List Unit × Fml) (List Bool) :=
  Stepped.bind
    (Stepped.ite (fun p => hasNil p.2) (Stepped.const 0) (walkSum step rootC (Stepped.mapIn leafF (Stepped.mapOut M Int.toNat))))
    (Stepped.ofFun outW)

/-- The converse of `Stepped.mapIn_runs`. -/
theorem reaches_of_mapIn {α β γ : Type} {f : α → β} {M : Stepped β γ} {s : (Stepped.mapIn f M).σ} {t S : ℕ} {c : γ}
    (h : (Stepped.mapIn f M).Reaches S c s t) : M.Reaches S c s t := by
  induction h with
  | halt ho hs => exact .halt ho hs
  | step ho hs _ ih => exact .step ho hs ih

theorem runs_of_mapIn {α β γ : Type} {f : α → β} {M : Stepped β γ} {a : α} {t S : ℕ} {c : γ} (h : (Stepped.mapIn f M).Runs a t S c) :
    M.Runs (f a) t S c := reaches_of_mapIn (f := f) h

/-- The engine is `IsPolyT` if `step` is polynomial-time and M is `IsPolyT`. This is
`CountKSat.Poly.isPolyT_countMK` without its last line. -/
@[instance_reducible] def isPolyT_engine {step : CNode → Option (CNode × CNode)} (hs : PolyT step) {M : Stepped Fml ℤ} [IsPolyT M] :
    IsPolyT (engine step M) :=
  haveI := IsPolyT.mapOut (M := M) (f := Int.toNat) (by fun_prop)
  haveI := IsPolyT.mapIn (M := Stepped.mapOut M Int.toNat) Poly.leafF_polyT
  haveI := isPolyT_walkSum (T := Stepped.mapIn leafF (Stepped.mapOut M Int.toNat)) hs Poly.rootC_polyT
  haveI : IsPolyT (Stepped.const 0 : Stepped (List Unit × Fml) ℕ) := IsPolyT.const 0
  haveI := IsPolyT.ite (M := (Stepped.const 0 : Stepped (List Unit × Fml) ℕ))
    (N := walkSum step rootC (Stepped.mapIn leafF (Stepped.mapOut M Int.toNat))) (p := fun p => hasNil p.2)
    (by have := hasNil_polyT; fun_prop)
  haveI := IsPolyT.ofFun Poly.outW_polyT
  IsPolyT.bind (M := Stepped.ite (fun p : List Unit × Fml => hasNil p.2) (Stepped.const 0)
    (walkSum step rootC (Stepped.mapIn leafF (Stepped.mapOut M Int.toNat)))) (N := Stepped.ofFun outW)

/-- A formula whose variables are below N is `toN φ` for a formula φ on N variables. -/
theorem exists_toN {N : ℕ} {ψ : Fml} (h : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < N) : ∃ φ : Sat3.CNF N, Decode.toN φ = ψ := by
  refine ⟨ψ.pmap (fun C hC => C.pmap (fun l hl => ((⟨l.1, hl⟩ : Fin N), l.2)) hC) h, ?_⟩
  unfold Decode.toN
  rw [List.map_pmap]
  conv_rhs => rw [← List.map_id ψ]
  rw [← List.pmap_eq_map (p := fun C => ∀ l ∈ C, l.1 < N) (H := h)]
  refine List.pmap_congr_left ψ fun C _ hC _ => ?_
  rw [List.map_pmap]
  conv_rhs => rw [id, ← List.map_id C]
  rw [← List.pmap_eq_map (p := fun l : ℕ × Bool => l.1 < N) (H := hC)]
  exact List.pmap_congr_left C fun l _ _ _ => rfl

end GraphProblems
