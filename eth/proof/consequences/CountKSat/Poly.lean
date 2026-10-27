/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSat.Walk
public import SparsifyWidthK.Poly.Sparsify
public import ToTuring.Poly.Sat

/-! The functions of the counting program, defined in `proof/consequences/CountKSat/Defs.lean`, are
polynomial-time (`PolyT`), and the counting machine `countMK` is
`IsPolyT` (its init, step and out are polynomial-time) if its decoder, its step function and the
machine that counts one sparse formula are. The last
theorem proves `StCertStepC`, one of the interface statements of
`proof/consequences/CountKSat/Interfaces.lean`. The proofs use the certificate of
`pickK` in `proof/sparsification/SparsifyWidthK/Poly/Sparsify.lean`, that of the summing walk in
`proof/consequences/CountKSat/Walk.lean`, the closure lemmas in `proof/machines/ToTuring/Lib` and
the certificates of the
combinators in `proof/machines/ToTuring/Poly`. `isPolyT_countMK` follows `IsPolyT.satM` of
`proof/machines/ToTuring/Poly/Sat.lean`. -/

@[expose] public section

namespace CountKSat.Poly

open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog Groundwork.Stepped

variable {α : Type}

/-- Writing «no literal of H is true» as unit clauses is polynomial-time. -/
@[fun_prop] theorem polyT_negU [Enc α] {H : α → PCl} (hH : PolyT H) : PolyT fun x => negU (H x) := by
  unfold negU; fun_prop

/-- The two children of a node of the counting tree are computed in polynomial time, for all
thresholds θ and every width k. -/
@[fun_prop] theorem polyT_stepC [Enc α] (θ : ℕ → ℕ) (k : ℕ) {s : α → CNode} (hs : PolyT s) : PolyT fun x => stepC θ k (s x) := by
  unfold stepC; fun_prop

/-- The root of the counting tree is computed in polynomial time. The number n comes in unary, so
the n clauses xᵢ ∨ ¬xᵢ are no longer than the input. -/
theorem rootC_polyT : PolyT rootC := by
  have hr : PolyT fun p : List Unit × Fml => List.range p.1.length := PolyT.range (Unary.of_length (by fun_prop))
  unfold rootC taut; fun_prop

/-- The formula that is counted at a leaf is computed in polynomial time. -/
theorem leafF_polyT : PolyT leafF := by unfold leafF; fun_prop

/-- Writing the result as a word of n + 1 bits is polynomial-time, again because n comes in unary. -/
theorem outW_polyT : PolyT outW := by
  have hu : Unary fun q : (List Unit × Fml) × ℕ => q.1.1.length + 1 := (Unary.of_length (by fun_prop)).add (Unary.const 1)
  unfold outW
  exact PolyT.toWord' hu (by fun_prop)

/-- `countMK decU step M` is `IsPolyT` if `decU` and `step` are polynomial-time and M is `IsPolyT`. -/
@[instance_reducible] def isPolyT_countMK {decU : List Bool → List Unit × Fml} {step : CNode → Option (CNode × CNode)}
    (hd : PolyT decU) (hs : PolyT step) {M : Stepped Fml ℤ} [IsPolyT M] : IsPolyT (countMK decU step M) :=
  haveI := IsPolyT.mapOut (M := M) (f := Int.toNat) (by fun_prop)
  haveI := IsPolyT.mapIn (M := Stepped.mapOut M Int.toNat) leafF_polyT
  haveI := isPolyT_walkSum (T := Stepped.mapIn leafF (Stepped.mapOut M Int.toNat)) hs rootC_polyT
  haveI : IsPolyT (Stepped.const 0 : Stepped (List Unit × Fml) ℕ) := IsPolyT.const 0
  haveI := IsPolyT.ite (M := (Stepped.const 0 : Stepped (List Unit × Fml) ℕ))
    (N := walkSum step rootC (Stepped.mapIn leafF (Stepped.mapOut M Int.toNat))) (p := fun p => hasNil p.2)
    (by have := hasNil_polyT; fun_prop)
  haveI := IsPolyT.ofFun outW_polyT
  haveI := IsPolyT.bind (M := Stepped.ite (fun p : List Unit × Fml => hasNil p.2) (Stepped.const 0)
    (walkSum step rootC (Stepped.mapIn leafF (Stepped.mapOut M Int.toNat)))) (N := Stepped.ofFun outW)
  IsPolyT.mapIn hd

/-- One step of the counting tree is computed in polynomial time: the interface statement
`StCertStepC`. -/
theorem certStepC : StCertStepC := fun θ k => polyT_stepC θ k PolyT.id'

end CountKSat.Poly
