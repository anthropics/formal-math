/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GraphProblems.Interfaces
public import GraphProblems.Engine
public import GraphProblems.Cert
public import ToTuring.Poly.Range
public import ToTuring.Machine.EndTM
import all StepMachines.Prog.Sat
import all StepMachines.Prog.Decode
import all WidthK.Top.Sat
import Mathlib.Tactic

/-! # A machine for counting the satisfying assignments with exactly s true variables

`sized b E`: on (n in unary, s, ψ), for every y < (b+1)^(n/b+1) run the counting engine E on the
formula `blockF b n s y ψ` (ψ, and digit i of y true variables in block i), and add the counts up.
This file defines this machine and its parts, proves `isPolyT_sized` for it, and proves small facts
on `cntN` and `ofWord`.
The paper's proof of Corollary 7 fixes the size with a circuit of O(n) gates instead. -/

@[expose] public section

namespace GraphProblems

open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Finset

/-- The input of the machine: (n in unary, s, ψ). -/
abbrev SIn : Type := List Unit × ℕ × Fml

/-- The number of vectors of block sizes. -/
def nY (b : ℕ) (a : SIn) : ℕ := (b + 1) ^ nBlocks b a.1.length

/-- The input of the engine for the vector y. -/
def buildB (b : ℕ) (p : SIn × ℕ) : List Unit × Fml :=
  (List.replicate (b * nBlocks b p.1.1.length) (), (blockF b p.1.1.length p.1.2.1 p.2 p.1.2.2).dedup)

/-- A word as an integer. -/
def wordZ (x : List Bool) : ℤ := (ofWord x : ℤ)

/-- The machine. -/
def sized (b : ℕ) (E : Stepped (List Unit × Fml) (List Bool)) : Stepped SIn ℕ :=
  Stepped.mapOut (sumRange (nY b) (Stepped.mapOut (Stepped.mapIn (buildB b) E) wordZ)) Int.toNat

theorem nY_polyT (b : ℕ) : PolyT (nY b) := by
  unfold nY
  exact PolyT.pow_unary (PolyT.const (b + 1)) (nBlocks_unary b (Unary.of_length (by fun_prop)))

theorem buildB_polyT (hB : StCertBlock) (b : ℕ) : PolyT (buildB b) := by
  have h1 : PolyT fun p : SIn × ℕ => List.replicate (b * nBlocks b p.1.1.length) () :=
    (Unary.const b).mul (nBlocks_unary b (Unary.of_length (by fun_prop)))
  have h2 := hB b
  unfold buildB; fun_prop

theorem wordZ_polyT : PolyT wordZ := by unfold wordZ; fun_prop

@[instance_reducible] def isPolyT_sized (hB : StCertBlock) (b : ℕ) {E : Stepped (List Unit × Fml) (List Bool)} [IsPolyT E] : IsPolyT (sized b E) :=
  haveI := IsPolyT.mapIn (M := E) (buildB_polyT hB b)
  haveI := IsPolyT.mapOut (M := Stepped.mapIn (buildB b) E) wordZ_polyT
  haveI := IsPolyT.sumRange (M := Stepped.mapOut (Stepped.mapIn (buildB b) E) wordZ) (nY_polyT b)
  IsPolyT.mapOut (M := sumRange (nY b) (Stepped.mapOut (Stepped.mapIn (buildB b) E) wordZ)) (f := Int.toNat) (by fun_prop)

/-! ### Small facts -/

theorem cntN_dedup (N : ℕ) (ψ : Fml) : cntN N ψ.dedup = cntN N ψ := by
  unfold cntN
  exact congrArg Finset.card (Finset.filter_congr fun a _ => by simp only [List.mem_dedup])

theorem cntN_le (N : ℕ) (ψ : Fml) : cntN N ψ ≤ 2 ^ N := by
  refine (Finset.card_filter_le _ _).trans ?_
  simp

theorem ofWord_binary {N v : ℕ} (h : v ≤ 2 ^ N) : ofWord (SatK.binary N v) = v := by
  have h2 : v < 2 ^ (N + 1) := lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num) (by omega))
  rw [SatK.binary, ← Decode.toWord_eq, ofWord_toWord h2]

end GraphProblems
