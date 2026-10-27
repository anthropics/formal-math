/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.SolverDefs
public import CountedRecursion.PolyQueries
public import ClauseBound.Alg.CertLevel
import Mathlib.Tactic

/-! # The plain functions of the solver

Every plain function of SolverDefs.lean is polynomial-time in what the solver holds. K and
2^{3ℓ'+x₀} are held in unary, so g, their product, and |ℛ| are given in unary; λ, B and ℓ are given
in unary; the number y of a pattern and d are given in binary. -/

public section

namespace ExplicitCost

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG Eight Eight.SecNetworks QueryMachines Printed

variable {α : Type} [Enc α]

/-- A number given in unary, written in unary. -/
@[fun_prop] theorem unary_polyT {f : α → ℕ} (hf : Unary f) : PolyT fun x => unary (f x) := hf

/-- λ is given in unary. -/
@[fun_prop] theorem hLam_unary {h : α → Head} (hh : PolyT h) : Unary fun x => hLam (h x) := by unfold hLam; fun_prop

/-- ℓ is given in unary. -/
@[fun_prop] theorem hLev_unary {h : α → Head} (hh : PolyT h) : Unary fun x => hLev (h x) := by unfold hLev; fun_prop

section Ready

variable {s : α → Ready} (hs : PolyT s)
include hs

/-- (ℓ, λ, B) is read off. -/
@[fun_prop] theorem rHead_polyT : PolyT fun x => rHead (s x) := by unfold rHead; fun_prop
/-- g, the product of two numbers held in unary, is given in unary. -/
@[fun_prop] theorem rG_unary : Unary fun x => rG (s x) := by unfold rG; fun_prop
/-- d is read off. -/
@[fun_prop] theorem rD_polyT : PolyT fun x => rD (s x) := by unfold rD; fun_prop
/-- The lists are read off. -/
@[fun_prop] theorem rLists_polyT : PolyT fun x => rLists (s x) := by unfold rLists; fun_prop
/-- |ℛ| is given in unary. -/
@[fun_prop] theorem rRect_unary : Unary fun x => rRect (s x) := by unfold rRect; fun_prop

end Ready

/-- «the |𝓘|^{|ℛ|} functions ι». -/
theorem nPatterns_polyT : PolyT nPatterns := by unfold nPatterns; fun_prop

/-- «the network with the smaller total». -/
@[fun_prop] theorem direction_polyT {v : α → Ready × ℕ} (hv : PolyT v) : PolyT fun x => direction (v x) :=
  PolyT.decide_lt
    (totalL_unary (L := fun x => rLists (v x).1) (p := fun x => rG (v x).1) (d := fun x => rG (v x).1) (tr := fun _ => true) (lam := fun x => hLam (rHead (v x).1)) (y := fun x => (v x).2)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)).poly
    (totalL_unary (L := fun x => rLists (v x).1) (p := fun x => rG (v x).1) (d := fun x => rG (v x).1) (tr := fun _ => false) (lam := fun x => hLam (rHead (v x).1)) (y := fun x => (v x).2)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)).poly

/-- The parent that is handed to the callee. -/
@[fun_prop] theorem parentAt_polyT {v : α → Ready × ℕ} {x : α → ℕ} (hv : PolyT v) (hx : PolyT x) : PolyT fun t => parentAt (v t) (x t) := by unfold parentAt; fun_prop

/-- What the search is given. -/
@[fun_prop] theorem searchInput_polyT (c : ℕ) {v : α → Ready × ℕ} (hv : PolyT v) : PolyT fun t => searchInput c (v t) := by unfold searchInput; fun_prop

/-- The context of the call. -/
@[fun_prop] theorem child_polyT {z : α → (Ready × ℕ) × CliqueCall} (hz : PolyT z) : PolyT fun t => child (z t) := by unfold child; fun_prop

/-- «computing d^{|ℛ|} and dividing by it». -/
theorem divide_polyT : PolyT fun p : Ready × ℤ => p.2 / (((rD p.1).toNat ^ rRect p.1 : ℕ) : ℤ) :=
  CertLevel.divZ_polyT (by fun_prop) (by fun_prop)

end ExplicitCost
