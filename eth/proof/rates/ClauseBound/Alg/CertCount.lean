/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.FuelCert
public import ToTuring.Poly.Count

/-! Polynomial-time certificates (`PolyT`, `Unary`) for those plain functions of the network of a
k-CNF that do not depend on the width k (`mu`, `rows` of StepMachines/Prog/CountNet.lean), with the
number g of groups as part of the data. -/

@[expose] public section

namespace ClauseBound.Alg.CertCount

open Groundwork Groundwork.Prog Groundwork.Prog.Count PaddedDescent.F

variable {α : Type} [Enc α]

/-- The number of clauses of a group, jointly in g and the formula. -/
@[fun_prop] theorem mu_polyT2 {g : α → ℕ} {φ : α → Fml} (hg : PolyT g) (hφ : PolyT φ) : PolyT fun x => mu (g x) (φ x) := by
  unfold mu
  exact PolyT.div (by fun_prop) hg

/-- The list 0, …, μ - 1 of the clauses of a group, jointly in g and the formula. -/
@[fun_prop] theorem rows_polyT2 {g : α → ℕ} {φ : α → Fml} (hg : PolyT g) (hφ : PolyT φ) : PolyT fun x => rows (g x) (φ x) := by
  have h : PolyT fun x => List.range (φ x).length := PolyT.range (Unary.of_length hφ)
  unfold rows; fun_prop

/-- The number of clauses of a group is given in unary, jointly in g and the formula. -/
@[fun_prop] theorem mu_unary2 {g : α → ℕ} {φ : α → Fml} (hg : PolyT g) (hφ : PolyT φ) : Unary fun x => mu (g x) (φ x) :=
  (Unary.of_length hφ).of_le (mu_polyT2 hg hφ) fun x => mu_le_length (g x) (φ x)

end ClauseBound.Alg.CertCount
