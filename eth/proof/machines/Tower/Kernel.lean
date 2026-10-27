/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import QueryMachines.Runs

/-! # Rules for costs

`WithinFrom.mono` and the three rules of `stWithinRules` (proof/machines/QueryMachines/Runs.lean),
with implicit arguments: the form in which the proofs of this folder use them. Nothing is proved
anew here. -/

public section

namespace QueryMachines.Tower

open Groundwork

variable {Q A α β : Type} {M : QueryMachine Q A α β} {O : Q → Option A} {w : Q → ℕ} {s : M.σ} {b : β} {S S' T T' : ℕ}

/-- The cost and the bound on the sizes may be raised. -/
theorem wfMono (h : M.WithinFrom O w s T S b) (hT : T ≤ T') (hS : S ≤ S') : M.WithinFrom O w s T' S' b := QueryMachine.WithinFrom.mono h hT hS

/-- A halted state costs nothing. -/
theorem wfHalt (h1 : M.out s = some b) (h2 : size s ≤ S) : M.WithinFrom O w s T S b := (stWithinRules Q A α β M O w s T S b).1 h1 h2

/-- An own step costs 1. -/
theorem wfStep (h1 : M.out s = none) (h2 : M.ask s = none) (h3 : size s ≤ S) (h : M.WithinFrom O w (M.step s) T S b) : M.WithinFrom O w s (T + 1) S b :=
  (stWithinRules Q A α β M O w s T S b).2.1 h1 h2 h3 h

/-- The query x costs w x. -/
theorem wfQuery {x : Q} {v : A} (h1 : M.out s = none) (h2 : M.ask s = some x) (h3 : O x = some v) (h4 : size s ≤ S) (h : M.WithinFrom O w (M.resume s v) T S b) :
    M.WithinFrom O w s (T + w x) S b :=
  (stWithinRules Q A α β M O w s T S b).2.2 x v h1 h2 h3 h4 h

end QueryMachines.Tower
