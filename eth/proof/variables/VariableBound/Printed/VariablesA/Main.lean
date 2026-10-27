/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Printed.ThmVariablesADefs
public import VariableBound.Top.Defs
import VariableBound.Printed.VariablesA.Level
import VariableBound.Printed.VariablesA.Arith
import UniformInK.Top.Time

/-! # The level of n, in unary

Two lemmas on the level of n, for the bound in the number n of variables (Appendix D):
`eq_replicate`, a list of units is known by its length, and `pick_eq`, what `Q.pick` gives for
⌊n^(1/17)⌋
is the level of n (`IsLevel`), written in unary. -/

public section

namespace VariableBound.VariablesA

open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN UniformInK MainTheoremForms
open Sat3 (CNF)

variable {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀)

/-- A list of units is known by its length. -/
theorem eq_replicate (u : U) : u = List.replicate u.length () := List.eq_replicate_iff.2 ⟨rfl, fun _ _ => rfl⟩

/-- What `Q.pick` gives for ⌊n^(1/17)⌋ is the level of n, in unary. -/
theorem pick_eq {n l : ℕ} (h : IsLevel S Q n l) : (Q.pick (root17 n)).1 = List.replicate l () := by
  rw [eq_replicate (Q.pick (root17 n)).1, level_eq_pick Q h]

end VariableBound.VariablesA
