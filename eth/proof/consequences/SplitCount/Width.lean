/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SplitCount.Defs
import Occ.Main
import GraphProblems.Engine

/-! # Proof of Corollary 6: the width reduction (the part beginning «Second» in its proof)

«each of these is turned into a 3-CNF with O(n) clauses and O(n) variables and the same number of
satisfying assignments, by the standard width reduction, which introduces a constant number of new
variables for each clause. The number is preserved if each new variable is forced, by three clauses
of at most 3 literals, to equal the disjunction of the two literals that it replaces in a long
clause»
The width reduction and its properties are those of proof/networks/Eight/Cor/Width.lean
(`Eight.Width.stWidth`), for formulas with variables in `Fin n`; the program `Eight.Width.widthP` on
formulas with numbers as variables gives the same formula (`Eight.Width.toN_widthReduce`) with the
same count (`Eight.Width.cntN_splitN`).
A formula on x₀ … xₙ₋₁ is `Decode.toN φ` for some φ (`GraphProblems.exists_toN`). -/

public section

namespace SplitCount

open Groundwork Groundwork.Prog CountKSat Eight.Width Occ

/-- **The width reduction of Corollary 6**, for the program: on Ψ on x₀ … xₙ₋₁ with m clauses of ≤ w
literals, `widthP` gives (n₃ in unary, Ψ₃): ≤ 3 literals per clause, variables below n₃, no clause
twice, n₃ ≤ n + (w−3)·m, ≤ m + 3(w−3)·m clauses, and as many satisfying assignments on n₃ variables
as Ψ on n. -/
theorem stStepThree : StStepThree := by
  intro w n Ψ hw hb
  obtain ⟨φ, rfl⟩ := GraphProblems.exists_toN hb
  obtain ⟨⟨h3, hnd⟩, -, hk⟩ := stWidth n φ
  obtain ⟨hf, hl⟩ := hk w fun C hC => by
    have := hw _ (List.mem_map_of_mem hC)
    simpa using this
  have e1 : (widthP (List.replicate n (), Decode.toN φ)).1.length = n + numFresh φ := by simp [widthP, numFresh_toN]
  have e2 : (widthP (List.replicate n (), Decode.toN φ)).2 = Decode.toN (widthReduce φ) := by simp [widthP, toN_widthReduce]
  rw [e1, e2, Decode.length_toN, Decode.length_toN]
  refine ⟨fun C hC => ?_, below_toN _, ?_, by omega, hl, ?_⟩
  · obtain ⟨⟨D, hD, hDl⟩, -⟩ := Decode.mem_toN hC
    exact hDl ▸ h3 D hD
  · refine List.Nodup.map (List.map_injective_iff.2 fun a b hab => ?_) hnd
    exact Prod.ext (Fin.ext (Prod.ext_iff.1 hab).1) (Prod.ext_iff.1 hab).2
  · rw [toN_widthReduce, ← numFresh_toN, cntN_splitN]

end SplitCount
