/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PiecesCountedStatement
import PiecesCounted.Basic
import QueryMachines.CombRuns
import Mathlib.Tactic

/-! # From the oracle to the algorithm

A machine that asks the pieces at the prices `price c` stays within its cost when each of these
queries is answered by running the algorithm of the last clause of Definition 7(c). This is the
substitution rule for query machines (`QueryMachines.stSubstWithin`) with the answering machine
`passOrRun Alg`:
a query of the first kind is asked again (no own step, cost w x); a query to the pieces is answered
by running Alg (at most 2^{cλ} own steps, no query). In both cases the substitution rule charges two
more, and these are in the prices of the hypothesis. -/

public section

namespace PiecesCounted

open Groundwork QueryMachines

/-- The answering machine on a query of the first kind: it asks the query again and hands the answer
back. -/
theorem passOrRun_pass {Q : Type} [HasSize Q] (Alg : Stepped (List Unit × Question) Answer) (O : Q → Option Answer) (w : Q → ℕ) {x : Q} {v : Answer} (hv : O x = some v) :
    (passOrRun Alg).Within O w ((), Sum.inl x) (w x) (max (size x) (size v) + 2) v :=
  ⟨0, [id x], (stBranchRuns Q Answer (Unit × (Q ⊕ (List Unit × Question))) Q (List Unit × Question) Answer (fun p => p.2) (QueryMachine.query id) (QueryMachine.lift Alg) O ((), Sum.inl x) 0
    (max (size x) (size v) + 1) [id x] v).1 x rfl (stQueryRuns Q Answer Q id O x v hv), by simp⟩

/-- The answering machine on a query to the pieces: it runs the algorithm. -/
theorem passOrRun_run {Q : Type} [HasSize Q] {Alg : Stepped (List Unit × Question) Answer} (O : Q → Option Answer) (w : Q → ℕ) {g : List Unit × Question} {v : Answer} {t S : ℕ} (h : Alg.Runs g t S v) :
    (passOrRun Alg).Within O w ((), Sum.inr g) t (S + 1) v :=
  ⟨t, [], (stBranchRuns Q Answer (Unit × (Q ⊕ (List Unit × Question))) Q (List Unit × Question) Answer (fun p => p.2) (QueryMachine.query id) (QueryMachine.lift Alg) O ((), Sum.inr g) t
    S [] v).2 g rfl (stLiftRuns Q Answer (List Unit × Question) Answer Alg O g t S v h), by simp⟩

/-- Proof of `OracleFromAlgorithm`: the substitution `stSubstWithin` puts the answering machine
`passOrRun Alg` in place of the oracle, and each answer stays within its price. -/
theorem oracleFromAlgorithm : OracleFromAlgorithm := by
  intro Q α β _ M Alg D c hC O w a T S Λ SQ b hSQ hM
  have key := stSubstWithin (Q ⊕ (List Unit × Question)) Answer Q Answer Unit α β M (passOrRun Alg) (Sum.elim O fun g => if g.1.length ≤ Λ then D.oracle g else none) O
    (Sum.elim (fun x => w x + 2) (price c)) w () a T S (max (room c Λ + 1) (SQ + 2)) b (Sum.elim w fun g => steps c g.1.length) hM ?_ ?_
  · obtain ⟨own, L, hr, hle⟩ := key
    refine ⟨own, L, QueryMachine.Runs.mono (stMapInRuns _ _ _ _ _ (fun a : α => ((), a)) (M.subst (passOrRun Alg)) O a own _ L b hr) le_rfl ?_, hle⟩
    have e : size () = 1 := rfl
    rw [e]
    omega
  · rintro (x | g) v hv
    · have hv' : O x = some v := hv
      have := hSQ x v hv'
      exact (passOrRun_pass Alg O w hv').mono le_rfl (by omega)
    · have hv' : (if g.1.length ≤ Λ then D.oracle g else none) = some v := hv
      split at hv'
      · rename_i hg
        have := room_le_of_length_le c hg
        exact (passOrRun_run O w (hC g v hv')).mono le_rfl (by omega)
      · cases hv'
  · rintro (x | g) <;> exact le_rfl

end PiecesCounted
