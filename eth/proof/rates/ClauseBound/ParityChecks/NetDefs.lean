/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.TopN.EvalW
public import ParityChecksStatement

/-! # The sums of the parity checks as sums over marks in layers: definitions and interface lemmas

A check number j becomes a dummy variable, number n + j; the incidence (e, j) becomes the clause
number e of ψ with the literal (n + j, false) of that dummy variable added. Then every sum that the
choice of the checks and the final count need is
a sum `truncW` over the assignments of n + r variables, with layers of clauses: all clauses, the
incidences, and, for `sumB` only, the clauses not yet decided; a mark in layer i has the weight
ws_i, and the number of marks
in layer i lies between lo_i and hi_i. A state of the choice is (j, t, Lam): Lam is the list of the
r checks, each a list of numbers of clauses; the checks before j are complete; check j has been
decided for
the clauses before t. -/

@[expose] public section

namespace ClauseBound.ParityChecks

open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.TopN.EvalW

/-- The incidences of the checks before j, each with its dummy literal, and those of check j
without. -/
def incL (n : ℕ) (ψ : Fml) (Lam : List (List ℕ)) (j : ℕ) : Fml :=
  ((List.range j).flatMap fun j' => (Lam.getD j' []).map fun e => ψ.getD e [] ++ [(n + j', false)]) ++
    (Lam.getD j []).map fun e => ψ.getD e []

/-- The sum for B_i (the quantity `_root_.ParityChecks.Bint`; `StBridgeB` states how the two are
related) in the state (j, t, Lam). -/
def sumB (n r nb M i : ℕ) (ψ : Fml) (Lam : List (List ℕ)) (j t : ℕ) : ℤ :=
  truncW (n + r) [1, -2, 1] [nb + 1, 0, i] [nb + 1, M, i] [ψ, incL n ψ Lam j, ψ.drop t]

/-- The sum for A (the quantity `_root_.ParityChecks.Aint`; `StBridgeA` states how the two are
related) in a state with the checks before j complete. -/
def sumA (n r nb M : ℕ) (ψ : Fml) (Lam : List (List ℕ)) (j : ℕ) : ℤ :=
  truncW (n + r) [1, -2] [nb + 1, 0] [nb + 1, M] [ψ, incL n ψ (Lam.take j) j]

/-- The sum for the final count. -/
def sumF3 (n r nb M : ℕ) (ψ : Fml) (Lam : List (List ℕ)) : ℤ :=
  truncW (n + r) [-1, -2] [0, 0] [nb, M] [ψ, incL n ψ (Lam.take r) r]

/-- The clauses that ξ violates, as a set of numbers of clauses. -/
def Vof {n : ℕ} (ψ : Fml) (ξ : Fin n → Bool) : Finset (Fin ψ.length) := Finset.univ.filter fun e => vio (Mark.ext ξ) (ψ.getD e.val []) = true

/-- The check number j as a set. -/
def Lof (ψ : Fml) (Lam : List (List ℕ)) (j : ℕ) : Finset (Fin ψ.length) := Finset.univ.filter fun e => e.val ∈ Lam.getD j []

/-- The clauses from number t on. -/
def Dof (ψ : Fml) (t : ℕ) : Finset (Fin ψ.length) := Finset.univ.filter fun e => t ≤ e.val

/-- The checks are lists without repetition of numbers of clauses. -/
def WfC (ψ : Fml) (r : ℕ) (Lam : List (List ℕ)) : Prop := Lam.length = r ∧ ∀ L ∈ Lam, L.Nodup ∧ ∀ e ∈ L, e < ψ.length

/-! ### Bridge.lean: the three sums are 2^r times B_i, A and the count, modulo 2^{M+1} -/

def StBridgeB : Prop := ∀ (n r nb M i j t : ℕ) (ψ : Fml) (Lam : List (List ℕ)), (∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) → WfC ψ r Lam → j < r →
  sumB n r nb M i ψ Lam j t ≡ 2 ^ r * _root_.ParityChecks.Bint (Vof (n := n) ψ) nb i j (Lof ψ Lam) (Dof ψ t) [ZMOD 2 ^ (M + 1)]

def StBridgeA : Prop := ∀ (n r nb M j : ℕ) (ψ : Fml) (Lam : List (List ℕ)), (∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) → WfC ψ r Lam → j ≤ r →
  sumA n r nb M ψ Lam j ≡ 2 ^ r * _root_.ParityChecks.Aint (Vof (n := n) ψ) nb j (Lof ψ Lam) [ZMOD 2 ^ (M + 1)]

def StBridgeF : Prop := ∀ (n r nb M : ℕ) (ψ : Fml) (Lam : List (List ℕ)), (∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) → WfC ψ r Lam →
  _root_.ParityChecks.Good (Vof (n := n) ψ) nb r (Lof ψ Lam) →
  sumF3 n r nb M ψ Lam ≡ 2 ^ r * (nSat n ψ : ℤ) [ZMOD 2 ^ (M + 1)]

end ClauseBound.ParityChecks
