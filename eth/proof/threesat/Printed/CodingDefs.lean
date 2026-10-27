/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.Programs

/-! # Between Definition 3's tables and the tables of this development (definitions and statements only)

Definition 3 writes a setting z_w as ONE string of (K − 1)λ bits; the programs and theorems of this
development write it as the list of K strings with the empty string at w (`Paper.Tables`,
`Groundwork.Prog.ServesInst`). These three statements carry everything across; the files on
Definition 4, Lemma 1 and Proposition 3 use them and nothing else about the coding.
This file has no proofs. -/

@[expose] public section

namespace Printed

open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines

/-- Tables as Definition 3 has them (argument: one string), read as tables of this development
(argument: one string for every node, the empty string at w itself): the strings are concatenated. -/
def listTables (K : ℕ) (W : ℕ → List Bool → ℤ) : Paper.Tables K := fun v θ => W v.val (List.ofFn θ).flatten

/-- The query machine `askTable`, closed over the tables `tables K lam W`, is a procedure that
answers every well-formed query of this development in ONE step. -/
def StAskServes : Prop := ∀ (C : Type) [HasSize C] (K lam B : ℕ) (W : ℕ → List Bool → ℤ) (c : C), (∀ w < K, ∀ z ∈ words ((K - 1) * lam), |W w z| < 2 ^ B) →
  ServesInst ((askTable : QueryMachine TableQuery ℤ (C × IQ) ℤ).close (tables K lam W)) c lam B 1 (size c + size K + K * (2 * lam + 2) + B + 3) (listTables K W)

/-- The value of the clique as the network of Definition 3 is the sum over one string per edge for
the tables read as lists of strings (`listTables`). -/
def StCliqueValue : Prop := ∀ (K lam : ℕ) (W : ℕ → List Bool → ℤ), 2 ≤ K → 1 ≤ lam → (clique K lam fun w => W w.val).value = Paper.cliqueValue lam (listTables K W)

/-- Cutting a setting into its strings: the query (w, z) of Definition 3 becomes the query with the
strings z_w(w') used here; and concatenating them gives z back. -/
def StToLists : Prop := ∀ (K lam : ℕ) (w : Fin K), ∀ z ∈ words ((K - 1) * lam),
  toLists K lam (w.val, z) = (w.val, List.ofFn fun u : Fin K => if u = w then [] else copyAt lam w u z) ∧
  (∀ u : Fin K, u ≠ w → (copyAt lam w u z).length = lam) ∧ toTable (toLists K lam (w.val, z)) = (w.val, z)

end Printed
