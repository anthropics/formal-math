/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import AppVariablesStatement
public import VariableBound.Field.Defs
public import PaddedDescent.F.Fuel

/-! # Step 2 of Appendix D as a program: the search for the checks

«Algorithm: start with the empty list; while X(𝓛) > 0, replace 𝓛 by the list (𝓛, Γ_u), u ∈ Ω, with
the smallest Υ; then output F(𝓛).» A check is a list of numbers of clauses, a list of checks a list
of such
lists. The program is generic in the function `evX` that returns X(𝓛) and in the list `fam` of the
candidates Γ_u; proof/variables/VariableBound/Count puts in the sums over the networks of Step 3 and
the family of Lemma 13.
«The number Υ is a rational with polynomially many bits, so the comparisons are exact»: all
candidates of one round have the same number of checks, so their Υ have a common denominator, and
the program compares the
numerators, which are integers (`upsNum`). The loop runs r̄ rounds and does nothing once X(𝓛) = 0.
The list is cut off by the pad after every round, so that the program is polynomial-time in the pad
with no side
condition; the cut-off does nothing if the pad is long enough.
This file has definitions only. The statements are propositions;
proof/variables/VariableBound/Search proves them. -/

@[expose] public section

namespace VariableBound

open Groundwork PaddedDescent.F AppVariables

/-- A list of checks, given by numbers of clauses, as a list of sets of clauses. -/
def chksD (m : ℕ) (L : List (List ℕ)) : List (Finset (Fin m)) := L.map (Fld.setD m)

/-- Σ_E 2^load(E). -/
def loadSum (m : ℕ) (L : List (List ℕ)) : ℕ := ((List.range m).map fun E => 2 ^ (L.filter fun l => l.contains E).length).sum

/-- The numerator of Υ(𝓛) over the denominator 3^r·2^(β−1)·2^t̄·(15n̄)^(r̄−r), for a list 𝓛 of r ≤
r̄ checks with X(𝓛) = x. -/
def upsNum (m nb β rb tb : ℕ) (x : ℤ) (L : List (List ℕ)) : ℤ :=
  4 ^ L.length * 2 ^ tb * (15 * nb) ^ (rb - L.length) * x + 3 ^ L.length * 2 ^ (β - 1) * (15 * nb + 16) ^ (rb - L.length) * loadSum m L

/-- The first member of the list with the smallest key; the default [] on the empty list. -/
def argminD (key : List ℕ → ℤ) (fam : List (List ℕ)) : List ℕ :=
  (fam.foldl (fun (best : Option (List ℕ × ℤ)) l => match best with
    | none => some (l, key l)
    | some b => if key l < b.2 then some (l, key l) else some b) none).elim [] fun b => b.1

/-- One round: nothing if X(𝓛) = 0; otherwise the candidate with the smallest Υ is appended. -/
def roundD (evX : List (List ℕ) → ℤ) (fam : List (List ℕ)) (m nb β rb tb : ℕ) (L : List (List ℕ)) : List (List ℕ) :=
  if evX L = 0 then L else L ++ [argminD (fun l => upsNum m nb β rb tb (evX (L ++ [l])) (L ++ [l])) fam]

/-- The search: r̄ rounds from the empty list. -/
def searchD (pad : U) (evX : List (List ℕ) → ℤ) (fam : List (List ℕ)) (m nb β rb tb : ℕ) : List (List ℕ) :=
  (List.range rb).foldl (fun L _ => cap pad [] (roundD evX fam m nb β rb tb L)) (cap pad [] [])

/-- The conditions of Step 2 of Appendix D on a list of checks, here given by numbers: r ≤ r̄
checks, each an increasing list of at most s̄ = 16m/n̄ numbers below m, and load(E) ≤ t̄ + 2 for
every clause E. -/
def StructD (m nb rb tb : ℕ) (L : List (List ℕ)) : Prop :=
  L.length ≤ rb ∧ (∀ l ∈ L, l.Pairwise (· < ·) ∧ (∀ E ∈ l, E < m) ∧ nb * l.length ≤ 16 * m) ∧ ∀ E < m, (L.filter fun l => l.contains E).length ≤ tb + 2

/-- The search is right. X has at most 2^n elements; β, r̄, t̄ are the parameters of «Setting and
parameters» in Appendix D, for m clauses and n̄ ≥ 1; the candidates are increasing lists of numbers
below m, the list of candidates is not empty, and
they have (a), (b), (c) of Lemma 13 for v = n̄; `evX` returns X(𝓛) on every list that satisfies
`StructD`; the word of every such list fits under the pad. Then the list found satisfies `StructD`
and X = 0. -/
def StSearchD : Prop := ∀ (X : Type) [Fintype X] (m : ℕ) (V : X → Finset (Fin m)) (n nb rb tb : ℕ) (pad : U) (evX : List (List ℕ) → ℤ) (fam : List (List ℕ)),
  Fintype.card X ≤ 2 ^ n → 1 ≤ nb → IsRb (beta n m nb) rb → IsTb m nb rb tb →
  fam ≠ [] → (∀ l ∈ fam, l.Pairwise (· < ·) ∧ ∀ E ∈ l, E < m) →
  IsFamily nb (Finset.univ : Finset (Fin fam.length)) (fun i => Fld.setD m (fam.get i)) →
  (∀ L, StructD m nb rb tb L → evX L = Xsum V nb (chksD m L)) → (∀ L, StructD m nb rb tb L → len L ≤ pad.length) →
  StructD m nb rb tb (searchD pad evX fam m nb (beta n m nb) rb tb) ∧ Xsum V nb (chksD m (searchD pad evX fam m nb (beta n m nb) rb tb)) = 0

/-- The search is polynomial-time in the pad, jointly in everything it reads, if `evX` is; m, n̄, β,
r̄, t̄ are given in unary. -/
def StCertSearchD : Prop := ∀ (α : Type) [Enc α] (pad : α → U) (evX : α → List (List ℕ) → ℤ) (fam : α → List (List ℕ)) (m nb β rb tb : α → ℕ),
  PolyT pad → (PolyT fun p : α × List (List ℕ) => evX p.1 p.2) → PolyT fam → Unary m → Unary nb → Unary β → Unary rb → Unary tb →
  PolyT fun x => searchD (pad x) (evX x) (fam x) (m x) (nb x) (β x) (rb x) (tb x)

end VariableBound
