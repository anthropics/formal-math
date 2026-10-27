/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.ViaGrouping.SatPsiDefs
public import Eight.SecProof_NetworkDefs
public import ThmEveryDeltaStatement

/-! # The printed objects, and Lean's as these with padding (definitions and statements only)

Section 6: «A setting z_a of node a is a bit string with one bit z_a[o] for each occurrence o in
cluster a, and S_a is the set of all these bit strings.» In the network on which the machines run
(`Eight.ViaGrouping.satNet`, on `Groundwork.Prog.Count.wordNet`) a setting has one bit for each
PLACE of a literal, 3 places per clause and m̄ clauses per cluster, and
W_a has one condition more: the bit at a place without a literal is 0. And: «a clause is a nonempty
set of literals, and a 3-CNF is a finite set of clauses with at most 3 literals each», where Lean's
end statement has lists (`Sat3.CNF`, `Sat3.Is3CNF`).
This file defines the printed objects in the words of the paper, without reference to Lean's, and
states that Lean's are these up to padding:
* `PaddingOf N₀ N pad`: the network N is the network N₀ with each setting z of a node a written as
  the string pad a z; on the settings of N that write no setting of N₀, W is 0; W, Ψ, f and the
  numbers c_{a,b} are carried over. Then both have the same value and the same total
  (`StPaddingValue`).
* `occNet g Φ`: the network of Φ with one bit per occurrence; `StOccNet`: `satNet g 3 Φ` is
  `occNet g Φ` with padding; `StOccNetCounts`: so its value is the number of satisfying assignments
  of the variables that occur.
* `ThreeCNF n`: a 3-CNF as a set of sets; `StSetForm`: Theorem 2 for these, whichever way the set is
  written as a list.
No proof of the main theorems uses this file: their machines run on the padded network.
Three choices that the paper leaves open are fixed here as in Lean's network: the clusters are
blocks of m̄ consecutive clauses; the occurrences of a variable are listed in reading order (by
clause, then by position in the clause); the tests between two clusters are listed in reading order
of their earlier occurrence.
(proof/networks/Eight/SecProof_NetworkDefs.lean has another definition called tests, a set of pairs
of places; `Coding.tests` is a list of pairs of occurrences.)
This file has no proofs. -/

@[expose] public section

namespace Coding

open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping

/-! ## Padding -/

/-- The network N is the network N₀ with padded settings. -/
structure PaddingOf {g : ℕ} (N₀ N : Net g) (pad : Fin g → List Bool → List Bool) : Prop where
  /-- a setting of N₀ is written by a setting of N, and different settings by different ones -/
  maps : ∀ a, ∀ z ∈ N₀.S a, pad a z ∈ N.S a
  inj : ∀ a, ∀ z ∈ N₀.S a, ∀ z' ∈ N₀.S a, pad a z = pad a z' → z = z'
  /-- a setting of N that writes no setting of N₀ has W = 0 -/
  off : ∀ a, ∀ y ∈ N.S a, (∀ z ∈ N₀.S a, pad a z ≠ y) → N.W a y = 0
  W : ∀ a, ∀ z ∈ N₀.S a, N.W a (pad a z) = N₀.W a z
  Ψ : ∀ a b, a ≠ b → ∀ z ∈ N₀.S a, ∀ z' ∈ N₀.S b, N.Ψ a b (pad a z) (pad b z') = N₀.Ψ a b z z'
  c : ∀ a b, a ≠ b → N.c a b = N₀.c a b
  f : ∀ a b, a ≠ b → ∀ z ∈ N₀.S a, ∀ θ ∈ words (N₀.c a b), N.f a b (pad a z) θ = N₀.f a b z θ

/-- Padding changes neither the value nor the total. -/
def StPaddingValue : Prop := ∀ (g : ℕ) (N₀ N : Net g) (pad : Fin g → List Bool → List Bool), PaddingOf N₀ N pad → N.value = N₀.value ∧ N.U = N₀.U

/-! ## The network of Φ, one bit per occurrence -/

section Occurrences

variable (g : ℕ) (Φ : Fml)

/-- «An occurrence is a pair o = (E, ω) of a clause E ∈ Φ and a literal ω ∈ E, that is, one position
of one clause»: (number of the clause, position in the clause). For a clause that lists no literal
twice, positions and literals correspond; a clause of a list that repeats a literal has two
occurrences of it, which the paper's sets never have. All occurrences in the clauses number e₀, …,
e₀ + r − 1, in reading order. -/
def occIn (e₀ r : ℕ) : List (ℕ × ℕ) := (List.range' e₀ r).flatMap fun e => (List.range (Φ.getD e []).length).map fun j => (e, j)

/-- The occurrences in cluster a: the cluster holds the clauses number a·m̄, …, a·m̄ + m̄ − 1 (those
that exist), m̄ = ⌈m/g⌉. -/
def occOf (a : ℕ) : List (ℕ × ℕ) := occIn Φ (a * mu g Φ) (mu g Φ)

/-- All occurrences in Φ. -/
def occAll : List (ℕ × ℕ) := occIn Φ 0 Φ.length

/-- The literal at an occurrence. -/
def litOf (o : ℕ × ℕ) : ℕ × Bool := (Φ.getD o.1 []).getD o.2 (0, false)

/-- The cluster in which an occurrence lies. -/
def clusterOf (o : ℕ × ℕ) : ℕ := o.1 / mu g Φ

/-- «For each variable, list all its occurrences in Φ, across all clusters, in some order o₁, …, o_d
(any order will do); the pairs {o₁,o₂}, {o₂,o₃}, … of consecutive occurrences are the equality
tests»: (o, o') is a test if o' is the next occurrence of the variable of o in reading order. All
tests, in reading order of (o, o'). -/
def tests : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (occAll Φ ×ˢ occAll Φ).filter fun p =>
    decide ((occAll Φ).idxOf p.1 < (occAll Φ).idxOf p.2) && decide ((litOf Φ p.1).1 = (litOf Φ p.2).1) &&
      (occAll Φ).all fun o => !(decide ((occAll Φ).idxOf p.1 < (occAll Φ).idxOf o) && decide ((occAll Φ).idxOf o < (occAll Φ).idxOf p.2) && decide ((litOf Φ o).1 = (litOf Φ p.1).1))

/-- The tests with one occurrence in cluster a and the other in cluster b, in their order. For a =
b: the tests with both occurrences in cluster a. -/
def testsBetween (a b : ℕ) : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (tests Φ).filter fun p => (clusterOf g Φ p.1 == a && clusterOf g Φ p.2 == b) || (clusterOf g Φ p.1 == b && clusterOf g Φ p.2 == a)

/-- z_a[o]: the bit of the setting z of cluster a at the occurrence o. -/
def bitAt (a : ℕ) (z : List Bool) (o : ℕ × ℕ) : Bool := z.getD ((occOf g Φ a).idxOf o) false

/-- «call o = (E, ω) true if ω is positive and z_a[o] = 1, or ω is negative and z_a[o] = 0». -/
def isTrue (a : ℕ) (z : List Bool) (o : ℕ × ℕ) : Bool := bitAt g Φ a z o == (litOf Φ o).2

/-- z_a|_b: «the bits of z_a at their occurrences in cluster a», for the tests between the clusters
a and b, in the order of these tests. -/
def restrict (a b : ℕ) (z : List Bool) : List Bool := (testsBetween g Φ a b).map fun p => bitAt g Φ a z (if clusterOf g Φ p.1 = a then p.1 else p.2)

/-- **The network of Φ** on [g], as printed: a setting of node a has one bit for each occurrence in
cluster a, and S_a is the set of all these strings; W_a is 1 exactly if every clause of cluster a
has a true occurrence and z_a[o] = z_a[o'] for every test with both occurrences in cluster a;
c_{a,b} is the number of tests between the clusters a and b;
Ψ_{a,b}(z_a, z_b) = [z_a|_b = z_b|_a], f_{a,b}(z_a, θ) = [z_a|_b = θ]. -/
def occNet : Net g where
  len a := (occOf g Φ a.val).length
  S a := words (occOf g Φ a.val).length
  W a z := if ((List.range' (a.val * mu g Φ) (mu g Φ)).all fun e => !(decide (e < Φ.length)) || (List.range (Φ.getD e []).length).any fun j => isTrue g Φ a.val z (e, j)) &&
      ((testsBetween g Φ a.val a.val).all fun p => bitAt g Φ a.val z p.1 == bitAt g Φ a.val z p.2) then 1 else 0
  Ψ a b z z' := if restrict g Φ a.val b.val z = restrict g Φ b.val a.val z' then 1 else 0
  c a b := (testsBetween g Φ a.val b.val).length
  f a b z θ := if restrict g Φ a.val b.val z = θ then 1 else 0

/-- The padding: the string of 3·m̄ bits with the bit z_a[o] at the place of the occurrence o =
(a·m̄ + r, j), which is place 3r + j, and 0 at the places without a literal. -/
def padOcc (a : Fin g) (z : List Bool) : List Bool :=
  (List.range (mu g Φ * 3)).map fun i => decide (i % 3 < (Φ.getD (a.val * mu g Φ + i / 3) []).length) && bitAt g Φ a.val z (a.val * mu g Φ + i / 3, i % 3)

end Occurrences

/-- **Lean's network of Φ is the printed one with padding**, for g ≥ 1 clusters and clauses of at
most 3 literals. -/
def StOccNet : Prop := ∀ (g : ℕ) (Φ : Fml), 0 < g → (∀ C ∈ Φ, C.length ≤ 3) → PaddingOf (occNet g Φ) (satNet g 3 Φ) (padOcc g Φ)

/-- «The network of Φ is the following network on [g] with P = 6m̄ and B = 1 … Definition 2 holds:
Σ_{b ≠ a} c_{a,b} ≤ 2·3m̄ = P»: the printed network satisfies Definition 2 (all but (iii)) with the
printed parameters, for m ≥ 1. -/
def StOccNetIs : Prop := ∀ (g : ℕ) (Φ : Fml), 0 < g → Φ ≠ [] → (∀ C ∈ Φ, C.length ≤ 3) → (occNet g Φ).Is (6 * mu g Φ) 1

/-- «Their length is at most 3m̄ ≤ P» and «all values are 0 or 1». -/
def StOccNetSmall : Prop := ∀ (g : ℕ) (Φ : Fml), (∀ C ∈ Φ, C.length ≤ 3) →
  (∀ a : Fin g, (occNet g Φ).len a ≤ 3 * mu g Φ) ∧ (∀ (a : Fin g) z, (occNet g Φ).W a z = 0 ∨ (occNet g Φ).W a z = 1) ∧
  (∀ (a b : Fin g) z z', (occNet g Φ).Ψ a b z z' = 0 ∨ (occNet g Φ).Ψ a b z z' = 1) ∧ ∀ (a b : Fin g) z θ, (occNet g Φ).f a b z θ = 0 ∨ (occNet g Φ).f a b z θ = 1

/-- **«Hence Z is the number of assignments of the variables occurring in Φ **«Hence Z is the number
of assignments of the variables occurring in Φ that satisfy Φ»**, and so Φ is satisfiable if and
only if Z &gt; 0, for the printed network. if and only if Z > 0**, for the printed network. -/
def StOccNetCounts : Prop := ∀ (g : ℕ) (Φ : Fml), 0 < g → (∀ C ∈ Φ, C.length ≤ 3) → (occNet g Φ).value = (Eight.numSat Φ : ℤ) ∧ (0 < (occNet g Φ).value ↔ Φ.Sat)

/-- The count for the printed network is carried over from Lean's network, for which this
development proves it along the printed sentences («Every term of the value Z is 0 or 1. Each test
is checked exactly once … so a term is 1 exactly if all occurrences of each variable carry the same
bit and every clause has a true occurrence»: `Eight.network_value_eq`,
proof/networks/Eight/SecProof_Network.lean): padding does not change the value. These sentences are
not proved a second time for the printed network. -/
def StOccNetCountsOf : Prop := StOccNet → StPaddingValue → StOccNetCounts

/-- «An occurrence lies in at most two tests. The total number of tests is the number of occurrences
minus the number of variables that occur, hence at most 3m − 1» (m ≥ 1, nonempty clauses of at most
3 literals). -/
def StTests : Prop := ∀ Φ : Fml, Φ ≠ [] → (∀ C ∈ Φ, C ≠ [] ∧ C.length ≤ 3) →
  (∀ o ∈ occAll Φ, ((tests Φ).filter fun p => p.1 == o || p.2 == o).length ≤ 2) ∧
  (tests Φ).length + ((occAll Φ).map fun o => (litOf Φ o).1).toFinset.card = (occAll Φ).length ∧ (tests Φ).length ≤ 3 * Φ.length - 1

/-- Three clauses on three variables, each variable in all three clauses; with g = 3 every cluster
is one clause (m̄ = 1), and each of the three occurrences in the middle clause lies in two tests,
one to each of the other clusters. -/
def sixExample : Fml := [[(0, true), (1, true), (2, true)], [(0, false), (1, true), (2, true)], [(0, true), (1, false), (2, true)]]

/-- The footnote to «Their length is at most 3m̄ ≤ P»: «P is taken as large as 6m̄ because Σ_{b ≠ a}
c_{a,b} can reach 6m̄». An example in which it does, in the printed network and in Lean's. -/
def StRowSumReached : Prop := mu 3 sixExample = 1 ∧ ∑ b ∈ univ.erase (1 : Fin 3), (occNet 3 sixExample).c 1 b = 6 * mu 3 sixExample ∧
  ∑ b ∈ univ.erase (1 : Fin 3), (satNet 3 3 sixExample).c 1 b = 6 * mu 3 sixExample

/-! ## Sets for lists -/

/-- «a clause is a nonempty set of literals, and a 3-CNF is a finite set of clauses with at most 3
literals each», on the variables x₀, …, xₙ₋₁. A literal is a variable with the value that makes it
true (`Sat3.Lit`). -/
structure ThreeCNF (n : ℕ) where
  clauses : Finset (Finset (Sat3.Lit n))
  nonempty : ∀ E ∈ clauses, E.Nonempty
  width : ∀ E ∈ clauses, E.card ≤ 3

/-- Some assignment makes a literal of every clause true. -/
def ThreeCNF.Satisfiable {n : ℕ} (Φ : ThreeCNF n) : Prop := ∃ a : Fin n → Bool, ∀ E ∈ Φ.clauses, ∃ l ∈ E, a l.1 = l.2

/-- The list of lists φ writes the set of sets Φ: every clause of Φ is written exactly once, in some
order of the clauses, with its literals in some order, each once. -/
def Writes {n : ℕ} (φ : Sat3.CNF n) (Φ : ThreeCNF n) : Prop := (∀ C ∈ φ, C.Nodup) ∧ (φ.map List.toFinset).Nodup ∧ (φ.map List.toFinset).toFinset = Φ.clauses

/-- Every 3-CNF can be written; and whatever writes it is an instance in the sense of the end
statement, has as many clauses, has no empty clause, and is satisfiable exactly if the 3-CNF is. -/
def StWrites : Prop := ∀ (n : ℕ) (Φ : ThreeCNF n), (∃ φ, Writes φ Φ) ∧
  ∀ φ, Writes φ Φ → Sat3.Is3CNF φ ∧ φ.length = Φ.clauses.card ∧ [] ∉ φ ∧ (Sat3.Satisfiable φ ↔ Φ.Satisfiable)

/-- **Theorem 2 in its decision form for 3-CNFs as sets**: for every δ > 0 there are one machine and
one constant such that for every 3-CNF Φ on n variables, in whichever way it is written on the tape,
the machine halts after at most c·2^{δn} steps and outputs whether Φ is satisfiable. -/
def StSetForm : Prop := ∀ δ : ℝ, 0 < δ → ∃ (M : Turing.TM2ComputableAux Bool Bool) (c : ℕ), (∀ k, Finite (M.tm.Γ k)) ∧
  ∀ (n : ℕ) (Φ : ThreeCNF n) (φ : Sat3.CNF n), Writes φ Φ → ∃ (b : Bool) (t : ℕ), (b = true ↔ Φ.Satisfiable) ∧ (t : ℝ) ≤ c * (2 : ℝ) ^ (δ * n) ∧ Sat3.HaltsWith M φ b t

/-- It follows from Theorem 2 for lists. -/
def StSetFormOf : Prop := StWrites → Sat3.ThmEveryDelta → StSetForm

/-- Section 3, Conventions: «a 3-CNF is a set of clauses (Section 6), so m = O(n³)»: a 3-CNF on n
variables has at most 14n³ clauses. -/
def StCubic : Prop := ∀ (n : ℕ) (Φ : ThreeCNF n), Φ.clauses.card ≤ 14 * n ^ 3

end Coding
