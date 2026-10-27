/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.ViaGrouping.Defs
public import Eight.SecProof_NetworkDefs

/-! # Section 6, «Clusters, occurrences, equality tests»: the network of Φ as Definition 2 prints a network (definitions only)

The network of Φ in this development (`Paper.networkOf g Φ`, for clauses of at most k literals
`Groundwork.Prog.Count.wordNet g k Φ`) comes with procedures for W_a and f_{a,b} only
(`Groundwork.Prog.satP g k`). Definition 2(iii) also asks for the number P and
for a procedure that computes Ψ_{a,b}. This file adds them, in the words of the paper:
«Choose an order of these tests, and let z_a|_b ∈ {0,1}^{c_{a,b}} list the bits of z_a at their
occurrences in cluster a; likewise z_b|_a. Put Ψ_{a,b}(z_a, z_b) = [z_a|_b = z_b|_a]» (`restr`,
`satPsi`); «with P = 6m̄» (`satPf`).
The tests between two clusters, in their order, are the list `Groundwork.Prog.Count.links`.
Different from the paper, as in `Groundwork.Prog.Count.wordNet`: a setting has one bit for each
PLACE of a literal (k places per clause, so k·m̄ bits per cluster), not one for each
occurrence; the bit at a place without a literal must be 0. This file has no proofs. -/

@[expose] public section

namespace Eight.ViaGrouping

open Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks

/-- z_a|_b: the bits of the setting z of cluster a at its occurrences in the tests between the
clusters a and b, in the order of these tests. A test is a pair (place in the earlier cluster, place
in the later cluster). -/
def restr (g k : ℕ) (Φ : Fml) (a b : ℕ) (z : List Bool) : List Bool :=
  if a < b then (links g k Φ a b).map fun p => z.getD p.1 false else (links g k Φ b a).map fun p => z.getD p.2 false

/-- Ψ_{a,b}(z, z') = [z|_b = z'|_a], for the query q = ((a, b), (z, z')): 1 if every test between
the clusters a and b holds, else 0. -/
def satPsi (g k : ℕ) (Φ : Fml) (q : PsiQ) : ℤ := if restr g k Φ q.1.1 q.1.2 q.2.1 = restr g k Φ q.1.2 q.1.1 q.2.2 then 1 else 0

/-- The procedure for Ψ: one step, which computes `satPsi`. Its context is Φ itself. -/
def satPsiM (g k : ℕ) : Stepped (Fml × PsiQ) ℤ := Stepped.ofFun fun x => satPsi g k x.1 x.2

/-- P = 2k·m̄, for k = 3 the paper's P = 6m̄; at least 1, because Definition 2 asks for P ≥ 1 and m̄ =
0 if Φ has no clause. -/
def satPf (g k : ℕ) (Φ : Fml) : ℕ := max 1 (2 * k * mu g Φ)

/-- What an algorithm is given of the network of a formula with at most k literals per clause
(Definition 2(iii)): P, the lengths, and the four procedures. -/
def satProcs (g k : ℕ) : Procs Fml := ofProcs (satP g k) (satPf g k) (satPsiM g k)

/-- The network of Φ on g clusters, for clauses of at most k literals, as the data of Definition 2. -/
def satNet (g k : ℕ) (Φ : Fml) : Net g := ofNetwork (wordNet g k Φ) fun _ => mu g Φ * k

end Eight.ViaGrouping
