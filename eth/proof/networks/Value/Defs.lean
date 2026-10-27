/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.ViaGrouping.Display

/-! # «… so the value equals Z», along the sentences of the paper (definitions and statements only)

Proof of Lemma 1, after the display of W̃_γ: the value of this clique is a sum over the settings of
its nodes γ; the two copies of the string on an edge {γ, γ'} must agree, and both W̃_γ and W̃_γ'
read θ_{a,b} from the same block of this string,
so θ_{a,b} = θ_{b,a}; the appended bits must be 0. Together with the sums inside the tables, this is
a sum over all z ∈ ∏_{a ∈ [g]} S_a and over one string θ_{a,b} ∈ {0,1}^{c_{a,b}} per pair {a,b} of
nodes in different groups. Each θ_{a,b} occurs only in f_{a,b} and f_{b,a}, and
Σ_{θ_{a,b}∈{0,1}^{c_{a,b}}} f_{a,b}(z_a, θ_{a,b}) f_{b,a}(z_b, θ_{a,b}) = Ψ_{a,b}(z_a, z_b), so the
value equals Z.
And after Definition 3: only the terms in which the two copies on every edge agree contribute, and
the value is the sum, over all choices of one string in {0,1}^λ per edge, of ∏_{w∈[K]} W_w evaluated
at the strings on the edges at w.

`Eight.ViaGrouping.stValue` (proof/networks/Eight/ViaGrouping/Table.lean) proves «the value equals
Z» by another route: each group is merged into one node (`Groundwork.Network.value_merge`), and the
merged network is compared with its tables (`Groundwork.Prog.NetE.ZW_merged`,
`Groundwork.Network.ZW_toInst`, `Paper.grouped_value`);
Here each sentence of the paper is a statement, and the end statements are proved from these and
from nothing else of that route. Most implications below are between closed propositions, so their
types do not force the route; no proof of this folder uses the theorems just named.
The objects are those of this development: the clique as a network (`Eight.SecNetworks.clique`), the
display of W̃_γ (`Eight.ViaGrouping.display`), the appended bits and θ_{a,b}
(`Eight.SecNetworks.appendedBits`, `thetaAt`), the grouping number x (`Paper.grouping`).
This file has no proofs. -/

@[expose] public section

namespace Value

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping

/-! ## The clique: two copies on every edge, and one string per edge (Definition 3 and the sentences after it) -/

/-! Tables whose argument gives, for every other node w', the string on the edge {w, w'}
(`Paper.Tables`) are read as the tables of Definition 3, whose argument is the setting z_w (one
string of (K − 1)λ bits, the concatenation of the K − 1 copies z_w(w')), by
`Eight.SecNetworks.tablesOn` (proof/networks/Eight/SecNetworks_Clique.lean). Every table on settings
is of this form. -/

/-- The choices of one string of λ bits per edge {w, w'}, w < w'. (A function on all pairs; the
empty string off the edges.) -/
def edgeStrings (K lam : ℕ) : Finset (Fin K × Fin K → List Bool) := tuples (fun p : Fin K × Fin K => p.1 < p.2) (fun _ => words lam) []

/-- In the choice z = (z_w) of one setting per node, the two copies of the string on every edge
agree. -/
def CopiesAgree {K : ℕ} (lam : ℕ) (z : Fin K → List Bool) : Prop := ∀ p ∈ pairs (Fin K), copyAt lam p.1 p.2 (z p.1) = copyAt lam p.2 p.1 (z p.2)

/-- The term of the choice z = (z_w) in the value of the (K, λ)-clique: ∏_w W_w(z_w) ∏_{{w,w'}}
[z_w(w') = z_{w'}(w)]. -/
def cliqueTerm {K : ℕ} (lam : ℕ) (W : Fin K → List Bool → ℤ) (z : Fin K → List Bool) : ℤ :=
  (∏ w, W w (z w)) * ∏ p ∈ pairs (Fin K), if copyAt lam p.1 p.2 (z p.1) = copyAt lam p.2 p.1 (z p.2) then 1 else 0

/-- «The value of this clique is by definition a sum over the settings of its nodes». -/
def StSumOverSettings : Prop := ∀ (K lam : ℕ) (W : Fin K → List Bool → ℤ),
  (clique K lam W).value = ∑ z ∈ Fintype.piFinset (fun _ : Fin K => words ((K - 1) * lam)), cliqueTerm lam W z

/-- «The two copies of the string on an edge must agree» / «only the terms in which the two copies
on every edge agree contribute»: every other term is 0, and in such a term the factors of the edges
are 1. -/
def StCopiesMustAgree : Prop := ∀ (K lam : ℕ) (W : Fin K → List Bool → ℤ) (z : Fin K → List Bool),
  (¬ CopiesAgree lam z → cliqueTerm lam W z = 0) ∧ (CopiesAgree lam z → cliqueTerm lam W z = ∏ w, W w (z w))

/-- The choices of settings in which all copies agree are the choices of one string per edge: each Λ
belongs to exactly one choice z of settings, the one with z_w(w') = Λ{w, w'} for all w ≠ w'; and
every z in which all copies agree belongs to some Λ. -/
def StOneStringPerEdge : Prop := ∀ (K lam : ℕ),
  (∀ Λ ∈ edgeStrings K lam, ∃! z : Fin K → List Bool, z ∈ Fintype.piFinset (fun _ : Fin K => words ((K - 1) * lam)) ∧ ∀ w w' : Fin K, w' ≠ w → copyAt lam w w' (z w) = star Λ w w') ∧
  ∀ z ∈ Fintype.piFinset (fun _ : Fin K => words ((K - 1) * lam)), CopiesAgree lam z → ∃ Λ ∈ edgeStrings K lam, ∀ w w' : Fin K, w' ≠ w → copyAt lam w w' (z w) = star Λ w w'

/-- «and the value is the sum, over all choices of one string in {0,1}^λ per edge, of ∏_{w∈[K]} W_w
evaluated at the strings on the edges at w» (after Definition 3). The right-hand side is
`Paper.cliqueValue lam W` written out. It holds for all K and λ (Definition 3 has K ≥ 2, λ ≥ 1). -/
def StCliqueValue : Prop := ∀ (K lam : ℕ) (W : Paper.Tables K),
  (clique K lam (tablesOn lam W)).value = ∑ Λ ∈ edgeStrings K lam, ∏ w, W w (star Λ w)

/-- The sentence after Definition 3, with what it rests on in its hypotheses. -/
def StCliqueValueOf : Prop := StSumOverSettings → StCopiesMustAgree → StOneStringPerEdge → StCliqueValue

/-! ## The clique of the groups -/

section Groups

variable {C : Type} [HasSize C] {g K : ℕ}

/-- «We define a (K, L)-clique whose nodes are the groups. By Definition 3 only its tables W̃_γ need
to be defined»: the network of Definition 3 with the display of W̃_γ as tables, for the grouping
number x. -/
def groupClique (Np : Procs C) (c : C) (N : Net g) (hK0 : 0 < K) (x L : ℕ) : Net K := clique K L (tablesOn L (display Np c N hK0 x))

/-- The pairs {a, b}, a < b, of nodes in different groups. -/
abbrev Across (χ : Fin g → Fin K) (p : Fin g × Fin g) : Prop := p.1 < p.2 ∧ χ p.1 ≠ χ p.2

/-- The choices of «one string θ_{a,b} ∈ {0,1}^{c_{a,b}} per pair {a,b} of nodes in different
groups». (A function on all pairs; the empty string elsewhere.) -/
def blockStrings (N : Net g) (χ : Fin g → Fin K) : Finset (Fin g × Fin g → List Bool) := tuples (Across χ) (fun p => words (N.c p.1 p.2)) []

/-- What the tables read from a choice Λ of one string per edge of the clique of the groups: for
each pair {a, b}, a < b, of nodes in different groups, the string θ_{a,b} that the table of a's
group cuts out of the string on the edge between the two groups. (The empty string at all other
pairs.) -/
def readBlocks (Np : Procs C) (c : C) (hK0 : 0 < K) (x : ℕ) (Λ : Fin K × Fin K → List Bool) : Fin g × Fin g → List Bool :=
  fun p => if Across (Paper.grouping hK0 x) p then thetaAt Np.toPaperNetwork c hK0 x (star Λ (Paper.grouping hK0 x p.1)) p.1 p.2 else []

/-- On every edge of the clique of the groups all appended bits of the string are 0. -/
def AppendedZero (g : ℕ) (Np : Procs C) (c : C) (x : ℕ) (Λ : Fin K × Fin K → List Bool) : Prop :=
  ∀ γ γ' : Fin K, γ' ≠ γ → ∀ bit ∈ appendedBits (g := g) Np.toPaperNetwork c x γ γ' (star Λ γ γ'), bit = false

/-- The term of (z, θ) in the joint sum: ∏_a W_a(z_a), times Ψ_{a,b}(z_a, z_b) for the pairs inside
a group, times f_{a,b}(z_a, θ_{a,b})·f_{b,a}(z_b, θ_{a,b}) for the pairs of nodes in different
groups. -/
def jointTerm (N : Net g) (χ : Fin g → Fin K) (z : Fin g → List Bool) (θ : Fin g × Fin g → List Bool) : ℤ :=
  (∏ a, N.W a (z a)) * (∏ p ∈ pairs (Fin g) with χ p.1 = χ p.2, N.Ψ p.1 p.2 (z p.1) (z p.2)) *
    ∏ p ∈ pairs (Fin g) with χ p.1 ≠ χ p.2, N.f p.1 p.2 (z p.1) (θ p) * N.f p.2 p.1 (z p.2) (θ p)

end Groups

/-- «For each pair of groups {γ, γ'} choose an order of the pairs {a, b} … In this order, the pair
{a, b} is assigned a block of c_{a,b} consecutive positions of {1, …, L}; the L − Y_{γ,γ'} positions
after the last block hold the appended bits»: the layout that `thetaAt` and `appendedBits` use. The
order is that of the list
`NetE.prs`: the pairs (a', b') with a' in the group with the smaller number, in increasing order of
a', then of b' (the paper: any order will do). The block of the pair number i begins after the
blocks of the pairs before it. The numbers c are those that the procedures give (`cap`). -/
def StLayout : Prop := ∀ (C : Type) [HasSize C] (g K : ℕ) (Np : Procs C) (c : C) (hK0 : 0 < K) (x : ℕ) (Θ : Fin K → List Bool) (a b : Fin g), Paper.grouping hK0 x a < Paper.grouping hK0 x b →
  (thetaAt Np.toPaperNetwork c hK0 x Θ a b =
      ((Θ (Paper.grouping hK0 x b)).drop (((lbLens K g Np.toPaperNetwork c x (Paper.grouping hK0 x a).val (Paper.grouping hK0 x b).val).take ((prs K g x (Paper.grouping hK0 x a).val (Paper.grouping hK0 x b).val).idxOf (a.val, b.val))).sum)).take (Np.cap c a.val b.val)) ∧
  (thetaAt Np.toPaperNetwork c hK0 x Θ b a =
      ((Θ (Paper.grouping hK0 x a)).drop (((lbLens K g Np.toPaperNetwork c x (Paper.grouping hK0 x a).val (Paper.grouping hK0 x b).val).take ((prs K g x (Paper.grouping hK0 x a).val (Paper.grouping hK0 x b).val).idxOf (a.val, b.val))).sum)).take (Np.cap c a.val b.val)) ∧
  ∀ θ : List Bool, appendedBits (g := g) Np.toPaperNetwork c x (Paper.grouping hK0 x a) (Paper.grouping hK0 x b) θ = θ.drop (lbLens K g Np.toPaperNetwork c x (Paper.grouping hK0 x a).val (Paper.grouping hK0 x b).val).sum

/-- «both W̃_γ and W̃_γ' read θ_{a,b} from the same block of this string, so θ_{a,b} = θ_{b,a}». (In
Lean the two copies on an edge have been made one string before, by `StCliqueValue`; the paper says
both in one sentence.) For one string per edge of the clique of the groups, and a, b in different
groups, θ_{a,b} as the table of a's group reads it is θ_{b,a} as the table of b's group reads it. -/
def StSameBlock : Prop := ∀ (C : Type) [HasSize C] (g K : ℕ) (Np : Procs C) (c : C) (hK0 : 0 < K) (x : ℕ) (Λ : Fin K × Fin K → List Bool) (a b : Fin g),
  Paper.grouping hK0 x a ≠ Paper.grouping hK0 x b →
    thetaAt Np.toPaperNetwork c hK0 x (star Λ (Paper.grouping hK0 x a)) a b = thetaAt Np.toPaperNetwork c hK0 x (star Λ (Paper.grouping hK0 x b)) b a

/-- «the appended bits must be 0»: if on some edge an appended bit of the string is 1, the product
of the tables is 0. -/
def StAppendedZero : Prop := ∀ (C : Type) [HasSize C] (g K : ℕ) (Np : Procs C) (c : C) (N : Net g) (hK0 : 0 < K) (x : ℕ) (Λ : Fin K × Fin K → List Bool),
  ¬ AppendedZero g Np c x Λ → ∏ γ, display Np c N hK0 x γ (star Λ γ) = 0

/-- The choices of one string of L bits per edge {γ, γ'} with all appended bits 0 are the choices of
one block of c_{a,b} bits per pair {a, b} of nodes in different groups: what the tables read from
such a Λ is a choice of blocks, and every choice θ of blocks is read from exactly one such Λ. -/
def StBlocks : Prop := ∀ (C : Type) [HasSize C] (g K : ℕ) (hK0 : 0 < K) (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
  ∀ x L : ℕ, (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) →
    (∀ Λ ∈ edgeStrings K L, AppendedZero g Np c x Λ → readBlocks Np c hK0 x Λ ∈ blockStrings N (Paper.grouping hK0 x)) ∧
    ∀ θ ∈ blockStrings N (Paper.grouping hK0 x), ∃! Λ : Fin K × Fin K → List Bool, Λ ∈ edgeStrings K L ∧ AppendedZero g Np c x Λ ∧ readBlocks Np c hK0 x Λ = θ

/-- «Together with the sums inside the tables»: a product over the groups of sums over the settings
of the nodes of the group is one sum over the settings of all nodes, because every node lies in
exactly one group. For an arbitrary grouping χ, arbitrary sets S_a and arbitrary functions F_γ. -/
def StSumsInside : Prop := ∀ (g K : ℕ) (χ : Fin g → Fin K) (S : Fin g → Finset (List Bool)) (F : Fin K → (Fin g → List Bool) → ℤ),
  ∏ γ, ∑ z ∈ tuples (fun a => χ a = γ) S [], F γ z = ∑ z ∈ Fintype.piFinset S, ∏ γ, F γ fun a => if χ a = γ then z a else []

/-- «Together with the sums inside the tables, this is a sum over all z ∈ ∏_{a ∈ [g]} S_a and over
one string θ_{a,b} ∈ {0,1}^{c_{a,b}} per pair {a,b} of nodes in different groups.» -/
def StJointSum : Prop := ∀ (C : Type) [HasSize C] (g K : ℕ) (hK0 : 0 < K) (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
  ∀ x L : ℕ, (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) →
    ∑ Λ ∈ edgeStrings K L, ∏ γ, display Np c N hK0 x γ (star Λ γ)
      = ∑ z ∈ Fintype.piFinset N.S, ∑ θ ∈ blockStrings N (Paper.grouping hK0 x), jointTerm N (Paper.grouping hK0 x) z θ

/-- «Each θ_{a,b} occurs only in f_{a,b} and f_{b,a}, and Σ_{θ_{a,b}∈{0,1}^{c_{a,b}}} f_{a,b}(z_a,
θ_{a,b}) f_{b,a}(z_b, θ_{a,b}) = Ψ_{a,b}(z_a, z_b)»: for every grouping χ and every z ∈ ∏ S_a, the
sum of the joint terms over θ is the term of z in the value Z of the network. -/
def StSumOut : Prop := ∀ (g K P B : ℕ) (N : Net g), N.Is P B → ∀ (χ : Fin g → Fin K), ∀ z ∈ Fintype.piFinset N.S,
  ∑ θ ∈ blockStrings N χ, jointTerm N χ z θ = (∏ a, N.W a (z a)) * ∏ p ∈ pairs (Fin g), N.Ψ p.1 p.2 (z p.1) (z p.2)

/-- **«… so the value equals Z»**, for the clique of the groups as the network of Definition 3 (two
copies of the string on every edge): its value is the value of the network N. -/
def StValueEqualsZ : Prop := ∀ (C : Type) [HasSize C] (g K : ℕ) (hK0 : 0 < K) (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
  ∀ x L : ℕ, (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) → (groupClique Np c N hK0 x L).value = N.value

/-- The joint sum, with what it rests on in its hypotheses. -/
def StJointSumOf : Prop := StSameBlock → StAppendedZero → StBlocks → StSumsInside → StJointSum

/-- «so the value equals Z», with the sentences before it in its hypotheses. -/
def StValueEqualsZOf : Prop := StCliqueValue → StJointSum → StSumOut → StValueEqualsZ

/-- The form in which the proof of Lemma 1 in proof/networks/Eight/ViaGrouping takes the step
(`Eight.ViaGrouping.StValue`: the value of the clique written with one string per edge, the tables
as `Paper.groupedTables`), from «so the value equals Z» for the clique as a network: back by the
sentence after Definition 3 (`StCliqueValue`), and by
`Eight.ViaGrouping.groupedTables_eq_display`, which says that the tables are given by the display of
W̃_γ (a fact on how the tables are defined, not on the value). So the proof of Lemma 1 runs through
the clique with two copies on every edge. -/
def StValueOf : Prop := StCliqueValue → StValueEqualsZ → Eight.ViaGrouping.StValue

end Value
