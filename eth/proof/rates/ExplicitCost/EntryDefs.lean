/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.Programs

/-! # One entry of W̃_γ, with K and g as data

Definitions and statements only; nothing is proved here.

**Why.** Lemma 8 (grouping with explicit cost) says that the value of a network is computed «within
(K^g + 𝒯·2^{2gP/K}τ)(g(P+B))^{C₁} operations, by one procedure, the same for all K, g, ζ and all
networks», and Appendix A says: «all costs are
counted again, because poly(·) there hides constants that depend on K and e»; C₁ is an absolute
constant. Its proof: «an entry is a sum of at most 2^{2gP/K} terms, each a product of at most g²
values. Testing a grouping, finding the blocks in an argument Θ … and
the arithmetic for one term … take time polynomial in g(P+B)». For Lemma 1 of the main text the
machine `Printed.tableQ K g` computes an entry; there K and g are parameters of the Lean definition,
so there is one machine, one constant and one certificate for each
K and g (`Printed.StEntryCost`: «The constant depends on K and g only»). Here the same machine reads
K and g from its input, in unary.

**What is here.** `entryData`: built like `Printed.tableQ`, from the same plain functions
(proof/machines/StepMachines/Prog/NetProg.lean, proof/networks/Eight/ViaGrouping/Defs.lean), each
called with the K and g of the input. `EntryCostExplicit`: the cost of an entry with ONE constant
for all K, g
and all networks. `EntryPoly`: ONE certificate of polynomial-time steps. `EntrySameRuns`: for each K
and g the machine runs as `Printed.tableQ K g` does. -/

@[expose] public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed

/-- The input: (K, g) in unary, and the input of Definition 2(iii) (P, B and the numbers P_a,
c_{a,b}, in unary). -/
abbrev DataInput : Type := (List Unit × List Unit) × NetInput

/-- Definition 2(iii) read by the machine: the numbers are read off the input, and each of the four
procedures is one query. As `Printed.asked`, with K and g beside the input. -/
def askedData : ProcsQ NetQuery ℤ DataInput where
  P c := asked.P c.2
  B c := asked.B c.2
  len c := asked.len c.2
  cap c := asked.cap c.2
  mem := QueryMachine.mapOut (QueryMachine.query fun x => Sum.inl x.2) fun v => decide (v ≠ 0)
  W := QueryMachine.query fun x => Sum.inr (Sum.inl x.2)
  Ψ := QueryMachine.query fun x => Sum.inr (Sum.inr (Sum.inl x.2))
  f := QueryMachine.query fun x => Sum.inr (Sum.inr (Sum.inr x.2))

/-- The K of the input. -/
def kOf (u : X0 DataInput) : ℕ := u.1.1.1.1.length

/-- The g of the input. -/
def gOf (u : X0 DataInput) : ℕ := u.1.1.1.2.length

/-- [z_a ∈ S_a]·W_a(z_a). -/
def wData : QueryMachine NetQuery ℤ ((X0 DataInput × ℕ) × ℕ) ℤ :=
  QueryMachine.gated (QueryMachine.mapIn (fun u : (X0 DataInput × ℕ) × ℕ => qW (kOf u.1.1) (gOf u.1.1) askedData.under.toPaperNetwork u) askedData.mem)
    (QueryMachine.mapIn (fun u : (X0 DataInput × ℕ) × ℕ => qW (kOf u.1.1) (gOf u.1.1) askedData.under.toPaperNetwork u) askedData.W)

/-- [z_a ∈ S_a][z_b ∈ S_b]·Ψ_{a,b}(z_a, z_b). -/
def psiData : QueryMachine NetQuery ℤ ((X0 DataInput × ℕ) × ℕ) ℤ :=
  QueryMachine.gated (QueryMachine.mapIn (fun u : (X0 DataInput × ℕ) × ℕ => qW (kOf u.1.1) (gOf u.1.1) askedData.under.toPaperNetwork u) askedData.mem)
    (QueryMachine.gated (QueryMachine.mapIn (fun u : (X0 DataInput × ℕ) × ℕ => qMb (kOf u.1.1) (gOf u.1.1) askedData.under u) askedData.mem)
      (QueryMachine.mapIn (fun u : (X0 DataInput × ℕ) × ℕ => qPsi (kOf u.1.1) (gOf u.1.1) askedData.under u) askedData.Ψ))

/-- [z_a ∈ S_a]·f_{a,b}(z_a, θ_{a,b}). -/
def fData : QueryMachine NetQuery ℤ ((X0 DataInput × ℕ) × ℕ) ℤ :=
  QueryMachine.gated (QueryMachine.mapIn (fun u : (X0 DataInput × ℕ) × ℕ => qW (kOf u.1.1) (gOf u.1.1) askedData.under.toPaperNetwork u) askedData.mem)
    (QueryMachine.mapIn (fun u : (X0 DataInput × ℕ) × ℕ => qF (kOf u.1.1) (gOf u.1.1) askedData.under.toPaperNetwork u) askedData.f)

/-- The factor number i = a·g + b of a term of W̃_γ(Θ), as `Printed.termQ`. -/
def termData : QueryMachine NetQuery ℤ ((X0 DataInput × ℕ) × ℕ) ℤ :=
  QueryMachine.ite (fun u : (X0 DataInput × ℕ) × ℕ => isOne (kOf u.1.1) (gOf u.1.1) u) (QueryMachine.const 1)
    (QueryMachine.ite (fun u : (X0 DataInput × ℕ) × ℕ => isW (gOf u.1.1) u) wData (QueryMachine.ite (fun u : (X0 DataInput × ℕ) × ℕ => isPsi (kOf u.1.1) (gOf u.1.1) u) psiData fData))

/-- **One entry W̃_γ(Θ)**, K and g read from the input: 0 unless all appended bits are 0; else the
sum, over all strings of Σ_{a ∈ G_γ} P_a bits, of the product of the g² factors. -/
def entryData : QueryMachine NetQuery ℤ (X0 DataInput) ℤ :=
  QueryMachine.ite (fun u : X0 DataInput => validB (kOf u) (gOf u) askedData.under.toPaperNetwork u)
    (QueryMachine.sumRange (fun u : X0 DataInput => nStates (kOf u) (gOf u) askedData.under.toPaperNetwork u) (QueryMachine.prodRange (fun v : X0 DataInput × ℕ => nPairs (gOf v.1) v) termData)) (QueryMachine.const 0)

/-- The input for K, g and the network N with the parameters P, B. -/
def dataInput (K : ℕ) {g : ℕ} (N : Net g) (P B : ℕ) : DataInput := ((unary K, unary g), netInput N P B)

/-- **The cost of an entry, with one constant.** There is ONE number c₁ such that for all 1 ≤ K ≤ g,
every network N on [g] with parameters P, B, every price τ ≥ 1 of a query of Definition 2(iii),
every grouping number x < K^g with at most 2g/K nodes in every
group and Y_{γ,γ'} ≤ L ≤ 2gP: the machine `entryData`, asked for the entry (γ, Θ) of the tables W̃
of the (K, L)-clique of the groups, returns it within 2^{P·⌊2g/K⌋}·τ·(g(P+B))^{c₁} operations, on
states of size at most (g(P+B))^{c₁}; and the entry is below 2^{B'} in absolute value, B' = ⌈2gP/K⌉ +
g²B («As shown there, |W̃_γ| < 2^{B'}»). The proof of Lemma 8 has L ≤ gP + 1;
L ≤ 2gP is weaker (P ≥ 1) and is what `Printed.StEntryCost` asks. -/
def EntryCostExplicit : Prop := ∃ c₁ : ℕ, ∀ (K g : ℕ) (hK0 : 0 < K) (N : Net g) (P B τ : ℕ), K ≤ g → N.Is P B → 1 ≤ τ →
  ∀ x < K ^ g, ∀ L ≤ 2 * (g * P), (∀ γ : Fin K, K * #{a : Fin g | Paper.grouping hK0 x a = γ} ≤ 2 * g) → (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) →
    ∀ (γ : Fin K), ∀ Θ ∈ words ((K - 1) * L),
      entryData.Within (netOracle N) (fun _ => τ) ((dataInput K N P B, x), toLists K L (γ.val, Θ)) (2 ^ (P * (2 * g / K)) * τ * (g * (P + B)) ^ c₁) ((g * (P + B)) ^ c₁)
        ((Value.groupClique asked.under (netInput N P B) N hK0 x L).W γ Θ) ∧
      |(Value.groupClique asked.under (netInput N P B) N hK0 x L).W γ Θ| < 2 ^ bitsOut K g P B

/-- **One certificate**: the machine has polynomial-time steps. (The plain functions inside are
polynomial-time jointly in K and g: proof/rates/PaddedDescent/F/CertNet.lean.) -/
def EntryPoly : Prop := entryData.PolyTimeSteps

/-- For each K and g the machine runs as `Printed.tableQ K g` does: the same result, own steps and
queries. A state holds the input in up to four places (the two loops, the test before a factor, the
pending query), so the states are larger by at most four copies of K and g in unary. -/
def EntrySameRuns : Prop := ∀ (K g : ℕ) (O : NetQuery → Option ℤ) (c : NetInput) (x : ℕ) (q : IQ) (own S : ℕ) (L : List NetQuery) (b : ℤ),
  (tableQ K g asked).Runs O ((c, x), q) own L S b → entryData.Runs O ((((unary K, unary g), c), x), q) own L (S + 4 * (2 * K + 2 * g + 2)) b

end ExplicitCost
