/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ExplicitCost.EntryDefs
public import AppRunningTimeStatement

/-! # The lemma on groupings with explicit cost (Lemma 8), on counted operations

Definitions and statements only; nothing is proved here.

**The text.** «Let K, g ≥ 2 be integers and 0 < ζ ≤ 1. Take a network on [g] with parameters P, B, τ
and total U, and assume that (i) g = 3K⁸ and ζ = 1/(2K), or (ii) K divides g, c_{a,b} ≤ P/g for all
a ≠ b, and 2ζ²g ≥ K·ln(2gK). Put L = ⌈(U + 2ζgP)/K²⌉ and B' = ⌈2gP/K⌉ + g²B. If an algorithm outputs
the value of every
(K, L)-clique with |W_w| < 2^{B'} within 𝒯 operations, then the value of the network is computed
within (K^g + 𝒯·2^{2gP/K}τ)(g(P+B))^{C₁} operations, by one procedure, the same for all K, g, ζ and
all networks, which calls that algorithm.» Its proof: «The algorithm is that of Lemma 1: find the
first such grouping among all
K^g, define the (K, L)-clique with the tables W̃_γ, whose value is that of the network, run the
given algorithm on it, and answer each query by computing the entry.»

**What is here.**
* `GroupingInput`: what the procedure is given: ζ as a fraction, K and g in unary, and the input of
  Definition 2(iii).
* `labelLength`, `bitsOut`: L and B', computed from the input. `goodData`: «at most 2g/K nodes in
  every group and Y_{γ,γ'} ≤ L for all γ ≠ γ'». `searchData`: «find the first such grouping among
  all K^g».
* `groupingCall`: the procedure up to the point where it «calls that algorithm»: the search, and
  then ONE query, the call, which asks for the value of the (K, L)-clique of the groups of the
  grouping x that the search has found (its entries are below 2^{B'}). `GroupingWithCall`: with the
  call answered rightly, at any price, it returns the value of the network.
* `groupingData E arg`: the whole procedure, made from ANY machine E for cliques: `groupingCall`,
  with the call answered by E on `arg (K, L, B')`, each of whose queries is answered by `entryData`
  (`QueryMachines.QueryMachine.subst`, twice).
* `GroupingExplicit`: the lemma for this procedure, with ONE constant C₁. `GroupingPoly`: it has
  polynomial-time steps if E has. The steps of the proof, each as a statement: `LabelLengthIsL`,
  `SearchFinds`, `SearchCost`, `ValueIsKept`, `EntryCostExplicit` (EntryDefs.lean), `SizesStmt`,
  `GroupingWithCall`.

**Where this differs from the text.** (1) An operation is a step of a machine with query access, and
every statement carries a bound on the sizes of the states; here it is polynomial in g(P+B) and the
length of ζ, plus what E needs. (2) The hypothesis on E therefore names a bound S_E on the sizes of
ITS states, which the
text lacks. It restricts nothing: S_E is arbitrary, and there are only finitely many tables for
given K, L, B', so every machine that is right on all of them has such a bound; it only enters the
bound on the states of the procedure. (3) ζ is a fraction a/b of natural numbers, part of the input;
in both uses of the lemma ζ is such a fraction (1/(2K), 2^{−ℓ−5}). (4) K, g, P, B, the P_a and
c_{a,b} are given in unary. (5) E is handed K besides L and B' (through `arg`, which may drop it or
put a level in its place). -/

@[expose] public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed

/-- What the procedure is given: ζ = a/b as the pair (a, b), and (K, g) in unary with the input of
Definition 2(iii). -/
abbrev GroupingInput : Type := (ℕ × ℕ) × DataInput

/-- The K of the input. -/
def inK (c : GroupingInput) : ℕ := c.2.1.1.length
/-- The g of the input. -/
def inG (c : GroupingInput) : ℕ := c.2.1.2.length
/-- The P of the input. -/
def inP (c : GroupingInput) : ℕ := askedData.P c.2
/-- The B of the input. -/
def inB (c : GroupingInput) : ℕ := askedData.B c.2
/-- The total U, the sum of the numbers c_{a,b} of the input over the ordered pairs a ≠ b. -/
def inU (c : GroupingInput) : ℕ := Uc (inG c) askedData.under.toPaperNetwork c.2

/-- «L = ⌈(U + 2ζgP)/K²⌉», for ζ = a/b: ⌈(bU + 2agP)/(bK²)⌉. The lemma has ζ ≤ 1; the procedure
reads min(a, b) for a, so that on EVERY input, also one with a > b, the number is at most U + 2gP +
1 and can be written in unary in polynomial time. -/
def labelLength (c : GroupingInput) : ℕ := (c.1.2 * inU c + 2 * min c.1.1 c.1.2 * inG c * inP c + c.1.2 * inK c ^ 2 - 1) / (c.1.2 * inK c ^ 2)

/-- «at most 2g/K nodes in every group and Y_{γ,γ'} ≤ L for all γ ≠ γ'», for the grouping number x. -/
def goodData (cx : GroupingInput × ℕ) : Bool :=
  ((List.range (inK cx.1)).all fun G => decide (inK cx.1 * (members (inK cx.1) (inG cx.1) cx.2 G).length ≤ 2 * inG cx.1)) &&
  (List.range (inK cx.1)).all fun G => (List.range (inK cx.1)).all fun G' =>
    G == G' || decide (lbLen (inK cx.1) (inG cx.1) askedData.under.toPaperNetwork cx.1.2 cx.2 G G' ≤ labelLength cx.1)

/-- «find the first such grouping among all K^g». The loop halts at the first one. It reads only the
numbers of the input and asks nothing. -/
def searchData : Stepped GroupingInput (Option ℕ) := Exits.firstUntil (fun c => inK c ^ inG c) (Stepped.ofFun goodData) id

/-- What a machine for cliques is given: K, λ, B in unary. -/
abbrev CliqueInput : Type := List Unit × List Unit × List Unit

/-- The call: the number x of the grouping, and (K, L, B'). It asks for the value of the (K,
L)-clique of the groups of x. -/
abbrev CliqueCall : Type := ℕ × CliqueInput

/-- The call that the procedure makes on the input c when the search has found x. -/
def callOf (cx : GroupingInput × ℕ) : CliqueCall := (cx.2, (unary (inK cx.1), unary (labelLength cx.1), unary (bitsOut (inK cx.1) (inG cx.1) (inP cx.1) (inB cx.1))))

/-- **The procedure of the lemma, up to the call**: the search; then one query, the call, whose
answer is the result. The result is 0 if no grouping is good (which does not happen in cases (i) and
(ii)). -/
def groupingCall : QueryMachine CliqueCall ℤ GroupingInput ℤ := QueryMachine.optBind (QueryMachine.lift searchData) (QueryMachine.query callOf) zeroOf

/-- How a query (γ, Θ) to the tables of the clique of the groups becomes an input of `entryData`,
for the input c of the procedure and the grouping x. -/
def entryInput (y : (GroupingInput × ℕ) × TableQuery) : X0 DataInput := ((y.1.1.2, y.1.2), toLists (inK y.1.1) (labelLength y.1.1) y.2)

/-- The call carried out by a machine E for cliques: E on `arg (K, L, B')`, and its query (γ, Θ) is
answered by `entryData`, which asks the queries of Definition 2(iii). -/
def answerCall {α : Type} (E : QueryMachine TableQuery ℤ α ℤ) (arg : CliqueInput → α) : QueryMachine NetQuery ℤ (GroupingInput × CliqueCall) ℤ :=
  QueryMachine.mapIn (fun y : GroupingInput × CliqueCall => ((y.1, y.2.1), arg y.2.2)) (E.subst (QueryMachine.mapIn entryInput entryData))

/-- **The procedure of the lemma**, made from a machine E for cliques. -/
def groupingData {α : Type} (E : QueryMachine TableQuery ℤ α ℤ) (arg : CliqueInput → α) : QueryMachine NetQuery ℤ GroupingInput ℤ :=
  QueryMachine.mapIn (fun c : GroupingInput => (c, c)) (groupingCall.subst (answerCall E arg))

/-- The input for ζ = a/b, K, g and the network N with the parameters P, B. -/
def groupingInput (a b K : ℕ) {g : ℕ} (N : Net g) (P B : ℕ) : GroupingInput := ((a, b), dataInput K N P B)

/-! ### The steps of the proof -/

/-- The number computed is the L of the lemma, and `Printed.bitsOut` is its B'. -/
def LabelLengthIsL : Prop := ∀ (a b K g : ℕ) (N : Net g) (P B : ℕ), 0 < b → a ≤ b → 0 < K → N.Is P B →
  labelLength (groupingInput a b K N P B) = AppRunningTime.Lof K g ((a : ℝ) / b) P N.U ∧ bitsOut K g P B = AppRunningTime.B'of K g P B

/-- «Some grouping has at most 2g/K nodes in every group and Y_{γ,γ'} ≤ L for all γ ≠ γ'»
(`AppRunningTime.SomeGrouping`), so the search finds one: in case (i) or (ii) there is a first x <
K^g that the test accepts, and its grouping has the two properties. -/
def SearchFinds : Prop := ∀ (a b K g : ℕ) (hK0 : 0 < K) (N : Net g) (P B : ℕ), 2 ≤ K → 2 ≤ g → 0 < a → a ≤ b → N.Is P B → AppRunningTime.Cases K g ((a : ℝ) / b) P N.c →
  ∃ x < K ^ g, (List.range (K ^ g)).find? (fun y => goodData (groupingInput a b K N P B, y)) = some x ∧
    (∀ γ : Fin K, K * #{v : Fin g | Paper.grouping hK0 x v = γ} ≤ 2 * g) ∧ ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ AppRunningTime.Lof K g ((a : ℝ) / b) P N.U

/-- «Testing a grouping … take[s] time polynomial in g(P+B)»: here a test is one step, so the search
takes at most C·K^g steps, on states of size polynomial in g(P+B) and the length of ζ; that a step
takes polynomial time is `GroupingPoly`. One constant for all inputs. -/
def SearchCost : Prop := ∃ C : ℕ, ∀ (a b K g : ℕ) (N : Net g) (P B x : ℕ), 1 ≤ K → K ≤ g → N.Is P B →
  (List.range (K ^ g)).find? (fun y => goodData (groupingInput a b K N P B, y)) = some x →
    searchData.Runs (groupingInput a b K N P B) (C * K ^ g) ((g * (P + B) + size (a, b)) ^ C) (some x)

/-- «… the (K, L)-clique with the tables W̃_γ, whose value is that of the network». This is
`Value.StValueEqualsZ` (proof/networks/Value/Defs.lean), which holds for all K and g. (It speaks of
procedures that run; the clique of the groups reads only the numbers of the procedures, so it is the
same for `asked.under` and for `asked` with the
oracle built in.) -/
def ValueIsKept : Prop := Value.StValueEqualsZ

/-- «K ≤ g in both cases and L ≤ gP + 1» (`AppRunningTime.GroupingSizes`). -/
def SizesStmt : Prop := AppRunningTime.GroupingSizes

/-! ### The lemma -/

/-- **The lemma up to the call.** There is ONE constant C such that in case (i) or (ii) the search
finds a grouping number x < K^g, the first that its test accepts, with the two properties, for
which: whenever the call of x is answered by the value of the (K, L)-clique of the groups of x, at
the price tc, the procedure `groupingCall` returns the value of the
network within C·K^g + tc operations, on states of size at most (g(P+B) + the length of ζ)^C. (What
is known of that clique: its entries are below 2^{B'} and are computed by `entryData`:
`EntryCostExplicit`.) -/
def GroupingWithCall : Prop := ∃ C : ℕ, ∀ (a b K g : ℕ) (hK0 : 0 < K) (N : Net g) (P B tc : ℕ), 2 ≤ K → 2 ≤ g → 0 < a → a ≤ b → N.Is P B → AppRunningTime.Cases K g ((a : ℝ) / b) P N.c →
  ∃ x < K ^ g, (List.range (K ^ g)).find? (fun y => goodData (groupingInput a b K N P B, y)) = some x ∧
    (∀ γ : Fin K, K * #{v : Fin g | Paper.grouping hK0 x v = γ} ≤ 2 * g) ∧ (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ AppRunningTime.Lof K g ((a : ℝ) / b) P N.U) ∧
    ∀ O : CliqueCall → Option ℤ, O (callOf (groupingInput a b K N P B, x)) = some (Value.groupClique asked.under (netInput N P B) N hK0 x (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U)).value →
      groupingCall.Within O (fun _ => tc) (groupingInput a b K N P B) (C * K ^ g + tc) ((g * (P + B) + size (a, b)) ^ C) N.value

/-- E, on the input `inp`, outputs the value of every (K, L)-clique with |W_w| < 2^{B'} within 𝒯
operations, a query counted as one operation, on states of size at most S_E. -/
def SolvesCliques {α : Type} (E : QueryMachine TableQuery ℤ α ℤ) (inp : α) (K L B' 𝒯 SE : ℕ) : Prop :=
  ∀ W : ℕ → List Bool → ℤ, (∀ w < K, ∀ z ∈ words ((K - 1) * L), |W w z| < 2 ^ B') →
    E.Within (tables K L W) QueryMachine.unitCost inp 𝒯 SE (clique K L fun w => W w.val).value

/-- **Lemma 8**, for the procedure of its proof. There is ONE constant C₁ such that for all K, g ≥
2, every fraction 0 < ζ = a/b ≤ 1, every network N on [g] with parameters P, B, τ and total U in
case (i) or (ii), and EVERY machine E that outputs the value of every (K, L)-clique with |W_w| <
2^{B'} within 𝒯
operations: the procedure `groupingData E arg` outputs the value of N within (K^g +
𝒯·2^{2gP/K}·τ)·(g(P+B))^{C₁} operations, where each query of Definition 2(iii) costs τ operations;
its states have size at most S_E + (g(P+B) + the length of ζ)^{C₁}. -/
def GroupingExplicit : Prop := ∃ C₁ : ℕ, ∀ (α : Type) (E : QueryMachine TableQuery ℤ α ℤ) (arg : CliqueInput → α) (a b K g : ℕ) (N : Net g) (P B τ 𝒯 SE : ℕ),
  2 ≤ K → 2 ≤ g → 0 < a → a ≤ b → N.Is P B → 1 ≤ τ → AppRunningTime.Cases K g ((a : ℝ) / b) P N.c →
  SolvesCliques E (arg (unary K, unary (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U), unary (AppRunningTime.B'of K g P B))) K (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U) (AppRunningTime.B'of K g P B) 𝒯 SE →
    ∃ T : ℕ, (groupingData E arg).Within (netOracle N) (fun _ => τ) (groupingInput a b K N P B) T (SE + (g * (P + B) + size (a, b)) ^ C₁) N.value ∧
      (T : ℝ) ≤ ((K : ℝ) ^ g + 𝒯 * (2 : ℝ) ^ (2 * (g : ℝ) * P / K) * τ) * ((g : ℝ) * (P + B)) ^ C₁

/-- The procedure has polynomial-time steps, up to the call and as a whole if E has and `arg` is
polynomial-time: one certificate for all K, g, ζ. -/
def GroupingPoly : Prop := groupingCall.PolyTimeSteps ∧
  ∀ (α : Type) [Enc α] (E : QueryMachine TableQuery ℤ α ℤ) (arg : CliqueInput → α), E.PolyTimeSteps → PolyT arg → (groupingData E arg).PolyTimeSteps

/-- How the steps give the lemma up to the call. -/
def GroupingWithCallFrom : Prop := SearchFinds → SearchCost → SizesStmt → ValueIsKept → GroupingWithCall

/-- How the lemma up to the call, the cost of an entry and the rules of substitution give the lemma.
(The rule for a machine run on a function of its input, `Printed.mapIn_within`, is used besides.) -/
def GroupingExplicitFrom : Prop := GroupingWithCall → LabelLengthIsL → EntryCostExplicit → SizesStmt → QueryMachines.StMono → QueryMachines.StSlowDown → QueryMachines.StSubstWithin → GroupingExplicit

end ExplicitCost
