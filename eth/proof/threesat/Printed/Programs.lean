/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PrintedStatement
public import Eight.ViaGrouping.AlgDefs
public import Exits.AlgDefs
public import Value.Defs

/-! # The algorithms of the proofs, as machines with query access, and what is proved of them (definitions and statements only)

PrintedStatement.lean states Definition 4, Lemma 1 and Proposition 3 in the paper's words: «there
are an algorithm and a constant». A statement of that form reads the same whichever way it was
proved. This file names the algorithms of the printed proofs and states each step for the named
algorithm:
* `bruteMachine K`: «Trying all 2^{λK(K−1)/2} choices of one string per edge» (after Definition 4);
* `groupingMachine K g M`: the algorithm of the proof of Lemma 1, made from ANY machine M for
  cliques on K nodes: find the first good grouping; L; B' = ⌈2gP/K⌉ + g²B; «Run the algorithm for
  (K, e) with L, B' in the roles of λ, B … Answer each of its … queries by computing the entry»
  (`QueryMachine.subst` with `tableQ`);
* `levelMachine K g M`: the algorithm of the proof of Proposition 3: for every ι, the machine of
  Lemma 1 on the row network or the column network, whose values are computed with queries to the
  tables of the clique on g² nodes; P = g³λ and B₁ = gB + g²λ + 1 are handed over;
* `CLIQUE`, `NETWORK`, `COUNT`, `SAT`: the four procedures of Algorithm 1.
The plain functions inside (which bits of a string belong to which node, when a grouping is good,
the functions of Lemma 2 on the grid, …) are those of proof/networks/Eight/ViaGrouping, and each
machine is built in the same way as the step machine of the same purpose there and in
proof/threesat/Exits (`tableM`, `Exits.netAlg`, `levelAlgP`, `brute`), with «ask» in the place of
the answering procedure.
Different from Algorithm 1 as printed: SAT decides, returning at the first formula with Count(Φ) >
0, where the printed #Sat adds up counts; Clique has B as an argument and is passed B' in line 12
(Definition 4 and the proof of Lemma 1 say so; the pseudocode does not pass it); the level ℓ and the
parameter τ of Lemma 4 are parameters of the machines (they depend on δ only).
This file has no proofs. -/

@[expose] public section

namespace Printed

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines

/-- A machine for cliques: queries to the tables, input (λ, B) in unary, an integer as result. -/
abbrev CliqueMachine : Type 1 := QueryMachine TableQuery ℤ (List Unit × List Unit) ℤ

/-- A machine for networks: the queries of Definition 2(iii), the input of Definition 2(iii), an
integer as result. -/
abbrev NetMachine : Type 1 := QueryMachine NetQuery ℤ NetInput ℤ

/-! ## Two ways to write a setting of a node of a clique -/

/-- The programs of this development name a setting of the node w as the list of K strings, the
empty string at w itself. As one string, the form of Definition 3: their concatenation. -/
def toTable (x : IQ) : TableQuery := (x.1, x.2.flatten)

/-- Back: z_w cut into its K − 1 strings z_w(w') of λ bits (`SecNetworks.copyAt`), the empty string
at w. -/
def toLists (K lam : ℕ) (x : TableQuery) : IQ := (x.1, (List.range K).map fun u => if u = x.1 then [] else copyAt lam x.1 u x.2)

/-- Ask the tables for the entry named by the second component. -/
def askTable {C : Type} [HasSize C] : QueryMachine TableQuery ℤ (C × IQ) ℤ := QueryMachine.query fun x => toTable x.2

/-! ## Brute force -/

/-- «Trying all 2^{λK(K−1)/2} choices of one string per edge»: the sum over all choices of the
product over the nodes of the table entries; built as `Groundwork.brute`. B is not read. -/
def bruteMachine (K : ℕ) : CliqueMachine :=
  QueryMachine.sumRange (bruteBound K fun c : List Unit × List Unit => c.1.length)
    (QueryMachine.prodRange (Function.const _ K) (QueryMachine.mapIn (bruteQuery K (fun c : List Unit × List Unit => c.1.length) nilC) askTable))

/-! ## Procedures that may ask -/

/-- What an algorithm is given of a network (Definition 2(iii)), when the four procedures themselves
have query access to something else: `SecNetworks.Procs` with machines that may ask. -/
structure ProcsQ (Q A C : Type) : Type 1 where
  P : C → ℕ
  B : C → ℕ
  len : C → ℕ → ℕ
  cap : C → ℕ → ℕ → ℕ
  mem : QueryMachine Q A (C × WQ) Bool
  W : QueryMachine Q A (C × WQ) ℤ
  Ψ : QueryMachine Q A (C × PsiQ) ℤ
  f : QueryMachine Q A (C × FQ) ℤ

variable {Q A C : Type}

/-- The same numbers, with the step machines underneath. It is used only to hand the NUMBERS to the
plain functions of proof/networks/Eight/ViaGrouping, which take a `SecNetworks.Procs` and read
nothing else of it. -/
def ProcsQ.under (Np : ProcsQ Q A C) : Procs C :=
  { P := Np.P, B := Np.B, len := Np.len, cap := Np.cap, mem := Np.mem.toStepped, W := Np.W.toStepped, Ψ := Np.Ψ.toStepped, f := Np.f.toStepped }

/-- The oracle built into all four procedures. -/
def ProcsQ.close (Np : ProcsQ Q A C) (O : Q → Option A) : Procs C :=
  { P := Np.P, B := Np.B, len := Np.len, cap := Np.cap, mem := Np.mem.close O, W := Np.W.close O, Ψ := Np.Ψ.close O, f := Np.f.close O }

/-- (c, x or y) is (c, x) or (c, y). -/
def dist {X Y : Type} (p : C × (X ⊕ Y)) : (C × X) ⊕ (C × Y) := match p.2 with | .inl x => .inl (p.1, x) | .inr y => .inr (p.1, y)

/-- The four procedures as ONE machine that answers the queries of Definition 2(iii); yes is 1 and
no is 0. -/
def ProcsQ.answer (Np : ProcsQ Q A C) : QueryMachine Q A (C × NetQuery) ℤ :=
  QueryMachine.branch dist (QueryMachine.mapOut Np.mem fun b => if b = true then 1 else 0) (QueryMachine.branch dist Np.W (QueryMachine.branch dist Np.Ψ Np.f))

/-- The same for procedures that are step machines. -/
def answerOf (Np : Procs C) : Stepped (C × NetQuery) ℤ :=
  Stepped.branch dist (Stepped.mapOut Np.mem fun b => if b = true then 1 else 0) (Stepped.branch dist Np.W (Stepped.branch dist Np.Ψ Np.f))

/-- The input of Definition 2(iii) for a network on [g], written down from the numbers. -/
def inputOf (g : ℕ) (P B : ℕ) (len : ℕ → ℕ) (cap : ℕ → ℕ → ℕ) : NetInput :=
  ((unary P, unary B), ((List.range g).map fun a => unary (len a), (List.range g).map fun a => (List.range g).map fun b => if a = b then [] else unary (cap a b)))

/-- A machine for networks, run on the network that the procedures Np give in the context c: it is
handed the numbers, and each of its queries is answered by running the procedure. -/
def networkOn [HasSize C] (g : ℕ) (NM : NetMachine) (Np : ProcsQ Q A C) : QueryMachine Q A C ℤ :=
  QueryMachine.mapIn (fun c => (c, inputOf g (Np.P c) (Np.B c) (Np.len c) (Np.cap c))) (NM.subst Np.answer)

/-- The same for procedures that are step machines. -/
def networkOnSteps [HasSize C] (g : ℕ) (NM : NetMachine) (Np : Procs C) : Stepped C ℤ :=
  Stepped.mapIn (fun c => (c, inputOf g (Np.P c) (Np.B c) (Np.len c) (Np.cap c))) (NM.plug (answerOf Np))

/-! ## The algorithm of the proof of Lemma 1 -/

section Table

variable [HasSize C] (K g : ℕ) (Np : ProcsQ Q A C)

/-- [z_a ∈ S_a]·W_a(z_a). -/
def wQ : QueryMachine Q A ((X0 C × ℕ) × ℕ) ℤ :=
  QueryMachine.gated (QueryMachine.mapIn (qW K g Np.under.toPaperNetwork) Np.mem) (QueryMachine.mapIn (qW K g Np.under.toPaperNetwork) Np.W)

/-- [z_a ∈ S_a][z_b ∈ S_b]·Ψ_{a,b}(z_a, z_b). -/
def psiQ : QueryMachine Q A ((X0 C × ℕ) × ℕ) ℤ :=
  QueryMachine.gated (QueryMachine.mapIn (qW K g Np.under.toPaperNetwork) Np.mem)
    (QueryMachine.gated (QueryMachine.mapIn (qMb K g Np.under) Np.mem) (QueryMachine.mapIn (qPsi K g Np.under) Np.Ψ))

/-- [z_a ∈ S_a]·f_{a,b}(z_a, θ_{a,b}). -/
def fQ : QueryMachine Q A ((X0 C × ℕ) × ℕ) ℤ :=
  QueryMachine.gated (QueryMachine.mapIn (qW K g Np.under.toPaperNetwork) Np.mem) (QueryMachine.mapIn (qF K g Np.under.toPaperNetwork) Np.f)

/-- The factor number i = a·g + b of a term of W̃_γ(Θ), as `Eight.ViaGrouping.termP`. -/
def termQ : QueryMachine Q A ((X0 C × ℕ) × ℕ) ℤ :=
  QueryMachine.ite (isOne K g) (QueryMachine.const 1) (QueryMachine.ite (isW g) (wQ K g Np) (QueryMachine.ite (isPsi K g) (psiQ K g Np) (fQ K g Np)))

/-- **One entry W̃_γ(Θ)**: 0 unless all appended bits are 0; else the sum, over all strings of Σ_{a
∈ G_γ} P_a bits, of the product of the g² factors. Built as `Eight.ViaGrouping.tableM`. -/
def tableQ : QueryMachine Q A (X0 C) ℤ :=
  QueryMachine.ite (validB K g Np.under.toPaperNetwork) (QueryMachine.sumRange (nStates K g Np.under.toPaperNetwork) (QueryMachine.prodRange (nPairs g) (termQ K g Np))) (QueryMachine.const 0)

end Table

/-- Definition 2(iii) read by a machine for networks: the numbers are read off the input, and each
of the four procedures is one query. -/
def asked : ProcsQ NetQuery ℤ NetInput where
  P c := c.1.1.length
  B c := c.1.2.length
  len c a := (c.2.1.getD a []).length
  cap c a b := ((c.2.2.getD a []).getD b []).length
  mem := QueryMachine.mapOut (QueryMachine.query fun x => Sum.inl x.2) fun v => decide (v ≠ 0)
  W := QueryMachine.query fun x => Sum.inr (Sum.inl x.2)
  Ψ := QueryMachine.query fun x => Sum.inr (Sum.inr (Sum.inl x.2))
  f := QueryMachine.query fun x => Sum.inr (Sum.inr (Sum.inr x.2))

/-- «B' = ⌈2gP/K⌉ + g²B». -/
def bitsOut (K g P B : ℕ) : ℕ := (2 * (g * P) + (K - 1)) / K + g ^ 2 * B

/-- **The algorithm of the proof of Lemma 1**, made from a machine M for cliques on K nodes. «Go
through all K^g groupings (a constant) and fix the first good one» (`Exits.search`: it stops there,
as line 10 of Algorithm 1 says; it reads only the numbers c_{a,b} and P, and asks nothing). «Let L =
max{1, ⌊(U + gP/K)/K²⌋}» (`lamP`).
«Run the algorithm for (K, e) with L, B' in the roles of λ, B … Answer each of its … queries by
computing the entry»: M gets (L, B'), and its query (γ, Θ) is answered by `tableQ`, which asks the
queries of Definition 2(iii). The result is 0 if no grouping is good (which does not happen for g =
3K⁸). -/
def groupingMachine (K g : ℕ) (M : CliqueMachine) : NetMachine :=
  QueryMachine.optBind (QueryMachine.lift (Exits.search K g asked.under))
    (QueryMachine.mapIn (fun cx : NetInput × ℕ => (cx, (unary (lamP K g asked.under cx), unary (bitsOut K g (asked.P cx.1) (asked.B cx.1)))))
      (M.subst (QueryMachine.mapIn (fun y : (NetInput × ℕ) × TableQuery => (y.1, toLists K (lamP K g asked.under y.1) y.2)) (tableQ K g asked))))
    zeroOf

/-! ## The algorithm of the proof of Proposition 3 -/

/-- The weight W_a of a row (or column): the product of the g table entries, each asked for, or 0 if
the check of the straight edges inside the row fails. Built as `Groundwork.Prog.sideWP`. -/
def sideWQ {C : Type} [HasSize C] (g : ℕ) (tr : Bool) (lam : C → ℕ) : QueryMachine TableQuery ℤ ((C × ℕ) × WQ) ℤ :=
  QueryMachine.ite (sideChk g tr lam) (QueryMachine.prodRange (sideG g) (QueryMachine.mapIn (sideQuery g tr lam) askTable)) (QueryMachine.const 0)

/-- **«Two networks for each ι»**: the row network (tr = false) or the column network (tr = true) of
ι, as Definition 2(iii) asks, in the context ((λ, B), y), y the number of ι. «P = g³λ», «B₁ = gB +
g²λ + 1 in the role of B». W_a is computed with g queries to the tables of the clique on g² nodes;
Ψ_{a,a'} (`gridPsi`) and
f_{a,a'} (`gridFf`) in one step, with no query; every string of g³λ bits is a setting (here each
grid point keeps a slot of λ bits for the edge to itself, where the paper encodes a row in g(g² − 1)λ
bits); W_a is 0 unless those slots are 0 and the straight edges inside the row agree. The numbers
and functions are those of `Eight.ViaGrouping.levelProcs`, but for B₁. -/
def gridProcs (g : ℕ) (tr : Bool) : ProcsQ TableQuery ℤ ((List Unit × List Unit) × ℕ) where
  P c := g ^ 3 * c.1.1.length
  B c := g * c.1.2.length + g ^ 2 * c.1.1.length + 1
  len c _ := nMemb g g tr * (g * g) * c.1.1.length
  cap c a b := capG eightF g g tr 0 c.1.1.length c.2 a b
  mem := QueryMachine.lift (Stepped.mapIn (fun _ => ()) (Stepped.const true))
  W := sideWQ g tr fun c : List Unit × List Unit => c.1.length
  Ψ := QueryMachine.lift (Stepped.ofFun fun x => gridPsi g tr x.1.1.1.length x.1.2 x.2)
  f := QueryMachine.lift (Stepped.ofFun fun x => gridFf eightF [] g g tr 0 x.1.1.1.length x.1.2 x.2)

/-- **The algorithm of the proof of Proposition 3** for cliques on g² nodes, made from a machine M
for cliques on K nodes: for every ι : ℛ → {0, …, t}, t = ⌈λ/3⌉, «apply Lemma 1 to the network with
the smaller total»; «adding the Z_ι and dividing by 2^{t|ℛ|} gives Z». Built as
`Eight.ViaGrouping.levelAlgP`. -/
def levelMachine (K g : ℕ) (M : CliqueMachine) : CliqueMachine :=
  QueryMachine.bind
    (QueryMachine.sumRange (numPat8 g fun c : List Unit × List Unit => c.1.length)
      (QueryMachine.ite (useRowP g fun c : List Unit × List Unit => c.1.length) (networkOn g (groupingMachine K g M) (gridProcs g false)) (networkOn g (groupingMachine K g M) (gridProcs g true))))
    (QueryMachine.lift (Stepped.ofFun fun p : (List Unit × List Unit) × ℤ => p.2 / ((2 ^ (tOf p.1.1.length * nRect g) : ℕ) : ℤ)))

/-! ## Algorithm 1 -/

/-- **procedure Clique(ℓ, λ, the tables)**: level 0 is brute force; level ℓ + 1 is the algorithm of
Proposition 3 on Clique(ℓ). -/
def CLIQUE : ℕ → CliqueMachine
  | 0 => bruteMachine (levelK 0)
  | ℓ + 1 => levelMachine (levelK ℓ) (levelG ℓ) (CLIQUE ℓ)

/-- **procedure Network(ℓ, a network on g_ℓ nodes)**: the algorithm of Lemma 1 with K = K_ℓ, which
calls Clique(ℓ). -/
def NETWORK (ℓ : ℕ) : NetMachine := groupingMachine (levelK ℓ) (levelG ℓ) (CLIQUE ℓ)

/-- The procedures of the network of Φ (`Eight.ViaGrouping.satProcs`), which also give «B = 1». -/
def formulaProcs (g k : ℕ) : Procs Fml := { satProcs g k with B := fun _ => 1 }

/-- **procedure Count(Φ)**, for a fixed level ℓ: «if m = 0 then return 1»; «return Network(ℓ, the
network of Φ on g_ℓ clusters)». A step machine: the queries of Network are answered by the
procedures of the network of Φ. -/
def COUNT (ℓ : ℕ) : StepMachine Paper.Formula ℤ :=
  Stepped.ite (fun Φ : Paper.Formula => Φ.isEmpty) (Stepped.const 1) (networkOnSteps (levelG ℓ) (NETWORK ℓ) (formulaProcs (levelG ℓ) 3))

/-- **Lines 1 to 4 for deciding** (the paper's procedure #Sat counts), for a fixed level ℓ and a
fixed parameter τ of Lemma 4 (`Suffices.satLoop`: lines 1 to 4, with the early return). -/
def SAT (ℓ τ : ℕ) : StepMachine (List Bool) Bool := Suffices.satLoop τ (COUNT ℓ)

/-! ## The statements, each for the named machine -/

/-- «(K, ½) is achievable», by brute force. -/
def StBrute : Prop := ∀ K : ℕ, 2 ≤ K → (bruteMachine K).PolyTimeSteps ∧ ∃ Cc : ℕ, AchievedBy (bruteMachine K) Cc K (1 / 2)

/-- **Proof of Lemma 1, «Cost», first half**: «So |W̃_γ| < 2^{B'} with B' = ⌈2gP/K⌉ + g²B, and one
entry costs 2^{2gP/K}·poly(P + B)·τ operations». For a network N on [g] with parameters P, B, a
grouping number x < K^g with (G1) and Y_{γ,γ'} ≤ L ≤ 2gP: the machine `tableQ`, asked for the entry
(γ, Θ) of the tables W̃ of the (K, L)-clique of the groups
(`Value.groupClique` has them as its tables: the display of the paper; of its first argument it
reads only the numbers P_a, c_{a,b}), returns it within c₁·2^{P·⌊2g/K⌋}·τ operations, if each query
of Definition 2(iii) costs τ, on states of size at most c₁·(P + B)^{c₁}; and the entry is below
2^{B'}. Here P·⌊2g/K⌋ ≤ 2gP/K, and the factor poly(P + B) of the print is not needed, because an own
step may take polynomial time; the sizes of the states are bounded instead.
K and g are positive (for g = 0 the entry is 1 and B' = 0). The constant depends on K and g only. -/
def StEntryCost : Prop := ∀ K g : ℕ, ∃ c₁ : ℕ, ∀ (hK0 : 0 < K), 0 < g → ∀ (N : Net g) (P B τ : ℕ), N.Is P B → 1 ≤ τ →
  ∀ x < K ^ g, ∀ L ≤ 2 * (g * P), (∀ γ : Fin K, K * #{a : Fin g | Paper.grouping hK0 x a = γ} ≤ 2 * g) → (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) →
    ∀ (γ : Fin K), ∀ Θ ∈ words ((K - 1) * L),
      (tableQ K g asked).Within (netOracle N) (fun _ => τ) ((netInput N P B, x), toLists K L (γ.val, Θ)) (c₁ * 2 ^ (P * (2 * g / K)) * τ) (c₁ * (P + B) ^ c₁)
        ((Value.groupClique (asked.close (netOracle N)) (netInput N P B) N hK0 x L).W γ Θ) ∧
      |(Value.groupClique (asked.close (netOracle N)) (netInput N P B) N hK0 x L).W γ Θ| < 2 ^ bitsOut K g P B

/-- **Lemma 1 for the algorithm of its proof, from ANY machine that does what Definition 4 asks.** -/
def StGroupingTied : Prop := ∀ (K : ℕ) (e : ℝ) (M : CliqueMachine) (Cc : ℕ), 2 ≤ K → 0 ≤ e → AchievedBy M Cc K e →
  ∃ C₁ : ℕ, ComputesNetworks (groupingMachine K (3 * K ^ 8) M) C₁ (3 * K ^ 8) K e

/-- The same with the steps of the proof in its hypotheses: «a good grouping exists … fix the first
good one» (`Eight.ViaGrouping.StSearch`), the run of the search (`Exits.StSearchStops`), «one entry
costs …» (`StEntryCost`), «so the value equals Z» for the clique of the groups as the network of
Definition 3 (`Value.StValueEqualsZ`), and
«answer each of its at most … queries by computing the entry» (`StAnswerEachQuery` is the form for
step machines; here `QueryMachines.StSubst`). -/
def StGroupingTiedOf : Prop := Eight.ViaGrouping.StSearch → Exits.StSearchStops → StEntryCost → Value.StValueEqualsZ → QueryMachines.StSubst → StGroupingTied

/-- The machine of Lemma 1 has polynomial-time steps if M has. -/
def StGroupingPoly : Prop := ∀ (K g : ℕ) (M : CliqueMachine), M.PolyTimeSteps → (groupingMachine K g M).PolyTimeSteps

/-- **Lemma 1 for networks given by procedures** (`SecNetworks.IsNetwork`: Definition 2 with (iii)
as four step machines that take at most τ steps each): a machine that does what Lemma 1 says, with
its queries answered by the procedures, outputs the value within 3·C₁·2^{e(U + gP/K) + 2gP/K}(P +
B)^{C₁}·τ steps. -/
def StOnProcedures : Prop := ∀ (NM : NetMachine) (C₁ g K : ℕ) (e : ℝ), ComputesNetworks NM C₁ g K e →
  ∀ (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), SecNetworks.IsNetwork Np c N P B τ S →
    ∃ T : ℕ, (networkOnSteps g NM Np).Runs c T (size c + C₁ * (P + B) ^ C₁ + S + 4) N.value ∧
      (T : ℝ) ≤ 3 * (C₁ * (2 : ℝ) ^ (e * ((N.U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ C₁) * τ

/-- **Proof of Proposition 3: «Both networks satisfy Definition 2 with P = g³λ (so gP = N), with B₁ =
gB + g²λ + 1 in the role of B, and with τ = poly(B + λ)».** For g ≥ 1 there is a constant a such
that for λ, B ≥ 1, tables with |W_w| < 2^B of the clique on g² nodes, and every y < (t + 1)^{|ℛ|}:
the network `levelNetP g tr λ y` is a network with parameters g³λ and B₁;
the input that `gridProcs` hands over is the input that belongs to it; and every query of Definition
2(iii) to it is answered by `gridProcs` within a·(B + λ)^a operations, a query to the tables counted
as one operation. -/
def StBothNetworks : Prop := ∀ g : ℕ, 1 ≤ g → ∃ a : ℕ, ∀ (tr : Bool) (lam B : ℕ) (W : ℕ → List Bool → ℤ) (y : ℕ), 1 ≤ lam → 1 ≤ B → (∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B) → y < (tOf lam + 1) ^ nRect g →
  (levelNetP g tr lam y fun w θ => W w.val (List.ofFn θ).flatten).Is (g ^ 3 * lam) (g * B + g ^ 2 * lam + 1) ∧
  inputOf g ((gridProcs g tr).P ((unary lam, unary B), y)) ((gridProcs g tr).B ((unary lam, unary B), y)) ((gridProcs g tr).len ((unary lam, unary B), y)) ((gridProcs g tr).cap ((unary lam, unary B), y))
    = netInput (levelNetP g tr lam y fun w θ => W w.val (List.ofFn θ).flatten) (g ^ 3 * lam) (g * B + g ^ 2 * lam + 1) ∧
  ∀ (x : NetQuery) (v : ℤ), netOracle (levelNetP g tr lam y fun w θ => W w.val (List.ofFn θ).flatten) x = some v →
    (gridProcs g tr).answer.Within (tables (g * g) lam W) QueryMachine.unitCost (((unary lam, unary B), y), x) (a * (B + lam) ^ a) (a * (B + lam) ^ a) v

/-- **Proposition 3, first sentence, for the algorithm of its proof, from ANY machine that does what
Definition 4 asks.** -/
def StLevelTied : Prop := ∀ (K : ℕ) (e : ℝ) (M : CliqueMachine) (Cc : ℕ), 2 ≤ K → 0 ≤ e → AchievedBy M Cc K e →
  ∃ Cc' : ℕ, AchievedBy (levelMachine K (3 * K ^ 8) M) Cc' ((3 * K ^ 8) ^ 2) ((Eight.rho + 2 / K) * e + 2 / K)

/-- The machine of Proposition 3 has polynomial-time steps if M has. -/
def StLevelPoly : Prop := ∀ (K g : ℕ) (M : CliqueMachine), M.PolyTimeSteps → (levelMachine K g M).PolyTimeSteps

/-- **Section 8: «By brute force and Proposition 3, (K_ℓ, e_ℓ) is achievable for every ℓ»**, by
Clique(ℓ). The numbers e_ℓ are `Eight.Level.levelE`, the recursion that the paper prints in Section 8. -/
def StClique : Prop := ∀ ℓ : ℕ, (CLIQUE ℓ).PolyTimeSteps ∧ ∃ Cc : ℕ, AchievedBy (CLIQUE ℓ) Cc (levelK ℓ) (Level.levelE ℓ)

/-- **Section 6, «Cost», for Count**: as `Exits.StCountCost`, for the machine of this file. -/
def StCountCost : Prop := ∀ (δ' : ℝ) (ℓ : ℕ), 0 < δ' → δ' ≤ 1 → 72 / δ' ≤ levelK ℓ → Level.levelE ℓ ≤ δ' / 12 →
  PolyTimeSteps (COUNT ℓ) ∧ ∃ A : ℕ, ∀ Φ : Paper.Formula, (∀ C ∈ Φ, C.length ≤ 3) → ∃ T : ℕ, (COUNT ℓ).Runs Φ T (A * size Φ ^ A) (numSat Φ) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length)

/-- **The deciding form of Algorithm 1 decides 3-SAT, with the constants of its header.** Let 0 < δ
≤ 1 («We may assume δ ≤ 1»), ε = δ/3, let Mc ≥ 1 and τ be a constant and a parameter of Lemma 4 for
ε (`Enumerate.Enumerates (δ/3) Mc τ`), δ' = δ/(3·Mc), and ℓ the first level with K_ℓ ≥ 72/δ' and e_ℓ
≤ δ'/12 (`Eight.Level.firstLevel`). Then Sat(ℓ, τ) has polynomial-time steps and decides 3-SAT on n
variables within c·2^{δn} steps. As `Exits.StAlgorithm`, for the machines of this file. -/
def StAlgorithm : Prop := ∀ (δ : ℝ) (Mc τ : ℕ) (hδ' : 0 < δ / (3 * (Mc : ℝ))), 0 < δ → δ ≤ 1 → 1 ≤ Mc → Enumerate.Enumerates (δ / 3) Mc τ →
  PolyTimeSteps (SAT (Level.firstLevel hδ') τ) ∧ Paper.DecidesInSteps (SAT (Level.firstLevel hδ') τ) δ

/-- **Theorem 2 in its decision form for step machines, with the machine named**: for every δ > 0
there are a level ℓ and a parameter τ such that Sat(ℓ, τ) has polynomial-time steps and decides
3-SAT on n variables within c·2^{δn} steps. -/
def StDecides : Prop := ∀ δ : ℝ, 0 < δ → ∃ ℓ τ : ℕ, PolyTimeSteps (SAT ℓ τ) ∧ Paper.DecidesInSteps (SAT ℓ τ) δ

/-- **The proof of Theorem 2 in Section 6, from the printed definition**: «Since e* = 0 < δ'/12 and
achievability is monotone in e (Definition 4), (K, δ'/12) is achievable for infinitely many K»; for
ANY machine M that does what Definition 4 asks for (K, δ'/12), K ≥ 72/δ', the loop of lines 1 to 4
over the machine of Lemma 1 with M, on the network of Φ, decides 3-SAT within c·2^{δn} steps. -/
def StProofNamed : Prop := ∀ (δ : ℝ) (Mc τ K : ℕ) (M : CliqueMachine) (Cc : ℕ), 0 < δ → δ ≤ 1 → 1 ≤ Mc → Enumerate.Enumerates (δ / 3) Mc τ → 72 / (δ / (3 * (Mc : ℝ))) ≤ K → M.PolyTimeSteps → AchievedBy M Cc K (δ / (3 * (Mc : ℝ)) / 12) →
  PolyTimeSteps (Suffices.satLoop τ (networkOnSteps (3 * K ^ 8) (groupingMachine K (3 * K ^ 8) M) (formulaProcs (3 * K ^ 8) 3))) ∧
    Paper.DecidesInSteps (Suffices.satLoop τ (networkOnSteps (3 * K ^ 8) (groupingMachine K (3 * K ^ 8) M) (formulaProcs (3 * K ^ 8) 3))) δ

/-- The end statements of the chain. The last two fields are one and the same proposition:
`through_eStar` stands for the proof of Section 6 (through `everyEta` and `proofNamed`),
`by_algorithm` for Algorithm 1 (through `decides`); the statement itself does not say that these
proofs run through the definitions and machines of this file. `proofNamed` and `algorithm` speak of
a constant Mc and a parameter τ of Lemma 4 (`Enumerate.Enumerates`); that there are such for every ε
is the field `enumeration`, Lemma 4 as an enumeration (proof/threesat/Enumerate/). -/
structure EndStatements : Prop where
  mono : StMono
  half : StHalf
  answerEachQuery : StAnswerEachQuery
  groupingLemma : GroupingLemma
  levelProposition : LevelProposition
  eStarZero : EStarZero
  everyEta : StEveryEta
  clique : StClique
  enumeration : Enumerate.StEnumeration
  proofNamed : StProofNamed
  algorithm : StAlgorithm
  decides : StDecides
  through_eStar : Sat3.ThmEveryDelta
  by_algorithm : Sat3.ThmEveryDelta

end Printed
