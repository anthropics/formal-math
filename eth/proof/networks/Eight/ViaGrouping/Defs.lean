/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.SecNetworks_LemGrouping
public import Eight.Level.Defs

/-! # Lemma 1 along the printed proof: the program and the interfaces (definitions only)

The files of proof/networks/Eight/ViaGrouping/ hold the algorithm of the printed proof of Lemma 1,
for networks as Definition 2 prints them (passed to the form of the namespace `Paper` by
proof/networks/Eight/SecNetworks_LemGrouping.lean):
* «Go through all K^g groupings and fix the first good one», good as printed: (G1) every group has
  at most 2g/K nodes, (G2) Y_{γ,γ'} ≤ (U + gP/K)/K², with the P that the algorithm is given
  (`goodP`, `searchP`);
* L = max{1, ⌊(U + gP/K)/K²⌋} (`lamP`);
* the tables W̃_γ(Θ) = [all appended bits are 0]·Σ_{(z_a)} ∏ W_a(z_a) ∏ Ψ_{a,b}(z_a, z_b) ∏
  f_{a,b}(z_a, θ_{a,b}), each z_a ranging over S_a, computed with the four procedures of Definition
  2(iii) (`tableM`);
* «Run the algorithm for (K, e) with L, B' in the roles of λ, B … Answer each of its queries by
  computing the entry» (`netAlg`).
The plain functions that cut a setting of a group and a string Θ(γ') into their parts (`members`,
`zA`, `labOf`, `validB`, …) are those of proof/machines/StepMachines/Prog/NetProg.lean; they depend
only on the numbers P_a and c_{a,b}.

Different from the paper: the search goes on past the first good grouping (it runs through all K^g
and keeps the first), which the printed sentence allows but line 10 of Algorithm 1 does not do; a
string of P_a bits that is not a setting is met and gives the factor 0; the algorithm does not read
B:
the algorithm for cliques is not told B either, and its bound holds for every B that bounds the
entries. So `GiveP` leaves out «B is given», and the theorems of this folder ask less of the
procedures than Definition 2 does. On the other hand P, which the algorithm
does read, must be given in unary for the steps to take polynomial time (`KeepsP`).
This file has no proofs. -/

@[expose] public section

namespace Eight.ViaGrouping

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks

/-! ## Definition 2(iii) without «B is given», and what Lemma 1 says of an algorithm -/

/-- Definition 2(iii), all but one clause: in the context c the procedures give the numbers P, P_a,
c_{a,b} of N, decide membership in S_a for strings of P_a bits, and compute every value of W_a,
Ψ_{a,b}, f_{a,b}, each within τ steps on states of size at
most S. The clause left out: that they give B. -/
structure GiveP {C : Type} (Np : Procs C) (c : C) {g : ℕ} (N : Net g) (P τ S : ℕ) : Prop where
  P_eq : Np.P c = P
  len_eq : ∀ a : Fin g, Np.len c a = N.len a
  cap_eq : ∀ a b : Fin g, a ≠ b → Np.cap c a b = N.c a b
  mem_runs : ∀ (a : Fin g) (z : List Bool), z.length = N.len a → Np.mem.Runs (c, (a.val, z)) τ S (decide (z ∈ N.S a))
  W_runs : ∀ (a : Fin g), ∀ z ∈ N.S a, Np.W.Runs (c, (a.val, z)) τ S (N.W a z)
  Ψ_runs : ∀ (a b : Fin g), a ≠ b → ∀ z ∈ N.S a, ∀ z' ∈ N.S b, Np.Ψ.Runs (c, ((a.val, b.val), (z, z'))) τ S (N.Ψ a b z z')
  f_runs : ∀ (a b : Fin g), a ≠ b → ∀ z ∈ N.S a, ∀ θ ∈ words (N.c a b), Np.f.Runs (c, ((a.val, b.val), (z, θ))) τ S (N.f a b z θ)

/-- Definition 2 with `GiveP` for (iii). Every network in the sense of `SecNetworks.IsNetwork` is
one in this sense. -/
structure IsNetworkP {C : Type} {g : ℕ} (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ) : Prop where
  is : N.Is P B
  τ_pos : 1 ≤ τ
  given : GiveP Np c N P τ S

/-- The bound of Lemma 1 for the algorithm NA, with the exponent ε·U + b·gP/K: one constant A (the
paper's C₁) such that NA outputs the value of every network on [g] with parameters P, B, τ and total
U within A·2^{εU + b·gP/K}·(P + B)^A·τ steps, on states
of size at most S + A·(size of the context + P + B)^A. Lemma 1 has ε = e and b = e + 2, since e·U +
(e + 2)·gP/K = e(U + gP/K) + 2gP/K. -/
def Correct (NA : NetAlg) (g K : ℕ) (ε b : ℝ) : Prop := ∃ A : ℕ, ∀ (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
  ∃ T : ℕ, (NA.app Np).Runs c T (S + A * (size c + P + B) ^ A) N.value ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (ε * (N.U : ℝ) + b * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ A * τ

/-- The procedures have polynomial-time steps (`SecNetworks.Procs.Keeps`), and the number P is given
in unary. The algorithm of the printed proof computes L = max{1, ⌊(KU + gP)/K³⌋} from P and gives it
to the algorithm for cliques, whose steps are known to take polynomial time only when λ is given in
unary. So P is asked to be given in unary too. -/
structure KeepsP {C : Type} [Enc C] (Np : Procs C) : Prop where
  keeps : Np.Keeps
  P : Unary Np.P

/-- The algorithm has polynomial-time steps whenever the procedures have and P is given in unary. -/
def AlgKeeps (NA : NetAlg) : Prop :=
  ∀ (C : Type) [HasSize C] [Enc C] [Carried C] (Np : Procs C), KeepsP Np → Nonempty (IsPolyT (NA.app Np))

/-! ## The program -/

section Program

variable {C : Type} [HasSize C] (K g : ℕ) (Np : Procs C)

/-- L = max{1, ⌊(U + gP/K)/K²⌋}, written max{1, ⌊(KU + gP)/K³⌋}, with the given P. -/
def lamP (cx : C × ℕ) : ℕ := Colouring.beta K g (Uc g Np.toPaperNetwork cx.1) (Np.P cx.1)

/-- Is the grouping number x good? (G1) K·|G_γ| ≤ 2g for every γ; (G2) K³·Y_{γ,γ'} ≤ K·U + g·P for
all γ ≠ γ'. -/
def goodP (cx : C × ℕ) : Bool :=
  ((List.range K).all fun G => decide (K * (members K g cx.2 G).length ≤ 2 * g)) &&
  (List.range K).all fun G => (List.range K).all fun G' =>
    G == G' || decide (K ^ 3 * lbLen K g Np.toPaperNetwork cx.1 cx.2 G G' ≤ K * Uc g Np.toPaperNetwork cx.1 + g * Np.P cx.1)

/-- The query (b, z_b), for the factor number i = a·g + b. -/
def qMb (u : (X0 C × ℕ) × ℕ) : C × WQ := (u.1.1.1.1, (u.2 % g, zA K g Np.toPaperNetwork u.1 (u.2 % g)))

/-- The query ((a, b), (z_a, z_b)) for Ψ_{a,b}, i = a·g + b. -/
def qPsi (u : (X0 C × ℕ) × ℕ) : C × PsiQ :=
  (u.1.1.1.1, ((u.2 / g, u.2 % g), (zA K g Np.toPaperNetwork u.1 (u.2 / g), zA K g Np.toPaperNetwork u.1 (u.2 % g))))

/-- [z_a ∈ S_a]·W_a(z_a). -/
def wM : Stepped ((X0 C × ℕ) × ℕ) ℤ := gated (mapIn (qW K g Np.toPaperNetwork) Np.mem) (mapIn (qW K g Np.toPaperNetwork) Np.W)

/-- [z_a ∈ S_a][z_b ∈ S_b]·Ψ_{a,b}(z_a, z_b), by the procedure for Ψ. -/
def psiP : Stepped ((X0 C × ℕ) × ℕ) ℤ :=
  gated (mapIn (qW K g Np.toPaperNetwork) Np.mem) (gated (mapIn (qMb K g Np) Np.mem) (mapIn (qPsi K g Np) Np.Ψ))

/-- [z_a ∈ S_a]·f_{a,b}(z_a, θ_{a,b}). -/
def fM : Stepped ((X0 C × ℕ) × ℕ) ℤ := gated (mapIn (qW K g Np.toPaperNetwork) Np.mem) (mapIn (qF K g Np.toPaperNetwork) Np.f)

/-- The factor number i = a·g + b of a term of W̃_γ(Θ): 1 if a is not in the group or b < a is in
it; the factor of W_a if b = a; of Ψ_{a,b} if b > a is in the group; of f_{a,b} if b is in another
group. -/
def termP : Stepped ((X0 C × ℕ) × ℕ) ℤ :=
  ite (isOne K g) (const 1) (ite (isW g) (wM K g Np) (ite (isPsi K g) (psiP K g Np) (fM K g Np)))

/-- One entry W̃_γ(Θ): 0 unless all appended bits are 0; else the sum, over all strings of Σ_{a ∈
G_γ} P_a bits, of the product of the g² factors. -/
def tableM : Stepped (X0 C) ℤ :=
  ite (validB K g Np.toPaperNetwork) (sumRange (nStates K g Np.toPaperNetwork) (prodRange (nPairs g) (termP K g Np))) (const 0)

/-- «Go through all K^g groupings and fix the first good one.» -/
def searchP : Stepped C (Option ℕ) := firstRange (nCol K g) (ofFun (goodP K g Np)) id

end Program

/-- **The algorithm of the proof of Lemma 1**: find the first good grouping, then run the algorithm
E for cliques on K nodes with L in the role of λ, answering each query by computing the entry of W̃.
The result is 0 if no grouping is good (which does not
happen for g = 3K⁸). -/
def netAlg (K g : ℕ) (E : Paper.CliqueAlgorithm) : NetAlg :=
  ⟨fun Np => optBind (searchP K g Np) (E.app (lamP K g Np) (tableM K g Np)) zeroOf⟩

/-! ## The steps of the proof, as statements -/

/-- «A good grouping exists» and «fix the first good one»: for g = 3K⁸ the search finds a grouping x
< K^g, and it is good as printed (`SecNetworks.Good`). -/
def StSearch : Prop := ∀ (K : ℕ) (hK : 2 ≤ K) (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net (3 * K ^ 8)) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
  ∃ x < K ^ (3 * K ^ 8), (List.range (K ^ (3 * K ^ 8))).find? (fun x => goodP K (3 * K ^ 8) Np (c, x)) = some x ∧
    Good N.c P (Paper.grouping (g := 3 * K ^ 8) (by omega : 0 < K) x)

/-- «So |W̃_γ| < 2^{B'} with B' = ⌈2gP/K⌉ + g²B, and one entry costs 2^{2gP/K}·poly(P + B)·τ
operations»: for a grouping with (G1) and Y_{γ,γ'} ≤ L ≤ 2gP, the procedure `tableM` answers every
query to the tables W̃ of the (K, L)-clique of the groups
(`Paper.groupedTables` of the network in the form of the namespace `Paper`;
`groupedTables_eq_display` in Display.lean writes them out as the display of the paper) within
c₁·2^{P·⌊2g/K⌋}·τ steps, on states of size at most S + c₁·(size c + P + B)^{c₁}; every entry is at
most
2^{P·⌊2g/K⌋ + g²B} in absolute value. The constant depends on K and g only. Here P·⌊2g/K⌋ ≤ 2gP/K;
the factor poly(P + B) of the paper is not needed, because steps are counted and a step may take
polynomial time (`StKeeps`); the sizes of the states are
bounded instead. -/
def StTable : Prop := ∀ K g : ℕ, ∃ c₁ : ℕ, 1 ≤ c₁ ∧ ∀ (hK0 : 0 < K) (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
  ∀ x < K ^ g, ∀ L ≤ 2 * (g * P), (∀ γ : Fin K, K * #{a : Fin g | Paper.grouping hK0 x a = γ} ≤ 2 * g) → (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) →
    ServesInst (tableM K g Np) (c, x) L (P * (2 * g / K) + g ^ 2 * B) (c₁ * 2 ^ (P * (2 * g / K)) * τ) (S + c₁ * (size c + P + B) ^ c₁)
      (Paper.groupedTables Np.toPaperNetwork c N.toPaperNetwork hK0 x L)

/-- «… so the value equals Z»: the (K, L)-clique with the tables W̃ has the value of the network. -/
def StValue : Prop := ∀ (K g : ℕ) (hK0 : 0 < K) (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
  ∀ x L : ℕ, (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) → Paper.cliqueValue L (Paper.groupedTables Np.toPaperNetwork c N.toPaperNetwork hK0 x L) = N.value

/-- The algorithm has polynomial-time steps if E has. -/
def StKeeps : Prop := ∀ (K g : ℕ) (E : Paper.CliqueAlgorithm), E.PolyTimeSteps → AlgKeeps (netAlg K g E)

/-- **Lemma 1 for the algorithm of its proof**: if E evaluates (K, λ)-cliques with the exponent e,
then `netAlg K (3K⁸) E` evaluates networks on [3K⁸] with the exponent e(U + gP/K) + 2gP/K. -/
def StLemGrouping : Prop := ∀ (K : ℕ) (e : ℝ) (E : Paper.CliqueAlgorithm), 2 ≤ K → 0 ≤ e → E.Within K e → Correct (netAlg K (3 * K ^ 8) E) (3 * K ^ 8) K e (e + 2)

/-! ## From a network in the form of the namespace `Paper`, with a procedure for Ψ, to the data of Definition 2 -/

/-- A network in the form of the namespace `Paper`, read as the data of Definition 2: Ψ is the sum
that `Paper.Network` defines; `n` gives the lengths P_a. -/
def ofNetwork {g : ℕ} (N : Paper.Network (Fin g) (List Bool) (List Bool)) (n : Fin g → ℕ) : Net g where
  len := n
  S := N.S
  W := N.W
  Ψ := N.Ψ
  c := N.c
  f := N.f

/-- The procedures `Paper.NetworkProcedures`, with a function that gives P and a procedure Q for Ψ.
Every string of P_a bits is a setting, so the test for membership forgets the query and says yes. B
is not given (the entry is a dummy). -/
def ofProcs {C : Type} [HasSize C] (Np : Paper.NetworkProcedures C) (Pf : C → ℕ) (Q : Stepped (C × PsiQ) ℤ) : Procs C where
  P := Pf
  B := fun _ => 0
  len := Np.n
  cap := Np.cap
  mem := mapIn (fun _ => ()) (const true)
  W := Np.W
  Ψ := Q
  f := Np.f

/-- The bridge: a network in the form of the namespace `Paper` with parameters P, B, τ, together
with a procedure Q that computes its Ψ within τ steps, is a network in the sense of Definition 2
with parameters P, B + 1, τ («at most 2^B» gives «below 2^{B+1}»), with the same value and the same
total. -/
def StBridge : Prop := ∀ (C : Type) [HasSize C] (g : ℕ) (Np : Paper.NetworkProcedures C) (Pf : C → ℕ) (Q : Stepped (C × PsiQ) ℤ) (c : C) (N : Paper.Network (Fin g) (List Bool) (List Bool)) (P B τ S : ℕ),
  1 ≤ P → 1 ≤ τ → Paper.IsNetwork Np c N P B τ S → Pf c = P →
  (∀ a b : Fin g, a ≠ b → ∀ z ∈ N.S a, ∀ z' ∈ N.S b, Q.Runs (c, ((a.val, b.val), (z, z'))) τ S (N.Ψ a b z z')) →
  IsNetworkP (ofProcs Np Pf Q) c (ofNetwork N fun a => Np.n c a) P (B + 1) τ (S + 2) ∧ (ofNetwork N fun a => Np.n c a).value = N.value ∧ (ofNetwork N fun a => Np.n c a).U = N.U

end Eight.ViaGrouping
