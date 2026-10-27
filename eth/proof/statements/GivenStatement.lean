/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.Programs
public import Printed.CodingDefs

/-! # A «network on J with parameters P, B, τ», given by procedures: one definition (definitions and statements only)

Definition 2 of the paper, clause (iii): «an algorithm receives P, B and the numbers P_a, c_{a,b} as
input, and can decide membership in S_a and compute any value of W_a, Ψ_{a,b}, f_{a,b} with at most
τ operations.»
`Eight.SecNetworks.IsNetwork` (proof/networks/Eight/SecNetworks_Defs.lean) reads «at most τ
operations» as at most τ steps of four step machines. A step of a step machine is an arbitrary
function, so that definition alone bounds no cost; that the steps are computed in polynomial time,
and that the numbers are handed over in unary, are separate statements about the procedures.
Here the two are joined: `IsGivenNetwork` is Definition 2 with clause (iii) as one property. The two
sentences of the paper that say so of a network, «Both networks satisfy Definition 2 …» (proof of
Proposition 3) and «Definition 2 holds» (Section 6), are stated for it (`StGridGiven`,
`StFormulaGiven`), and Lemma 1 is applied to a network in this sense, with the number of operations
and the polynomial-time steps of the whole in one conclusion (`StOnGiven`).
proof/threesat/Given proves these three and from them proves Proposition 3, Section 8's sentence on
Clique(ℓ), «Cost» of Section 6 and Theorem 2, each in the form stated in the namespace `Printed`,
word for word.
This file has no proofs. -/

@[expose] public section

namespace Given

open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

variable {Q A C : Type}

/-- What makes a step of the procedures an operation that costs something: the four numbers (P, B,
the P_a, the c_{a,b}) are computed from the context in unary in polynomial time, and each of the
four machines with query access has polynomial-time steps
(`QueryMachines.QueryMachine.PolyTimeSteps`: start, own step, result, the query asked and the taking
of its answer are computed in polynomial time in the length of the state, on Mathlib's Turing
machines).
The procedures do not know the oracle, so the polynomials do not depend on it. -/
structure PolyTimeProcs [Enc Q] [Enc A] [Enc C] (Np : ProcsQ Q A C) : Prop where
  P : Unary Np.P
  B : Unary Np.B
  len : Unary fun p : C × ℕ => Np.len p.1 p.2
  cap : Unary fun p : C × ℕ × ℕ => Np.cap p.1 p.2.1 p.2.2
  mem : Np.mem.PolyTimeSteps
  W : Np.W.PolyTimeSteps
  Ψ : Np.Ψ.PolyTimeSteps
  f : Np.f.PolyTimeSteps

/-- **Definition 2**, all clauses as one property: N is a network on [g] with parameters P, B, τ,
given by the procedures Np in the context c, where the procedures may query the oracle O.
First conjunct (`Eight.SecNetworks.IsNetwork` of the procedures with the oracle built in):
* «Let P, B, τ ≥ 1 be integers», the sets S_a ⊆ {0,1}^{P_a} with «one fixed length P_a ≤ P», the
  symmetry of Ψ and c, the factorization of Ψ_{a,b} through c_{a,b} bits, «(i) Σ_{b ∈ J∖{a}} c_{a,b}
  ≤ P for every a ∈ J», «(ii) all values of all W_a, Ψ_{a,b}, f_{a,b} are below 2^B in absolute
  value» (`Net.Is`, and 1 ≤ τ);
* (iii) «an algorithm receives P, B and the numbers P_a, c_{a,b} as input»: the procedures give
  these numbers in the context c; «and can decide membership in S_a and compute any value of W_a,
  Ψ_{a,b}, f_{a,b} with at most τ operations»: each of the four machines answers within τ steps when
  the oracle is built in, that is, within τ operations, an own step and a query to O each counted as
  one (`QueryMachines.StClose`), on states of size at most S.
Second conjunct (`PolyTimeProcs`): these operations are polynomial-time steps, uniformly in the
oracle, and the numbers are handed over in unary. With the bound S on the states this makes clause (iii)
a bound on cost: τ operations, each polynomial in S.
Not in the print: the bound S (the paper counts operations on words and bounds no memory), the
context c, and the oracle. A network may be given by procedures that themselves query something. For
Proposition 3 these are the tables of the larger clique; Section 8 says of the recursion: «a query
to W̃_γ is answered by evaluating the sum in Lemma 1, which in turn queries the tables one level
up». Procedures that are step machines are the case without queries (`ofProcs`, `noTable`). -/
def IsGivenNetwork [Enc Q] [Enc A] [Enc C] {g : ℕ} (Np : ProcsQ Q A C) (O : Q → Option A) (c : C) (N : Net g) (P B τ S : ℕ) : Prop :=
  SecNetworks.IsNetwork (Np.close O) c N P B τ S ∧ PolyTimeProcs Np

/-- Procedures that are step machines, as procedures with query access that ask nothing. -/
def ofProcs (Np : Procs C) : ProcsQ Unit Unit C :=
  { P := Np.P, B := Np.B, len := Np.len, cap := Np.cap, mem := QueryMachine.lift Np.mem, W := QueryMachine.lift Np.W, Ψ := QueryMachine.lift Np.Ψ, f := QueryMachine.lift Np.f }

/-- The oracle that answers nothing. -/
def noTable : Unit → Option Unit := fun _ => none

/-- **Lemma 1, applied to a network given in this sense.** Let NM do what Lemma 1 says for (K, e) on
networks on [g] (`Printed.ComputesNetworks`: each query of Definition 2(iii) is charged τ
operations). On a network given by Np with the oracle O, the machine `networkOn g NM Np` (NM is
handed the numbers; each of its queries is answered by running the procedure, which may query O)
has polynomial-time steps if NM has, and outputs the value within 3·C₁·2^{e(U + gP/K) + 2gP/K}(P +
B)^{C₁}·τ operations, an own step and a query to O each counted as one. (The 3: a query of NM takes
the at most τ operations of the procedure and two more.) The count of operations holds for every NM,
so the hypothesis on the steps of NM stands where it is used. -/
def StOnGiven : Prop := ∀ (NM : NetMachine) (C₁ g K : ℕ) (e : ℝ), ComputesNetworks NM C₁ g K e →
  ∀ (Q A C : Type) [Enc Q] [Enc A] [HasSize C] [Enc C] [Carried C] (Np : ProcsQ Q A C) (O : Q → Option A) (c : C) (N : Net g) (P B τ S : ℕ), IsGivenNetwork Np O c N P B τ S →
    (NM.PolyTimeSteps → (networkOn g NM Np).PolyTimeSteps) ∧
    ∃ T : ℕ, (networkOn g NM Np).Within O QueryMachine.unitCost c T (size c + C₁ * (P + B) ^ C₁ + S + 4) N.value ∧
      (T : ℝ) ≤ 3 * (C₁ * (2 : ℝ) ^ (e * ((N.U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ C₁) * τ

/-- **Proof of Proposition 3, «Two networks for each ι»: «Both networks satisfy Definition 2 with P =
g³λ (so gP = N), with B₁ = gB + g²λ + 1 in the role of B, and with τ = poly(B + λ)».** For g ≥ 1
there is a constant a such that, for every context c that holds λ ≥ 1 and B in unary, all tables
with |W_w| < 2^B of the clique on g² nodes and every y < (t + 1)^{|ℛ|}: the network
`levelNetP g tr λ y` (tr = false: rows; tr = true: columns) is a network with parameters g³λ, B₁,
a·(B + λ)^a,
given by `Printed.gridProcs g tr` in the context (c, y) with query access to the tables. -/
def StGridGiven : Prop := ∀ g : ℕ, 1 ≤ g → ∃ a : ℕ, ∀ (tr : Bool) (c : List Unit × List Unit) (lam B : ℕ) (W : ℕ → List Bool → ℤ) (y : ℕ), c.1.length = lam → c.2.length = B → 1 ≤ lam →
  (∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B) → y < (tOf lam + 1) ^ nRect g →
  IsGivenNetwork (gridProcs g tr) (tables (g * g) lam W) (c, y) (levelNetP g tr lam y (listTables (g * g) W)) (g ^ 3 * lam) (g * B + g ^ 2 * lam + 1) (a * (B + lam) ^ a)
    (size c + size (g * g) + g * g * (2 * lam + 2) + B + 3 + a * (size c + B + lam) ^ a + 2)

/-- **Section 6, «Definition 2 holds»**, of the network of Φ on g clusters: with P = max{1, 2k·m̄},
B = 1 and τ = 1, given by `Printed.formulaProcs g k`, step machines that ask nothing. -/
def StFormulaGiven : Prop := ∀ g : ℕ, 0 < g → ∀ (k : ℕ) (Φ : Fml),
  IsGivenNetwork (ofProcs (formulaProcs g k)) noTable Φ (satNet g k Φ) (satPf g k Φ) 1 1 (size Φ + 2 * g + 6 * (mu g Φ * k) + 8 + 2)

end Given
