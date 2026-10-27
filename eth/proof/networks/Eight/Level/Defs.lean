/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.SecCrossing_PolyDefs
public import SingleBitPieces.SecNetworks_LemGrouping
public import Paper.SecPseudocode_Algorithm
public import ClauseBound.Alg.Grid

/-! # Proposition 3 through Lemma 2 from the eight-square identity: definitions and interface statements

One level of the recursion, for the pieces of Lemma 2 from the eight-square identity, is built on
the functions A_0, …, A_t, t = ⌈λ/3⌉, of `EightSquareStatement.lean` and their factorizations
`Eight.fTop`, `Eight.fBot` (one step per value): for every
ι : ℛ → {0, …, t} the network with the smaller total, and the final division by 2^{t|ℛ|}. ρ = 11/12
(`Eight.rho`).
The networks of a grid on words, for any family of pieces given by plain functions, are those of
proof/rates/ClauseBound/Alg/GridNet.lean (`ClauseBound.Alg.GridNet.gridN`), taken at p = d = g. The
procedure for the weights of a row or a column is
`Groundwork.Prog.sideWP`, which does not depend on the pieces.
At the end: the numbers e_ℓ of Section 8 («The algorithm in pseudocode»).
This file has definitions and propositions `St… : Prop` only; nothing is proved or assumed here. -/

@[expose] public section

namespace Eight.Level

open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped

/-- The number of functions ι : ℛ → {0, …, t}: (t + 1)^{|ℛ|}. -/
def numPat8 {C : Type} (g : ℕ) (lam : C → ℕ) (c : C) : ℕ := (tOf (lam c) + 1) ^ nRect g

/-- The row network (tr = false) or the column network (tr = true) of ι, on words; ι is written by
the number y in base t + 1. -/
noncomputable def netOfι (g : ℕ) (tr : Bool) (lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) : Network (Fin (nParts g g tr)) (List Bool) (List Bool) :=
  gridN eightF [] g g tr 0 lam y Rm

/-- The same network given by procedures: a weight is computed with g queries to the tables of the
clique, a value of a factor in one step. -/
def levelNet (g : ℕ) (tr : Bool) : NetFormer := fun lam R =>
  { n := fun c _ => nMemb g g tr * (g * g) * lam c.1
    cap := fun c a b => capG eightF g g tr 0 (lam c.1) c.2 a b
    W := sideWP g tr lam R
    f := ofFun fun x => gridFf eightF [] g g tr 0 (lam x.1.1) x.1.2 x.2 }

/-- «Apply Lemma 1 to the network with the smaller total»: is it the row network? -/
def useRowP {C : Type} (g : ℕ) (lam : C → ℕ) (x : C × ℕ) : Bool :=
  decide (totalG eightF g g false 0 (lam x.1) x.2 ≤ totalG eightF g g true 0 (lam x.1) x.2)

/-- Procedure CLIQUE of Algorithm 1 at a level above 0: for every ι : ℛ → {0, …, ⌈λ/3⌉}, the
algorithm `NE` for networks on [g] is run on the row network or on the column network of ι,
whichever has the smaller total; the values are
added up, and the sum is divided by 2^{⌈λ/3⌉|ℛ|}. -/
def levelAlg (g : ℕ) (NE : NetEvaluator) : Evaluator :=
  ⟨fun lam R => bind (sumRange (numPat8 g lam) (Stepped.ite (useRowP g lam) (NE.app (levelNet g false lam R)) (NE.app (levelNet g true lam R))))
    (ofFun fun p => p.2 / ((2 ^ (tOf (lam p.1) * nRect g) : ℕ) : ℤ))⟩

/-! ### Interface statements -/

/-- Lemma 2 in the form that the networks of a grid need. -/
def StPieces : Prop := ∀ lam : ℕ, 1 ≤ lam →
  (∀ x y u v : Bits lam, ∑ i ∈ Finset.range (tOf lam + 1), A lam i x y u v = 2 ^ tOf lam * Pieces.cross x y u v) ∧
    CutsOK eightF [] 0 lam fun i => A lam i

/-- The procedures present the network, within a·(B + λ)^a·t steps, t the cost of one query to the
tables of the clique (not ⌈λ/3⌉), and size S + a·(size c + B + λ)^a (the paper: τ = poly(B + λ)). -/
def StPresents : Prop := ∀ (g : ℕ) (tr : Bool), ∃ a : ℕ, ∀ (C : Type) [HasSize C] (lam : C → ℕ) (R : Stepped (C × IQ) ℤ) (c : C) (B t S : ℕ)
  (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ), 1 ≤ lam c → 1 ≤ t → y < (tOf (lam c) + 1) ^ nRect g → ServesInst R c (lam c) B t S Rm →
  (levelNet g tr lam R).Presents (c, y) (netOfι g tr (lam c) y Rm) (a * (B + lam c) ^ a * t) (S + a * (size c + B + lam c) ^ a)

/-- The procedures have polynomial-time steps. -/
def StNetKeeps : Prop := ∀ (g : ℕ) (tr : Bool), NetFormer.Keeps (levelNet g tr)

/-- The display «the smaller total»: min(U_row, U_col) ≤ N(ρ + 1/g) + 2g⁴, N = g⁴λ; N/g is written
g³λ. -/
def StMin : Prop := ∀ g lam y : ℕ, 1 ≤ lam →
  ((min (totalG eightF g g false 0 lam y) (totalG eightF g g true 0 lam y) : ℕ) : ℝ) ≤ rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4

/-- «Cost»: an algorithm for networks on [g] with the exponent of Lemma 1 gives an algorithm for
cliques on g² nodes with the exponent (ρ + 2/K)e + 2/K. -/
def StLevel : Prop := ∀ (K g : ℕ) (e : ℝ) (NE : NetEvaluator), 2 ≤ K → K ≤ g → 0 ≤ e → NE.Correct g K e (e + 2) →
  (levelAlg g NE).Correct (g * g) ((rho + 2 / K) * e + 2 / K)

/-- The algorithm of a level has polynomial-time steps if that for networks has. -/
def StLevelKeeps : Prop := ∀ (g : ℕ) (NE : NetEvaluator), NE.Keeps → (levelAlg g NE).Keeps

/-! ### The numbers e_ℓ of Section 8 -/

/-- e_ℓ of the first display of Section 8, with ρ = 11/12: e₀ = 1/2, e_{ℓ+1} = (ρ + 2/K_ℓ)·e_ℓ +
2/K_ℓ. K_ℓ is `Paper.levelK`: K₀ = 64, K_{ℓ+1} = 9K_ℓ¹⁶. -/
noncomputable def levelE : ℕ → ℝ
  | 0 => 1 / 2
  | ℓ + 1 => (rho + 2 / Paper.levelK ℓ) * levelE ℓ + 2 / Paper.levelK ℓ


open Paper

end Eight.Level
