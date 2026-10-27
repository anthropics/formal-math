/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.ViaGrouping.Defs

/-! # One level of the recursion on an algorithm for networks in the printed form (definitions and statements only)

proof/networks/Eight/Level/Defs.lean builds one level of the recursion (Proposition 3; procedure
CLIQUE of Algorithm 1 above level 0) on an algorithm for networks in the form of
`Groundwork.Prog.NetEvaluator`, which is given no procedure for Ψ and no P. Here the same level is
built
on an algorithm `NA : SecNetworks.NetAlg` for networks as Definition 2 prints them. The row network
and the column network of ι are the same (`Eight.Level.netOfι`, `Eight.Level.levelNet`); the
algorithm is given in addition
* P = g³λ, the number of the sentence «Both networks satisfy Definition 2 with P = g³λ» of the proof
  of Proposition 3, and
* a procedure for Ψ_{a,b}: a plain function `psi λ y ((a, b), (z, z'))`, one step per value.
The function for Ψ is a parameter here, one for the rows and one for the columns; `StPsiOK` and
`StPsiPoly` say what is asked of it.
The loop over ι, the choice of the network with the smaller total and the final division by 2^{t|ℛ|}
are those of `Eight.Level.levelAlg`.
This file has definitions and propositions `St… : Prop` only; nothing is proved or assumed here. -/

@[expose] public section

namespace Eight.ViaGrouping

open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped Eight.SecNetworks Eight.Level

/-! ## The algorithm of one level -/

/-- The row network (tr = false) or the column network (tr = true) of ι, given as Definition 2(iii)
asks: the procedures of `Eight.Level.levelNet`, the number P = g³λ, and the function `psi` for Ψ,
one step per value. Every string of g³λ bits is a setting, so the test for membership says yes; B is
not given
(see `ofProcs`). The context is (c, y); y is the number of ι. -/
def levelProcs {C : Type} [HasSize C] (g : ℕ) (tr : Bool) (psi : ℕ → ℕ → PsiQ → ℤ) (lam : C → ℕ) (R : Stepped (C × IQ) ℤ) : Procs (C × ℕ) :=
  ofProcs (levelNet g tr lam R) (fun c => g ^ 3 * lam c.1) (ofFun fun x => psi (lam x.1.1) x.1.2 x.2)

/-- The row network (tr = false) or the column network (tr = true) of ι as the data of Definition 2:
the network `Eight.Level.netOfι` that Algorithm 1 runs, with Ψ_{a,a'} the sum that its factorization
defines and P_a = g³λ for every a (in the paper P_a = g(g² − 1)λ; the λ bits more per grid point are
the dummy string of proof/networks/Eight/SecLevel_Grid.lean). It has g nodes
(`nParts g g tr` is g). -/
noncomputable def levelNetP (g : ℕ) (tr : Bool) (lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) : Net (nParts g g tr) :=
  ofNetwork (netOfι g tr lam y Rm) fun _ => g ^ 3 * lam

/-- Procedure CLIQUE of Algorithm 1 at a level above 0, on an algorithm `NA` for networks in the
printed form: for every ι : ℛ → {0, …, ⌈λ/3⌉}, `NA` is run on the row network or on the column
network of ι, whichever has the smaller total; the values are
added up, and the sum is divided by 2^{⌈λ/3⌉|ℛ|}. `psiR`, `psiC` compute Ψ for the row networks and
for the column networks. -/
def levelAlgP (g : ℕ) (psiR psiC : ℕ → ℕ → PsiQ → ℤ) (NA : NetAlg) : Evaluator :=
  ⟨fun lam R => bind (sumRange (numPat8 g lam) (Stepped.ite (useRowP g lam) (NA.app (levelProcs g false psiR lam R)) (NA.app (levelProcs g true psiC lam R))))
    (ofFun fun p => p.2 / ((2 ^ (tOf (lam p.1) * nRect g) : ℕ) : ℤ))⟩

/-! ## Interface statements -/

/-- The function `psi` computes Ψ_{a,b} of the network of ι on settings: for λ ≥ 1, y < (t + 1)^{|ℛ|},
a ≠ b, z ∈ S_a, z' ∈ S_b. (Ψ does not depend on the tables of the clique.) -/
def StPsiOK (g : ℕ) (tr : Bool) (psi : ℕ → ℕ → PsiQ → ℤ) : Prop :=
  ∀ (lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)), 1 ≤ lam → y < (tOf lam + 1) ^ nRect g → ∀ a b : Fin (nParts g g tr), a ≠ b →
    ∀ z ∈ (netOfι g tr lam y Rm).S a, ∀ z' ∈ (netOfι g tr lam y Rm).S b, psi lam y ((a.val, b.val), (z, z')) = (netOfι g tr lam y Rm).Ψ a b z z'

/-- The function `psi` is computed in polynomial time, for λ in unary. -/
def StPsiPoly (psi : ℕ → ℕ → PsiQ → ℤ) : Prop :=
  ∀ (C : Type) [Enc C] (lam : C → ℕ), Unary lam → PolyT fun x : (C × ℕ) × PsiQ => psi (lam x.1.1) x.1.2 x.2

/-- The bound of Lemma 1 read on a network given as a `PNet`: if NA has the bound of Lemma 1
(`Correct`), then on the procedures of such a network, together with a function that gives P and a
procedure Q that computes its Ψ within t steps, NA has the
bound that `Groundwork.Prog.NetEvaluator.Correct` states. -/
def StOfPaperNetwork : Prop := ∀ (NA : NetAlg) (g K : ℕ) (ε b : ℝ), Correct NA g K ε b →
  ∃ A : ℕ, ∀ (C : Type) [HasSize C] (Np : PNet C) (Pf : C → ℕ) (Q : Stepped (C × PsiQ) ℤ) (c : C) (N : Network (Fin g) (List Bool) (List Bool)) (P B t S : ℕ),
    1 ≤ P → 1 ≤ t → Np.Presents c N t S → N.Sized P B → Pf c = P →
    (∀ a b : Fin g, a ≠ b → ∀ z ∈ N.S a, ∀ z' ∈ N.S b, Q.Runs (c, ((a.val, b.val), (z, z'))) t S (N.Ψ a b z z')) →
    ∃ T : ℕ, (NA.app (ofProcs Np Pf Q)).Runs c T (S + A * (size c + P + B) ^ A) N.value ∧
      (T : ℝ) ≤ A * (2 : ℝ) ^ (ε * (N.U : ℝ) + b * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ A * t

/-- «Cost»: an algorithm for networks on [g], in the printed form, with the exponent of Lemma 1
gives an algorithm for cliques on g² nodes with the exponent (ρ + 2/K)e + 2/K. -/
def StLevelP : Prop := ∀ (K g : ℕ) (e : ℝ) (psiR psiC : ℕ → ℕ → PsiQ → ℤ) (NA : NetAlg), 2 ≤ K → K ≤ g → 0 ≤ e → StPsiOK g false psiR → StPsiOK g true psiC →
  Correct NA g K e (e + 2) → (levelAlgP g psiR psiC NA).Correct (g * g) ((rho + 2 / K) * e + 2 / K)

/-- The algorithm of a level has polynomial-time steps if that for networks has and the two
functions for Ψ are computed in polynomial time. -/
def StLevelKeepsP : Prop := ∀ (g : ℕ) (psiR psiC : ℕ → ℕ → PsiQ → ℤ) (NA : NetAlg), StPsiPoly psiR → StPsiPoly psiC → AlgKeeps NA → (levelAlgP g psiR psiC NA).Keeps

end Eight.ViaGrouping
