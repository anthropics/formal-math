/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.Spec
public import StepMachines.Prog.Comb
public import Groundwork.Net.Colouring
public import Groundwork.Net.ColouringNet

/-! Programs for the rebalancing of networks (Lemma 1): the test `goodB` of a good colouring of the
g nodes with K colours, and the procedure `mergedM`,
which computes an entry of the table of one class by brute force over the states of the class, with
the plain functions they use and the values they compute.
A network has, at every node a, states z with integer weights W_a(z), and for every pair of nodes
labels θ of c_ab bits
(the capacity `Np.cap`) and factors f_ab(z,θ). Its value is the sum over all states of the product
of the weights
and of the interactions Ψ_ab(z,z') = Σ_θ f_ab(z,θ)·f_ba(z',θ).
A colouring of the g nodes with K colours is a number x < K^g (digit a in radix K = the colour of
a). -/

namespace Groundwork.Prog

open Finset Stepped

namespace NetE

variable {C : Type} (K g : ℕ) (Np : PNet C)

/-! ### The plain functions -/

/-- The colour of the node a. -/
@[expose] public def col (x a : ℕ) : ℕ := x / K ^ a % K

/-- The nodes of colour G, in increasing order. -/
@[expose] public def members (x G : ℕ) : List ℕ := (List.range g).filter fun a => col K x a == G

/-- The lengths of the states of the members of G. -/
@[expose] public def stLens (c : C) (x G : ℕ) : List ℕ := (members K g x G).map (Np.n c)

/-- The length of a state of the class G. -/
@[expose] public def stLen (c : C) (x G : ℕ) : ℕ := (stLens K g Np c x G).sum

/-- The state of the member a in the state z of the class G. -/
@[expose] public def zAt (c : C) (x G : ℕ) (z : List Bool) (a : ℕ) : List Bool :=
  (chunks (stLens K g Np c x G) z).getD ((members K g x G).idxOf a) []

/-- The pairs (a,b), a in G, b in G'. -/
@[expose] public def prs (x G G' : ℕ) : List (ℕ × ℕ) :=
  (members K g x G).flatMap fun a => (members K g x G').map fun b => (a, b)

/-- The lengths of the labels of these pairs. -/
@[expose] public def lbLens (c : C) (x G G' : ℕ) : List ℕ := (prs K g x G G').map fun p => Np.cap c p.1 p.2

/-- The capacity between the classes G and G'. -/
@[expose] public def lbLen (c : C) (x G G' : ℕ) : ℕ := (lbLens K g Np c x G G').sum

/-- The label of the pair p in the label θ of the classes G < G'. -/
@[expose] public def lAt (c : C) (x G G' : ℕ) (θ : List Bool) (p : ℕ × ℕ) : List Bool :=
  (chunks (lbLens K g Np c x G G') θ).getD ((prs K g x G G').idxOf p) []

/-- The number of label bits at the node a: Σ_{b≠a} c_ab. -/
@[expose] public def rowSum (c : C) (a : ℕ) : ℕ := (((List.range g).filter fun b => b != a).map (Np.cap c a)).sum

/-- U: the sum of c_ab over the ordered pairs a ≠ b. -/
@[expose] public def Uc (c : C) : ℕ := ((List.range g).map (rowSum g Np c)).sum

/-- The largest row sum. -/
@[expose] public def Pc (c : C) : ℕ := ((List.range g).map (rowSum g Np c)).foldr max 0

/-- β: the bound on the label bits between two classes in a good colouring. -/
@[expose] public def betaC (c : C) : ℕ := Colouring.beta K g (Uc g Np c) (Pc g Np c)

/-- Is the colouring x good? Every class has fewer than 2g/K members and any two classes share at
most β label bits. -/
@[expose] public def goodB (cx : C × ℕ) : Bool :=
  ((List.range K).all fun G => decide (K * (members K g cx.2 G).length < 2 * g)) &&
  (List.range K).all fun G => (List.range K).all fun G' =>
    G == G' || decide (lbLen K g Np cx.1 cx.2 G G' ≤ betaC K g Np cx.1)

/-- The input of the procedure of the merged instance: ((c, x), (G, θs)). -/
public abbrev X0 (C : Type) : Type := (C × ℕ) × IQ

/-- In every label at G the bits after the first `lbLen` (the length of a label of the two classes)
are 0. The length of the label
is not tested: it is a hypothesis of `validB_iff`. -/
@[expose] public def validB (u : X0 C) : Bool :=
  (List.range K).all fun G' => G' == u.2.1 ||
    (((u.2.2.getD G' []).drop (lbLen K g Np u.1.1 u.1.2 (min u.2.1 G') (max u.2.1 G'))).all fun b => !b)

/-- The number of states of the class. -/
@[expose] public def nStates (u : X0 C) : ℕ := 2 ^ stLen K g Np u.1.1 u.1.2 u.2.1

/-- The state of the class with number y. -/
@[expose] public def zOf (u : X0 C × ℕ) : List Bool := toWord (stLen K g Np u.1.1.1 u.1.1.2 u.1.2.1) u.2

/-- The state of the node a. -/
@[expose] public def zA (u : X0 C × ℕ) (a : ℕ) : List Bool :=
  zAt K g Np u.1.1.1 u.1.1.2 u.1.2.1 (zOf K g Np u) a

/-- The label of {a,b}, a in G, b in another class. -/
@[expose] public def labOf (u : X0 C) (a b : ℕ) : List Bool :=
  if u.2.1 < col K u.1.2 b then lAt K g Np u.1.1 u.1.2 u.2.1 (col K u.1.2 b) (u.2.2.getD (col K u.1.2 b) []) (a, b)
  else lAt K g Np u.1.1 u.1.2 (col K u.1.2 b) u.2.1 (u.2.2.getD (col K u.1.2 b) []) (b, a)

/-- The factor number i = a*g + b of the product is 1: a is not in G, or b ≤ a is another member of
G. -/
@[expose] public def isOne (u : (X0 C × ℕ) × ℕ) : Bool :=
  col K u.1.1.1.2 (u.2 / g) != u.1.1.2.1 ||
    (col K u.1.1.1.2 (u.2 % g) == u.1.1.2.1 && decide (u.2 % g < u.2 / g))

/-- It is the weight of a. -/
@[expose] public def isW (u : (X0 C × ℕ) × ℕ) : Bool := u.2 / g == u.2 % g

/-- It is the interaction of two members. -/
@[expose] public def isPsi (u : (X0 C × ℕ) × ℕ) : Bool := col K u.1.1.1.2 (u.2 % g) == u.1.1.2.1

/-- The query for the weight of a at its state, i = a*g + a. -/
@[expose] public def qW (u : (X0 C × ℕ) × ℕ) : C × WQ := (u.1.1.1.1, (u.2 / g, zA K g Np u.1 (u.2 / g)))

/-- The query for f_ab at the state of a and the label of {a,b}, b in another class. -/
@[expose] public def qF (u : (X0 C × ℕ) × ℕ) : C × FQ :=
  (u.1.1.1.1, ((u.2 / g, u.2 % g), (zA K g Np u.1 (u.2 / g), labOf K g Np u.1.1 (u.2 / g) (u.2 % g))))

/-- The number of labels of the pair (a,b), i = a*g + b. -/
@[expose] public def nLab (u : (X0 C × ℕ) × ℕ) : ℕ := 2 ^ Np.cap u.1.1.1.1 (u.2 / g) (u.2 % g)

/-- The query for f_ab at the state of a and the label with number y. -/
@[expose] public def qP1 (u : ((X0 C × ℕ) × ℕ) × ℕ) : C × FQ :=
  (u.1.1.1.1.1, ((u.1.2 / g, u.1.2 % g),
    (zA K g Np u.1.1 (u.1.2 / g), toWord (Np.cap u.1.1.1.1.1 (u.1.2 / g) (u.1.2 % g)) u.2)))

/-- The query for f_ba at the state of b and the same label. -/
@[expose] public def qP2 (u : ((X0 C × ℕ) × ℕ) × ℕ) : C × FQ :=
  (u.1.1.1.1.1, ((u.1.2 % g, u.1.2 / g),
    (zA K g Np u.1.1 (u.1.2 % g), toWord (Np.cap u.1.1.1.1.1 (u.1.2 / g) (u.1.2 % g)) u.2)))

/-- The number of factors of the product: one for each i = a*g + b. -/
@[expose] public def nPairs (_ : X0 C × ℕ) : ℕ := g * g

/-- The number of colourings. -/
@[expose] public def nCol (_ : C) : ℕ := K ^ g

/-- The constant result 0. -/
@[expose] public def zeroOf (_ : C) : ℤ := 0

/-! ### The programs -/

variable [HasSize C]

/-- Ψ_ab(z_a,z_b) by its definition. -/
@[expose] public def psiM : Stepped ((X0 C × ℕ) × ℕ) ℤ :=
  sumRange (nLab g Np) (mul2 (mapIn (qP1 K g Np) Np.f) (mapIn (qP2 K g Np) Np.f))

/-- The factor number i. -/
@[expose] public def termM : Stepped ((X0 C × ℕ) × ℕ) ℤ :=
  ite (isOne K g) (const 1) (ite (isW g) (mapIn (qW K g Np) Np.W)
    (ite (isPsi K g) (psiM K g Np) (mapIn (qF K g Np) Np.f)))

/-- The procedure of the merged instance: the entry of the tensor of the class G at the labels θs,
by brute force over
the states of the class. -/
@[expose] public def mergedM : Stepped (X0 C) ℤ :=
  ite (validB K g Np) (sumRange (nStates K g Np) (prodRange (nPairs g) (termM K g Np))) (const 0)

/-! ### What the programs compute -/

omit [HasSize C]

/-- The weights of a network on Fin g, as a function of numbers. -/
@[expose] public def valW {g : ℕ} (N : Network (Fin g) (List Bool) (List Bool)) (a : ℕ) (z : List Bool) : ℤ :=
  if h : a < g then N.W ⟨a, h⟩ z else 0

/-- The factors of a network on Fin g, as a function of numbers. -/
@[expose] public def valF {g : ℕ} (N : Network (Fin g) (List Bool) (List Bool)) (a b : ℕ) (z θ : List Bool) : ℤ :=
  if h : a < g ∧ b < g then N.f ⟨a, h.1⟩ ⟨b, h.2⟩ z θ else 0

/-- The result of termM. -/
@[expose] public def termVal (N : Network (Fin g) (List Bool) (List Bool)) (u : (X0 C × ℕ) × ℕ) : ℤ :=
  if isOne K g u then 1
  else if isW g u then valW N (u.2 / g) (zA K g Np u.1 (u.2 / g))
  else if isPsi K g u then
    ∑ y ∈ range (nLab g Np u),
      valF N (u.2 / g) (u.2 % g) (zA K g Np u.1 (u.2 / g)) (toWord (Np.cap u.1.1.1.1 (u.2 / g) (u.2 % g)) y) *
      valF N (u.2 % g) (u.2 / g) (zA K g Np u.1 (u.2 % g)) (toWord (Np.cap u.1.1.1.1 (u.2 / g) (u.2 % g)) y)
  else valF N (u.2 / g) (u.2 % g) (zA K g Np u.1 (u.2 / g)) (labOf K g Np u.1.1 (u.2 / g) (u.2 % g))

/-- The result of mergedM. -/
@[expose] public def mergedVal (N : Network (Fin g) (List Bool) (List Bool)) (u : X0 C) : ℤ :=
  if validB K g Np u then ∑ y ∈ range (nStates K g Np u), ∏ i ∈ range (g * g), termVal K g Np N ((u, y), i) else 0

end NetE

end Groundwork.Prog
