/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Data
public import PaddedDescent.Params
public import StepMachines.Prog.NetProg
public import StepMachines.Prog.Side
public import StepMachines.Prog.GridDefs
public import StepMachines.Prog.CountNet
public import StepMachines.Prog.Sat
public import StepMachines.Math.SparsifyProg
public import StepMachines.Math.SparsifyTree
public import SparsifyWidthK.Defs
public import SparsifyWidthK.DefsProg
public import PaddedDescent.F.MarkNet

/-! # The definitions, part 3: the program

The pure function `A : List Bool × U → Bool` that decides 3-SAT when the pad is long enough, and, at
the end of the file, the predicates (`Bud`, `Fits`,
`Chain`, `NetFits`, `MarkFits`) and bounds (`lamG`, `Ub`, `Pb`, `layLen`, `schedLen`, `stackLen`) in
which the arithmetic says that a pad is long enough. K, g, the label lengths and the list of
levels are data, in unary.

There are two rebalancings. At the top, a network of marks (F/MarkNet.lean) on 3K⁸ nodes is
rebalanced by `rebalF`, with the label length `betaC` and the test `goodB` of
StepMachines/Prog/NetProg.lean. At the levels below, where any two nodes of a network share a
bounded number of label bits, `rebalG` works on a grid of side
g = K·L with a small factor L; its label length is handed in. The sparsification tree is that of
proof/sparsification/SparsifyWidthK at width 3, whose leaves have at most (2 + 8τ + 96τ²)·n clauses.
The clauses of a leaf are divided into layers (F/MarkMath.lean), and the number of its satisfying
assignments is one evaluation `evalF`: a sum of values of
networks of marks, whose number of shared label bits grows only with the square of the logarithm of
the number of clauses per variable. -/

@[expose] public section

namespace PaddedDescent.F

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Prog.Count Groundwork.Grid

/-! ### The rebalancing on explicit data -/

/-- The counterpart of `NetE.termM` / `NetE.termVal` for an explicit `FNet`, with its sums taken
over the pad. -/
def termF {C : Type} (pad : U) (K g : ℕ) (F : FNet C) (u : (X0 C × ℕ) × ℕ) : ℤ :=
  bif isOne K g u then 1
  else bif isW g u then F.W (qW K g F.toP u)
  else bif isPsi K g u then sumF (nLab g F.toP u) pad fun y => F.f (qP1 K g F.toP (u, y)) * F.f (qP2 K g F.toP (u, y))
  else F.f (qF K g F.toP u)

/-- The counterpart of `NetE.mergedM` / `NetE.mergedVal` for an explicit `FNet`, with its sums taken
over the pad: one entry of the merged instance. -/
def mergedF {C : Type} (pad : U) (K g : ℕ) (F : FNet C) (u : X0 C) : ℤ :=
  bif validB K g F.toP u then sumF (nStates K g F.toP u) pad fun y => prodL (g * g) fun i => termF pad K g F ((u, y), i)
  else 0

/-- From a network on g nodes, given by plain functions in the context c, to the explicit instance
on K nodes: the first good colouring,
the new label length (in unary), the whole new table. `none` if no good colouring is found. -/
def rebalF {C : Type} (pad : U) (K g : ℕ) (F : FNet C) (c : C) : Option PInst :=
  ((rng pad (K ^ g)).find? fun x => goodB K g F.toP (c, x)).map fun x =>
    (List.replicate (betaC K g F.toP c) (), tabulate pad K (betaC K g F.toP c) fun q => mergedF pad K g F ((c, x), q))

/-- Is the colouring x good for the label length β? Every class has fewer than 2g/K members and any
two classes share at most β label bits. This is
`NetE.goodB` with β in place of `betaC`. -/
def goodG {C : Type} (K g : ℕ) (Np : PNet C) (β : ℕ) (cx : C × ℕ) : Bool :=
  ((List.range K).all fun G => decide (K * (members K g cx.2 G).length < 2 * g)) &&
  (List.range K).all fun G => (List.range K).all fun G' => G == G' || decide (lbLen K g Np cx.1 cx.2 G G' ≤ β)

/-- `rebalF` with the new label length β handed in: the first colouring that is good for β, β in
unary, the whole new table. -/
def rebalG {C : Type} (pad : U) (K g β : ℕ) (F : FNet C) (c : C) : Option PInst :=
  ((rng pad (K ^ g)).find? fun x => goodG K g F.toP β (c, x)).map fun x =>
    (List.replicate β (), tabulate pad K β fun q => mergedF pad K g F ((c, x), q))

/-! ### The network of one term of one level of the recursion, read off an explicit table -/

def botF (pad : U) (tr : Bool) (i : ℕ) (x y w : List Bool) : ℤ :=
  sumF (2 ^ x.length) pad fun s =>
    if (toWord x.length s).count true = i then prodL x.length (fun k => botTerm tr x y w s k) else 0

/-- The counterpart of `Grid.cutW` on explicit words, with its sums taken over the pad. -/
def cutF (pad : U) (tr top : Bool) (i : ℕ) (x y w : List Bool) : ℤ :=
  if validW x.length (sideCnt tr x.length i) w = true then
    if top = true then prodL x.length (topTerm tr x y w) else botF pad tr i x y w
  else 0

/-- The counterpart of `Grid.sideItem` on explicit words, with its sums taken over the pad. -/
def itemF (pad : U) (g : ℕ) (tr : Bool) (n y a b : ℕ) (z θ : List Bool) (i i' : ℕ) : ℤ :=
  cutF pad tr (decide (a < b)) (rectDig g tr n y (tri (min a b) (max a b)) (tri i i'))
    (he g n z i (node g tr b i')) (he g n z i' (node g tr b i)) (sideChunk g tr n y a b θ (tri i i'))

/-- ((pad, g in unary, tr), (ℓ in unary, pattern y, table)); tr = false: rows merged, tr = true:
columns merged. -/
abbrev SideCtx := (U × U × Bool) × (U × ℕ × Tab)

/-- The counterpart of `sideWP` / `sideWv`, read off an explicit table. -/
def sideWF (g : ℕ) (tr : Bool) (ℓ y : ℕ) (T : Tab) (q : WQ) : ℤ :=
  bif sideChk g tr (fun n : ℕ => n) ((ℓ, y), q) then
    prodL g fun i => look T (node g tr q.1 i, (List.range (g * g)).map (sideLabels g tr ℓ q.1 q.2 i))
  else 0

/-- The counterpart of `sideFv` on explicit data, with its sums taken over the pad. -/
def sideFF (pad : U) (g : ℕ) (tr : Bool) (ℓ y : ℕ) (q : FQ) : ℤ :=
  bif sideEdges g tr (fun n : ℕ => n) ((ℓ, y), q) then
    prodL (g * g) fun j => if j / g < j % g then itemF pad g tr ℓ y q.1.1 q.1.2 q.2.1 q.2.2 (j / g) (j % g) else 1
  else 0

def sideF : FNet SideCtx where
  n c _ := c.1.2.1.length ^ 3 * c.2.1.length
  cap c a b := sideCap c.1.2.1.length c.1.2.2 c.2.1.length c.2.2.1 a b
  W x := sideWF x.1.1.2.1.length x.1.1.2.2 x.1.2.1.length x.1.2.2.1 x.1.2.2.2 x.2
  f x := sideFF x.1.1.1 x.1.1.2.1.length x.1.1.2.2 x.1.2.1.length x.1.2.2.1 x.2

/-! ### One level, all levels, the bottom -/

/-- The context of the side network for the instance I on g·g nodes and the pattern y: the cheaper
side. -/
def sideCtx (pad : U) (gu : U) (I : PInst) (y : ℕ) : SideCtx :=
  ((pad, gu, decide (priceCol gu.length I.1.length y < priceRow gu.length I.1.length y)), (I.1, y, I.2))

/-- An upper bound for the number of label bits that two nodes of a side network share
(`Grid.sideCap_le`). -/
def capM (g lam : ℕ) : ℕ := g * lam + 2 * g ^ 2 * lam

/-- An upper bound for U of the cheaper side network. -/
def Ubar (g lam : ℕ) : ℕ := g ^ 2 * (g - 1) * lam + (717 * g ^ 4 * lam) / 800 + g ^ 4 / 2 + 1

/-- The label length one level down: U/K² with the relative error of the colouring, rounded up. -/
def lamNext (K g lam : ℕ) : ℕ := (Dcol * Ubar g lam + 3 * g ^ 2 * capM g lam) / (Dcol * K ^ 2) + 1

/-- The instance on K nodes that the pattern y of the instance I on g·g nodes leads to. -/
def childF (pad : U) (L : Lvl) (I : PInst) (y : ℕ) : Option PInst :=
  rebalG pad L.1.length L.2.length (lamNext L.1.length L.2.length I.1.length) sideF (sideCtx pad L.2 I y)

/-- One level: an instance on g·g nodes becomes the list of its (ℓ+1)^R children on K nodes; Z is
the sum of theirs. -/
def expand (pad : U) (L : Lvl) (I : PInst) : List PInst :=
  (rng pad ((I.1.length + 1) ^ nRect L.2.length)).filterMap (childF pad L I)

/-- All levels, breadth first: the work list after the steps of sched. -/
def descend (pad : U) (sched : List Lvl) (I : PInst) : List PInst :=
  sched.foldl (fun w L => cap pad [] (w.flatMap (expand pad L))) (cap pad [] [I])

/-- Brute force on K nodes: the counterpart of `brute`, read off an explicit table, with the sum
taken over the pad. -/
def bruteF (pad : U) (K : ℕ) (I : PInst) : ℤ :=
  sumF (2 ^ (K * (K - 1) / 2 * I.1.length)) pad fun y =>
    prodL K fun v => look I.2 (query0 K I.1.length [] (toWord (K * (K - 1) / 2 * I.1.length) y) v)

/-! ### The schedule -/

/-- 3K⁸ in unary: the number of nodes of the network of a formula. -/
def gU (Ku : U) : U := List.replicate (3 * Ku.length ^ 8) ()

/-- g = K·L in unary: the side of the grid at a level. -/
def mulU (Ku Lu : U) : U := List.replicate (Ku.length * Lu.length) ()

/-- g² in unary. -/
def sqU (gu : U) : U := List.replicate (gu.length * gu.length) ()

/-- After t rounds: ([(K_{t−1}, g_{t−1}), …, (K₀, g₀)], K_t, L_t), with K₀ = 256, g_j = K_j·L_j,
K_{j+1} = g_j², L_{j+1} = 2·L_j. -/
def schedF (pad : U) (t : ℕ) : List Lvl × U × U :=
  (List.replicate t ()).foldl
    (fun st _ => cap pad ([], [], []) ((st.2.1, mulU st.2.1 st.2.2) :: st.1, sqU (mulU st.2.1 st.2.2), st.2.2 ++ st.2.2))
    (cap pad ([], [], []) ([], List.replicate 256 (), List.replicate (Lseq 0) ()))

/-! ### One sparse formula, the sparsification tree, the whole function -/

/-- The top rebalancing, all levels and exhaustive search at the bottom, for any network given by
plain functions: the value of the network, if the pad is
long enough. S = (steps of the schedule, K_t). -/
def valF {C : Type} (pad : U) (S : List Lvl × U) (F : FNet C) (c : C) : ℤ :=
  (rebalF pad S.2.length (gU S.2).length F c).elim 0 fun I => ((descend pad S.1 I).map (bruteF pad 256)).sum

/-- One evaluation: the sum of the values of the networks of marks over the admissible profiles. It
is `Mark.trunc n w Ls` under the hypotheses of `StEval`.
p = (n, w, β, b), in unary: number of variables, cap, and the two parameters of the code of the
labels. k is the width of the clauses. -/
def evalF (k : ℕ) (pad : U) (S : List Lvl × U) (p : U × U × U × U) (Ls : List Fml) : ℤ :=
  sumF (Mark.nProf (gU S.2).length (Mark.cls Ls).length Ls.length) pad fun y =>
    bif Mark.adm k (gU S.2).length p.1.length p.2.1.length Ls y then valF pad S Mark.markF ((gU S.2, p.1, p.2.2.1, p.2.2.2), (Ls, y)) else 0

/-- The clauses of ψ, placed one after the other into R + 1 layers; every decision takes two
evaluations. -/
def layersF (k : ℕ) (pad : U) (S : List Lvl × U) (p : U × U × U × U) (R : ℕ) (ψ : Fml) : List Fml :=
  ψ.foldl (fun Ls C => cap pad [] (Mark.placeE (evalF k pad S p) p.2.1.length Ls C)) (cap pad [] (List.replicate (R + 1) []))

/-- The number of assignments of the n variables that satisfy ψ, under the hypotheses of `StCountM`. -/
def countM (k : ℕ) (pad : U) (S : List Lvl × U) (p : U × U × U × U) (R : ℕ) (ψ : Fml) : ℤ :=
  evalF k pad S p ([] :: layersF k pad S p R ψ)

/-- The parameters (n, w, β, b) of the evaluations for n variables and precision s, in unary. -/
def markPar (n s : ℕ) : U × U × U × U :=
  (List.replicate n (), List.replicate (capOf n) (), List.replicate (betaOf s) (), List.replicate (2 ^ betaOf s) ())

/-- The depth-first walk of the sparsification tree for width k, one round for each unit of the pad. -/
def walkF (k : ℕ) (pad : U) (τ : ℕ) (test : Sparsify.PFml → Bool) (r : Sparsify.PFml) : Bool :=
  (pad.foldl (fun st _ => cap pad ([], false) (Sparsify.roundB (WidthK.Prog.stepK (WidthK.theta τ) k) test st))
    (cap pad ([], false) ([r], false))).2

/-- THE function, for 3-SAT. -/
def A (p : List Bool × U) : Bool :=
  bif hasNil (decF p.1) then false
  else walkF 3 p.2 (tauOf (sOf (Decode.dec p.1).1))
    (fun ψ => decide (0 < countM 3 p.2
      ((schedF p.2 (depthOf (sOf (Decode.dec p.1).1))).1, (schedF p.2 (depthOf (sOf (Decode.dec p.1).1))).2.1)
      (markPar (Decode.dec p.1).1 (sOf (Decode.dec p.1).1)) (layersOf (sOf (Decode.dec p.1).1)) ψ))
    (Sparsify.rootP (decF p.1))

/-! ### The interface between the programs and the arithmetic -/

/-- P of `sideN_sized`. -/
def Pn (g lam : ℕ) : ℕ := 2 * g ^ 3 * lam

/-- An upper bound for the bit length of the entries one level down. -/
def bNext (K g lam B : ℕ) : ℕ :=
  Pn g lam * (2 * g / K) + (g * B + g ^ 2 * lam) * (2 * g / K + 2 * g / K * (2 * g / K)) * K

/-- An upper bound for (length of the word of an instance) + 2. -/
def instLen (K lam B : ℕ) : ℕ := 4 * lam + K * (2 ^ ((K - 1) * lam) * (3 * B + 10) + 4) + 10

/-- What one step «g·g nodes, labels ≤ lam → K nodes» needs of the length F of the pad. -/
structure Bud (F K g lam : ℕ) : Prop where
  pat : (lam + 1) ^ nRect g ≤ F
  col : K ^ g ≤ F
  st : 2 ^ (Pn g lam * (2 * g / K)) ≤ F
  lab : 2 ^ Pn g lam ≤ F
  tab : 2 ^ ((K - 1) * lamNext K g lam) ≤ F

/-- The pad of length F suffices for a work list of at most cnt instances on Kup nodes, labels ≤ Λ,
entries ≤ 2^B, and all steps of the
schedule below it. -/
def Fits (F : ℕ) : ℕ → ℕ → ℕ → ℕ → List Lvl → Prop
  | Kup, Λ, B, cnt, [] => cnt * instLen Kup Λ B + 2 ≤ F ∧ 2 ^ (Kup * (Kup - 1) / 2 * Λ) ≤ F
  | Kup, Λ, B, cnt, L :: r =>
      cnt * instLen Kup Λ B + 2 ≤ F ∧ Bud F L.1.length L.2.length Λ ∧
        Fits F L.1.length (lamNext L.1.length L.2.length Λ) (bNext L.1.length L.2.length Λ B) (cnt * (Λ + 1) ^ nRect L.2.length) r

/-- A network on g nodes in which any two nodes share a bounded number of label bits has a good
colouring with K colours: g is at least about
4·Dcol²·K·log₂(g·K). -/
def ColOK (K g : ℕ) : Prop := ∃ m, 4 * Dcol ^ 2 * m * K ≤ g ∧ (g + 2) * K < 2 ^ m

/-- The schedule is a chain of steps g·g → K that ends at 256 nodes. -/
def Chain : ℕ → List Lvl → Prop
  | Kup, [] => Kup = 256
  | Kup, L :: r => Kup = L.2.length * L.2.length ∧ 2 ≤ L.1.length ∧ ColOK L.1.length L.2.length ∧ Chain L.1.length r

/-- The steps of the schedule of depth t, as a mathematical object: what `schedF` computes when the
pad is long enough. -/
def schedL : ℕ → List Lvl
  | 0 => []
  | j + 1 => (List.replicate (Kseq j) (), List.replicate (gseq j) ()) :: schedL j

/-- An upper bound for the length of the word of every state of `schedF pad t`. -/
def schedLen (t : ℕ) : ℕ := (t + 1) * (8 * Kseq t + 8) + 4 * Lseq t + 8

/-- An upper bound for the label length of the top instance of a network with U ≤ Ub and size P. -/
def lamG (K g Ub P : ℕ) : ℕ := (K ^ 3 + K * Ub + g * P) / K ^ 3

/-- The pad of length F suffices for one network on 3K_t⁸ nodes with U ≤ Ub, size P and entries 0,
1, −1, under the schedule S = (steps, K_t). -/
structure NetFits (F : ℕ) (S : List Lvl × U) (Ub P : ℕ) : Prop where
  chain : Chain S.2.length S.1
  two_le : 2 ≤ S.2.length
  col : S.2.length ^ (3 * S.2.length ^ 8) ≤ F
  st : 2 ^ (P * (2 * (3 * S.2.length ^ 8) / S.2.length)) ≤ F
  lab : 2 ^ P ≤ F
  tab : 2 ^ ((S.2.length - 1) * lamG S.2.length (3 * S.2.length ^ 8) Ub P) ≤ F
  fits : Fits F S.2.length (lamG S.2.length (3 * S.2.length ^ 8) Ub P) (P * (2 * (3 * S.2.length ^ 8) / S.2.length)) 1 S.1

/-- An upper bound for U of the network of marks of an admissible profile: width k, R₁ layers, cap
w, code parameter β, at most b·(n + 1) clauses. -/
def Ub (k g n w β R₁ : ℕ) : ℕ := 2 * R₁ * ((k - 1) * w * (1 + β) + (k - 1) * (n + 1) + g ^ 2)

/-- An upper bound for the size P of the network of marks: every variable occurs in at most Δ
clauses. -/
def Pb (g n β Δ : ℕ) : ℕ := 2 * (2 + β) * Mark.qv g n * (Δ + 4)

/-- An upper bound for the length of the word of a division of at most m clauses, of at most k
literals on variables below n, into R + 1 layers. -/
def layLen (k n m R : ℕ) : ℕ := m * (k * (3 * n + 5) + 10) + 4 * (R + 1) + 2

/-- The pad of length F suffices for all evaluations for one formula: width k, n variables, at most
m clauses, every variable in at most Δ of them, R + 1 layers,
code parameters β and b, cap n + 2. -/
structure MarkFits (k F : ℕ) (S : List Lvl × U) (n β b R Δ m : ℕ) : Prop where
  net : NetFits F S (Ub k (3 * S.2.length ^ 8) n (n + 2) β (R + 2)) (Pb (3 * S.2.length ^ 8) n β Δ)
  prof : Mark.nProf (3 * S.2.length ^ 8) m (R + 2) ≤ F
  lay : layLen k n m R ≤ F
  last : 2 ^ R * m + 5 * 3 ^ R ≤ 3 ^ R * (n + 2)
  b_pos : 0 < b
  b_le : b ≤ 2 ^ β
  m_le : m ≤ b * (n + 1)

/-- An upper bound for the length of the word of a state of the walk: at most bsum τ k · n + 1
formulas of at most 2^k·m clauses of at most k
literals on variables below n, and a flag. -/
def stackLen (k τ n m : ℕ) : ℕ := (WidthK.bsum τ k * n + 1) * (2 ^ k * m * (k * (3 * n + 5) + 10) + 4) + 8

/-- An upper bound for the length of the code of an instance of k-SAT on n variables, plus 1, and so
for its number of clauses. -/
def inLen (k n : ℕ) : ℕ := (k * 2 ^ k + 1) * (n + 2) ^ (k + 1)

end PaddedDescent.F
