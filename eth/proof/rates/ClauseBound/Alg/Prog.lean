/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.Data

/-! # The definitions, part 2: evaluation by enumeration, one level, all levels, and what they need of the pad -/

@[expose] public section

namespace ClauseBound.Alg

open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F

/-! ### A network evaluated by enumeration of all labels -/

/-- The length of the chunk number j = a·g + b of the word that holds one label for every pair a <
b. -/
def enumLen {C : Type} (g : ℕ) (F : FNet C) (c : C) (j : ℕ) : ℕ := if j / g < j % g then F.cap c (j / g) (j % g) else 0

/-- The number of bits of that word: U/2. -/
def enumBits {C : Type} (g : ℕ) (F : FNet C) (c : C) : ℕ := ∑ j ∈ Finset.range (g * g), enumLen g F c j

/-- Z = Σ_θ ∏_a Σ_{z_a} W_a(z_a) ∏_{b ≠ a} f_ab(z_a, θ_ab). -/
def enumF {C : Type} (pad : U) (g : ℕ) (F : FNet C) (c : C) : ℤ :=
  sumF (2 ^ enumBits g F c) pad fun t =>
    prodL g fun a => sumF (2 ^ F.n c a) pad fun zi =>
      F.W (c, (a, toWord (F.n c a) zi)) * prodL g fun b =>
        if b = a then 1
        else F.f (c, ((a, b), (toWord (F.n c a) zi, chunkAt (enumLen g F c) (min a b * g + max a b) (toWord (enumBits g F c) t))))

/-! ### One level -/

section Level
variable (P : PiecesF)

/-- The context of the network of the pattern y of the instance I. -/
def gctx (pad : U) (s : Step) (tr : Bool) (I : PInst) (y : ℕ) : GridCtx := ((pad, (s.1.2.1, s.1.2.2), tr, s.2.1.2), (I.1, y, I.2))

/-- The number of patterns. -/
def nPat (s : Step) (lam : ℕ) : ℕ := P.cnt s.h lam ^ nRectG s.p s.d

/-- Σ_q ι(q). -/
def sumDig (s : Step) (lam y : ℕ) : ℕ := ∑ q ∈ Finset.range (nRectG s.p s.d), digit (P.cnt s.h lam - 1) y q

/-- Is the column network taken for the pattern y? -/
def colSide (s : Step) (lam y : ℕ) : Bool :=
  if s.thin = true then decide (sumDig P s lam y ^ 2 * s.a ≤ s.b * (nRectG s.p s.d * Pieces.nblk lam s.h) ^ 2)
  else decide (totalG P s.p s.d true s.h lam y < totalG P s.p s.d false s.h lam y)

/-- The largest sum of the two numbers of bits of a piece. -/
def capSum (h lam : ℕ) : ℕ := (Finset.range (P.cnt h lam)).sup fun i => P.cap false h lam i + P.cap true h lam i

/-- N = (pd)²λ. -/
def Nof (s : Step) (lam : ℕ) : ℕ := (s.p * s.d) ^ 2 * lam

/-- An upper bound for U of every network that is rebalanced at this step. -/
def ubarG (s : Step) (lam : ℕ) : ℕ :=
  if s.thin = true then Nof s lam - Nof s lam / s.a + (s.p * s.d) ^ 2
  else s.p * (s.p - 1) * s.d * lam + nRectG s.p s.d * capSum P s.h lam

/-- An upper bound for U/2 of every column network that is evaluated by enumeration at this step:
e·X is written 8·√(b·X²/a). -/
def ebarG (s : Step) (lam : ℕ) : ℕ :=
  c2 s.d * s.p * lam + nRectG s.p s.d + 8 * (Nat.sqrt (s.b * (nRectG s.p s.d * (lam + s.h)) ^ 2 / s.a) + 1)

/-- The label length one level down. -/
def lamNextG (s : Step) (lam : ℕ) : ℕ := (s.D * ubarG P s lam + 3 * s.p ^ 2 * (s.d ^ 2 * (P.m * lam))) / (s.D * s.K ^ 2) + 1

/-- The instance on K nodes that the pattern y leads to. -/
def childG (pad : U) (s : Step) (I : PInst) (y : ℕ) : Option PInst :=
  rebalG pad s.K s.p (lamNextG P s I.1.length) (gridF P) (gctx pad s (!s.thin && colSide P s I.1.length y) I y)

/-- One level: the sum of the terms that are evaluated at once, and the instances on K nodes of the
other terms. -/
def expandG (pad : U) (s : Step) (I : PInst) : ℤ × List PInst :=
  (sumF (nPat P s I.1.length) pad fun y =>
      if (s.thin && colSide P s I.1.length y) = true then enumF pad s.d (gridF P) (gctx pad s true I y) else 0,
   (rng pad (nPat P s I.1.length)).filterMap fun y =>
      if (s.thin && colSide P s I.1.length y) = true then none else childG P pad s I y)

/-! ### All levels -/

/-- ((sum so far, common factor so far), label length in unary, work list): factor · Z = sum + Σ of
the values of the work list. -/
abbrev DState : Type := (ℤ × ℕ) × U × List PInst

def stepG (pad : U) (st : DState) (s : Step) : DState :=
  ((st.1.1 * (P.d s.h st.2.1.length ^ nRectG s.p s.d : ℕ) + ((st.2.2.map (expandG P pad s)).map Prod.fst).sum,
    st.1.2 * P.d s.h st.2.1.length ^ nRectG s.p s.d),
   List.replicate (lamNextG P s st.2.1.length) (), (st.2.2.map (expandG P pad s)).flatMap Prod.snd)

def descendG (pad : U) (sched : List Step) (I : PInst) : DState :=
  sched.foldl (fun st s => cap pad ((0, 1), [], []) (stepG P pad st s)) (cap pad ((0, 1), [], []) ((0, 1), I.1, [I]))

/-- The value of the instance I on the nodes of the first step of sched; K₀ is the number of nodes
after the last step. -/
def solveG (pad : U) (K₀ : ℕ) (sched : List Step) (I : PInst) : ℤ :=
  ((descendG P pad sched I).1.1 + ((descendG P pad sched I).2.2.map (bruteF pad K₀)).sum) / (descendG P pad sched I).1.2

/-! ### What a step needs -/

/-- P of the networks that are rebalanced. -/
def PnG (s : Step) (lam : ℕ) : ℕ := P.m * (s.p * s.d ^ 2 * lam)

/-- An upper bound for the bit length of the entries one level down. -/
def bNextG (s : Step) (lam B : ℕ) : ℕ :=
  PnG P s lam * (2 * s.p / s.K) + (s.d * B + s.d ^ 2 * P.bits s.h lam) * (2 * s.p / s.K + 2 * s.p / s.K * (2 * s.p / s.K)) * s.K

/-- What one step needs of the length F of the pad. -/
structure BudG (F : ℕ) (s : Step) (lam : ℕ) : Prop where
  pieces : 2 ^ P.need s.h lam ≤ F
  pat : nPat P s lam ≤ F
  col : s.K ^ s.p ≤ F
  st : 2 ^ (PnG P s lam * (2 * s.p / s.K)) ≤ F
  lab : 2 ^ PnG P s lam ≤ F
  tab : 2 ^ ((s.K - 1) * lamNextG P s lam) ≤ F
  enumLab : s.thin = true → 2 ^ ebarG s lam ≤ F
  enumSt : s.thin = true → 2 ^ (s.p ^ 2 * s.d * lam) ≤ F

end Level

end ClauseBound.Alg
