/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Prog
public import PiecesStatement

/-! # The definitions, part 1: pieces as programs, the steps of a schedule, the network of one term on a p × d grid

Everything is a pure function of data and a pad, as in the namespace `PaddedDescent.F`. -/

@[expose] public section

namespace ClauseBound.Alg

open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F

/-- The argument of one factor of a piece: ((pad, column-wise?), (parameter h, index i), (first
string, second string, label θ)); λ is the length of the first string. -/
abbrev PQ : Type := (U × Bool) × (ℕ × ℕ) × (List Bool × List Bool × List Bool)

/-- Pieces as programs. The pieces for the strings of λ bits and the parameter h are numbered 0, …,
cnt h λ − 1. `cap tr h λ i` is the number of bits through which the piece number i
factors row-wise (tr = false) or column-wise (tr = true); `top` is the function of the first two
strings of that factorization, `bot` that of the other two. -/
structure PiecesF where
  cnt : ℕ → ℕ → ℕ
  d : ℕ → ℕ → ℕ
  cap : Bool → ℕ → ℕ → ℕ → ℕ
  top : PQ → ℤ
  bot : PQ → ℤ
  /-- the pad that the loops inside top and bot need, as an exponent of 2 -/
  need : ℕ → ℕ → ℕ
  /-- all values of the pieces and of top and bot have at most this many bits -/
  bits : ℕ → ℕ → ℕ
  /-- every cap is at most 2·m·λ (the paper has m = 1; code words that are easier to compute may
  need m = 2) -/
  m : ℕ

/-- A word of n bits as a function. -/
def bitsOf {n : ℕ} (x : Pieces.Bits n) : List Bool := List.ofFn x

/-- What the grid needs of the pieces at (h, λ): they add up to d·[x = v][y = u]; top and bot
factorize them over all words of cap bits, when the pad is long enough; sizes. -/
structure PiecesF.Spec (P : PiecesF) (h lam : ℕ) : Prop where
  cnt_pos : 1 ≤ P.cnt h lam
  d_pos : 1 ≤ P.d h lam
  m_pos : 1 ≤ P.m
  cap_le : ∀ tr i, i < P.cnt h lam → P.cap tr h lam i ≤ 2 * P.m * lam
  ex : ∃ A : ℕ → Pieces.Four lam,
    (∀ x y u v, ∑ i ∈ Finset.range (P.cnt h lam), A i x y u v = P.d h lam * Pieces.cross x y u v) ∧
    (∀ i < P.cnt h lam, ∀ x y u v, |A i x y u v| ≤ 2 ^ P.bits h lam) ∧
    ∀ pad : U, 2 ^ P.need h lam ≤ pad.length → ∀ i < P.cnt h lam,
      (∀ x y u v, A i x y u v = ∑ θ ∈ words (P.cap false h lam i),
        P.top ((pad, false), (h, i), (bitsOf x, bitsOf y, θ)) * P.bot ((pad, false), (h, i), (bitsOf u, bitsOf v, θ))) ∧
      (∀ x y u v, A i x y u v = ∑ θ ∈ words (P.cap true h lam i),
        P.top ((pad, true), (h, i), (bitsOf x, bitsOf u, θ)) * P.bot ((pad, true), (h, i), (bitsOf y, bitsOf v, θ))) ∧
      ∀ tr (x y : Pieces.Bits lam) θ, |P.top ((pad, tr), (h, i), (bitsOf x, bitsOf y, θ))| ≤ 2 ^ P.bits h lam ∧
        |P.bot ((pad, tr), (h, i), (bitsOf x, bitsOf y, θ))| ≤ 2 ^ P.bits h lam

/-- The certificates of the pieces. -/
structure PiecesF.Keeps (P : PiecesF) : Prop where
  cnt : Unary fun p : U × U => P.cnt p.1.length p.2.length
  d : PolyT fun p : U × U => P.d p.1.length p.2.length
  cap : Unary fun p : Bool × U × U × ℕ => P.cap p.1 p.2.1.length p.2.2.1.length p.2.2.2
  top : PolyT P.top
  bot : PolyT P.bot
  need : Unary fun p : U × U => P.need p.1.length p.2.length
  bits : Unary fun p : U × U => P.bits p.1.length p.2.length

/-- One step of a schedule, «p·d nodes → K nodes», all numbers in unary: ((K, p, d), (D, h), (thin?,
a, b)).
D: the grouping of the parts into the K groups is allowed the relative error 1/D. h: the parameter
of the pieces.
thin = false: both networks are rebalanced, the one with the smaller total is taken. thin = true: a
comparison that involves the sum of the values of ι and the numbers a and b decides between
evaluating the column network by enumeration
and rebalancing the row network. -/
abbrev Step : Type := (U × U × U) × (U × U) × (Bool × U × U)

namespace Step
variable (s : Step)
def K : ℕ := s.1.1.length
def p : ℕ := s.1.2.1.length
def d : ℕ := s.1.2.2.length
def D : ℕ := s.2.1.1.length
def h : ℕ := s.2.1.2.length
def thin : Bool := s.2.2.1
def a : ℕ := s.2.2.2.1.length
def b : ℕ := s.2.2.2.2.length
end Step

/-- The number of rectangles of the p × d grid. -/
def nRectG (p d : ℕ) : ℕ := c2 p * c2 d

/-- The number of parts (merged rows, or merged columns if tr) and the number of nodes of a part. -/
def nParts (p d : ℕ) (tr : Bool) : ℕ := if tr = true then d else p
def nMemb (p d : ℕ) (tr : Bool) : ℕ := if tr = true then p else d

/-- The position, among the p·d nodes of the instance, of the node number i of the part a: the node
in row r and column j has the position j + d·r. -/
def nodeG (d : ℕ) (tr : Bool) (a i : ℕ) : ℕ := if tr = true then a + d * i else i + d * a

/-- The number of the rectangle number κ of the pair of parts number q. -/
def rectIxG (d : ℕ) (tr : Bool) (q κ : ℕ) : ℕ := if tr = true then κ * c2 d + q else q * c2 d + κ

/-- The half-edge from the node number x of a part towards the node at position u, in the word z of
a state of the part. -/
def heG (p d ℓ : ℕ) (z : List Bool) (x u : ℕ) : List Bool := block ℓ u (block (p * d * ℓ) x z)

/-- ((pad, (p, d) in unary, tr, h in unary), (ℓ in unary, pattern y, table)). -/
abbrev GridCtx : Type := (U × (U × U) × Bool × U) × (U × ℕ × Tab)

section Grid
variable (P : PiecesF)

/-- ι at the rectangle number κ of the pair of parts number q: a digit of y in base cnt. -/
def digG (d : ℕ) (tr : Bool) (h ℓ y q κ : ℕ) : ℕ := digit (P.cnt h ℓ - 1) y (rectIxG d tr q κ)

/-- The length of the chunk of that rectangle in a label. -/
def lenG (d : ℕ) (tr : Bool) (h ℓ y q κ : ℕ) : ℕ := P.cap tr h ℓ (digG P d tr h ℓ y q κ)

/-- The length of the labels of the parts a, b. -/
def capG (p d : ℕ) (tr : Bool) (h ℓ y a b : ℕ) : ℕ :=
  nMemb p d tr * ℓ + ∑ κ ∈ Finset.range (c2 (nMemb p d tr)), lenG P d tr h ℓ y (tri (min a b) (max a b)) κ

/-- The half-edges from a node to itself are 0…0 and the edges inside the part agree. -/
def chkG (p d : ℕ) (tr : Bool) (ℓ : ℕ) (q : WQ) : Bool :=
  ((List.range (nMemb p d tr)).all fun i => (heG p d ℓ q.2 i (nodeG d tr q.1 i)).all (!·)) &&
    (List.range (nMemb p d tr)).all fun i => (List.range (nMemb p d tr)).all fun i' =>
      decide (i' ≤ i) || (heG p d ℓ q.2 i (nodeG d tr q.1 i') == heG p d ℓ q.2 i' (nodeG d tr q.1 i))

/-- The weight of a part. -/
def gridW (p d : ℕ) (tr : Bool) (ℓ : ℕ) (T : Tab) (q : WQ) : ℤ :=
  bif chkG p d tr ℓ q then
    prodL (nMemb p d tr) fun i => look T (nodeG d tr q.1 i,
      (List.range (p * d)).map fun u => if u = nodeG d tr q.1 i then [] else heG p d ℓ q.2 i u)
  else 0

/-- The factor of the parts a = q.1.1 and b = q.1.2 on the side of a. -/
def gridFf (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ) (q : FQ) : ℤ :=
  bif (List.range (nMemb p d tr)).all fun i => heG p d ℓ q.2.1 i (nodeG d tr q.1.2 i) == block ℓ i q.2.2 then
    prodL (nMemb p d tr * nMemb p d tr) fun j =>
      if j / nMemb p d tr < j % nMemb p d tr then
        (if q.1.1 < q.1.2 then P.top else P.bot) ((pad, tr),
          (h, digG P d tr h ℓ y (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2)) (tri (j / nMemb p d tr) (j % nMemb p d tr))),
          (heG p d ℓ q.2.1 (j / nMemb p d tr) (nodeG d tr q.1.2 (j % nMemb p d tr)),
           heG p d ℓ q.2.1 (j % nMemb p d tr) (nodeG d tr q.1.2 (j / nMemb p d tr)),
           chunkAt (lenG P d tr h ℓ y (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2))) (tri (j / nMemb p d tr) (j % nMemb p d tr))
             (q.2.2.drop (nMemb p d tr * ℓ))))
      else 1
  else 0

/-- The network of the term Z_ι with all rows (tr = false) or all columns (tr = true) merged. -/
def gridF : FNet GridCtx where
  n c _ := nMemb c.1.2.1.1.length c.1.2.1.2.length c.1.2.2.1 * (c.1.2.1.1.length * c.1.2.1.2.length) * c.2.1.length
  cap c a b := capG P c.1.2.1.1.length c.1.2.1.2.length c.1.2.2.1 c.1.2.2.2.length c.2.1.length c.2.2.1 a b
  W x := gridW x.1.1.2.1.1.length x.1.1.2.1.2.length x.1.1.2.2.1 x.1.2.1.length x.1.2.2.2 x.2
  f x := gridFf P x.1.1.1 x.1.1.2.1.1.length x.1.1.2.1.2.length x.1.1.2.2.1 x.1.1.2.2.2.length x.1.2.1.length x.1.2.2.1 x.2

/-- What the rectangles cost in the network of the pattern y (every rectangle counts twice). -/
def priceG (p d : ℕ) (tr : Bool) (h ℓ y : ℕ) : ℕ :=
  2 * ∑ q ∈ Finset.range (nRectG p d), P.cap tr h ℓ (digit (P.cnt h ℓ - 1) y q)

/-- U of that network. -/
def totalG (p d : ℕ) (tr : Bool) (h ℓ y : ℕ) : ℕ :=
  nParts p d tr * (nParts p d tr - 1) * nMemb p d tr * ℓ + priceG P p d tr h ℓ y

end Grid

end ClauseBound.Alg
