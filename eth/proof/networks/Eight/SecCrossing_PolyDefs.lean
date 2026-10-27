/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import EightSquareStatement
public import PaddedDescent.F.Fuel
public import ClauseBound.Alg.Data

/-! # Lemma 2 from the eight-square identity: the pieces and their factorizations as programs (definitions only)

Strings are lists of bits here. `aMul` computes A_i as in the proof of Lemma 2(a), «multiplying them
out one at a time»: a polynomial in T is kept as the list of its coefficients, lowest first
(`mulStep`, `mulUpTo`, `mulOut`). `fTop` and `fBot` are the two functions of the factorizations in
the proof of Lemma 2(b), for both directions (tr = false: row-wise, tr = true: column-wise):
«Let θ = (Q, θ'), where a set Q ⊆ [t] is written as a string of t bits, and put f(·,θ) = f_Q(·,θ')
and f'(·,θ) = f'_Q(·,θ') if |Q| = i, and f(·,θ) = f'(·,θ) = 0 otherwise»; θ' lists the indices of
the blocks in their order, 3 bits for a block whose
function (R row-wise, C column-wise) factors through 3 bits, 6 bits for a block of the other kind,
which we call wide; «whenever one of these numbers exceeds 2λ, use the factorization through 2λ bits
instead».
Both directions have the same formulas, because C(x,y,u,v) = R(x,u,y,v). `eightF` is the family of
pieces in the form in which the networks of a grid (proof/rates/ClauseBound/Alg) take it. -/

@[expose] public section

namespace Eight

open Groundwork PaddedDescent.F ClauseBound.Alg

/-- The three bits of a list from position j on; positions beyond the end count as 0. -/
def blkAt (w : List Bool) (j : ℕ) : Block := (w.getD j false, w.getD (j + 1) false, w.getD (j + 2) false)

/-- The block number s (from 0) of a string, zeros appended. -/
def blkL (w : List Bool) (s : ℕ) : Block := blkAt w (3 * s)

/-! ### A_i -/

/-- Four strings x, y, u, v. -/
abbrev FourL : Type := List Bool × List Bool × List Bool × List Bool

/-- R at the block number s. -/
def rAt (q : FourL) (s : ℕ) : ℤ := Rb (blkL q.1 s) (blkL q.2.1 s) (blkL q.2.2.1 s) (blkL q.2.2.2 s)

/-- C at the block number s. -/
def cAt (q : FourL) (s : ℕ) : ℤ := Cb (blkL q.1 s) (blkL q.2.1 s) (blkL q.2.2.1 s) (blkL q.2.2.2 s)

/-- The number of blocks, from the length of the first string. -/
def tL (q : FourL) : ℕ := tOf q.1.length

/-- One multiplication: the list of coefficients of (r + T·c)·P, where l is the list of coefficients
of P, lowest first. The entry number j is r·l_j + c·l_{j−1}; the list (0 :: l) has l_{j−1} at the
place j. -/
def mulStep (r c : ℤ) (l : List ℤ) : List ℤ :=
  (List.range (l.length + 1)).map fun j => r * l.getD j 0 + c * (0 :: l).getD j 0

/-- The list of coefficients after the factors number 0, …, n − 1 have been multiplied in, one at a
time, starting from the polynomial 1. -/
def mulUpTo (q : FourL) (n : ℕ) : List ℤ :=
  (List.range n).foldl (fun l s => mulStep (rAt q s) (cAt q s) l) [1]

/-- The paper's program for A_0, …, A_t: all t factors R(x_s,y_s,u_s,v_s) + T·C(x_s,y_s,u_s,v_s)
multiplied out one at a time. -/
def mulOut (q : FourL) : List ℤ := mulUpTo q (tL q)

/-- A_i as a function of (i, x, y, u, v), by the paper's program: the entry number i of the list,
and 0 beyond its end, that is, for i > t. -/
def aMul (p : ℕ × FourL) : ℤ := (mulOut p.2).getD p.1 0

/-! ### The two factorizations -/

/-- The number of bits of the factorization with θ = (Q, θ'): 4t + 3i row-wise, 7t − 3i column-wise
(for i ≤ t, as everywhere it is used; the subtraction is that of natural numbers). -/
def longCap (tr : Bool) (t i : ℕ) : ℕ := bif tr then 7 * t - 3 * i else 4 * t + 3 * i

/-- Is the factorization with θ = (Q, θ') used, that is, does its number of bits not exceed 2λ? -/
def useLong (tr : Bool) (lam i : ℕ) : Bool := decide (longCap tr (tOf lam) i ≤ 2 * lam)

/-- Is the block number s wide? Row-wise the blocks in Q (they take C) are wide, column-wise the
others (they take R). -/
def wide (tr : Bool) (Q : List Bool) (s : ℕ) : Bool := Q.getD s false != tr

/-- Where the index of the block number s begins in θ': 3 bits for each earlier block and 3 more for
each earlier wide block. -/
def off (tr : Bool) (Q : List Bool) (s : ℕ) : ℕ := 3 * s + 3 * (List.range s).countP (wide tr Q)

/-- The factor of the block number s in the first function: ψ_k(a_s, b_s), k the index of the block;
for a wide block, [(a_s, b_s) = index of the block]. -/
def topAt (tr : Bool) (Q w a b : List Bool) (s : ℕ) : ℤ :=
  if wide tr Q s = true then (if blkL a s = blkAt w (off tr Q s) ∧ blkL b s = blkAt w (off tr Q s + 3) then 1 else 0)
  else psi (blkAt w (off tr Q s)) (blkL a s) (blkL b s)

/-- The factor of the block number s in the second function: ψ_k(b_s, a_s); for a wide block with
the index (k, k'), R(k, a_s, k', b_s), which is C(k, k', a_s, b_s). -/
def botAt (tr : Bool) (Q w a b : List Bool) (s : ℕ) : ℤ :=
  if wide tr Q s = true then Rb (blkAt w (off tr Q s)) (blkL a s) (blkAt w (off tr Q s + 3)) (blkL b s)
  else psi (blkAt w (off tr Q s)) (blkL b s) (blkL a s)

/-- The first function of a factorization of A_i, as a function of (direction, i, first string a,
second string b, θ); (a, b) is (x, y) row-wise and (x, u) column-wise; λ is the length of a. -/
def fTop (q : Bool × ℕ × List Bool × List Bool × List Bool) : ℤ :=
  if useLong q.1 q.2.2.1.length q.2.1 = true then
    (if (q.2.2.2.2.take (tOf q.2.2.1.length)).count true = q.2.1 then
      prodL (tOf q.2.2.1.length) (topAt q.1 (q.2.2.2.2.take (tOf q.2.2.1.length)) (q.2.2.2.2.drop (tOf q.2.2.1.length)) q.2.2.1 q.2.2.2.1)
    else 0)
  else (if q.2.2.1 ++ q.2.2.2.1 = q.2.2.2.2 then 1 else 0)

/-- The second function of a factorization of A_i; (a, b) is (u, v) row-wise and (y, v) column-wise.
In the factorization through 2λ bits, θ = (θ₁, θ₂) stands for the two strings of the first function. -/
def fBot (q : Bool × ℕ × List Bool × List Bool × List Bool) : ℤ :=
  if useLong q.1 q.2.2.1.length q.2.1 = true then
    (if (q.2.2.2.2.take (tOf q.2.2.1.length)).count true = q.2.1 then
      prodL (tOf q.2.2.1.length) (botAt q.1 (q.2.2.2.2.take (tOf q.2.2.1.length)) (q.2.2.2.2.drop (tOf q.2.2.1.length)) q.2.2.1 q.2.2.2.1)
    else 0)
  else bif q.1 then aMul (q.2.1, q.2.2.2.2.take q.2.2.1.length, q.2.2.1, q.2.2.2.2.drop q.2.2.1.length, q.2.2.2.1)
    else aMul (q.2.1, q.2.2.2.2.take q.2.2.1.length, q.2.2.2.2.drop q.2.2.1.length, q.2.2.1, q.2.2.2.1)

/-- The functions A_0, …, A_t with their two factorizations, in the form in which the networks of a
grid take a family of pieces: t + 1 pieces, which add up to 2^t·[x = v][y = u]; the piece number i
factors through c_i^row bits
row-wise and c_i^col bits column-wise; no pad is needed; all values are at most 2^t in absolute
value; every number of bits is at most 2λ. The parameter h of a family of pieces is not used. -/
def eightF : PiecesF where
  cnt _ lam := tOf lam + 1
  d _ lam := 2 ^ tOf lam
  cap tr _ lam i := bif tr then ccol lam i else crow lam i
  top q := fTop (q.1.2, q.2.1.2, q.2.2.1, q.2.2.2.1, q.2.2.2.2)
  bot q := fBot (q.1.2, q.2.1.2, q.2.2.1, q.2.2.2.1, q.2.2.2.2)
  need _ _ := 0
  bits _ lam := tOf lam
  m := 1

/-! ### Interface statements (nothing is proved or assumed here) -/

/-- `aMul` computes A_i. -/
def StAMul : Prop := ∀ (lam i : ℕ) (x y u v : Pieces.Bits lam), aMul (i, List.ofFn x, List.ofFn y, List.ofFn u, List.ofFn v) = A lam i x y u v

/-- Lemma 2(b) for the functions `fTop` and `fBot`: they factorize A_i through c_i^row bits row-wise
and c_i^col bits column-wise, with values at most 2^t in absolute value. -/
def StFact : Prop := ∀ lam, 1 ≤ lam → ∀ i ≤ tOf lam,
  (∀ x y u v : Pieces.Bits lam, A lam i x y u v = ∑ θ : Pieces.Bits (crow lam i),
    fTop (false, i, List.ofFn x, List.ofFn y, List.ofFn θ) * fBot (false, i, List.ofFn u, List.ofFn v, List.ofFn θ)) ∧
  (∀ x y u v : Pieces.Bits lam, A lam i x y u v = ∑ θ : Pieces.Bits (ccol lam i),
    fTop (true, i, List.ofFn x, List.ofFn u, List.ofFn θ) * fBot (true, i, List.ofFn y, List.ofFn v, List.ofFn θ)) ∧
  ∀ tr (a b : Pieces.Bits lam) (θ : List Bool),
    |fTop (tr, i, List.ofFn a, List.ofFn b, θ)| ≤ 2 ^ tOf lam ∧ |fBot (tr, i, List.ofFn a, List.ofFn b, θ)| ≤ 2 ^ tOf lam

/-- The three programs are polynomial-time. -/
def StPoly : Prop := PolyT aMul ∧ PolyT fTop ∧ PolyT fBot

/-- All parts of the family are computed in polynomial time. -/
def StKeeps : Prop := eightF.Keeps

end Eight
