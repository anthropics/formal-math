/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import AppRunningTimeStatement

/-! # Pieces with parameters (ρ, c): the operations on programs. Definitions only

The programs and predicates that the files on «we may and do assume c_row, c_col ≤ 2λ» and on the
definition of pieces speak of; nothing is proved here.
* `valF P`, `valOf P`: the value of a piece, added up from P's own factorization.
* `trimV P val c`: the pieces of the programs P, read at h = 0, with every factorization through 2λ
  bits or more replaced by F(z,z') = Σ_θ [z = θ]·F(θ,z'), with their program `val` for F. This is
  the form that the theorem on the general recursion uses.
* `atZero P c m`: the programs read at the parameter h = 0, in the form that the recursion reads.
* `Realizes P h lam A`: the functions A are the pieces of the programs P. -/

@[expose] public section

namespace GeneralPieces

open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen AppRunningTime

/-- The argument of `valF`: ((pad, column-wise?), (parameter h in unary, index i), four strings).
The first two strings are the arguments of `top`, the other two those of `bot`: they are
x, y, u, v row-wise and x, u, y, v column-wise. λ is the length of the first string. -/
abbrev VQ : Type := (U × Bool) × (U × ℕ) × (List Bool × List Bool × List Bool × List Bool)

/-- The value of the piece number i: the sum of top·bot over all words of `cap` bits, cut off by the
pad. -/
def valF (P : PiecesF) (q : VQ) : ℤ :=
  sumF (2 ^ P.cap q.1.2 q.2.1.1.length q.2.2.1.length q.2.1.2) q.1.1 fun t =>
    P.top (q.1, (q.2.1.1.length, q.2.1.2), (q.2.2.1, q.2.2.2.1, toWord (P.cap q.1.2 q.2.1.1.length q.2.2.1.length q.2.1.2) t)) *
      P.bot (q.1, (q.2.1.1.length, q.2.1.2), (q.2.2.2.2.1, q.2.2.2.2.2, toWord (P.cap q.1.2 q.2.1.1.length q.2.2.1.length q.2.1.2) t))

/-- Is the label of the query a word of 2λ bits? -/
def isLong (q : PQ) : Bool := decide (q.2.2.2.2.length = 2 * q.2.2.1.length)

/-- The functions A are the pieces of P at (h, λ): what `PiecesF.Spec` says of some A. -/
def Realizes (P : PiecesF) (h lam : ℕ) (A : ℕ → Pieces.Four lam) : Prop :=
  (∀ x y u v, ∑ i ∈ Finset.range (P.cnt h lam), A i x y u v = P.d h lam * Pieces.cross x y u v) ∧
  (∀ i < P.cnt h lam, ∀ x y u v, |A i x y u v| ≤ 2 ^ P.bits h lam) ∧
  ∀ pad : U, 2 ^ P.need h lam ≤ pad.length → ∀ i < P.cnt h lam,
    (∀ x y u v, A i x y u v = ∑ θ ∈ words (P.cap false h lam i),
      P.top ((pad, false), (h, i), (bitsOf x, bitsOf y, θ)) * P.bot ((pad, false), (h, i), (bitsOf u, bitsOf v, θ))) ∧
    (∀ x y u v, A i x y u v = ∑ θ ∈ words (P.cap true h lam i),
      P.top ((pad, true), (h, i), (bitsOf x, bitsOf u, θ)) * P.bot ((pad, true), (h, i), (bitsOf y, bitsOf v, θ))) ∧
    ∀ tr (x y : Pieces.Bits lam) θ, |P.top ((pad, tr), (h, i), (bitsOf x, bitsOf y, θ))| ≤ 2 ^ P.bits h lam ∧
      |P.bot ((pad, tr), (h, i), (bitsOf x, bitsOf y, θ))| ≤ 2 ^ P.bits h lam

/-- The program for the value of a piece: `valF` at h = 0, from the row-wise factorization. It reads
λ off the first string. -/
def valOf (P : PiecesF) (q : ValQ) : ℤ := valF P ((q.1, false), ([], q.2.1.2), q.2.2)

/-- The programs of P read at h = 0 for every h, with the exponent c·λ of the pad, the bound (2λ)^c
for the number of bits of the values, and the constant m. -/
def atZero (P : PiecesF) (c m : ℕ) : PiecesF where
  cnt _ lam := P.cnt 0 lam
  d _ lam := P.d 0 lam
  cap tr _ lam i := P.cap tr 0 lam i
  top q := P.top (q.1, (0, q.2.1.2), q.2.2)
  bot q := P.bot (q.1, (0, q.2.1.2), q.2.2)
  need _ lam := c * lam
  bits _ lam := (2 * lam) ^ c
  m := m

/-- The four strings at which the second function of the new factorization asks for the value of the
piece: the halves of the label θ take the places of the arguments of the first function, which are
x, y row-wise and x, u column-wise. -/
def askAt (q : PQ) : List Bool × List Bool × List Bool × List Bool :=
  bif q.1.2 then (q.2.2.2.2.take q.2.2.1.length, q.2.2.1, q.2.2.2.2.drop q.2.2.1.length, q.2.2.2.1)
  else (q.2.2.2.2.take q.2.2.1.length, q.2.2.2.2.drop q.2.2.1.length, q.2.2.1, q.2.2.2.1)

/-- The pieces of P, read at h = 0, with every factorization through 2λ bits or more replaced by
F(z,z') = Σ_θ [z = θ]·F(θ,z'), where F(θ,z') is computed by `val`. -/
def trimV (P : PiecesF) (val : ValQ → ℤ) (c : ℕ) : PiecesF where
  cnt _ lam := P.cnt 0 lam
  d _ lam := P.d 0 lam
  cap tr _ lam i := min (P.cap tr 0 lam i) (2 * lam)
  top q := bif isLong q then (if q.2.2.1 ++ q.2.2.2.1 = q.2.2.2.2 then 1 else 0) else P.top (q.1, (0, q.2.1.2), q.2.2)
  bot q := bif isLong q then val (q.1.1, (List.replicate q.2.2.1.length (), q.2.1.2), askAt q) else P.bot (q.1, (0, q.2.1.2), q.2.2)
  need _ lam := c * lam
  bits _ lam := (2 * lam) ^ c
  m := 1

end GeneralPieces
