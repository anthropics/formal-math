/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.DefGenPieces.Progs

/-! # Pieces as programs: the values of the pieces

Lemmas on the pieces with parameters (ρ, c) of Appendix A when they are given as programs (the
definitions `valF` and `Realizes` are in `DefGenPieces/Progs.lean`). In the paper an algorithm
computes the values of the pieces
(part (c) of the definition). Pieces as programs have no program for the values, so `valF` adds up
P's own factorization, top·bot, over all words of P's number of bits, on a pad that is long enough
for this loop.

`valF_eq_sum` says that `valF` is this sum; `valF_eq` says that, for programs that realize functions
A, it is the value of the piece, from either factorization. -/

@[expose] public section

namespace GeneralPieces

open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen

namespace Trim

@[simp] theorem length_bitsOf {n : ℕ} (x : Pieces.Bits n) : (bitsOf x).length = n := by simp [bitsOf]

@[simp] theorem length_rep (n : ℕ) : (rep n).length = n := by simp [rep]

/-- Every word of n bits is the word of a function. -/
theorem exists_bitsOf {n : ℕ} {w : List Bool} (hw : w.length = n) : ∃ x : Pieces.Bits n, bitsOf x = w := by
  subst hw
  exact ⟨w.get, List.ofFn_get w⟩

/-- If the pad is long enough for the loop, `valF` is the sum of top·bot over all words of `cap`
bits. -/
theorem valF_eq_sum (P : PiecesF) {pad : U} {tr : Bool} {h lam i : ℕ} (hp : 2 ^ P.cap tr h lam i ≤ pad.length) (a b a' b' : Pieces.Bits lam) :
    valF P ((pad, tr), (rep h, i), (bitsOf a, bitsOf b, bitsOf a', bitsOf b')) =
      ∑ θ ∈ words (P.cap tr h lam i), P.top ((pad, tr), (h, i), (bitsOf a, bitsOf b, θ)) * P.bot ((pad, tr), (h, i), (bitsOf a', bitsOf b', θ)) := by
  unfold valF
  simp only [length_bitsOf, length_rep]
  rw [sumF_eq hp]
  exact sum_toWord _ fun θ => P.top ((pad, tr), (h, i), (bitsOf a, bitsOf b, θ)) * P.bot ((pad, tr), (h, i), (bitsOf a', bitsOf b', θ))

end Trim

open Trim

/-- For part (c) of the definition of pieces (one algorithm computes every value of the A_i): when
the pad is long enough, `valF` is the value of the piece, from either
factorization. -/
theorem valF_eq {P : PiecesF} {h lam : ℕ} {A : ℕ → Pieces.Four lam} (hA : Realizes P h lam A) {pad : U} (hn : 2 ^ P.need h lam ≤ pad.length) {i : ℕ}
    (hi : i < P.cnt h lam) (hc : ∀ tr, 2 ^ P.cap tr h lam i ≤ pad.length) (x y u v : Pieces.Bits lam) :
    valF P ((pad, false), (rep h, i), (bitsOf x, bitsOf y, bitsOf u, bitsOf v)) = A i x y u v ∧
      valF P ((pad, true), (rep h, i), (bitsOf x, bitsOf u, bitsOf y, bitsOf v)) = A i x y u v :=
  ⟨(valF_eq_sum P (hc false) x y u v).trans ((hA.2.2 pad hn i hi).1 x y u v).symm,
    (valF_eq_sum P (hc true) x u y v).trans ((hA.2.2 pad hn i hi).2.1 x y u v).symm⟩

end GeneralPieces
