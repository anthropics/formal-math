/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import AppRunningTimeStatement
public import GeneralPieces.DefGenPieces.Progs
public import GeneralPieces.Tied.Defs
public import Eight.SecCrossing_PolyDefs

/-! # Appendix A: the pieces of Lemma 2 are pieces with parameters (11/12, c)

Definitions and statements only. The functions A_0, …, A_t, the numbers t, c^row_i, c^col_i are
those of `EightSquareStatement.lean` (namespace `Eight`); the programs for the two factorizations
(`Eight.eightF`) and for the
values (`Eight.aMul`) are those of `proof/networks/Eight/SecCrossing_PolyDefs.lean`. «Pieces with
parameters (ρ, c)» is `AppRunningTime.IsPieces` of `AppRunningTimeStatement.lean`, which also says
how «within T operations» is rendered. -/

@[expose] public section

namespace AppRunningTime

open Eight

/-- The program for the value of a piece of Lemma 2, as a function of (pad, (λ in unary, number i of
the piece), (x, y, u, v)). It uses neither the pad nor λ. -/
def valEight (q : ValQ) : ℤ := aMul (q.2.1.2, q.2.2)

/-- The sentences after the definition of pieces: «By Lemma 2, the functions A_0, …, A_t of
Definition 5 are pieces with parameters (11/12, c), with 𝓘 = {0, …, t}, d = 2^t and the numbers
c^row_i, c^col_i defined there, for which
c^row_i + c^col_i ≤ 11λ/3 + 8. This holds for every integer c ≥ 8 such that 2^{cλ} exceeds the
polynomial running times in Lemma 2 for all λ ≥ 1.» Here it holds for every c ≥ 8: the programs are
polynomial-time and have
no loop that a pad cuts off, so the second condition on c does not occur. -/
def LemPiecesPieces : Prop := ∀ c : ℕ, 8 ≤ c → IsPieces (11 / 12) c eightF A valEight ∧
  ∀ lam, 1 ≤ lam → eightF.cnt 0 lam = tOf lam + 1 ∧ eightF.d 0 lam = 2 ^ tOf lam ∧
    ∀ i ≤ tOf lam, eightF.cap false 0 lam i = crow lam i ∧ eightF.cap true 0 lam i = ccol lam i ∧ ((crow lam i + ccol lam i : ℕ) : ℝ) ≤ 11 * lam / 3 + 8

end AppRunningTime
