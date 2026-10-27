/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.SecCrossing_PolyDefs
public import StepMachines.Prog.Chunks

/-! # Lemma 2(b): the factorization of the product that belongs to one set Q of blocks (a statement only)

Proof of Lemma 2(b): the product with C at the blocks in Q and R at the others has a row-wise
factorization (f_Q, f'_Q) through 3(t − i) + 6i bits, whose index θ' lists the blocks s = 1, …, t in
order.
`StChunk` says this for a fixed Q, in both directions at once: the sum over all words θ' of the
product of the two functions is the product over the blocks. The four strings are called a, b
(arguments of the first function) and
a', b' (arguments of the second). A block that is not wide contributes Σ_k ψ_k(a,b)·ψ_k(b',a') =
R(a,b,a',b'); a wide block contributes Σ_{k,k'} [(a,b) = (k,k')]·R(k,a',k',b') = R(a,a',b,b'). -/

@[expose] public section

namespace Eight

open Groundwork Groundwork.Prog PaddedDescent.F Finset

/-- The number of bits of θ': 3 for each block and 3 more for each wide block. -/
def lenW (tr : Bool) (Q : List Bool) (t : ℕ) : ℕ := 3 * t + 3 * (List.range t).countP (wide tr Q)

/-- The factorization of the product that belongs to Q. -/
def StChunk : Prop := ∀ (tr : Bool) (t : ℕ) (Q a b a' b' : List Bool),
  ∑ w ∈ words (lenW tr Q t), prodL t (topAt tr Q w a b) * prodL t (botAt tr Q w a' b') =
    ∏ s ∈ range t, if wide tr Q s = true then Rb (blkL a s) (blkL a' s) (blkL b s) (blkL b' s) else Rb (blkL a s) (blkL b s) (blkL a' s) (blkL b' s)

end Eight
