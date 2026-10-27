/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.Top

/-! # Any network on 3K⁸ nodes through a clique solver: definitions and the interface statements

What a top network other than that of Section 6 (for example the network of marks of the theorem on
n variables) plugs into: the network is rebalanced to K nodes with labels of a length that is
computed from bounds Ub ≥ U and P, and handed to the solver. `countG` of Alg/Top.lean is the case of
the network of a formula. -/

@[expose] public section

namespace ClauseBound.Alg

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F

variable {Idx : Type} [Enc Idx] (S : Solver Idx)

/-- An upper bound for the label length of the instance on K nodes that a network on g nodes with U
≤ Ub and size P is rebalanced to. -/
def lamS (K g Ub P : ℕ) : ℕ := (K ^ 3 + K * Ub + g * P) / K ^ 3

/-- An upper bound for the bit length of the entries of that instance, if the values of the network
have at most B bits. -/
def bitsS (K g P B : ℕ) : ℕ := P * (2 * g / K) + B * (2 * g / K + 2 * g / K * (2 * g / K)) * K

/-- The value of the network that F presents in the context c, through the solver at the index i. -/
def valS {C : Type} (pad : U) (i : Idx) (Ub P : ℕ) (F : FNet C) (c : C) : ℤ :=
  (rebalG pad (S.K i) (3 * S.K i ^ 8) (lamS (S.K i) (3 * S.K i ^ 8) Ub P) F c).elim 0 fun I => S.run (pad, i, I)

/-- The exponent of a pad that suffices for that. -/
def needNet (i : Idx) (Ub P B : ℕ) : ℕ :=
  max (max (3 * S.K i ^ 8 * Nat.size (S.K i)) (P * (2 * (3 * S.K i ^ 8) / S.K i + 1)))
    (max ((S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) Ub P)
      (S.need (i, List.replicate (lamS (S.K i) (3 * S.K i ^ 8) Ub P) (), List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) P B) ())))

def StValS : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (ok : Idx → Prop), S.Correct ok → ∀ (C : Type) (F : FNet C) (c : C) (pad : U) (i : Idx)
  (N : Network (Fin (3 * S.K i ^ 8)) (List Bool) (List Bool)) (Ub P B : ℕ), ok i → 2 ≤ S.K i → F.toP.Presents c N 0 0 → N.Sized P B → N.U ≤ Ub →
  2 ^ needNet S i Ub P B ≤ pad.length → valS S pad i Ub P F c = N.value

def StCertValS : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly → ∀ (C : Type) [Enc C] (F : FNet C), FKeeps F →
  ∀ (α : Type) [Enc α] (pad : α → U) (i : α → Idx) (Ub P : α → ℕ) (c : α → C), PolyT pad → PolyT i → Unary Ub → Unary P → PolyT c →
  PolyT fun t => valS S (pad t) (i t) (Ub t) (P t) F (c t)

end ClauseBound.Alg
