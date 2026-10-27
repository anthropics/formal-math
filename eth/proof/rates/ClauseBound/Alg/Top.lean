/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.Interfaces
public import CountKSatRate.Interfaces

/-! # The definitions, part 3, and the interface lemmas of the top level in m

From a clique solver with a sequence of indices to ONE function of (input, pad) and ONE exponent
function of the input, with the statements on their correctness, on their polynomial cost and on the
size of the exponent. -/

@[expose] public section

namespace ClauseBound.Alg

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat

/-- k in unary: the leading 1s of the input. -/
def kOf (x : List Bool) : U := (x.takeWhile id).map fun _ => ()

/-- The input after 1ᵏ 0. -/
def restOf (x : List Bool) : List Bool := (x.dropWhile id).drop 1

/-- (n in unary, the formula). -/
def fmlOf (x : List Bool) : U × Fml := decU (kOf x).length (restOf x)

/-- ⌊m^{1/9}⌋ in unary. -/
def root9 (m : ℕ) : U := List.replicate (((List.range (m + 1)).filter fun b => decide (b ^ 9 ≤ m)).length - 1) ()

section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

/-- P of the network of a k-CNF with m clauses on g nodes. -/
def PtopK (g k m : ℕ) : ℕ := max 1 (2 * k * ((m + g - 1) / g))

/-- An upper bound for the label length of the top instance (U ≤ 2km). -/
def lamTopK (K g k m : ℕ) : ℕ := (K ^ 3 + K * (2 * k * m) + g * PtopK g k m) / K ^ 3

/-- The value of the network of ψ on 3K⁸ nodes: rebalanced to K nodes with labels of exactly
`lamTopK` bits, then the solver at the index i. -/
def countG (pad : U) (i : Idx) (ku : U) (ψ : Fml) : ℤ :=
  (rebalG pad (S.K i) (3 * S.K i ^ 8) (lamTopK (S.K i) (3 * S.K i ^ 8) ku.length ψ.length) satFk
    ((List.replicate (3 * S.K i ^ 8) (), ku), ψ)).elim 0 fun I => S.run (pad, i, I)

/-- The exponent of a pad that suffices for a k-CNF with m clauses at the index i. -/
def needTop (i : Idx) (k m : ℕ) : ℕ :=
  max (max (3 * S.K i ^ 8 * Nat.size (S.K i)) (PtopK (3 * S.K i ^ 8) k m * (2 * (3 * S.K i ^ 8) / S.K i + 1)))
    (max ((S.K i - 1) * lamTopK (S.K i) (3 * S.K i ^ 8) k m)
      (S.need (i, List.replicate (lamTopK (S.K i) (3 * S.K i ^ 8) k m) (),
        List.replicate (PtopK (3 * S.K i ^ 8) k m * (2 * (3 * S.K i ^ 8) / S.K i)) ())))

/-- `needTop` computed under the bound b; `none` if it is larger. -/
def needTopC (b : U) (i : Idx) (k m : ℕ) : Option ℕ :=
  (S.needC (b, i, List.replicate (lamTopK (S.K i) (3 * S.K i ^ 8) k m) (),
      List.replicate (PtopK (3 * S.K i ^ 8) k m * (2 * (3 * S.K i ^ 8) / S.K i)) ())).bind fun v =>
    if max (max (3 * S.K i ^ 8 * Nat.size (S.K i)) (PtopK (3 * S.K i ^ 8) k m * (2 * (3 * S.K i ^ 8) / S.K i + 1)))
        (max ((S.K i - 1) * lamTopK (S.K i) (3 * S.K i ^ 8) k m) v) ≤ b.length
    then some (max (max (3 * S.K i ^ 8 * Nat.size (S.K i)) (PtopK (3 * S.K i ^ 8) k m * (2 * (3 * S.K i ^ 8) / S.K i + 1)))
        (max ((S.K i - 1) * lamTopK (S.K i) (3 * S.K i ^ 8) k m) v))
    else none

/-- The exponent of the clique algorithm at the level picked for m, if it is at most n; `none` if
exhaustive counting is at least as good. -/
def planM (pick : U → U × Idx) (x : List Bool) : Option ℕ :=
  needTopC S (fmlOf x).1 (pick (root9 (fmlOf x).2.length)).2 (kOf x).length (fmlOf x).2.length

/-- THE exponent function: the smaller of n and the exponent of the clique algorithm. -/
def eM (pick : U → U × Idx) (x : List Bool) : ℕ := (planM S pick x).getD (fmlOf x).1.length

/-- THE function: the number of satisfying assignments of the formula written in p.1, in n + 1 bits,
when the pad p.2 is long enough. -/
def AM (pick : U → U × Idx) (p : List Bool × U) : List Bool :=
  outW (fmlOf p.1,
    bif (planM S pick p.1).isNone then ((rng p.2 (2 ^ (fmlOf p.1).1.length)).filter fun y => satAt (fmlOf p.1).2 y).length
    else bif hasNil (fmlOf p.1).2 then 0
    else (countG S p.2 (pick (root9 (fmlOf p.1).2.length)).2 (kOf p.1) (fmlOf p.1).2).toNat)

end

/-! ### Decoding the input -/

def StDecM : Prop := ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → (∀ C ∈ φ, C.length ≤ k) →
  kOf (SatM.enc k φ) = List.replicate k () ∧ fmlOf (SatM.enc k φ) = (List.replicate n (), Decode.toN φ)

def StCertDecM : Prop := PolyT kOf ∧ PolyT fmlOf

/-! ### The value of the top instance -/

/-- The solver at the index i, fed with the rebalanced network of ψ, returns the value of that
network. -/
def StCountG : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (ok : Idx → Prop), S.Correct ok → ∀ (pad : U) (i : Idx) (k : ℕ) (ψ : Fml), ok i → 2 ≤ S.K i → 1 ≤ k →
  (∀ C ∈ ψ, C.length ≤ k) → 2 ^ needTop S i k ψ.length ≤ pad.length →
  countG S pad i (List.replicate k ()) ψ = (Count.wordNet (3 * S.K i ^ 8) k ψ).value

/-- Correctness of `AM`: on the code of a k-CNF with at least one clause in which all n variables
occur, and a pad of at least 2^(`eM`) units, it returns the number of satisfying assignments in n +
1 bits. -/
def StCorrectM : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (k n : ℕ) (φ : Sat3.CNF n),
  1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → SatM.AllOccur φ → ∀ pad : U, 2 ^ eM S Q.pick (SatM.enc k φ) ≤ pad.length →
  AM S Q.pick (SatM.enc k φ, pad) = SatK.binary n (SatK.numSat φ)

/-! ### Polynomial-time bounds -/

def StCertSatK : Prop := FKeeps satFk

def StCertM : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly → ∀ pick : U → U × Idx, PolyT pick → PolyT (AM S pick) ∧ PolyT (eM S pick)

/-! ### The exponent is O(k·m·e) -/

/-- Part (c) of the theorems, as an inequality: with l the level picked for m, the exponent is at
most A·k·m·e_l. -/
def StTopArith : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), ∃ A : ℕ, ∀ k m : ℕ, 1 ≤ k → S.K (Q.idx 0) ^ 9 ≤ m →
  (needTop S (Q.pick (root9 m)).2 k m : ℝ) ≤ A * k * m * e (Q.pick (root9 m)).1.length

end ClauseBound.Alg
