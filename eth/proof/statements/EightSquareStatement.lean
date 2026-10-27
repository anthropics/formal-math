/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PiecesStatement
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Real.Basic

/-! # Lemma 2 from the eight-square identity: definitions and statements only

Section 4 of the paper, «Two crossing equalities as a sum of ⌈λ/3⌉ + 1 cheaper functions», which
starts from the eight-square identity of Degen and Graves. This file has no proofs. It imports parts
of Mathlib and
`PiecesStatement.lean` (which imports only Mathlib), from which it takes: `Pieces.Bits n` (strings
of n bits), `Pieces.Four n` (integer functions of four strings x, y, u, v), `Pieces.cross` ([x =
v][y = u]), `Pieces.rowwise`
(a function of (x,y) and (u,v)) and `Pieces.colwise` (a function of (x,u) and (y,v)).

The statements are `Eight.Signs` (the eight-square identity in the form used in Section 4) and
`Eight.LemPieces` (Lemma 2 without «computable in time poly(λ)», which needs a model of computation
that this file does not import). -/

@[expose] public section

namespace Eight

open Finset Polynomial

/-! ## The eight-square identity -/

/-- A block of three bits, p = (p₁, p₂, p₃). -/
abbrev Block : Type := Bool × Bool × Bool

/-- p ⊕ q, bit by bit. -/
def bxor (p q : Block) : Block := (p.1 ^^ q.1, p.2.1 ^^ q.2.1, p.2.2 ^^ q.2.2)

/-- φ(p,q) = Σ_{1 ≤ i ≤ j ≤ 3} p_i q_j + q₁p₂p₃ + p₁q₂p₃ + p₁p₂q₃, as a natural number. -/
def phi (p q : Block) : ℕ :=
  p.1.toNat * q.1.toNat + p.1.toNat * q.2.1.toNat + p.1.toNat * q.2.2.toNat + p.2.1.toNat * q.2.1.toNat + p.2.1.toNat * q.2.2.toNat
    + p.2.2.toNat * q.2.2.toNat
    + q.1.toNat * p.2.1.toNat * p.2.2.toNat + p.1.toNat * q.2.1.toNat * p.2.2.toNat + p.1.toNat * p.2.1.toNat * q.2.2.toNat

/-- The sign σ(p,q) = (−1)^{φ(p,q)}. -/
def sigma (p q : Block) : ℤ := (-1) ^ phi p q

/-- The eight-square identity, first form: for all blocks p, q, p', q' with p ⊕ q = p' ⊕ q' and q ≠
q', σ(p,q)σ(p',q') + σ(p,q')σ(p',q) = 0. -/
def Signs : Prop := ∀ p q p' q' : Block, bxor p q = bxor p' q' → q ≠ q' → sigma p q * sigma p' q' + sigma p q' * sigma p' q = 0

/-! ## The functions R and C of four blocks -/

/-- ψ_k(p,q) = [p ⊕ q = k]·σ(p,q). -/
def psi (k p q : Block) : ℤ := if bxor p q = k then sigma p q else 0

/-- R(x,y,u,v) = Σ_k ψ_k(x,y)·ψ_k(v,u). -/
def Rb (x y u v : Block) : ℤ := ∑ k, psi k x y * psi k v u

/-- C(x,y,u,v) = Σ_k ψ_k(x,u)·ψ_k(v,y). -/
def Cb (x y u v : Block) : ℤ := ∑ k, psi k x u * psi k v y

/-- Definition 1 of the paper with a bound: F(z,z') = Σ_θ f(z,θ)·f'(z',θ) over θ ∈ {0,1}^c, and all
values of f and f' are at most b in absolute value. (`Pieces.FactorsThrough` has the strict bound
«below b».) -/
def FactorsLe {Z Z' : Type} (F : Z → Z' → ℤ) (c : ℕ) (b : ℤ) : Prop :=
  ∃ (f : Z → Pieces.Bits c → ℤ) (f' : Z' → Pieces.Bits c → ℤ),
    (∀ z z', F z z' = ∑ θ, f z θ * f' z' θ) ∧ (∀ z θ, |f z θ| ≤ b) ∧ ∀ z' θ, |f' z' θ| ≤ b

/-! ## The pieces A_0, …, A_t -/

/-- t = ⌈λ/3⌉. -/
def tOf (lam : ℕ) : ℕ := (lam + 2) / 3

/-- The bit number j (from 0) of a string after zeros have been appended. -/
def bitAt {lam : ℕ} (x : Pieces.Bits lam) (j : ℕ) : Bool := if h : j < lam then x ⟨j, h⟩ else false

/-- The block number s (from 0) of a string after zeros have been appended. -/
def blockAt {lam : ℕ} (x : Pieces.Bits lam) (s : ℕ) : Block := (bitAt x (3 * s), bitAt x (3 * s + 1), bitAt x (3 * s + 2))

/-- ∏_s (R(x_s,y_s,u_s,v_s) + T·C(x_s,y_s,u_s,v_s)), a polynomial in T; the blocks are numbered s =
0, …, t − 1. -/
noncomputable def prodRC {lam : ℕ} (x y u v : Pieces.Bits lam) : ℤ[X] :=
  ∏ s ∈ range (tOf lam), (C (Rb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s)) + X * C (Cb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s)))

/-- A_i: the coefficient of T^i. -/
noncomputable def A (lam i : ℕ) : Pieces.Four lam := fun x y u v => (prodRC x y u v).coeff i

/-- c_i^row = min{2λ, 4t + 3i}. -/
def crow (lam i : ℕ) : ℕ := min (2 * lam) (4 * tOf lam + 3 * i)

/-- c_i^col = min{2λ, 7t − 3i}. (For i ≤ t the subtraction of natural numbers is the ordinary one.) -/
def ccol (lam i : ℕ) : ℕ := min (2 * lam) (7 * tOf lam - 3 * i)

/-- ρ = 11/12. -/
noncomputable def rho : ℝ := 11 / 12

/-- **Lemma 2**, without «computable in time poly(λ)». For every λ ≥ 1 and i ∈ {0, …, t}: (a) A_0 +
… + A_t = 2^t·[x = v][y = u], and |A_i| ≤ 2^t; (b) as a function of (x,y) and (u,v), A_i factors
through c_i^row bits, as a
function of (x,u) and (y,v) through c_i^col bits, and the functions of both factorizations have
values at most 2^t in absolute value; (c) c_i^row ≤ 2λ, c_i^col ≤ 2λ and c_i^row + c_i^col ≤ 4ρλ +
8, where ρ = 11/12. -/
structure LemPieces : Prop where
  a_sum : ∀ lam : ℕ, 1 ≤ lam → ∀ x y u v : Pieces.Bits lam, ∑ i ∈ range (tOf lam + 1), A lam i x y u v = 2 ^ tOf lam * Pieces.cross x y u v
  a_abs : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → ∀ x y u v : Pieces.Bits lam, |A lam i x y u v| ≤ 2 ^ tOf lam
  b_row : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → FactorsLe (Pieces.rowwise (A lam i)) (crow lam i) (2 ^ tOf lam)
  b_col : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → FactorsLe (Pieces.colwise (A lam i)) (ccol lam i) (2 ^ tOf lam)
  c_row : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → crow lam i ≤ 2 * lam
  c_col : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → ccol lam i ≤ 2 * lam
  /-- from the proof of (c): c_i^row + c_i^col ≤ 11t -/
  c_sum_t : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → crow lam i + ccol lam i ≤ 11 * tOf lam
  c_sum : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → ((crow lam i + ccol lam i : ℕ) : ℝ) ≤ 4 * rho * lam + 8

end Eight
