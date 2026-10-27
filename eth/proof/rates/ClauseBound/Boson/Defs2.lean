/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Boson.Defs
public import ClauseBound.Part.Bits
public import PiecesStatement

/-! # The dual families and the operators Q_s: definitions

A combination of monomials with integer coefficients is a list of pairs (coefficient, list of
parts). Definitions only. -/

@[expose] public section

namespace ClauseBound.Boson

open Finset

/-- A combination of monomials. -/
abbrev FA : Type := List (ℤ × List ℕ)

/-- (−1)^{n−1}·y_n, where y_n = Σ_{j=1}^{n} C(n,j)·t_j. -/
def yl (n : ℕ) : List (ℤ × ℕ) := (List.range n).map fun i => ((-1) ^ (n - 1) * (n.choose (i + 1) : ℤ), i + 1)

/-- a^μ = ∏_i (−1)^{μ_i−1}·y_{μ_i}, multiplied out. -/
def aFam : List ℕ → FA
  | [] => [(1, [])]
  | n :: μ => (yl n).flatMap fun cj => (aFam μ).map fun cL => (cj.1 * cL.1, cj.2 :: cL.2)

/-- z_ν = ∏_k k^{m_k}·m_k!, where m_k is the number of parts equal to k. -/
def zz (ν : Multiset ℕ) : ℕ := ∏ k ∈ ν.toFinset, k ^ ν.count k * (ν.count k).factorial

/-- Q_s(a,b) = Σ_{i=0}^{2h} (−1)^i·a^{⟨i⟩}[s−h+i]∘b[h−s−i], h the weight of b. -/
def Qk (A : FA) (b : List ℕ) (s : ℤ) : Ker := fun π σ =>
  ∑ i ∈ range (2 * b.sum + 1), (-1) ^ i *
    (A.map fun c => c.1 * ((c.2.sum + b.sum).choose i : ℤ) * mul2 c.2 (s - b.sum + i) b (b.sum - s - i) π σ).sum

/-- The same with the two factors of every product exchanged. -/
def Qk' (A : FA) (b : List ℕ) (s : ℤ) : Ker := fun π σ =>
  ∑ i ∈ range (2 * b.sum + 1), (-1) ^ i *
    (A.map fun c => c.1 * ((c.2.sum + b.sum).choose i : ℤ) * mul2 b (b.sum - s - i) c.2 (s - b.sum + i) π σ).sum

/-- All monomials of the combination have positive parts and weight at most h. -/
def FA.Ok (A : FA) (h : ℕ) : Prop := ∀ c ∈ A, Pos c.2 ∧ c.2.sum ≤ h

/-- The parts of a partition, as a list. -/
noncomputable def lst {h : ℕ} (q : Nat.Partition h) : List ℕ := q.parts.toList

end ClauseBound.Boson
