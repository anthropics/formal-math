/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Defs
public import UniformInK.Top.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Semiring

/-! # The sparsification theorem for the geometric thresholds: definitions and statements

The thresholds are `UniformInK.thetaU τ`: θ 0 = 1 and θ i = 4·τ^(2i−1); the numbers β are
`UniformInK.betaSU τ`: β 0 = 0 and β i = 4·τ^(2i−2). They satisfy `SparsificationLemma.ThrC` if 1 ≤
k and 8k ≤ τ.
Two forms of one theorem: for any τ that is large enough for ε (`StThmTau`); and for τ = 2^(4s+17),
with 2^(−s) in the role of ε, which is what the end theorem for all widths k uses (`StThmS`).
For a rational ε ∈ (0,1], τ = ⌈(8k/ε)³⌉ is large enough for k and ε (`tauE`, `StTauE`).
This file has definitions only. The statements are propositions; they are proved in other files. -/

@[expose] public section

namespace SparsificationLemma.Geo

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK PaddedDescent

/-- The thresholds `thetaU τ` with the numbers `betaSU τ` satisfy the four conditions, if 1 ≤ k and
8k ≤ τ. -/
def StThrGeo : Prop := ∀ k τ : ℕ, 1 ≤ k → 8 * k ≤ τ → ThrC k τ (thetaU τ) (betaSU τ)

/-- 2·(θ 0 + … + θ (k−1)) + 2 ≤ τ^(2k), if 1 ≤ k and 8 ≤ τ. -/
def StDegGeo : Prop := ∀ k τ : ℕ, 1 ≤ k → 8 ≤ τ → 2 * (∑ j ∈ range k, thetaU τ j) + 2 ≤ τ ^ (2 * k)

/-- The outputs for the parameter τ. Paths are cut after τ^(2k)·n steps; no path is longer
(`StThmTau`). -/
def outTau (k n τ : ℕ) (φ : PFml) : List PFml := outputs (thetaU τ) k (bsumU τ k * n) φ

/-- The theorem for any τ ≥ 8k with (k/τ)·log₂(e·τ·τ^(2k)) ≤ ε. The procedure stops on every path;
the outputs are k-CNFs on the same variables, none with a clause written twice; there are at most
2^(εn) of them;
every assignment that satisfies φ satisfies exactly one of them, and every other assignment none; a
variable occurs in at most τ^(2k) clauses of an output. -/
def StThmTau : Prop := ∀ (k n τ : ℕ) (ε : ℝ) (φ : PFml), 1 ≤ k → 8 * k ≤ τ →
  ((k : ℝ) / (τ : ℝ)) * Real.logb 2 (Real.exp 1 * (τ : ℝ) * (bsumU τ k : ℝ)) ≤ ε → IsKCNF k n φ →
  (∀ x ∈ tree (thetaU τ) k (bsumU τ k * n) φ, stepC (thetaU τ) k x = none) ∧
  (∀ Φ ∈ outTau k n τ φ, IsKCNF k n Φ ∧ Φ.Nodup) ∧
  ((outTau k n τ φ).length : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ)) ∧
  (∀ b, ExactlyOne b φ (outTau k n τ φ)) ∧
  ∀ Φ ∈ outTau k n τ φ, ∀ v, occN Φ v ≤ τ ^ (2 * k)

/-- The parameter for width k and a rational ε: τ = ⌈(8k/ε)³⌉. -/
def tauE (k : ℕ) (ε : ℚ) : ℕ := ⌈(8 * (k : ℚ) / ε) ^ 3⌉₊

/-- τ = ⌈(8k/ε)³⌉ is large enough for k and ε, and at most (9k/ε)³. -/
def StTauE : Prop := ∀ (k : ℕ) (ε : ℚ), 1 ≤ k → 0 < ε → ε ≤ 1 →
  8 * k ≤ tauE k ε ∧
  ((k : ℝ) / (tauE k ε : ℝ)) * Real.logb 2 (Real.exp 1 * (tauE k ε : ℝ) * (bsumU (tauE k ε) k : ℝ)) ≤ (ε : ℝ) ∧
  (tauE k ε : ℝ) ≤ (9 * (k : ℝ) / (ε : ℝ)) ^ 3

/-- The theorem for τ = 2^(4s+17) and s ≥ `s0U k` (then k² ≤ 2^s), with 2^(−s) in the role of ε: at
most 2^(n/2^s) outputs, so at most 2^(⌊n/2^s⌋+1); at most 2^(2k(4s+17)) occurrences of a variable. -/
def StThmS : Prop := ∀ (k n s : ℕ) (φ : PFml), 1 ≤ k → s0U k ≤ s → IsKCNF k n φ →
  (∀ x ∈ tree (thetaU (tauOf s)) k (bsumU (tauOf s) k * n) φ, stepC (thetaU (tauOf s)) k x = none) ∧
  (∀ Φ ∈ outTau k n (tauOf s) φ, IsKCNF k n Φ ∧ Φ.Nodup) ∧
  ((outTau k n (tauOf s) φ).length : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2 ^ s) ∧
  (outTau k n (tauOf s) φ).length ≤ 2 ^ (n / 2 ^ s + 1) ∧
  (∀ b, ExactlyOne b φ (outTau k n (tauOf s) φ)) ∧
  ∀ Φ ∈ outTau k n (tauOf s) φ, ∀ v, occN Φ v ≤ 2 ^ betaU k s

end SparsificationLemma.Geo
