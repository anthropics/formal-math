/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.Threshold
public import PaddedDescent.F.ArithInv

/-! # The numbers that stay fixed during the descent (definitions only)

For precision s and n variables: the bounds Ub and Pb of the network of marks, and the values of X,
Z, Qm, Wm, L with which the invariant `Inv` of
`PaddedDescent/F/ArithInv.lean` is used. -/

@[expose] public section

namespace PaddedDescent.F.Arith

/-- X = ⌊n/2^s⌋ + 1. The padding string, which the algorithm takes besides the formula, has length
2^(C₀·X) for a constant C₀. -/
def Xof (s n : ℕ) : ℕ := n / 2 ^ s + 1

/-- Z = Y², with Y = `Ytop s`: the part of the bound on K_j²·Λ_j (K_j nodes, Λ_j bits on an edge of
the clique at level j) that does not decay with j. -/
def Zof (s : ℕ) : ℕ := Ytop s ^ 2

/-- The bound on the number of shared bits of the network of marks at the top, for width k. -/
def Ubof (k s n : ℕ) : ℕ := Ub k (gtop s) n (n + 2) (betaOf s) (layersOf s + 2)

/-- The bound on the size of the network of marks at the top, if every variable occurs in at most Δ
clauses. -/
def Pbof (Δ s n : ℕ) : ℕ := Pb (gtop s) n (betaOf s) Δ

/-- Qm = Ub + X + Z: a bound on K_j²·Λ_j at all levels. -/
def Qmof (k s n : ℕ) : ℕ := Ubof k s n + Xof s n + Zof s

/-- Wm = 17·Qm·K³, where K = `Ktop s` is the number of nodes at the top level: a bound on the number
of bits of an entry at all levels. -/
def Wmof (k s n : ℕ) : ℕ := 17 * Qmof k s n * Ktop s ^ 3

/-- L = 6s + 24 + (binary digits of n): Qm + 1 ≤ 2^L. -/
def Lof (s n : ℕ) : ℕ := 6 * s + 24 + Nat.size n

end PaddedDescent.F.Arith
