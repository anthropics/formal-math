/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Contracts

/-!
# 3SUM from Convolution-3SUM: the time and the need of the host

The host s3(n, U, x, fr) has a parameter `κ` (a natural number, fixed with the program): it first
replaces the bound `U` by `max U (n^κ)`. So on all inputs with `U ≤ n^κ` it asks the
Convolution-3SUM solver for instances of one and the same length and bound, `8 m²` and
`120 n^κ + 40` with `m = mPar n (2 n^κ)`. (A running time `T N B` of an arbitrary solver need not be
monotone in `N`.)

The time is split into the host's own work and the number of calls of the solver. This file has the
definitions and one identity (`tNodes_eq`); the arithmetic (`claim_CH20_Theorem_5_1_of_host`) starts
from them.
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe Finset

/-- An upper bound on the number of calls of the recursive procedure for one three-set input. -/
def callsB (n : ℕ) : ℕ := 2 * 3 ^ fuel n

/-- The cost of one call of the recursive procedure without the call of the solver. -/
def nodeOwn (n V m np : ℕ) : ℕ := tModulus np n n n V + tNodeArray m n n n V + 3 * tHeavy n V + 360

/-- The time of the recursive procedure, split into its own work and the calls of the solver. -/
theorem tNodes_eq (T : ℕ → ℕ → ℕ) (n V m np calls : ℕ) :
    tNodes T n V m np calls = calls * (nodeOwn n V m np + T (8 * m ^ 2) (60 * V + 40)) := by
  unfold tNodes tNode nodeOwn
  ring

/-- The time of params: four logarithms and a square root. -/
def tParams (n V : ℕ) : ℕ :=
  tLog2 (2 * V) + (18 * Nat.sqrt n + 12) + tLog2 (wPar n V + 1) + tLog2 n +
    (tLog2 (Nat.log 2 n + 2) + 30) + 160

/-- The time of prep: primes, count table, a copy, sorting, distinct values, binary digits. -/
def tPrep (n Λ m : ℕ) : ℕ :=
  tPrimes m + (13 * (m * m) + 6) + (16 * n + 6) + tSort n + tDistinct n + tBits n Λ + 240

/-- The time of params and prep. -/
def tSetup (n V : ℕ) : ℕ := tParams n V + tPrep n (Lam V) (mPar n V)

/-- The number of three-set inputs. -/
def inputsB (V : ℕ) : ℕ := 2 * Lam V ^ 2 + 2

/-- The number of calls of the solver, for the bound `V = 2U`. -/
def coreCalls (n V : ℕ) : ℕ := inputsB V * callsB n

/-- The host's own work, for the bound `V = 2U`. -/
def coreOwn (n V : ℕ) : ℕ :=
  tSetup n V + inputsB V * (callsB n * nodeOwn n V (mPar n V) #(Nat.primesLE (mPar n V)) + 3 *
    tPick n + 300) + tTwice n + tZeroThree n + 400

/-- The time of the host after the bound has been fixed. -/
def coreTime (T : ℕ → ℕ → ℕ) (n V : ℕ) : ℕ :=
  coreOwn n V + coreCalls n V * T (8 * mPar n V ^ 2) (60 * V + 40)

/-- **The time of the host.** -/
def chTime (κ : ℕ) (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ := 20 * κ + 40 + coreTime T n (2 * max U (n ^ κ))

/-- The cells of the host's own arrays: the block of parameters, the primes, the count table, the
sorted copy, values and multiplicities, the binary digits, three sets for a splitting, the doubles,
and one cell for the set {0}. -/
def coreCells (n V : ℕ) : ℕ := 6 + mPar n V + mPar n V * mPar n V + 7 * n + n * Lam V + 1

/-- The need of the host after the bound has been fixed. -/
def coreNeed (r : ℕ → ℕ → Need) (n V : ℕ) : Need :=
  ⟨(nodesNeed r n V (mPar n V) (fuel n)).word + 8 * (mPar n V + 1) ^ 2 + 8 * V + 4 * n + 64,
    coreCells n V + (nodesNeed r n V (mPar n V) (fuel n)).cells + mPar n V + n + Lam V + 8,
    (nodesNeed r n V (mPar n V) (fuel n)).depth + Nat.log 2 n + 6⟩

/-- **The need of the host.** -/
def chNeed (κ : ℕ) (r : ℕ → ℕ → Need) (n U : ℕ) : Need :=
  ⟨(coreNeed r n (2 * max U (n ^ κ))).word + 2 * n ^ κ + 2 * U,
    (coreNeed r n (2 * max U (n ^ κ))).cells,
    (coreNeed r n (2 * max U (n ^ κ))).depth + 1⟩

end Light.Sec3.ChanHe
