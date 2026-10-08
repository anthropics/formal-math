/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.LightModel

/-!
# Theorem 17 as a claim about programs of the light language

`Claim.Theorem_17 M MM D g` says: from every solver of Lop-AE-SparseTri with running time `T` there
is a solver of Exact Triangle whose running time is at most
`4ng (T + C n²/√D) + C (κ n³ log n/g + MM(n) D^{3/2} + n² D g)` (`bound17`, with the three terms
`termScans`, `termPrime`, `termBuild` of the additional time).  Here `κ` is the exponent in
`|w(e)| ≤ n^κ` (the paper's ν), `D` and `g` are the parameters of the reduction as functions of
`n`, `MM(n)` is the number of ring operations of the matrix multiplication, and `M` says what
"solved in time" means.
This file reduces the claim, for the interpretation by programs of the light language, to two facts
about a host: it turns solvers into solvers and keeps their need (word size, cells, depth of calls)
polynomial, and its time function obeys the bound (`ObeysBound17`, `claim17_of_host`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp

/-- The right-hand side of `Claim.Theorem_17`. -/
noncomputable def bound17 (MM : ℕ → ℝ) (D g : ℕ → ℕ) (C : ℝ) (T : ℕ → ℕ → ℕ → ℝ) (n : ℕ)
    (κ : ℝ) : ℝ :=
  4 * (n : ℝ) * (g n : ℝ) * (T n (D n) (queryCap n (D n)) + C * ((n : ℝ) ^ 2 / Real.sqrt (D n))) +
    C * (termScans n (g n) κ + termPrime MM n (D n) + termBuild n (D n) (g n))

/-- The time of a host, as a function `time` of the time of the solver, obeys the bound of
Theorem 17 with some constant: whenever `T` bounds the time `Tn` of the solver, `bound17` with `T`
bounds `time Tn`, under the hypotheses of the theorem. -/
def ObeysBound17 (MM : ℕ → ℝ) (D g : ℕ → ℕ) (time : (List ℕ → ℕ) → ℕ → ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (Tn : List ℕ → ℕ) (T : ℕ → ℕ → ℕ → ℝ),
    (∀ m d w w' : ℕ, 1 ≤ m → 1 ≤ d → w ≤ w' → (Tn [m, d, w] : ℝ) ≤ T m d w') →
    ∀ (n U : ℕ) (κ : ℝ), 16 ≤ D n → D n ≤ n → 1 ≤ g n → (g n : ℝ) ≤ Real.sqrt (D n) → 1 ≤ κ →
      (U : ℝ) ≤ (n : ℝ) ^ κ → (time Tn n U : ℝ) ≤ bound17 MM D g C T n κ

/-- **From a host to the claim.**  `time` and `need` are the host's time and need as functions of
those of the solver.  A program has a natural number `U` as the bound on the weights and the claim a
real number `u`; the time for `u` is the largest time for a `U ≤ u`. -/
theorem claim17_of_host (MM : ℕ → ℝ) (D g : ℕ → ℕ) (time : (List ℕ → ℕ) → ℕ → ℕ → ℕ)
    (need : (List ℕ → Need) → ℕ → ℕ → Need)
    (host : ∀ (Q : Program) (pS : ℕ) (Tn : List ℕ → ℕ) (r : List ℕ → Need), PolyNeedN r →
      SolvesN lopDetectTask Q pS Tn r →
      ∃ (R : Program) (p' : ℕ), Solves etTask (Q ++ R) p' (time Tn) (need r) ∧ PolyNeed (need r))
    (bound : ObeysBound17 MM D g time) :
    Claim.Theorem_17 lightModel MM D g := by
  obtain ⟨C, hC, bound⟩ := bound
  refine ⟨C, hC, fun T hT => ?_⟩
  obtain ⟨Q, pS, Tn, r, hpoly, hsolves, hle⟩ := hT
  obtain ⟨R, p', hs, hp⟩ := host Q pS Tn r hpoly hsolves
  exact ⟨timeUpTo (time Tn), hs.solvedIn hp, fun n κ u h16 hDn hg1 hg hκ hu =>
    timeUpTo_le fun U hU =>
      bound Tn T hle n U κ h16 hDn hg1 hg hκ (hU.trans (max_le hu (by positivity)))⟩

end Light.Sec3
