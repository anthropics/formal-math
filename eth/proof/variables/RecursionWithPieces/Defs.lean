/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsifyThenCount.PlanUsedDefs
public import GeneralPieces.Tied.BoundDefs
public import VariableBound.Printed.ThmVariablesADefs

/-! # The function for Theorem 1 on the recursion of Appendix A with the pieces of Appendix B: definitions and statements

`GeneralPieces.Tied.BoundInM` (proof/rates/GeneralPieces/Tied/BoundDefs.lean) is the bound in m for
the algorithm `AM` on the recursion of Appendix A, on the schedule of display (40) with the least x₀
of the theorem on the
general recursion, for programs for the pieces of Appendix B. The merged function
`SparsifyThenCount.ABDG` (proof/variables/SparsifyThenCount/Defs.lean), for the three bounds of
Theorem 1, sparsifies and counts each output by Steps 1 to 4 of
Appendix D, and it takes the solver for cliques, the function `pick` that chooses the level, and the
precision as arguments.
Here it is given those of Appendices A and B.

* `solverAB P₀ val c`: the recursion `solveG` as a solver for cliques (`solverOf`), on the programs
  `GeneralPieces.Tied.recOf P₀ val c`: the pieces (P₀, val) after «we may and do assume c^row, c^col
  ≤ 2λ».
* `pickAB P₀ val c`: the program `ClauseBound.Gen.Pick.pick` with x₀ = `GeneralPieces.x₀Of c`, the
  least x₀ ≥ 18 with 2^x₀ ≥ c + 5. From a bound in unary it gives the largest ℓ with K_ℓ ≤ bound (ℓ =
  0 if the bound is below K₀) and the schedule of
  display (40) for that ℓ (`GeneralPieces.pick_spec`).
* `prec`: the precision s(ℓ) = ℓ + 1, in unary, so ε = 2^(−(ℓ+1)). With ρ = 1/√2 this lies between
  e_ℓ²/2 and 2e_ℓ², where Step 5 takes ε between e_ℓ and 2e_ℓ.
* `fnAll Θ P₀ val c` and `expAll P₀ val c`: `SparsifyThenCount.ABDG Θ` and `VariableBound.eBD` on
  these three.
* `TiedAt Θ c P₀ A val`: seven statements about these functions. `TiedEvery Θ`: they hold for all c,
  P₀, A, val that are the pieces of Appendix B. `TiedAll Θ`: they hold for some c, P₀, A, val.
  `TiedAllCal`: `TiedAll` for `StepSparsify.thCal`,
  the thresholds θ_0 = 2, θ_c = α·β_c, taken to be Calabro's and not checked against Calabro's
  dissertation (the paper does not print them), with α = ⌈2(k−1)²ε⁻¹⌈log₂(32(k−1)²/ε)⌉⌉, for max(k, 3)
  in place of k and ε = 2^(−s).

**What is named and what is quantified.** Named: the recursion, the schedule, x₀ as a function of c,
the choice of the level, the precision, the thresholds, the walk through the counting tree, the
count of a leaf, the algorithm for the bound in
m, the merge, the exponent of the pad. Quantified (universally in `TiedEvery`, existentially in
`TiedAll`): the constant c and the programs (P₀, val) for the pieces, with the functions A that they
compute. Of these the first field of `TiedAt` says that they are pieces with parameters (1/√2, c)
as Appendix A defines them, and that h, μ(x), the index set, d = h!, the functions A_s and the
numbers of bits are those of the proof of the theorem on pieces with ρ = 1/√2 in Appendix B. The
programs themselves are not fixed by that.

**What a tied statement says and does not say.** It fixes the function that the machine computes on
every input, not the steps of the machine. On the code of a formula, with the pad that the machine
uses, `fnAll Θ …` has the same value, the
number of satisfying assignments, for every family Θ that serves and for all c, P₀, val of which the
statement holds. What ties the bounds to this function is the field `alg`: the function and `expAll`
are polynomial-time, the function is right when the pad has at least
2^(`expAll`) units, and for every q the number q·(|x| + 2^(`expAll` x) + 1)^q, which bounds the
steps of the padding machine, is within the bounds. The statement names the algorithm. It does not
force an argument: that the groupings inside the recursion exist by
case (ii) of the lemma on groupings with explicit cost, with Hoeffding's inequality, is seen in the
proofs, not in the statement. The field `partB` says that every step of the schedule meets the
hypotheses of case (ii).
Nor does it say how a network at the top level is handed to the solver; the proofs use case (i) of
that lemma, as the paper does (proof/variables/RecursionWithPieces/Main.lean). In `TiedAll` the
constant c is only said to exist, and x₀ = x₀Of c grows with it. For x₀ ≥ 21, that is c ≥ 2^20 − 4,
a
counting condition that would give the groupings without case (ii) seems to hold at every step too
(seen numerically, not proved in Lean; see proof/rates/GeneralPieces/Tied/BoundDefs.lean), so the
statement does not rule out a proof without case (ii). `TiedEvery` has the seven parts for every c
for which
(c, P₀, A, val) are the pieces; if the pieces of Appendix B exist with some c ≤ 2^20 − 5, then x₀Of
c ≤ 20 and that counting condition fails at some step
(at x₀ = 18, 19 and 20), so that counting argument alone would not give those cases. Whether such a
c exists is not known: the c of the theorem on pieces is not explicit.

**What differs from the printed text.** Everything that proof/variables/SparsifyThenCount/Defs.lean
lists for Steps 5 and 6 (the range of k by computed tests, ε = 2^(−s), one Δ for all outputs, the
declared width, the side list of the walk) and
proof/variables/SparsifyThenCount/PlanUsedDefs.lean for the plan. The cost is counted through a pad,
in Appendices A and B as in Appendix D: a function that is polynomial-time in the input and a pad,
and a bound on 2^(exponent), the number of units that the pad must have; no count of
operations is stated. The bound in m and the bound with the minimum are for formulas in which every
variable occurs.
This file has definitions only; proof/variables/RecursionWithPieces/Main.lean proves `TiedAllCal`. -/

@[expose] public section

namespace RecursionWithPieces

open Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Gen VariableBound VariableBound.Decide SparsifyThenCount

/-! ### The functions -/

section
variable (Θ : ℕ → ℕ → ℕ → ℕ) (P₀ : PiecesF) (val : AppRunningTime.ValQ → ℤ) (c : ℕ)

/-- The solver for cliques of Appendix A: the recursion `solveG` on the programs `recOf P₀ val c`,
that is on the pieces (P₀, val) with every factorization through 2λ bits or more replaced. Its index
is a schedule with the number K₀ in unary. -/
def solverAB : Solver (List Step × U) := solverOf (GeneralPieces.Tied.recOf P₀ val c)

/-- The choice of the level: from a bound in unary, the largest ℓ with K_ℓ ≤ bound (in unary; ℓ = 0
if the bound is below K₀) and the schedule of display (40) for that ℓ, with x₀ the least integer
with x₀ ≥ 18 and 2^x₀ ≥ c + 5. -/
def pickAB : U → U × (List Step × U) := Pick.pick (GeneralPieces.Tied.recOf P₀ val c) (GeneralPieces.x₀Of c)

/-- The precision at level ℓ: s = ℓ + 1, in unary, so ε = 2^(−(ℓ+1)). With ρ = 1/√2 this lies
between e_ℓ²/2 and 2e_ℓ², where Step 5 takes ε between e_ℓ and 2e_ℓ. -/
def prec (u : U) : U := () :: u

/-- The merged function of (input, pad): `SparsifyThenCount.ABDG Θ` on the solver, the choice of the
level and the precision above. -/
def fnAll : List Bool × U → List Bool := ABDG Θ (solverAB P₀ val c) (pickAB P₀ val c) prec

/-- The exponent of its pad, a function of the input: `VariableBound.eBD` on the same three. -/
def expAll : List Bool → ℕ := eBD (solverAB P₀ val c) (pickAB P₀ val c) prec

end

/-! ### The end statement, tied to the functions -/

/-- The end statement for the thresholds Θ, the constant c and the programs (P₀, val) for the
functions A. The rates are log₂ log₂(n+4)/√(log₂(n+4)) in n and 1/√(log₂(m+2)) in m. -/
structure TiedAt (Θ : ℕ → ℕ → ℕ → ℕ) (c : ℕ) (P₀ : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ) : Prop where
  /-- (P₀, A, val) are the pieces of the proof of the theorem on pieces with ρ = 1/√2 in Appendix B,
  with the constant c: the body of `AppRunningTime.ThmHalfPieces` -/
  pieces : GeneralPieces.Tied.IsPiecesB c P₀ A val
  /-- part (b) of the theorem on the general recursion for the named program, with some constant C₀:
  the recursion on the schedule of display (40) for x₀ = `x₀Of c`; every step has the numbers of
  that display and meets the hypotheses of case (ii)
  of the lemma on groupings with explicit cost; the program is polynomial-time, returns the value of
  the clique if the pad has 2^needB units, and needB obeys the bound of part (b) -/
  partB : ∃ C₀ : ℕ, GeneralPieces.Tied.PartB (GeneralPieces.Tied.recOf P₀ val c) (1 / Real.sqrt 2) (GeneralPieces.x₀Of c) C₀
  /-- part (c), first sentence, for the named programs: the algorithm `AM` for the bound in m with
  its exponent `eM`, on `solverAB` and `pickAB`, at the rate 1/(log₂(m+2))^α' with α' = log₂(1/ρ) =
  log₂ √2; `AM` on these two is the branch of `fnAll` for the bound in m -/
  partCm : GeneralPieces.Tied.PartCm (GeneralPieces.Tied.recOf P₀ val c) (1 / Real.sqrt 2) (GeneralPieces.x₀Of c)
  /-- the pair (`fnAll`, `expAll`) is an algorithm for the two rates in the sense of
  `VariableBound.Decide.Alg`: both functions are polynomial-time; on the code of (k, φ), k ≥ 1, φ a
  k-CNF, with a pad of at least 2^(`expAll`) units, `fnAll` is the number of
  satisfying assignments in n + 1 bits; for every q the number q·(|x| + 2^(`expAll` x) + 1)^q, which
  bounds the steps of the padding machine, is within the bound in n if n ≥ 1, and within the bound
  in m if all variables occur and m ≥ 1, with
  constants that do not depend on k -/
  alg : Alg (SatK.rN 1 (1 / 2)) (SatM.rPow (1 / 2)) (fnAll Θ P₀ val c) (expAll P₀ val c)
  /-- one machine puts out, on every bit string x, the value of `fnAll` on x with a pad of
  2^(`expAll` x) units, within C·(|x| + 2^(`expAll` x) + 1)^C steps, and counts within the three
  bounds, each under its conditions (`VariableBound.TiedOut`) -/
  counts : TiedOut (fnAll Θ P₀ val c) (expAll P₀ val c) id (SatK.rN 1 (1 / 2)) (SatM.rPow (1 / 2))
  /-- a second machine does the same for «some bit is 1», that is, whether the count is not 0 -/
  decides : TiedOut (fnAll Θ P₀ val c) (expAll P₀ val c) bitOf (SatK.rN 1 (1 / 2)) (SatM.rPow (1 / 2))
  /-- for every width k ≥ 1 and all large n, the plan exists on the code of (k, φ), for every k-CNF
  φ on n variables; where the plan exists the branch `SparsifyThenCount.ADG Θ` for the bound in n is
  `SparsifyThenCount.numDG Θ`, the walk through the counting tree with every leaf counted by
  `VariableBound.countD`, not exhaustive counting -/
  planUsed : PlanUsed (solverAB P₀ val c) (pickAB P₀ val c) prec

/-- **The end statement tied to its functions, for all pieces.** For all c, P₀, A, val: if (P₀, A,
val) are the pieces of Appendix B with the constant c (`GeneralPieces.Tied.IsPiecesB`), then
`TiedAt Θ c P₀ A val` holds. By itself this does not say that such c, P₀, A, val exist;
`AppRunningTime.ThmHalfPieces` says that, and with it `TiedEvery Θ` gives `TiedAll Θ`. -/
def TiedEvery (Θ : ℕ → ℕ → ℕ → ℕ) : Prop := ∀ (c : ℕ) (P₀ : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ), GeneralPieces.Tied.IsPiecesB c P₀ A val → TiedAt Θ c P₀ A val

/-- **The end statement tied to its functions, with the thresholds Θ in the sparsification.** There
are a constant c and programs (P₀, val) for functions A, which the statement does not name (they are
existentially quantified), such that `TiedAt` holds:
they are the pieces of Appendix B; the recursion of Appendix A on them, on the schedule of display (40)
with the least x₀ of the theorem, satisfies parts (b) and (c), first sentence, of the theorem on the
general recursion; the
merged function `fnAll Θ` on that recursion, with the level chosen by the named program `pickAB` and
the precision s(ℓ) = ℓ + 1, is with `expAll` an algorithm for the rates log₂ log₂(n+4)/√(log₂(n+4))
and 1/√(log₂(m+2)); one machine puts out
its value on every bit string and counts within the three bounds; a second machine does the same for
«some bit is 1»; and the plan is used. The statement fixes what the machines put out and a bound on
their steps, not the steps themselves. -/
def TiedAll (Θ : ℕ → ℕ → ℕ → ℕ) : Prop := ∃ (c : ℕ) (P₀ : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ), TiedAt Θ c P₀ A val

/-- `TiedAll` for the thresholds `StepSparsify.thCal`: θ_0 = 2, θ_c = α·β_c, taken to be Calabro's
(the paper does not print them), for max(k, 3) in place of k and ε = 2^(−s). -/
def TiedAllCal : Prop := TiedAll StepSparsify.thCal

end RecursionWithPieces
