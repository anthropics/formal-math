/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import MinOfBounds.Defs
public import PairsToBound.Defs
public import GeneralPieces.Tied.Defs
public import GeneralPieces.Tied.BoundDefs
public import RecursionToBound.Defs

/-! # The Main Theorem along the route of the paper: definitions and statements

**The text.** After Corollary 11: «This is the Main Theorem.» So the proof of Theorem 1 is the proof
of Corollary 11, whose route is: (1) Theorem B: there are pieces with parameters (1/√2, c). (2)
Theorem A (b) on these pieces: one algorithm for the cliques on K_ℓ nodes; Theorem D (b), first
sentence: its pairs (K_ℓ, e_ℓ) satisfy the hypothesis of
Theorem D (a). (3) Theorem D (a), applied to it. (4) Step 6: Theorem D (b). (5) Theorem A (c), first
sentence, with the same pieces: the bound in m. (6) Corollary 11: rename, run the algorithms of (5)
and (4) in alternation. (7) «This is the Main Theorem.»

**Why this statement.** `MainTheoremForms.MainTheoremCompact` says only that some machine has the
bound, whatever the proof. So here each bound is stated for EVERY machine that is made in the
printed way, and existence is stated apart.

**What is stated here.**
* `AssembledAsPrinted fa ea fm em K₀ post N`: the machine N is assembled as the paper says, from ANY
  machines that compute the named functions: Ma computes fa with the exponent ea (in the chain: the
  function of Steps 1 to 5 of Appendix D on the solver S); Mb computes exhaustive counting; M₂
  chooses between Ma (behind a front end that rewrites the code at k = the largest number of
  literals in a clause, or 3) and Mb by the printed test
  with K₀; M₁ computes fm with the exponent em (in the chain: the function for the bound in m on the
  SAME solver); N runs M₁ and M₂ in alternation behind a front end that renames the variables that
  occur. Nothing else is known of these machines.
* Theorem D (a) for every machine that computes the named function, and that there is one, is
  `RecursionToBound.ThmVariablesAForEveryMachine`.
* `BoundInMForEveryMachine`: the first sentence of Theorem A (c) at ρ = 1/√2, for the formulas in
  which every variable occurs, in the same form.
* `BuiltAsPrinted`: the same for a machine that is exhibited, with finite alphabets, polynomial-time
  front ends, and the named computations `TwoMachines.choose` and `TwoMachines.alt` carried out.
**What differs from the text.** In (5) the bound in m is `MinOfBounds.MeetsBoundInM`: the first
sentence of Theorem A (c) at α′ = 1/2 ONLY for formulas on x₀ … xₙ₋₁ in which every variable occurs,
on the code that has n in unary,
which is all that the proof of Corollary 11 uses after the renaming; the sentence as printed (any
names, counted over the variables that occur) is not stated here.
Further differences: cost is the length of a padding string in (2), (3) and (5); alternation and
choice cost a power. In (3) the function is `RecursionToBound.count`, which follows Step 5 as
printed
(ε a fraction between e and 2e, each output's own Δ, k the largest number of literals in a clause or
3, exhaustive counting below a bound n₁), with the differences that
proof/variables/RecursionToBound/Defs.lean lists.
The bound n₁ from which on n is “large” is a parameter of the chain. The ties fix what a machine
puts out and a bound on its steps, not the steps themselves. -/

@[expose] public section

namespace MainRoute

open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound
open Sat3 (CNF)

/-! ### The two named functions -/

section
variable (c : ℕ) (P₀ : PiecesF) (val : AppRunningTime.ValQ → ℤ) (n₁ : ℕ)

/-- The function of Steps 1 to 5 of Appendix D (`RecursionToBound.count`) on the recursion of
Appendix A on the pieces (P₀, val) with the constant c, with the level picked by
`RecursionWithPieces.pickAB` for ⌊n^(1/17)⌋, the fraction `PairsToBound.fractionHalf` as the number
in [e_ℓ, 2e_ℓ], and exhaustive counting below n₁ and wherever the exponent computed exceeds n. That
it returns the number of satisfying assignments is claimed only in the range of Theorem D (a)
(`RecursionToBound.CountIsRight`). -/
def fnN : List Bool × U → List Bool := RecursionToBound.count (RecursionWithPieces.solverAB P₀ val c) n₁ (RecursionWithPieces.pickAB P₀ val c) fractionHalf

/-- The exponent of its padding string. -/
def padExpN : List Bool → ℕ := RecursionToBound.expo (RecursionWithPieces.solverAB P₀ val c) n₁ (RecursionWithPieces.pickAB P₀ val c) fractionHalf

/-- The function for the bound in m (`ClauseBound.Alg.AM`) on the same recursion, with the level
picked by the same program `RecursionWithPieces.pickAB`, here for ⌊m^(1/9)⌋. It tries all
assignments where it has no exponent at most n; the text does so for m < K₀^9. -/
def fnM : List Bool × U → List Bool := AM (RecursionWithPieces.solverAB P₀ val c) (RecursionWithPieces.pickAB P₀ val c)

/-- The exponent of its padding string. -/
def padExpM : List Bool → ℕ := eM (RecursionWithPieces.solverAB P₀ val c) (RecursionWithPieces.pickAB P₀ val c)

end

/-! ### Item (5) for every machine that computes the named function -/

/-- The first sentence of Theorem A (c), for every machine that computes the named function. For all
pieces with parameters (1/√2, c): (i) there are a machine with finite alphabets and a q such that
the machine computes `AM` (the network of the formula, rebalanced and handed to the solver) on the
solver `RecursionWithPieces.solverAB P₀ val c` with the exponent `eM`; (ii) EVERY machine
that computes this function with this exponent meets the bound in m (`MinOfBounds.MeetsBoundInM`)
with some constant. -/
def BoundInMForEveryMachine : Prop :=
  ∀ (c : ℕ) (P₀ : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ), AppRunningTime.IsPieces (1 / Real.sqrt 2) c P₀ A val →
    (∃ (M : TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ Computes M (fnM c P₀ val) (padExpM c P₀ val) q) ∧
    ∀ (M : TM2ComputableAux Bool Bool) (q : ℕ), Computes M (fnM c P₀ val) (padExpM c P₀ val) q → ∃ C : ℕ, MeetsBoundInM M C

/-! ### The machine of the Main Theorem -/

/-- The machine M₂ is made as Step 6 says from the function fa with the exponent ea and the number
K₀: there are machines Ma and Mb, a front end `pre` and a test such that Ma computes fa with ea, Mb
computes exhaustive counting, `pre` rewrites the code at k = the largest number of literals in a
clause, or 3, `test` is the printed test with K₀, and M₂ chooses by `test` between Ma behind
`pre` and Mb on the input as it is. -/
def ChosenAsPrinted (fa : List Bool × U → List Bool) (ea : List Bool → ℕ) (K₀ : ℕ) (M₂ : TM2ComputableAux Bool Bool) : Prop :=
  ∃ (Ma Mb : TM2ComputableAux Bool Bool) (qa qb q₂ : ℕ) (pre : List Bool → List Bool) (test : List Bool → Bool),
    Computes Ma fa ea qa ∧ Computes Mb exhaust (fun x => (fmlOf x).1.length) qb ∧
    RewritesAtWidthOr3 pre ∧ TestsTheMainRegime K₀ test ∧ Chooses Ma Mb test pre id id id M₂ q₂

/-- The machine N is assembled as the proof of Corollary 11 says: there are a machine M₂ made as
Step 6 says, a machine M₁ that computes fm with the exponent em, and a front end `ren` that renames
the variables that occur, such that N runs M₁ and M₂ in alternation behind `ren`, with `post` after
either. -/
def AssembledAsPrinted (fa : List Bool × U → List Bool) (ea : List Bool → ℕ) (fm : List Bool × U → List Bool) (em : List Bool → ℕ) (K₀ : ℕ) (post : List Bool → List Bool) (N : TM2ComputableAux Bool Bool) : Prop :=
  ∃ (M₁ M₂ : TM2ComputableAux Bool Bool) (q₁ q : ℕ) (ren : List Bool → List Bool),
    ChosenAsPrinted fa ea K₀ M₂ ∧ Computes M₁ fm em q₁ ∧ RenamesTheVariablesThatOccur ren ∧ Alternates M₁ M₂ ren ren post post N q

/-- The same with everything that “assembled” should mean for a machine that is exhibited: all five
machines have finite alphabets; the three front ends and the test are polynomial-time; M₂ carries
out the named computation `TwoMachines.choose` on codings of Ma and Mb, and N the named computation
`TwoMachines.alt` («one operation of each at a time») on codings of M₁ and M₂. -/
def BuiltAsPrinted (fa : List Bool × U → List Bool) (ea : List Bool → ℕ) (fm : List Bool × U → List Bool) (em : List Bool → ℕ) (K₀ : ℕ) (post : List Bool → List Bool) (N : TM2ComputableAux Bool Bool) : Prop :=
  ∃ (Ma Mb M₂ M₁ : TM2ComputableAux Bool Bool) (qa qb q₂ q₂' q₁ q q' : ℕ) (pre ren : List Bool → List Bool) (test : List Bool → Bool) (Ka : Coding Ma) (Kb : Coding Mb) (K₁ : Coding M₁) (K₂ : Coding M₂),
    (∀ i, Finite (Ma.tm.Γ i)) ∧ (∀ i, Finite (Mb.tm.Γ i)) ∧ (∀ i, Finite (M₂.tm.Γ i)) ∧ (∀ i, Finite (M₁.tm.Γ i)) ∧ (∀ i, Finite (N.tm.Γ i)) ∧
    PolyT pre ∧ PolyT test ∧ PolyT ren ∧
    Computes Ma fa ea qa ∧ Computes Mb exhaust (fun x => (fmlOf x).1.length) qb ∧
    RewritesAtWidthOr3 pre ∧ TestsTheMainRegime K₀ test ∧ Hosts (choose Ka Kb test pre id id id) M₂ q₂' ∧ Chooses Ma Mb test pre id id id M₂ q₂ ∧
    Computes M₁ fm em q₁ ∧ RenamesTheVariablesThatOccur ren ∧ Hosts (alt K₁ K₂ ren ren post post) N q' ∧ Alternates M₁ M₂ ren ren post post N q

end MainRoute
