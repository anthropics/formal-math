/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import EightSquareStatement
import GeneralPieces.Main
import MinOfBounds.Arith
import MinOfBounds.Main
import MinOfBounds.Rename
import SparsificationLemma.Main
import CountedToPadded.GenLevels
import CountedToPadded.Levels
import CountedToPadded.Main
import CountedToPadded.Need
import CountedToPadded.Pick
import CountedToPadded.RunFor
import CountedToPadded.SolverPoly
import CountedToPadded.Tables
import CountedToPadded.TablesValue
import Coding.Grid
import Coding.Occ
import Coding.OccMore
import Coding.OccTests
import Coding.Padding
import Coding.SetForm
import Coding.Sets
import Complement.FromGamma
import Complement.Main
import Complement.Readers
import Complement.Sets
import QueryMachines.Comb
import QueryMachines.CombRuns
import QueryMachines.Poly
import QueryMachines.Runs
import CountedRoute.Main
import VariableBound.Field.Main
import VariableBound.StepParity
import RecursionToBound.Cert.Top
import RecursionToBound.Exponent
import RecursionToBound.Guard
import RecursionToBound.Main
import RecursionToBound.Numbers
import RecursionToBound.OneOutput
import RecursionToBound.Tree
import PairsToBound.Arith
import PairsToBound.Exhaust
import PairsToBound.FrontEnd
import PairsToBound.Main
import PairsToBound.Pairs
import PairsToBound.Width
import Eight.SecNetworks_Defs
import Eight.SecCrossing_Identity
import Eight.SecCrossing_LemPieces
import Enumerate.Enumeration
import Enumerate.Named
import Exits.Count
import Exits.Decides
import Exits.End
import Exits.Grouping
import Exits.Level
import Exits.Poly
import Exits.Runs
import ExplicitCost.Cost
import ExplicitCost.GroupingCall
import ExplicitCost.GroupingLemma
import ExplicitCost.GroupingNumbers
import ExplicitCost.GroupingPoly
import ExplicitCost.GroupingSearch
import ExplicitCost.Poly
import ExplicitCost.SameRuns
import FixedWidthSteps.Choice
import FixedWidthSteps.Hypothesis
import FixedWidthSteps.Main
import FixedWidthSteps.Numbers
import FixedWidthSteps.Sentence
import FixedWidthSteps.Small
import FreeCode.Behind
import FreeCode.Brute
import FreeCode.Code
import FreeCode.Main
import FreeCode.Order
import FreeCode.Random
import FreeCode.ReaderCert
import FromPrinted.Circuits
import FromPrinted.Core
import FromPrinted.Count
import FromPrinted.Dom
import FromPrinted.FreeCode
import FromPrinted.Sat3Graph
import FromPrinted.Sets
import FromPrinted.SplitSat
import FromPrinted.Verifier
import Given.End
import Given.Level
import Given.Networks
import CountedInstance.Main
import NamesInOrder.Arith
import NamesInOrder.Chain
import NamesInOrder.General
import NamesInOrder.Main
import Occ.Main
import PiecesCounted.Assume
import PiecesCounted.Basic
import PiecesCounted.EightSquare
import PiecesCounted.Half
import PiecesCounted.Oracle
import PiecesCounted.Padded
import Printed.Achievable
import Printed.Coding
import Printed.End
import Printed.GroupingEntry
import Printed.GroupingPoly
import Printed.GroupingProcs
import Printed.GroupingRun
import Printed.LevelFrom
import Printed.LevelNetworks
import PrintedOrder.AddUp
import PrintedOrder.Close
import PrintedOrder.Counting
import PrintedOrder.Deciding
import CountedRecursion.Main
import Sat3Graph.Ask
import Sat3Graph.Cert
import Sat3Graph.Coloring
import Sat3Graph.Dominating
import Sat3Graph.Main
import Sat3Graph.Sets
import SizeCircuit.Gamma
import SizeCircuit.General
import SizeCircuit.Main
import SizeCircuit.Sized
import SizeCircuit.SizedCert
import SplitCount.Cert
import SplitCount.Disjoint
import SplitCount.StepOne
import SplitCount.Suffices
import SplitCount.Tree
import SplitCount.Width
import SplitSat.Cert
import SplitSat.Leaf
import SplitSat.Main
import SplitSat.Reader
import SplitSat.Walk
import Suffices.Loop
import Suffices.Main
import Suffices.Total
import ThmVariables.Bound
import ThmVariables.EveryMachine
import ThmVariables.Main
import ThmVariables.PartA
import ThmCount.FrontEnd
import ThmCount.MEps
import ThmCount.Main
import ThmCount.Rates
import ThmCount.Remark
import Tower.Cost
import Tower.Poly
import Tower.PolyTower
import Tower.Runs
import Tower.TowerRuns
import Tower.Toy.Machines
import Tower.Toy.Meets
import Value.Blocks
import Value.Clique
import Value.End
import Value.Joint
import Value.Sums
import Variance.Cov
import Variance.Grouping
import Variance.Var
import GivenStatement
import KSatFreeCodeStatement
import Solution
import OccurM.AllOccur
import OccurM.Arith
import OccurM.Main
import OccurM.Prep
import OccurM.Top
import OccurM.Wrapper
import Paper.SecNetworks_DefFactor
import PaperSentencesStatement
import PiecesCountedStatement
import PrintedStatement
import KSatStatement
import Batteries.Tactic.Alias

/-!
# The numbered statements of the paper, in its order, each with its counterpart in Lean

Every entry is an `alias`: a declaration in the namespace `PaperIndex` whose type is that of the
original and whose body is the original,
so Lean itself checks that each counterpart exists. To read a statement, follow the name on the
right-hand side to its source.
Below the counterpart of a statement stand, where there are any, further forms of it and the named
steps of its proof.
The numbers in the comments are those that the paper in this folder prints; no name in this file
carries one.
The words in parentheses recall, in short, what the PAPER states there. They do not describe the
Lean statement, which may be worded differently
(machines and their steps in place of algorithms and operations, for one): for that, read the
original declaration.
`scripts/PrintAxiomsIndex.lean` prints the axioms on which each entry rests.

Where a statement is marked as proved differently from the paper, the differences on the route of
the Main Theorem are these. (1) Running two algorithms in alternation costs a constant power, with
the length of the input added, where the paper has a constant factor. (2) Before Theorems D (a) and
A (c) are applied, each algorithm counted in operations is turned into one that is given the tables
written out, not by queries, together with a string of blank symbols as its budget of time, and that
must answer correctly once that string has about 2^{e′_ℓ K²λ}·(K(λ+B))^{O(K²)} symbols; the paper
has no such step. (3) The pieces of Appendix B meet the time clause of Definition 7 by writing
2^{cλ} symbols and then working in one step, which Lean's bound on memory for Definition 7,
exponential in λ, allows; so for operations on words the printed c follows only with a larger
constant. (4) The proof of Theorem A (b) uses Lemma 8 only up to the call of the given algorithm and
runs its induction over the depth of the recursion with bounds fixed from the top. (5) After the
step of (2), Theorem D (a) is applied at a number e′_ℓ in [e_ℓ, 2e_ℓ], with 2C₀ + 1 in place of the
constant C₀. In Lean's model of cost, an operation is a table query or a step that may be any
polynomial-time function of the whole state, and Lean adds a bound on the size of the states:
polynomial in Definition 4, the bound (57) itself in the hypothesis of Theorem D (a), and
exponential in λ in Definition 7.

The paper states Theorem 2, Lemma 4 and Algorithm 1 for counting the satisfying assignments of a
3-CNF. The Lean files of proof/threesat and parts of proof/consequences, proof/machines,
proof/networks/Coding and proof/networks/Eight carry out the same proof for deciding satisfiability:
procedure Count counts, as in the paper, but lines 1 to 4 of Algorithm 1 answer «satisfiable» if the
count is positive for some formula of the list (in `Exits`, `Printed` and `Given` at the first such
formula), where the paper adds the counts up; these files call this deciding form procedure Sat,
where the paper has #Sat. What these files state of Lemma 4, and pass on to the rest of the proof,
is only that the formula is satisfiable if and only if at least one formula of the list is
(`Enumerate` derives it from the stronger fact that every satisfying assignment satisfies exactly
one formula of the list); the two properties that the printed form adds are proved in Lean,
separately, for the list of Lean's own branching procedure (see the entry under Lemma 4). So the
sentences between «…» in the comments on Section 6, Lemma 4, lines 1 to 4 of Algorithm 1 and the
proof of Corollary 5 are worded for deciding; those in the comments on the proof of Corollary 6
follow the Lean proof described under it, which runs Count on every formula of the sparsification;
and not all of them are to be found word for word in the paper. The statement files
`ThmEveryDeltaStatement.lean` and `PaperSentencesStatement.lean` also state Theorem 2 in this
deciding form, and the latter quotes it so. The six theorems under Theorem 2 state its decision
form, which the printed statement implies; the printed, counting statement is in Lean the case k = 3
of the first half of the entry under Corollary 6 (`FromPrinted.SplitCount.countingCorollary`), which
has a proof of its own.
-/

/-! ## Theorem 1, Section 1 -/

/-- **Theorem 1** (Main Theorem: one deterministic algorithm counts the satisfying assignments of a
k-CNF on n variables, each of which occurs, with m clauses, in time 2^{O(min{k²·n·log log n/√(log
n), k·m/√(log m)})}). In Lean: time is counted in steps of one of Mathlib's multi-stack Turing
machines with finite alphabets, not in word-RAM operations, on the input 1ᵏ0 1ⁿ0 followed by k slots
of ⌊log(2n)⌋+1 bits per clause; one machine and one C serve all k ≥ 1, m ≥ 2 and n ≥ 4, and nothing
is said about formulas with fewer than two clauses or fewer than four variables (Theorem 1 states no
ranges and leaves them to its O(·); Corollary 11 has these ranges); the variables are x₀,…,x_{n−1},
each of which occurs, and nothing is added to the bound. The statement is the printed one up to this
coding, these ranges and this machine model (the passage from Turing-machine steps to time on a word
RAM is not made in Lean), but the proof is not the printed one step for step (see the head of this
index). -/
alias PaperIndex.mainTheorem := MainResults.mainTheorem

/-- Theorem 1: a further proof of the Main Theorem, for the variables x₀ … x_(n−1), each of which
occurs. In Lean: time is counted in steps of Mathlib's multi-stack Turing machine with finite
alphabets, for one machine and one constant C chosen before k and the formula on x₀,…,x_{n−1}, each
of which occurs, with k ≥ 1, m ≥ 2 and n ≥ 4 (ranges that Theorem 1 does not state); the statement
only says that some machine has the bound, and its proof is not the printed one but goes through
machines made as the proofs for the pieces of Appendix B describe. -/
alias PaperIndex.mainTheoremInNamesInOrder := NamesInOrder.mainTheoremHolds

/-- Theorem 1: the same statement over the statement files with narrow imports. In Lean: time is
counted in steps of one deterministic multi-stack Turing machine of Mathlib with finite alphabets,
not in word-RAM operations; this machine and one constant C serve every k ≥ 1, m ≥ 2 and n ≥ 4, and
nothing is said outside these ranges, which Theorem 1 does not state. The variables are
x₀,…,x_{n−1}, all occurring; the input writes k and n in unary and each clause in k slots of
⌊log(2n)⌋+1 bits. The proof is not the printed one step for step (see the head of this index). -/
alias PaperIndex.mainTheoremOverNarrowImports := CountedRoute.mainTheoremHolds

/-- A step of the proof of Theorem 1: as Appendix E says of «every polynomial in the length of the
input»: for every c there is a c′ with c·L^c ≤ 2^{c′·min{km/√(log m), k²n log log n/√(log n)}} for
the length L of the input (which writes n in unary), when k≥1, m≥2, n≥4 and every variable occurs. -/
alias PaperIndex.mainTheorem.NamesInOrder.polynomialIsBelowTheBound := NamesInOrder.polynomialIsBelowTheBound

/-- A step of the proof of Theorem 1: for all pieces of Appendix B and every large enough cut-off
below which all assignments are tried: machines for the algorithm of Theorem A (c) on the recursion
of Appendix A meet the bound in m; machines combining these with machines for Steps 1–5 of Appendix
D on it and with exhaustive counting meet Corollary 11; one exists. -/
alias PaperIndex.mainTheorem.NamesInOrder.forAllPieces := NamesInOrder.forAllPieces

/-- A step of the proof of Theorem 1: «n≤km», as in the proof of Theorem A (c) and in Appendix E: if
each of the n variables occurs in a k-CNF with m clauses, then n ≤ km. -/
alias PaperIndex.mainTheorem.NamesInOrder.variablesAreFew := NamesInOrder.variablesAreFew

/-- A step of the proof of Theorem 1: not in the paper: the input 1ᵏ0 1ⁿ0 followed by the clauses
has k + n + 2 + mk(⌊log(2n)⌋+1) bits, at most 6(km)² if every variable occurs and at most
k(2n+1)^{k+3} as no clause repeats. -/
alias PaperIndex.mainTheorem.NamesInOrder.codeIsShort := NamesInOrder.codeIsShort

/-- A step of the proof of Theorem 1: not in the paper: for every c there is a c′ with c·(6(km)²)^c
≤ 2^{c′km/√(log m)}, rounded down, for all k ≥ 1 and m ≥ 2. -/
alias PaperIndex.mainTheorem.NamesInOrder.polynomialIsBelowTheBoundInM := NamesInOrder.polynomialIsBelowTheBoundInM

/-- A step of the proof of Theorem 1: not in the paper: for every c there is a c′ with
c·(k(2n+1)^{k+3})^c ≤ 2^{c′k²n log log n/√(log n)}, rounded down, for all k ≥ 1 and n ≥ 4. -/
alias PaperIndex.mainTheorem.NamesInOrder.polynomialIsBelowTheBoundInN := NamesInOrder.polynomialIsBelowTheBoundInN

/-- A step of the proof of Theorem 1: not in the paper: a machine built as Step 6 of Appendix D and
Corollary 11 say (the test of that step picks Steps 1–5 or trying all assignments, run in
alternation, step by step, with a machine for the bound in m on the input as it is; rewriting and
test in polynomial time) alternates two counting machines and has finite alphabets. -/
alias PaperIndex.mainTheorem.NamesInOrder.builtIsAssembledDirectly := NamesInOrder.builtIsAssembledDirectly

/-- A step of the proof of Theorem 1: if an algorithm for cliques with query access meets the
hypothesis of Theorem D (a) in polynomial-time steps, with states bounded by (57) and e_ℓ ≤ a/√(log
K_ℓ), then, for every large enough cut-off below which all assignments are tried, every machine made
as Step 6 of Appendix D says has the bound of Theorem D (b), every machine for the bound in m of
Theorem A (c) meets it, every machine built from these as Corollary 11 says has the bound of
Corollary 11 and of Theorem 1, and such a machine exists. -/
alias PaperIndex.mainTheorem.CountedRoute.onEveryMachineWithQueryAccess := CountedRoute.onEveryMachineWithQueryAccess

/-- A step of the proof of Theorem 1: from the bounds that the algorithm of Theorem A (b) gives with
operations counted: Theorem 1 and Corollary 11 when every variable occurs, the conclusion of Theorem
D (b), and the first sentence of Theorem A (c) at α′ = ½; all four are proved in Lean, so the
implication alone shows little. -/
alias PaperIndex.mainTheorem.CountedRoute.closedStatementsFrom := CountedRoute.closedStatementsFrom

/-- A step of the proof of Theorem 1: not in the paper: the chain for algorithms with query access
follows from four Lean theorems: such an algorithm, counted in operations, gives one that is a
polynomial-time function of the tables written out and a string of units, for the computed number in
[e_ℓ, 2e_ℓ] cut at 1 in place of e_ℓ; facts on that number; and two that give, for every algorithm
of that kind, the bound in m of Theorem A (c), the bound of Theorem D (b) and that of Corollary 11;
as all four are proved, the implication alone shows little. -/
alias PaperIndex.mainTheorem.CountedRoute.onEveryMachineWithQueryAccessFrom := CountedRoute.onEveryMachineWithQueryAccessFrom

/-! ## Theorem 2, Section 2 -/

/-- **Theorem 2** (for every δ > 0 a deterministic algorithm counts the satisfying assignments of a
3-CNF on n variables, with any number of clauses, in time O(2^{δn}); the statement here is its
decision form). In Lean: this is the decision form: the paper's Theorem 2 counts the satisfying
assignments, and this statement says only that for every δ > 0 a machine decides satisfiability
within c·2^{δn} steps, which is weaker: it follows from the printed theorem, and Lean does not
derive the printed theorem from it. No Lean statement states the printed, counting sentence on its
own; it is the case k = 3 of the first half of Corollary 6 (see there), whose Lean proof differs
from the printed proof of Section 6 (it does not take K from e* = 0, and it sparsifies with Lean's
own procedure). The algorithm is a deterministic multi-stack Turing machine of Mathlib with finite
alphabets, time counted in its steps; its input is n in unary, then three slots of ⌊log₂(2n)⌋+1 bits
per clause, on the variables x₀,…,x_{n−1}; clauses are lists of literals, possibly empty or with a
literal repeated (the paper has nonempty sets), none written twice. The proof, not the statement,
reads Definition 2 (iii) as one condition (procedures of polynomial-time steps answer every question
within τ operations) and goes through e* = 0 (Proposition 3). -/
alias PaperIndex.threeSat := Given.threeSat_through_eStar

/-- Theorem 2: the same statement, proved through the algorithm in pseudocode. In Lean: this is the
decision form: the machine decides satisfiability, where the paper's Theorem 2, and procedure #Sat
of Algorithm 1, count the satisfying assignments (for the counting form see Corollary 6 at k = 3).
The algorithm is a multi-stack Turing machine of Mathlib; a formula is a list of clauses, each a
list of literals that may be empty or repeat a literal, where the paper has nonempty sets. The
statement does not show the proof: the machine simulates a deciding form of lines 1 to 4 of
Algorithm 1 (it stops at the first formula of the list with a positive count), here proved with
Definition 2 (iii) read as one condition: the network is given by procedures whose steps take
polynomial time and which answer every question within τ operations. -/
alias PaperIndex.threeSatByAlgorithm := Given.threeSat_by_algorithm

/-- Theorem 2: a further proof of the same statement, by the proof of Section 6. In Lean: steps of a
multi-stack Turing machine of Mathlib are counted, and a 3-CNF is a list of lists of at most 3
literals, which may be empty or repeat a literal, not a set of nonempty sets. Its proof passes
through Definition 4 with a polynomial bound on memory added and an operation read as a table query
or a polynomial-time step on the whole state. -/
alias PaperIndex.threeSatInPrinted := Printed.threeSat_through_eStar

/-- Theorem 2: a further proof of the same statement, through the algorithm in pseudocode, on
machines with counted queries. In Lean: a deterministic multi-stack Turing machine of Mathlib, with
time counted in its steps; a formula is a list of clauses, each a list of literals that may be empty
or repeat a literal, where the paper has nonempty sets. The proof has the machine simulate procedure
Sat of Algorithm 1, built on algorithms for cliques with query access, a table query at one
operation; the statement does not show this. -/
alias PaperIndex.threeSatInPrintedByAlgorithm := Printed.threeSat_by_algorithm

/-- Theorem 2: a further proof of the same statement, by the proof of Section 6. In Lean: a
deterministic multi-stack Turing machine of Mathlib, with time counted in its steps; a formula is a
list of clauses, each a list of literals that may be empty or repeat a literal, where the paper has
nonempty sets. The proof goes through e* = 0 for a form of Definition 4 in which each step takes
polynomial time, a table query costs t steps and the bound is multiplied by t, which the statement
does not show. -/
alias PaperIndex.threeSatInExits := Exits.threeSat_through_eStar

/-- Theorem 2: a further proof of the same statement, through the algorithm in pseudocode, on step
machines with a loop that can be left early. In Lean: a deterministic multi-stack Turing machine of
Mathlib, time counted in its steps; a formula is a list of clauses, each a list of literals that may
be empty or repeat one, where the paper has nonempty sets. The proof (not in the statement) has the
machine simulate procedure Sat of Algorithm 1, on algorithms for cliques whose steps take polynomial
time and whose table queries cost t steps each, with the searches of lines 3 and 10 stopped at the
first success. -/
alias PaperIndex.threeSatInExitsByAlgorithm := Exits.threeSat_by_algorithm

/-- A step of the proof of Theorem 2: a loop over a finite list of points that may stop early halts
within Σ (t(x)+1) steps over the points it meets and returns the fold over them; its body need only
halt on these points. -/
alias PaperIndex.threeSat.Exits.stFoldUntil := Exits.stFoldUntil

/-- A step of the proof of Theorem 2: a search over y = 0,…,N−1 that stops at the first good y, as
in line 10 of Algorithm 1: it returns that y within Σ (t(y)+1) steps, summed over the y up to it. -/
alias PaperIndex.threeSat.Exits.stFirstUntil := Exits.stFirstUntil

/-- A step of the proof of Theorem 2: a walk over the leaves of a tree of depth at most k that stops
at the first leaf passing a test, as in lines 2 and 3 of Algorithm 1: at most t+2 steps per leaf
tested, and k more. -/
alias PaperIndex.threeSat.Exits.stWalkUntil := Exits.stWalkUntil

/-- A step of the proof of Theorem 2: the loop that may stop early has polynomial-time steps if its
body has and its other ingredients are computed in polynomial time. -/
alias PaperIndex.threeSat.Exits.stFoldUntilPoly := Exits.stFoldUntilPoly

/-- A step of the proof of Theorem 2: from the bound for a loop that may stop early: the bound for
the search that stops at the first good y (line 10 of Algorithm 1). -/
alias PaperIndex.threeSat.Exits.stFirstUntilOf := Exits.stFirstUntilOf

/-- A step of the proof of Theorem 2: from the bound for a loop that may stop early: the bound for
the walk that stops at the first leaf passing a test (lines 2 and 3 of Algorithm 1). -/
alias PaperIndex.threeSat.Exits.stWalkUntilOf := Exits.stWalkUntilOf

/-- A step of the proof of Theorem 2: the reduction by Lemma 4 in its form for deciding, in Section
6, for Theorem 2 in its decision form (a test for 3-CNFs with m ≤ Mn clauses, in time O(2^{δ'm})
plus a polynomial in n, suffices) implies the form the rest of the Lean proof uses: a test for every
number of clauses within O(2^{δ'm}) steps suffices. -/
alias PaperIndex.threeSat.Suffices.stPrintedGivesSparse := Suffices.stPrintedGivesSparse

/-- A step of the proof of Theorem 2: lines 1–4 of Algorithm 1: if Count halts within t steps on
each formula tested, up to the first with a positive count, the loop answers within (number
tested)·(t+2)+τ⁶n+2 steps; τ is a parameter of the Lean sparsification procedure, not the τ of
Definition 2. -/
alias PaperIndex.threeSat.Suffices.stLoopRuns := Suffices.stLoopRuns

/-- A step of the proof of Theorem 2: «Lemma 4 yields at most 2^{δn/3} such formulas, in time
2^{δn/3} times a polynomial in n, so the total time is O(2^{δn})»: at most 2^{δn/3} formulas of at
most A·2^x + A(n+1)^A + 3 steps each, x ≤ δn/3, plus D·n + 2 steps, take at most c·2^{δn} steps, c
depending only on δ, A, D. -/
alias PaperIndex.threeSat.Suffices.stTotal := Suffices.stTotal

/-- A step of the proof of Theorem 2: the reduction «By Lemma 4 with ε=δ/3, it suffices …» of
Section 6, by lines 1–4 of Algorithm 1, at every parameter τ at which the depth-first walk through
the tree of the Lean sparsification procedure gives a list as Lemma 4 says, with its constant M. -/
alias PaperIndex.threeSat.Suffices.stSuffices := Suffices.stSuffices

/-- A step of the proof of Theorem 2: from the bound for the walk that stops at the first leaf
passing a test: the run of lines 1–4 of Algorithm 1. -/
alias PaperIndex.threeSat.Suffices.stLoopRunsOf := Suffices.stLoopRunsOf

/-- A step of the proof of Theorem 2: from the run of lines 1–4 of Algorithm 1, the count of the
total time and the polynomial-time steps of the loop: the reduction by Lemma 4 in Section 6. -/
alias PaperIndex.threeSat.Suffices.stSufficesOf := Suffices.stSufficesOf

/-- A step of the proof of Theorem 2: «By brute force and Proposition 3, (K_ℓ,e_ℓ) is achievable for
every ℓ», for procedure Clique of Algorithm 1. -/
alias PaperIndex.threeSat.Exits.stClique := Exits.stClique

/-- A step of the proof of Theorem 2: from Proposition 3 for the algorithm of its proof: «By brute
force and Proposition 3, (K_ℓ,e_ℓ) is achievable for every ℓ», for procedure Clique of Algorithm 1. -/
alias PaperIndex.threeSat.Exits.stCliqueOf := Exits.stCliqueOf

/-- A step of the proof of Theorem 2: line 6 of Algorithm 1, «if m=0 then return 1»: on the formula
without clauses, Count returns 1 in one step, at every level. -/
alias PaperIndex.threeSat.Exits.stCountNil := Exits.stCountNil

/-- A step of the proof of Theorem 2: «Cost» of Section 6 for Count of Algorithm 1: for 0<δ'≤1, at
each level ℓ with K_ℓ≥72/δ' and e_ℓ≤δ'/12, Count has polynomial-time steps and counts the satisfying
assignments of the variables that occur in m clauses of ≤3 literals within A·2^{δ'm} steps; here
Count is built on clique algorithms with polynomial-time steps and table queries of t steps each,
and the search of line 10 stops at the first good grouping. -/
alias PaperIndex.threeSat.Exits.stCountCost := Exits.stCountCost

/-- A step of the proof of Theorem 2: from Lemma 1 for the algorithm of its proof, the
polynomial-time steps of that algorithm and the bound for Clique: «Cost» of Section 6 for Count of
Algorithm 1. -/
alias PaperIndex.threeSat.Exits.stCountCostOf := Exits.stCountCostOf

/-- A step of the proof of Theorem 2: for 0<δ≤1: if the list of the sparsification procedure at
parameter τ (from which its thresholds are computed; not the τ of Definition 2) satisfies Lemma 4
for ε=δ/3, then Algorithm 1 with the constants of its header decides 3-SAT on n variables within
c·2^{δn} steps, each computed in polynomial time. -/
alias PaperIndex.threeSat.Exits.stAlgorithm := Exits.stAlgorithm

/-- A step of the proof of Theorem 2: from the reduction by Lemma 4 in its form for deciding and
«Cost» for Count: the deciding form of procedure #Sat of Algorithm 1, with the constants of its
header, decides 3-SAT within c·2^{δn} steps. -/
alias PaperIndex.threeSat.Exits.stAlgorithmOf := Exits.stAlgorithmOf

/-- A step of the proof of Theorem 2: Theorem 2 in its decision form for step machines, by the
deciding form of procedure #Sat of Algorithm 1: for every δ>0 some level ℓ and parameter τ make
Sat(ℓ, τ), with polynomial-time steps, decide 3-SAT on n variables within c·2^{δn} steps. -/
alias PaperIndex.threeSat.Exits.stDecides := Exits.stDecides

/-- A step of the proof of Theorem 2: from Algorithm 1 with the constants of its header and Lemma 4
as an enumeration: Theorem 2 in its decision form for machines counted in steps, by the deciding
form of procedure #Sat of Algorithm 1, as in the proof of Theorem 2 («We may assume δ≤1»). -/
alias PaperIndex.threeSat.Exits.stDecidesOf := Exits.stDecidesOf

/-- A step of the proof of Theorem 2: for 0<δ≤1, δ′=δ/(3M), M=M(δ/3) of Lemma 4: if K≥72/δ′ and a
clique algorithm of polynomial-time steps meets the bound of Definition 4 for (K, δ′/12) times query
cost t, with a memory bound, then lines 1–4 of Algorithm 1, counting each formula by the proof of
Lemma 1 over that algorithm on its network of 3K⁸ clusters, decide 3-SAT in c·2^{δn} steps. -/
alias PaperIndex.threeSat.Exits.stProofNamed := Exits.stProofNamed

/-- A step of the proof of Theorem 2: the proof in Section 6 for a given algorithm for cliques, from
the reduction by Lemma 4 as printed, Lemma 1 for the algorithm of its proof, and its polynomial-time
steps. -/
alias PaperIndex.threeSat.Exits.stProofNamedOf := Exits.stProofNamedOf

/-- A step of the proof of Theorem 2: from e*=0, Lemma 4 as an enumeration and the proof of Section
6 for any algorithm for cliques that meets Definition 4: Theorem 2, for a multi-stack Turing machine
of Mathlib. -/
alias PaperIndex.threeSat.Exits.stThroughEStarOf := Exits.stThroughEStarOf

/-- A step of the proof of Theorem 2: from Theorem 2 for Sat of Algorithm 1 at a level ℓ and
sparsification parameter τ, in steps of polynomial time each: for every δ>0 some multi-stack Turing
machine of Mathlib decides 3-SAT within c·2^{δn} steps (the proof simulates Sat; Theorem 2 is also
proved in Lean otherwise, so the implication alone shows little). -/
alias PaperIndex.threeSat.Exits.stByAlgorithmOf := Exits.stByAlgorithmOf

/-- A step of the proof of Theorem 2: if an algorithm for cliques with polynomial-time steps meets
Definition 4 for (K, δ'/12), δ'=δ/(3M), K≥72/δ', then lines 1–4 of Algorithm 1 over the algorithm of
Lemma 1 built on it decide 3-SAT within c·2^{δn} steps. -/
alias PaperIndex.threeSat.Printed.stProofNamed := Printed.stProofNamed

/-- A step of the proof of Theorem 2: for every level ℓ, procedure Clique of Algorithm 1 has
polynomial-time steps and meets Definition 4 for the pair (K_ℓ, e_ℓ) of (38); here Definition 4 is
read with a table query at one operation and a polynomial bound on memory. -/
alias PaperIndex.threeSat.Printed.stClique := Printed.stClique

/-- A step of the proof of Theorem 2: Algorithm 1, run with the parameter τ of Lemma 4 and the
constants of its header, decides 3-SAT on n variables within c·2^{δn} steps, each step computed in
polynomial time. -/
alias PaperIndex.threeSat.Printed.stAlgorithm := Printed.stAlgorithm

/-- A step of the proof of Theorem 2: Theorem 2 in its decision form for machines counted in steps
that each take polynomial time, by the deciding form of procedure #Sat of Algorithm 1: for every δ>0
some level ℓ and some value of the parameter of the Lean proof's sparsification procedure make it
decide 3-SAT on n variables within c·2^{δn} steps. -/
alias PaperIndex.threeSat.Printed.stDecides := Printed.stDecides

/-- A step of the proof of Theorem 2: the statements of Section 3, Section 5, Section 6 and Section
8 in one, from five facts: a good grouping exists and the first is found, the search stops there,
«so the value equals Z», the reduction by Lemma 4, and Lemma 4 as an enumeration. -/
alias PaperIndex.threeSat.Printed.endStatements_of := Printed.endStatements_of

/-- A step of the proof of Theorem 2: fourteen statements: two sentences after Definition 4, «Answer
each of its … queries» from Lemma 1's proof, Lemma 1, Proposition 3 (three statements), (K_ℓ,e_ℓ)
achievable, Lemma 4 listing one formula at a time, Section 6's proof, Algorithm 1 and Theorem 2
three times; here from Definition 4 with a table query at one operation. -/
alias PaperIndex.threeSat.Printed.endStatements := Printed.endStatements

/-- A step of the proof of Theorem 2: procedure Clique of Algorithm 1, with polynomial-time steps, a
table query as one operation and a polynomial bound on memory, gives «By brute force and Proposition
3, (K_ℓ,e_ℓ) is achievable for every ℓ» (38); in the proof Definition 2 (iii) is met by procedures
with polynomial-time steps answering any question in τ operations. -/
alias PaperIndex.threeSat.Given.stClique := Given.stClique

/-- A step of the proof of Theorem 2: if 0<δ≤1, Lemma 4 at ε=δ/3 leaves ≤M·n clauses, δ′=δ/(3M),
K≥72/δ′ and a clique algorithm with poly-time steps meets Definition 4 for (K,δ′/12) and a memory
bound: lines 1–4 of Algorithm 1, counting Φ by Lemma 1 on it with 3K⁸ clusters, decide 3-SAT in
c·2^{δn} steps. -/
alias PaperIndex.threeSat.Given.stProofNamed := Given.stProofNamed

/-- A step of the proof of Theorem 2: Algorithm 1, run with the constant M of Lemma 4 for ε = δ/3
and a parameter s of the enumeration for that ε, decides 3-SAT on n variables within c·2^{δn} steps. -/
alias PaperIndex.threeSat.Given.stAlgorithm := Given.stAlgorithm

/-- A step of the proof of Theorem 2: for every δ>0 there are a level ℓ and a parameter τ of the
sparsification used for Lemma 4 (not the τ of Definition 2) such that the machine Sat(ℓ, τ), built
from Algorithm 1, has polynomial-time steps and decides 3-SAT on n variables within c·2^{δn} steps,
for a constant c. -/
alias PaperIndex.threeSat.Given.stDecides := Given.stDecides

/-- A step of the proof of Theorem 2: the same fourteen statements as the entry for Printed (two
sentences after Definition 4, «Answer each of its … queries» from the proof of Lemma 1, Lemma 1,
Proposition 3 three times, (K_ℓ,e_ℓ) achievable, Lemma 4 listing one formula at a time, the proof of
Section 6, Algorithm 1, Theorem 2 three times), from Definition 4 with a table query at one
operation and a polynomial bound on memory; the nine that rest on a network are here proved reading
Definition 2 (iii) as one condition: the network is given by procedures with polynomial-time steps
that answer every question within τ operations. -/
alias PaperIndex.threeSat.Given.endStatements := Given.endStatements

/-- A step of the proof of Theorem 2: from Theorem 2 for formulas written as lists, and the fact
that every 3-CNF can be written as a list and every list that writes it is covered: Theorem 2 for
3-CNFs as sets. -/
alias PaperIndex.threeSat.Coding.stSetFormOf := Coding.stSetFormOf

/-- A step of the proof of Theorem 2: Theorem 2 for 3-CNFs as finite sets of clauses, as in Section
6: for every δ>0 one multi-stack Turing machine of Mathlib decides them within c·2^{δn} steps,
however the set is written as a list. -/
alias PaperIndex.threeSat.Coding.stSetForm := Coding.stSetForm

/-- A step of the proof of Theorem 2: «Cost» of Section 6 for Count of Algorithm 1: for 0<δ'≤1, at
each level ℓ with K_ℓ≥72/δ', e_ℓ≤δ'/12, it counts the satisfying assignments of m clauses of ≤3
literals within A·2^{δ'm} steps; here from Definition 4 with a table query at one operation. -/
alias PaperIndex.threeSat.Printed.stCountCost := Printed.stCountCost

/-- A step of the proof of Theorem 2: «Cost» in Section 6 for Count of Algorithm 1: for 0<δ′≤1 and
each level ℓ with K_ℓ≥72/δ′, e_ℓ≤δ′/12, Count has polynomial-time steps and, on m clauses of ≤3
literals, returns the number of satisfying assignments of the variables that occur, within A·2^{δ′m}
steps. -/
alias PaperIndex.threeSat.Given.stCountCost := Given.stCountCost

/-- A step of the proof of Theorem 2: if a network arises from another by lengthening every setting
with extra bits, it has the same value and the same total U. -/
alias PaperIndex.threeSat.Coding.stPaddingValue := Coding.stPaddingValue

/-- A step of the proof of Theorem 2: Lean's network of Φ on g≥1 clusters, with one bit per place of
a clause of at most 3 literals, is the network of Φ of Section 6 with its settings lengthened by
extra bits. -/
alias PaperIndex.threeSat.Coding.stOccNet := Coding.stOccNet

/-- A step of the proof of Theorem 2: for the network of Φ of Section 6: «Their length is at most
3m̄ ≤ P», and all values of W_a, Ψ_{a,b} and f_{a,b} are 0 or 1. -/
alias PaperIndex.threeSat.Coding.stOccNetSmall := Coding.stOccNetSmall

/-- A step of the proof of Theorem 2: «Hence Z is the number of assignments of the variables
occurring in Φ that satisfy Φ, and Φ is satisfiable if and only if Z > 0», for the network of Φ of
Section 6 on g≥1 clusters. -/
alias PaperIndex.threeSat.Coding.stOccNetCounts := Coding.stOccNetCounts

/-- A step of the proof of Theorem 2: from two facts, that Lean's network of Φ is that of Section 6
with lengthened settings and that lengthening keeps the value: Z counts the satisfying assignments,
and Φ is satisfiable iff Z>0. -/
alias PaperIndex.threeSat.Coding.stOccNetCountsOf := Coding.stOccNetCountsOf

/-- A step of the proof of Theorem 2: «An occurrence lies in at most two tests», and the number of
tests is that of occurrences minus that of variables that occur, at most 3m−1 (m≥1 nonempty clauses
of ≤3 literals). -/
alias PaperIndex.threeSat.Coding.stTests := Coding.stTests

/-- A step of the proof of Theorem 2: the footnote of Section 6, «P is taken as large as 6m̄ because
Σ_{b≠a} c_{a,b} can reach 6m̄»: three clauses in three clusters, where the middle cluster reaches
6m̄. -/
alias PaperIndex.threeSat.Coding.stRowSumReached := Coding.stRowSumReached

/-- A step of the proof of Theorem 2: every 3-CNF as a set, as in Section 6, can be written as a
list of lists; every such list is a 3-CNF list with as many clauses, none empty, satisfiable exactly
if the set is. -/
alias PaperIndex.threeSat.Coding.stWrites := Coding.stWrites

/-- A step of the proof of Theorem 2: «a 3-CNF is a set of clauses (Section 6), so m=O(n³)» (Section 3):
a 3-CNF on n variables has at most 14n³ clauses. -/
alias PaperIndex.threeSat.Coding.stCubic := Coding.stCubic

/-! ## Definition 1, Section 3 -/

/-- **Definition 1** (a function of two arguments factors through c bits). In Lean: a string of c
bits is a function from {0,…,c−1} to the truth values, F takes its two arguments one after the
other, and the sets 𝒳 and 𝒳′ need not be finite. -/
alias PaperIndex.factorsThrough := Paper.FactorsThrough

/-! ## Definition 2, Section 3 -/

/-- **Definition 2** (a network on a set of nodes, with parameters P, B, τ). In Lean: an operation
is one step, which may be any function computed in polynomial time in the length of the state, or
one query to an oracle that the procedures may use; the procedures get an extra input of their own
and must keep their states of size at most S, a number that the paper does not have and that the
definition does not tie to P and B. P, B, the P_a and the c_{a,b} are handed over in unary, and the
nodes are 0,…,g−1. -/
alias PaperIndex.network := Given.IsGivenNetwork

/-- Beside Definition 2: in Section 6, «Definition 2 holds» for a variant of the network of Φ on g
clusters whose settings have one bit for each of the k literal positions of each clause: P = max{1,
2k·m̄} (6m̄ for k = 3 and m ≥ 1), B = 1 and τ = 1 (printed: τ polynomial in m), values given by
procedures that make no queries. -/
alias PaperIndex.network.Given.stFormulaGiven := Given.stFormulaGiven

/-- Beside Definition 2: the network of a 3-CNF Φ with m≥1 clauses on g clusters, as in Section 6,
satisfies Definition 2 except its condition (iii), with P=6m̄ and B=1. -/
alias PaperIndex.network.Coding.stOccNetIs := Coding.stOccNetIs

/-! ## Definition 3, Section 3 -/

/-- **Definition 3** (the (K, λ)-clique with tables W₁, …, W_K). In Lean: nodes are numbered from 0,
K and λ may be any natural numbers, and the setting z_w of a node is one list of (K−1)λ bits, its
K−1 strings of λ bits written one after another; the tables may be any integer-valued functions. The
bound |W_w| < 2^B and query access come in with Definition 4, where a query counts as one operation
and the other kind of operation is a machine step that may be any polynomial-time function of the
whole state. -/
alias PaperIndex.clique := Eight.SecNetworks.clique

/-- Definition 3: query access to the tables: a query names w and a setting of (K−1)λ bits, is
answered by exactly one entry, and costs one operation. In Lean: nodes are numbered 0, …, K−1 and a
setting is one list of bits; a query (w, z) is answered by W_w(z) only if w < K and z has (K−1)λ
bits, and gets no answer otherwise. -/
alias PaperIndex.tableQueries := Printed.tables

/-- Beside Definition 3: the value of the (K, λ)-clique is the sum of its terms over all choices of
one setting z_w ∈ ({0,1}^λ)^{K−1} for each node w. -/
alias PaperIndex.clique.Value.stSumOverSettings := Value.stSumOverSettings

/-- Beside Definition 3: a term in which the two copies z_w(w′) and z_{w′}(w) differ on some edge is
0, and a term in which they agree on every edge equals ∏_w W_w(z_w). -/
alias PaperIndex.clique.Value.stCopiesMustAgree := Value.stCopiesMustAgree

/-- Beside Definition 3: the choices of settings in which the two copies on every edge agree
correspond one to one to the choices of one string in {0,1}^λ per edge, by z_w(w′) = the string on
{w, w′}. -/
alias PaperIndex.clique.Value.stOneStringPerEdge := Value.stOneStringPerEdge

/-- Beside Definition 3: for all K and λ, «the value is the sum, over all choices of one string in
{0,1}^λ per edge, of ∏_{w∈[K]} W_w evaluated at the strings on the edges at w». -/
alias PaperIndex.clique.Value.stCliqueValue := Value.stCliqueValue

/-- Beside Definition 3: if the value is the sum over the settings, only terms whose copies agree
count, and these are the choices of one string per edge, then the value is the sum over one string
per edge of ∏_w W_w. -/
alias PaperIndex.clique.Value.stCliqueValueOf := Value.stCliqueValueOf

/-- Beside Definition 3: a setting z_w of (K−1)λ bits, cut into its K−1 strings z_w(w′) of λ bits
each (the empty string at w), gives z_w back when these strings are concatenated. -/
alias PaperIndex.clique.Printed.stToLists := Printed.stToLists

/-- Beside Definition 3: for K ≥ 2 and λ ≥ 1, the value of the (K, λ)-clique is the sum, over one
string in {0,1}^λ per edge, of the product of the K entries, each named by concatenating the strings
at its node. -/
alias PaperIndex.clique.Printed.stCliqueValue := Printed.stCliqueValue

/-- Beside Definition 3: a procedure with the tables built in, all entries below 2^B in absolute
value, answers every well-formed query in one step: it «receives W_w(z_w) at the cost of one
operation». -/
alias PaperIndex.clique.Printed.stAskServes := Printed.stAskServes

/-- Beside Definition 3: for K ≥ 2, λ ≥ 1 and tables written out as a list T, the value of the (K,
λ)-clique with these tables is the value that the written-out form (λ, T) stands for. -/
alias PaperIndex.clique.QueryMachines.Bridge.tablesValue := QueryMachines.Bridge.tablesValue

/-! ## Definition 4, Section 3 -/

/-- **Definition 4** (the pair (K, e) is achievable). In Lean: an operation is one machine step,
which may be any function computed in polynomial time in the length of the state, or one table
query; λ and B are handed over in unary; all states have size at most C·(B+λ)^C, which the paper
does not ask, so this implies the printed notion (by an argument outside Lean) but the converse is
not claimed. -/
alias PaperIndex.achievable := Printed.Achievable

/-- Beside Definition 4: a run within given bounds on its own steps and on the sizes of its states
stays within any larger bounds, with the same list of queries. -/
alias PaperIndex.achievable.QueryMachines.stMono := QueryMachines.stMono

/-- Beside Definition 4: the cost of a run, rule by rule: a halted state costs nothing, a step of
the machine's own costs 1, and the query x costs its price w(x). -/
alias PaperIndex.achievable.QueryMachines.stWithinRules := QueryMachines.stWithinRules

/-- Beside Definition 4: the result of a run and the list of queries it asks are determined by the
input and the answers to the queries. -/
alias PaperIndex.achievable.QueryMachines.stUnique := QueryMachines.stUnique

/-- Beside Definition 4: a query costs one operation: the cost of a run with queries equals the
number of steps of the same machine with the answers to its queries built in. -/
alias PaperIndex.achievable.QueryMachines.stClose := QueryMachines.stClose

/-- Beside Definition 4: an algorithm that takes at most T operations makes at most T queries; this
bounds the number of queries in the proof of Lemma 1. -/
alias PaperIndex.achievable.QueryMachines.stQueriesLe := QueryMachines.stQueriesLe

/-- Beside Definition 4: if each query costs t ≥ 1 operations instead of one, a run within T
operations stays within T·t operations. -/
alias PaperIndex.achievable.QueryMachines.stSlowDown := QueryMachines.stSlowDown

/-- Beside Definition 4: if the queries of a machine are answered by a second machine with queries
of its own, own steps add up, with two more per query, and the queries asked are those of the
answering runs, in order. -/
alias PaperIndex.achievable.QueryMachines.stSubst := QueryMachines.stSubst

/-- Beside Definition 4: if the queries of a machine are answered by a machine without queries that
takes t(x) steps on the query x, the whole run takes its own steps plus the sum of t(x)+2 over the
queries asked. -/
alias PaperIndex.achievable.QueryMachines.stPlug := QueryMachines.stPlug

/-- Beside Definition 4: if the query x is priced at w(x) and a second machine answers it within
w(x)−2 operations, answering the queries in this way keeps the whole within the cost of the first
machine. -/
alias PaperIndex.achievable.QueryMachines.stSubstWithin := QueryMachines.stSubstWithin

/-- Beside Definition 4: answering queries by a second machine and then building in the answers to
its queries gives the same machine as answering them by the second machine with its answers built
in. -/
alias PaperIndex.achievable.QueryMachines.stCloseSubst := QueryMachines.stCloseSubst

/-- Beside Definition 4: a machine whose steps run in polynomial time keeps this property when its
queries are answered by a machine without queries whose steps run in polynomial time. -/
alias PaperIndex.achievable.QueryMachines.stPolyPlug := QueryMachines.stPolyPlug

/-- Beside Definition 4: a machine whose steps run in polynomial time keeps this property when its
queries are answered by a machine with queries of its own whose steps run in polynomial time. -/
alias PaperIndex.achievable.QueryMachines.stPolySubst := QueryMachines.stPolySubst

/-- Beside Definition 4: a machine whose steps run in polynomial time keeps this property when
answers computed in polynomial time from the query alone are built in. -/
alias PaperIndex.achievable.QueryMachines.stPolyClose := QueryMachines.stPolyClose

/-- Beside Definition 4: a machine without queries, seen as a machine with query access, runs as
before and asks no query. -/
alias PaperIndex.achievable.QueryMachines.stLiftRuns := QueryMachines.stLiftRuns

/-- Beside Definition 4: the machine that asks one query and returns the answer takes no step of its
own and asks exactly that query. -/
alias PaperIndex.achievable.QueryMachines.stQueryRuns := QueryMachines.stQueryRuns

/-- Beside Definition 4: rewriting the queries of a machine by a function h gives the same run, with
the list of queries mapped by h. -/
alias PaperIndex.achievable.QueryMachines.stMapAskRuns := QueryMachines.stMapAskRuns

/-- Beside Definition 4: applying a function g to the input before a machine runs gives the run of
that machine on g of the input. -/
alias PaperIndex.achievable.QueryMachines.stMapInRuns := QueryMachines.stMapInRuns

/-- Beside Definition 4: applying a function to the result of a machine gives the same run, with the
function applied to the result. -/
alias PaperIndex.achievable.QueryMachines.stMapOutRuns := QueryMachines.stMapOutRuns

/-- Beside Definition 4: running one machine after another: own steps add up, with one more for the
hand-over, and the queries of the first come before those of the second. -/
alias PaperIndex.achievable.QueryMachines.stBindRuns := QueryMachines.stBindRuns

/-- Beside Definition 4: running two machines on one input and returning both results: own steps add
up, with one more for the hand-over, and the queries of the first come first. -/
alias PaperIndex.achievable.QueryMachines.stBothRuns := QueryMachines.stBothRuns

/-- Beside Definition 4: a choice between two machines made from the input: the run is that of the
machine chosen, on states one larger. -/
alias PaperIndex.achievable.QueryMachines.stBranchRuns := QueryMachines.stBranchRuns

/-- Beside Definition 4: a loop: the own steps are the sum over the rounds of the own steps of the
body plus one, the queries of the rounds follow one another, and the result is the fold over the
rounds. -/
alias PaperIndex.achievable.QueryMachines.stFoldWhileRuns := QueryMachines.stFoldWhileRuns

/-- Beside Definition 4: a loop over y < N(a), the range a function of the input a: own steps are
the sum over y of the steps of the body plus one, and the queries of the rounds follow one another. -/
alias PaperIndex.achievable.QueryMachines.stFoldRangeRuns := QueryMachines.stFoldRangeRuns

/-- Beside Definition 4: where a function g has a value, the machine that computes g returns it in
one step. -/
alias PaperIndex.achievable.Groundwork.Stepped.ofOption_runs := Groundwork.Stepped.ofOption_runs

/-- Beside Definition 4: building in the answers to the queries leaves a machine without queries
unchanged. -/
alias PaperIndex.achievable.QueryMachines.QueryMachine.close_lift := QueryMachines.QueryMachine.close_lift

/-- Beside Definition 4: building in the answers to the queries turns a single query into one step
that looks the answer up. -/
alias PaperIndex.achievable.QueryMachines.QueryMachine.close_query := QueryMachines.QueryMachine.close_query

/-- Beside Definition 4: building in the answers to queries rewritten by a function h is building
in, for each query, the answer to its image under h. -/
alias PaperIndex.achievable.QueryMachines.QueryMachine.close_mapAsk := QueryMachines.QueryMachine.close_mapAsk

/-- Beside Definition 4: building in the answers to the queries commutes with applying a function to
the input. -/
alias PaperIndex.achievable.QueryMachines.QueryMachine.close_mapIn := QueryMachines.QueryMachine.close_mapIn

/-- Beside Definition 4: building in the answers to the queries commutes with applying a function to
the result. -/
alias PaperIndex.achievable.QueryMachines.QueryMachine.close_mapOut := QueryMachines.QueryMachine.close_mapOut

/-- Beside Definition 4: building in the answers to the queries commutes with running one machine
after another. -/
alias PaperIndex.achievable.QueryMachines.QueryMachine.close_bind := QueryMachines.QueryMachine.close_bind

/-- Beside Definition 4: building in the answers to the queries commutes with a loop. -/
alias PaperIndex.achievable.QueryMachines.QueryMachine.close_foldWhile := QueryMachines.QueryMachine.close_foldWhile

/-- Beside Definition 4: building in the answers to the queries commutes with a choice between two
machines made from the input. -/
alias PaperIndex.achievable.QueryMachines.QueryMachine.close_branch := QueryMachines.QueryMachine.close_branch

/-- Beside Definition 4: building in the answers to the queries commutes with running two machines
on one input and returning both results. -/
alias PaperIndex.achievable.QueryMachines.QueryMachine.close_both := QueryMachines.QueryMachine.close_both

/-- Beside Definition 4: building in the answers to the queries commutes with a choice between two
machines by a yes-or-no test on the input. -/
alias PaperIndex.achievable.QueryMachines.QueryMachine.close_ite := QueryMachines.QueryMachine.close_ite

/-- Beside Definition 4: building in the answers to the queries leaves a machine that returns a
constant unchanged. -/
alias PaperIndex.achievable.QueryMachines.QueryMachine.close_const := QueryMachines.QueryMachine.close_const

/-- Beside Definition 4: building in the answers to the queries commutes with running a first
machine and then, if it returns a value, a second machine on it (a default value otherwise). -/
alias PaperIndex.achievable.QueryMachines.QueryMachine.close_optBind := QueryMachines.QueryMachine.close_optBind

/-- Beside Definition 4: a lemma on machines with query access to tables, with no counterpart in the
paper: answering the queries by a fixed oracle before or after forming a loop over the numbers below
a bound gives the same machine. -/
alias PaperIndex.achievable.QueryMachines.QueryMachine.close_foldRange := QueryMachines.QueryMachine.close_foldRange

/-- Beside Definition 4: building in the answers to the queries commutes with the sum over y < N(a)
of the results of a machine. -/
alias PaperIndex.achievable.QueryMachines.QueryMachine.close_sumRange := QueryMachines.QueryMachine.close_sumRange

/-- Beside Definition 4: building in the answers to the queries commutes with the product over y <
N(a) of the results of a machine. -/
alias PaperIndex.achievable.QueryMachines.QueryMachine.close_prodRange := QueryMachines.QueryMachine.close_prodRange

/-- Beside Definition 4: building in the answers to the queries commutes with a test followed, if it
says yes, by a second machine (0 otherwise). -/
alias PaperIndex.achievable.QueryMachines.QueryMachine.close_gated := QueryMachines.QueryMachine.close_gated

/-- Beside Definition 4: the remark «If (K,e) is achievable, so is (K,e₁) for every e₁≥e». -/
alias PaperIndex.achievable.Printed.stMono := Printed.stMono

/-- Beside Definition 4: for K ≥ 2, trying all choices of one string per edge gives the value of a
(K,λ)-clique within C·2^{K²λ/2}(B+λ)^C operations, on states of size at most C(B+λ)^C, for some C. -/
alias PaperIndex.achievable.Printed.stBrute := Printed.stBrute

/-- Beside Definition 4: (K,½) is achievable for every K ≥ 2, so e* ≤ ½; also 0 ≤ e*. -/
alias PaperIndex.achievable.Printed.stHalf := Printed.stHalf

/-! ## Lemma 1, Section 3 -/

/-- **Lemma 1** (if (K, e) is achievable and g = 3K⁸, the value of every network on [g] is computed
within C₁·2^{e(U+gP/K)+2gP/K}·(P+B)^{C₁}·τ operations). In Lean: an operation is one polynomial-time
step or one query, and the network is given by queries, each membership test or value of W_a,
Ψ_{a,b}, f_{a,b} costing τ operations, in place of the algorithm of Definition 2 (iii). The
achievability assumed also bounds memory polynomially, and the conclusion adds polynomial-time steps
and states of size at most C₁·(P+B)^{C₁}; because of these bounds on memory, neither this statement
nor the printed lemma implies the other. -/
alias PaperIndex.grouping := Printed.groupingLemma

/-- Lemma 1: the same for the algorithm of its proof, built on any algorithm for cliques. In Lean:
for K ≥ 2, e ≥ 0 and any machine meeting the bound of Definition 4 for (K, e) with polynomially
bounded memory, the algorithm of the proof built on it attains the bound for some C₁, on states of
size at most C₁·(P+B)^{C₁}. The network is given by queries at τ operations each; the time of one
step is not bounded here. -/
alias PaperIndex.groupingForTheAlgorithm := Printed.stGroupingTied

/-- A step of the proof of Lemma 1: for γ ≠ γ', Y_{γ,γ'} is the sum of c_{a,b} over the ordered
pairs (a,b) that contribute, that is, with a ∈ G_γ and b ∈ G_γ'. -/
alias PaperIndex.grouping.Variance.stYIsSum := Variance.stYIsSum

/-- A step of the proof of Lemma 1: «Each ordered pair (a,b) contributes with probability 1/K²»: of
the K^g groupings, K^g/K² put a in G_γ and b in G_γ'. -/
alias PaperIndex.grouping.Variance.stPairProb := Variance.stPairProb

/-- A step of the proof of Lemma 1: «so 𝔼Y_{γ,γ'}=U/K²», with the expectation written as a sum over
all K^g groupings. -/
alias PaperIndex.grouping.Variance.stMean := Variance.stMean

/-- A step of the proof of Lemma 1: Var Y_{γ,γ'} is the sum, over two ordered pairs, of their
c-values times the covariance of their indicators (sums over all groupings, scaled by K⁴), as used
in «Hence». -/
alias PaperIndex.grouping.Variance.stVarIsSumOfCov := Variance.stVarIsSumOfCov

/-- A step of the proof of Lemma 1: «The indicators of two ordered pairs have covariance 0 if the
pairs are disjoint». -/
alias PaperIndex.grouping.Variance.stCovDisjoint := Variance.stCovDisjoint

/-- A step of the proof of Lemma 1: the covariance of the indicators of two ordered pairs is «at
most 1 otherwise», which holds for any two pairs. -/
alias PaperIndex.grouping.Variance.stCovLeOne := Variance.stCovLeOne

/-- A step of the proof of Lemma 1: by Definition 2 (i), for symmetric c, the ordered pairs that
meet a fixed pair have c-values summing to at most 4P. -/
alias PaperIndex.grouping.Variance.stMeeting := Variance.stMeeting

/-- A step of the proof of Lemma 1: «Hence Var Y_{γ,γ'}≤Σ_{(a,b)∈[g]²: a≠b} c_{a,b}·4P=4PU», with
the variance written as a sum over all groupings. -/
alias PaperIndex.grouping.Variance.stVar := Variance.stVar

/-- A step of the proof of Lemma 1: the inequality behind «Hence», with any numbers κ(p,q) in place
of the covariances: for symmetric c with Definition 2 (i), if κ is 0 on disjoint ordered pairs and
at most m ≥ 0, then Σ_p Σ_q c_p c_q κ(p,q) ≤ 4PU·m. -/
alias PaperIndex.grouping.Variance.stHence := Variance.stHence

/-- A step of the proof of Lemma 1: the bound Var Y_{γ,γ'} ≤ 4PU, derived from the variance as a sum
of covariances, covariance 0 for disjoint pairs and at most 1 otherwise, and the inequality behind
«Hence». -/
alias PaperIndex.grouping.Variance.stVarOf := Variance.stVarOf

/-- A step of the proof of Lemma 1: «so 𝔼Y_{γ,γ'}=U/K²», derived from Y_{γ,γ'} as a sum over the
contributing ordered pairs and from each pair contributing with probability 1/K². -/
alias PaperIndex.grouping.Variance.stSoMean := Variance.stSoMean

/-- A step of the proof of Lemma 1: U ≤ gP by Definition 2 (i), as in «4PU≤4gP²». -/
alias PaperIndex.grouping.Variance.stTotalLe := Variance.stTotalLe

/-- A step of the proof of Lemma 1: if Var Y_{γ,γ'} ≤ 4PU and U ≤ gP, then «by Chebyshev
Pr(Y_{γ,γ'}>U/K²+gP/K³)≤4K⁶/g». -/
alias PaperIndex.grouping.Variance.stChebOfVar := Variance.stChebOfVar

/-- A step of the proof of Lemma 1: if every pair of groups obeys the Chebyshev bound, then «By a
union bound over the fewer than K²/2 pairs of groups, some pair violates this bound with probability
less than» 2K⁸/g. -/
alias PaperIndex.grouping.Variance.stSomePairOfCheb := Variance.stSomePairOfCheb

/-- A step of the proof of Lemma 1: the paragraph «A good grouping exists» at g = 3K⁸, with its
numbers 4/(3K²), 2/3, K/g, 1/3, derived from the bound on the variance, U ≤ gP, Chebyshev and the
union bound. -/
alias PaperIndex.grouping.Variance.stGroupingOf := Variance.stGroupingOf

/-- A step of the proof of Lemma 1: «A good grouping exists»: for g = 3K⁸ and symmetric c with
Definition 2 (i), the Chebyshev and union bounds of the text hold and some grouping is good. -/
alias PaperIndex.grouping.Variance.groupingFacts := Variance.groupingFacts

/-- A step of the proof of Lemma 1: from the existence of a good grouping: «Go through all K^g
groupings (a constant) and fix the first good one» finds, for g = 3K⁸, a good grouping numbered
below K^g. -/
alias PaperIndex.grouping.Variance.stSearchOfGrouping := Variance.stSearchOfGrouping

/-- A step of the proof of Lemma 1: «Go through all K^g groupings (a constant) and fix the first
good one»: for g = 3K⁸ the search finds a grouping numbered below K^g with (G1) and (G2). -/
alias PaperIndex.grouping.Variance.stSearch := Variance.stSearch

/-- A step of the proof of Lemma 1: the layout of a string on an edge: «the pair {a,b} is assigned a
block of c_{a,b} consecutive positions of {1,…,L}», pairs in a fixed order, and the positions after
the last block are appended bits. -/
alias PaperIndex.grouping.Value.stLayout := Value.stLayout

/-- A step of the proof of Lemma 1: for one string per edge, «both W̃_γ and W̃_γ' read θ_{a,b} from
the same block of this string, so θ_{a,b}=θ_{b,a}». -/
alias PaperIndex.grouping.Value.stSameBlock := Value.stSameBlock

/-- A step of the proof of Lemma 1: «the appended bits must be 0»: if an appended bit on some edge
is 1, the product of the tables W̃_γ is 0. -/
alias PaperIndex.grouping.Value.stAppendedZero := Value.stAppendedZero

/-- A step of the proof of Lemma 1: if Y_{γ,γ'} ≤ L, the strings of L bits, one per edge, with all
appended bits 0 correspond one to one to the choices of one θ_{a,b} ∈ {0,1}^{c_{a,b}} per pair in
different groups. -/
alias PaperIndex.grouping.Value.stBlocks := Value.stBlocks

/-- A step of the proof of Lemma 1: «Together with the sums inside the tables»: a product over the
groups of sums over the settings of their nodes is one sum over the settings of all nodes. -/
alias PaperIndex.grouping.Value.stSumsInside := Value.stSumsInside

/-- A step of the proof of Lemma 1: «Together with the sums inside the tables, this is a sum over
all z∈∏_{a∈[g]}S_a and over one string θ_{a,b}∈{0,1}^{c_{a,b}} per pair {a,b} of nodes in different
groups». -/
alias PaperIndex.grouping.Value.stJointSum := Value.stJointSum

/-- A step of the proof of Lemma 1: «Each θ_{a,b} occurs only in f_{a,b} and f_{b,a}»: for each z,
summing over all θ gives the term of z in the value Z of the network. -/
alias PaperIndex.grouping.Value.stSumOut := Value.stSumOut

/-- A step of the proof of Lemma 1: «so the value equals Z»: if Y_{γ,γ'} ≤ L, the (K,L)-clique of
the groups, with two copies of the string on every edge as in Definition 3, has the value of the
network. -/
alias PaperIndex.grouping.Value.stValueEqualsZ := Value.stValueEqualsZ

/-- A step of the proof of Lemma 1: the sum over all z and one θ_{a,b} per pair in different groups,
derived from θ_{a,b}=θ_{b,a}, the appended bits being 0, the correspondence of strings and blocks,
and the sums inside the tables. -/
alias PaperIndex.grouping.Value.stJointSumOf := Value.stJointSumOf

/-- A step of the proof of Lemma 1: «so the value equals Z», derived from the value of a clique as a
sum over one string per edge, the joint sum over z and θ, and summing out each θ_{a,b}. -/
alias PaperIndex.grouping.Value.stValueEqualsZOf := Value.stValueEqualsZOf

/-- A step of the proof of Lemma 1: «so the value equals Z» with the value of the clique written
over one string per edge, derived from the form with two copies per edge and the sentence after
Definition 3. -/
alias PaperIndex.grouping.Value.stValueOf := Value.stValueOf

/-- A step of the proof of Lemma 1: «so the value equals Z»: if Y_{γ,γ'} ≤ L, the (K,L)-clique with
the tables W̃_γ, its value written over one string per edge, has the value of the network. -/
alias PaperIndex.grouping.Value.stValue := Value.stValue

/-- A step of the proof of Lemma 1: line 10 of Algorithm 1 stops at the first good grouping: if x is
the first number below K^g whose grouping is good, the search halts within 2(x+1) steps and returns
x. -/
alias PaperIndex.grouping.Exits.stSearchStops := Exits.stSearchStops

/-- A step of the proof of Lemma 1: the run of the search in line 10 of Algorithm 1, derived from
the same statement for any loop that stops at its first success. -/
alias PaperIndex.grouping.Exits.stSearchStopsOf := Exits.stSearchStopsOf

/-- A step of the proof of Lemma 1: Lemma 1 for the algorithm of its proof, derived from: a good
grouping exists and the first is found, the cost of one entry, «so the value equals Z», and the run
of the search. -/
alias PaperIndex.grouping.Exits.stGroupingLemmaOf := Exits.stGroupingLemmaOf

/-- A step of the proof of Lemma 1: the algorithm of the proof of Lemma 1, with the search of line
10 of Algorithm 1, has polynomial-time steps if the algorithm for cliques has. -/
alias PaperIndex.grouping.Exits.stKeeps := Exits.stKeeps

/-- A step of the proof of Lemma 1: the polynomial-time steps of the algorithm of the proof of Lemma
1, derived from those of a loop that can stop early. -/
alias PaperIndex.grouping.Exits.stKeepsOf := Exits.stKeepsOf

/-- A step of the proof of Lemma 1: «Answer each of its at most C 2^{eK²L}(B'+L)^C queries by
computing the entry»: if each takes at most t ≥ 1 steps, the value comes within 3C·2^{eK²λ}(B+λ)^C·t
steps. -/
alias PaperIndex.grouping.Printed.stAnswerEachQuery := Printed.stAnswerEachQuery

/-- A step of the proof of Lemma 1: «|W̃_γ|<2^{B'}», and one entry takes c₁·2^{P⌊2g/K⌋}·τ operations
on states of polynomial size, for a grouping with (G1) and Y_{γ,γ'} ≤ L ≤ 2gP. -/
alias PaperIndex.grouping.Printed.stEntryCost := Printed.stEntryCost

/-- A step of the proof of Lemma 1: Lemma 1 for the algorithm of its proof on any clique algorithm,
derived from: the first good grouping is found and the search stops there, the cost of an entry, «so
the value equals Z», answering queries. -/
alias PaperIndex.grouping.Printed.stGroupingTiedOf := Printed.stGroupingTiedOf

/-- A step of the proof of Lemma 1: the algorithm of the proof of Lemma 1 has polynomial-time steps
if the algorithm for cliques on which it is built has. -/
alias PaperIndex.grouping.Printed.stGroupingPoly := Printed.stGroupingPoly

/-- A step of the proof of Lemma 1: if a machine does what Lemma 1 says, then with its queries
answered by the procedures of Definition 2 (iii), of at most τ steps each, it takes at most
3C₁·2^{e(U+gP/K)+2gP/K}(P+B)^{C₁}·τ steps. -/
alias PaperIndex.grouping.Printed.stOnProcedures := Printed.stOnProcedures

/-- A step of the proof of Lemma 1: Lemma 1 as used in Proposition 3 and Section 6: if a machine
does what it says, then on a network whose procedures query an oracle it needs at most
3C₁·2^{e(U+gP/K)+2gP/K}(P+B)^{C₁}·τ operations. -/
alias PaperIndex.grouping.Given.stOnGiven := Given.stOnGiven

/-- A step of the proof of Lemma 1: Lemma 1 for the algorithm of its proof, with the search of line
10 of Algorithm 1, built on any algorithm for cliques that meets the bound for (K, e). -/
alias PaperIndex.grouping.Exits.stGroupingLemma := Exits.stGroupingLemma

/-! ## Eight-square identity, Section 4 -/

/-- **Eight-square identity, display (28)** (σ(p,q)·σ(p′,q′) + σ(p,q′)·σ(p′,q) = 0 for all blocks
with p ⊕ q = p′ ⊕ q′ and q ≠ q′). In Lean: as printed. -/
alias PaperIndex.eightSquareIdentity := Eight.signs

/-! ## Definition 5, Section 4 -/

/-- **Definition 5** (the functions A₀, …, A_t). In Lean: as printed, with the blocks numbered from 0. -/
alias PaperIndex.pieces := Eight.A

/-! ## Lemma 2, Section 4 -/

/-- **Lemma 2** (the A_i add up to 2^t·[x = v][y = u], and A_i factors through c_i^row bits row-wise
and through c_i^col bits column-wise). In Lean: the claims that Aᵢ and the functions of both
factorizations are computable in time poly(λ) are left out; the statement adds the bound c_i^row +
c_i^col ≤ 11t from the proof of Lemma 2 (c). -/
alias PaperIndex.piecesLemma := Eight.lemPieces

/-! ## Proposition 3, Section 5 -/

/-- **Proposition 3** (if (K, e) is achievable and g = 3K⁸, then (g², e′) is achievable for e′ = (ρ +
2/K)·e + 2/K; hence e* = 0; this entry is the first sentence). In Lean: «achievable» is Definition 4
with a bound C·(B+λ)^C on the size of every state added, in the hypothesis and in the conclusion, so
this does not give the printed statement; an operation is one step of a machine (any function
computed in polynomial time in the state) or one table query, and λ and B are given in unary. -/
alias PaperIndex.level := Given.levelProposition

/-- Proposition 3: its second sentence: e* = 0. In Lean: e* is the infimum for Lean's «achievable»,
which adds a polynomial memory bound to Definition 4 and counts steps and queries, so it is not the
printed e*; as Mathlib's infimum of the empty set is 0, it says something only with «(K, ½) is
achievable for every K», proved separately, as is «for every η > 0, (K, η) is achievable for
infinitely many K». -/
alias PaperIndex.levelHence := Given.eStarZero

/-- A step of the proof of Proposition 3: Proposition 3, first sentence, for the algorithm of its
proof: if an algorithm for (K, e), K ≥ 2, e ≥ 0, has polynomial-time steps, so does the one built on
it, and it works for (9K¹⁶, (ρ+2/K)e+2/K). -/
alias PaperIndex.level.Exits.stLevelUp := Exits.stLevelUp

/-- A step of the proof of Proposition 3: the first sentence of Proposition 3 for the algorithm of
its proof, from Lemma 1 for the algorithm of its proof: «Apply Lemma 1 to the network with the
smaller total». -/
alias PaperIndex.level.Exits.stLevelUpOf := Exits.stLevelUpOf

/-- A step of the proof of Proposition 3: the first sentence of Proposition 3, derived from its form
for the algorithm of its proof. -/
alias PaperIndex.level.Exits.stLevelAchievableOf := Exits.stLevelAchievableOf

/-- A step of the proof of Proposition 3: «Hence e* = 0», derived from the first sentence of
Proposition 3 (for K ≥ 2, e ≥ 0) by the last paragraph of its proof. -/
alias PaperIndex.level.Exits.stEStarOf := Exits.stEStarOf

/-- A step of the proof of Proposition 3: the second sentence of Proposition 3: «Hence e* = 0»; here
e* is taken over a form of Definition 4 in which each step takes polynomial time, a table query
costs t steps, the bound is multiplied by t, entries are at most 2^B with B = 0 allowed, and memory
is bounded. -/
alias PaperIndex.level.Exits.eStar_eq_zero := Exits.eStar_eq_zero

/-- A step of the proof of Proposition 3: if a table query takes one step: «Both networks satisfy
Definition 2 with P = g³λ (so gP = N), with B₁ = gB + g²λ + 1 in the role of B, and with τ = poly(B +
λ)». -/
alias PaperIndex.level.Printed.grid_isNetwork_of := Printed.grid_isNetwork_of

/-- A step of the proof of Proposition 3: in the proof of Proposition 3, for each ι: «Both networks
satisfy Definition 2 with P=g³λ (so gP=N), with B₁=gB+g²λ+1 in the role of B, and with τ=poly(B+λ)». -/
alias PaperIndex.level.Printed.stBothNetworks := Printed.stBothNetworks

/-- A step of the proof of Proposition 3: Proposition 3, first sentence, for the algorithm of its
proof: built on any machine that meets Definition 4 (with a memory bound) for (K, e), K ≥ 2, e ≥ 0,
it meets it for ((3K⁸)², (ρ+2/K)e+2/K); here from Definition 4 with a table query at one operation. -/
alias PaperIndex.level.Printed.stLevelTied := Printed.stLevelTied

/-- A step of the proof of Proposition 3: the algorithm of the proof of Proposition 3 has
polynomial-time steps if the algorithm for cliques on which it is built has; here from Definition 4
with a table query at one operation. -/
alias PaperIndex.level.Printed.stLevelPoly := Printed.stLevelPoly

/-- A step of the proof of Proposition 3: Proposition 3, first sentence: «If (K,e) is achievable and
g=3K⁸, then (g²,e′) is achievable for e′=(ρ+2/K)e+2/K», with ρ = 11/12. -/
alias PaperIndex.level.Printed.levelProposition := Printed.levelProposition

/-- A step of the proof of Proposition 3: the second sentence of Proposition 3: «Hence e* = 0»; here
e* is formed from Definition 4 with a table query at one operation and with an added bound on memory
polynomial in B+λ (in Lean the infimum of no numbers is 0, so this says what the paper says only
together with «e* ≤ ½», which is proved beside it). -/
alias PaperIndex.level.Printed.eStarZero := Printed.eStarZero

/-- A step of the proof of Proposition 3: the last sentence of the proof: «That is, for every η>0,
(K,η) is achievable for infinitely many K»; here «achievable» is that of Definition 4 with a table
query at one operation and a polynomial bound on memory added. -/
alias PaperIndex.level.Printed.stEveryEta := Printed.stEveryEta

/-- A step of the proof of Proposition 3: «Both networks satisfy Definition 2 with P = g³λ (so gP =
N), with B₁ = gB + g²λ + 1 in the role of B, and with τ = poly(B + λ)», the tables given by query
access. -/
alias PaperIndex.level.Given.stGridGiven := Given.stGridGiven

/-- A step of the proof of Proposition 3: Proposition 3, first sentence: from any machine meeting
Definition 4 for (K, e), K ≥ 2, e ≥ 0 (a table query is one operation, a bound on memory added), one
built on it meets it for ((3K⁸)², (ρ+2/K)e+2/K); proved reading Definition 2 (iii) as one condition:
procedures with polynomial-time steps answer every question within τ operations. -/
alias PaperIndex.level.Given.stLevelTied := Given.stLevelTied

/-- A step of the proof of Proposition 3: the algorithm of the proof of Proposition 3 has
polynomial-time steps if the clique algorithm it is built on, as in Definition 4 with a table query
at one operation, has; proved reading Definition 2 (iii) as one condition: the network is given by
procedures with polynomial-time steps that answer every question within τ operations. -/
alias PaperIndex.level.Given.stLevelPoly := Given.stLevelPoly

/-- A step of the proof of Proposition 3: end of the proof of Proposition 3: «That is, for every
η>0, (K,η) is achievable for infinitely many K», in the sense of Definition 4 with a query as one
operation and memory bounded polynomially; proved with Definition 2 (iii) read as: the network is
given by procedures with polynomial-time steps that answer every question within τ operations. -/
alias PaperIndex.level.Given.stEveryEta := Given.stEveryEta

/-- A step of the proof of Proposition 3: the inequality g(g²−1)λ ≤ g³λ of «encoded by concatenation
in g(g²−1)λ≤P bits», where P = g³λ. -/
alias PaperIndex.level.Coding.stGridLength := Coding.stGridLength

/-- A step of the proof of Proposition 3: in Lean a setting of a row (or column) has g³λ bits, with
unused bits in each grid point's slot for itself; read at g(g²−1)λ bits it is the same network. -/
alias PaperIndex.level.Coding.stGridPadding := Coding.stGridPadding

/-- A step of the proof of Proposition 3: the first sentence of Proposition 3 (with g² written 9K¹⁶,
for K ≥ 2 and e ≥ 0), derived from its form for the algorithm of its proof. -/
alias PaperIndex.level.Exits.stLevelAchievable := Exits.stLevelAchievable

/-! ## Lemma 4, Section 6 -/

/-- **Lemma 4** (Sparsification Lemma, for clauses of at most 3 literals, in the form of Dell et
al.: an assignment satisfies φ if and only if it satisfies at least one of the listed formulas, and
no two of them share a satisfying assignment). In Lean: this is the lemma for deciding only: φ is
satisfiable if and only if at least one of the listed formulas is. The printed lemma says more: an
assignment satisfies φ if and only if it satisfies at least one of them, and no two of them share a
satisfying assignment (the form of Dell et al.); neither is part of this statement. Both are proved
in a separate theorem, SparsificationLemma.stExactlyOne, for the outputs of Lean's branching
procedure, which include the list that this machine prints, at every clause width and for all
thresholds: every assignment that satisfies the formula satisfies exactly one of the outputs, and
every other assignment satisfies none. They are proved again, in several separate statements, for
the search tree in Lean's proof of Corollary 6. One Turing machine of Mathlib serves every ε:
started on 1^s 0 111 0 followed by the code of φ, with s depending on ε, it prints the list within
2^(εn)·c(n+1)^c steps, c depending on ε. Lean proves this for the branching procedure of Appendix C
with thresholds of its own, not by the cited lemma; no Lean proof of Theorem 2 uses this statement. -/
alias PaperIndex.sparsification := SparsificationLemma.Mach.lemSparsification_holds

/-- Lemma 4: as an enumeration. In Lean: for every ε > 0 there are M(ε) and a parameter τ such that
a depth-first walk through the tree of the branching procedure of Appendix C, with thresholds of
Lean's own, produces the formulas one after the other; the time is stated as two moves of the walk
per formula produced, each move taking polynomial time on a stack of polynomial size. -/
alias PaperIndex.sparsificationAsEnumeration := Enumerate.stEnumeration

/-- Lemma 4: the lemma in its form for deciding, together with the statement that the list is the
one that Lean's own branching procedure produces. In Lean: one Turing machine serves every ε, given
in unary a precision s depending on ε; within 2^(εn)·c(n+1)^c steps it prints, in order, the
formulas produced by a branching procedure like that of Appendix C with thresholds of Lean's own and
the parameter 2^(4s+17) (not the τ of Definition 2), without its deletion of clauses holding a
variable and its negation; these are at most 2^(εn) formulas on the same variables, each with at
most M(ε)·n clauses, none repeated, at least one of them satisfiable exactly if φ is. -/
alias PaperIndex.sparsificationWithItsList := Enumerate.stNamed

/-- A step of the proof of Lemma 4: not in the paper: in order, the formulas that a depth-first walk
produces through the tree of a branching procedure like that of Appendix C (outputs ψ ∪ 𝒩, Lean's
own thresholds, not Calabro's, no deletion of clauses with a variable and its negation) are the list
printed by Lean's machine for Lemma 4 as worded. -/
alias PaperIndex.sparsification.Enumerate.stProducedIsList := Enumerate.stProducedIsList

/-- A step of the proof of Lemma 4: as in the proof of Theorem C: the walk that produces the outputs
ψ ∪ 𝒩 and the walk without the set 𝒩 go through the same tree and have the same ψ at each leaf. -/
alias PaperIndex.sparsification.Enumerate.stSameTree := Enumerate.stSameTree

/-- A step of the proof of Lemma 4: the lemma as an enumeration for every parameter τ ≥ 24 with
(3/τ)·log₂(e·τ·τ⁶) ≤ ε, with M(ε) = τ⁶. -/
alias PaperIndex.sparsification.Enumerate.stEnumeratesTau := Enumerate.stEnumeratesTau

/-- A step of the proof of Lemma 4: the lemma as worded, with its list named as the formulas of the
branching procedure of Appendix C with Lean's own thresholds, from three facts: a machine prints
that list, the procedure produces it, and the procedure meets the lemma for every large enough
parameter τ. -/
alias PaperIndex.sparsification.Enumerate.stNamedOf := Enumerate.stNamedOf

/-- A step of the proof of Lemma 4: the lemma as worded, with its list being the formulas of the
branching procedure, gives the lemma as worded and the lemma as an enumeration. -/
alias PaperIndex.sparsification.Enumerate.stNamedGives := Enumerate.stNamedGives

/-! ## Definition 6, Section 7 -/

/-- **Definition 6** (s_k, s_∞, ETH and SETH; this entry is s_k). In Lean: time is counted in steps
of Mathlib's deterministic multi-stack Turing machines with finite alphabets, not in operations of
the word RAM, and the bound is ⌊c·2^{δn}⌋ steps for every n; a k-CNF is a list of clauses of at most
k literals, no clause written twice, each clause a list of literals that may be empty or repeat a
literal (the paper has nonempty sets); it is given to the machine as n in unary followed by k slots
of ⌊log₂(2n)⌋+1 bits for each clause; s_k is ∞ if no δ works. -/
alias PaperIndex.exponentOfKSat := SatK.sTM

/-- Definition 6: the same numbers for a code of formulas that does not depend on k. In Lean: time
is counted in steps of Mathlib's multi-stack Turing machines, not in word-RAM operations as in the
paper, on a fixed code of formulas, the same for every k, that writes each clause with its own
literals and an end mark; the paper fixes no code. A formula is a list of clauses without
repetition, each a list of literals, and s_k is ∞ if no δ works. The Main Theorem's file states that
ETH is false for numbers defined with another code, k slots per clause; Lean does not state how the
two are related. -/
alias PaperIndex.exponentOfKSatForACodeWithoutSlots := SatFree.s

/-- Definition 6: the sentence after it: s_k ≤ s_{k+1}. In Lean: the inequality is proved for the
numbers s_k defined with Mathlib's multi-stack Turing machines and a code of formulas that is the
same for every k. -/
alias PaperIndex.exponentsIncrease := SatFree.increasing

/-- Definition 6: the sentences after it: s_∞ is the limit of the s_k, and ETH is the same as s₃ > 0.
In Lean: the limit and the equivalence are proved for the numbers s_k defined with Mathlib's
multi-stack Turing machines and a code of formulas that is the same for every k. -/
alias PaperIndex.limitAndEth := SatFree.limitAndEth

/-- Definition 6: s_∞. In Lean: the numbers s_k are those defined on Turing machines, with the value
∞ where no δ works. -/
alias PaperIndex.sInfinity := PaperSentences.sInfty

/-- Definition 6: the Exponential Time Hypothesis. In Lean: the numbers s_k are those defined on
Turing machines, with the value ∞ where no δ works. -/
alias PaperIndex.eth := PaperSentences.ETH

/-- Definition 6: the Strong Exponential Time Hypothesis. In Lean: the numbers s_k are those defined
on Turing machines, with the value ∞ where no δ works. -/
alias PaperIndex.seth := PaperSentences.SETH

/-- Beside Definition 6: «Trying all assignments»: exhaustive search decides k-SAT, for every k,
within c·2^n polynomial-time steps, and one Turing machine with finite alphabets simulates it within
c·(n+2)^c·2^n steps. -/
alias PaperIndex.exponentOfKSat.FreeCode.stBrute := FreeCode.stBrute

/-- Beside Definition 6: «Trying all assignments»: one machine with finite alphabets decides k-SAT
for every k, within c·(n+2)^c·2^n steps, where c depends on k. -/
alias PaperIndex.exponentOfKSat.SatFree.bruteForce := SatFree.bruteForce

/-- Beside Definition 6: «Trying all assignments gives s_k≤1, so s_∞≤1». -/
alias PaperIndex.exponentOfKSat.SatFree.atMostOne := SatFree.atMostOne

/-- Beside Definition 6: «Corollary 5 holds under each of these conventions»: for randomized
algorithms with error at most p, for every p ≥ 0, s_k = 0 for every k ≥ 3. -/
alias PaperIndex.exponentOfKSat.SatFree.allZeroRandomized := SatFree.allZeroRandomized

/-- Beside Definition 6: «A k-CNF is also a (k+1)-CNF»: a machine that decides (k+1)-SAT decides
k-SAT within the same time bound. -/
alias PaperIndex.exponentOfKSat.SatFree.sameMachine := SatFree.sameMachine

/-- Beside Definition 6: the «Hence» for any nondecreasing sequence u_k in [0,∞]: it tends to
sup_{k≥3} u_k, and u_k > 0 for all k ≥ 3 exactly if u_3 > 0. -/
alias PaperIndex.exponentOfKSat.SatFree.henceForEverySequence := SatFree.henceForEverySequence

/-- Beside Definition 6: «A deterministic algorithm is a randomized algorithm that uses no random
bits»: a machine that decides k-SAT in time t is a randomized algorithm with no random bits and
error 0. -/
alias PaperIndex.exponentOfKSat.SatFree.deterministicIsRandomized := SatFree.deterministicIsRandomized

/-- Beside Definition 6: «so allowing randomness can only make s_k smaller»: for every p ≥ 0, s_k
defined with randomized algorithms of error at most p is at most s_k. -/
alias PaperIndex.exponentOfKSat.SatFree.randomnessHelps := SatFree.randomnessHelps

/-- Beside Definition 6: s_∞ = sup_{k≥3} s_k, formed from the numbers s_k defined with Mathlib's
multi-stack Turing machines and a code of formulas that is the same for every k. -/
alias PaperIndex.exponentOfKSat.SatFree.sInfty := SatFree.sInfty

/-- Beside Definition 6: ETH: s_k > 0 for all k ≥ 3, for the numbers s_k defined with Mathlib's
multi-stack Turing machines and a code of formulas that is the same for every k. -/
alias PaperIndex.exponentOfKSat.SatFree.ETH := SatFree.ETH

/-- Beside Definition 6: SETH: s_∞ = 1, for s_∞ formed from the numbers s_k defined with Mathlib's
multi-stack Turing machines and a code of formulas that is the same for every k. -/
alias PaperIndex.exponentOfKSat.SatFree.SETH := SatFree.SETH

/-- Beside Definition 6: the code of a formula, which the paper does not fix, determines the number
of variables, the formula and where the code ends, so the bits that follow it are determined too. -/
alias PaperIndex.exponentOfKSat.SatFree.codeReadable := SatFree.codeReadable

/-! ## Corollary 5, Section 7 -/

/-- **Corollary 5** (s_k = 0 for every k ≥ 3; hence s_∞ = 0, and both ETH and SETH are false). In
Lean: s_k is defined for deterministic multi-stack Turing machines of Mathlib with finite alphabets,
on a code of formulas with k slots per clause, with time ⌊c·2^{δn}⌋ steps; how these s_k relate to
those for the code that does not depend on k is not stated; the cited theorem that s_3 = 0 implies
s_k = 0 is in Lean only for machines cut into polynomial-time steps
(PrintedOrder.eth_and_seth_false); here, for each k > 3, Lean builds a machine that sparsifies,
splits long clauses and calls the 3-SAT machine of the decision form of Theorem 2. The paper gets
s_3 = 0 from the count of Theorem 2 being positive; Lean gets it from the deciding machine directly. -/
alias PaperIndex.ethAndSethFail := FromPrinted.SplitSat.eth_and_seth_false

/-- Corollary 5: ETH is false, as MainResults.lean states it. In Lean: only the negation of ETH is
stated, that is s_3 = 0; s_3 is defined with deterministic multi-stack Turing machines of Mathlib
that decide 3-SAT on formulas with no clause written twice within ⌊c·2^{δn}⌋ steps for every n, so
time is counted in machine steps, not word-RAM operations; it is proved from the Main Theorem, by
turning a counting machine into a deciding one, not from Theorem 2 as in the paper. -/
alias PaperIndex.ethIsFalse := MainResults.ethIsFalse

/-- Corollary 5: the same for the numbers s_k of a code of formulas that does not depend on k. In
Lean: s_k is defined for deterministic multi-stack Turing machines of Mathlib with finite alphabets,
on a code of formulas that does not depend on k; formulas are lists, n is the declared number of
variables, s_k is taken in [0, ∞], and O(2^{δn}) means ⌊c·2^{δn}⌋ steps for every n; as for
Corollary 5, the cited theorem that s_3 = 0 implies s_k = 0 is not in Lean, which builds a machine
for each k instead. -/
alias PaperIndex.ethAndSethFailForACodeWithoutSlots := FromPrinted.FreeCode.allZero

/-- Corollary 5: the remark before it: the same holds when the algorithms may be randomized. In
Lean: a randomized algorithm is a Turing machine of Mathlib that gets ⌊a·2^{βn}⌋ random bits after
the code of the formula and must halt within the time bound on every string of bits, with error at
most p for any real p ≥ 0; the code of formulas does not depend on k. -/
alias PaperIndex.ethAndSethFailForRandomizedAlgorithms := FromPrinted.FreeCode.allZeroRandomized

/-- Corollary 5: the sentence after it: the nondeterministic variant NSETH is false as well. In
Lean: NSETH is stated for deterministic multi-stack Turing machines of Mathlib in verifier form: the
machine gets a witness of any length before the code of the k-DNF, and the formula must be a
tautology exactly when some witness makes it output 1 within c·2^{(1−ε)n} steps; that this matches
nondeterministic time is not proved in Lean. -/
alias PaperIndex.nsethFails := FromPrinted.Consequences.nsethFalse

/-- Corollary 5: the same, with the steps of its proof in the printed order: first the theorem on
3-SAT, then the implication. In Lean: s_k is defined by deterministic multi-stack Turing machines of
Mathlib with finite alphabets, on a code with k slots per clause, in ⌊c·2^{δn}⌋ steps; its relation
to the s_k for a code independent of k is not stated; the step from s_3 = 0 to s_k = 0 is proved
only for machines cut into polynomial-time steps with states of polynomial size, not for every
algorithm. -/
alias PaperIndex.ethAndSethFailInThePrintedOrder := PrintedOrder.eth_and_seth_false

/-- A step of the proof of Corollary 5: for every sequence u_k in [0, ∞]: if sup_{k≥3} u_k = 1, then
u_k > 0 for some k ≥ 3 (the general fact behind «s_∞=1 gives s_k>0 for some k»). -/
alias PaperIndex.ethAndSethFail.SatFree.supOneGivesPositive := SatFree.supOneGivesPositive

/-- A step of the proof of Corollary 5: «s_∞=1 gives s_k>0 for some k»: if SETH holds, then s_k > 0
for some k ≥ 3. -/
alias PaperIndex.ethAndSethFail.SatFree.sethGivesSomeK := SatFree.sethGivesSomeK

/-- A step of the proof of Corollary 5: if a procedure for 3-SAT runs in polynomial-time steps, so
does the reduction of k-SAT to it (sparsify at width k, split the long clauses, ask that procedure). -/
alias PaperIndex.ethAndSethFail.SplitSat.stReduceCert := SplitSat.stReduceCert

/-- A step of the proof of Corollary 5: «split every long clause into clauses of 3 literals with new
variables»: a formula on n variables with at most B·n clauses of at most k literals becomes a 3-CNF
without repeated clauses on at most (1+(k−3)·B)·n variables, satisfiable exactly if the formula is. -/
alias PaperIndex.ethAndSethFail.SplitSat.stLeaf := SplitSat.stLeaf

/-- A step of the proof of Corollary 5: «sparsify»: for k ≥ 3 and ε > 0 some threshold makes the
tree at width k have at most 2^{εn} leaves of at most B·n clauses, and the formula is satisfiable
exactly if some leaf is. -/
alias PaperIndex.ethAndSethFail.SplitSat.stSparsifyK := SplitSat.stSparsifyK

/-- A step of the proof of Corollary 5: «s_3=0 implies s_k=0 for every k≥3», for machines cut into
polynomial-time steps: from a family deciding 3-SAT with every exponent, the reduction decides k-SAT
with any exponent δ > 0. -/
alias PaperIndex.ethAndSethFail.SplitSat.stImplication := SplitSat.stImplication

/-- A step of the proof of Corollary 5: k ≥ 3: if sparsifying leaves ≤ 2^{δn/3} formulas of ≤ B·n
clauses and 3-SAT is decided with exponent δ₃, δ₃(1+(k−3)B) ≤ δ/3, then sparsifying and splitting
long clauses decides k-SAT with exponent δ. -/
alias PaperIndex.ethAndSethFail.SplitSat.stReduce := SplitSat.stReduce

/-- A step of the proof of Corollary 5: if the tree at width k has at most 2^{δn/3} leaves of at
most B·n clauses and a procedure decides 3-SAT with δ₃(1+(k−3)B) ≤ δ/3, the reduction decides k-SAT
with the exponent δ. -/
alias PaperIndex.ethAndSethFail.SplitSat.stReduceCore := SplitSat.stReduceCore

/-- A step of the proof of Corollary 5: not in the paper, which fixes no code of a formula: a code
of formulas that does not depend on k can be turned back into the formula in polynomial time. -/
alias PaperIndex.ethAndSethFail.FreeCode.stReader := FreeCode.stReader

/-- A step of the proof of Corollary 5: not in the paper: the code that does not depend on k of a
k-CNF on n variables has length at most a·(n+2)^d, with a and d depending only on k. -/
alias PaperIndex.ethAndSethFail.FreeCode.stLength := FreeCode.stLength

/-- A step of the proof of Corollary 5: a procedure that decides w-SAT on (N in unary, formula) with
the exponent δ does so within the same number of steps on the code that does not depend on k, after
any map turning it back into the formula. -/
alias PaperIndex.ethAndSethFail.FreeCode.stBehindReader := FreeCode.stBehindReader

/-- A step of the proof of Corollary 5: for every level and threshold, the machine of Theorem 2
first turns the code of its input into the formula and then works on that formula. -/
alias PaperIndex.ethAndSethFail.FromPrinted.SplitSat.stCore3Eq := FromPrinted.SplitSat.stCore3Eq

/-- A step of the proof of Corollary 5: «Theorem 2 gives s_3 = 0», for the machine of Theorem 2 in
its decision form after its input is turned into the formula: for every δ > 0 some level and
threshold make it decide 3-SAT with the exponent δ. -/
alias PaperIndex.ethAndSethFail.FromPrinted.SplitSat.stCore3 := FromPrinted.SplitSat.stCore3

/-- A step of the proof of Corollary 5: for every k ≥ 3 and δ > 0 and some parameters, the reduction
(sparsify, split long clauses, ask the machine of Theorem 2) has polynomial-time steps and decides
k-SAT with the exponent δ. -/
alias PaperIndex.ethAndSethFail.FromPrinted.SplitSat.stSATsplit := FromPrinted.SplitSat.stSATsplit

/-- A step of the proof of Corollary 5: for k ≥ 3 and δ > 0 the reduction to the machine of Theorem
2, for some parameters, decides k-SAT with the exponent δ, and a Turing machine of Mathlib
simulating it does so within ⌊c·2^{δn}⌋ steps. -/
alias PaperIndex.ethAndSethFail.FromPrinted.SplitSat.stTiedTM := FromPrinted.SplitSat.stTiedTM

/-- A step of the proof of Corollary 5: «Theorem 2 gives s_3=0» for its machine: for δ > 0, the
deciding form of procedure #Sat of Algorithm 1 decides 3-SAT with the exponent δ, and a Turing
machine of Mathlib simulating it does so within ⌊c·2^{δn}⌋ steps. -/
alias PaperIndex.ethAndSethFail.FromPrinted.SplitSat.stTiedThreeTM := FromPrinted.SplitSat.stTiedThreeTM

/-- A step of the proof of Corollary 5: Corollary 5 from two hypotheses: Turing machines simulating
the machine of Theorem 2 (k = 3) and the reduction (k > 3) decide k-SAT within ⌊c·2^{δn}⌋ steps for
every δ > 0. -/
alias PaperIndex.ethAndSethFail.FromPrinted.SplitSat.endFrom := FromPrinted.SplitSat.endFrom

/-- A step of the proof of Corollary 5: «Theorem 2 gives s_3=0» for the code that does not depend on
k: for δ > 0, its machine after a polynomial-time decoding, simulated by a Turing machine, decides
3-SAT within ⌊c·2^{δn}⌋ steps. -/
alias PaperIndex.ethAndSethFail.FromPrinted.FreeCode.stTiedThree := FromPrinted.FreeCode.stTiedThree

/-- A step of the proof of Corollary 5: for the code that does not depend on k, k ≥ 3 and δ > 0: the
reduction to the machine of Theorem 2 after a polynomial-time decoding, simulated by a Turing
machine, decides k-SAT within ⌊c·2^{δn}⌋ steps. -/
alias PaperIndex.ethAndSethFail.FromPrinted.FreeCode.stTied := FromPrinted.FreeCode.stTied

/-- A step of the proof of Corollary 5: Corollary 5 for the code that does not depend on k, from two
hypotheses: Turing machines simulating the machine of Theorem 2 (k = 3) and the reduction (k > 3)
decide k-SAT within ⌊c·2^{δn}⌋ steps. -/
alias PaperIndex.ethAndSethFail.FromPrinted.FreeCode.allZeroFrom := FromPrinted.FreeCode.allZeroFrom

/-- A step of the proof of Corollary 5: for k ≥ 3 and δ > 0, from the reduction to the machine of
Theorem 2: a machine that ignores its witness recognizes the tautologies among k-DNFs on n variables
within c·2^{δn} steps. -/
alias PaperIndex.ethAndSethFail.FromPrinted.Consequences.stVerifier := FromPrinted.Consequences.stVerifier

/-- A step of the proof of Corollary 5: for 1 ≤ k ≤ 3 and δ > 0 some procedure with polynomial-time
steps decides k-SAT with the exponent δ (the small widths in the statement on NSETH). -/
alias PaperIndex.ethAndSethFail.FromPrinted.Consequences.stSmallWidths := FromPrinted.Consequences.stSmallWidths

/-- A step of the proof of Corollary 5: NSETH, in verifier form on Turing machines of Mathlib, is
false if procedures decide k-SAT with every exponent for k ≤ 3 and the verifier on the reduction
recognizes k-DNF tautologies for k > 3. -/
alias PaperIndex.ethAndSethFail.FromPrinted.Consequences.nsethFrom := FromPrinted.Consequences.nsethFrom

/-- A step of the proof of Corollary 5: «Theorem 2 gives s_3 = 0», for machines cut into
polynomial-time steps: a family of procedures deciding 3-SAT, one for each exponent, each the
machine of Theorem 2 in its decision form at some level and threshold. -/
alias PaperIndex.ethAndSethFail.PrintedOrder.stThreeSatFamily := PrintedOrder.stThreeSatFamily

/-- A step of the proof of Corollary 5: for every family of procedures deciding 3-SAT with every
exponent, every k ≥ 3 and δ > 0: a Turing machine simulating the reduction decides k-SAT within
⌊c·2^{δn}⌋ steps. -/
alias PaperIndex.ethAndSethFail.PrintedOrder.stHosted := PrintedOrder.stHosted

/-- A step of the proof of Corollary 5: Corollary 5 in the printed order, from three hypotheses: a
family of procedures for 3-SAT from Theorem 2, the implication to k-SAT on Turing machines, and a
Turing machine for 3-SAT. -/
alias PaperIndex.ethAndSethFail.PrintedOrder.endThroughImplication := PrintedOrder.endThroughImplication

/-- A step of the proof of Corollary 5: from «s_3=0 implies s_k=0 for every k≥3» for machines cut
into polynomial-time steps: for every family deciding 3-SAT with every exponent, a simulating Turing
machine decides k-SAT within ⌊c·2^{δn}⌋ steps. -/
alias PaperIndex.ethAndSethFail.PrintedOrder.hostedFrom := PrintedOrder.hostedFrom

/-! ## Section 7, a passage without a number -/

/-- **Section 7** (the paragraph on E^NP: E^NP does not have linear-size circuits). In Lean: E^NP is
defined by Mathlib's multi-stack Turing machines that may ask an oracle for CNF satisfiability, one
step per query, within 2^{c(n+1)} steps; the statement joins this form, a form with an ordinary
machine restarted after each answer, and a form where circuits of c(n+1) gates, each any function of
two bits, fail at infinitely many lengths; the paper derives it from «ETH is false» by a cited
theorem of Williams, which is not in Lean: Lean proves the conclusion directly, following Williams's
argument. -/
alias PaperIndex.circuits := FromPrinted.Consequences.circuits

/-- For this passage of Section 7: the algorithm that the Lean proof uses (the printed proof cites
it): for every δ>0 a procedure in polynomial-time steps tells within c·2^{δN} steps whether the
formula made from the input is unsatisfiable. -/
alias PaperIndex.circuits.FromPrinted.Consequences.stAlgoRuns := FromPrinted.Consequences.stAlgoRuns

/-- For this passage of Section 7: if Corollary 6 holds for a family of machines cut into
polynomial-time steps, then E^NP does not have linear-size circuits, in three Lean forms. -/
alias PaperIndex.circuits.FromPrinted.Consequences.circuitsFrom := FromPrinted.Consequences.circuitsFrom

/-! ## Corollary 6, Section 7 -/

/-- **Corollary 6** (for every k ≥ 3 and δ > 0 a deterministic algorithm counts the satisfying
assignments of a k-CNF on n variables in time O(2^{δn}); at k = 3, its first half is Theorem 2 as
printed). In Lean: the algorithm is a deterministic multi-stack Turing machine of Mathlib, on a code
of formulas with n in unary and k slots per clause, and time is counted in its steps, not in
word-RAM operations; #ETH is stated for such machines; the cited results of Dell et al. are replaced
by proofs in Lean for procedures made of polynomial-time steps. At k = 3 the first half of this
statement is the sentence of Theorem 2 as printed. The proof is not the printed one: the paper takes
the case k = 3 from Theorem 2 and reduces every k to it; Lean does not go through a counting Theorem
2: it runs one search tree at width k, splits long clauses at every leaf, and counts each leaf with
procedure Count of Algorithm 1, whose bound is in the number of clauses, with the number of groups
taken from a level of Algorithm 1 and not from e* = 0. -/
alias PaperIndex.counting := FromPrinted.SplitCount.countingCorollary

/-- Corollary 6: the same, by a proof that adds up the counts because, as printed, no two formulas
of the sparsification share a satisfying assignment. In Lean: the algorithm is a deterministic
multi-stack Turing machine of Mathlib and time is counted in its steps, not in operations of a word
RAM; the sparsification for counting is proved in Lean with thresholds of its own, in place of the
cited lemma of Dell et al. The proof sparsifies at width k and adds up the counts because no two of
the formulas share a satisfying assignment. The paper takes the case k = 3 from Theorem 2 and
reduces every k to it; Lean also reduces every k to width 3, but then counts each formula with Count
and does not apply Theorem 2. It also differs from the printed proof in two more ways: the number K
of groups and the clique algorithm come from a level of Algorithm 1, not from any K that e* = 0
provides; and each leaf, after its long clauses are split as in the printed proof, is counted by
another Lean form of procedure Count, not by the one that follows Algorithm 1 line by line, and is
not sparsified a second time. -/
alias PaperIndex.countingInThePrintedOrder := PrintedOrder.countingCorollary

/-- A step of the proof of Corollary 6: at most n variables occur in a formula whose variables are
among x₀, …, x_{n−1}. -/
alias PaperIndex.counting.Occ.stNumOccLe := Occ.stNumOccLe

/-- A step of the proof of Corollary 6: the number v of variables that occur, and the number Z of
their assignments that satisfy the formula, are the same whether its variables are read in {0,…,N−1}
or as natural numbers. -/
alias PaperIndex.counting.Occ.stSameAsFin := Occ.stSameAsFin

/-- A step of the proof of Corollary 6: Z·2^{n′}: a formula on x₀, …, x_{n−1} in which v variables
occur and n′ = n − v do not has Z·2^{n′} satisfying assignments, Z the number of satisfying
assignments of the v variables that occur. -/
alias PaperIndex.counting.Occ.stCountOcc := Occ.stCountOcc

/-- A step of the proof of Corollary 6: «with no clauses the number is 2^n»: the formula without
clauses has 2^n satisfying assignments of x₀, …, x_{n−1}. -/
alias PaperIndex.counting.Occ.stCountNil := Occ.stCountNil

/-- A step of the proof of Corollary 6: if each of x₀, …, x_{n−1} occurs in the formula, and no
other variable does, its number of satisfying assignments is Z, the number of satisfying assignments
of the variables that occur. -/
alias PaperIndex.counting.Occ.stCountAllOccur := Occ.stCountAllOccur

/-- A step of the proof of Corollary 6: the number of variables that occur in a formula, written in
unary, is computed from the formula in polynomial time. -/
alias PaperIndex.counting.Occ.stNumOccCert := Occ.stNumOccCert

/-- A step of the proof of Corollary 6: from n in unary, the formula and Z, the number Z·2^{n−v} is
computed in polynomial time, where v is the number of variables that occur. -/
alias PaperIndex.counting.Occ.stTimesFreeCert := Occ.stTimesFreeCert

/-- A step of the proof of Corollary 6: multiplying a computed Z by 2^{n−v}, and running a counting
procedure on each output of the sparsification, keep the steps polynomial-time if those of the given
procedures are. -/
alias PaperIndex.counting.SplitCount.stCert := SplitCount.stCert

/-- A step of the proof of Corollary 6: «no two of which share a satisfying assignment», at one node
of the sparsification: an assignment satisfies the node exactly if it satisfies one of its two
children, and never both. -/
alias PaperIndex.counting.SplitCount.stDisjoint := SplitCount.stDisjoint

/-- A step of the proof of Corollary 6: «no two of which share a satisfying assignment»: no
assignment satisfies the formulas of two different leaves of the sparsification tree below a node,
cut at any depth. -/
alias PaperIndex.counting.SplitCount.stDisjointLeaves := SplitCount.stDisjointLeaves

/-- A step of the proof of Corollary 6: if a procedure computes Z as in Section 6 with an exponent
δ′ ≥ 0, then multiplying its result by 2^{n'} counts as the first sentence of the proof says, with
the same δ′. -/
alias PaperIndex.counting.SplitCount.stStepOneFor := SplitCount.stStepOneFor

/-- A step of the proof of Corollary 6: the reduction of Dell et al.: if a procedure counts as in
the first sentence of the proof with δ′ small enough for δ, then sparsifying, reducing the width and
counting gives #k-SAT in time O(2^{δn}). -/
alias PaperIndex.counting.SplitCount.stSuffices := SplitCount.stSuffices

/-- A step of the proof of Corollary 6: for every k and ε > 0 some thresholds make the
sparsification give at most 2^{εn} k-CNFs on the same variables, each with O(n) clauses, whose
numbers of satisfying assignments add up. -/
alias PaperIndex.counting.SplitCount.stStepTwo := SplitCount.stStepTwo

/-- A step of the proof of Corollary 6: the width reduction: m clauses of at most w literals on n
variables become a 3-CNF without repeated clauses on at most n+(w−3)m variables, with at most
m+3(w−3)m clauses and the same count. -/
alias PaperIndex.counting.SplitCount.stStepThree := SplitCount.stStepThree

/-- A step of the proof of Corollary 6: if 0<δ′≤1, 2≤K, K≥72/δ′ and a clique algorithm meets
Definition 4's bound for (K, δ′/12) and a memory bound, the algorithm of Lemma 1's proof with it
computes Z of Φ's network on 3K⁸ clusters in A·2^{δ′m} steps. -/
alias PaperIndex.counting.FromPrinted.SplitCount.stComputesZ := FromPrinted.SplitCount.stComputesZ

/-- A step of the proof of Corollary 6: Count of Algorithm 1 at level ℓ is line 6 followed by the
algorithm of Lemma 1 for K = K_ℓ with Clique at level ℓ, run on the network of Φ on g_ℓ = 3K_ℓ⁸
clusters. -/
alias PaperIndex.counting.FromPrinted.SplitCount.stCountIsNetworkMachine := FromPrinted.SplitCount.stCountIsNetworkMachine

/-- A step of the proof of Corollary 6: for 0 < δ′ ≤ 1 and every level ℓ with K_ℓ ≥ 72/δ′ and e_ℓ ≤
δ′/12, Count of Algorithm 1 at level ℓ, its result times 2^{n'}, counts as the first sentence of the
proof says. -/
alias PaperIndex.counting.FromPrinted.SplitCount.stStepOne := FromPrinted.SplitCount.stStepOne

/-- A step of the proof of Corollary 6: if a counting sparsification with ε = δ/3 leaves at most
Bl·n clauses, then for δ′ fixed by δ, k, Bl and a level ℓ with K_ℓ ≥ 72/δ′, e_ℓ ≤ δ′/12, it and
Count of Algorithm 1 count k-CNFs in time O(2^{δn}). -/
alias PaperIndex.counting.FromPrinted.SplitCount.stCountsAt := FromPrinted.SplitCount.stCountsAt

/-- A step of the proof of Corollary 6: if a counting sparsification with ε = δ/3 is given, K ≥ 2, K
≥ 72/δ′ and a clique algorithm meets Definition 4 for (K, δ′/12), then with Lemma 1 they count
k-CNFs in time O(2^{δn}). -/
alias PaperIndex.counting.FromPrinted.SplitCount.stCountsWithAnyCliqueAlgorithm := FromPrinted.SplitCount.stCountsWithAnyCliqueAlgorithm

/-- A step of the proof of Corollary 6: for every k ≥ 1 and δ > 0 some level and thresholds give a
procedure built from Algorithm 1, with polynomial-time steps, that counts the satisfying assignments
of k-CNFs in time O(2^{δn}). -/
alias PaperIndex.counting.FromPrinted.SplitCount.stEngineCounts := FromPrinted.SplitCount.stEngineCounts

/-- A step of the proof of Corollary 6: for every k ≥ 1 and δ > 0 some procedure built from
Algorithm 1, with polynomial-time steps, writes the count of a k-CNF on n variables in n+1 bits
within c·2^{δn} steps, in polynomial memory. -/
alias PaperIndex.counting.FromPrinted.SplitCount.stCOUNTsplitCounts := FromPrinted.SplitCount.stCOUNTsplitCounts

/-- A step of the proof of Corollary 6: for k ≥ 1, δ > 0: a procedure built from Algorithm 1 with
polynomial-time steps counts satisfying assignments of a k-CNF on n variables in c·2^{δn} steps; so
does a Mathlib Turing machine simulating it. -/
alias PaperIndex.counting.FromPrinted.SplitCount.stTiedTM := FromPrinted.SplitCount.stTiedTM

/-- A step of the proof of Corollary 6: if for every k ≥ 1 and δ > 0 a Mathlib Turing machine
simulating a procedure built from Algorithm 1 counts k-CNFs within ⌊c·2^{δn}⌋ steps, then Corollary
6 holds for such machines. -/
alias PaperIndex.counting.FromPrinted.SplitCount.endFrom := FromPrinted.SplitCount.endFrom

/-- A step of the proof of Corollary 6: if no assignment satisfies two formulas of a list, and an
assignment satisfies a formula exactly if it satisfies one of the list, then their numbers of
satisfying assignments on n variables add up to its number. -/
alias PaperIndex.counting.PrintedOrder.stAddUp := PrintedOrder.stAddUp

/-- A step of the proof of Corollary 6: from two hypotheses, that the counts of the leaves of the
sparsification tree add up to that of the input and the bounds on the tree: the counting form of the
Sparsification Lemma that the proof uses. -/
alias PaperIndex.counting.PrintedOrder.stepTwoFrom := PrintedOrder.stepTwoFrom

/-- A step of the proof of Corollary 6: if the counting sparsification holds, then for k ≥ 1, δ > 0
a procedure built from Algorithm 1 counts k-CNFs within c·2^{δn} steps, and so does a Mathlib Turing
machine simulating it, within ⌊c·2^{δn}⌋. -/
alias PaperIndex.counting.PrintedOrder.tiedFrom := PrintedOrder.tiedFrom

/-- A step of the proof of Corollary 6: line 6 of Algorithm 1, «if m=0 then return 1»: if a
procedure computes Z as in Section 6 with an exponent δ′, then so does that procedure preceded by
this line, with the same δ′. -/
alias PaperIndex.counting.FromPrinted.SplitCount.stFirstLine := FromPrinted.SplitCount.stFirstLine

/-- A step of the proof of Corollary 6: an assignment satisfies the formula of a node of the
sparsification tree for counting exactly if it satisfies the formula of some leaf below it, cut at
any depth. -/
alias PaperIndex.counting.PrintedOrder.stCovered := PrintedOrder.stCovered

/-- A step of the proof of Corollary 6: the formula at the root of the sparsification tree, with the
set 𝒩 of Appendix C empty, has the satisfying assignments of the input. -/
alias PaperIndex.counting.PrintedOrder.stRootSame := PrintedOrder.stRootSame

/-- A step of the proof of Corollary 6: the numbers of satisfying assignments of the leaves of the
sparsification tree add up to that of the input, for all thresholds, every width and every depth of
the cut. -/
alias PaperIndex.counting.PrintedOrder.stTreeAddsUp := PrintedOrder.stTreeAddsUp

/-- A step of the proof of Corollary 6: «at most 2^{εn} k-CNFs on the same variables, each with O(n)
clauses»: for every k ≥ 2 and ε > 0 some thresholds give a sparsification tree with these bounds
(for k = 1 the leaves have clauses of at most 2 literals). -/
alias PaperIndex.counting.PrintedOrder.stBounds := PrintedOrder.stBounds

/-- A step of the proof of Corollary 6: the number of satisfying assignments of a node of the
sparsification tree is the sum of those of its two children. -/
alias PaperIndex.counting.PrintedOrder.stStepAdds := PrintedOrder.stStepAdds

/-- A step of the proof of Corollary 6: if no two leaves share a satisfying assignment, each node
has exactly those of the leaves below it, the root has those of the input and such covers add up,
then the leaves' counts add up to the input's. -/
alias PaperIndex.counting.PrintedOrder.treeAddsUpFrom := PrintedOrder.treeAddsUpFrom

/-- A step of the proof of Corollary 6: if the two children of a node share no satisfying assignment
and together have those of the node, and such covers add up, then the count of a node is the sum of
those of its children. -/
alias PaperIndex.counting.PrintedOrder.stepAddsFrom := PrintedOrder.stepAddsFrom

/-- A step of the proof of Corollary 6: from the sum at one step of the tree as a hypothesis: for
every k and ε > 0 some thresholds give a sparsification tree with at most 2^{εn} leaves, each with
O(n) clauses. -/
alias PaperIndex.counting.PrintedOrder.boundsFrom := PrintedOrder.boundsFrom

/-! ## Corollary 7, Section 7 -/

/-- **Corollary 7** (the independent sets, cliques, vertex covers and dominating sets of a given
size and the proper k-colorings of a graph on n vertices are counted in time O(2^{δn})). In Lean:
the algorithms are multi-stack Turing machines of Mathlib with finite alphabets, and time is counted
in their steps; the size s ranges over 0 ≤ s ≤ n, where the paper allows any integer s; the counts
follow the printed proof except for dominating sets, where the formula Γ is joined at each leaf of
the shortening tree rather than before the shortening; the five decisions are read off the counts,
where the printed proof takes four of them from prior work. -/
alias PaperIndex.graphs := FromPrinted.Consequences.graphsByCounting

/-- Corollary 7: the first lines of its proof: the five decision problems from 3-SAT alone. In Lean:
the five problems are decided by multi-stack Turing machines of Mathlib, with time counted in their
steps, for sizes s with 0 ≤ s ≤ n; that the deciders use only an algorithm for 3-SAT, as the first
lines of the proof (for Independent Set, Clique, Vertex Cover and k-Coloring, by cited reductions)
and the remark after it (for Dominating Set) say, holds of the machines built in the proof and is
not part of the statement. -/
alias PaperIndex.graphsFromThreeSatAlone := FromPrinted.Sat3Graph.decideFromThreeSat

/-- A step of the proof of Corollary 7: if circuits test |S|=s with at most a·(n+1) gates and n ≥ 1,
then Γ is a 3-CNF on ≤ (a+1)(n+1) variables with ≤ 4a(n+1)+1 clauses, and each S of size s has
exactly one satisfying extension, no other S any. -/
alias PaperIndex.graphs.SizeCircuit.stGamma := SizeCircuit.stGamma

/-- A step of the proof of Corollary 7: if circuits test |S|=s with at most a·(n+1) gates, a formula
ψ on x₀,…,xₙ₋₁ together with Γ has as many satisfying assignments as ψ has with exactly s true
variables, for every n ≥ 0. -/
alias PaperIndex.graphs.SizeCircuit.stGammaCount := SizeCircuit.stGammaCount

/-- A step of the proof of Corollary 7: «clauses of at most 3 literals that force it to equal the
value of the gate»: the four clauses of a gate hold exactly if its variable has the value of the
gate, each with at most 3 literals. -/
alias PaperIndex.graphs.SizeCircuit.stForces := SizeCircuit.stForces

/-- A step of the proof of Corollary 7: for a nonempty circuit whose gates read earlier wires only,
every assignment of its n inputs extends uniquely so that the clauses of all gates hold, and the
last gate's variable then has the circuit's value. -/
alias PaperIndex.graphs.SizeCircuit.stUniqueExtension := SizeCircuit.stUniqueExtension

/-- A step of the proof of Corollary 7: a family of circuits given in the development tests whether |S|=s
with at most a·(n+1) gates, for some constant a, and is computed from n and s in polynomial time. -/
alias PaperIndex.graphs.SizeCircuit.stSizeGates := SizeCircuit.stSizeGates

/-- A step of the proof of Corollary 7: «a circuit with O(n) gates of two inputs tests whether |S|=s»:
some family of such circuits, with at most a·(n+1) gates, is computed in polynomial time. -/
alias PaperIndex.graphs.SizeCircuit.stCircuitExists := SizeCircuit.stCircuitExists

/-- A step of the proof of Corollary 7: if Corollary 6 holds for machines cut into polynomial-time
steps, a #max(w,3)-SAT procedure of exponent ≤ δ/(a+1), run on ψ with Γ, counts the assignments of ψ
with s ones in c'·2^{δn} steps. -/
alias PaperIndex.graphs.SizeCircuit.stSizedFromEngine := SizeCircuit.stSizedFromEngine

/-- A step of the proof of Corollary 7: for every family of #k-SAT procedures of which Corollary 6
holds, size circuits and δ > 0: some member, run on ψ with Γ beside it, counts ψ's satisfying
assignments with s true variables in c'·2^{δn} steps. -/
alias PaperIndex.graphs.SizeCircuit.stSizedFromEngines := SizeCircuit.stSizedFromEngines

/-- A step of the proof of Corollary 7: if Corollary 6 holds for machines cut into polynomial-time
steps, then for every width w and δ > 0 some machine counts the assignments with s true variables
satisfying a width-w formula within c·2^{δn} steps. -/
alias PaperIndex.graphs.SizeCircuit.stSizedViaGamma := SizeCircuit.stSizedViaGamma

/-- A step of the proof of Corollary 7: if circuits test |S|=s with ≤ a·(n+1) gates and E counts for #max(w,3)-SAT
with exponent δ_E(a+1) ≤ δ, then E run on ψ with Γ counts ψ's satisfying assignments with s true
variables in c'·2^{δn} steps. -/
alias PaperIndex.graphs.SizeCircuit.stSizedBy := SizeCircuit.stSizedBy

/-- A step of the proof of Corollary 7: running E on ψ with Γ beside it has polynomial-time steps if
E has them and the size circuits are computed in polynomial time. -/
alias PaperIndex.graphs.SizeCircuit.stSizedCert := SizeCircuit.stSizedCert

/-- A step of the proof of Corollary 7: if circuits of ≤ a·(n+1) gates test |S| = s and a #3-SAT
procedure has exponent δ_E with δ_E(a+1) ≤ δ, it counts via Γ the independent sets, cliques and
vertex covers of size s ≤ n in c′·2^{δn} steps. -/
alias PaperIndex.graphs.Complement.stFromGamma := Complement.stFromGamma

/-- A step of the proof of Corollary 7: if for all δ > 0 the assignments with s true variables
satisfying a formula of any width are counted in c·2^{δn} steps, Turing machines count cliques and
vertex covers of size s and decide both problems in time O(2^{δn}). -/
alias PaperIndex.graphs.Complement.stOnTuringMachines := Complement.stOnTuringMachines

/-- A step of the proof of Corollary 7: the formula with the clause {¬x_u, ¬x_v} for each edge uv is
computed in polynomial time from n and the adjacency matrix, has at most 2 literals per clause,
variables below n and at most n² clauses. -/
alias PaperIndex.graphs.Complement.stIndepAlone := Complement.stIndepAlone

/-- A step of the proof of Corollary 7: the adjacency matrix of the complement graph is computed in
polynomial time from n and the adjacency matrix. -/
alias PaperIndex.graphs.Complement.stComplCert := Complement.stComplCert

/-- A step of the proof of Corollary 7: the two maps that turn a graph and s into the formula for
its cliques and for its vertex covers run in polynomial time. -/
alias PaperIndex.graphs.Complement.stReadersCert := Complement.stReadersCert

/-- A step of the proof of Corollary 7: for s ≤ n, (G, s) is turned into the formula for independent
sets of the complement with s, resp. of G with n − s; its satisfying assignments with that many true
variables count the cliques, resp. vertex covers, of size s. -/
alias PaperIndex.graphs.Complement.stReaders := Complement.stReaders

/-- A step of the proof of Corollary 7: if a machine counts the satisfying assignments with s true
variables of 2-CNFs in c·2^{δn} steps, then, run on the formulas for cliques and vertex covers, it
counts those of size s ≤ n in as many steps. -/
alias PaperIndex.graphs.Complement.stCounts := Complement.stCounts

/-- A step of the proof of Corollary 7: if for all widths and δ > 0 the satisfying assignments with
s true variables are counted in c·2^{δn} steps, then for every δ > 0 one machine, run on the
formulas for cliques and vertex covers, counts those of size s ≤ n in c·2^{δn} steps. -/
alias PaperIndex.graphs.Complement.stFromSized := Complement.stFromSized

/-- A step of the proof of Corollary 7: if E run on ψ with Γ beside it counts ψ's satisfying
assignments with s true variables, then on the formulas of a graph it counts its independent sets,
cliques and vertex covers of size s ≤ n in c'·2^{δn} steps. -/
alias PaperIndex.graphs.Complement.stFromGamma_of := Complement.stFromGamma_of

/-- A step of the proof of Corollary 7: «The cliques of size s are the independent sets of size s of
the complement graph», hence their numbers agree. -/
alias PaperIndex.graphs.Complement.stCliques := Complement.stCliques

/-- A step of the proof of Corollary 7: for s ≤ n, «the vertex covers of size s are the complements
of the independent sets of size n−s», hence their numbers agree. -/
alias PaperIndex.graphs.Complement.stCovers := Complement.stCovers

/-- A step of the proof of Corollary 7: the map on adjacency matrices turns the matrix of G into the
matrix of the complement graph. -/
alias PaperIndex.graphs.Complement.stComplMatrix := Complement.stComplMatrix

/-- A step of the proof of Corollary 7: if D decides 3-SAT with exponent δ₃ ≥ 0, the circuits for |S| =
s have ≤ a(n+1) gates and δ₃(a+1+B) ≤ δ, a machine built from them says in c′2^{δn} steps whether a
w-CNF on n variables with m clauses, (w−3)m ≤ B(n+1), has a satisfying assignment with s true
variables. -/
alias PaperIndex.graphs.Sat3Graph.stAskSized := Sat3Graph.stAskSized

/-- A step of the proof of Corollary 7: if the maps from a graph to the formulas for independent
sets, cliques and vertex covers run in polynomial time, the five deciders from 3-SAT have
polynomial-time steps whenever the 3-SAT procedure and size circuits do. -/
alias PaperIndex.graphs.Sat3Graph.stCert_of := Sat3Graph.stCert_of

/-- A step of the proof of Corollary 7: for k ≥ 3, if D decides 3-SAT with exponent δ₃ ≥ 0 and
δ₃(2k−3) ≤ δ, a machine built from D decides within c'·2^{δn} steps whether a graph on n vertices
has a proper coloring with k colors. -/
alias PaperIndex.graphs.Sat3Graph.stColoring := Sat3Graph.stColoring

/-- A step of the proof of Corollary 7: if the tree shortening clauses to w literals has ≤ 2^{δn/2}
leaves and D decides 3-SAT with exponent δ₃, δ₃(a+1+3(w−3)) ≤ δ/2, a machine built from D and Γ
decides Dominating Set in c'·2^{δn} steps. -/
alias PaperIndex.graphs.Sat3Graph.stDominating := Sat3Graph.stDominating

/-- A step of the proof of Corollary 7: if D decides 3-SAT with exponent δ₃ ≥ 0 and δ₃(a+1) ≤ δ, Γ
having ≤ a·(n+1) gates, machines built from D and Γ decide Independent Set, Clique and Vertex Cover
within c'·2^{δn} steps. -/
alias PaperIndex.graphs.Sat3Graph.stSets := Sat3Graph.stSets

/-- A step of the proof of Corollary 7: the deciders from 3-SAT for Independent Set, Clique, Vertex
Cover, Dominating Set and k-Coloring have polynomial-time steps if the 3-SAT procedure and the size
circuits do. -/
alias PaperIndex.graphs.Sat3Graph.stCert := Sat3Graph.stCert

/-- A step of the proof of Corollary 7: from the formulas for cliques and vertex covers and the
width 2 of that for independent sets: a 3-SAT procedure with δ₃(a+1) ≤ δ, Γ of ≤ a·(n+1) gates,
decides these three problems in c'·2^{δn} steps. -/
alias PaperIndex.graphs.Sat3Graph.stSets_of := Sat3Graph.stSets_of

/-- A step of the proof of Corollary 7: for every δ > 0 one machine built from Algorithm 1, with Γ
beside the formula, has polynomial-time steps and counts the independent sets, cliques and vertex
covers of size s within c·2^{δn} steps. -/
alias PaperIndex.graphs.FromPrinted.Consequences.stSetsCounted := FromPrinted.Consequences.stSetsCounted

/-- A step of the proof of Corollary 7: for k ≥ 3 and δ > 0 one machine built from Algorithm 1
counts the proper k-colorings of a graph on n vertices, through the k-CNF on kn variables, within
c·2^{δn} steps. -/
alias PaperIndex.graphs.FromPrinted.Consequences.stColoringsCounted := FromPrinted.Consequences.stColoringsCounted

/-- A step of the proof of Corollary 7: for δ > 0 some width w has a shortening tree with at most
2^{δn/2} leaves, and one machine built from Algorithm 1 counts the dominating sets of size s ≤ n
within c·2^{δn} steps. -/
alias PaperIndex.graphs.FromPrinted.Consequences.stDominatingCounted := FromPrinted.Consequences.stDominatingCounted

/-- A step of the proof of Corollary 7: both sentences of Corollary 7 on Turing machines, from the
statements that machines built from Algorithm 1 count independent sets, cliques, vertex covers,
dominating sets and k-colorings in c·2^{δn} steps. -/
alias PaperIndex.graphs.FromPrinted.Consequences.graphsFrom := FromPrinted.Consequences.graphsFrom

/-- A step of the proof of Corollary 7: for size circuits computed in polynomial time, δ > 0 and k ≥
3: with the machine of Theorem 2 as 3-SAT procedure, Independent Set, Clique, Vertex Cover,
Dominating Set and k-Coloring are decided in c·2^{δn} steps. -/
alias PaperIndex.graphs.FromPrinted.Sat3Graph.stWithThreeSatMachine := FromPrinted.Sat3Graph.stWithThreeSatMachine

/-- A step of the proof of Corollary 7: for δ > 0 and k ≥ 3, the five deciders built on the machine
of Theorem 2 have polynomial-time steps, decide their problems in c·2^{δn} steps, and are simulated
by Turing machines deciding in ⌊C·2^{δn}⌋ steps. -/
alias PaperIndex.graphs.FromPrinted.Sat3Graph.stTiedTM := FromPrinted.Sat3Graph.stTiedTM

/-- A step of the proof of Corollary 7: if Turing machines simulating the deciders built on the
machine of Theorem 2 decide the five problems in ⌊C·2^{δn}⌋ steps, then for δ > 0 and k ≥ 3 these
problems are decided by Turing machines in time O(2^{δn}). -/
alias PaperIndex.graphs.FromPrinted.Sat3Graph.endFrom := FromPrinted.Sat3Graph.endFrom

/-! ## Definition 7, Appendix A -/

/-- **Definition 7** (pieces with parameters (ρ, c)). In Lean: the algorithm is a machine that,
given λ in unary and a question, answers within 2^{cλ} steps, each of which may be any function
computable in time polynomial in the size of the state, on states of size at most
(2^{cλ}+(2λ)^c+8)·((2λ)^c+8), a bound the paper does not have. So a machine that writes 2^{cλ}
symbols and then does all its work in one step meets this clause, and the printed bound of 2^{cλ}
operations on words follows only with a larger c; the pieces of Appendix B (Theorem B) meet the
clause in exactly this way. Strings are lists of bits. -/
alias PaperIndex.generalPieces := PiecesCounted.IsPieces

/-- Beside Definition 7: from data that satisfy Definition 7: its clauses (a), (b) and the bounds on
sizes in (c) hold as pure mathematics for every λ ≥ 1, with the functions of the factorizations
taken from the data. -/
alias PaperIndex.generalPieces.PiecesCounted.toPure := PiecesCounted.toPure

/-- Beside Definition 7: pieces with parameters (ρ, c) are pieces with parameters (ρ′, c′) whenever
ρ ≤ ρ′ < 1 and c ≤ c′, with the same algorithm. -/
alias PaperIndex.generalPieces.PiecesCounted.growWithTheParameters := PiecesCounted.growWithTheParameters

/-- Beside Definition 7: pieces with parameters (ρ, c) give pieces with parameters (ρ, c+2) with the
same d, 𝓘 and A_i and with all numbers of bits c^row_i, c^col_i at most 2λ. -/
alias PaperIndex.generalPieces.PiecesCounted.mayAssume := PiecesCounted.mayAssume

/-- Beside Definition 7: by Lemma 2, the functions A_0, …, A_t of Definition 5 are pieces with
parameters (11/12, c) for every c from some c₀ ≥ 8 on, with one algorithm, 𝓘 = {0, …, t}, d = 2^t
and c^row_i + c^col_i ≤ 11λ/3 + 8. -/
alias PaperIndex.generalPieces.PiecesCounted.eightSquarePieces := PiecesCounted.eightSquarePieces

/-- Beside Definition 7 (c): if a machine that asks the pieces as an oracle, each query charged
about 2^{cλ} operations, answers within T operations, it still does so when the queries are answered
by running the algorithm of Definition 7 (c). -/
alias PaperIndex.generalPieces.PiecesCounted.oracleFromAlgorithm := PiecesCounted.oracleFromAlgorithm

/-- Beside Definition 7 (c): pieces whose programs get an extra input of 2^{cλ} ones are, for some
c′ ≥ c, pieces with one algorithm within 2^{c′λ} operations, also after any small shift of the index
set computed in polynomial time. -/
alias PaperIndex.generalPieces.PiecesCounted.fromPadded := PiecesCounted.fromPadded

/-! ## Lemma 8, Appendix A -/

/-- **Lemma 8** (the value of a network on [g] from an algorithm for (K, L)-cliques, with explicit
cost, by one procedure). In Lean: cost is counted in operations of a machine with query access, an
operation being a query or a step that may be any function of the whole state (that the steps take
polynomial time is a separate statement); the network is given by queries, each membership test or
value of W, Ψ, f costing τ operations. The states of the called algorithm are assumed to have size
at most some S_E, and those of the procedure have size at most S_E + (g(P+B) + size of ζ)^{C₁},
which the paper does not ask; the called algorithm is also given K; ζ must be a fraction a/b given
in the input; K, g, P, B and the network's numbers are in unary. The proof of the Main Theorem uses
only the part of this proof up to the call of the algorithm, not this statement. -/
alias PaperIndex.groupingExplicit := ExplicitCost.groupingExplicit

/-- A step of the proof of Lemma 8: the machine that computes the entries of the tables W̃_γ,
reading K and g from its input, takes polynomial time for each of its steps. -/
alias PaperIndex.groupingExplicit.ExplicitCost.entryPoly := ExplicitCost.entryPoly

/-- A step of the proof of Lemma 8: for each K and g, the machine for the entries of the tables W̃_γ
(proof of Lemma 1) that reads K and g from its input runs like the one built for these K and g: the
same result, steps and queries, on states larger by at most four copies of K and g in unary. -/
alias PaperIndex.groupingExplicit.ExplicitCost.entrySameRuns := ExplicitCost.entrySameRuns

/-- A step of the proof of Lemma 8: the string length and the bound on the entries that the
procedure computes are those of «Put L=⌈(U+2ζgP)/K²⌉ and B'=⌈2gP/K⌉+g²B». -/
alias PaperIndex.groupingExplicit.ExplicitCost.labelLengthIsL := ExplicitCost.labelLengthIsL

/-- A step of the proof of Lemma 8: in case (i) or (ii), the search through all K^g groupings finds
a first one that its test accepts, and it has at most 2g/K nodes in every group and Y_{γ,γ'} ≤ L for
all γ ≠ γ'. -/
alias PaperIndex.groupingExplicit.ExplicitCost.searchFinds := ExplicitCost.searchFinds

/-- A step of the proof of Lemma 8: the search for the first accepted grouping takes at most C·K^g
steps, a test being one step, on states of size polynomial in g(P+B) and the length of ζ, with one
constant C for all inputs. -/
alias PaperIndex.groupingExplicit.ExplicitCost.searchCost := ExplicitCost.searchCost

/-- A step of the proof of Lemma 8: the lemma up to the call of the clique algorithm follows from
the finding of the grouping, the cost of the search, the bounds on sizes, and the equality of the
value of the clique of the groups with that of the network. -/
alias PaperIndex.groupingExplicit.ExplicitCost.groupingWithCallFrom := ExplicitCost.groupingWithCallFrom

/-- A step of the proof of Lemma 8: with one constant C: if the call is answered by the value of the
(K, L)-clique of the groups of the first accepted grouping at a price t, the value of the network
comes within C·K^g + t operations. -/
alias PaperIndex.groupingExplicit.ExplicitCost.groupingWithCall := ExplicitCost.groupingWithCall

/-- A step of the proof of Lemma 8: the lemma follows from the lemma up to the call, the values of L
and B', the cost of an entry of W̃_γ, the bounds on sizes, and rules for answering the queries of a
machine by another machine. -/
alias PaperIndex.groupingExplicit.ExplicitCost.groupingExplicitFrom := ExplicitCost.groupingExplicitFrom

/-- A step of the proof of Lemma 8: each step of the procedure takes polynomial time, up to the
call, and as a whole if the called algorithm's steps do and its input is formed in polynomial time. -/
alias PaperIndex.groupingExplicit.ExplicitCost.groupingPoly := ExplicitCost.groupingPoly

/-- A step of the proof of Lemma 8: for a grouping with at most 2g/K nodes per group and Y_{γ,γ'} ≤
L ≤ 2gP, an entry of W̃_γ takes at most 2^{P⌊2g/K⌋}·τ·(g(P+B))^{c₁} operations, one c₁ for all, and
∣W̃_γ∣ < 2^{B'}. -/
alias PaperIndex.groupingExplicit.ExplicitCost.entryCostExplicit := ExplicitCost.entryCostExplicit

/-! ## Theorem A, Appendix A -/

/-- **Theorem A** (what pieces with parameters (ρ, c) give: the numbers K_ℓ and e_ℓ, one algorithm
for the cliques of all levels, and the running times for counting and for 3-SAT). In Lean: Theorem A (b)
and the hypothesis on the pieces (another form of Definition 7) measure time differently from the
paper: an algorithm is a polynomial-time program that is handed a string of blank symbols as its
budget of time and must be right once that string is as long as the bound, the tables being written
out, not queried; elsewhere time is counted in steps of a Turing machine. The first sentence of (c)
allows variables that do not occur but adds C·L^C, L the input length, to its bound in m; (d) is
proved from a stronger bound (exponent 3/19), without the pieces; the proof of the Main Theorem does
not use this statement. -/
alias PaperIndex.rate := FixedWidth.runningTimesFromPieces

/-- A step of the proof of Theorem A: Theorem A with the bound in m of Theorem A (c) plus a
polynomial in the input length, its bound for fixed k without the proviso and with one algorithm per
k, and Theorem A (d) from another bound. -/
alias PaperIndex.rate.ClausesOccur.runningTimesFromPieces := ClausesOccur.runningTimesFromPieces

/-- Theorem A (b): one algorithm with query access to the tables, given ℓ, λ and B, outputs the
value of the (K_ℓ, λ)-clique within 2^{e_ℓ·K_ℓ²·λ}·(K_ℓ(λ+B))^{C₀·K_ℓ²} operations, for every choice
of pieces. In Lean: an operation is a table query or a step that may be any polynomial-time function
of the whole state, and every state has size at most the bound; as such a state may be rewritten in
one step, the exponent e_ℓK_ℓ²λ holds for machine steps only up to a constant factor. The pieces are
assumed to have c^row_i, c^col_i ≤ 2λ, as the paper allows; their algorithm is counted in the same
operations, and the clique algorithm's steps are shown polynomial-time. -/
alias PaperIndex.cliquesOfAllLevelsInCountedOperations := ExplicitCost.recursionSolves

/-- A step of the proof of Theorem A (b): the number B′ of bits of the tables is at least 1 and
every entry is below 2^{B′} in absolute value; for tables whose entries are at most 2^B in absolute
value, B′ ≤ B + 1. -/
alias PaperIndex.rate.QueryMachines.Bridge.bitsOfTablesFacts := QueryMachines.Bridge.bitsOfTablesFacts

/-- A step of the proof of Theorem A (b): the number of operations allowed, 2 to a computed
exponent, is at least 4 times 2^{e′K_ℓ²λ}(K_ℓ(λ+B+1))^{C₀K_ℓ²}, the bound of Theorem A (b) with a
computed e′ for e_ℓ. -/
alias PaperIndex.rate.QueryMachines.Bridge.needSuffices := QueryMachines.Bridge.needSuffices

/-- A step of the proof of Theorem A (b): for e_ℓ ≥ 0, the form of the bound of Theorem A (b) in
which all states of the algorithm have size within its polynomial factor implies the form with sizes
within the whole bound. -/
alias PaperIndex.rate.CliqueLevels.solvesOfSolvesInFactor := CliqueLevels.solvesOfSolvesInFactor

/-- A step of the proof of Theorem A (b): a machine that may call itself, run with all its calls as
one machine whose state is the stack of activations, has polynomial-time steps if the machine has,
for all depths at once. -/
alias PaperIndex.rate.QueryMachines.Tower.selfCallPoly := QueryMachines.Tower.selfCallPoly

/-- A step of the proof of Theorem A (b): the machine that runs a clique algorithm with calls one
level down, the tables of each call computed from the caller's by a procedure, has polynomial-time
steps if both have them, for all depths. -/
alias PaperIndex.rate.QueryMachines.Tower.towerPoly := QueryMachines.Tower.towerPoly

/-- A step of the proof of Theorem A (b): if a machine returns its value within T operations when
each call of smaller depth is answered at the price T + 2, then run with all its calls it does so
too, on states of size at most (depth + 1)(S + 1) + 1. -/
alias PaperIndex.rate.QueryMachines.Tower.selfCallRuns := QueryMachines.Tower.selfCallRuns

/-- A step of the proof of Theorem A (b): the recursion on ℓ of Theorem A (b): if a clique algorithm
and the procedure computing the tables of its calls meet a specification, the two run together
return every value within the recursive cost. -/
alias PaperIndex.rate.QueryMachines.Tower.towerRuns := QueryMachines.Tower.towerRuns

/-- A step of the proof of Theorem A (b): the number T(ℓ, t) of operations at level ℓ when one query
to the tables costs t: if level ℓ+1 costs a operations of its own, b calls to level ℓ and q queries,
and an entry of a level-ℓ table costs a′ + q′·t, then T(ℓ+1, t) = a + b·(T(ℓ, a′+q′·t+2) + 2) + q·t. -/
alias PaperIndex.rate.QueryMachines.Tower.costShape := QueryMachines.Tower.costShape

/-- A step of the proof of Theorem A (b): whether the code word of a value is at most as long as a
given string of units is decided in polynomial time, for every coding. -/
alias PaperIndex.rate.QueryMachines.Bridge.everyWordIsCompared := QueryMachines.Bridge.everyWordIsCompared

/-- A step of the proof of Theorem A (b): running a machine for as many steps as a given string of
units is long, with room 7S + 2 for its states, returns its result if it halts within that many
steps on states of size at most S. -/
alias PaperIndex.rate.QueryMachines.Bridge.runForIsRight := QueryMachines.Bridge.runForIsRight

/-- A step of the proof of Theorem A (b): that running a machine for as many steps as a string of
units is long is polynomial-time follows from the polynomial-time comparison of code words with such
strings. -/
alias PaperIndex.rate.QueryMachines.Bridge.runForPolyFrom := QueryMachines.Bridge.runForPolyFrom

/-- A step of the proof of Theorem A (b): running a machine with polynomial-time steps for as many
steps as a string of units is long is polynomial-time; this is how a bound on the number of
operations is rendered in the Lean. -/
alias PaperIndex.rate.QueryMachines.Bridge.runForPoly := QueryMachines.Bridge.runForPoly

/-- A step of the proof of Theorem A (b): the computed exponent of the number of operations allowed
is at most e′K_ℓ²λ + (2C₀ + 1)·K_ℓ²·log(K_ℓ(λ + B)), with e′ the computed number. -/
alias PaperIndex.rate.QueryMachines.Bridge.needIsSmall := QueryMachines.Bridge.needIsSmall

/-- A step of the proof of Theorem A (b): that a machine with query access, run for as many
operations as a string of units is long, gives a polynomial-time function follows from the same fact
for running a machine for that many steps. -/
alias PaperIndex.rate.QueryMachines.Bridge.solverOfMachinePolyFrom := QueryMachines.Bridge.solverOfMachinePolyFrom

/-- A step of the proof of Theorem A (b): the function that a polynomial-time machine with query
access gives, run for as many operations as a string of units is long, is polynomial-time. -/
alias PaperIndex.rate.QueryMachines.Bridge.solverOfMachinePoly := QueryMachines.Bridge.solverOfMachinePoly

/-- A step of the proof of Theorem A (b): that a clique machine meeting the bound of Theorem A (b)
gives the Lean form of the hypothesis of Theorem D (a) (levels for a computed e′_ℓ, constant 2C₀+1,
level picked by a program) follows from facts on running machines, the tables, e′_ℓ, the exponent
and polynomial time. -/
alias PaperIndex.rate.QueryMachines.Bridge.solverOfMachineLevelsFrom := QueryMachines.Bridge.solverOfMachineLevelsFrom

/-- A step of the proof of Theorem A (b): for costs linear in the costs of calls and queries,
queries that cost x ≥ 1 times as much make the whole cost at most x times as much, so the cost of an
entry enters as a factor. -/
alias PaperIndex.rate.QueryMachines.Tower.costSlowDown := QueryMachines.Tower.costSlowDown

/-- A step of the proof of Theorem A (b): an example for the theorems on recursion: a machine that
sums a table by calls one level down has polynomial-time steps, the depth being part of its input. -/
alias PaperIndex.rate.QueryMachines.Tower.Toy.toyPoly := QueryMachines.Tower.Toy.toyPoly

/-- A step of the proof of Theorem A (b): an example: two machines that sum a table over bit strings
meet the specification of the general theorem on a recursion with calls one level down, whose depth
is part of the input (the form used in the proof of Theorem A (b)), so its hypotheses can be met. -/
alias PaperIndex.rate.QueryMachines.Tower.Toy.toyMeets := QueryMachines.Tower.Toy.toyMeets

/-- A step of the proof of Theorem A (b): an example: one machine, given ℓ and queries to a table at
t operations each, returns the sum of the table over all bit strings of length ℓ within 2^ℓ·(t + 2ℓ + 5)
operations. -/
alias PaperIndex.rate.QueryMachines.Tower.Toy.toyRuns := QueryMachines.Tower.Toy.toyRuns

/-- Theorem A (c): the first sentence of part (c), for the pieces of Appendix B only (α′ = 1/2): the
bound in the number of clauses. In Lean: stated only at α′ = ½ and without the hypothesis on pieces:
it says that some multi-stack Turing machine of Mathlib counts within the bound, time in its steps;
the machine of the proof is built from the pieces of Appendix B, and the proof is not the printed
one (see the head of this index). -/
alias PaperIndex.boundInTheNumberOfClauses := CountedRoute.boundInMHolds

/-- A step of the proof of Theorem A (c): for α = ½ the exponent km/(log m)^α is km/√(log m), the
exponent of the bound in m of Theorem 1, for all k and m. -/
alias PaperIndex.rate.ClausesOccur.expHalf := ClausesOccur.expHalf

/-- A step of the proof of Theorem A (c): a formula with at least two clauses, none written twice,
has at least one variable that occurs. -/
alias PaperIndex.rate.ClausesOccur.someVariableOccurs := ClausesOccur.someVariableOccurs

/-- A step of the proof of Theorem A (c): if a machine counts as Theorem A (c) says, but with any α
∈ [0,1] for α′, a polynomial in the input length added to the bound and the number of variable names
in unary in the input, then where all variables occur and m ≥ 2 it takes at most
C′·2^{C′km/(log(m+2))^α} steps. -/
alias PaperIndex.rate.ClausesOccur.allOccurOfUnary := ClausesOccur.allOccurOfUnary

/-- A step of the proof of Theorem A (c): the first sentence of Theorem A (c), if there are pieces
with parameters (ρ, c), in machine steps and with a term polynomial in the input length added to the
bound. -/
alias PaperIndex.rate.ClausesOccur.countsFromPieces := ClausesOccur.countsFromPieces

/-- A step of the proof of Theorem A (c): if there are pieces with parameters (ρ, c): Theorem A (c),
first sentence, in time 2^{O(km/(log m)^{α′})} plus a polynomial in the input length, with the
number of variable names in unary. -/
alias PaperIndex.rate.ClausesOccur.countsUnaryFromPieces := ClausesOccur.countsUnaryFromPieces

/-- A step of the proof of Theorem A (c): for every machine and every constant, the bound in m of
Theorem 1 is the bound of the first sentence of Theorem A (c) at α′ = ½. -/
alias PaperIndex.rate.ClausesOccur.boundInClausesIsHalf := ClausesOccur.boundInClausesIsHalf

/-- A step of the proof of Theorem A (c): from Theorem B and the first sentence of Theorem A (c)
follows the bound in m of Theorem 1, since α′ = log √2 = ½; both bounds with an added term C·L^C in
the input length L, which the paper's statements lack. -/
alias PaperIndex.rate.ClausesOccur.boundInClausesFrom := ClausesOccur.boundInClausesFrom

/-- A step of the proof of Theorem A (c): the bound in m of Theorem 1 for one machine, with a term
polynomial in the input length and without the hypothesis that n ≥ 4 variables occur. -/
alias PaperIndex.rate.ClausesOccur.boundInClauses := ClausesOccur.boundInClauses

/-- A step of the proof of Theorem A (c): two functions, one for the input with the names in binary
and one with their number in unary, rename the variables that occur, and both are computable in
polynomial time. -/
alias PaperIndex.rate.OccurM.preparation := OccurM.preparation

/-- A step of the proof of Theorem A (c): for any algorithm for cliques and 0 ≤ α ≤ 1: a bound
2^{O(km/(log m)^α)} on formulas in which every variable occurs carries over to all k-CNFs once the
variables that occur are renamed first. -/
alias PaperIndex.rate.OccurM.topOccurOfTop := OccurM.topOccurOfTop

/-- A step of the proof of Theorem A (c): the first sentence of Theorem A (c) for the algorithm of
its proof: renaming the variables that occur, then the recursion of Theorem A (b) on pieces with
parameters (ρ, c), meets the bound in m. -/
alias PaperIndex.rate.OccurM.countsFromPiecesTied := OccurM.countsFromPiecesTied

/-- A step of the proof of Theorem A (c): the bound in m of Theorem 1 for the algorithm of the proof
of Theorem A (c), run on some programs for the pieces of Appendix B (α′ = ½) with the least x₀ of
Theorem A. -/
alias PaperIndex.rate.OccurM.boundInClausesTied := OccurM.boundInClausesTied

/-- A step of the proof of Theorem A (c): from the first sentence of Theorem A (c) and the bound in
m of Theorem 1 for the algorithm of the proof to the same statements for some machine. -/
alias PaperIndex.rate.OccurM.untie := OccurM.untie

/-- A step of the proof of Theorem A (c): if a machine counts within C·2^{C·km/(log(m+2))^α} steps
on formulas in which every variable occurs, every machine that renames the variables that occur and
then runs it meets the first sentence of Theorem A (c). -/
alias PaperIndex.rate.OccurM.everyWrapperCounts := OccurM.everyWrapperCounts

/-- A step of the proof of Theorem A (c): N (the number of variable names) in unary in the input,
0≤α≤1: if a machine counts in C·2^{C·km/(log(m+2))^α} steps when all variables occur, any machine
renaming the occurring variables and then running it counts k-CNFs with m≥2 clauses in 2^{O(km/(log
m)^α)} steps plus a polynomial in the input length. -/
alias PaperIndex.rate.OccurM.everyWrapperCountsUnary := OccurM.everyWrapperCountsUnary

/-- A step of the proof of Theorem A (c): both forms of the bound of Theorem A (b) (states within
its polynomial factor or within the whole bound) only weaken when C₀ grows, as used «with the larger
of C₀ and 10». -/
alias PaperIndex.rate.CliqueLevels.solvesGrowsWithTheConstant := CliqueLevels.solvesGrowsWithTheConstant

/-- A step of the proof of Theorem A (c): «as is the case for ρ=11/12 and for ρ=1/√2»: for both and
every x₀, a number between 0.85ρ^ℓ and ρ^ℓ is computed from ℓ as the proviso of Theorem A (c) asks. -/
alias PaperIndex.rate.FixedWidth.provisoHolds := FixedWidth.provisoHolds

/-- A step of the proof of Theorem A (c): the second sentence of Theorem A (c), under its hypotheses
and proviso: one machine counts k-CNFs on n ≥ 4 variables within 2^{C·n log log n/(log n)^{α′}}
steps, C depending on k. -/
alias PaperIndex.rate.FixedWidth.countsFromPieces := FixedWidth.countsFromPieces

/-- A step of the proof of Theorem A (c): for ½ ≤ ρ < 1 and x₀ ≥ 18: e_ℓ ≥ ½ρ^ℓ ≥ 2^{−ℓ−1} ≥ 1/log
K_ℓ, and every number between 0.85ρ^ℓ and ρ^ℓ lies in [e_ℓ, 2e_ℓ]. -/
alias PaperIndex.rate.FixedWidthSteps.chainOfInequalities := FixedWidthSteps.chainOfInequalities

/-- A step of the proof of Theorem A (c): e_ℓ ≤ (3x₀+6)/(log K_ℓ)^{α′}, by Theorem A (a), as the «In
particular» of Theorem D (a) needs. -/
alias PaperIndex.rate.FixedWidthSteps.rateOfThePairs := FixedWidthSteps.rateOfThePairs

/-- A step of the proof of Theorem A (c): for fixed k, the conditions n ≥ K₀¹⁷ and k ≤ (log n)^{1/4}
of Theorem D (a) hold for all but finitely many n. -/
alias PaperIndex.rate.FixedWidthSteps.conditionsHoldEventually := FixedWidthSteps.conditionsHoldEventually

/-- A step of the proof of Theorem A (c): a k-CNF with k ≤ 3 is also a 3-CNF, so that a formula with
k ≤ 2 is read as a 3-CNF. -/
alias PaperIndex.rate.FixedWidthSteps.readAsThree := FixedWidthSteps.readAsThree

/-- A step of the proof of Theorem A (c): for fixed k and the finitely many n ≥ 4 below a bound,
trying all assignments, 2^{cn}·n^{ck} steps, is within 2^{C·n log log n/(log n)^α} for some C. -/
alias PaperIndex.rate.FixedWidthSteps.smallCasesAreWithinTheBound := FixedWidthSteps.smallCasesAreWithinTheBound

/-- A step of the proof of Theorem A (c): that the pairs (K_ℓ, e_ℓ) of (40) meet the hypothesis of
Theorem D (a) follows from the levels of the recursion of Theorem A (b) and e_ℓ ≥ ½ρ^ℓ ≥ 2^{−ℓ−1} ≥
1/log K_ℓ. -/
alias PaperIndex.rate.FixedWidthSteps.hypothesisHoldsFrom := FixedWidthSteps.hypothesisHoldsFrom

/-- A step of the proof of Theorem A (c): from the «In particular» of Theorem D (a), its conditions
for all but finitely many n, the bound for the other n and facts on the width taken: the bound for
each fixed k. -/
alias PaperIndex.rate.FixedWidthSteps.everyChoiceCountsFrom := FixedWidthSteps.everyChoiceCountsFrom

/-- A step of the proof of Theorem A (c): the second sentence of Theorem A (c) from the steps of its
proof: Theorem D (a), its hypothesis, the rate of e_ℓ, a test choosing between two machines, and
trying all assignments. -/
alias PaperIndex.rate.FixedWidthSteps.sentenceFromTheSteps := FixedWidthSteps.sentenceFromTheSteps

/-- A step of the proof of Theorem A (c): for every c there is a C₀ such that the recursion of
Theorem A (b) on any pieces with parameters (ρ, c) meets the hypothesis of Theorem D (a) for the
pairs of (40). -/
alias PaperIndex.rate.FixedWidthSteps.hypothesisHolds := FixedWidthSteps.hypothesisHolds

/-- A step of the proof of Theorem A (c): if e_ℓ ≤ a/(log K_ℓ)^α′, α′ > 0, every machine using the
algorithm of Theorem D (a) when n ≥ K₀¹⁷ and k ≤ (log n)^{1/4}, else exhaustive search, counts for
fixed k in 2^{C·n log log n/(log n)^α′} steps. -/
alias PaperIndex.rate.FixedWidthSteps.everyChoiceCounts := FixedWidthSteps.everyChoiceCounts

/-- A step of the proof of Theorem A (c): every machine that meets the bound in m of Theorem A (c)
at α′ = ½, 2^(C·km/√(log m)), with a polynomial in the input length added, meets it with nothing
added, with another constant (for formulas in which every variable occurs). -/
alias PaperIndex.rate.NamesInOrder.boundInMWithoutThePolynomial := NamesInOrder.boundInMWithoutThePolynomial

/-- A step of the proof of Theorem A (c): for a polynomial-time clique algorithm with the hypothesis
of Theorem D (a) and e_ℓ ≤ a/√(log K_ℓ): every machine computing the algorithm of Theorem A (c) on
it meets the bound in m, every one alternating it with Step 6 of Appendix D meets Corollary 11, and
one exists. -/
alias PaperIndex.rate.NamesInOrder.onEverySolver := NamesInOrder.onEverySolver

/-- A step of the proof of Theorem A (c): the first sentence of Theorem A (c) at α′ = ½: one machine
with finite alphabets and one constant C count within 2^{C·km/√(log m)} steps, with nothing added. -/
alias PaperIndex.rate.NamesInOrder.boundInMHolds := NamesInOrder.boundInMHolds

/-! ## Theorem B, Appendix B -/

/-- **Theorem B** (there are pieces with parameters (1/√2, c), for an absolute constant c). In Lean:
the time clause of Definition 7 (c), «within 2^{cλ} operations», becomes at most 2^{cλ} steps of a
machine each of whose steps may be any polynomial-time function of its state, with states of size at
most (2^{cλ}+(2λ)^c+8)·((2λ)^c+8), λ given in unary; because this bound on memory is exponential in
λ, a machine that writes 2^{cλ} symbols and then does all the work in one step meets the clause, and
the pieces of this theorem meet it in exactly that way, so for a Turing machine only 2^{O(λ)} steps
follow, with a constant larger than c; the proof does not run the procedures of «Sizes and
operations» step by step. The proof of the Main Theorem uses the form below that names the functions
of the proof (PiecesCounted.halfPieces), from which this statement follows. -/
alias PaperIndex.halfPieces := PiecesCounted.halfPiecesExist

/-- Theorem B: for the functions of its proof. In Lean: the pieces are those of the proof: 𝓘 =
{−2h,…,2h}, d = h!, the A_s, c^row_s = ⌈log R^row_s⌉ and c^col_s = ⌈log R^col_s⌉; «within 2^{cλ}
operations» becomes at most 2^{cλ} steps of a machine each of whose steps may be any polynomial-time
function of its state, with states of size at most (2^{cλ}+(2λ)^c+8)·((2λ)^c+8), λ given in unary;
the machine of the proof writes 2^{cλ} symbols and then does all the work in one step, which this
exponential bound on memory allows, and does not run the procedures of «Sizes and operations» step
by step. -/
alias PaperIndex.halfPiecesNamed := PiecesCounted.halfPieces

/-- A step of the proof of Theorem B: from Theorem B with time given by a string of units appended
to the input, and a conversion of such time to counted steps: the same pieces with steps counted and
𝓘 shifted by −2h to {−2h,…,2h}. -/
alias PaperIndex.halfPieces.PiecesCounted.halfPiecesFrom := PiecesCounted.halfPiecesFrom

/-! ## Lemma 9, Appendix B -/

/-- **Lemma 9** (three properties of the operators Q_s(a, b) on V_E). In Lean: the statement is as
printed. The proof follows the five paragraphs of the printed proof, but proves the three claims for
the integer matrices of the operators, defined by the recursion (O2), and carries them over; and
several steps of «Generating functions», «One Laurent polynomial» and «The constant» are proved from
differential equations in the variables x_n, x′_n instead of by expanding the exponentials or by
inspecting 𝒩. -/
alias PaperIndex.operators := AppHalfPieces.lemmaQ

/-! ## Lemma 10, Appendix B -/

/-- **Lemma 10** (a^μ[−h]·b^ν = h!·[μ = ν] for all partitions μ, ν of h). In Lean: as printed. -/
alias PaperIndex.dual := AppHalfPieces.lemmaDual

/-! ## Theorem C, Appendix C -/

/-- **Theorem C** (one deterministic algorithm counts the satisfying assignments of a 3-CNF on n ≥ 2
variables in time 2^{O(n/(log n)^{α/10})}). In Lean: time is counted in steps of a multi-stack
Turing machine of Mathlib, on a code that writes n in unary; the Lean derives it from the statement
of Theorem D (b), through a proof of that statement other than the one shown below, not along the
sketched proof of Appendix C. -/
alias PaperIndex.count := PrintedOrder.countRateFromBoundInN

/-- A step of the proof of Theorem C: from Theorem D (b): if one algorithm counts satisfying
assignments of k-CNFs (k ≥ 1, n ≥ 4) in time 2^{Ck²n log log n/√(log n)}, then one counts those of
3-CNFs on n ≥ 2 variables in time 2^{O(n/(log n)^{1/20})}. -/
alias PaperIndex.count.ThmCount.stTheorem := ThmCount.stTheorem

/-- A step of the proof of Theorem C: a map computable in polynomial time turns the code of a 3-CNF
into the code of the same formula with four added variables whose values are forced. -/
alias PaperIndex.count.ThmCount.stFrontEnd := ThmCount.stFrontEnd

/-- A step of the proof of Theorem C: the four added forced variables keep a 3-CNF a 3-CNF and keep
its number of satisfying assignments; that number in n + 5 bits, without its four highest bits, is
the number in n + 1 bits. -/
alias PaperIndex.count.ThmCount.stPadKeepsCount := ThmCount.stPadKeepsCount

/-- A step of the proof of Theorem C: the code of a 3-CNF on n variables, with 3 slots per clause,
has length polynomial in n. -/
alias PaperIndex.count.ThmCount.stInputLength := ThmCount.stInputLength

/-- A step of the proof of Theorem C: dropping the four highest bits of the output, the last step of
the counting machine for Theorem C, takes polynomial time. -/
alias PaperIndex.count.ThmCount.stLastStep := ThmCount.stLastStep

/-- A step of the proof of Theorem C: every machine that adds the four forced variables, runs an
algorithm with the bound of Theorem D (b) and drops the four highest bits counts on 3-CNFs with n ≥
2 variables in time 2^{O(n/(log n)^{1/20})}. -/
alias PaperIndex.count.ThmCount.stFromVariablesB := ThmCount.stFromVariablesB

/-- A step of the proof of Theorem C: for a machine M with finite alphabets and the bound of Theorem
D (b), a machine that adds four forced variables in polynomial time, runs M and drops four top bits
exists, and all such count in time 2^{O(n/(log n)^{1/20})}. -/
alias PaperIndex.count.ThmCount.stCanBeWrappedAndEveryWrapperCounts := ThmCount.stCanBeWrappedAndEveryWrapperCounts

/-- A step of the proof of Theorem C: if the bound of Theorem D (b) holds, one algorithm counts the
satisfying assignments of 3-CNFs on n ≥ 4 variables in the time 2^{O(n(log log n)^{2/3}/(log
n)^{1/6})} of the remark after Theorem C. -/
alias PaperIndex.count.ThmCount.stRemarkTime_of := ThmCount.stRemarkTime_of

/-- A step of the proof of Theorem C: for all constants C, q, a, d some C' gives q·(2^{9C(n+4) log
log(n+4)/√(log(n+4))} + a(n+2)^d + 1)^q ≤ 2^{C'n/(log n)^{1/20}} for all n ≥ 2. -/
alias PaperIndex.count.ThmCount.stRates := ThmCount.stRates

/-- A step of the proof of Theorem C: for k = 3 and 0 < ε ≤ 1/2, the bound 2 + 4α(32α) on the
occurrences of a literal at a leaf of Calabro's sparsification, α his threshold, is O(ε^{-2}
log²(1/ε)). -/
alias PaperIndex.count.ThmCount.stMEps := ThmCount.stMEps

/-- A step of the proof of Theorem C: the remark after Theorem C: with Calabro's thresholds, each
output of the changed sparsification of a 3-CNF on n variables has at most (Aε^{-2} log²(1/ε)+2)n
clauses, 0 < ε ≤ 1/2, A a constant. -/
alias PaperIndex.count.ThmCount.stMEpsClauses := ThmCount.stMEpsClauses

/-- A step of the proof of Theorem C: one deterministic algorithm counts the satisfying assignments
of a 3-CNF on n ≥ 4 variables in time 2^{O(n(log log n)^{2/3}/(log n)^{1/6})}, the time of the
remark after Theorem C, derived from Theorem D (b). -/
alias PaperIndex.count.ThmCount.stRemarkTime := ThmCount.stRemarkTime

/-! ## Theorem D, Appendix D -/

/-- A step of the proof of Theorem D: the program that picks the level is polynomial-time and
returns, for a bound b ≥ K₀, the largest ℓ with K_ℓ ≤ b, as ℓ and K_ℓ in unary. -/
alias PaperIndex.oneLogFromLevels.QueryMachines.Bridge.pickOfFacts := QueryMachines.Bridge.pickOfFacts

/-- **Theorem D (a)** (from one algorithm for the (K_ℓ, λ)-cliques of all levels to one algorithm
that counts the satisfying assignments of a k-CNF on n variables in time 2^{O(k²·e·n·log(k/e))}). In
Lean: an operation of the algorithm in the hypothesis is a table query or a step that may be any
polynomial-time function of its whole state, and Lean adds that its states are no larger than the
bound (57); the conclusion counts steps of a multi-stack Turing machine of Mathlib with finite
alphabets, with k written in the input; the constant C′ is chosen after the algorithm, so «the
constants depend only on those of the hypothesis» is not stated; the proof first turns the algorithm
into one that is given the tables written out, not by queries, together with a string of blank
symbols as its budget of time, about 2^{e′_ℓK_ℓ²λ}·(K_ℓ(λ+B))^{O(K_ℓ²)} symbols long, with e′_ℓ in
[e_ℓ, 2e_ℓ] (see (2) and (5) at the head of this index), a step the paper does not have; the proof
of the Main Theorem does not use this statement. -/
alias PaperIndex.oneLogFromLevels := ThmVariables.partA

/-- Theorem D (a): for every machine that carries out the algorithm of the steps of its proof. In
Lean: the clique algorithm of the hypothesis is not counted in operations with query access, as
printed: it is given the tables written out and a string of 2^e symbols as its budget of time, runs
in polynomial time, and is right whenever e is at least the logarithm of the bound (57); the
conclusion is about the counting algorithm of Steps 1 to 5 built from it, which is handed such a
string too, with e computed from the formula: once its threshold for large n is large enough, some
multi-stack Turing machine of Mathlib computes it, and every Turing machine that computes it, with
any polynomial overhead, meets the bound of Theorem D (a), with a constant chosen after the machine. -/
alias PaperIndex.oneLogFromLevelsForEveryMachine := RecursionToBound.thmVariablesAForEveryMachine

/-- A step of the proof of Theorem D (a): if the algorithm for cliques is a polynomial-time function
of ℓ, of the tables written out (not queried) and of a string of T units, right once T ≥ (57), and
K_ℓ and a number in [e_ℓ, 2e_ℓ] are polynomial-time functions of ℓ, then one Turing machine has the
bound of Theorem D (a), with a constant chosen after these algorithms. -/
alias PaperIndex.oneLogFromLevels.RecursionToBound.thmVariablesAWithNumberBetween := RecursionToBound.thmVariablesAWithNumberBetween

/-- A step of the proof of Theorem D (a): for k ≥ 3 and a k-CNF, the tree of calls walked by the
algorithm, cut at any depth ≥ (β₁ + … + β_{k−1})·n, a bound on its path lengths, has as leaves
exactly the outputs of the sparsification of Appendix C. -/
alias PaperIndex.oneLogFromLevels.RecursionToBound.walkTreeIsSparsify := RecursionToBound.walkTreeIsSparsify

/-- A step of the proof of Theorem D (a): «Take ε ≤ 1 between e and 2e»: for k ≥ 3, 0 < e ≤ 1 and a
fraction between e and 2e, the ε made from it lies in [e, 2e], ε ≤ 1, and the sparsification has at
most 2^{εn} ≤ 2^{2en} outputs. -/
alias PaperIndex.oneLogFromLevels.RecursionToBound.outputsAreFew := RecursionToBound.outputsAreFew

/-- A step of the proof of Theorem D (a): for large n, 3 ≤ k ≤ (log n)^{1/4}, (log n)^{−C₀} ≤ e ≤ 1
and every Δ from 2 to the bound on occurrences in an output: log Δ ≤ 3k·log(8k/e) + 2 ≤ 4kC₀·log log
n and Δ ≤ (log n)^{4kC₀}. -/
alias PaperIndex.oneLogFromLevels.RecursionToBound.outputsAreWithinTheSetting := RecursionToBound.outputsAreWithinTheSetting

/-- A step of the proof of Theorem D (a): for k ≥ 3 and a k-CNF, every output of the sparsification
has Δ (the larger of 2 and the most clauses in which one variable occurs) at most 2(θ₀ + … +
θ_{k−1}) + 2, θ the thresholds for k, ε. -/
alias PaperIndex.oneLogFromLevels.RecursionToBound.ownDeltaIsBounded := RecursionToBound.ownDeltaIsBounded

/-- A step of the proof of Theorem D (a): for k ≥ 3, the bound 2(θ₀ + … + θ_{k−1}) + 2 on the
occurrences of a variable in an output, θ the thresholds for k and ε, is at most the printed
2(8k/ε)^{3k} + 2. -/
alias PaperIndex.oneLogFromLevels.RecursionToBound.occBoundIsThePrinted := RecursionToBound.occBoundIsThePrinted

/-- A step of the proof of Theorem D (a): not in the printed proof: the bounds of Step 3 that do not
depend on the formula (on the total U, on P, on the number of profiles, on the checks) increase with
Δ. -/
alias PaperIndex.oneLogFromLevels.RecursionToBound.boundsGrowWithDelta := RecursionToBound.boundsGrowWithDelta

/-- A step of the proof of Theorem D (a): «Hence the number of satisfying assignments of Φ is
computed in time 2^{O(ekn log Δ)}»: for large n, 3 ≤ k ≤ (log n)^{1/4} and 2 ≤ Δ ≤ (log n)^{4kC₀}
the exponent is at most A·e·k·n·log Δ. -/
alias PaperIndex.oneLogFromLevels.RecursionToBound.oneOutputCost := RecursionToBound.oneOutputCost

/-- A step of the proof of Theorem D (a): the time of the sparsification: the exponent needed to
walk its tree is at most εn + c·k·(log n + log(8k/ε)), a factor (8k/ε)^{O(k)} more than the printed
2^{εn}·n^{O(k)}. -/
alias PaperIndex.oneLogFromLevels.RecursionToBound.walkCost := RecursionToBound.walkCost

/-- A step of the proof of Theorem D (a): «The time is 2^{2en} n^{O(k)} 2^{O(ekn log Δ)} = 2^{O(k²en
log(k/e))}»: for large n and 3 ≤ k ≤ (log n)^{1/4}, the exponent for outputs and sparsification is
at most A·k²·e·n·log(k/e). -/
alias PaperIndex.oneLogFromLevels.RecursionToBound.exponentIsWithinTheBound := RecursionToBound.exponentIsWithinTheBound

/-- A step of the proof of Theorem D (a): a guard not in the printed proof: for n beyond its
threshold, the algorithm sparsifies exactly when the exponent it needs (for the outputs plus for the
sparsification tree) is at most n. -/
alias PaperIndex.oneLogFromLevels.RecursionToBound.planFailsOnlyAboveN := RecursionToBound.planFailsOnlyAboveN

/-- A step of the proof of Theorem D (a): the algorithm cuts k off at ⌊log₂(n+1)⌋, which the printed
proof does not; for n ≥ 1 and k ≤ (log n)^{1/4} this changes nothing: min(k, ⌊log₂(n+1)⌋) = k. -/
alias PaperIndex.oneLogFromLevels.RecursionToBound.cutOffIsIdle := RecursionToBound.cutOffIsIdle

/-- A step of the proof of Theorem D (a): in Step 5 of Appendix D, «The algorithm takes for k the
largest number of literals in a clause of its input, or 3 if that is larger», not the k written in
the code; from the code it also finds the level ℓ of n and the number given for ℓ (meant to lie in
[e_ℓ, 2e_ℓ]). -/
alias PaperIndex.oneLogFromLevels.RecursionToBound.widthOnTheCode := RecursionToBound.widthOnTheCode

/-- A step of the proof of Theorem D (a): correct once its threshold for large n is large enough:
for n ≥ K₀^{17}, 3 ≤ k ≤ (log n)^{1/4}, a k-CNF and a string of 2^e units or more, e the exponent it
computes, the algorithm outputs the count. -/
alias PaperIndex.oneLogFromLevels.RecursionToBound.countIsRight := RecursionToBound.countIsRight

/-- A step of the proof of Theorem D (a): the algorithm of Step 5 and its exponent are
polynomial-time in the input and a string of units, on all inputs, if the algorithm for cliques, the
choice of ℓ and the number in [e_ℓ, 2e_ℓ] are. -/
alias PaperIndex.oneLogFromLevels.RecursionToBound.countIsPolynomialTime := RecursionToBound.countIsPolynomialTime

/-- A step of the proof of Theorem D (a): the number e′_ℓ made from the number of the hypothesis
lies in [e_ℓ, 2e_ℓ], is positive and at most 1, and is itself computed from ℓ and K_ℓ in polynomial
time. -/
alias PaperIndex.oneLogFromLevels.QueryMachines.Bridge.cutNumberFacts := QueryMachines.Bridge.cutNumberFacts

/-- A step of the proof of Theorem D (a): not in the printed proof: a precision function for e
(Lean's replacement for the number in [e_ℓ, 2e_ℓ]) is one for every e′ with e_ℓ ≤ e′_ℓ ≤ min(2e_ℓ, 1),
with twice the constant. -/
alias PaperIndex.oneLogFromLevels.QueryMachines.Bridge.precisionCarriesOver := QueryMachines.Bridge.precisionCarriesOver

/-- A step of the proof of Theorem D (a): if the pairs (K_ℓ, e_ℓ) meet the hypothesis of Theorem D (a)
by a machine with polynomial-time steps and states of size at most (57), then it holds in Lean's
form with e′_ℓ∈[e_ℓ,2e_ℓ] for e_ℓ. -/
alias PaperIndex.oneLogFromLevels.QueryMachines.Bridge.solverOfMachineLevels := QueryMachines.Bridge.solverOfMachineLevels

/-- A step of the proof of Theorem D (a): the numbers K_ℓ of (40), for every x₀, are computed from ℓ
in time polynomial in K_ℓ. -/
alias PaperIndex.oneLogFromLevels.CliqueLevels.levelsAreComputed := CliqueLevels.levelsAreComputed

/-- A step of the proof of Theorem D (a): the last sentence of Theorem D (a): if e_ℓ ≤ c·(log
K_ℓ)^(−α′) for all ℓ, with α′ > 0, then every machine with the bound 2^{C·k²·e·n·log(k/e)} of the
sentence before it counts within 2^{C′·k²·n·log log n/(log n)^α′} steps. -/
alias PaperIndex.oneLogFromLevels.ThmVariables.inParticular := ThmVariables.inParticular

/-- A step of the proof of Theorem D (a): from an algorithm with query access meeting the hypothesis
of Theorem D (a), with polynomial-time steps and states no larger than (57) added: an algorithm for
cliques, a polynomial-time function whose time is stood for by the length of a unit string it is
given, for the same K_ℓ and the number in [e_ℓ, 2e_ℓ] cut at 1 in place of e_ℓ. -/
alias PaperIndex.oneLogFromLevels.ThmVariables.solverFromMachine := ThmVariables.solverFromMachine

/-- A step of the proof of Theorem D (a): if Theorem D (a) holds for clique algorithms given as a
function of the input and a string of T units, right once T is large, and a machine with query
access yields such a function, then it holds for the printed hypothesis plus polynomial-time steps
and states no larger than (57); all three are Lean theorems, so alone this shows little. -/
alias PaperIndex.oneLogFromLevels.ThmVariables.partAFromThePaddingString := ThmVariables.partAFromThePaddingString

/-- A step of the proof of Theorem D (a): if Theorem D (a) holds for every machine computing the
count of Steps 1–5 from a clique algorithm given a string of units as long as its operation count,
and each query-access algorithm yields one, then also with query access as in its hypothesis;
premises and conclusion are Lean theorems, so the implication alone shows little. -/
alias PaperIndex.oneLogFromLevels.ThmVariables.partAForEveryMachineFrom := ThmVariables.partAForEveryMachineFrom

/-- A step of the proof of Theorem D (a): Theorem D (a) with the bound for some machine follows from
it with the bound for every machine that computes the function of Steps 1 to 5 of Appendix D; both
forms are Lean theorems, so the implication alone shows little. -/
alias PaperIndex.oneLogFromLevels.ThmVariables.partAFromEveryMachine := ThmVariables.partAFromEveryMachine

/-- A step of the proof of Theorem D (a): under the hypothesis of Theorem D (a), with
polynomial-time steps and states no larger than (57) added, and for every large enough cut-off below
which all assignments are tried: a Turing machine computes the count of Steps 1–5 of Appendix D, and
every one that does has the bound 2^{C′·k²·e·n·log(k/e)}, C′ chosen after it. -/
alias PaperIndex.oneLogFromLevels.ThmVariables.partAForEveryMachine := ThmVariables.partAForEveryMachine

/-- A step of the proof of Theorem D (a): not in the printed proof: for 0 < e ≤ e′ ≤ 2e, e′ ≤ 1 and
k ≥ 1, 2^{C·k²·e′·n·log(k/e′)} ≤ 2^{2C·k²·e·n·log(k/e)}, so a number in [e_ℓ, 2e_ℓ] may stand for
e_ℓ. -/
alias PaperIndex.oneLogFromLevels.ThmVariables.boundAtANumberBetween := ThmVariables.boundAtANumberBetween

/-- **Theorem D (b)** (the second sentence of part (b): one algorithm counts the satisfying
assignments of a k-CNF on n variables, for all k ≥ 1 and n ≥ 4, in time 2^{C·k²·n·log log n/√(log
n)}). In Lean: only the second sentence of Theorem D (b), with time in steps of a multi-stack Turing
machine of Mathlib; that the pairs of (40) satisfy the hypothesis is a separate step. -/
alias PaperIndex.oneLog := CountedRoute.thmVariablesBHolds

/-- Theorem D (b): its second sentence, from the conclusion of part (a), for any algorithm for
cliques whose e_ℓ are at most a/√(log K_ℓ). In Lean: from a clique algorithm that is given the
tables written out and a string of blank symbols as its budget of time, whose levels have e_ℓ ≤
a/√(log K_ℓ) (only the upper half of the printed Θ), and a multi-stack Turing machine of Mathlib
with the conclusion of Theorem D (a): a machine that chooses between it and trying all assignments
exists, and every such machine meets the bound of Theorem D (b) in its steps, with C fixed before k,
n and the formula; that the pairs of (40) satisfy the hypothesis is a separate step. -/
alias PaperIndex.oneLogFromPartA := PairsToBound.thmVariablesBFromThmVariablesA

/-- Theorem D (b): the first sentence of part (b): the pairs of the recursion, for the pieces of
Appendix B, satisfy the hypothesis of part (a). In Lean: for some c and some x₀ ≥ 18 with 2^x₀ ≥ c +
7, not for every x₀ of Theorem A: one machine for cliques, built on pieces with parameters (1/√2,
c+2) that are those of the proof of Theorem B, meets the hypothesis with an operation read as a
table query or a step that may be any polynomial-time function of the whole state, and with its
states bounded by the same number; of e_ℓ = Θ((log K_ℓ)^(−1/2)) only the upper half is stated. -/
alias PaperIndex.theRecursionMeetsTheHypothesis := CountedInstance.theRecursionMeetsTheHypothesis

/-- A step of the proof of Theorem D (b): the pairs of (40), for any pieces with parameters (ρ, c)
and any x₀ ≥ 18 with 2^{x₀} ≥ c + 5, satisfy the hypothesis of Theorem D (a) except its clause on a
number in [e_ℓ, 2e_ℓ], with C₀ depending on c alone. -/
alias PaperIndex.oneLog.PairsToBound.theRecursionHasLevels := PairsToBound.theRecursionHasLevels

/-- A step of the proof of Theorem D (b): the pairs (K_ℓ, e_ℓ) of (40), for pieces with parameters
(1/√2, c) such as those of Appendix B, satisfy the hypothesis of Theorem D (a), with constants
depending on c alone. -/
alias PaperIndex.oneLog.PairsToBound.thePairsSatisfyTheHypothesis := PairsToBound.thePairsSatisfyTheHypothesis

/-- A step of the proof of Theorem D (b): for ρ = 1/√2 and x₀ ≥ 18: ½ρ^ℓ ≤ e_ℓ ≤ 0.85ρ^ℓ and x₀2^ℓ ≤
log K_ℓ ≤ (3x₀+6)2^ℓ, so ½√x₀/√(log K_ℓ) ≤ e_ℓ ≤ 0.85√(3x₀+6)/√(log K_ℓ). -/
alias PaperIndex.oneLog.PairsToBound.thetaOfThePairs := PairsToBound.thetaOfThePairs

/-- A step of the proof of Theorem D (b): if e_ℓ ≤ a/√(log K_ℓ) for all ℓ, every machine with the
conclusion of Theorem D (a) counts, for n ≥ K₀^{17} and 3 ≤ k ≤ (log n)^{1/4}, within 2^{C·k²·n·log
log n/√(log n)} steps. -/
alias PaperIndex.oneLog.PairsToBound.mainRegimeBound := PairsToBound.mainRegimeBound

/-- A step of the proof of Theorem D (b): «k is the largest number of literals in a clause, or 3 if
that is larger, which multiplies k² by at most 9»: it is ≥ 3, at most max(k, 3) for any width k ≥ 1
of the formula. -/
alias PaperIndex.oneLog.PairsToBound.widthOr3Stmt := PairsToBound.widthOr3Stmt

/-- A step of the proof of Theorem D (b): «the bound increases with k»: for n ≥ 4 and k ≤ k′,
2^{C·k²·n·log log n/√(log n)} at k is at most at k′, and likewise 2^{C·k²·e·n·log(k/e)} for 3 ≤ k ≤
k′, 0 < e ≤ 1. -/
alias PaperIndex.oneLog.PairsToBound.theBoundIncreasesWithTheWidth := PairsToBound.theBoundIncreasesWithTheWidth

/-- A step of the proof of Theorem D (b): polynomial-time functions of Step 6 of Appendix D exist:
one rewrites the input so that k is the largest number of literals in a clause, or 3; and, for each
K₀, one decides whether n ≥ K₀^17 and this k is at most (log n)^{1/4}, the case in which Theorem D (a)
is used. -/
alias PaperIndex.oneLog.PairsToBound.frontEndAndTestExist := PairsToBound.frontEndAndTestExist

/-- A step of the proof of Theorem D (b): every machine computing the count over all assignments
from the input and a string of 2ⁿ units, with polynomial overhead, runs within 2^{c·n}·n^{c·k} steps
for some c (the print: 2^n·n^{O(k)}). -/
alias PaperIndex.oneLog.PairsToBound.everyExhaustiveMachineTriesAll := PairsToBound.everyExhaustiveMachineTriesAll

/-- A step of the proof of Theorem D (b): some machine with finite alphabets computes the count over
all assignments from the input and a string of 2ⁿ units, on every bit string, and runs within
2^{c·n}·n^{c·k} steps. -/
alias PaperIndex.oneLog.PairsToBound.exhaustiveMachineExists := PairsToBound.exhaustiveMachineExists

/-- A step of the proof of Theorem D (b): (2n+1)^k ≤ n^{2k} for all k and all n ≥ 3, as in «as there
are fewer than (2n+1)^k ≤ n^{2k} clauses». -/
alias PaperIndex.oneLog.PairsToBound.clauseCountPowStmt := PairsToBound.clauseCountPowStmt

/-- A step of the proof of Theorem D (b): the inequalities of «It is within the bound»: for n ≥ 4, k
log n ≤ k²n log log n/√(log n); n ≤ k²n log log n/√(log n) if k > (log n)^{1/4}; n/√(17 log K₀) ≤ n
log log n/√(log n) if n < K₀^{17}. -/
alias PaperIndex.oneLog.PairsToBound.fallBackIsWithinTheBound := PairsToBound.fallBackIsWithinTheBound

/-- A step of the proof of Theorem D (b): if e_ℓ ≤ a/√(log K_ℓ), every machine choosing by the test
of Step 6 between one with the conclusion of Theorem D (a) and exhaustive search counts within
2^{Ck²n log log n/√(log n)} steps. -/
alias PaperIndex.oneLog.PairsToBound.everyChoiceMeetsThmVariablesB := PairsToBound.everyChoiceMeetsThmVariablesB

/-- A step of the proof of Theorem D (b): if Lean's statements of Theorem D (a) and of Theorem B
hold, then so does Lean's statement of Theorem D (b), along Step 6 of Appendix D; all three are
proved in Lean, so this implication by itself shows little. -/
alias PaperIndex.oneLog.PairsToBound.thmVariablesAImpliesThmVariablesB := PairsToBound.thmVariablesAImpliesThmVariablesB

/-- A step of the proof of Theorem D (b): the first sentence of Theorem D (b), time in operations:
for some c and x₀ ≥ 18, the algorithm for cliques of Theorem A (b) on the pieces of Appendix B with
parameters (1/√2, c+2) meets the hypothesis (57) for the pairs (40), and for it the bound of Theorem
D (b), the bound in m and that of Corollary 11 hold. -/
alias PaperIndex.oneLog.CountedRoute.onTheCountedRecursion := CountedRoute.onTheCountedRecursion

/-- A step of the proof of Theorem D (b): if the machine of Theorem A (b) on the pieces of Appendix
B meets the hypothesis of Theorem D (a) in counted operations, what follows from that hypothesis for
every machine with query access holds for it; premises and conclusion are all Lean theorems, so this
implication alone shows little. -/
alias PaperIndex.oneLog.CountedRoute.onTheCountedRecursionFrom := CountedRoute.onTheCountedRecursionFrom

/-! ## Corollary 11, Appendix D -/

/-- **Corollary 11** (one algorithm and one absolute constant C: time at most min{2^{C·km/√(log m)},
2^{C·k²·n·log log n/√(log n)}}). In Lean: time is counted in steps of a multi-stack Turing machine
of Mathlib with finite alphabets; the variables are x₀,…,x_{n−1}, and each of them occurs in the
formula; the statement is the printed one up to this coding and this machine model, but the proof is
not (see the head of this index). -/
alias PaperIndex.minOfBounds := CountedRoute.corMinHolds

/-- Corollary 11: for every pair of machines that meet the two bounds. In Lean: if one machine
counts within 2^{C₁·km/√(log m)} + C₁·L₁^{C₁} steps on formulas in which every variable occurs, L₁
being the length of the input that writes n in unary (the bound in m with an added term that the
paper does not have), and another has the bound of Theorem D (b), then a machine that renames the
variables that occur and runs the two in alternation exists, and every such machine counts, on
formulas with m ≥ 2 clauses in which n ≥ 4 variables occur, within min{2^{C·km/√(log m)},
2^{C·k²·n·log log n/√(log n)}} + C·L^C steps, for a new constant C chosen after the machine; so the
alternation costs a constant power where the paper has a constant factor; here L is the length of an
input code that allows any names of the variables, written in binary, n counts only the variables
that occur, and steps of a multi-stack Turing machine of Mathlib are counted. -/
alias PaperIndex.minOfBoundsFromTheTwoTheorems := MinOfBounds.minBoundFromTheTwoTheorems

/-- Corollary 11: the sentence after its proof: this is the Main Theorem. In Lean: proved as an
equivalence for every machine and every constant C, with L the length of the input code that writes
the names of the variables in binary: meeting min{2^{C·km/√(log m)}, 2^{C·k²·n·log log n/√(log n)}} +
C·L^C is the same as meeting 2^{C·min{km/√(log m), k²·n·log log n/√(log n)}} + C·L^C. The printed
Theorem 1 has neither the term C·L^C nor the ranges k ≥ 1, m ≥ 2, n ≥ 4. -/
alias PaperIndex.minOfBoundsIsTheMainTheorem := MinOfBounds.minBoundIsTheMainTheorem

/-- A step of the proof of Corollary 11: three Lean propositions (the bound in m of Theorem 1,
Theorem D (b), Corollary 11 plus a polynomial in the input length) each say that a machine with
finite alphabets and a constant meet its bound. -/
alias PaperIndex.minOfBounds.MinOfBounds.propositionsUnfold := MinOfBounds.propositionsUnfold

/-- A step of the proof of Corollary 11: a machine that counts within C·2^{C·km/√(log(m+2))} steps
when every variable occurs also meets, for some C′, the bound in m of Theorem A (c) at α′=½ plus
C′·(length of the code)^{C′}. -/
alias PaperIndex.minOfBounds.MinOfBounds.boundInMSuffices := MinOfBounds.boundInMSuffices

/-- A step of the proof of Corollary 11: renaming the n variables that occur to x₀,…,xₙ₋₁ gives a
formula with as many clauses, a k-CNF if the given one is, in which every variable occurs, and whose
count over all 2ⁿ assignments is that of the given one as assignments of the variables that occur. -/
alias PaperIndex.minOfBounds.MinOfBounds.renamedCodeIsTheCodeOfARenaming := MinOfBounds.renamedCodeIsTheCodeOfARenaming

/-- A step of the proof of Corollary 11: some map on bit strings that is computable in polynomial
time takes the input code of every k-CNF, k ≥ 1, to the code of the formula with its occurring
variables renamed x₀,…,xₙ₋₁. -/
alias PaperIndex.minOfBounds.MinOfBounds.renamingFrontEndExists := MinOfBounds.renamingFrontEndExists

/-- A step of the proof of Corollary 11: «Both compute the same number.»: if one machine meets the
bound in m of Theorem A (c) and another that of Theorem D (b), both output the count on the code of
the renamed formula within their bounds. -/
alias PaperIndex.minOfBounds.MinOfBounds.bothComputeTheSameNumber := MinOfBounds.bothComputeTheSameNumber

/-- A step of the proof of Corollary 11: the code of the formula with its occurring variables
renamed is at most a·L^a bits long, for a fixed a, where L is the length of the input code of the
given k-CNF. -/
alias PaperIndex.minOfBounds.MinOfBounds.renamedCodeIsPolynomial := MinOfBounds.renamedCodeIsPolynomial

/-- A step of the proof of Corollary 11: «this constant goes into C», as arithmetic: as km/√(log m)
and n·log log n/√(log n) are at least 2, an overhead q·(t + L + 1)^q on the faster time t, with L
the length of the code, fits into C and C·L^C. -/
alias PaperIndex.minOfBounds.MinOfBounds.overheadGoesIntoC := MinOfBounds.overheadGoesIntoC

/-- A step of the proof of Corollary 11: if one machine meets the bound in m of Theorem A (c) at α′ =
½ and another that of Theorem D (b), every machine running the two in alternation after renaming the
variables meets the bound of Corollary 11 plus C·L^C, L the length of the input with variable names
in binary; the bound in m is assumed with such a term too. -/
alias PaperIndex.minOfBounds.MinOfBounds.everyAlternationMeetsMinBound := MinOfBounds.everyAlternationMeetsMinBound

/-- A step of the proof of Corollary 11: if two machines meet the bound in m of Theorem A (c) at α′ =
½ and that of Theorem D (b), then every machine running them in alternation on the renamed variables
that occur, each output tested for a bit 1, decides within the bound of Corollary 11 plus C·L^C for
some C, L the input length. -/
alias PaperIndex.minOfBounds.MinOfBounds.everyAlternationDecidesWithinMinBound := MinOfBounds.everyAlternationDecidesWithinMinBound

/-- A step of the proof of Corollary 11: for deciding: given machines with the bound in m of Theorem
A (c) at α′ = ½ and the bound of Theorem D (b), each followed by a test whether some output bit is
1, a machine running them in alternation after renaming exists, and every such machine decides
within the bound of Corollary 11 plus C·L^C, L the input length. -/
alias PaperIndex.minOfBounds.MinOfBounds.decidingFromTheTwoTheorems := MinOfBounds.decidingFromTheTwoTheorems

/-- A step of the proof of Corollary 11: if the bound in m of Theorem A (c) at α′ = ½ and that of
Theorem D (b) hold as Lean propositions, so does Corollary 11 on the input code that writes the
names of the variables in binary, plus a term C·L^C, L the input length, absent from Corollary 11;
all three are Lean theorems, so the implication alone shows little. -/
alias PaperIndex.minOfBounds.MinOfBounds.theTwoTheoremsImplyMinBound := MinOfBounds.theTwoTheoremsImplyMinBound

/-- A step of the proof of Corollary 11: when all of x₀,…,xₙ₋₁ occur, the cost q·(t+L+1)^q of the
alternation, t the faster bound and L the input length, is below 2^{C·min{km/√(log m), k²n log log
n/√(log n)}} for some C. -/
alias PaperIndex.minOfBounds.NamesInOrder.alternationCostGoesIntoC := NamesInOrder.alternationCostGoesIntoC

/-- A step of the proof of Corollary 11: if machines meet the bound in m of Theorem A (c) at α′ = ½,
with nothing added, and that of Theorem D (b), every machine that alternates them on the unchanged
input meets the corollary's bound, that of Theorem 1. -/
alias PaperIndex.minOfBounds.NamesInOrder.everyDirectAlternationMeetsTheBound := NamesInOrder.everyDirectAlternationMeetsTheBound

/-- A step of the proof of Corollary 11: the corollary for formulas on x₀,…,xₙ₋₁, each of which
occurs: one Turing machine with finite alphabets and one C meet min{2^{C·km/√(log m)}, 2^{C·k²n log
log n/√(log n)}}. -/
alias PaperIndex.minOfBounds.NamesInOrder.corMinHolds := NamesInOrder.corMinHolds

/-- A step of the proof of Corollary 11: if a machine meets the bound of Theorem 1 when the
variables x₀,…,xₙ₋₁ all occur, every machine running it after a renaming meets it for any names,
plus C·L^C, L the code length. -/
alias PaperIndex.minOfBounds.NamesInOrder.generalFormFollows := NamesInOrder.generalFormFollows

/-- A step of the proof of Corollary 11: from Theorem 1 for formulas in which all of x₀,…,xₙ₋₁
occur: Theorem 1 for any names of the variables, with C·L^C added to the bound, L the length of the
input code; both are Lean theorems, so the implication alone shows little. -/
alias PaperIndex.minOfBounds.NamesInOrder.generalFormFollowsAsPropositions := NamesInOrder.generalFormFollowsAsPropositions

/-! ## Lemma 12, Appendix D -/

/-- **Lemma 12** (Cut-off). In Lean: as printed, stated for any finite set in place of {0,1}^n and
any function V from it to finite sets. -/
alias PaperIndex.cutOff := VariableBound.lemCutoff

/-! ## Lemma 13, Appendix D -/

/-- **Lemma 13** (Family of checks). In Lean: the clauses are the numbers 0,…,m−1 and v = 2^a; the
sets, each an increasing list of numbers below m, are listed in time polynomial in m and a, both
given in unary, and are indexed by their places in the list; the list is also stated to be
non-empty, which the printed lemma does not say but its proof shows (|Ω| ≥ (15/16)|𝔽|⁴). -/
alias PaperIndex.familyOfChecks := VariableBound.Fld.lemFamily_listed

