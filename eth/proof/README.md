# The proofs

Every Lean file other than `MainResults.lean`, `Challenge.lean` and `Solution.lean` lies here. `PaperIndex.lean` has one entry for each numbered statement of the paper, which points to its Lean counterpart, followed by entries for further forms of it and for the steps of its proof. The folders below are groups: after the statements and the model of computation, in the order of the paper; a group is not part of a module's name: `proof/machines/Wrap/Arith.lean` is the module `Wrap.Arith`.

**Why several files define a CNF.** `MainResults.lean` imports all of Mathlib, and every file that stands over it is slow and needs much memory to compile. The proofs therefore stand over the statement files in `statements/`, which repeat the definitions with narrow imports, and `Solution.lean` passes from one to the other by unfolding definitions.

Sections 3, 5 and 6 of the paper, with Algorithm 1 of Section 8, are developed in `Paper` and `Eight` and, each in another way, in three more folders. `Exits` runs Algorithm 1 line by line on step machines; `Printed` starts from Definition 4 with a table query at one operation, as printed, but with a polynomial bound on memory added; `Given` takes Definition 2, clause (iii) included, as one property of a network given by procedures that may query tables. In `PaperIndex.lean` the main entries for Definitions 2 and 4, Lemma 1 and Proposition 3 come from `Given` and `Printed`; the other main entries of these sections come from `Paper`, `Eight` and `SparsificationLemma`. So some statements are proved more than once. The proof of the Main Theorem in `Solution.lean`, listed under «The proof of the Main Theorem, by name» below, does not use the Lean statements of Lemma 1, Proposition 3 or Theorem 2; for Theorem A (b) it uses the early-stopping loop of `Exits` and, from the proof of Lemma 1 in `Printed`, the grouping procedure with its counted queries; it uses nothing of `Given`.

The paper states Theorem 2, Lemma 4 and Algorithm 1 for counting the satisfying assignments of a 3-CNF. The Lean files of proof/threesat (`Suffices`, `Exits`, `Enumerate`, `Printed`, `Given`, `ThreeSatOnTree`, `ThreeSatPrinted`) and parts of proof/consequences, proof/machines, proof/networks/Coding and proof/networks/Eight carry out the same proof for deciding satisfiability: procedure Count counts, as in the paper, but lines 1 to 4 of Algorithm 1 answer «satisfiable» if the count is positive for some formula of the list (in `Exits`, `Printed` and `Given` at the first such formula), where the paper adds the counts up; these files call this deciding form procedure Sat, where the paper has #Sat. What these files state of Lemma 4, and pass on to the rest of the proof, is only that the formula is satisfiable if and only if at least one formula of the list is (`Enumerate` derives it from the stronger fact that every satisfying assignment satisfies exactly one formula of the list); the two properties that the printed form adds are proved in Lean, separately, for the list of Lean's own branching procedure (see the entry under Lemma 4). So the sentences between «…» in the comments on Section 6, Lemma 4, lines 1 to 4 of Algorithm 1 and the proof of Corollary 5 are worded for deciding; those in the comments on the proof of Corollary 6 follow the Lean proof described under it, which runs Count on every formula of the sparsification; and not all of them are to be found word for word in the paper. The statement files `ThmEveryDeltaStatement.lean` and `PaperSentencesStatement.lean` also state Theorem 2 in this deciding form, and the latter quotes it so. The six theorems under Theorem 2 state its decision form, which the printed statement implies; the printed, counting statement is in Lean the case k = 3 of the first half of the entry under Corollary 6 (`FromPrinted.SplitCount.countingCorollary`), which has a proof of its own.

## statements/ : definitions and propositions only, with narrow imports

- `NetworkStatements`: Definitions for a recursion with single-bit pieces, which the paper does not use
- `StepMachineStatements`: The algorithm as a step machine: definitions
- `ThreeSatStatement`: ETH for 3-SAT on Mathlib Turing machines (Definition 6): `s₃TM` > 0, the infimum of the δ for which some machine decides 3-SAT in time O(2^{δn})
- `KSatStatement`: k-SAT in time O(2^{δn}) and the numbers s_k
- `CountKSatStatement`: The statement for #k-SAT and for the counting Exponential Time Hypothesis
- `ThreeSatRateStatement`: Definitions: ONE Turing machine decides 3-SAT on n variables, for all n, within C·2^{C·n/(log₂(n+2))^c} steps, or A·2^{δn} for every δ > 0
- `ClauseBoundStatement`: The statements: ONE machine counts the satisfying assignments of a k-CNF with m clauses, for all k and m, within a bound in k·m
- `FixedWidthVariableBoundStatement`: Counting the satisfying assignments of a k-CNF on n variables within 2^{O(n·r(n))}, for a fixed width k: the definitions
- `UniformInKStatement`: The statement: one machine counts the satisfying assignments of a k-CNF, for all k, within 2^{O(k²·n·log log n/√(log n))} steps, and within the smaller of this and 2^{O(k·m/√(log m))}
- `MainTheoremFormsStatement`: Theorem 1, Corollary 11 and Theorem D (b), in the paper's wording
- `PaperSentencesStatement`: Theorem 2, Definition 6, Corollaries 5 and 6, and the counting bound of Theorem C, as Lean propositions
- `ThmEveryDeltaStatement`: Theorem 2: for every constant δ > 0, 3-SAT on n variables can be decided in time O(2^{δn})
- `EightSquareStatement`: Lemma 2 from the eight-square identity: definitions and statements only
- `ParityChecksStatement`: Parity checks (pure mathematics; imports Mathlib only): definitions of Step 1 of Appendix D (σ_i, η, good checks, tuples of marks), and statements on a choice of the checks by conditional expectations that differs from its Step 2
- `LevelsStatement`: The schedule of levels of Theorem A and part (a) of Theorem A (pure mathematics; definitions and statements only; imports Mathlib only)
- `PiecesStatement`: Pieces with parameters (ρ, c), and blocks of bits (pure mathematics; definitions only; imports Mathlib only)
- `PartitionStatement`: Statements on the number of partitions (pure mathematics; definitions and statements only; imports Mathlib only)
- `AppRunningTimeStatement`: Appendix A: pieces with parameters (ρ, c) (Definition 7), the grouping step and two size bounds of Lemma 8, Theorem A on the general recursion
- `AppHalfPiecesStatement`: Appendix B: the ring V = ℚ[t₁, t₂, …], its operators a[r] and Q_s(a,b), the two lemmas on them, and the pieces with ρ = 1/√2
- `AppVariablesStatement`: Appendix D, Steps 1 and 2, as printed: parity checks, the cut-off lemma, the family of checks, the search for the checks
- `CircuitLowerBoundStatement`: The statement of the circuit lower bound for E^NP (Section 7): E^NP does not have circuits of linear size
- `CircuitLowerBoundInfinitelyOftenStatement`: The circuit lower bound for E^NP (Section 7) with «infinitely many lengths» written out
- `GraphProblemsStatement`: The statement of Corollary 7: counting in graphs
- `ClausesOccurStatement`: The bound in the number m of clauses, for formulas over arbitrary names of the variables
- `CliqueLevelsStatement`: «One deterministic algorithm, given ℓ ≥ 0, λ, B ≥ 1 and query access to tables with |W_w| < 2^B, outputs the value of the (K_ℓ, λ)-clique within 2^{e_ℓK_ℓ²λ}·(K_ℓ(λ+B))^{C₀K_ℓ²} operations»
- `KSatFreeCodeStatement`: Definition 6 with a code of the formula that does not mention k (definitions only)
- `PiecesCountedStatement`: Pieces with parameters (ρ, c), with «one algorithm … within 2^{cλ} operations»
- `PrintedStatement`: «Achievable» as printed, and what the paper derives from it and for it (definitions and statements only)
- `GivenStatement`: A «network on J with parameters P, B, τ», given by procedures: one definition (definitions and statements only)
- `VariablesFixedWidthStatement`: The bound in the number n of variables, for fixed k
- `PiecesFromEightSquaresStatement`: Appendix A: the pieces of Lemma 2 are pieces with parameters (11/12, c)
- `CountedInstanceStatement`: The hypothesis of Theorem D (a) holds for the recursion of Theorem A (b) on the pieces of Appendix B, in counted operations

## machines/ : the model of computation (the declarations of the first two folders are in the namespace `Groundwork`)

- `StepMachines` (43 files): algorithms as machines cut into steps: the combinators, ranges, codes, the programs on networks
- `ToTuring` (46 files): certificates of polynomial time; from a machine cut into steps to one of Mathlib's Turing machines
- `QueryMachines` (7 files): machines with query access: own steps and queries counted (the unit of cost of Section 3)
- `Wrap` (8 files): a machine around a machine: front end, simulation, last step
- `TwoMachines` (2 files): two machines run in alternation, or one chosen by a test
- `Tower` (12 files): one machine with query access for a recursion whose depth is part of the input

## networks/ : Sections 3 to 5

- `Groundwork` (12 files): networks on a grid, crossings, the value of a network
- `Paper` (8 files): Definitions 1 and 4; the main text in its order, for the variant of the pieces made from single bits
- `SingleBitPieces` (7 files): Lemma 1, Proposition 3 and Section 6 with the constants of the paper, for a variant of the pieces of Lemma 2 that the paper does not print (made from single bits, ρ = (log 12)/4)
- `Eight` (65 files): the eight-square identity, Definitions 2, 3, 5, Lemmas 1 and 2, Proposition 3, Section 6, Algorithm 1, and Corollaries 5 to 7 and the circuit lower bound of Section 7 on these
- `Value` (7 files): proof of Lemma 1, «so the value equals Z»
- `Variance` (4 files): proof of Lemma 1, the variance from the printed counts
- `Coding` (11 files): the printed objects of Sections 3, 5 and 6, and how the objects that the Lean proofs use arise from them by padding

## threesat/ : Sections 6 and 8

- `Exits` (10 files): a loop that can be left early; Algorithm 1 line by line; Theorem 2 on it
- `Suffices` (5 files): proof of Theorem 2, «it suffices …»
- `Enumerate` (3 files): Lemma 4 as an enumeration
- `ThreeSatOnTree` (2 files): Theorem 2 on the tree of Lemma 4
- `ThreeSatPrinted` (2 files): Theorem 2 through the printed proofs of Lemmas 1, 2 and Proposition 3
- `Printed` (20 files): Section 3, Proposition 3, Section 6 and Algorithm 1 from Definition 4 as printed: a table query costs one operation
- `Given` (3 files): Definition 2 as one property of a network (clause (iii): at most τ operations, each a polynomial-time step or a query), and Proposition 3, Section 6 and Theorem 2 from it; the index's main entries for these point here

## consequences/ : Section 7

- `WidthK` (5 files): k-SAT, s_k, SETH (Definition 6, Corollary 5)
- `CountKSat` (11 files): #k-SAT (Corollary 6); the host machine for outputs that are words
- `CountKSatRate` (10 files): the padding machine, exhaustive counting, rates for #k-SAT
- `GraphProblems` (13 files): Corollary 7: counting in graphs
- `CircuitLowerBound` (28 files): Section 7, the paragraph «Circuit lower bounds»: E^NP has no circuits of linear size, proved in Lean; one step of any machine as a table
- `Occ` (2 files): variables that do not occur in a formula
- `SplitCount` (11 files): Corollary 6 in the order of its printed proof (the index says what differs)
- `SplitSat` (9 files): Corollary 5 by the reduction that its printed proof describes (the index says what differs)
- `FreeCode` (10 files): k-SAT on a code of the input that does not depend on k
- `SizeCircuit` (11 files): proof of Corollary 7: the circuit that tests the size of a set
- `Complement` (5 files): proof of Corollary 7: cliques and vertex covers
- `Sat3Graph` (9 files): the five decision problems of Corollary 7 from 3-SAT alone (the first paragraph of its proof)
- `ThmCount` (6 files): Theorem C from Theorem D (b)
- `Consequences` (4 files): Corollary 7, the circuit lower bound for E^NP and the sentence on NSETH, from the folders above
- `FromPrinted` (12 files): Section 7 on the machines of proof/threesat/Printed
- `PrintedOrder` (5 files): three places of Section 7 and Appendix C where a sentence of the printed proof is made a step of the proof of the corollary or theorem in question

## sparsification/ : the sparsification lemma, Appendix C

- `SparsifyWidthK` (9 files): the branching rule for clauses of width k, on finite sets and as a program
- `SparsificationLemma` (33 files): Lemma 4 as a machine and as a walk; the changed sparsification algorithm of Appendix C with Calabro's thresholds
- `UniformInK` (25 files): one machine and one constant for all widths k
- `StepSparsify` (8 files): Step 5 of Appendix D (sparsification) for any thresholds that serve

## rates/ : Appendices A and B

- `PaddedDescent` (61 files): an algorithm for 3-SAT with a rate, as a polynomial-time function of the input and of a string of blank symbols given with it as a budget of time: walk of the sparsification tree, marks and layers, rebalancing, descent through the levels, exhaustive search at the bottom; certificates and arithmetic
- `ClauseBound` (129 files): the recursion on pieces, the operators behind the pieces with 1/√2, the bound in the number m of clauses
- `GeneralPieces` (77 files): Appendices A and B, statement by statement (Definition 7, Lemma 8, Theorems A, B, Lemmas 9, 10)
- `OccurM` (8 files): Theorem A (c) for formulas in which variables need not occur
- `PiecesCounted` (10 files): Definition 7 and Theorem B with operations counted
- `ExplicitCost` (11 files): Lemma 8 with operations counted
- `CountedToPadded` (12 files): from counted operations to a budget of time given as a string of blank symbols: Theorem A (b) and the hypothesis of Theorem D (a) for machines with query access
- `PiecesFromEightSquares` (1 file): the pieces of Lemma 2 as pieces in the sense of Definition 7, and the rate that Theorem A gives with them
- `CountedRecursion` (60 files): Theorem A (b) with operations counted: one machine for all levels, its run and its cost, along the printed proof

## variables/ : Appendix D

- `VariableBound` (76 files): Appendix D: Lemmas 12, 13, Steps 1 to 4, the bound in the number n of variables; the renaming of variables
- `SparsifyThenCount` (9 files): sparsification with the thresholds of Step 5 and the count of each output, in one function
- `RecursionWithPieces` (4 files): sparsification and the count of each output in one function, on the recursion of Appendix A with the pieces of Appendix B
- `RecursionToBound` (13 files): Theorem D (a) along Step 5 as printed
- `PairsToBound` (7 files): Theorem D (b) from (a), Step 6
- `FixedWidthSteps` (8 files): Theorem A for a fixed width: the steps (the end theorems are in the namespace FixedWidth)
- `CountedInstance` (2 files): the recursion of Theorem A (b) on the pieces of Appendix B meets the hypothesis of Theorem D (a)
- `ThmVariables` (5 files): Theorem D with operations counted

## maintheorem/ : the Main Theorem

- `MinOfBounds` (4 files): Corollary 11 from Theorem A (c) and Theorem D (b)
- `MainRoute` (6 files): the chain from the pieces to the Main Theorem for every machine that is made in the printed way; it follows the order of the paper's proof, with the differences listed at the head of the index
- `WidthThree` (1 file): the algorithm for all widths, run at width 3
- `NamesInOrder` (5 files): the Main Theorem for formulas on the variables x₀, …, x_{n−1} (the paper's x_1, …, x_n), each of which occurs, and the step to arbitrary names
- `CountedRoute` (2 files): the Main Theorem from Theorem A (b) with operations counted; it follows the order of the paper's proof, with the differences listed at the head of the index

## The proof of the Main Theorem, by name

- Theorem B: the pieces with ρ = 1/√2: `PiecesCounted.halfPieces`
- a sentence after Definition 7: «We may and do assume c^row_i, c^col_i ≤ 2λ»: `PiecesCounted.mayAssume`
- Theorem A (b), with operations counted on a machine with query access: `ExplicitCost.recursionSolves`
- Theorem A (a): the numbers of (40) meet the clauses on numbers of the hypothesis of Theorem D (a): `CountedInstance.thePairsMeetTheClauses`
- Theorem D (b), first sentence: the pairs of (40) satisfy the hypothesis of Theorem D (a): `CountedInstance.theRecursionMeetsTheHypothesis`
- not in the paper: from counted operations to a solver, a function of input and pad (with e_ℓ replaced by a computed e′_ℓ in [e_ℓ, 2e_ℓ], cut at 1, and C₀ by 2C₀ + 1): `QueryMachines.Bridge.solverOfMachineLevels`
- Theorem D (a), for the program of the line above, which is given the tables written out and a pad, and for every machine that computes the counting function built on it: `RecursionToBound.thmVariablesAForEveryMachine`
- Step 6 of Appendix D: the bound of Theorem D (b): `PairsToBound.everyChoiceMeetsThmVariablesB`
- Theorem A (c), first sentence, at α′ = ½: the bound in m, with a polynomial in the length of the input added: `MainRoute.boundInMOnEverySolver`
- the bound in m with nothing added: `NamesInOrder.boundInMWithoutThePolynomial`
- Corollary 11: the two machines run in alternation: `NamesInOrder.everyDirectAlternationMeetsTheBound`
- all of this for every solver: both bounds, and every machine assembled directly has the bound of the Main Theorem: `NamesInOrder.onEverySolver`
- the same for every machine with query access: `CountedRoute.onEveryMachineWithQueryAccess`
- the same on the machine of Theorem A (b): `CountedRoute.onTheCountedRecursion`
- Theorem 1 (Main Theorem), as MainTheoremFormsStatement.lean states it, read off the line above: `CountedRoute.mainTheoremHolds`
- Theorem 1 (Main Theorem), as MainResults.lean states it: `MainResults.mainTheorem`
- towards ETH: the Main Theorem for any names of the variables: `NamesInOrder.generalFormFollowsAsPropositions`
- one machine that decides 3-SAT within c·2^{δn} steps for every δ > 0: `Wrap.countingBoundImpliesFailureOfETH`
- ETH is false (in the form of Theorem 2, s₃ = 0; also stated in Corollary 5), as MainResults.lean states it: `MainResults.ethIsFalse`

## Words used in the comments

- **pad**: An extra input to a program: a list of units (type `U`, a number in unary). Every exponential loop is cut off at the length of the pad, so the programs are polynomial-time in the length of input and pad; a bound of T operations in the paper becomes «right as soon as the pad has at least T units», usually written as 2^(exponent) units (before Theorems D (a) and A (c) are applied, a somewhat larger number; see the head of the index of the paper's statements). (see `proof/statements/AppRunningTimeStatement.lean`)
- **certificate**: A proof that a function is polynomial-time: `PolyT f` (proof/machines/ToTuring/PolyT.lean), or `Unary f` when the number f x is computed in polynomial time written in unary (so it is polynomially bounded). Certificates are proved function by function, each for arguments that are themselves polynomial-time functions of a context x, so that they compose (e.g. proof/variables/VariableBound/Net/CertNet.lean). (see `proof/machines/ToTuring/PolyT.lean`)
- **step machine**: Lean's rendering of the paper's count of operations (`Groundwork.Stepped`, `Paper.StepMachine`; best read in proof/networks/Paper/SecNetworks_Model.lean): a type of states, a start, a step function and an output, with «X operations» read as X steps. A step may be any Lean function, so a count of steps means something only together with `PolyTimeSteps` (each step polynomial-time on Mathlib's Turing machine) and states of polynomial size (in Definition 7 the bound on the states is exponential in λ; see the head of the index of the paper's statements); `steps_to_time` then turns steps into Turing-machine time. (see `proof/networks/Paper/SecNetworks_Model.lean`)
- **interface statement**: A lemma stated as a proposition, a definition named `St…` (mostly in Defs or Interfaces files). One file proves it as a theorem `st…` (e.g. `stDecU : StDecU`, possibly from other St… statements); a file that needs it takes `(h : St…)` as a hypothesis (proof/consequences/CountKSat/Interfaces.lean). (see `proof/consequences/CountKSat/Interfaces.lean`)
- **named program**: A specific program given by a Lean definition, such as `Tied.runB` or `RecursionWithPieces.solverAB`. Statements about it assert the property of that very function, rather than saying that some program exists. (see `proof/rates/GeneralPieces/Tied/Defs.lean`)
- **tied**: Said of a form of a statement that names the programs or functions it is about (it is «tied» to them), where the plain form only says that some program or machine exists. The namespace `GeneralPieces.Tied` (proof/rates/GeneralPieces/Tied/Defs.lean) holds such forms of parts (b) and (c) of Theorem A, e.g. the recursion `solveG` on the schedule of display (40); there are tied forms of other theorems too. (see `proof/rates/GeneralPieces/Tied/Defs.lean`)
- **solver**: A clique solver (`ClauseBound.Alg.Solver`): for each index i, a number K i of nodes, a function `run` of (pad, index, instance) meant to output the value of a (K i, λ)-clique, and the exponent `need` of a pad that suffices. Being polynomial-time (`Solver.Poly`) and being right once the pad has 2^need units (`Solver.Correct`) are separate hypotheses. This is the form in which part (b) of Theorem A, and the hypothesis of Theorem D (a), are used. (see `proof/rates/ClauseBound/Alg/Interfaces.lean`)
- **label length**: The number of bits that two nodes of a network share through their labels: c_{a,b} in a general network (U is the sum over ordered pairs), and λ for every pair in a (K, λ)-clique (Definition 3). When a network on g nodes is regrouped into K groups (Lemma 1), the new label length is max 1 ⌊(U + gP/K)/K²⌋ (`beta`, proof/networks/Groundwork/Net/Colouring.lean); the programs use upper bounds of this kind (`lamS`, `lamNextG`). (see `proof/networks/Groundwork/Net/Colouring.lean`)
- **schedule of levels**: The numbers K_ℓ, g_ℓ, ζ_ℓ, e_ℓ of display (40) in Theorem A (`Levels.Gen`, LevelsStatement.lean). The programs turn them into a schedule `sched P x₀ ℓ` (proof/rates/ClauseBound/Gen/Defs.lean): a list of steps, the j-th going from a grid of g_j × g_j = K_{j+1} nodes to K_j nodes, from K_ℓ nodes down to K₀; the recursion runs down it one level at a time. (see `proof/statements/LevelsStatement.lean`)
- **heart, petals**: The heart is the nonempty set H of literals on which a node of the sparsification tree branches; it lies in at least θ(j − |H|) clauses of size j > |H| (the node takes the smallest such j and a largest such H). The petals are these clauses with H removed: the clauses E ∖ H, E ∈ F, of Appendix C. (see `proof/sparsification/SparsifyWidthK/Defs.lean`)
- **heavy child**: In a branching step of the sparsification tree, the child that gets the petals Q = {E∖H : E ∈ F} as clauses; the light child gets the heart H as a clause instead (proof/sparsification/SparsifyWidthK/Defs.lean). In the counting tree (proof/consequences/CountKSat/Defs.lean) the heavy child also puts «every literal of H is false» on its side list, the set 𝒩 of Appendix C, so that no assignment satisfies both children. (In proof/consequences/GraphProblems the words name another branching.) (see `proof/consequences/CountKSat/Defs.lean`)
- **walk**: The depth-first pass through the sparsification (or counting) tree with a stack of nodes: a leaf on top is dropped, another node is replaced by its two children (proof/machines/StepMachines/Prog/Walk.lean). As a step machine it tests the leaves (`walk`) or adds up their counts (`walkSum`); as a function of a pad it runs one round per unit of the pad and adds up (`walkS` in proof/consequences/CountKSatRate/Defs.lean, `walkSG` in proof/sparsification/StepSparsify/Defs.lean). (see `proof/machines/StepMachines/Prog/Walk.lean`)
- **layer**: Lean's networks of marks (proof/rates/PaddedDescent/F/MarkNet.lean; the paper has none: Step 3 of Appendix D uses two kinds of objects instead) take their clauses as a list of formulas, the layers; a profile counts marked clauses layer by layer. In proof/rates/ClauseBound/TopN the clauses are placed one at a time into R + 1 layers chosen so that the layers are good (proof/rates/PaddedDescent/F/MarkLayers.lean); in proof/rates/ClauseBound/ParityChecks the layers are fixed — all clauses, the incidences of the checks and, for B_i, the clauses not yet decided — so three for B_i and two for A and the count. (see `proof/rates/PaddedDescent/F/MarkNet.lean`)
- **reading**: In the generating functions of the proof of Lemma 9 (Appendix B; proof/rates/GeneralPieces/GenF), one of the two ways in which a construction, set up once for an inner variable u and an outer variable v, is used: in the first reading (`rd = false`) u = ω₁, v = ω₂ and the inner family is A; in the second (`rd = true`) u = ω₂, v = ω₁ and the inner family is B. (see `proof/rates/GeneralPieces/GenF/Defs.lean`)
- **word**: The word of a value x (`wd x`, proof/machines/ToTuring/Enc.lean) is the string of symbols that stands for x on a stack of Mathlib's Turing machine; `len x` is its length, and polynomial time (`PolyT`) is measured in it. It is not the machine word of the paper's word RAM. (see `proof/machines/ToTuring/Enc.lean`)
- **cut off**: Every enumeration of exponentially many things runs only up to the length of the pad (`rng`, `sumF`), and every growing state is replaced by a default once its word is longer than the pad (`cap`), so the functions are polynomial-time in (pad, arguments) without side conditions; the proofs show that for a long enough pad no cut-off is active (proof/rates/PaddedDescent/F/Fuel.lean). (see `proof/rates/PaddedDescent/F/Fuel.lean`)
- **exponent function, padding machine**: An algorithm is given as a function A of (input, pad) with an exponent function e of the input: A is right once the pad has 2^(e x) units. The padding machine (`padM`, proof/rates/PaddedDescent/Pad.lean) starts with a pad of one unit, doubles it until it has 2^(e x) units and then applies A, which gives one Turing machine with q·(|x| + 2^(e x) + 1)^q steps when A and e are polynomial-time (`exists_tm_padded`). (see `proof/rates/PaddedDescent/Pad.lean`)
- **OL**: An ending of names and files (`countOL`, `FitsOL`, `StCountOL`, `PbOL`, `MasterOL.lean`), all in proof/rates/ClauseBound/ParityChecks/: the programs, bounds and statements of the bound in the number n of variables (Appendix D). OL stands for «one logarithm»: the exponent n·log log n/√(log n) has the factor log log n only once. (see `proof/rates/ClauseBound/ParityChecks/ProgDefs.lean`)
- **Boson**: The namespace `ClauseBound.Boson` (proof/rates/ClauseBound/Boson/) holds the construction of Appendix B with integer coefficients (the paper takes ℚ): the operators a[r] for a monomial a, each given by its matrix on the monomials in t₁, t₂, … (`op`), built by the recursion (O2) from the multiplications by t_l and the derivations k·∂/∂t_k; the operators Q_s of Lemma 9; the dual families of Lemma 10; and the pieces with ρ = 1/√2 of Theorem B. The paper's own definition of a[r] on ℚ[t₁, t₂, …] is `AppHalfPieces.op` (AppHalfPiecesStatement.lean). The name comes from physics: these operators act on the Fock space of the Heisenberg algebra (Appendix H). (see `proof/rates/ClauseBound/Boson/Defs.lean`)
- **2 (at the end of a name)**: A final 2 has no single meaning. In proof/rates/GeneralPieces/ most names that end in 2 (`LevelOK2`, `ChainG2`, `StSolveG2`, `solveG2`, `child_spec2`) belong to the analysis of the recursion of Appendix A under case (ii) of Lemma 8 (groups of exactly g/K nodes, Hoeffding's inequality); a few (`stValS2`, `stCountG2`, `endO2`) use case (i). Otherwise it is a place in a numbered list (`StN2`, `StY2`, in proof/rates/GeneralPieces/GenF), a second operand (`mul2`) or a second file (`Defs2.lean`). (see `proof/rates/GeneralPieces/Defs.lean`)
- **Groundwork**: The namespace `Groundwork` runs through several groups of folders: proof/networks/Groundwork/ (networks, grids and the crossing), proof/machines/StepMachines/ (step machines), proof/machines/ToTuring/ (the passage to Turing machines), and also proof/consequences/WidthK/ (`Groundwork.DecodeK`, `Groundwork.Prog.SatTopK`, for formulas of width k) and proof/machines/QueryMachines/ (`Groundwork.Stepped`, machines that make queries). (see `proof/networks/Groundwork/Net/Defs.lean`)
- **ChainOn**: For the solver made from a machine E with query access (`solverOfMachine E num C₀`), with fnN = the function of Steps 1 to 5 of Appendix D on it (exhaustive counting below n₁) and fnM = the function for the bound in m on it, each with the exponent of its pad: (1) every machine made from fnN as Step 6 of Appendix D says has the bound of Theorem D (b); (2) every machine that computes fnM has the bound in m, with nothing added; (3) every machine assembled directly (`AssembledDirectly`) from such machines has the bound of Corollary 11, which is that of the Main Theorem; (4) a machine built directly (`BuiltDirectly`) exists. K₀ picks the level (`pickOf kf K₀`) and is the number in the test of Step 6. (see `proof/maintheorem/CountedRoute/Defs.lean`)
- **RouteOn**: For a solver S with levels Q, the function num (a number in [e_ℓ, 2e_ℓ]), a function fm with exponent em for the bound in m, and the threshold n₁: the steps Theorem D (a) → Step 6 → Corollary 11 of the proof, in a form that the paper does not print: the variables are renamed first, and the bounds allow an added polynomial in the length of the input. Every machine that computes the function of Steps 1 to 5 on S has the conclusion of Theorem D (a). Every machine that chooses, as Step 6 says, between a machine with that conclusion and one that tries all assignments has the bound of Theorem D (b). Every machine assembled as printed from these and a machine for fm has the bound of Corollary 11 (also for deciding). Such a machine exists. (see `proof/maintheorem/MainRoute/GeneralDefs.lean`)
- **AssembledDirectly**: N is assembled as the proof of Corollary 11 says, with nothing renamed: for some machine M₂ made as Step 6 says from fa, ea, K₀ (`ChosenAsPrinted`) and some machine M₁ that computes fm with exponent em, N runs M₁ and M₂ in alternation on its input (whenever both put out the same answer, N puts it out within a polynomial in the faster one's time plus the input length). (see `proof/maintheorem/NamesInOrder/Defs.lean`)
- **BuiltDirectly**: `AssembledDirectly`, with every part exhibited: Ma (computing fa with ea), Mb (exhaustive counting), M₂, M₁ (computing fm with em) and N all have finite alphabets; the front end `pre`, which rewrites the input so that its declared width is max(3, largest clause width), and the test of Step 6 with K₀ are polynomial-time; M₂ carries out the named computation `TwoMachines.choose` on codings of Ma and Mb, and N carries out `TwoMachines.alt` on codings of M₁ and M₂. (see `proof/maintheorem/NamesInOrder/Defs.lean`)
- **ChosenAsPrinted**: M₂ is made as Step 6 of Appendix D says: for some machines Ma computing fa with exponent ea and Mb computing exhaustive counting, a front end `pre` that rewrites the input at k = max(3, largest clause width), and the printed test with K₀ (n ≥ K₀^17 and k ≤ (log n)^(1/4)), M₂ chooses by the test between Ma behind `pre` and Mb. (see `proof/maintheorem/MainRoute/Defs.lean`)
- **OnEverySolver**: For every polynomial-time solver S with levels Q and every num computing a number in [e_ℓ, 2e_ℓ] (the hypothesis of Theorem D (a)), there is an n₀ such that, whenever e_ℓ ≤ a/√(log K_ℓ) for all ℓ (a natural), clauses (2) to (4) of `ChainOn` hold for S and every n₁ ≥ n₀, with `RecursionToBound.count` and `ClauseBound.Alg.AM` on S as the two functions. (see `proof/maintheorem/NamesInOrder/Defs.lean`)
