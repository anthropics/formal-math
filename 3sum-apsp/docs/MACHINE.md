# The machine, the language and the programs

The paper proves sentences of the form "… can be computed deterministically in time O(…)" on a word RAM. This guide explains how these sentences are stated and proved in this formalization. It is written for a reader who holds the paper and has not seen the code.

**Only Part 1 has to be read in order to believe a statement.** Parts 2 and 3 describe the proofs, which Lean checks.

* **Part 1** describes the machine, what it means to solve a problem on it, how the inputs are laid out, and what a skeptical reader should check.
* **Part 2** follows a proof from a claim down to the machine, and describes the small programming language in which the programs are written and the compiler to the machine with its proof.
* **Part 3** goes through the programs: which programs stand behind which statement, how their routines correspond to the steps of the paper, where they depart from the paper's description and why, which further steps they pay for, and what is known about the constants.

No bound of the paper changes. The bounds in the statements are those that the paper prints, `docs/REMARKS.md` records where the Lean text departs from the wording of the paper, and Part 3 is about the way in which the programs reach the bounds.

`README.md` explains the words statement, library and lemma. `docs/INDEX.md` names the statements for each item of the paper and says where they are proved. `docs/PROGRAMS.md` lists the programs and the lemmas about them, item by item, and `docs/FILES.md` lists every file of the library with the title of its header.

## Part 1. The machine and the statements

The running-time sentences of the paper are stated in two places, about one machine. `EndStatement.lean` defines the machine, gives a short definition of "solved in time O(n^r)", writes down five problems and states five claims; it imports nothing. `PaperStatements.lean`, which stands beside it, has 25 statements about the same machine, called here the statements about programs, which follow the paper item by item with the bounds as printed. A theorem such as `wordRam_theorem_5` says that the proposition `Items.Theorem_5` holds. These propositions are in the section "The word RAM: running times" of `PaperStatements.lean`, each with the sentence of the paper that it renders. What solving means and how the inputs are laid out is defined in its section "The word RAM: problems".

### References and letters

"Theorem 5", "Section 2.4.4" and "(8)" refer to the paper; (8) and (9) are its two displayed cost expressions in Theorem 30. Letters have the paper's meaning, and quotations have the paper's letters; the table lists the exceptions. ε* = ln 4/(5 ln 10) is the number defined before Theorem 24, and "log" is the natural logarithm.

| the paper's letter | Lean's letter | meaning |
|---|---|---|
| ν | `κ` | the exponent of the bound n^ν on the numbers of an input (Sections 3 and 5); this guide writes κ |
| — | `c`, `c₀` | the exponent of the bound N^{O(1)} on the entries of the matrices (Sections 2 and 4); this guide writes κ here too |
| κ | `κ` | in Section 4 and in Theorem 1: the exponent in \|W\| ≤ N²/D^κ |
| w | `η` | an output string of Section 4; this guide writes w |
| — | `U` | a bound on the absolute values of the numbers of an instance (in the hinted problems of Corollary 40, U is also the name of a matrix) |
| — | `b` | the slope of the word size |

### The machine

Memory cells are named by integers, negative ones included, and hold words of a fixed number of bits, the word size. A word is read as a signed number in two's complement wherever a sign matters.

A program is a finite list of instructions (`Instr`). There are nine instructions:

* put the constant 1 into a cell;
* add, subtract or multiply two cells (three instructions; the result wraps around);
* load from, or store to, the cell whose name is the signed value of a given cell (two instructions);
* continue at a fixed position of the program if a given cell is negative;
* accept;
* reject.

An instruction names its cells by integers in the text of the program. Every instruction takes one step, the halting one included, and a position outside the program counts as reject. `exec P t pc m` is the verdict and the final memory if the program P, run from the position pc on the memory m, halts within t steps. At the start the input stands in the cells 0, 1, 2, …, one number in each cell, and every other cell holds 0 (`loadWords`).

### Where the machine is weaker than the standard word RAM

The machine is weaker than the standard word RAM in three respects, so in these respects an upper bound on time proved for it is stronger.

* There is no division, no shift and no bitwise operation.
* The only constant is 1. The numerals in a program's text name cells and positions in the program; they are never used as values. So a constant k has to be built, in about log k steps.
* The program does not choose the word size.

**What a program cannot do.**

* A program is a finite list of instructions. In every statement it is chosen before the input and before the size of the input, so it cannot contain answers that depend on them.
* Every cell outside the input holds 0 at the start, so there is no advice in the initial memory. A program may use any cell, also the negative ones, but it reaches a cell whose name is not a numeral of its text only through a word that holds the name.
* One step writes at most one cell.

### Where the model is generous, and what is defined twice

The machine is as generous as the standard word RAM in two respects.

1. A multiplication of two words takes one step.
2. Every cell whose name fits into a word can be addressed.

On four further points the machine is generous; none of them changes an exponent.

3. Every cell outside the input, with a positive or a negative name, holds 0 at the start, and `Solves` charges no space, so a table that is addressed directly by a number costs nothing to set up (on a machine without this, lazy initialization costs a constant factor). The definition of a data structure below says how space is measured there.
4. The finitely many cells that a program names in its text are arbitrary integers and need not be addressable by a word.
5. The slope b of the word size is chosen after the exponent κ of the magnitude of the numbers.
6. The inputs of phases and the queries arrive at no cost.

**Defined twice.** The following notions are defined twice: in `EndStatement.lean`, with Lean's core library only, and again with Mathlib, mostly because the paper uses them also over the real numbers and for rectangular matrices. For each notion a statement says that the two definitions agree; these statements are the section "Agreement with the definitions of EndStatement.lean" of `PaperStatements.lean`.

| notion | in `EndStatement.lean` | with Mathlib | the statement that the two agree |
|---|---|---|---|
| a program solves a problem | `Problem`, `Problem.SolvedBy` and the word sizes of `Problem.SolvedInTime`, for one size n | `Problem`, `Admissible`, `output` and `Solves`, for several sizes | `agreement_solves` |
| O(n^r) | `BigO`, for a rational exponent and from n = 2 on | `IsBigOPow`, for a real exponent and all large n | `agreement_bigO`, for r ≥ 0 |
| solved in time | `Problem.SolvedInTime` and `BigO` | `SolvesWithin`, `SolvedInTimeAt` and `SolvedInTime`; "The five claims and the other statements" below compares the two | `agreement_solvedInTime`, for a rational exponent r ≥ 0 and no logarithmic factor |
| Exact Triangle | `EndStatement.ExactTriangle` | `TriangleInstance.HasZeroTriangle` | `agreement_exactTriangle` |
| the (min,+)-product | the output of `EndStatement.MinPlusProduct` | `IsMinPlusProduct` | `agreement_minPlusProduct` |
| APSP | `EndStatement.Path` and `EndStatement.APSP`, where a missing edge is `none` | `walkWeight`, `NoNegativeCycle` and `IsDistanceMatrix`, where it is ⊤ | `agreement_apsp_noNegativeCycle` (the promise), `agreement_apsp_output` (the output) |
| a matrix written row by row | `EndStatement.rowByRow` | `rowMajor` | `agreement_rowByRow` |
| the weight of a k-clique | the sum in `EndStatement.ZeroWeightKClique` | `cliqueWeight` | `agreement_cliqueWeight` |

The bound `Within` on the steps of a phase is not compared with `BigO`.

**Names that occur twice.** `Theorem_19` is a claim of `EndStatement.lean` and a proposition `Items.Theorem_19`. `Solves` is said of programs of the machine (below) and of procedures of the language (Part 2).

### The word size

A statement fixes, together with the program, a number b, the slope. The program then has to work, within the same bound on the number of steps, at every word size that is at least b · (1 + ⌊log₂ p₁⌋ + ⌊log₂ p₂⌋ + …), where p₁, p₂, … are the sizes of the instance (`Admissible`; the table of layouts says which numbers count as sizes). The smallest admissible word size is a constant times the logarithm of the size, which is the paper's "O(log n)-bit words". Since the bound on the steps has to hold there, a program gains nothing from longer words. The definitions do not ask that the numbers of the input fit into a word, so the b that comes with the program has to be large enough for that.

### Problems, and what solving means

Two structures are called `Problem`. The one of `EndStatement.lean` has one size n: it consists of the instances of each size, the list of numbers that is the input, a condition that says when to accept, and a condition on the output cells. The one of `PaperStatements.lean` is more general: it consists of the instances, their sizes, the list of numbers written into the memory, and a predicate that says which verdicts and output cells are correct answers. The output cells are the cells right after the input, read as signed words (`output`).

`Solves prob P b dom T` is the definition of solving for a single program. For every instance x that satisfies dom and every admissible word size, the run of the program P from its first instruction on the starting memory gives a verdict within T(x) steps, and the verdict and the output cells are a correct answer.

`SolvesWithin Q κ P b T` is the definition of solving for a problem Q of the first kind. It is what `Problem.SolvedInTime` asks of the runs of P, for a real bound T: on every instance, of any size n, whose input numbers have absolute value at most n^κ, and at every word size of at least b (⌊log₂ n⌋ + 1) bits, P halts within T(n) steps with the right verdict and output (`Problem.SolvedBy`).

* The size n is the only size, and it stands in cell 0 in front of the input.
* The verdict has to be accept exactly if the answer is yes, and the output has to be right.
* The bound speaks of every number of the input list, so the entries 1 of an adjacency matrix count too. This costs nothing, since n^κ is at least 1 as soon as there is a vertex.

Four short forms cover the bounds in one size. Each takes a problem Q of the form of `EndStatement.lean`.

* `SolvedInTimeAt Q κ a e`: there are a program, a slope and a constant C such that the program solves Q, at every size n, 0 included, within C (n^a (log n)^e + 1) steps (`SolvesWithin`). For a ≥ 0 the "+ 1" matters only at n ≤ 1, where n^a (log n)^e may be 0.
* `SolvedInTime Q a e`: the same for every natural number κ, which is the paper's "integers of absolute value n^{O(1)}" (Theorem 2). The program, the slope and the constant may depend on κ. A real κ is covered by rounding up, since n^κ is only a bound. This is how "O(n^a (log n)^e)" is read.
* `SolvedInPolylogTime Q a`: the exponent e may depend on κ as well; this is "Õ(n^a)".
* `SolvedInLittleOTime Q a`: the bound is C (n^{a + o(n)} + 1) for a function o that tends to 0 and may depend on κ; this is "n^{a+o(1)}".

**Data structures.** `IsDataStructure` is the definition for the two-stage data structures of Section 4. It speaks of a preprocessing program, a query program and three cells through which queries are put and answered, all fixed before the instance. A version in which the data structure may be an arbitrary mathematical function would be vacuous, since it could be the map (I, J) ↦ (XY)[I, J] itself.

* The preprocessing accepts within its time bound.
* It leaves unchanged every cell that lies more than the space bound before or after the input.
* After that, every finite sequence of queries (I, J) with I, J < N is served, each within the query bound (`Serves`). A query starts at the first instruction of the query program, on the memory that the previous run has left, with I and J written into two of the cells (`withQuery`). It accepts and leaves the entry (XY)[I, J] in the third cell. Nothing is reset between queries.

So "space" is the extent of the memory in which the structure lies, not the number of cells written, which is at most the time in any case. A structure scattered over a large range of addresses does not count as small. Cells that the preprocessing restores, and cells that the queries write, are not constrained.

**Phases.** `RunsPhases` is the definition for problems whose input arrives in phases. It takes a list of phases, each with its own program, its input and a number of steps.

* When a phase begins, its input is written into the cells that follow the inputs of the earlier phases (`withInput`), and its program starts at its first instruction on the memory that the earlier phases have left.
* Each phase has to accept within its number of steps. The first phase starts on a memory of zeros, and the output is read from the cells after the last input.
* So a program cannot see the input of a later phase, and whatever it writes into the cells reserved for that input is overwritten.
* Receiving an input costs no steps. The running times of Corollary 40 do not depend on this: the proofs take the saving γ of "General τ" at most 1 (the statement asks only for γ > 0), and then the bound of a phase is at least the length of its input.
* `Within s C n a` says that the number s of steps is at most C (n^a + 1).

### The layouts

Matrices are written row by row, one number per cell (`rowByRow`, `rowMajor`). Booleans are written as 0 and 1 (`bit`), and indices and vertices count from 0. The first cells hold the sizes. A program for a problem with an output has to accept, and to leave the output in the cells right after the input.

| problem | sizes | input cells | correct answer |
|---|---|---|---|
| `thinProduct`, the wanted entries of a thin product | N, D | N, D, \|W\|, extra, X (N × D), Y (D × N), the rows of the positions of W, then their columns (`ThinInstance.input`) | accept; output cell i holds (XY)[Iᵢ, Jᵢ] |
| `lopCount`, `lopDetect` (#Lop-AE-SparseTri and Lop-AE-SparseTri, Section 3.1) | N, D | the same without extra, with the two biadjacency matrices as X and Y and the query pairs as W | accept; output cell i holds the number of triangles through the i-th query pair, or, for `lopDetect`, 1 if the pair lies in a triangle and 0 if not |
| the data structure | N, D | N, D, extra, X, Y (`ThinPair.input`) | see `IsDataStructure` above |
| `ExactTriangle` | n | n, the matrices w(a,b), w(b,c), w(a,c) | accept if there is a zero triangle, reject if not |
| `ThreeSum` | n | n, x₀, …, x_{n−1} | accept if three numbers at distinct places sum to 0, reject if not |
| `MinPlusProduct` | n | n, A, B (integer entries, no +∞) | accept; the n² output cells hold the (min,+)-product |
| `APSP` (directed graphs; an instance has no negative cycle) | n | n, the adjacency matrix, the weights (0 where there is no edge) | accept; two output cells for each pair (i, j): 1 and the distance, or 0 and anything if j cannot be reached from i. Every vertex reaches itself at distance 0. |
| `ZeroWeightKClique k` | n | n, then an n × n matrix of weights for each of the k² ordered pairs (i, j) of parts. Only the blocks (i, j) with i < j count, and the other blocks may hold any numbers within the bound. | accept if some k vertices, one in each part, have total edge weight 0, reject if not |
| `GraphExactTriangle` | n | n, the adjacency matrix, the weights (0 where there is no edge) | accept if three pairwise adjacent vertices have edge weights that sum to 0, reject if not |
| `MinKClique k`, `MaxKClique k` (n ≥ 1) | n | as `ZeroWeightKClique k` | accept; the k output cells hold the vertices, one in each part, of a k-clique of minimum (maximum) total weight; every such clique is accepted |
| v-hinted Mv (`AchievesVHinted`) | n | Phase 1: n, t, M (n × t); Phase 2: V (t × n); Phase 3: i | n output cells: the product of M and column i of V |
| Mv-hinted Mv (`AchievesMvHinted`) | n | Phase 1: n, t, N (n × n), V (t × n); Phase 2: I (t indices); Phase 3: j | n output cells: N_{[n],I} V_{[t],j} |
| uMv-hinted uMv (`AchievesUMvHinted`) | n | Phase 1: n, t₁, t₂, U (n × t₁), N (n × n), V (t₂ × n); Phase 2: I (t₁ indices); Phase 3: J (t₂ indices); Phase 4: i, j | one output cell: the entry (i, j) of U N_{I,J} V |

`ExactTriangle`, `ThreeSum`, `MinPlusProduct`, `APSP` and `ZeroWeightKClique` are the five problems of `EndStatement.lean`. The statements about programs speak of them through `SolvesWithin`. `GraphExactTriangle`, `MinKClique` and `MaxKClique` are further problems of the same form, defined in `PaperStatements.lean`.

"extra" stands for the three numbers m, L, t in Theorem 30 and for nothing elsewhere. The set W is given as a list without repetitions. The bound on the absolute values of the numbers is not written into the memory. For the matrix problems it is a number U that is part of the instance as a mathematical object (`ThinPair`); for the problems in the form of `EndStatement.lean` it is a hypothesis of `SolvesWithin`. In every statement it is the size raised to an exponent that is fixed before the program, and it is 1 for the 0/1 matrices of the lopsided triangle problems (`ThinInstance.ZeroOne`).

In the hinted problems of Section 5.4 the matrices are Boolean and the products are over the Boolean semiring. The hint dimension is t = ⌊n^τ⌋ (`hintSize`), where the paper treats n^τ as an integer. Since t is part of the input, no program has to compute n^τ. Each of the three definitions says that there are one program for each phase, a slope, a constant C and an exponent a₁ with the following property. For every n ≥ 1, all inputs of all phases and every admissible word size, the phases run and the output is right. The first phase takes at most C (n^{a₁} + 1) steps, and each later one at most C (n^{aᵢ} + 1) steps.

### The order of the quantifiers

In every statement the choices are made in this order:

1. the constants of the problem (the exponent κ of the bound on the numbers, the k of k-Clique, the τ of the hinted problems);
2. the program or programs, the slope and the constant of the time bound;
3. the instance;
4. the word size, which may be any admissible one.

So a program cannot depend on the instance or on its size, it can contain answers for finitely many instances only, and it cannot rely on long words.

In the statements on the data structure for D ≤ N^ε the real parameters of Corollaries 31 and 32 come first (c, θ, ε, q, and the κ of Corollary 32, which is not the exponent of the bound on the numbers). Then, where the paper has "there is a γ", comes the number γ, then the exponent of the bound on the entries. After these come the programs, the slope and the constant, and last the instance and the word size.

The programs for the hinted problems are deterministic and the statements are about all inputs, which covers an adaptive adversary. The polynomial Phase 1 cannot prepare all answers. In v-hinted Mv an answer depends on M and on one column of V, which has 2^t possible values, more than any polynomial in n, since τ > 0 is fixed first. In the other two problems there are n^t, and n^{t₁} and n^{t₂}, possible hints.

### The five claims and the other statements

The five claims are `Theorem_19`, `Theorem_22_3SUM`, `Theorem_22_MinPlus`, `Theorem_22_APSP` and `Corollary_39_ZeroWeight`, in terms of `Problem.SolvedInTime`, `Problem.SolvedBy` (what is asked of a single run) and `BigO`. The theorems `endStatement_…` of `Challenge/EndStatement.lean` say that they hold, and `README.md` introduces them.

**What is the same** in the five claims and in the statements about programs: the machine, the starting memory, the output cells, the rule for the word size (at least b (⌊log₂ n⌋ + 1) bits, chosen after the program), the order of the quantifiers, and the five problems themselves. Both have every natural number κ, 0 included, as the exponent of the bound on the numbers, where the paper has ν ≥ 1 in Theorem 19 and Corollary 39. Both have every size n, 0 included, in the statements with one size (an instance of Min-Weight or Max-Weight k-Clique has at least one vertex in each part, so that a clique exists).

**What differs** is the form of the time bound. In the five claims it is a function T of n with natural values and T(n)^q ≤ K n^p for n ≥ 2, where p/q is the exponent. In the statements about programs it is at most C (n^a (log n)^e + 1) steps, with a real a. For e = 0 and a = p/q ≥ 0 the two forms say the same (`agreement_solvedInTime`).

The condition on T says nothing about T(0) and T(1), but these are two fixed numbers, so nothing is given away. In their bounds the five claims ask less than the other statements, which have the sharper exponents and the logarithms. So each of the five claims follows from a statement about programs by arithmetic on the form of the bound.

**The two numerals of Theorem 22.** Theorem 22 prints two numerals for each of its problems: one for the algorithm that uses Theorem 5 (1.99923 for 3SUM, 2.99949 for the other two) and one for the algorithm that uses Corollary 26 (1.9992 and 2.99942). Each claim is proved with the algorithm to which its numeral belongs. All five claims go by the route through Corollary 26: they follow from `wordRam_theorem_19` (third bound), `wordRam_theorem_22_second` and `wordRam_corollary_39_zero`. The numerals of the route through Theorem 5 are stated in `wordRam_theorem_22_first`.

**Statements that follow from others.** As statements about the existence of programs, the bounds by the route through Theorem 5 follow from the smaller bounds by the route through Corollary 26. This implication is not stated in Lean. The bounds are proved by both routes of the paper, each with its own programs.

**What the statements about programs have beyond the five claims:** the logarithmic factors and all printed bounds of Theorems 19 and 22, with the bounds for 3SUM before rounding in `Items.Theorem_22_threeSum`; the statements with the two sizes N and D; the data structures; the problems in phases; the minimum-weight and maximum-weight cases of Corollary 39; Exact Triangle on n-vertex graphs (`Items.Theorem_2_graphs`; `Items.Theorem_2` has the tripartite form). The short definition of `EndStatement.lean` has one size, a rational exponent and no logarithm, so these sentences cannot be said in its terms.

**No cited result is assumed.** No statement about programs has a cited result among its hypotheses. The reductions of [CH20], [VW13] and [VW18] that Theorem 21 and Corollary 39 cite are written as programs, with proofs.

**"The conjecture fails."**

* `Items.Corollary_40_fail` says that Conjectures 5.2, 5.7 and 5.12 of [vdBNS19], read as statements about programs of this machine, are false for every 0 < τ < τ₀ (τ₀ is a parameter of the proposition; the statement has it for τ₀ = 1/18 and for τ₀ = ε*; for 5.12: 0 < τ₁ < τ₀ τ₂ and τ₂ < 1). This holds whatever real number ω ≥ 2 stands in the place of the exponent of rectangular matrix multiplication (for 5.12: whatever numbers ω₂ ≥ 2 and ω₃ ≥ 1 + τ₂).
* A conjecture is read as in `PaperStatements.lean`, "Section 5: definitions": for every ε > 0 the exponents ω − ε and 1 + τ − ε (for 5.12: ω₂ − ε, ω₃ − ε and τ₁ + τ₂ − ε) are not achieved together.
* The exponents ω(1, 1, τ), ω(1, τ₁, 1) and ω(τ₂, τ₁, 1) themselves are not defined in this formalization. What remains outside is the sentence of Corollary 40 that they are at least 2, and at least 1 + τ₂, "because of the input and output sizes".

### What a skeptical reader should check

1. The definition of the machine at the beginning of `EndStatement.lean`: `Instr`, `exec`, `loadWords`. For the five claims, only the rest of that file has to be read as well.
2. For the statements about programs, read the two sections of `PaperStatements.lean` on the word RAM; the first begins with a list of the 28 definitions of Sections 2 to 5 that these statements use. Check in particular that `Solves`, `IsDataStructure` and `RunsPhases` start every run on the memory described above and reset nothing.
3. The order of the quantifiers: the program, the slope and the constant stand before the instance, and the word size stands last.
4. The points on which the model is generous, and the notions that are defined twice.
5. The definitions of the mathematical objects in the answer predicates and in the bounds: K, N₀ and α_d in "Section 2: definitions" of `PaperStatements.lean`; the lopsided instances and the zero triangles of a graph in "Section 3: definitions"; the cost expressions (8) and (9) and the cost of a query in "Section 4: definitions"; the hinted products in "Section 5: definitions".
6. Lean's kernel, and Mathlib's definitions of matrix products, real powers, logarithms and square roots (Mathlib is not needed for the five claims).
7. That the definitions cannot be met for free. Three lemmas of the library show this; they are lemmas, not statements, so they help to judge the definitions and are not among the claims.
   * `not_solvedInTimeAt_threeSum`: for no a < 1 is 3SUM solved in O(n^a (log n)^e) steps, because a program cannot read its input in that time.
   * `not_endStatement_solvedInTime_threeSum`: for no rational r < 1 is 3SUM solved in O(n^r) steps in the sense of `EndStatement.lean`, the sense of the five claims.
   * `not_achievesVHinted`: for no a₃ < 1 does `AchievesVHinted τ a₂ a₃` hold, whatever is prepared in Phases 1 and 2, because the n output cells depend on the index that arrives in Phase 3, and a step writes one cell.
8. That each statement is proved. `docs/INDEX.md` says where, and the proofs depend on no axiom beyond the three standard ones of Lean (propext, Classical.choice, Quot.sound); `README.md`, "How to check it", says how to verify both.

### What is not stated about programs

Theorems 17, 21 and 33 to 35, Lemmas 36 and 37, Corollary 38 and the half of Theorem 2 on real inputs have no statement about programs. `docs/REMARKS.md`, "What is not proved", gives the reasons, and `docs/INDEX.md` says what is stated about each of them.

## Part 2. The language and the compiler

This part and the next describe the proof.

### How to follow a proof from a claim down

"Exact Triangle is solved in time O(n^{3−ε})" is said seven times in this formalization. The list below follows the order in which a proof uses these layers: layers 1 and 2 speak of the machine, layers 3 to 5 of the language, and layers 6 and 7 lead from the language back to the machine. `docs/INDEX.md` names the file in which each statement is proved, and `docs/PROGRAMS.md` lists, item by item, the lemmas of the route and the routines. The example is Theorem 19. Limits, tasks, solvers, hosts and the need of a procedure are explained in the sections that follow.

1. **The claim.** `Theorem_19` in `EndStatement.lean` says that Exact Triangle is solved in time O(n^{3−ε_T}), with a rational exponent and a step bound in natural numbers. `endStatement_theorem_19` derives it from the last bound of layer 2. Only the form of the bound changes; the program is the same.
2. **The statement about programs.** `Items.Theorem_19` is the printed sentence with its three bounds, about programs of the same machine. `wordRam_theorem_19` proves it from layers 3 and 6.
3. **The running-time claim.** `Claim.Theorem_19_second M` is the part of the sentence that uses Corollary 26 (the second and third bound), for an arbitrary meaning M of "is solved in time T" (a `DetTimeModel`). The paper's deductions between running times, here the cost analysis of the proof of Theorem 19, are lemmas about an arbitrary M (for instance `Theorem19.second_of_explicit`). Each of them has the form: if these running-time claims hold for M, then so does that one. Layer 4 proves the claims from which the deductions start for one particular M, and a lemma (`solvedInTime_of_claim`) turns a claim for that M into a bound of layer 2, using layer 6.
4. **The meaning given by programs.** For this M, "Exact Triangle is solved in time T" means that some procedure of some program of the language solves the task within T steps, with a polynomially bounded need (`SolvedIn`). The claims from which the deductions start are proved by giving programs: `Claim.Theorem_17` by the host of Theorem 17, and `Claim.Corollary_16` by a host applied to the solver of Corollary 26.
5. **The specification of a routine.** A host or solver consists of routines, each with a theorem of the form `Ends` or `Meets`. The conditions in it speak of functions on numbers and lists, and lemmas tie these functions to the mathematics of the section. For Theorem 17 the tie is loose: the statement `theorem_17` is about the reduction on finite sets, and the sentences of its third step are proved a second time for the lists of the program. The two developments share F(p), the first step of the proof, the number of instances and the counting step (`TriangleInstance.card_le_F_of_distinct_scans`).
6. **From a solver to the machine.** One more procedure reads the input in its layout and calls the solver. Since the need is polynomially bounded, every admissible word size allows limits that cover it. A run of c steps of the language becomes at most A·c + A steps of the machine, for a constant A that depends on the program only (`solves_of_programSolves`). This rests on the compiler's theorem (`compileProgram_correct`), which rests on the simulation of single statements (`sim`).
7. **The machine.** `exec` of `EndStatement.lean`; in the proofs, its runs are `Steps`.

In a picture, where ⇐ means "follows from":

    Theorem_19 of EndStatement.lean
      ⇐  the third bound of Items.Theorem_19                       (only the form of the bound changes)
      ⇐  Claim.Theorem_19_second for programs   +   the way to the machine
            Claim.Theorem_19_second for programs
               ⇐  Claim.Theorem_17 and Claim.Corollary_16 for programs      (the arithmetic of the proof of Theorem 19)
                     Claim.Theorem_17    ⇐  the host of Theorem 17  ⇐  the specifications of its routines  ⇐  lemmas of Section 3
                     Claim.Corollary_16  ⇐  a host applied to the solver of Corollary 26
            the way to the machine
               ⇐  the outermost procedure  +  limits that fit every admissible word size  +  the compiler's theorem (⇐ the simulation)

**The other items of Sections 3 and 5.3** go the same way. The places where their programs meet the statements of Section 3 are `theorem_21b_repeated_squaring` and `theorem_21b_entries_bounded` for APSP, `theorem_21b_negative_to_exact` for Negative Triangle, and `theorem_21a_convolution_to_exact` for Convolution-3SUM; for 3SUM it is the lemma `ChanHe.instances_correct`.

**The statements for Theorem 30 and Corollaries 26, 31 and 32 are proved without layers 3 and 4.** Their programs are lists of routines. The specifications of the routines are joined to a specification of the whole program, the bounds of the routines are added up, and the program is compiled. Theorem 5 goes through all the layers: its running-time claim is `Claim.Theorem_5`, and `claim_theorem_5` proves it for programs, by the solver of Section 2.4.4 behind a test of its regime.

**The last sentence of Corollary 26 is proved in two forms, for two users.** `wordRam_corollary_26_wanted` is the statement about the machine: one program that reads N, D, |W|, X, Y and W in their layout, on the inputs with N ≥ D^18. The second form is a running-time claim for programs (layer 4): a procedure that other procedures can call, at any place of the memory, and that is right on every instance. Corollary 16, and through it the bounds of Theorems 19, 22 and 2 that use Corollary 26, rest on the second form and do not use the first. Both forms run the same routines and take their costs from the same lemma, `Corollary26.costs`. The programs of Corollary 40 use neither form: they call the preprocessing and the query directly.

### The folders and namespaces of the library

The folders of the library, from the bottom up:

| Folder | What it holds | May import |
|---|---|---|
| `ThreeSumApsp/Util/` | general facts that mention no object of the paper: lists, sums, digits, ceilings, logarithms, primes; in `ThreeSumApsp/Util/Asymptotics/`, the calculus of bounds of the form n^a (log n)^e | — |
| `ThreeSumApsp/Sec1/` to `ThreeSumApsp/Sec5/` | what needs no machine, section by section, in files named after the items of the paper | Util |
| `ThreeSumApsp/ConditionalTimes/` | the three conditional lemmas, with the definitions in which they are stated | Util, Sec1 to Sec5 |
| `ThreeSumApsp/TimeClaims/` | the paper's deductions from one running-time sentence to the next, for an arbitrary meaning of "is solved in time T" | Util, Sec1 to Sec5 |
| `ThreeSumApsp/Spec/` | the objects of the paper as functions on numbers and lists, in the form in which programs handle them, each shown to compute the paper's object | Util, Sec1 to Sec5 |
| `ThreeSumApsp/Machine/` | facts about runs of the word RAM | Util |
| `ThreeSumApsp/Lang/` | the programming language, rules for reasoning about its programs, a few general routines, and the compiler with the proof that it is correct | Util, Machine |
| `ThreeSumApsp/Programs/` | the algorithms and reductions of the paper as programs of the language, section by section, each with a proof of what it computes and a bound on its steps | all of the above but ConditionalTimes |
| `ThreeSumApsp/RunningTimes/` | the proofs of the statements about programs, item by item, each with its outermost procedure, which reads the input as the statement lays it out (for Theorem 30, Section 4.4 and the phases of Corollary 40 the outermost procedures are in `ThreeSumApsp/Programs/`, because later programs call them) | the same, and Programs |
| `ThreeSumApsp/Statements/` | the theorems that Comparator compares, one file for each file of `Challenge/` under the same name: `ThreeSumApsp/Statements/EndStatement.lean` proves the five claims, and `ThreeSumApsp/Statements/PaperStatements.lean` names, in one line each, the theorem of the library that proves a further statement | all of the above |
| `ThreeSumApsp/ModelChecks/` | lemmas that show that the definitions of solving cannot be met for free; they are not statements, so Comparator does not compare them, and no statement rests on them | Util, Sec1 to Sec5, Machine, Statements |

Of the files of the library, a file imports only those of its own folder and of the folders in the last column, where `ThreeSumApsp/Sec1/` to `ThreeSumApsp/Sec5/` count as one folder; `python3 scripts/layers.py --check` tests this.

Namespaces, by folder:

| Namespace | Where |
|---|---|
| `EndStatement` | `EndStatement.lean` |
| `PaperStatements` | the statements of `PaperStatements.lean` (`PaperStatements.Lemma_6`) and the theorems which say that they hold (`PaperStatements.lemma_6`) |
| `ThreeSumApsp` | the definitions of `PaperStatements.lean`, and the mathematics; facts of `ThreeSumApsp/Util/` about Mathlib's objects are in `Nat`, `Int`, `Real`, `List` and `Finset` |
| `ThreeSumApsp.WordRam` | what solving means, in `PaperStatements.lean` (the statements about programs, `Items.…`, are in `ThreeSumApsp.WordRam.Items`), and `ThreeSumApsp/Machine/` |
| `ThreeSumApsp.Spec` | `ThreeSumApsp/Spec/` |
| `Light` | `ThreeSumApsp/Lang/`; in the Lean files the language is called the light language |
| `Light.Sec2` to `Light.Sec5` | the programs: `ThreeSumApsp/Programs/Sec2/` to `ThreeSumApsp/Programs/Sec5/`, and the outermost procedures in `ThreeSumApsp/RunningTimes/` |

### The language

The programs are written in a small imperative language, in which the paper's procedures can be written almost as printed. There they are verified, with explicit bounds on a precisely defined number of steps, and then they are compiled to the machine of `EndStatement.lean`.

A program is a list of procedure bodies, numbered from 0. It is a finite piece of data and contains no Lean functions. Each running procedure has local variables 0, 1, 2, …, and the memory is an array of integers addressed by natural numbers. Expressions (`Expr`) are constants, local variables, sums, differences, products, and the content of the cell at an address. Tests (`Cond`) compare two expressions by < or =. Statements (`Stmt`) are skip, assignment, store, sequence, if, while, and the call of a procedure by its number. A called procedure starts with its arguments in the local variables 0, 1, … and with 0 in all others. Its result is what its local variable 0 holds at the end. Recursion is allowed. There is no division.

The language has one flat memory and numbered local variables. So each program has to manage its arrays itself: their addresses, that they do not overlap, and the free space. The theorems about programs therefore speak of addresses and of cells that are unchanged outside a region.

### The number of steps

`Exec lim P d s σ σ' c` says that, within the limits lim, the statement s of the program P, started in the state σ at nesting depth d of calls, ends in the state σ' after exactly c steps. A state consists of the local variables and the memory.

Every constant, variable, operation and load of an expression costs 1. A test costs its two sides plus 1. An assignment costs its expression plus 1, and a store costs its two expressions plus 1. An if, and each test of a while, costs the test plus 1. A call costs its arguments, plus 2, plus the body. Skip and the sequencing of two statements cost nothing.

### Limits

A run is subject to three limits (`Limits`), called `word`, `space` and `depth`. It forms no number of absolute value above `word`, touches no cell at or above the address `space`, and nests calls at most `depth` deep. A run that would break a limit does not exist. So a proof that a run exists is also a proof that all its numbers fit. This is the paper's paragraph "Word size" (Section 2.4.4 and the proof of Theorem 30), made part of every specification.

### How a routine is verified

`docs/VERIFYING.md` describes the program logic: the judgment `Ends` (a statement, started in a state, ends within T steps in a state that satisfies a condition), the contract `Meets` of a procedure, the rules and tactics, the conventions of the files, and one routine line by line. Parts 2 and 3 use this much of it. A verified routine comes with its text, with a time bound that is a function of the sizes of the input, and with a specification against a function on numbers and lists that is defined without reference to any machine. Separate theorems prove that these functions compute the objects that the paper defines. The proof of a caller does not depend on the body of a callee.

### The compiler

`compileProgram P p0 dec` is the program of the word RAM that runs procedure p0 of the program P. For a decision problem (dec set) the compiled program accepts if the result of p0 is positive and rejects if not. Otherwise it always accepts. The headers of `ThreeSumApsp/Lang/Compiler/StatementCode.lean` and `ThreeSumApsp/Lang/Compiler/ProgramCode.lean` describe the code in full.

**Cells.** Cell a ≥ 0 of the language is cell a of the machine. Everything else lives in negative cells. The cells −1 to −4 are left to the interface: the two arguments of the outermost call stand in −1 and −2, and its result is put into −3 (−4 is not used). The odd cells from −5 down hold the registers of the compiled code, temporaries for the evaluation of expressions, and a pool of numbers. The even cells hold the call stack: stack cell j is the cell −2j, and the compiled statements write no stack cell before the cell −8. One number is read off the text of a program, its *width* F (`frameSize`). Every frame has F local variables, and there are 2F + 1 temporaries.

**Jumps, constants and start-up.** The machine can only branch to a fixed position, and only if a cell is negative. A return loads the position r to return to into a register and jumps to the *dispatcher*, the code "subtract 1; if negative, go to position j" for j = 0, 1, 2, …. The dispatcher arrives at r after 2(r + 1) steps, which is a constant for a fixed program. A constant of the program text is built where it is used, from its binary digits, by additions. The numbers that the compiled code needs for itself are offsets in a frame and positions to return to. They are kept in the pool and not built where they are used, because the length of the code that builds a number from its digits depends on the number, and a position to return to depends on the lengths. The pool holds all the numbers from 0 up to the position of the dispatcher (`dispPos`). The first instructions and the start-up code write everything that the compiled statements rely on.

### The compiler's theorem

The theorem is `compileProgram_correct`.

**What is assumed.**

* The outermost statement, which calls procedure p0 of P on two arguments i and j in a memory μ, ends after c steps within the limits lim. This is a fact about `Exec`.
* The word size fits the limits and the text (`Fits`): signed words hold twice `word` and two more, all addresses of the memory and of a stack with room for the allowed depth of calls, and the numbers of the pool.
* The memory m of the machine holds μ (`Holds`): every cell a ≥ 0 holds the word of μ(a), and these numbers have absolute value at most `word`.
* The cells −1 and −2 hold the words of i and j, which obey the same bound.

**What is concluded.** Started at position 0 on m, the compiled program gives the verdict that belongs to the result of p0 within `ramSteps` = `startCost` + `stepsPerStep` · c steps. `Outcome` describes the memory at the end.

* The cells a ≥ 0 hold the final memory of the run of P.
* The cell −3 holds the result.
* The cells −1 and −2 are unchanged.
* All cells from `space` on are unchanged, and so are all cells below −`lowCell`, where `lowCell` bounds the extent of the stack and the pool.

**The two constants.** `stepsPerStep` is twice the position of the dispatcher. `startCost` is that position plus F + 13. Both depend on the text of P and on the flag dec only: not on the input, not on the limits, not on the word size.

**The other cells.** Nothing is assumed about the cells below −2. This is what allows a query program to start on the memory that another compiled program has left. In the statements about data structures the two arguments of a query and its answer stand in the cells −1, −2 and −3. In the other statements the two arguments are 0, since the machine starts with zeros there.

**The structure of the proof.** It goes from the machine upwards: words and runs of the machine (`Steps`), the relation between a state of the language and a memory of the machine (`Rel`), expressions, tests, calls, the simulation, whole programs. The simulation (`sim`) says that a run of a statement in c steps is matched by a run of its code in at most `stepsPerStep` · c steps; its proof is an induction on the run, with one lemma for each rule of `Exec`.

### From a program of the language to a statement

The notions `Solves` and `IsDataStructure` of `PaperStatements.lean`, which Part 1 describes, speak about programs of the word RAM. `ProgramSolves` is the corresponding notion for a program of the language, and it speaks only about `Exec`. On the memory that holds the input in the layout of the problem, the call of p0 ends within T(x) steps. It does so within limits that are at most 2^s ((p₁ + 1) ⋯ (p_r + 1))^k in the parameters p₁, …, p_r of the instance. The result and the cells after the input are a correct answer. `ProgramIsDataStructure` is the analogue for a preprocessing procedure and a query procedure of one program.

**Polynomial limits give a slope.** At every admissible word size w (Part 1), a polynomial bound as above is at most 2^w as soon as the slope b is at least s + k r + k. The compiled program adds to this slope the number of binary digits of a number that is computed from its text, for the offsets and positions that the code itself forms. With this slope every admissible word size satisfies `Fits`.

**Time A · T + A.** `solves_of_programSolves` says that the compiled program satisfies `Solves` with the time A · T + A, where A = `timeConst` depends on the compiled program only. The same constant also bounds the extent of the memory, including the stack and the pool. `isDataStructure_of_program` says the same from `ProgramIsDataStructure` to `IsDataStructure`, for the two compiled programs. A solver is one use of the compiler's theorem, from the initial memory. A data structure is one use for the preprocessing and then an induction on the list of queries, with one use for each query.

### Tasks, solvers and hosts

A *task* is a problem with a calling convention. A procedure gets the sizes, a bound U on the absolute values of the numbers, the addresses of its arrays, and, as its last argument, a pointer to free memory. All inputs and outputs lie below this pointer. The procedure may write its output and the cells from the pointer on, and no other cell. Nothing is assumed about the content of the free cells, so a solver can be called again and again.

`Solves task P p T need` says that procedure p of P solves the task within T(size, U) steps whenever the limits allow for `need`, which consists of a largest number, a number of free cells and a number of nested calls. It also says that this holds in every program that begins with P.

A reduction of the paper becomes a *host*: a procedure that calls an arbitrary solver of another task. `IsHost lower upper time need` says that from every solver of `lower` one obtains, by appending procedures, a solver of `upper`. Its time and need are the given functions of the solver's, and its need stays polynomial. A call costs the callee's own number of steps plus a constant. This is the paper's account of a reduction (beginning of Section 3): its "running time is the extra time plus the total time to solve B on each instance created".

### Running-time claims

The paper's deductions of the kind "Plug Theorem 19 into Theorem 21" are proved once, for an arbitrary meaning of the sentence "the problem is solved in time T". Such a meaning is a `DetTimeModel`: one predicate on time bounds for each problem. A *running-time claim* is a proposition about a `DetTimeModel`. For example, the claim for Theorem 17 says that from every time bound for Lop-AE-SparseTri one gets the time bound of Theorem 17 for Exact Triangle. "The five claims", in contrast, always means the five propositions of `EndStatement.lean`. The hosts and solvers prove the running-time claims for the meaning given by programs (`SolvedIn`, layer 4 above). For each problem one more procedure reads the sizes from the layout of the problem (Part 1), forms U = n^κ by κ multiplications, computes the addresses and calls the solver. Then the compiler's theorem applies.

### Phases

Corollary 40 speaks of an algorithm that receives its input in phases. `RunsPhases` (Part 1) is the notion on the machine. There is a corresponding notion for one program of the language with one procedure for each phase, and the compiled programs are proved to run in phases. The invariant between two phases says that the memory of the machine holds the memory of the program of the language and that the two argument cells hold 0. Writing the input of a phase keeps the invariant. So does a run of a compiled program, which may start on whatever an earlier one has left, because its start-up code sets up all that it needs.

### A glossary for Parts 2 and 3

`docs/VERIFYING.md` explains the vocabulary of the proofs about programs. These are the names of the notions of "Tasks, solvers and hosts" and "Running-time claims".

| notion | name | what it says |
|---|---|---|
| what a run needs | `Need`, `Need.Ok` | the largest absolute value formed, the cells used from the free pointer on, the levels of calls below the procedure; `Need.Ok`: for a procedure called at depth d with the free pointer fr, the limits cover all three |
| a need is polynomially bounded | `PolyNeed` | each of its three parts, in the size n and the bound U on the numbers |
| a function is polynomially bounded | `PolyBounded` | F n U ≤ K ((n + 1)(U + 1))^e for some K and e |
| a problem with a calling convention | `Task` | instances, size, bound, arguments, what holds before and after |
| a procedure solves a task | `Solves` (the one for procedures of the language) | within T(size, bound) steps whenever the limits allow for the need, also in every longer program |
| solved in time T | `SolvedIn` | for a real-valued T: by some solver with a polynomially bounded need |
| a reduction as a program | `IsHost` | every solver of one task extends to a solver of another, with the given time and need |
| the tasks behind Theorems 21 and 22 | `etTask`, `ntTask`, `c3Task`, `s3Task`, `mpTask`, `apTask` | Exact Triangle, Negative Triangle, Convolution-3SUM, 3SUM, the (min,+)-product, APSP |

## Part 3. The programs

Solver, host and need are explained in Part 2, "Tasks, solvers and hosts". The *outermost procedure* of a program is the procedure p0 of the compiler's theorem: it reads the input in the layout of the problem (Part 1) and calls the solver.

### Which programs run, and by which route of the paper

The paper sometimes has two routes, one through Theorem 5 and one through Corollary 26. Each statement about programs is then proved by its own route. Statements that have no program of their own follow from the others by arithmetic.

| Statement | Programs that run | Route of the paper |
|---|---|---|
| Theorem 5: `wordRam_theorem_5` | The outermost procedure reads N, D, \|W\|, forms the bound N^κ and calls a solver that is right on every instance: it tests the regime of the theorem and falls back to inner products outside it. In the regime it calls the solver of Section 2.4.4. | Section 2's own algorithm. It is not derived from Corollary 26. |
| Theorem 30: `wordRam_theorem_30` | One list of procedures is compiled twice. The preprocessing program uses the shared stage of Section 2 and the routines of Section 4. The query program starts on the memory that the preprocessing leaves behind. | Sections 4.2 and 4.3 |
| Theorem 30, offline form: `wordRam_theorem_30_wanted` | The same procedures: preprocess, then one query for each wanted position. | "In particular, for every set W" (Theorem 30) |
| Corollary 26: `wordRam_corollary_26`, `wordRam_corollary_26_wanted` | The *general program* with the numbers of the printed proof in its text. The general program consists of the procedures of Theorem 5 and Theorem 30, and of routines that find m = ⌈log₄ D⌉, L and t and pad the matrices. Two rational numbers, for L = ⌈am/b⌉ and t = ⌈pm/q⌉, and a threshold m₀ are constants of its text. For Corollary 26 they are 21, 1/9 and 60 (`program26`). | Theorem 30 with "L := 21m and t := ⌈m/9⌉", which applies "For m ≥ 60". For smaller m, where "the corollary holds trivially", a query computes an inner product. The costs are bounded by the five steps of the printed proof (`Corollary26.costs`). |
| Corollaries 31 and 32: `wordRam_corollary_31`, `wordRam_corollary_32` | The general program, with rational numbers close to c and θ and a threshold m₀ in its text. | "We repeat the proof of Corollary 26 with L := ⌈cm⌉ and t := ⌈θm⌉": Theorem 30 with these parameters, "once m exceeds a constant depending on c, θ, and ε". Below the threshold, where "the corollary again holds trivially", a query computes an inner product. |
| Theorems 24 and 25: `wordRam_theorem_24`, `wordRam_theorem_25` | The general program, with c and θ chosen for ε and q (for Theorem 25: for ε and κ/2). | the proofs of Theorems 24 and 25: Corollary 31, and "ask one query for each position of W" |
| Theorem 1, Theorem 3: `wordRam_theorem_1`, `wordRam_theorem_3` | The sentences before the last: the program of Corollary 26. Last sentences: the general program, with c and θ chosen for ε and κ/2 (for ε and q). | The sentences before the last come from Corollary 26. The last sentences are Theorems 25 and 24 with 0.1204 < ε*, with the logarithms absorbed into a smaller γ and a larger q, and with the case D = 1. |
| Corollary 15: `wordRam_corollary_15` | The program of Theorem 5 with a test of its regime and a fallback to inner products, called on the two biadjacency matrices with the bound 1; a host that cuts W into pieces; a host that turns counts into answers 0 or 1. | through Theorem 5: Section 2's programs |
| Corollary 16: `wordRam_corollary_16` | The host that turns counts into answers, over the offline solver of Corollary 26 with a test of its regime and a fallback to inner products. No host cuts W, since the bound holds for every W. | From Corollary 26: Section 4's programs |
| Theorem 19: `wordRam_theorem_19` | Two programs, one for the first bound and one for the second, which implies the third. Both are the host of Theorem 17. First bound: D is the largest power of four with D ≤ n^{1/18}, and g = ⌈D^{1/36}⌉, over the solver of Corollary 15. Second bound: D = ⌊n^{1/18}⌋, g = ⌈D^{0.0315}⌉, over the solver of Corollary 16. | "using Theorem 5 (via Corollary 15)" and "using Corollary 26", each bound by its own route |
| Theorem 22, the sentence "Using Theorem 5": `wordRam_theorem_22_first` | The reductions of Theorem 21 as hosts: 3SUM to Convolution-3SUM after Chan and He, Convolution-3SUM to Exact Triangle, Negative Triangle to Exact Triangle, the (min,+)-product from Negative Triangle, APSP by repeated squaring. They run over the first program of Theorem 19, with brute force below a fixed size. | "Using Theorem 5 (through Theorem 19)" |
| Theorem 22, last sentence: `wordRam_theorem_22_second` | The same reductions over the second program of Theorem 19. | "Using Corollary 26 instead" |
| Theorem 22, 3SUM: `wordRam_theorem_22_threeSum` | Those of Theorem 22, one for each route. | The statement has the printed forms n^{2−1/1296+o(1)} and n^{2−ε′/2+o(1)}; see "3SUM with polylogarithmic factors" below. |
| Theorem 2, its deterministic sentence: `wordRam_theorem_2` | No new program: those of Theorem 19 and of Theorem 22, last sentence. | The exponents 2.9983 and 1.9992 are those of the route through Corollary 26, and 2.9995 is above the 2.99942 of that route. |
| Theorem 2, first line, n-vertex graphs: `wordRam_theorem_2_graphs` | A host that writes the tripartite instance of an n-vertex graph, over the second program of Theorem 19. | As in the row above |
| Corollary 39, zero weight: `wordRam_corollary_39_zero` | The host of the reduction from k-Clique to triangles, over the second program of Theorem 19. | The exponent k − ε_T⌊k/3⌋ has ε_T = 0.0017, which belongs to the second bound of Theorem 19. |
| Corollary 39, minimum and maximum weight: `wordRam_corollary_39_min_max` | The same host, which in each of its n^t rounds compares the weight of the triangle found with the best so far, over a host that finds a maximum-weight triangle with a solver of Exact Triangle, over the second program of Theorem 19. For the minimum, a host that negates the weights stands in between. | the proof of Corollary 39, with [VW13, Theorem 3.3] |
| Corollary 40, running times for τ < 1/18: `wordRam_corollary_40_times` | For each of the three hinted problems one program of the language: the program of Corollary 26, followed by one procedure for each phase and their routines. It is compiled once for each phase. | The data structure of Corollary 26: the phase after the hint preprocesses, the last phase asks queries. |
| Corollary 40, "General τ": `wordRam_corollary_40_general_times` | The same phase procedures after the general program. | Corollary 31, "with c and θ chosen as in the proof of Theorem 24 for q := 1/2" |
| Corollary 40, "fail", for 1/18 and for ε*: `wordRam_corollary_40_fail` | None of its own. | The exponents 2 − 0.063τ and 1 + 0.437τ (for τ < ε*: 2 − γτ and 1 + τ/2) are below 2 and 1 + τ, "whatever the value of ω" (Corollary 40). |
| Theorem 4: `wordRam_theorem_4` | None of its own. | Corollary 40, with 0.1204 < ε*: a conjecture that fails up to τ₀ fails up to every smaller bound. |
| The five claims: `endStatement_theorem_19`, `endStatement_theorem_22_3SUM`, `endStatement_theorem_22_MinPlus`, `endStatement_theorem_22_APSP`, `endStatement_corollary_39_zeroWeight` | No program of their own: the second program of Theorem 19 and the programs of the rows for Theorem 22, last sentence, and Corollary 39 (zero weight). Only the form of the time bound changes. | As in those rows. |

### How explicit the programs are

The statements say that programs exist. The proofs describe the programs, but not everything in them is computed.

The program of Theorem 30 is a fixed list of procedures that is written out in the library (`program30`) and can be printed and compiled. The program of Theorem 5 is such a list (`programThin`) followed by the outermost procedure, which depends on κ. The programs of Corollary 15, of the first bound of Theorem 19 and of the sentence "Using Theorem 5" of Theorem 22 are determined by the proofs in the same way, as such lists followed by hosts. They are not written out as one list.

The program of Corollary 26 is a fixed list of procedures as well (`program26`): it is the general program (`program31`) at the parameters `ratParams26`, that is, with the numbers 21, 1/9 and 60 in its text. Two lemmas name it in their statements: compiled with its main procedure for the preprocessing, for a query or for the offline form, it meets the bounds of Corollary 26 (`isDataStructure_program26`, `solves_program26`). The programs that are built on it consist of this list and of hosts or phase procedures, and are determined by the proofs; "What inherits this" below lists them. The constant C of the time bound and the slope b are not added up for them.

The programs of Corollaries 31 and 32, and all programs that are built on them, contain numerals that are proved to exist but are not computed: the threshold m₀ and the rational parameters. Three quantities are therefore known only to exist for these programs: the length of the text, the constant C, and the slope b. None of the five claims uses these programs.

### The steps of the paper and the routines

Every routine is specified against a function on numbers and lists, and a separate theorem links that function to the paper's definition in `PaperStatements.lean`. `docs/PROGRAMS.md` lists for each item the final theorem, the programs, the routines and the lemmas about them, with their files. The table below goes through the main steps; the table of "Which programs run, and by which route of the paper" has the hosts and the items that are arithmetic.

**How the objects are stored.** In Section 2 a string over an alphabet of b letters is stored as one number, its code in base b, with level 1 as the most significant digit. An array on strings is stored in the order of the codes, so a slice is a segment. In Section 4 a leaf, a box or an output string is handled as the string of its L digits in the memory, level 1 first. A term P_ij has the digit 3(i − 1) + (j − 1), P₀ the digit 9, and the star the digit 10.

| Where | The step of the paper | The program |
|---|---|---|
| Section 2.3.4 | "We fix K₀² ≤ K distinct subsets" | an enumeration, which is written to a table |
| Section 2.4.1 | "We compute the encodings of the input arrays" | a recursive routine, which forms A_λ (step (2) of Full, Section 2.3.1) for each of the ten terms λ and calls itself on A_λ. Everything up to here is one procedure, the *shared stage*, which the programs of Section 4 use too. |
| Section 2.4.2 | Pruned | recursive as printed. The set S is a strictly increasing list of codes, and a vertex is given by the two addresses at which its parts of the two encodings begin. |
| Section 2.4.4 | "Sort the sets W_T"; "we run Pruned(W_T)" | a routine for the tile and the output string of each wanted position, a radix sort, a loop over the tiles, and a pass over W for the report |
| proof of Lemma 29 | val(π) "with ten lookups in the trie" | one routine: it writes the ten terms one after the other in the place of the highest star, looks each string up, and puts the star back |
| proof of Lemma 29 | "Generating the boxes with e stars", "in increasing order of their number of stars", for every tile | three nested loops |
| Section 4.3, before Lemma 29 | "reading the product at a leaf" | a routine that finds the place of the leaf in the two encodings from its L digits by Horner's rule |
| Section 4.3 | the query, steps (1) to (3) | step (1) is done from the tables; a routine places a string of length m at the levels of Q; "the sum in Lemma 28, which has two parts" has one loop for each part |
| proof of Corollary 26 | "Let m := ⌈log₄ D⌉"; "pad the inner dimension"; "Let L := 21m and t := ⌈m/9⌉" | a loop; a copying routine; two calls. One procedure text, which finds ⌈am/b⌉ by counting, stands in the program twice, with the numbers for L and with those for t. |
| proof of Theorem 17 | the prime: P and Q "over the ring ℤ[x]/(x^p − 1)" | the matrices are written, with a ring element as a vector of p integers; a recursive routine for Strassen's algorithm computes PQ, and the count is read off |
| proof of Theorem 17 | the instances | for each chunk and each piece, the two matrices are written and the solver is called; the oracle is an arbitrary solver of Lop-AE-SparseTri |
| proof of Theorem 17 | "scan the piece C_k of its instance" | a routine. For Theorem 19, procedures compute the two choices of D and g. |
| Theorem 21 | the reductions behind it | hosts over an arbitrary solver: Convolution-3SUM from Exact Triangle [VW13, Theorem 4.3], Negative Triangle from Exact Triangle [VW13, Theorem 3.3], the (min,+)-product from Negative Triangle (three hosts, with [VW18, Lemma 4.1] and [VW18, Theorem 4.2]), APSP by repeated squaring, and 3SUM from Convolution-3SUM [CH20, Theorem 5.1] |
| Corollary 39 | "We enumerate the n^t ways […] and for each of them we build H" | the loop of the host, which builds the three matrices of H and calls the solver of Exact Triangle once in each round |
| Corollary 40, Conjecture 5.2 of [vdBNS19] | "we preprocess X := M and Y := V"; "n queries" | Phase 2; Phase 3 |
| Conjecture 5.7 of [vdBNS19] | "The proof is the same, with X := N_{[n],I} and Y := V" | Phase 2 first writes X |
| Conjecture 5.12 of [vdBNS19] | "Cut the n rows of U into n/t₂ blocks of t₂ rows"; "t₂ queries" | Phase 3 writes Y := N_{I,J} and preprocesses the blocks; Phase 4 |

### Where the programs depart from the paper's description, and why

None of these departures changes a statement about programs. They are choices that the paper leaves open, changes forced by the weaker machine, or simplifications within the stated bounds. The files that `docs/PROGRAMS.md` names for an item describe its routines in their headers and docstrings. Departures of the Lean statements from the wording of the paper are recorded in `docs/REMARKS.md`.

**In all sections**

- **No division.** Quotients, remainders, digits, roots and logarithms are obtained by counting, by doubling, or by long division with a table of doubles. Where a step may not depend on log N or on log U, tables are filled in advance by counters.
- **The bound U is an argument.** A solver is told a bound U ≥ 1 on the numbers and has to be right for every valid bound; "time T(n, u)" is read as: at most T(n, u) steps whenever the bound that is handed over is at most u. The routines for Theorem 5, Theorem 30 and Corollaries 26, 31 and 32 never read the bound.
- **A solver has to be right on every instance.** Theorem 5 and Corollary 26 speak about a regime (for Theorem 5: D ≥ 4 a power of four, N ≥ D^18, |W| ≤ N²/√D; for Corollary 26: N ≥ D^18, to which the statements here add D ≥ 1). A procedure that other procedures call is required to be correct, with a polynomial need, on all inputs. So it first tests the regime and falls back to inner products outside it. The statements for Theorem 5, Theorem 30 and Corollary 26 themselves ask for correctness in the regime only.
- **Nothing is assumed about free memory.** A solver that is called repeatedly finds what earlier calls have left, so every routine clears what it needs to be zero, within its time bound.
- **One word for one number.** The slope is chosen after κ, so a number of absolute value n^{O(1)} takes one cell. The programs do not need the factor 1 + log u, where u is the bound on the numbers, by which the running-time claims (Part 2) allow for numbers of several words.

**Theorem 5 (Section 2)**

- **A string is one word.** The paper charges O(L) for handling a string (Section 2.4.4); here a string is stored as its code, a number below 10^L ≤ N², and a call of Pruned costs O(|S| + 1). The whole program then takes O(N² log D / D^{1/18}) steps of the language. The statement about the program is the printed bound, with log² D.
- **Band, block and digits of every row come from tables.** The paper allows O(L) operations for each position of W to "locate the output strings" (Section 2.4.4); on this machine a long division of I would cost about log N steps, and N is not bounded by any function of D. So counters fill tables for all rows I < N once, in O(NL) steps and cells, which is within the bound because N ≥ D^18.
- **Radix sort, and grouping by tile.** "Sort the sets W_T" is done for all tiles at once: L stable counting sorts on the stored digits of the codes, the last digit first, and then one counting sort on the numbers of the tiles. Since the program sorts all of W at once, for all tiles, a comparison sort would cost it a factor log |W|, which is not bounded in terms of D.
- **The padding of N is not carried out** (Section 2.3.4). The program does not copy the matrices; it skips the rows beyond N when it forms the input array of a band.
- **One concrete layout.** The statements of Section 2 hold for every way of numbering rows, columns and subsets. The running-time sentences ("locate the output strings", "list the K₀² subsets […] O(L) operations per subset") need one particular layout that can be computed within those bounds, for example base-3 and base-4 digits for the bijections. A running-time form of Theorem 5 therefore concerns some layout, not every layout. The program uses base-3 and base-4 digits, and a fixed enumeration of the subsets.
- **Dense linear forms.** The paper notes that each φ_λ has at most three monomials; the program multiplies by all seven coefficients 0, ±1 from a table, which is a constant factor.
- **An explicit stack for the lists.** The work areas of nested calls of Pruned lie one behind the other, so a run on W_T needs at most L (3 |W_T| + 11) cells.
- **Small computations.** m is found by multiplying by 4 until D is reached, K by Pascal's triangle in O(L²) steps and K₀ by counting up in O(√K) steps, both within the bound because K ≤ N.
- **A directory.** The shared stage leaves the sizes and the base addresses of its arrays in a short block of cells at the start of its work area.

**Theorem 30 (Sections 4.2 and 4.3)**

- **The preprocessing begins with the shared stage of Section 2,** so the entries above on the tables, the padding of N, the layout, the linear forms, K and K₀ and the directory hold here too. In the range of Theorem 30 the time of the stage and the length of its block are within (8) (`sharedShape_le`, `sharedEnd_sub_le`, `within8_ten_pow`, `within8_N_mul`, `within8_bands`).
- **One enumeration serves for three:** the boxes with e stars, the leaves of order below t that contribute to an output string w, and the boxes of w. The number of boxes with e stars and the numbers α_d are never computed.
- **The boxes of w come in one loop.** Where the proof of Theorem 30 says "for every V ⊆ Q with |V| = m − t and every box of 𝓑_V", the program has one loop. It follows the second description of the boxes of w in Section 4.2, in which "each box of w arises exactly once" (`existsUnique_starBelow_eq`). The lemma `mem_boxesOf_iff` says that the list of the program consists of exactly the strings of the boxes of this description. The α_t boxes are the same. Only their order differs: it is the lexicographic order of the strings, in which the sets V are interleaved. The lemma `sum_boxesOf` says that a sum over the list of the program is the sum over the union of the sets 𝓑_V, and the lemma `sum_queryTerms_storedD` splits it into the double sum of Lemma 28.
- **Tries are arrays.** The paper stores the boxes of a tile "in a standard trie on their strings of L symbols". Here a vertex is a block of 11 cells, one for each symbol, that hold the relative addresses of the children; the tries of all tiles lie in one area, and a table holds one root for each tile.
- **A query does not depend on N.** It reads band, block and digits of I and J from the tables of the shared stage, which are part of the data structure. These tables have O(NL) cells, which is at most a constant times the last term of (8).
- **A query keeps the data structure intact.** Of the cells a ≥ 0 it writes only three scratch strings inside the block of the data structure.
- **m, L and t are input.** In the statement for Theorem 30 one pair of programs serves all parameters.
- **The offline forms have programs of their own,** because their layout differs: the list W and the output cells lie next to the matrices.

**Corollaries 26, 31 and 32 (Section 4.4)**

- **The programs of Corollaries 26, 31 and 32 contain a threshold.** The text of the general program contains a constant m₀. For m = ⌈log₄ D⌉ below it the preprocessing finds m and 4^m and stores the flag 0, and a query computes an inner product. From m₀ on, the preprocessing and the query are those of Theorem 30 on the padded matrices.
  - *Corollary 26.* The constant is the 60 of the printed proof: the inequality (10) holds "for all m ≥ 60" (`eq_10_corollary_26`), and "For m ≥ 60, Theorem 30 thus applies" (`hyp30_26`, `pre31_program26_above`, `query31_program26_above`). The case m < 60 of the program renders the sentence "(For m < 60, D is bounded by a constant, and the corollary holds trivially.)" (`pre31_program26_below`, `query31_program26_below`).
  - *Corollaries 31 and 32.* The constant is that of "once m exceeds a constant depending on c, θ, and ε" (proof of Corollary 31); its existence is proved, but its value is not computed. The general program is proved on 1 ≤ D ≤ N^ε, with log D + 1 in place of log D; on D ≥ 2 this gives the printed bounds. The case D = 1 is needed because the last sentences of Theorems 1 and 3 have no lower bound on D.
  - *What inherits this.* The programs that are built on Corollary 26 contain the 60: those of Corollary 16, of the second and third bound of Theorem 19, of the last sentence of Theorem 22, of Theorem 2, of Corollary 39, of the sentences before the last of Theorems 1 and 3, of Corollary 40 for τ < 1/18, and of all five claims of `EndStatement.lean`. The programs that are built on Corollaries 31 and 32 contain a threshold that is not computed: those of Theorems 24 and 25, of the last sentences of Theorems 1 and 3, and of "General τ" in Corollary 40.
- **One text serves Corollary 26 and Corollaries 31 and 32.** The paper does the calculation in full for L = 21m and t = ⌈m/9⌉ and then says that "the same calculation works with L = ⌈cm⌉ and t = ⌈θm⌉" (Section 4.4); the mathematics of the library does the same. The programs are written once, with the parameters a, b, p, q and m₀, and their routines carry 31 or 32 in their names; the program of Corollary 26 is this text at (21, 1, 1, 9, 60) (`program26_pre31`, `program26_levels31`, `program26_switch31`, `program26_query31`).
- **Three cells in front of the padded matrices** hold the flag, the base address of the block of Theorem 30, and 4^m.
- **From the costs to the program.** The step from the two costs of Theorem 30 to the steps, the cells and the word size of the program is proved once, for all parameters (`CostsWithin`), with constants that are only shown to exist.
- **The padded matrices are copied.** How to pad the inner dimension from D to 4^m < 4D is a choice that the paper leaves open; the programs write two padded copies and keep the given matrices. Writing the two copies takes O(N 4^m) steps and cells. These are within (8): N 4^m is at most its last term, because K N₀ 4^m ≤ 7^L (`N_mul_pow_le_cost8`).
- **Rational parameters in the program text.** Corollaries 31 and 32 are stated for all real c and θ, as printed. The program holds rational numbers c′ = a/b slightly above c and θ′ = p/q slightly below θ, since its text is finite; for D ≥ 1 its bounds are then below the printed ones. ⌈am/b⌉ and ⌈pm/q⌉ are found by counting, in O(L) steps.

**Corollaries 15 and 16, Theorems 17 and 19 (Sections 3.1 to 3.3)**

Theorem 17 is not among the statements about programs. It is proved for programs with Strassen's algorithm only, which is the form that Theorem 19 uses.

- **One loop over all instances.** Where the paper says "For each chunk 𝒬 ⊆ W_ϱ and each piece C_k", the program numbers the instances and keeps the number of the piece and the number of the chunk as two counters.
- **X and Y are written anew for every instance,** although Y depends only on the piece. Both cost O(nD), which is what the paper charges for an instance.
- **The query pairs are not copied.** A chunk is a segment of the two sorted arrays of rows and columns, and the solver gets the addresses of the segment.
- **Scans are guarded rather than stopped.** The paper stops as soon as a zero triangle is found; the program calls the solver for every instance, which the bound allows, but makes no scan after the first successful one.
- **The instances are not all produced before the first call.** The program has room for one instance. "The reduction is non-adaptive" is a statement about the reduction: which instances are formed does not depend on any answer.
- **Residues by a table of doubles.** This costs O(log U) steps for each weight and prime, and it stays below the terms of Theorem 17.
- **Z-order for Strassen's algorithm.** P, Q and PQ are padded to 2^⌈log₂ n⌉ rows and columns and stored so that the four quadrants of a matrix are the four quarters of its segment of the memory.
- **Strassen's seven products as seven phases of one shape.** Each phase forms two signed sums of quarters of the operands and adds their product, with signs, to two quarters of the result. The signs are 1, −1 or 0. A sign 0 stands for an operand or a quarter that Strassen's scheme does not use, so a few more vector operations are made than necessary.
- **Only Strassen's algorithm.** The term n^{ω+o(1)} D^{3/2} of Theorem 17 appears with n^{log₂ 7} in place of n^{ω+o(1)}. The paper notes that this suffices for Theorem 19.
- **Brute force for small n.** The program tests the hypotheses 16 ≤ D ≤ n and 1 ≤ g ≤ √D of Theorem 17 and runs the brute force if one fails. With D = ⌊n^{1/18}⌋ this happens for all n < 16^18.
- **Primes by trial products.** The primes of the window [√D/2, √D) are found in O(D^{3/2}) steps, which is below the term n^{log₂ 7} D^{3/2}.
- **D and g are computed by procedures that are parameters of the host.** The host of Theorem 17 is written once, and the two choices in the proof of Theorem 19 are two pairs of procedures.
- **From U to κ.** The number of false positives is bounded in terms of U through κ := max(1, log U / log n).
- **The piece size of Corollary 15** is found by counting up and stopping at |W|, because only O(|W| + 1) steps are allowed outside the calls.

**Theorems 21 and 22 (Section 3.4)**

The paper cites the reductions of Theorem 21 and does not describe them; for these reductions the points below are the choices of the programs.

- **Convolution-3SUM from Exact Triangle.** All 2(⌊√N⌋ + 1) instances are asked, also after the answer yes.
- **Negative from Exact Triangle.** The prefixes of the weights are computed from the top level down, one binary digit for each level.
- **Finding from deciding.** A half of a part of h vertices is its first or its last ⌈h/2⌉ vertices, so the halves of an odd part overlap and no padding is needed. All eight combinations are asked at each level.
- **All pairs.** The blocks have ⌈n^{1/3}⌉ vertices, and the last block of a part is moved back so that it ends at n. A pair that has been found is masked by the weight 2U + 1.
- **The product** is found bit by bit from the top, for all pairs at once.
- **APSP.** The number 3nU stands for +∞, and entries above nU are reset to it after each squaring.
- **3SUM from Convolution-3SUM.** The program follows the construction defined in `PaperStatements.lean` ("The reduction of Chan and He: definitions"); `docs/REMARKS.md`, "Section 3: cited results", lists its departures from [CH20]. The number of pairs (candidate prime, element) of the searches for the moduli, which is defined there as a count, becomes a running time here, up to the factor O(log U).
- **The 3SUM host has κ in its text.** It first raises the bound U to max(U, n^κ), so that all inputs with U ≤ n^κ lead to instances of Convolution-3SUM of one length. This is needed because the length depends on U, and the running time of an arbitrary solver need not be monotone in the length.
- **3SUM with polylogarithmic factors.** The programs give n^{2−1/1296} (log n)^{O(1)} and n^{2−ε′/2} (log n)^{O(1)}. The printed forms with n^{o(1)} follow.

**Corollary 39 (Section 5.3)**

- **The program of Corollary 39 depends on k,** which is fixed before the program. Wherever the paper's construction ranges over the parts or over pairs of parts, the program text contains one statement for each of them instead of a loop.
- **A vertex of H is never decoded.** Its digits in base n are the chosen vertices; the program keeps the digits of the current row and column in k cells and moves them on by adding 1 with carries.
- **All n^t choices are run,** also after a triangle of weight zero has been found, and the three matrices are rebuilt for every choice.
- **The bound on the weights of H.** The paper uses binom(k, 2) n^ν ≤ N^{2ν} for n ≥ k². The program passes binom(k, 2) U to the solver as the bound; the inequality is used only in the arithmetic of the running time.
- **The cited reduction of Corollary 39 is programmed.** The paper cites [VW13, Theorem 3.3]; here the search for the weight and for the vertices is a program with a proof. It makes O(log² U + log n) calls in all, which is the paper's "O(log² n) times as much" for U = n^κ.
- **The vertices of the best clique** are recovered at the end by counting up with digits in base n, in O(n^t + N) steps once.

**Corollary 40 (Section 5.4)**

- **The statements about data structures cannot be used as parts.** The definition of a data structure in the statements about programs fixes the input at cell 0, assumes zeros elsewhere, and does not say which cells the two programs use. The hinted problems need a structure next to other data (the index and the output follow the matrices at once), on a matrix that is built elsewhere (X = N_{[n],I}), or ⌈n/t₂⌉ structures at the same time. So Corollary 40 is proved from the specifications of the two routines in the language, which take addresses as arguments, name the cells they change and assume nothing about them.
- **Nothing is copied in v-hinted Mv.** M and V are preprocessed where the phases have put them.
- **The blocks of U are aligned at the end.** n need not be a multiple of t₂. Block number k has the t₂ rows from n − (k + 1) t₂ on, and the last block starts at row 0, so that it may overlap the one before. Every block is then a contiguous piece of U: nothing is copied or padded. There are ⌈n/t₂⌉ ≤ 2n/t₂ blocks.
- **A table in place of a division.** There is no division, so Phase 3 writes, for every row, the first row of its block into a table of n cells, from which Phase 4 finds the block of row i and the place of i in it.
- **Rounding in the case τ < 1/18.** With t = ⌊n^τ⌋ three facts are used. First, t^18 ≤ n. Second, ⌊n^{τ₁}⌋^18 is an integer that is at most n^{τ₂}, hence at most ⌊n^{τ₂}⌋. Third, t ≥ n^τ/2 costs a factor 2^{0.063}.
- **Rounding in "General τ" for Conjecture 5.12.** "[…] we use the same blocks, which requires n^{τ₁} ≤ n^{ετ₂}". For the integers the condition of the data structure is t₁ ≤ t₂^ε, which holds as soon as t₁ exceeds a constant. Below its threshold the data structure does not use the condition, so the threshold m₀ of the program is chosen at least as large as that constant.
- **γ ≤ 1 in "General τ".** The saving γ is taken at most 1 and below γ(c, θ). Writing X, or Y and the table, then stays within n^{2−γτ} and n^{1+τ₂−γτ₁}, and the logarithmic factors of Corollary 31 are absorbed.
- **Bounds for Conjecture 5.12 in "General τ".** For "we use the same blocks" the statement has Phase 2 in O(n^{τ₁}), Phase 3 in O(n^{1+τ₂−γτ₁}) and Phase 4 in O(n^{τ₂+τ₁/2}) steps, which is what the argument gives. Phase 2, "a Phase 2 that only stores I" (Corollary 40), returns at once, since the input is written into the memory by the definition of a phase.

### Steps that the programs pay for, within the printed bounds

Here the programs do what the paper describes. A program has to carry out and to count every step, where a proof need not. Each of these steps is within the printed bound, and the library writes the count out.

- **Theorem 5: writing the input arrays.** The program pays for writing the entries of X and Y into the input arrays of the bands. It clears the 7^L cells of an array, which the O(10^L) for each band covers. It then writes K₀² N₀ D entries, each at a place that it computes in O(L) steps. Over all bands this is at most 2 N K₀ D (L + 1) steps, which fits within the printed bound because K₀ D² ≤ K N₀ ≤ D^18 ≤ N; this is part of the proved estimate of the cost. The proof of Theorem 30 prints this step: "we form it in O(L · 7^L) operations".
- **Lemma 29: the enumeration of the boxes is started m − t + 1 times for a tile.** "We compute the values of the boxes in increasing order of their number of stars": for each e = 0, …, m − t the program starts an enumeration of the boxes with e stars. They come from the leaves with at least e and at most m − t symbols P₀, "by turning the e lowest symbols P₀ of that leaf into stars" (proof of Lemma 29, "The count"). A start costs O(L) steps. Lemma 29 counts "O(L) time and space per box". The m − t + 1 starts are within this bound, because a tile has at least m − t + 1 boxes, one for each number of stars (the lemma `succ_le_card_boxes`). So are the root of the trie and its cell in the table of roots, which come on top of the "at most L vertices per box" (the lemma `within8_trieSpace`).
- **Theorem 30: every partial sum fits in a word.** "[…] every value we compute is a sum of at most 10^m products of two such numbers" (proof of Theorem 30, "Word size"). A routine adds its numbers one after the other, so at every moment it holds the sum of an initial part of a list. The library bounds all these sums, where A and B bound the numbers of the two encodings: by 10^e A B in the dynamic program for a box with e stars, and by 10^m A B in a query (the lemmas `abs_dp_partial_sum_le` and `abs_query_partial_sum_le`).
- **Corollaries 39 and 40.** The programs also pay for building the n^t graphs H of Corollary 39 (O(k² N²) steps each) and for writing X = N_{[n],I} and Y = N_{I,J} in Corollary 40; both fit within the printed bounds.

### The constants

The constants are not optimized. Each stage of the proofs rounds up generously, so what the proofs give is far above what the programs need.

- **Programs of the language.** Every routine has a bound with explicit numerals. For Theorem 5 and Theorem 30 these add up to an explicit constant in front of N² log² D / D^{1/18}, of (8), of L Σ_{d ≤ t} α_d and of (9). The hosts of Theorem 17, Convolution-3SUM, Negative Triangle, the (min,+)-product and APSP also have explicit constants. The step from 3SUM to Convolution-3SUM, Theorems 19, 22 and 2 and Corollary 39 are obtained with asymptotic estimates and have no explicit constant. For everything built on Corollaries 26, 31 and 32 the constant exists but is not computed.
- **Assumptions in two of these bounds.** The bounds for Negative Triangle and the (min,+)-product assume, like Theorem 21(b), that T(s, u)/s is nondecreasing in s. They also assume that T(s, u) ≥ s² (1 + log u), the time to write down an instance. This is how additive terms and calls at smaller sizes are absorbed.
- **The compiler.** One step of the language becomes at most 2 · (position of the dispatcher) steps of the machine, where the position of the dispatcher is the length of the code in front of it (Part 2, "The compiler's theorem"). Every step is charged the cost of the most expensive event. That event is a return, which walks down the dispatcher because the machine has no indirect jump. The constant C of a statement is the product of the compiler's constant and the constant of the program of the language. Its value is not listed here. The lengths of the compiled programs behind Theorems 19, 22 and 2 are not computed.
- **The slope.** A word has to hold the offsets, code positions and numerals of the compiled code, and the addresses and numbers of the run. So the slope is the sum of a number that depends on the text and a number that comes from the polynomial bound on the need. Explicit slopes follow from the proofs for Theorem 5 and Theorem 30 only; they grow linearly with the exponent of the bound on the entries.
- **Large numerals in a program text.** The programs of Theorem 22, and those of Theorem 2 for 3SUM, the (min,+)-product and APSP, contain the numeral 16^18 ≈ 4.7 · 10²¹, the size below which they use brute force. Such a numeral enters the slope through its number of binary digits, 73, because a word has to hold it. The threshold m₀ enters in the same way. The proofs for the programs of Corollaries 26, 31 and 32 themselves and for Corollary 40 also use 4^{m₀}, as a bound on 4^m below the threshold; for Corollary 26 this is 4^60, a number of 121 binary digits. The procedure for Corollary 26 that other procedures call, on which Corollary 16 and all that is built on it rest, does not need this number: its need is bounded in terms of N, D and U, with a summand 1000 that covers the 60.
- **What the threshold 60 means in numbers.** m = ⌈log₄ D⌉ ≥ 60 means D > 4^59, and then N ≥ D^18 > 2^2124. The programs of Corollary 26 build the data structure of Theorem 30 for these D, and for D ≤ 4^59 a query is an inner product of D terms.
- **What the constants depend on.** For a fixed exponent of the bound on the numbers each statement gives one program, one slope and one constant. The programs for Theorem 30 and Corollaries 26, 31 and 32 do not depend on this exponent at all; only the slope does. The program for Theorem 5 and the programs for the problems of Section 3 depend on κ through the outermost procedure, which forms N^κ or n^κ, and, for 3SUM, through the host.
