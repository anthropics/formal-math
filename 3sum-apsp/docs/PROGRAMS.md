# The programs, item by item

This file is written by `scripts/index.py` from `docs/programs.json`, from the headers and the proofs of the files that
prove the running-time statements, and from the docstrings of the lemmas; do not edit it.

`docs/MACHINE.md`, Part 3, says in words which programs run and by which route of the paper. This file gives the names.
For each running-time item of the paper, in the order of the pages, it has

* the statements, and the file in which they are proved;
* the header of that file, which tells the route from the programs to the statements;
* the lemmas of the route: those that the header names, those that the proofs in the file use, and, among those that the
  proofs of these use in turn, the main results of their files and the deductions between running-time claims; each
  with the first sentence of its docstring and with its file;
* the routines of the programs. A routine is a procedure of the light language, a definition whose name ends in
  `Body`. The table says what is proved about it, in the words of the docstring of the lemma; which list-level functions
  of `ThreeSumApsp/Spec/` the lemma is stated with; which function bounds the number of steps (where the column is empty, the
  bound is written out in the lemma); and where routine and lemma stand. A routine that several items run is listed once,
  under the item with the fewest routines among them.

## Theorems 1 to 4 (pages 5 to 8)

Statements: `wordRam_theorem_1`, `wordRam_theorem_2`, `wordRam_theorem_2_graphs`, `wordRam_theorem_3`, `wordRam_theorem_4`, proved in `ThreeSumApsp/RunningTimes/Sec1/Theorems1_4.lean`.

The theorems of the introduction restate later items.

* Theorem 1: the last sentence of Corollary 26 with `|W| ≤ N²/√D` (`corollary_26_W`), and Theorem
  25 without its logarithms (`dataStructureBelow_wantedBelow_epsStar`), for `ε < 0.1204 < ε*`.
* Theorem 2, the deterministic sentence: the last bound of Theorem 19 and the bounds of Theorem 22
  using Corollary 26, where `2.9995` is above `2.99942` (`SolvedInTime.mono_exponent`).  Its first
  line is printed for `n`-vertex graphs: "an instance on an arbitrary `n`-vertex graph reduces to
  this form by taking three copies of the vertex set" (Section 3.2), which is one more program
  (`Light.Sec3.Theorem2.graphs_of`).
* Theorem 3: Corollary 26, and Theorem 24 without its logarithms (the same lemma), for
  `ε < 0.1204 < ε*`.
* Theorem 4: Corollary 40.

| Lemma or definition | What it says | File |
|---|---|---|
| `ThreeSumApsp.corollary_26_W` | Corollary 26: `\|W\| D^{0.437} + N²/D^{0.063}` "is O(N²/D^{0.063}) whenever \|W\| ≤ N²/√D" (with constant 2). | `ThreeSumApsp/Sec4/Corollary26.lean` |
| `ThreeSumApsp.dataStructureBelow_wantedBelow_epsStar` | The last sentences of Theorems 3 and 1, on the word RAM, for every `ε < ε*` (the theorems have `ε < 0.1204`): choose `c` and `θ` as in the proof of Theorem 24 (`exists_admissible`), for the wanted entries with `q := κ/2` and `γ' := min{γ, κ/2}` as in the proof of Theorem 25, and give away half of the exponent to absorb the logarithmic factors. | `ThreeSumApsp/RunningTimes/Sec4/Corollary31_32.lean` |
| `ThreeSumApsp.WordRam.SolvedInTime.mono_exponent` | A bound `O(n^a (log n)^e)` is a bound `O(n^a' (log n)^e)` for `a ≤ a'`. | `ThreeSumApsp/Machine/Solving.lean` |
| `Light.Sec3.Theorem2.graphs_of` | Theorem 2, first line, as printed: "Exact Triangle on n-vertex graphs in O(n^{2.9983}) time", from the bound for the tripartite form. | `ThreeSumApsp/RunningTimes/Sec3/Theorem19/GraphsLayout.lean` |
| `ThreeSumApsp.WordRam.exists_solves_of_dominated` | A program that solves a problem in time `O(f)` solves it in time `O(f')` if `f = O(f')`. | `ThreeSumApsp/Machine/Solving.lean` |
| `ThreeSumApsp.wordRam_corollary_26_wanted` | Corollary 26, on the word RAM: the offline form. | `ThreeSumApsp/RunningTimes/Sec4/Corollary26.lean` |
| `ThreeSumApsp.wordRam_theorem_19` | Theorem 19, on the word RAM. | `ThreeSumApsp/RunningTimes/Sec3/Theorem19.lean` |
| `ThreeSumApsp.wordRam_theorem_22_second` | Theorem 22, on the word RAM: the bounds using Corollary 26. | `ThreeSumApsp/RunningTimes/Sec3/Theorem22.lean` |
| `ThreeSumApsp.exactTriangleIn_of_explicit` | The first deterministic line of Theorem 2, "Exact Triangle on n-vertex graphs in O(n^{2.9983}) time", for the tripartite form of the problem, from the explicit form of Theorem 19 (`3 - ε_T = 2.9983`). | `ThreeSumApsp/TimeClaims/Sec3/Theorem19.lean` |
| `Light.Sec3.claim_theorem_19_usingCorollary26` | Theorem 19, the bound using Corollary 26, for programs of the light language. | `ThreeSumApsp/RunningTimes/Sec3/Theorem19.lean` |
| `ThreeSumApsp.wordRam_corollary_26` | Corollary 26, on the word RAM: the two-stage data structure. | `ThreeSumApsp/RunningTimes/Sec4/Corollary26.lean` |
| `ThreeSumApsp.wordRam_corollary_40_times` | Corollary 40, on the word RAM: the running times for `τ < 1/18`. | `ThreeSumApsp/RunningTimes/Sec5/Corollary40.lean` |
| `ThreeSumApsp.wordRam_corollary_40_fail` | Corollary 40, on the word RAM: the three conjectures fail for `τ < 1/18`, and more generally for `τ < ε*`. | `ThreeSumApsp/RunningTimes/Sec5/Corollary40.lean` |
| `ThreeSumApsp.Corollary40.fail_mono` | Conjectures that fail up to `τ₀` fail up to every smaller bound. | `ThreeSumApsp/RunningTimes/Sec5/Corollary40.lean` |

| Routine | What is proved about it | Lemma | Stated with | Time | Files |
|---|---|---|---|---|---|
| `graphEtBody` | The host is correct. | `graphEt_spec` |  | `graphEtTime` | `ThreeSumApsp/Programs/Sec3/Theorem19/Graphs.lean` |

The programs also run routines that are listed under other items: 29 under Theorem 5, 45 under Theorem 22, 34 under Theorem 19, 1 under Corollaries 15 and 16, 12 under Corollary 26, 18 under Theorem 30, 12 under Corollary 40.

## Theorem 5 (page 13)

Statements: `wordRam_theorem_5`, proved in `ThreeSumApsp/RunningTimes/Sec2/Theorem5.lean`.

The route.  The solver of Section 2.4.4 is a procedure of the light language.  "Is solved in time T"
asks for a right answer on every input, so the procedure first tests whether the input is in the
regime of the theorem and falls back on brute force outside it; in the regime its running time obeys
the bound of the theorem (`Light.Sec2.claim_theorem_5`).  An outermost procedure reads the sizes
`N`, `D` and `|W|` from the input layout, forms the bound `N^κ` on the entries, computes the
addresses of the two matrices, of the wanted positions and of the output, and calls the solver; the
compiler turns the program into one for the word RAM (`Light.Sec3.realized_thinProduct`).

| Lemma or definition | What it says | File |
|---|---|---|
| `Light.Sec2.claim_theorem_5` | Theorem 5, for programs of the light language. | `ThreeSumApsp/Programs/Sec2/Theorem5/AllInstances/Program.lean` |
| `Light.Sec3.realized_thinProduct` | The thin matrix product: if the task is solved in time T, the wanted entries are computed on the word RAM within a constant times T. | `ThreeSumApsp/RunningTimes/Sec3/Corollary15_16/Layout.lean` |
| `ThreeSumApsp.FromClaims.Theorem5.of_claim` | Theorem 5, about programs, from the claim about `M`. | `ThreeSumApsp/RunningTimes/FromClaims.lean` |
| `Light.Sec2.thin_claim` | The running-time claim "Theorem 5" for programs of the light language, from a program as in thin_solves. | `ThreeSumApsp/Programs/Sec2/Theorem5/AllInstances/Solver.lean` |
| `Light.Sec2.thm5_spec` | Theorem 5, the solver, with the constant 2 c + 100, where c is the constant with which the called procedures meet their entries. | `ThreeSumApsp/Programs/Sec2/Theorem5/Solver.lean` |
| `Light.Sec2.mainCallees_of_prefix` | The procedures that the solver calls meet their entries, in every program that begins with program5. | `ThreeSumApsp/Programs/Sec2/Theorem5/Program.lean` |
| `Light.Sec3.realizedN` | If a task with the calling convention of the thin matrix product is solved, the problem is solved on the word RAM within a constant times the time of the solver. | `ThreeSumApsp/RunningTimes/Sec3/Corollary15_16/Layout.lean` |

Lists of procedures: `Light.Sec2.programThin` (`ThreeSumApsp/Programs/Sec2/Theorem5/AllInstances/Program.lean`).

| Routine | What is proved about it | Lemma | Stated with | Time | Files |
|---|---|---|---|---|---|
| `sharedBody` | shared(L, m, N, D, aX, aY, b0): fills the shared block. | `shared_entry` |  |  | `ThreeSumApsp/Programs/Sec2/Theorem5/SharedStage.lean` |
| `powBody` | The loop that is written out κ times turns U = 1 into U = n^κ. | `pow_spec` |  |  | `ThreeSumApsp/Programs/Sec2/Theorem5/LibraryContracts.lean`<br>`ThreeSumApsp/Lang/TopProcedure.lean` |
| `binomBody` | binom returns (L choose m) and changes no cell outside the L + 2 cells from pas. | `binom_spec` |  |  | `ThreeSumApsp/Programs/Sec2/Theorem5/Tables/Binomials.lean` |
| `sqrtBody` | sqrt(K) returns ⌊√K⌋ and leaves the memory as it is. | `sqrt_meets` |  | `sqrtTime` | `ThreeSumApsp/Lang/Lib/Sqrt.lean` |
| `subsetTableBody` | subsets writes the table and changes nothing else. | `subsetTable_spec` | `unrank` |  | `ThreeSumApsp/Programs/Sec2/Theorem5/Tables/Subsets.lean` |
| `countersBody` | counters writes the band and the block of every row and changes nothing else. | `counters_spec` |  |  | `ThreeSumApsp/Programs/Sec2/Theorem5/Tables/BandCounters.lean` |
| `digitsBody` | digits writes the table of digits and changes nothing else. | `digits_spec` |  |  | `ThreeSumApsp/Programs/Sec2/Theorem5/Tables/Digits.lean` |
| `coefBody` | coef writes the two tables and changes nothing else, in 7 · 140 steps: the specification that its callers assume. | `coef_entry` | `phiFlat`, `psiFlat` |  | `ThreeSumApsp/Programs/Sec2/Theorem5/Tables/Coefficients.lean` |
| `bandArrayBody` | bandArray(L, m, N, D, K0, N0, S7, β, side, aA, sI, sK, mask, dig3, dig4, arr), for the left side: side = 0, aA the address of X, sI = D, sK = 1 (sI and sK are the strides of the index I of the band and of the inner index k: the entry is at aA + I sI + k sK). The same procedure for the right side: side = 1, aA the address of Y, sI = 1, sK = N. | `bandArrayL_entry`, `bandArrayR_entry` | `arrL`, `stdLayout`, `arrR` |  | `ThreeSumApsp/Programs/Sec2/Theorem5/Encode/BandArray.lean` |
| `encStepBody` | encStep writes `∑_{s < 7} tab[7 lam + s] · src[s n + j]` to `dst[j]` for all `j < n` and changes nothing else. | `encStep_meets` |  | `tEncStep` | `ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Step.lean` |
| `encodeBody` | encode is correct and takes at most `encTime L` steps, in every program whose procedures number pS and pE are encStep and encode. | `encode_spec` |  | `encTime` | `ThreeSumApsp/Programs/Sec2/Theorem5/Encode/Recursion.lean` |
| `encodeBandsBody` | encodeBands for the row bands of X: side = 0, the coefficients φ at tab. encodeBands for the column bands of Y: side = 1, the coefficients ψ at tab. | `encodeBandsL_entry`, `encodeBandsR_entry` | `arrL`, `stdLayout`, `phiFlat`, `arrT`, `arrR` |  | `ThreeSumApsp/Programs/Sec2/Theorem5/Encode/AllBands.lean` |
| `wantedBody` | wanted: in a program that has Wanted.wantedBody as procedure number pWanted, a call writes the tile, the code and the digits of the code of each wanted position, changes no other cell, and takes at most 86 (w + 1) (L + 1) steps. | `wanted_entry` | `outCodeOfPos` |  | `ThreeSumApsp/Programs/Sec2/Theorem5/Wanted/Codes.lean` |
| `countSortBody` | countSort sorts the items stably by their keys: the five phases, one after the other. | `countSort_meets` |  | `countSortTime` | `ThreeSumApsp/Lang/Lib/CountSort.lean` |
| `sortWantedBody` | sortWanted(w, L, nT, tid, dgt, perm): "sort the sets W_T" (Section 2.4.4), by a radix sort: L stable counting sorts on the digits of the codes, the last digit first, then one on the numbers of the tiles. t i and x i are the tile and the code of position i. | `sortWanted_entry` |  |  | `ThreeSumApsp/Programs/Sec2/Theorem5/Wanted/Sort.lean` |
| `segBoundsBody` | segBounds: a call takes at most cSegBounds (codes.length + 11) steps. | `segBounds_entry` | `sliceList` |  | `ThreeSumApsp/Programs/Sec2/Theorem5/Pruned/Slices.lean` |
| `unionBody` | union: a call writes the merge of the two lists to pc, returns its length and changes no cell outside the output, in at most 70 (na + nb + 1) steps. | `union_entry` | `mergeUnion` |  | `ThreeSumApsp/Programs/Sec2/Theorem5/Pruned/Union.lean` |
| `pickBody` | pick, writing: a call with add = 0 writes the values of the codes of the small list to pDst and changes no other cell, in at most cPick (small.length + big.length + 1) steps. pick, adding: a call with add = 1 adds the values of the codes of the small list to the cells from pDst on and changes no other cell, in at most cPick (small.length + big.length + 1) steps. | `pickSet_entry`, `pickAdd_entry` | `restrictList` |  | `ThreeSumApsp/Programs/Sec2/Theorem5/Pruned/Restrict.lean` |
| `prunedBody` | pruned does what PrunedSpec says, in at most 5500 prunedWork steps. | `pruned_entry` | `prunedWork`, `prunedList` |  | `ThreeSumApsp/Programs/Sec2/Theorem5/Pruned/Recursion.lean`<br>`ThreeSumApsp/Programs/Sec2/Theorem5/Pruned/Contract.lean` |
| `runTilesBody` | runTiles does what `RunTilesSpec` says: for every tile the values of the pruned recursion stand in SV, and only SV and the stack have changed. | `runTiles_entry` | `prunedWork`, `prunedList` |  | `ThreeSumApsp/Programs/Sec2/Theorem5/Pruned/AllTiles.lean` |
| `reportBody` | report does what `ReportSpec` says: OUT[π[i]] = SV[i] for i < w, and no cell outside the output has changed, in at most 20 (w + 1) steps. | `report_entry` |  |  | `ThreeSumApsp/Programs/Sec2/Theorem5/Wanted/Report.lean` |
| `fillBody` | fill(dst, n, x) writes x into the n cells from dst and changes nothing else. | `fill_meets` |  | `fillTime` | `ThreeSumApsp/Lang/Lib/Copy.lean` |
| `copyBody` | copy(src, dst, n) copies the n cells from src to dst and changes nothing else. | `copy_meets` |  | `copyTime` | `ThreeSumApsp/Lang/Lib/Copy.lean` |
| `gatherBody` | gather: a call ends within 20 (w + 1) steps with dst[i] = src[π[i]] for i < w, and no cell outside the w cells of dst has changed. | `gather_entry` |  |  | `ThreeSumApsp/Programs/Sec2/Theorem5/Wanted/Gather.lean` |
| `thm5Body` | Theorem 5, the solver, with the constant 2 c + 100, where c is the constant with which the called procedures meet their entries. | `thm5_spec` |  |  | `ThreeSumApsp/Programs/Sec2/Theorem5/Solver.lean` |
| `regimeBody` | regime(N, D, w) changes no cell. It returns m if 1 ≤ m, D = 4^m, D^18 ≤ N and w 2^m ≤ N², and 0 if there is no such m. | `regime_entry` |  |  | `ThreeSumApsp/Programs/Sec2/Theorem5/AllInstances/RegimeTest.lean` |
| `thinBruteBody` | The brute force is right on every instance for which D U² fits in a word. | `thinBrute_spec` |  |  | `ThreeSumApsp/Programs/Sec2/Theorem5/AllInstances/BruteForce.lean` |
| `thinBody` | thin solves the task on all instances, in the program P5 ++ [regime, thinBrute, thin], where P5 is a program of 26 procedures whose number pThm5 is the solver of Theorem 5, which does its task within K · thm5Shape steps also after more procedures are appended. | `thin_solves` |  | `thinTime` | `ThreeSumApsp/Programs/Sec2/Theorem5/AllInstances/Solver.lean` |
| `powTableBody` | powTable(dst, L, b) writes the powers 1, b, …, b^(L-1) into the L cells from dst and changes nothing else. | `powTable_meets` |  | `powTableTime` | `ThreeSumApsp/Lang/Lib/PowTable.lean` |

## Corollaries 15 and 16 (page 32)

Statements: `wordRam_corollary_15`, `wordRam_corollary_16`, proved in `ThreeSumApsp/RunningTimes/Sec3/Corollary15_16.lean`.

The route, as in the paper.  The number of triangles through a query pair is an entry of the product
of the two biadjacency matrices, and detection follows from counting.  So Theorem 5 gives the first
case of Corollary 15; splitting the query pairs into pieces gives the general case; and the offline
form of Corollary 26 gives Corollary 16.  These are claims about programs of the light language
(`claim_corollary_15_first`, `claim_corollary_15`, `claim_corollary_16`).  The outermost procedures
for the input layout and the compiler (`Light.Sec3.realized_lopCount`,
`Light.Sec3.realized_lopDetect`, together `lopRealized`) carry them to the word RAM.

| Lemma or definition | What it says | File |
|---|---|---|
| `Light.Sec3.claim_corollary_15_first` | Corollary 15, the case of at most `n²/√D` query pairs, for programs of the light language. | `ThreeSumApsp/RunningTimes/Sec3/Corollary15_16.lean` |
| `Light.Sec3.claim_corollary_15` | Corollary 15, the general case, for programs of the light language. | `ThreeSumApsp/RunningTimes/Sec3/Corollary15_16.lean` |
| `Light.Sec3.claim_corollary_16` | Corollary 16 for programs of the light language. | `ThreeSumApsp/RunningTimes/Sec3/Corollary15_16.lean` |
| `Light.Sec3.realized_lopCount` | #Lop-AE-SparseTri: if the task is solved in time T, the problem is solved on the word RAM within a constant times T. | `ThreeSumApsp/RunningTimes/Sec3/Corollary15_16/Layout.lean` |
| `Light.Sec3.realized_lopDetect` | Lop-AE-SparseTri: if the task is solved in time T, the problem is solved on the word RAM within a constant times T. | `ThreeSumApsp/RunningTimes/Sec3/Corollary15_16/Layout.lean` |
| `Light.Sec3.lopRealized` | The outermost procedures and the compiler carry the running times of both problems to the word RAM. | `ThreeSumApsp/RunningTimes/Sec3/Corollary15_16.lean` |
| `ThreeSumApsp.FromClaims.Corollary15.of_claim` | Corollary 15, about programs, from the claim about `M`. | `ThreeSumApsp/RunningTimes/FromClaims.lean` |
| `ThreeSumApsp.FromClaims.Corollary16.of_claim` | Corollary 16, about programs, from the claim about `M`. | `ThreeSumApsp/RunningTimes/FromClaims.lean` |
| `ThreeSumApsp.Corollary15.first_of_theorem_5` | The deduction of the first case of Corollary 15 from Theorem 5: "Apply Theorem 5 with N = n to the two biadjacency matrices". | `ThreeSumApsp/TimeClaims/Sec3/Corollary15_16.lean` |
| `Light.Sec2.claim_theorem_5` | Theorem 5, for programs of the light language. | `ThreeSumApsp/Programs/Sec2/Theorem5/AllInstances/Program.lean` |
| `Light.Sec3.claim_lopCountFromThinProduct` | Counting common neighbours is a thin matrix product (Section 3.1). | `ThreeSumApsp/Programs/Sec3/Corollary15_16/CountAndDetect.lean` |
| `Light.Sec3.claim_lopDetectFromCount` | Detection from counting (proof of Corollary 15). | `ThreeSumApsp/Programs/Sec3/Corollary15_16/CountAndDetect.lean` |
| `ThreeSumApsp.Corollary15.general_of_theorem_5` | The deduction of the general case of Corollary 15 from Theorem 5: "For larger W, apply the theorem to each of at most [...] pieces." | `ThreeSumApsp/TimeClaims/Sec3/Corollary15_16.lean` |
| `Light.Sec3.claim_lopSplit` | Corollary 15, the general case: a solver for the instances of #Lop-AE-SparseTri(n, D) with at most n²/√D query pairs gives one for every set W of query pairs. "For larger W, apply the theorem [Theorem 5] to each of at most ⌈\|W\|√D/n²⌉ + 1 pieces." | `ThreeSumApsp/Programs/Sec3/Corollary15_16/Split.lean` |
| `ThreeSumApsp.Corollary16.of_corollary_26` | The deduction of Corollary 16 from Corollary 26: "This is Corollary 26 with N = n, applied to the two biadjacency matrices as above." | `ThreeSumApsp/TimeClaims/Sec3/Corollary15_16.lean` |
| `Light.Sec4.claim_corollary_26_wanted` | Corollary 26, last sentence, for programs of the light language. | `ThreeSumApsp/Programs/Sec4/Corollary26/Claim.lean` |
| `Light.Sec3.realized_lop` | The two lopsided triangle problems: what differs between them is how the answers are read off the memory (hpost). | `ThreeSumApsp/RunningTimes/Sec3/Corollary15_16/Layout.lean` |
| `Light.Sec2.thin_claim` | The running-time claim "Theorem 5" for programs of the light language, from a program as in thin_solves. | `ThreeSumApsp/Programs/Sec2/Theorem5/AllInstances/Solver.lean` |
| `Light.Sec2.thm5_spec` | Theorem 5, the solver, with the constant 2 c + 100, where c is the constant with which the called procedures meet their entries. | `ThreeSumApsp/Programs/Sec2/Theorem5/Solver.lean` |
| `Light.Sec2.mainCallees_of_prefix` | The procedures that the solver calls meet their entries, in every program that begins with program5. | `ThreeSumApsp/Programs/Sec2/Theorem5/Program.lean` |
| `Light.Sec3.LopHosts.detect_spec` | detect solves Lop-AE-SparseTri. | `ThreeSumApsp/Programs/Sec3/Corollary15_16/CountAndDetect.lean` |
| `Light.Sec3.LopSplitHost.split_spec` | split solves #Lop-AE-SparseTri. | `ThreeSumApsp/Programs/Sec3/Corollary15_16/Split.lean` |
| `Light.Sec4.allInstancesTime26_le` | The time of allInstances26 in the regime is within the bound of Corollary 26. | `ThreeSumApsp/Programs/Sec4/Corollary26/AllInstances.lean` |
| `Light.Sec4.allInstances26_program26` | The procedure allInstances26 of `program26` solves the task on all instances: the program holds allInstances26, regimeTest26 and the brute force at their numbers. | `ThreeSumApsp/Programs/Sec4/Corollary26/Claim.lean` |

| Routine | What is proved about it | Lemma | Stated with | Time | Files |
|---|---|---|---|---|---|
| `lopDetectBody` | detect solves Lop-AE-SparseTri. | `detect_spec` |  | `lopDetectTime` | `ThreeSumApsp/Programs/Sec3/Corollary15_16/CountAndDetect.lean` |
| `lopSplitBody` | split solves #Lop-AE-SparseTri. | `split_spec` |  | `lopSplitTime` | `ThreeSumApsp/Programs/Sec3/Corollary15_16/Split.lean` |

The programs also run routines that are listed under other items: 29 under Theorem 5, 12 under Corollary 26, 18 under Theorem 30.

## Theorem 19 (page 35)

Statements: `wordRam_theorem_19`, proved in `ThreeSumApsp/RunningTimes/Sec3/Theorem19.lean`.

The route, as in the paper.  Theorem 17 reduces Exact Triangle to instances of the lopsided triangle
problem.  With the parameters `D` and `g` of Section 3.3 and Corollary 15 for the instances the
total is `O(n^{3−1/648} log² n)` (`claim_theorem_19_usingTheorem5`); with Corollary 16 it is
`O(n^{3−ε'} log n)`, `ε' = 0.00175` (`claim_theorem_19_usingCorollary26`).  Both are claims about
programs of the light language that keep the dependence on `κ`.  The outermost procedure for the
input layout and the compiler (`Light.Sec3.realized_exactTriangle`) carry them to the word RAM.
The third bound of the theorem, `O(n^{3−ε_T})`, follows from the second, so it rests on Corollary 16
and not on Corollary 15.

Section 3.4 needs the two bounds for all numbers of vertices and all bounds on the weights:
`claim_exactTriangleUniform_usingTheorem5`, `claim_exactTriangleUniform_usingCorollary26`.  They
combine the program with brute force below a threshold, as in the proof ("smaller instances are
solved by brute force").

| Lemma or definition | What it says | File |
|---|---|---|
| `Light.Sec3.claim_theorem_19_usingTheorem5` | Theorem 19, the bound using Theorem 5, for programs of the light language. | `ThreeSumApsp/RunningTimes/Sec3/Theorem19.lean` |
| `Light.Sec3.claim_theorem_19_usingCorollary26` | Theorem 19, the bound using Corollary 26, for programs of the light language. | `ThreeSumApsp/RunningTimes/Sec3/Theorem19.lean` |
| `Light.Sec3.realized_exactTriangle` | Exact Triangle: if the task is solved in time T, then Exact Triangle is solved on the word RAM within a constant times T. | `ThreeSumApsp/RunningTimes/Sec3/Theorem19/Layout.lean` |
| `Light.Sec3.claim_exactTriangleUniform_usingTheorem5` | The bound using Theorem 5, for all numbers of vertices and all bounds on the weights. | `ThreeSumApsp/RunningTimes/Sec3/Theorem19.lean` |
| `Light.Sec3.claim_exactTriangleUniform_usingCorollary26` | The bound using Corollary 26, for all numbers of vertices and all bounds on the weights. | `ThreeSumApsp/RunningTimes/Sec3/Theorem19.lean` |
| `ThreeSumApsp.FromClaims.Theorem19.of_claim` | Theorem 19, about programs, from the two claims about `M`. | `ThreeSumApsp/RunningTimes/FromClaims.lean` |
| `ThreeSumApsp.Theorem19.first_of_explicit` | The first bound of Theorem 19 in the printed form, for every constant `κ ≥ 1`, from the explicit form. | `ThreeSumApsp/TimeClaims/Sec3/Theorem19.lean` |
| `ThreeSumApsp.Theorem19.second_of_explicit` | The second bound of Theorem 19 in the printed form, with "O(n^{3-ε'} log n) ≤ O(n^{3-ε_T})", from the explicit form. | `ThreeSumApsp/TimeClaims/Sec3/Theorem19.lean` |
| `ThreeSumApsp.Theorem19.explicit_of_theorem_17_corollary_15` | The deduction "By Theorem 5" in the proof of Theorem 19: from Theorem 17 (with Strassen's algorithm) and the first case of Corollary 15, with `D` the largest power of four at most `n^{1/18}` and `g = ⌈D^{1/36}⌉`. | `ThreeSumApsp/TimeClaims/Sec3/Theorem19.lean` |
| `Light.Sec3.claim_theorem_17₅` | Theorem 17 for programs of the light language, with D "the largest power of four with D ≤ n^{1/18}" and "g := ⌈D^{1/36}⌉". | `ThreeSumApsp/Programs/Sec3/Theorem17/ClaimAtParameters.lean` |
| `Light.Sec3.claim_corollary_15_first` | Corollary 15, the case of at most `n²/√D` query pairs, for programs of the light language. | `ThreeSumApsp/RunningTimes/Sec3/Corollary15_16.lean` |
| `ThreeSumApsp.Theorem19.explicit_of_theorem_17_corollary_16` | The deduction "By Corollary 26" in the proof of Theorem 19: from Theorem 17 (with Strassen's algorithm) and Corollary 16, with `D = ⌊n^{1/18}⌋` and `g = ⌈D^{0.0315}⌉`. | `ThreeSumApsp/TimeClaims/Sec3/Theorem19.lean` |
| `Light.Sec3.claim_theorem_17₂₆` | Theorem 17 for programs of the light language, with "D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉". | `ThreeSumApsp/Programs/Sec3/Theorem17/ClaimAtParameters.lean` |
| `Light.Sec3.claim_corollary_16` | Corollary 16 for programs of the light language. | `ThreeSumApsp/RunningTimes/Sec3/Corollary15_16.lean` |
| `ThreeSumApsp.exactTriangleUniform_of_explicit` | From the explicit form of Theorem 19, brute force for small instances ("smaller instances are solved by brute force") and two closure properties: Exact Triangle in time `K s^{3-δ} (log s + 1)^e (1 + log u)²` for all `s` and `u`. | `ThreeSumApsp/TimeClaims/Sec3/Theorem19.lean` |
| `Light.Sec3.claim_bruteForce` | "Smaller instances are solved by brute force" (proof of Theorem 19): Exact Triangle is solved in time `C n³ (1 + log u)`, where `u` bounds the absolute values of the weights. | `ThreeSumApsp/Programs/Sec3/Theorem19/BruteForceClaim.lean` |
| `Light.Sec3.closure_chooseBySize` | Two algorithms, chosen by the size of the instance. | `ThreeSumApsp/Programs/Sec3/Theorem19/ChooseBySize.lean` |
| `Light.Sec3.closure_monoExactTriangle` | A program that solves Exact Triangle in time `T` solves it in every larger time. | `ThreeSumApsp/RunningTimes/Sec3/Theorem19.lean` |
| `Light.Sec3.claim17_of_host` | From a host to the claim. `time` and `need` are the host's time and need as functions of those of the solver. | `ThreeSumApsp/Programs/Sec3/Theorem17/Claim.lean` |
| `Light.Sec3.hostNeed_poly` | The need of the host stays polynomial, if the parameters, the numbers that the parameter procedures form, and the need of the solver are polynomially bounded. | `ThreeSumApsp/Programs/Sec3/Theorem17/Host/NeedPolynomial.lean` |
| `Light.Sec3.obeysBound17_hostTime` | The bound of Theorem 17 for the host. The parameter routines compute `Dfun n` from `n` and `Gfun D` from `D`. | `ThreeSumApsp/Programs/Sec3/Theorem17/TimeBound/Total.lean` |
| `Light.Sec3.brute_solves` | brute solves Exact Triangle. | `ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/BruteForce.lean` |
| `Light.Sec3.ChooseHost.bySize_spec` | choose solves Exact Triangle. | `ThreeSumApsp/Programs/Sec3/Theorem19/ChooseBySize.lean` |

Lists of procedures: `Light.Sec3.et17Procs` (`ThreeSumApsp/Programs/Sec3/Theorem17/Host/Program.lean`), `Light.Sec3.paramProcs` (`ThreeSumApsp/Programs/Sec3/Theorem17/ClaimAtParameters.lean`).

| Routine | What is proved about it | Lemma | Stated with | Time | Files |
|---|---|---|---|---|---|
| `scanBody` | scan returns 1 if some `c` in the interval has `S(a,b,c) = 0`, and 0 if not; it changes no cell. | `scan_spec` | `scanHit` | `tScan` | `ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/Scan.lean` |
| `bruteBody` | The brute force. In any program that holds `scanBody` as its procedure number `pScan`, `bruteBody pScan` ends within `tBrute n` steps, decides whether the instance has a zero triangle, and changes no cell. | `brute_spec` | `triOf` | `tBrute` | `ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/BruteForce.lean` |
| `primesBody` | primes writes the primes of the window, in increasing order, to dst, and returns their number. | `primes_spec` | `primesList` | `tPrimes` | `ThreeSumApsp/Programs/Sec3/Theorem17/Parameters/Primes.lean` |
| `bitLenBody` | bitLen returns the least len with U < 2^len and changes no cell. | `bitLen_spec` | `bitLen` | `tBitLen` | `ThreeSumApsp/Programs/Sec3/Theorem17/Parameters/Residues.lean` |
| `dblTableBody` | dblTable writes p, 2p, …, 2^len p and changes nothing else. | `dblTable_spec` | `dblList` | `tDblTable` | `ThreeSumApsp/Programs/Sec3/Theorem17/Parameters/Residues.lean` |
| `residBody` | resid returns w mod p and changes no cell. | `resid_meets` | `dblList`, `resid` | `tResid` | `ThreeSumApsp/Programs/Sec3/Theorem17/Parameters/Residues.lean` |
| `residuesBody` | residues writes the residues of a list and changes nothing else. | `residues_spec` | `residList`, `dblList` | `tResidues` | `ThreeSumApsp/Programs/Sec3/Theorem17/Parameters/Residues.lean` |
| `spreadTableBody` | spreadTable: at most 30 N2 + 17 steps. | `spreadTable_spec` | `spreadList` |  | `ThreeSumApsp/Programs/Sec3/Theorem17/Hashing/ZOrder.lean` |
| `szTableBody` | szTable writes p, 4p, …, 4^J p and changes nothing else. | `szTable_spec` |  | `tSzTable` | `ThreeSumApsp/Programs/Sec3/Theorem17/Hashing/SizeTable.lean` |
| `buildZBody` | buildZ, for any two multipliers that keep the places inside the matrix. | `buildZ_spec` | `spread`, `spreadList` | `buildZTime` | `ThreeSumApsp/Programs/Sec3/Theorem17/Hashing/ZOrder.lean` |
| `countZeroBody` | countZero returns the count and leaves the memory as it was. | `countZero_spec` | `countBy`, `spreadList` | `countZeroTime` | `ThreeSumApsp/Programs/Sec3/Theorem17/Hashing/Count.lean` |
| `vlinBody` | vlin writes a + s b to dst and changes nothing else, in at most 23 n + 6 steps. | `vlin_spec` |  |  | `ThreeSumApsp/Programs/Sec3/Theorem17/Hashing/RingOps.lean` |
| `cconvBody` | cconv writes the cyclic convolution to dst and changes nothing else, in at most 32 p² + 21 p + 6 steps. | `cconv_spec` | `cconv` |  | `ThreeSumApsp/Programs/Sec3/Theorem17/Hashing/RingOps.lean` |
| `phaseBody` | A phase adds s1 M to c1 and s2 M to c2, where M = (a1 + sA a2) · (b1 + sB b2), and changes nothing else but the scratch space. | `phase_meets` | `strassenList` | `strSteps` | `ThreeSumApsp/Programs/Sec3/Theorem17/Hashing/Strassen.lean` |
| `strBody` | Strassen's algorithm, at every level. | `strassen_spec` | `strassenList` | `strSteps` | `ThreeSumApsp/Programs/Sec3/Theorem17/Hashing/Strassen.lean` |
| `countPrimeBody` | countPrime returns the count of the proof of Theorem 17 for the prime p, and changes only cells of its work area. | `countPrime_spec` | `countOf` | `countTime` | `ThreeSumApsp/Programs/Sec3/Theorem17/Hashing/CountPrime.lean` |
| `choosePrimeBody` | choosePrime returns the first prime of the range with the smallest count (0 if the range has no prime), and changes only cells of its work area. | `choosePrime_spec` | `chosenPrime`, `bitLen` | `chooseTime` | `ThreeSumApsp/Programs/Sec3/Theorem17/Hashing/ChoosePrime.lean` |
| `queryCapNatBody` | queryCapNat returns ⌊n²/√D⌋, for D ≥ 1. | `queryCapNat_meets` | `queryCapNat` | `tQueryCapNat` | `ThreeSumApsp/Programs/Sec3/Theorem17/Parameters/Sizes.lean` |
| `ceilDivBody` | ceilDiv returns ⌈a/b⌉, for b ≥ 1. | `ceilDiv_meets` |  | `tCeilDiv` | `ThreeSumApsp/Programs/Sec3/Theorem17/Parameters/Sizes.lean` |
| `classesBody` | classes writes the starts of the classes and the rows and columns of the pairs, class after class. | `classes_meets` | `classStarts`, `queryRows`, `queryCols` | `tClasses` | `ThreeSumApsp/Programs/Sec3/Theorem17/Instances/Classes.lean` |
| `chunksBody` | chunks writes the table of the chunks and returns their number. | `chunks_meets` | `chunkTabOf` | `tChunks` | `ThreeSumApsp/Programs/Sec3/Theorem17/Instances/Chunks.lean` |
| `writeXBody` | writeX writes the matrix X and changes nothing else. | `writeX_spec` | `xList` | `tWriteX` | `ThreeSumApsp/Programs/Sec3/Theorem17/Instances/WriteMatrices.lean` |
| `writeYBody` | writeY writes the matrix Y and changes nothing else. | `writeY_spec` | `yList` | `tWriteY` | `ThreeSumApsp/Programs/Sec3/Theorem17/Instances/WriteMatrices.lean` |
| `scanPairsBody` | scanPairs returns the new value of `f`; no cell changes; the time depends on the number of scans that are made. | `scanPairs_spec` |  | `tScanPairs` | `ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/ScanPairs.lean` |
| `hostLoopBody` | hostLoop returns 1 if a scan has found a zero triangle, and 0 if not, and changes no cell below x. | `hostLoop_spec` |  | `tHostLoop` | `ThreeSumApsp/Programs/Sec3/Theorem17/Host/Loop.lean` |
| `et17Body` | et17 decides Exact Triangle. In every program `P₀ ++ R` that satisfies the context `Et17Ctx` (it holds the solver, the procedures of the host and the two parameter procedures), on an instance with `x.Pre μ fr` and within limits that allow for `hostNeed`, the body of et17 ends within `hostTime` steps in a state that satisfies `etTask.Post`. | `et17_spec` |  | `hostTime` | `ThreeSumApsp/Programs/Sec3/Theorem17/Host/Text.lean`<br>`ThreeSumApsp/Programs/Sec3/Theorem17/Host/Correct.lean` |
| `sieveBody` | sieve(m, out, fr) writes the primes up to m in ascending order to out and returns their number. | `sieve_meets` |  | `sieveTime` | `ThreeSumApsp/Lang/Lib/Sieve.lean` |
| `powLtBody` | powLt, for g ≥ 1, returns 1 if g^e < t and 0 if not, in at most 16 e + 14 steps. | `powLt_meets` |  |  | `ThreeSumApsp/Programs/Sec3/Theorem17/Parameters/Sizes.lean` |
| `rootCeilBody` | rootCeil returns the least g with g^e ≥ t, for e ≥ 1 and t ≥ 1. | `rootCeil_meets` | `rootCeil` | `tRootCeil` | `ThreeSumApsp/Programs/Sec3/Theorem17/Parameters/Sizes.lean` |
| `d26Body` | d26 returns ⌊n^{1/18}⌋. | `d26_spec` | `paramD₂₆Nat` | `tD26` | `ThreeSumApsp/Programs/Sec3/Theorem17/Parameters/Sizes.lean` |
| `d5Body` | d5 returns the largest power of four that is at most n^{1/18}. | `d5_spec` | `paramD₂₆Nat`, `paramD₅Nat` | `tD5` | `ThreeSumApsp/Programs/Sec3/Theorem17/Parameters/Sizes.lean` |
| `g5Body` | g5 returns ⌈D^{1/36}⌉, for D ≥ 1. | `g5_spec` | `paramG₅Nat` | `tG5` | `ThreeSumApsp/Programs/Sec3/Theorem17/Parameters/Sizes.lean` |
| `g26Body` | g26 returns ⌈D^{0.0315}⌉, for D ≥ 1. | `g26_spec` | `paramG₂₆Nat` | `tG26` | `ThreeSumApsp/Programs/Sec3/Theorem17/Parameters/Sizes.lean` |
| `bySizeBody` | choose solves Exact Triangle. | `bySize_spec` |  | `bySizeTime` | `ThreeSumApsp/Programs/Sec3/Theorem19/ChooseBySize.lean` |

The programs also run routines that are listed under other items: 29 under Theorem 5, 1 under Corollaries 15 and 16, 12 under Corollary 26, 18 under Theorem 30.

## Theorem 22 (page 36)

Statements: `wordRam_theorem_22_first`, `wordRam_theorem_22_second`, `wordRam_theorem_22_threeSum`, proved in `ThreeSumApsp/RunningTimes/Sec3/Theorem22.lean`.

"Plug Theorem 19 into Theorem 21."  Each bound has three ingredients.

1. The paper's deduction between running times, proved for every reading `M` of the sentence "is
   solved by a deterministic algorithm in time T" (lemmas such as `threeSum_of_uniform_theorem_21a`;
   nothing is assumed about `M`).
2. The reading `lightModel`, in which the sentence means that a program of the light language solves
   the task within T steps.  For this reading the reductions that Theorem 21 cites are theorems,
   because they are written as programs that call an arbitrary solver (`Sec3.claim_…`); so
   Theorem 21 holds for it: `claim_theorem_21a` for 3SUM, `claim_theorem_21b_minPlus` and
   `claim_theorem_21b_apsp` for the (min,+)-product and APSP.
3. The way to the machine: a solver of a task, with one more procedure for the input layout,
   compiled, is a program of the word RAM that takes a constant times as many steps
   (`Sec3.realized_threeSum`, `realized_minPlusProduct`, `realized_apsp`).

From a bound `O(s^{3−δ} (log s)^e)` for Exact Triangle this gives

* 3SUM in `O(n^a)` time for every `a > 2 − δ/2` (`threeSum_of_uniform`);
* the (min,+)-product and APSP in `O(n^{3−δ/3} (log n)^{O(1)})` time (`minPlus_polylog_of_uniform`,
  `apsp_polylog_of_uniform`), and so in `O(n^a)` time for every `a > 3 − δ/3`
  (`SolvedInPolylogTime.solvedInTime`).

The theorem is the case `δ = 1/648` (using Theorem 5) and the case `δ = ε' = 0.00175` (using
Corollary 26).  For 3SUM the programs lose polylogarithmic factors only
(`Theorem22.threeSum_polylog`); the printed form with `n^{o(1)}` follows
(`SolvedInPolylogTime.solvedInLittleOTime`).

| Lemma or definition | What it says | File |
|---|---|---|
| `ThreeSumApsp.threeSum_of_uniform_theorem_21a` | "Plug Theorem 19 into Theorem 21", 3SUM, in general form: with exponent `3 - δ` for Exact Triangle the time for 3SUM is `n^{2-δ/2+o(1)}`. | `ThreeSumApsp/TimeClaims/Sec3/Theorem21_22.lean` |
| `Light.lightModel` | The reading of "is solved in time T" by programs of the light language. | `ThreeSumApsp/Programs/LightModel.lean` |
| `Light.Sec3.claim_theorem_21a` | Theorem 21(a): 3SUM from Exact Triangle, through Convolution-3SUM. | `ThreeSumApsp/RunningTimes/Sec3/Theorem22.lean` |
| `Light.Sec3.claim_theorem_21b_minPlus` | Theorem 21(b): the (min,+)-product from Exact Triangle, through Negative Triangle. | `ThreeSumApsp/RunningTimes/Sec3/Theorem22.lean` |
| `Light.Sec3.claim_theorem_21b_apsp` | Theorem 21(b): APSP from Exact Triangle, through the (min,+)-product. | `ThreeSumApsp/RunningTimes/Sec3/Theorem22.lean` |
| `Light.Sec3.realized_threeSum` | 3SUM: if the task is solved in time T, then 3SUM is solved on the word RAM within a constant times T. | `ThreeSumApsp/RunningTimes/Sec3/Theorem22/ThreeSumLayout.lean` |
| `Light.Sec3.realized_minPlusProduct` | The (min,+)-product: if the task is solved in time T, then the product is computed on the word RAM within a constant times T. | `ThreeSumApsp/RunningTimes/Sec3/Theorem22/MinPlusLayout.lean` |
| `Light.Sec3.realized_apsp` | APSP: if the task is solved in time T, then APSP is solved on the word RAM within a constant times T. | `ThreeSumApsp/RunningTimes/Sec3/Theorem22/ApspLayout.lean` |
| `Light.Sec3.threeSum_of_uniform` | 3SUM in `O(n^a)` time for every `a > 2 − δ/2`. | `ThreeSumApsp/RunningTimes/Sec3/Theorem22.lean` |
| `Light.Sec3.minPlus_polylog_of_uniform` | The (min,+)-product in `O(n^{3−δ/3} (log n)^{O(1)})` time. | `ThreeSumApsp/RunningTimes/Sec3/Theorem22.lean` |
| `Light.Sec3.apsp_polylog_of_uniform` | APSP in `O(n^{3−δ/3} (log n)^{O(1)})` time. | `ThreeSumApsp/RunningTimes/Sec3/Theorem22.lean` |
| `ThreeSumApsp.WordRam.SolvedInPolylogTime.solvedInTime` | A bound `O(n^a (log n)^{O(1)})` is a bound `O(n^a')` for `a < a'`. | `ThreeSumApsp/Machine/Solving.lean` |
| `ThreeSumApsp.Theorem22.threeSum_polylog` | Theorem 22, on the word RAM, with `(log n)^{O(1)}` in place of `n^{o(1)}`: 3SUM in `O(n^{2−1/1296} (log n)^{O(1)})` and in `O(n^{2−ε'/2} (log n)^{O(1)})` time. | `ThreeSumApsp/RunningTimes/Sec3/Theorem22.lean` |
| `ThreeSumApsp.WordRam.SolvedInPolylogTime.solvedInLittleOTime` | A bound `O(n^a (log n)^{O(1)})` is a bound `n^{a+o(1)}`. | `ThreeSumApsp/Machine/PolylogIsLittleO.lean` |
| `Light.Sec3.claim_exactTriangleUniform_usingTheorem5` | The bound using Theorem 5, for all numbers of vertices and all bounds on the weights. | `ThreeSumApsp/RunningTimes/Sec3/Theorem19.lean` |
| `Light.Sec3.claim_exactTriangleUniform_usingCorollary26` | The bound using Corollary 26, for all numbers of vertices and all bounds on the weights. | `ThreeSumApsp/RunningTimes/Sec3/Theorem19.lean` |
| `ThreeSumApsp.Theorem21a.of_CH20_VW13` | Theorem 21(a) from two reductions: [CH20, Theorem 5.1] followed by [VW13, Theorem 4.3]. | `ThreeSumApsp/TimeClaims/Sec3/Theorem21_22.lean` |
| `Light.Sec3.ChanHe.claim_CH20_Theorem_5_1` | [CH20, Theorem 5.1] for programs of the light language: 3SUM from Convolution-3SUM. | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Program.lean` |
| `Light.Sec3.claim_VW13_Theorem_4_3` | [VW13, Theorem 4.3] for programs of the light language: Convolution-3SUM from Exact Triangle. | `ThreeSumApsp/Programs/Sec3/Theorem21a/Convolution/TimeBound.lean` |
| `ThreeSumApsp.Theorem21b.minPlus_of_VW13_VW18` | Theorem 21(b), (min,+)-product, from two reductions: [VW13, Theorem 3.3] followed by [VW18, Theorem 4.2]. | `ThreeSumApsp/TimeClaims/Sec3/Theorem21_22.lean` |
| `Light.Sec3.claim_VW13_Theorem_3_3` | [VW13, Theorem 3.3] for programs of the light language: Negative Triangle from Exact Triangle, with c = 6. | `ThreeSumApsp/Programs/Sec3/Theorem21b/NegativeTriangle/TimeBound.lean` |
| `Light.Sec3.claim_VW18_Theorem_4_2` | [VW18, Theorem 4.2]: the (min,+)-product from Negative Triangle. | `ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/TimeBound.lean` |
| `ThreeSumApsp.Theorem21b.apsp_of_minPlus` | Theorem 21(b), APSP: repeated squaring on top of the (min,+)-product. | `ThreeSumApsp/TimeClaims/Sec3/Theorem21_22.lean` |
| `Light.Sec3.claim_apspFromMinPlus` | APSP from the (min,+)-product, for programs of the light language. | `ThreeSumApsp/Programs/Sec3/Theorem21b/Apsp/TimeBound.lean` |
| `ThreeSumApsp.FromClaims.solvedInTime_of_claim` | A claim "solved in `O(n^a)` time on numbers of absolute value at most `n^κ`, for every `κ`", in a reading `S` of "is solved in time T" that is realized, gives programs. | `ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean` |
| `ThreeSumApsp.FromClaims.solvedInPolylogTime_of_claim` | A claim "solved in `O(n^a (log n)^{O(1)})` time on numbers of absolute value at most `n^κ`, for every `κ`", in a reading `S` of "is solved in time T" that is realized, gives programs. | `ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean` |
| `ThreeSumApsp.minPlus_of_uniform_theorem_21b` | "Plug Theorem 19 into Theorem 21", (min,+)-product, in general form: with exponent `3 - δ` for Exact Triangle the time is `O(n^{3-δ/3} (log n)^{O(1)})`. | `ThreeSumApsp/TimeClaims/Sec3/Theorem21_22.lean` |
| `ThreeSumApsp.apsp_of_uniform_theorem_21b` | "Plug Theorem 19 into Theorem 21", APSP, in general form. | `ThreeSumApsp/TimeClaims/Sec3/Theorem21_22.lean` |
| `Light.Sec3.threeSum_solvedInPolylogTime` | 3SUM in time `O(n^{2−δ/2} (log n)^{O(1)})` on the word RAM, if Exact Triangle is solved in the uniform time with exponent `3 − δ`. | `ThreeSumApsp/RunningTimes/Sec3/Theorem22/ThreeSumPolylog.lean` |
| `Light.Sec3.ChanHe.isHost_s3` | The host: from every solver of Convolution-3SUM, the procedures of the reduction make a solver of 3SUM. | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Program.lean` |
| `Light.Sec3.isHost_nt` | Negative Triangle from Exact Triangle: from every solver of Exact Triangle, the three procedures affine, prefDown, nt make a solver of Negative Triangle. | `ThreeSumApsp/Programs/Sec3/Theorem21b/NegativeTriangle/Host.lean` |
| `Light.Sec3.MinPlusFromNeg.findTime_dominated` | Finding from deciding: the time grows by a constant factor only. | `ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/TimeBound.lean` |
| `Light.Sec3.MinPlusFromNeg.pairsTime_dominated` | All pairs from finding: O(n²) questions at the size ⌈n^{1/3}⌉. | `ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/TimeBound.lean` |
| `Light.Sec3.MinPlusFromNeg.mpTime_dominated` | The product from all pairs: O(log u) calls, if a call takes at least n² steps. | `ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/TimeBound.lean` |
| `Light.Sec3.isHost_find` | [VW18, Lemma 4.1]: finding a negative triangle from deciding whether there is one. | `ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/FindNegativeTriangle.lean` |
| `Light.Sec3.isHost_pairs` | The middle step of [VW18, Theorem 4.2]: all pairs with a witness, from finding a negative triangle. | `ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/AllPairs.lean` |
| `Light.Sec3.isHost_mp` | The (min,+)-product from "all pairs", as a host. | `ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/BitSearch.lean` |
| `Light.Sec3.isHost_ap` | APSP from the (min,+)-product, as a host. | `ThreeSumApsp/Programs/Sec3/Theorem21b/Apsp/Host.lean` |
| `Light.Sec3.threeSum_polylog_claim` | 3SUM in time `O(n^{2−δ/2} (log n)^{O(1)})` by programs of the light language, if Exact Triangle is solved in the uniform time with exponent `3 − δ`. | `ThreeSumApsp/RunningTimes/Sec3/Theorem22/ThreeSumPolylog.lean` |

| Routine | What is proved about it | Lemma | Stated with | Time | Files |
|---|---|---|---|---|---|
| `emodBody` | emod(x, M, fr) returns the remainder of x modulo M and changes no cell below the free pointer. | `emod_meets` |  | `emodTime` | `ThreeSumApsp/Lang/Lib/Emod.lean` |
| `cbrtCeilBody` | cbrtCeil(n) returns the least s with s³ ≥ n and leaves the memory as it is. | `cbrtCeil_meets` |  | `cbrtCeilTime` | `ThreeSumApsp/Lang/Lib/Logs.lean` |
| `clog2Body` | clog2(x) returns ⌈log₂ x⌉ and leaves the memory as it is. | `clog2_meets` |  | `clog2Time` | `ThreeSumApsp/Lang/Lib/Logs.lean` |
| `halfBody` | half(h) returns ⌈h/2⌉ and leaves the memory as it is. | `half_meets` |  | `halfTime` | `ThreeSumApsp/Lang/Lib/Logs.lean` |
| `log2Body` | log2(x) returns ⌊log₂ x⌋ and leaves the memory as it is. | `log2_meets` |  | `log2Time` | `ThreeSumApsp/Lang/Lib/Logs.lean` |
| `mergeBody` | merge(a, na, b, nb, dst) writes `List.merge` of the two lists to dst and changes nothing else. | `merge_meets` |  | `mergeTime` | `ThreeSumApsp/Lang/Lib/Merge.lean` |
| `sortBody` | sort(n, a, fr) leaves a sorted permutation of the list at a. | `sort_meets` |  | `sortTime` | `ThreeSumApsp/Lang/Lib/MergeSort.lean` |
| `bitsBody` | bits(len, s, V, Λ, bt, fr) writes the table of the binary digits of the labels `x + V` of the `len` numbers from `s` to `bt` (`len Λ` cells). | `bits_spec` |  | `tBits` | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Bits.lean` |
| `pickBody` | pick(len, s, bt, Λ, β, x, β', x', two, out) writes the elements selected by one binary digit (`two = 0`) or by two to `out` (room for `len` cells) and returns their number. | `pick_spec` |  | `tPick` | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Bits.lean` |
| `collBody` | coll(len, s, M, cnt, fr) returns the number of colliding ordered pairs of the set at `s` modulo `M`. | `coll_spec` |  | `tColl` | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Buckets.lean` |
| `heavyBody` | heavy(len, s, M, out, cnt, fr) writes the heavy elements of the set at `s` modulo `M` to `out` (room for `len` cells) and returns their number. | `heavy_spec` |  | `tHeavy` | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Buckets.lean` |
| `residBody` | resid(len, s, sg, M, key, fr) writes the remainders of `sg · x` modulo `M`, for the `len` numbers `x` from `s`, to `key`. `sg` is 1 or -1. | `resid_spec` |  | `tResid` | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Buckets.lean` |
| `tallyBody` | tally(len, key, cnt, δ) adds `δ` to the cell `cnt + k` for each of the `len` numbers `k` from `key`. | `tally_spec` |  | `tTally` | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Buckets.lean` |
| `distinctBody` | distinct(n, a, val, mul): the `n` cells from `a` hold a sorted list. | `distinct_spec` |  | `tDistinct` | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Distinct.lean` |
| `twiceBody` | twice(nd, val, mul, out) writes the doubles of the values that are not 0 and occur at least twice to `out` (room for `nd` cells), and returns their number. | `twice_spec` |  | `tTwice` | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Distinct.lean` |
| `zeroThreeBody` | zeroThree(nd, val, mul) returns 1 if the value 0 occurs at least three times, and 0 if not; it writes no cell. | `zeroThree_spec` |  | `tZeroThree` | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Distinct.lean` |
| `gridBody` | grid(nd, val, bt, Λ, A, n, f, cx, fr) returns 1 if some splitting gives a yes-instance, and 0 if not. | `grid_spec` |  | `tGrid` | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Grid.lean` |
| `rowBody` | row(β, nd, val, bt, Λ, A, n, f, cx, fr) returns a number between 0 and `2Λ` that is positive exactly if some splitting `(β, β', v)` gives a yes-instance. | `row_spec` |  | `tRow` | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Grid.lean` |
| `hostBody` | The host: from the specification of core to what the task 3SUM asks. | `host_spec` | `vecOf` |  | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Host.lean` |
| `modulusBody` | modulus(s₁, l₁, s₂, l₂, s₃, l₃, Λ, np, pr, cnt, fr) returns the modulus of the node. | `modulus_spec` |  | `tModulus` | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Modulus.lean` |
| `searchBody` | search(mult, s₁, l₁, s₂, l₂, s₃, l₃, b₁, b₂, b₃, np, pr, cnt, fr) returns the least good prime up to `m`, and 1 if there is none. | `search_spec` |  | `tSearch` | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Modulus.lean` |
| `nodeArrayBody` | nodeArray(M, s₁, l₁, s₂, l₂, s₃, l₃, V, m, y, cnt, fr) writes the first `8 m²` cells of the one-array instance of the node to `y`. | `nodeArray_spec` |  | `tNodeArray` | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/NodeArray.lean` |
| `nodesBody` | nodes(f, s₁, l₁, s₂, l₂, s₃, l₃, cx, fr) returns 1 if the one-array instance of some node of the tree with `f` levels is a yes-instance at length `8 m²`, and 0 if not. `T` and `r` are the time and the need of the Convolution-3SUM solver that it calls. | `nodes_spec` |  |  | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Nodes.lean` |
| `paramsBody` | params(n, V, out) writes `Lam V`, `mPar n V` and `fuel n` to the three cells from `out`. | `params_spec` |  | `tParams` | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Parameters.lean` |
| `prepBody` | prep(n, V, Λ, m, x, b): the input `X` stands at `x`. | `prep_spec` |  | `tPrep` | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Prepare.lean` |
| `coreBody` | core(n, V, x, b), with `V = 2U`: the input `X`, `n` numbers of absolute value at most `U`, stands at `x`, below the free pointer `b`. | `core_spec` | `vecOf` | `coreTime` | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Reduction.lean` |
| `roundBody` | round(β, β', b, nd, val, bt, Λ, A, n, f, cx, fr), with `b` = 1 for `v = true` and 0 for `v = false`, returns 1 if the splitting gives a yes-instance, and 0 if not. | `round_spec` |  | `tRound` | `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Round.lean` |
| `convFillBody` | convFill writes the three matrices of instance number s, changes no cell before the first or after the last of them, and takes O(t²) steps. | `convFill_meets` | `convAB`, `convBC`, `convAC` | `convFillTime` | `ThreeSumApsp/Programs/Sec3/Theorem21a/Convolution/Fill.lean` |
| `c3Body` | The host is correct, in every program that begins with the solver's and contains the two helpers. | `c3_spec` | `vecOf` | `c3Time` | `ThreeSumApsp/Programs/Sec3/Theorem21a/Convolution/Host.lean` |
| `apBody` | The host is correct, in every program that begins with the solver's program and has the three passes. | `ap_spec` |  | `apTime` | `ThreeSumApsp/Programs/Sec3/Theorem21b/Apsp/Host.lean` |
| `apInitBody` | apInit writes the weight matrix to A, changes nothing else, and takes at most 23 n² + 17 n + 18 steps. | `apInit_meets` | `weightList` |  | `ThreeSumApsp/Programs/Sec3/Theorem21b/Apsp/Passes.lean` |
| `apOutBody` | apOut writes the pairs to out, changes nothing else, and takes at most 30 len + 8 steps. | `apOut_meets` |  |  | `ThreeSumApsp/Programs/Sec3/Theorem21b/Apsp/Passes.lean` |
| `clipBody` | clip writes the clipped list to dst, changes nothing else, and takes at most 23 len + 6 steps. | `clip_meets` | `clip` |  | `ThreeSumApsp/Programs/Sec3/Theorem21b/Apsp/Passes.lean` |
| `askBody` | ask asks the solver about the triple of blocks at the offsets oI, oK, oJ, and changes no cell below the free pointer. | `ask_meets` | `BlockDone`, `Witness` | `askTime` | `ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/AllPairs.lean` |
| `maskBody` | mask turns the block A of V held at ac into the third matrix of the instance, with the block O of marks held at tmp, and changes nothing else. | `mask_meets` | `maskNeg` | `maskTime` | `ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/AllPairs.lean` |
| `pairsBody` | allPairs solves the task. | `pairs_spec` |  | `pairsTime` | `ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/AllPairs.lean` |
| `mpBody` | The host is correct, in every program that begins with the solver's program and has the three passes. | `mp_spec` |  | `mpTime` | `ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/BitSearch.lean` |
| `subCopyBody` | subCopy writes the block of the matrix L at src to dst and changes nothing else. | `subCopy_meets` | `subMat` | `subCopyTime` | `ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/CopyBlock.lean` |
| `findBody` | find returns 1 and writes a negative triangle to the cells from `res` if there is one, and returns 0 if there is none (`findTask`), within `findTime` steps. | `find_spec` |  | `findTime` | `ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/FindNegativeTriangle.lean` |
| `probeBody` | probe returns 1 if the sub-instance of side h at the offsets a0, b0, c0 has a negative triangle, and 0 if not, and changes no cell below the free pointer. | `probe_meets` | `NegAt` | `probeTime` | `ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/FindNegativeTriangle.lean` |
| `addcBody` | addc writes the list with x added to every entry to dst and changes nothing else. | `addc_meets` |  |  | `ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/Passes.lean` |
| `bumpBody` | bump adds x (1 − flag) to every entry of the list at lo and changes nothing else. | `bump_meets` |  |  | `ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/Passes.lean` |
| `ntBody` | nt is correct, in every program that begins with the solver's program and has the two loops over arrays. | `nt_spec` | `triOf` | `ntTime` | `ThreeSumApsp/Programs/Sec3/Theorem21b/NegativeTriangle/Host.lean` |
| `affineBody` | affine writes the list of the numbers m x + c, for x in the list at src, to dst, and changes nothing else. | `affine_meets` | `affL` |  | `ThreeSumApsp/Programs/Sec3/Theorem21b/NegativeTriangle/Passes.lean` |
| `prefDownBody` | prefDown makes one step on every pair (q[i], r[i]), and changes nothing else. | `prefDown_meets` |  |  | `ThreeSumApsp/Programs/Sec3/Theorem21b/NegativeTriangle/Passes.lean` |

The programs also run routines that are listed under other items: 29 under Theorem 5, 34 under Theorem 19, 1 under Corollaries 15 and 16, 12 under Corollary 26, 18 under Theorem 30.

## Theorems 24 and 25 (page 39)

Statements: `wordRam_theorem_24`, `wordRam_theorem_25`, proved in `ThreeSumApsp/RunningTimes/Sec4/Theorem24_25.lean`.

Theorem 24, as in the paper: for `ε < ε*` and `q > 0` choose `c` and `θ` with `ε < R_c(γ)` and with
the `q` of Corollary 31 below the given one (`exists_admissible`), and apply Corollary 31.
Theorem 25, as in the paper: "Apply Theorem 24 with q := κ/2, and ask one query for each position of
W."  A statement "there are programs" gives no program that another one could call, so the lemma
`Theorem24.with_queries` says two things of one `γ`: there is the data structure of Theorem 24, and
there is a program that computes the entries at every set `W` of positions in
`O(N² log² D/D^γ + |W| D^q log D)` time.  In its proof both come from one choice of `c` and `θ`, and
the program is the one of `Corollary32.from_one`, which preprocesses and asks one query for each
position of `W`.  Theorem 24 is the first half of the lemma.  Theorem 25 is its second half at
`q := κ/2`, with `γ' := min{γ, κ/2}` and the sum of the two times from `Theorem25.time`.
The programs are those of Corollaries 31 and 32; only the bounds are rewritten
(`exists_isDataStructure_of_dominated`, `exists_solves_of_dominated`).

| Lemma or definition | What it says | File |
|---|---|---|
| `ThreeSumApsp.exists_admissible` | The choice of c and θ in the proof of Theorem 24. | `ThreeSumApsp/Sec4/Corollary31/Limit.lean` |
| `ThreeSumApsp.Theorem24.with_queries` | Theorem 24, and what the proof of Theorem 25 does with it: "ask one query for each position of W". | `ThreeSumApsp/RunningTimes/Sec4/Theorem24_25.lean` |
| `ThreeSumApsp.Corollary32.from_one` | Preprocess `X` and `Y` by Corollary 31 and "ask one query for each position of W" (proof of Theorem 25; "With Corollary 31 in place of Theorem 24, the same argument gives explicit exponents"), on the word RAM, with `D = 1` included: the entries at every set `W` of positions in `O(\|W\| D^q (log D + 1) + N² (log D + 1)² / D^γ)` time. | `ThreeSumApsp/RunningTimes/Sec4/Corollary31_32.lean` |
| `ThreeSumApsp.Theorem25.time` | Proof of Theorem 25: "As \|W\| ≤ N²/D^κ, this takes O(N² log² D/D^γ + \|W\| D^{κ/2} log D) = O(N² log² D/D^{γ'}) time, where γ' := min{γ, κ/2}." | `ThreeSumApsp/Sec4/Corollary32.lean` |
| `ThreeSumApsp.WordRam.exists_isDataStructure_of_dominated` | A data structure with the bounds `O(f)`, `O(f)`, `O(g)` is one with the bounds `O(f')`, `O(f')`, `O(g')` if `f = O(f')` and `g = O(g')`. | `ThreeSumApsp/Machine/Solving.lean` |
| `ThreeSumApsp.WordRam.exists_solves_of_dominated` | A program that solves a problem in time `O(f)` solves it in time `O(f')` if `f = O(f')`. | `ThreeSumApsp/Machine/Solving.lean` |
| `ThreeSumApsp.wordRam_corollary_31` | Corollary 31, on the word RAM. | `ThreeSumApsp/RunningTimes/Sec4/Corollary31_32.lean` |
| `ThreeSumApsp.dominated_wanted_add` | Proof of Theorem 25: the preprocessing and, for each of `w` positions, one query with an exponent `q ≤ q'` take `O(N² log² d / d^γ + w d^{q'} log d)` time, with `log d` for `log d + 1`. | `ThreeSumApsp/RunningTimes/Sec4/Corollary31_32/Arithmetic.lean` |


The programs also run routines that are listed under other items: 29 under Theorem 5, 12 under Corollary 26, 18 under Theorem 30.

## Corollary 26 (page 40)

Statements: `wordRam_corollary_26`, `wordRam_corollary_26_wanted`, proved in `ThreeSumApsp/RunningTimes/Sec4/Corollary26.lean`.

In the paper it is Theorem 30 with `L = 21m` and `t = ⌈m/9⌉` (the entry `c = 21`, `q = 0.43` of
Table 2), "with the logarithmic factors absorbed into the exponents".  The program is
`Light.Sec4.program26`: the program with rational parameters in its text (`Light.Sec4.program31`)
at 21, 1/9 and the threshold 60 (`Light.Sec4.ratParams26`).

The preprocessing finds `m = ⌈log₄ D⌉` and compares it with 60 (`Light.Sec4.program26_pre31`).
"For m ≥ 60, Theorem 30 thus applies": the preprocessing finds `L = 21m` and `t = ⌈m/9⌉`
(`Light.Sec4.program26_levels31`, `Light.Sec4.program26_switch31`), pads the inner dimension to
`4^m`, calls the preprocessing of Theorem 30, and stores the flag 1
(`Light.Sec4.pre31_program26_above`); a query calls the query of Theorem 30
(`Light.Sec4.query31_program26_above`).  "(For m < 60, D is bounded by a constant, and the corollary
holds trivially.)": the preprocessing stores the flag 0, and a query computes an inner product
(`Light.Sec4.program26_query31`, `Light.Sec4.pre31_program26_below`,
`Light.Sec4.query31_program26_below`).

On the inputs with `N ≥ D^18` and `m ≥ 60` the two costs of Theorem 30 at these parameters are
`O(N²/D^{0.063})` and `O(D^{0.437})` (`Light.Sec4.regime26`, from `Corollary26.costs`), which is
what the two lemmas about the compiled program with parameters ask for
(`Light.Sec4.isDataStructure_of_costsWithin`, `Light.Sec4.solves_of_costsWithin`).  So the compiled
`Light.Sec4.program26` meets the bounds of the corollary (`isDataStructure_program26`,
`solves_program26`), and `wordRam_corollary_26` and `wordRam_corollary_26_wanted`, which say that
there are programs, follow.

The last sentence of the corollary is proved once more in another form,
`Light.Sec4.claim_corollary_26_wanted`: a procedure that other procedures can call, at any place of
the memory, and that is right on every instance.  Corollary 16, and through it the second bounds of
Theorems 19 and 22, rest on that form, not on `wordRam_corollary_26_wanted`.

| Lemma or definition | What it says | File |
|---|---|---|
| `Light.Sec4.program26` | The program of Corollary 26: the parameters in its text are 21, 1/9 and 60. | `ThreeSumApsp/Programs/Sec4/Corollary26/Program.lean` |
| `Light.Sec4.program31` | The program for the parameters G. | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean` |
| `Light.Sec4.ratParams26` | The parameters of Corollary 26 in the program text: "L := 21m and t := ⌈m/9⌉", and the 60 of "for all m ≥ 60". | `ThreeSumApsp/Programs/Sec4/Corollary26/Regime.lean` |
| `Light.Sec4.program26_pre31` | pre31(N, D, aX, aY, fr) in the program of Corollary 26 finds m and 4^m; for m < 60 it stores the flag 0, for m ≥ 60 it runs preLarge31. | `ThreeSumApsp/Programs/Sec4/Corollary26/Program.lean` |
| `Light.Sec4.program26_levels31` | "L := 21m": the procedure that preLarge31 calls for L counts up to 21 m in steps of 1. | `ThreeSumApsp/Programs/Sec4/Corollary26/Program.lean` |
| `Light.Sec4.program26_switch31` | "t := ⌈m/9⌉": the procedure that preLarge31 calls for t counts up to m in steps of 9. | `ThreeSumApsp/Programs/Sec4/Corollary26/Program.lean` |
| `Light.Sec4.pre31_program26_above` | "For m ≥ 60, Theorem 30 thus applies": the preprocessing leaves the flag 1, the base address, and the data structure of Theorem 30 with L = 21 m and t = ⌈m/9⌉, which makes the cells ready for queries, and changes no cell outside the structure. | `ThreeSumApsp/Programs/Sec4/Corollary26/Program.lean` |
| `Light.Sec4.query31_program26_above` | For m ≥ 60 a query returns the entry in the time of a query of Theorem 30 with L = 21 m and t = ⌈m/9⌉, keeps the cells ready, and changes only cells of the structure behind its first three. | `ThreeSumApsp/Programs/Sec4/Corollary26/Program.lean` |
| `Light.Sec4.program26_query31` | query31(I, J, N, D, aX, aY, fr) in the program of Corollary 26 reads the flag: if it is 1, it calls the query of Theorem 30, and otherwise the inner product. | `ThreeSumApsp/Programs/Sec4/Corollary26/Program.lean` |
| `Light.Sec4.pre31_program26_below` | "(For m < 60, D is bounded by a constant, and the corollary holds trivially.)" The preprocessing takes the time of finding m and 4^m, stores the flag 0, which makes the cells ready for queries, and changes no cell but the three from fr on. | `ThreeSumApsp/Programs/Sec4/Corollary26/Program.lean` |
| `Light.Sec4.query31_program26_below` | "(For m < 60, D is bounded by a constant, and the corollary holds trivially.)" A query returns the entry in the time of an inner product of length D, and changes no cell. | `ThreeSumApsp/Programs/Sec4/Corollary26/Program.lean` |
| `Light.Sec4.regime26` | The regime N ≥ D^18. There is a constant with which, on these inputs, the two bounds of Corollary 26 dominate the two costs of Theorem 30 at L = 21 m and t = ⌈m/9⌉ for m ≥ 60. | `ThreeSumApsp/Programs/Sec4/Corollary26/Regime.lean` |
| `ThreeSumApsp.Corollary26.costs` | Corollary 26, the costs of Theorem 30 at "L := 21m and t := ⌈m/9⌉", in terms of the given `D`: there is a constant `C` such that for all `N ≥ D^{18}` with `m = ⌈log_4 D⌉ ≥ 60` the hypothesis `N ≥ √K N₀` of Theorem 30 holds, the expression (8) is at most `C N²/D^{0.063}`, and the query cost is at most `C D^{0.437}`. | `ThreeSumApsp/Sec4/Corollary26.lean` |
| `Light.Sec4.isDataStructure_of_costsWithin` | The program with the parameters G, compiled, is a data structure on every domain of inputs with entries bounded by N^e, for all bounds Tp (preprocessing time and space) and Tq (query time) that dominate the two costs of Theorem 30. | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean` |
| `Light.Sec4.solves_of_costsWithin` | The program with the parameters G, compiled with the main procedure offlineMain32, computes the wanted entries in time O(\|W\| Tq + Tp), on every domain of inputs with entries bounded by N^e and for all bounds Tp and Tq that dominate the two costs of Theorem 30. | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean` |
| `ThreeSumApsp.isDataStructure_program26` | The compiled `program26` is the data structure of Corollary 26. | `ThreeSumApsp/RunningTimes/Sec4/Corollary26.lean` |
| `ThreeSumApsp.solves_program26` | The compiled `program26` computes the wanted entries within the bound of Corollary 26. | `ThreeSumApsp/RunningTimes/Sec4/Corollary26.lean` |
| `Light.Sec4.claim_corollary_26_wanted` | Corollary 26, last sentence, for programs of the light language. | `ThreeSumApsp/Programs/Sec4/Corollary26/Claim.lean` |
| `Light.Sec4.pre31_program31` | The preprocessing, for all limits. | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean` |
| `Light.Sec4.query31_program31` | A query, for all limits. | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean` |
| `Light.Sec4.costs26` | The costs of Theorem 30 at the parameters of Corollary 26, for m ≥ 60. | `ThreeSumApsp/Programs/Sec4/Corollary26/Regime.lean` |
| `Light.Sec4.programIsDataStructure_of_costsWithin` | The programs with rational parameters are a data structure, on every domain and for all bounds that dominate the costs of Theorem 30. | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Statement.lean` |
| `Light.Sec4.programSolves_of_costsWithin` | The offline form as a light program: on the regime the wanted entries are computed in time O(Tp + \|W\| Tq). | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/OfflineStatement.lean` |
| `Light.Sec4.offline32_program31` | The offline routine, for all limits. | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean` |
| `Light.Sec4.allInstancesTime26_le` | The time of allInstances26 in the regime is within the bound of Corollary 26. | `ThreeSumApsp/Programs/Sec4/Corollary26/AllInstances.lean` |
| `Light.Sec4.allInstances26_program26` | The procedure allInstances26 of `program26` solves the task on all instances: the program holds allInstances26, regimeTest26 and the brute force at their numbers. | `ThreeSumApsp/Programs/Sec4/Corollary26/Claim.lean` |

Lists of procedures: `Light.Sec4.program26` (`ThreeSumApsp/Programs/Sec4/Corollary26/Program.lean`).

| Routine | What is proved about it | Lemma | Stated with | Time | Files |
|---|---|---|---|---|---|
| `log4Body` | log4(D, a) returns m = ⌈log₄ D⌉ and writes 4^m to the cell a. | `log4_meets` |  | `tLog4` | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Contracts.lean` |
| `padXBody` | padX(N, D, D', aX, aX') writes X, padded with zero columns to D' columns, to aX'. | `padX_meets` |  | `tPadX` | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Pad.lean` |
| `ipAtBody` | ipAt(I, J, N, D, aX, aY) returns (XY)[I, J] as an inner product. | `ipAt_meets` |  | `tIpAt` | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/InnerProduct.lean` |
| `pre31Body` | pre31(N, D, aX, aY, fr): m and 4^m; for m < m₀ the flag 0, for m ≥ m₀ preLarge31. | `pre31_meets` |  |  | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean`<br>`ThreeSumApsp/Programs/Sec4/ChoosingParameters/Preprocessing.lean` |
| `query31Body` | query31 reads the flag and calls the query of Theorem 30 if it is 1 and the inner product otherwise; it returns the entry (XY)[I, J] and keeps the structure ready. | `query31_meets` |  |  | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Setup.lean`<br>`ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean` |
| `preMain31Body` | The main procedure of the preprocessing leaves a memory that is ready for queries. | `preMain31_meets` |  | `tPre31` | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Layout.lean` |
| `queryMain31Body` | The main procedure of a query returns the entry and keeps the memory ready. | `queryMain31_meets` |  | `tQuery31` | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Layout.lean` |
| `offline32Body` | offline32(N, D, w, U, x, y, wi, wj, out, fr): preprocess, then ask one query for each wanted position and store its answer. | `offline32_meets` |  |  | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean` |
| `offlineMain32Body` | The main procedure leaves the wanted entries behind the input and returns 1. | `offlineMain32_meets` |  | `tOffline32` | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/OfflineLayout.lean` |
| `allInstances26Body` | allInstances26 solves the task on all instances, in every program that holds allInstances26, regimeTest26 and the brute force at their numbers and in which offline32 satisfies `OfflineSpec32` at the parameters of Corollary 26, also after more procedures are appended. | `allInstances26_solves` |  |  | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean`<br>`ThreeSumApsp/Programs/Sec4/Corollary26/AllInstances.lean` |
| `regimeTest26Body` | The procedure regimeTest26 returns 1 if D^18 ≤ N and 0 if not, and changes no cell. | `regimeTest26_meets` |  |  | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean`<br>`ThreeSumApsp/Programs/Sec4/Corollary26/AllInstances.lean` |
| `ceilMulBody` | Procedure number pn returns ⌈a m / b⌉ on the argument m, and changes no cell. | `ceilMul_meets` |  | `tCeilMul` | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Ceiling.lean` |

The programs also run routines that are listed under other items: 29 under Theorem 5, 18 under Theorem 30.

## Theorem 30 (pages 46 and 47)

Statements: `wordRam_theorem_30`, `wordRam_theorem_30_wanted`, proved in `ThreeSumApsp/RunningTimes/Sec4/Theorem30.lean`.

The route.  The preprocessing and the query are procedures of the light language, proved against the
paper's definitions (`Light.Sec4.preCoreSpec_all`, `Light.Sec4.queryAtSpec_all`; for the program
`Light.Sec4.program30`: `Light.Sec4.preCore_base58`, `Light.Sec4.queryAt_base58`).  The
preprocessing computes the shared encodings of Section 2 and then, for every tile, the trie of its
boxes, filled by the dynamic program of Lemma 29.  A query forms the sum of Lemma 28: the products
at the leaves of order below `t`, read from the encodings, plus the values of the boxes of the
output string, looked up in the trie of the tile.  The running times are bounded by the two costs of
the theorem, and the numbers and addresses that occur are polynomial in `N` ("Word size").  Two
outermost procedures read the input layout, and the compiler turns them into the two programs of the
data structure (`Light.Sec4.theorem_30_of`).  The offline form (9) preprocesses and then asks one
query for each wanted position (`Light.Sec4.theorem_30_wanted_of`).

| Lemma or definition | What it says | File |
|---|---|---|
| `Light.Sec4.preCoreSpec_all` | The same for all limits: the specification assumes Lim30, which contains the standing assumptions. | `ThreeSumApsp/Programs/Sec4/Theorem30/Routines.lean` |
| `Light.Sec4.queryAtSpec_all` | A query at a given place of the memory, for all limits. | `ThreeSumApsp/Programs/Sec4/Theorem30/Routines.lean` |
| `Light.Sec4.program30` | The program of Theorem 30. | `ThreeSumApsp/Programs/Sec4/Theorem30/Program.lean` |
| `Light.Sec4.preCore_base58` | The preprocessing at a given place of the memory, in every program that begins with base58. | `ThreeSumApsp/Programs/Sec4/Theorem30/Program.lean` |
| `Light.Sec4.queryAt_base58` | A query at a given place of the memory, in every program that begins with base58. | `ThreeSumApsp/Programs/Sec4/Theorem30/Program.lean` |
| `Light.Sec4.theorem_30_of` | Theorem 30 on the word RAM, for any program that holds the routines. | `ThreeSumApsp/Programs/Sec4/Theorem30/Layout.lean` |
| `Light.Sec4.theorem_30_wanted_of` | Theorem 30, the offline form, on the word RAM, for any program that holds the routines. | `ThreeSumApsp/Programs/Sec4/Theorem30/OfflineStatement.lean` |
| `Light.Sec4.queryAt_spec` | queryAt meets its specification. | `ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean` |
| `Light.Sec4.specs40` | Every program that holds the routines of Section 4 at their numbers meets all their specifications. | `ThreeSumApsp/Programs/Sec4/Theorem30/Routines.lean` |
| `Light.Sec4.top30` | Theorem 30 as a light program. c0 is the constant of the shared stage, c the exponent of the bound N^c on the entries. | `ThreeSumApsp/Programs/Sec4/Theorem30/Layout.lean` |
| `Light.Sec4.wanted_topSolves` | The offline form of Theorem 30 as a light program. | `ThreeSumApsp/Programs/Sec4/Theorem30/OfflineStatement.lean` |

Lists of procedures: `Light.Sec4.program30` (`ThreeSumApsp/Programs/Sec4/Theorem30/Program.lean`).

| Routine | What is proved about it | Lemma | Stated with | Time | Files |
|---|---|---|---|---|---|
| `nineFirstBody` | nineFirst writes the least string of n digits with lo nines. | `nineFirst_spec` | `nineFirst` | `tNineFirst` | `ThreeSumApsp/Programs/Sec4/Theorem30/NineFirst.lean` |
| `nineNextBody` | nineNext replaces the string by the next one and returns 1, or leaves the last string and returns 0. | `nineNext_spec` | `nineStrs`, `nineNext` | `tNineNext` | `ThreeSumApsp/Programs/Sec4/Theorem30/NineNext.lean` |
| `scatterBody` | scatter writes `Spec.scatter wl (starRunIf star sl)`. | `scatter_spec` | `scatter`, `starRunIf` | `tScatter` | `ThreeSumApsp/Programs/Sec4/Theorem30/Scatter.lean` |
| `starFirstBody` | starFirst writes the copy with the first e nines as stars, and returns the position of its last star. | `starFirst_spec` | `starFirst`, `lastStar` | `tStarFirst` | `ThreeSumApsp/Programs/Sec4/Theorem30/StarFirst.lean` |
| `hornerBody` | horner returns the number with the given decimal digits, and leaves the memory as it was. | `horner_spec` |  | `tHorner` | `ThreeSumApsp/Programs/Sec4/Theorem30/Horner.lean` |
| `lookupBody` | lookup returns the value stored for the string, and leaves the memory as it was. | `lookup_spec` | `WalkOK`, `trieLookup` | `tLookup` | `ThreeSumApsp/Programs/Sec4/Theorem30/Lookup.lean` |
| `insertBody` | insert stores the value for the string: the area then holds `Spec.trieInsert`. | `insert_spec` | `trieInsert`, `InsertOK` | `tInsert` | `ThreeSumApsp/Programs/Sec4/Theorem30/Insert.lean` |
| `newRootBody` | newRoot appends a new vertex to the array, and returns its address. | `newRoot_spec` | `trieNew` | `tNewRoot` | `ThreeSumApsp/Programs/Sec4/Theorem30/Insert.lean` |
| `sumTenBody` | sumTen returns the sum of the values of the ten strings, and leaves the memory as it was. | `sumTen_spec` | `WalkOK`, `trieLookup` | `tSumTen` | `ThreeSumApsp/Programs/Sec4/Theorem30/SumTen.lean` |
| `fillListBody` | fillList inserts the boxes with e stars, with their values, into the trie of their tile. | `fillList_spec` | `nineFirst`, `nineStrs`, `nineNext`, `starFirst`, `lastStar` | `tFillList` | `ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean` |
| `tileBody` | `tile` builds the trie of one tile, with the values of all its boxes, on top of the older tries, and writes its root into the cell behind the older roots. | `tile_spec` | `trieNew`, `fillTrie`, `arrT`, `TrieRep` | `tTile` | `ThreeSumApsp/Programs/Sec4/Theorem30/Tile.lean` |
| `allTilesBody` | `allTiles` builds the tries of all tiles, starting from the trie array [0], and changes nothing below cur or behind the trie area. | `allTiles_spec` | `arrT` | `tAllTiles` | `ThreeSumApsp/Programs/Sec4/Theorem30/AllTiles.lean` |
| `outDigitsBody` | `outDigits` writes the digits of the output string at wd and changes nothing else. | `outDigits_spec` |  | `tOutDigits` | `ThreeSumApsp/Programs/Sec4/Theorem30/OutDigits.lean` |
| `queryCoreBody` | `queryCore` returns the sum `trieQuery` for the output string whose digits are at wd: the products at its leaves of order below t, read from the two encodings, and what the trie with the given root holds for its boxes. | `queryCore_spec` | `trieQuery`, `arrT`, `digitsO`, `boxesOf`, `WalkOK` | `tQueryCore` | `ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean` |
| `preCoreBody` | preCore(L, m, t, N, D, aX, aY, b0) builds the data structure for the matrices at aX and aY in the block from b0 on. | `preCore_spec` | `arrT` | `tPreCore` | `ThreeSumApsp/Programs/Sec4/Theorem30/Preprocessing.lean` |
| `queryAtBody` | queryAt(I, J, b0) returns (XY)[I, J] from the block at b0, of which it changes only cells of the scratch strings WD to SS. | `queryAt_spec` | `trieQuery`, `arrT`, `digitsO`, `boxesOf`, `WalkOK` | `tQueryAt` | `ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean` |
| `wantedCoreBody` | wantedCore writes the wanted entries of XY to out. | `wantedCore_spec` |  | `tWantedCore` | `ThreeSumApsp/Programs/Sec4/Theorem30/Offline.lean` |
| `wantedMainBody` | The main procedure leaves the wanted entries behind the input and returns 1. | `wantedMain_meets` |  | `tWantedCore` | `ThreeSumApsp/Programs/Sec4/Theorem30/OfflineLayout.lean` |
| `queryMainBody` | The main procedure of a query returns the entry and keeps the data structure. | `queryMain_meets` |  | `tQueryAt` | `ThreeSumApsp/Programs/Sec4/Theorem30/Layout.lean` |
| `preMainBody` | The main procedure of the preprocessing builds the data structure behind the input. | `preMain_meets` |  | `tPreCore` | `ThreeSumApsp/Programs/Sec4/Theorem30/Layout.lean` |

The programs also run routines that are listed under other items: 29 under Theorem 5.

## Corollaries 31 and 32 (page 49)

Statements: `wordRam_corollary_31`, `wordRam_corollary_32`, proved in `ThreeSumApsp/RunningTimes/Sec4/Corollary31_32.lean`.

The route.  For rational `c` and `θ` the data structure of Theorem 30 with `L = ⌈cm⌉` levels and
switching order `t = ⌈θm⌉` is one program (`Light.Sec4.program31`), which computes `m`, `L` and `t`
itself.  The parameters include a threshold `m₀`: for `m < m₀` the preprocessing finds `m` and `4^m`
and stores the flag 0, and a query computes an inner product (the paper: "for smaller m the
corollary again holds trivially").  Real `c` and `θ` are replaced by rational ones nearby, for which
`ε` is still admissible, `γ` is no smaller and `q` no larger; at these the two costs of Theorem 30
obey the bounds of the corollaries on the inputs with `D ≤ N^ε` and `m ≥ m₀`
(`Light.Sec4.exists_ratParams`).  The two lemmas about this program, compiled
(`Light.Sec4.isDataStructure_of_costsWithin` for the data structure,
`Light.Sec4.solves_of_costsWithin` for the wanted entries), then give both corollaries in a form
that includes `D = 1` (`Corollary31.from_one`, `Corollary32.from_one`).  The corollaries as
printed, and the bounds without logarithmic factors for every `ε < ε*`
(`dataStructureBelow_wantedBelow_epsStar`), follow by arithmetic alone: the same programs, a smaller
domain, and a bound that dominates the proved one (`exists_isDataStructure_of_dominated`,
`exists_solves_of_dominated`).

| Lemma or definition | What it says | File |
|---|---|---|
| `Light.Sec4.program31` | The program for the parameters G. | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean` |
| `Light.Sec4.exists_ratParams` | The parameters of the program. On every instance with 1 ≤ D ≤ N^ε the two bounds are at least 1, and from the threshold on the hypotheses of Theorem 30 hold and its costs are within a constant times the two bounds. | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/RealParameters.lean` |
| `Light.Sec4.isDataStructure_of_costsWithin` | The program with the parameters G, compiled, is a data structure on every domain of inputs with entries bounded by N^e, for all bounds Tp (preprocessing time and space) and Tq (query time) that dominate the two costs of Theorem 30. | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean` |
| `Light.Sec4.solves_of_costsWithin` | The program with the parameters G, compiled with the main procedure offlineMain32, computes the wanted entries in time O(\|W\| Tq + Tp), on every domain of inputs with entries bounded by N^e and for all bounds Tp and Tq that dominate the two costs of Theorem 30. | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean` |
| `ThreeSumApsp.Corollary31.from_one` | Corollary 31, on the word RAM, with `D = 1` included: preprocessing in `O(N² (log D + 1)² / D^γ)` time and space, and a query in `O(D^q (log D + 1))` time. | `ThreeSumApsp/RunningTimes/Sec4/Corollary31_32.lean` |
| `ThreeSumApsp.Corollary32.from_one` | Preprocess `X` and `Y` by Corollary 31 and "ask one query for each position of W" (proof of Theorem 25; "With Corollary 31 in place of Theorem 24, the same argument gives explicit exponents"), on the word RAM, with `D = 1` included: the entries at every set `W` of positions in `O(\|W\| D^q (log D + 1) + N² (log D + 1)² / D^γ)` time. | `ThreeSumApsp/RunningTimes/Sec4/Corollary31_32.lean` |
| `ThreeSumApsp.dataStructureBelow_wantedBelow_epsStar` | The last sentences of Theorems 3 and 1, on the word RAM, for every `ε < ε*` (the theorems have `ε < 0.1204`): choose `c` and `θ` as in the proof of Theorem 24 (`exists_admissible`), for the wanted entries with `q := κ/2` and `γ' := min{γ, κ/2}` as in the proof of Theorem 25, and give away half of the exponent to absorb the logarithmic factors. | `ThreeSumApsp/RunningTimes/Sec4/Corollary31_32.lean` |
| `ThreeSumApsp.WordRam.exists_isDataStructure_of_dominated` | A data structure with the bounds `O(f)`, `O(f)`, `O(g)` is one with the bounds `O(f')`, `O(f')`, `O(g')` if `f = O(f')` and `g = O(g')`. | `ThreeSumApsp/Machine/Solving.lean` |
| `ThreeSumApsp.WordRam.exists_solves_of_dominated` | A program that solves a problem in time `O(f)` solves it in time `O(f')` if `f = O(f')`. | `ThreeSumApsp/Machine/Solving.lean` |
| `ThreeSumApsp.dominated_preprocessing_log` | The preprocessing, with `log d` for `log d + 1`. | `ThreeSumApsp/RunningTimes/Sec4/Corollary31_32/Arithmetic.lean` |
| `ThreeSumApsp.dominated_query_log` | A query, with `log d` for `log d + 1`. | `ThreeSumApsp/RunningTimes/Sec4/Corollary31_32/Arithmetic.lean` |
| `ThreeSumApsp.dominated_wanted_log` | Corollary 32: the time for at most `N² / d^κ` wanted entries is `O(N² log² d (d^{-γ} + d^{q-κ}))`. | `ThreeSumApsp/RunningTimes/Sec4/Corollary31_32/Arithmetic.lean` |
| `ThreeSumApsp.dominated_preprocessing` | The logarithmic factor of the preprocessing is absorbed by a smaller `γ`. | `ThreeSumApsp/RunningTimes/Sec4/Corollary31_32/Arithmetic.lean` |
| `ThreeSumApsp.dominated_query` | The logarithmic factor of a query is absorbed by a larger exponent. | `ThreeSumApsp/RunningTimes/Sec4/Corollary31_32/Arithmetic.lean` |
| `ThreeSumApsp.dominated_wanted_sparse` | Corollary 32: for at most `N² / d^κ` wanted entries, every `γ'` below `γ` and below `κ - q` absorbs the logarithmic factors. | `ThreeSumApsp/RunningTimes/Sec4/Corollary31_32/Arithmetic.lean` |
| `Light.Sec4.programIsDataStructure_of_costsWithin` | The programs with rational parameters are a data structure, on every domain and for all bounds that dominate the costs of Theorem 30. | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Statement.lean` |
| `Light.Sec4.pre31_program31` | The preprocessing, for all limits. | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean` |
| `Light.Sec4.query31_program31` | A query, for all limits. | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean` |
| `Light.Sec4.programSolves_of_costsWithin` | The offline form as a light program: on the regime the wanted entries are computed in time O(Tp + \|W\| Tq). | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/OfflineStatement.lean` |
| `Light.Sec4.offline32_program31` | The offline routine, for all limits. | `ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean` |

Lists of procedures: `Light.Sec4.program31` (`ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean`).


The programs also run routines that are listed under other items: 29 under Theorem 5, 18 under Theorem 30, 12 under Corollary 26.

## Corollary 39 (page 58)

Statements: `wordRam_corollary_39_zero`, `wordRam_corollary_39_min_max`, proved in `ThreeSumApsp/RunningTimes/Sec5/Corollary39.lean`.

The route, as in the paper: the reduction from `k`-Clique to a triangle problem on `n^{⌊k/3⌋}`
vertices per part, once for each choice of the vertices in the `k mod 3` remaining parts, followed
by Theorem 19. The exponent `k − ε_T ⌊k/3⌋` has `ε_T = 0.0017`, which belongs to the bound of
Theorem 19 using Corollary 26, so that bound is used.  For minimum and maximum weight the triangle
problem is Max-Weight Triangle, which is solved by a search with a solver of Exact Triangle.

The proof has three parts, which `corollary_39_zero_of_theorem_19` and
`corollary_39_min_max_of_theorem_19` put together: the reduction as a program that calls an
arbitrary solver, with its time; the arithmetic of the running times, for every reading of "is
solved in time T"; and the way from programs of the light language to the word RAM.

| Lemma or definition | What it says | File |
|---|---|---|
| `Light.Sec5.corollary_39_zero_of_theorem_19` | Corollary 39, the zero-weight case, on the word RAM, from the bound of Theorem 19 for Exact Triangle for programs of the light language. | `ThreeSumApsp/RunningTimes/Sec5/Corollary39/ZeroWeight.lean` |
| `Light.Sec5.corollary_39_min_max_of_theorem_19` | Corollary 39, minimum and maximum weight, on the word RAM, from the bound of Theorem 19 for Exact Triangle for programs of the light language. | `ThreeSumApsp/RunningTimes/Sec5/Corollary39/MinMaxWeight.lean` |
| `Light.Sec3.claim_theorem_19_usingCorollary26` | Theorem 19, the bound using Corollary 26, for programs of the light language. | `ThreeSumApsp/RunningTimes/Sec3/Theorem19.lean` |
| `ThreeSumApsp.zeroClique_of_theorem_19` | The deduction of the Zero-Weight part of Corollary 39 from Theorem 19 (in the explicit form of `Claim.Theorem_19_explicit`): "Theorem 19 decides whether H has a triangle of weight zero in O(N^{3-ε'} log N) time ... so each graph H costs O(N^{3-ε_T}) time, and the n^t graphs together cost O(n^t N^{3-ε_T}) = O(n^{k-ε_T⌊k/3⌋})." | `ThreeSumApsp/TimeClaims/Sec5/Corollary39.lean` |
| `Light.Sec5.claim_zeroCliqueFromExactTriangle` | The transfer claim of the proof of Corollary 39 holds for programs of the light language. | `ThreeSumApsp/RunningTimes/Sec5/Corollary39/ZeroWeight.lean` |
| `Light.Sec5.realized_zeroKClique` | Zero-Weight k-Clique: if the task is solved in time T, then the problem is solved on the word RAM within a constant times T. | `ThreeSumApsp/RunningTimes/Sec5/Corollary39/ZeroWeightLayout.lean` |
| `ThreeSumApsp.minMaxClique_of_theorem_19_VW13` | The deduction of the Min-Weight and Max-Weight parts of Corollary 39 from Theorem 19 and the cited [VW13, Theorem 3.3]. | `ThreeSumApsp/TimeClaims/Sec5/Corollary39.lean` |
| `Light.Sec5.claim_VW13_Theorem_3_3_max` | Max-Weight Triangle from Exact Triangle. | `ThreeSumApsp/Programs/Sec5/Corollary39/MinMaxWeight/TimeBound.lean` |
| `Light.Sec5.claim_minTriangleFromMax` | Min-Weight Triangle from Max-Weight Triangle. | `ThreeSumApsp/Programs/Sec5/Corollary39/MinMaxWeight/TimeBound.lean` |

| Routine | What is proved about it | Lemma | Stated with | Time | Files |
|---|---|---|---|---|---|
| `optBody` | The host finds a k-clique of maximum (minimum) total weight. | `opt_spec` |  | `optTime` | `ThreeSumApsp/Programs/Sec5/Corollary39/MinMaxWeight/Host.lean` |
| `maxTriBody` | maxTri finds a triangle of maximum weight. | `maxTri_spec` |  |  | `ThreeSumApsp/Programs/Sec5/Corollary39/MinMaxWeight/MaxTriangle.lean` |
| `minTriBody` | minTri finds a minimum weight triangle: it negates the three matrices and asks for a maximum weight triangle. | `minTri_spec` |  | `minTriTime` | `ThreeSumApsp/Programs/Sec5/Corollary39/MinMaxWeight/MinTriangle.lean` |
| `maskBody` | mask writes the matrix with the rows below r₀ and the columns below c₀ switched off, and changes nothing else. | `mask_meets` | `maskL` |  | `ThreeSumApsp/Programs/Sec5/Corollary39/MinMaxWeight/SearchRoutines.lean` |
| `pwBody` | pw writes the powers of two up to x, returns their number, and changes nothing else. | `pw_meets` |  |  | `ThreeSumApsp/Programs/Sec5/Corollary39/MinMaxWeight/SearchRoutines.lean` |
| `kcBody` | The host solves Zero-Weight k-Clique. | `kc_spec` |  | `kcTime` | `ThreeSumApsp/Programs/Sec5/Corollary39/ZeroWeight/Host.lean` |

The programs also run routines that are listed under other items: 29 under Theorem 5, 33 under Theorem 19, 1 under Corollaries 15 and 16, 3 under Theorem 22, 12 under Corollary 26, 18 under Theorem 30.

## Corollary 40 (page 59)

Statements: `wordRam_corollary_40_times`, `wordRam_corollary_40_general_times`, `wordRam_corollary_40_fail`, proved in `ThreeSumApsp/RunningTimes/Sec5/Corollary40.lean`.

The route, as in the paper.  Each of the three hinted problems is solved in phases by programs that
use a data structure for a thin matrix product: the phase after the hint preprocesses, the last
phase asks queries.  For `τ < 1/18` it is the data structure of Corollary 26
(`wordRam_corollary_40_times`), for `τ < ε*` ("General τ") that of Corollary 31 with suitable
parameters (`wordRam_corollary_40_general_times`); for uMv-hinted uMv the conditions are
`τ₁ < τ₂/18` and `τ₁ < ε* τ₂`.  "In each case the phases beat the conjectured
bounds whatever the value of ω": every exponent is below the conjectured one, and larger exponents
are easier to achieve (`AchievesVHinted.mono` and its two companions).  So the three conjectures
fail for `τ < ε*`, by `not_conjecture52_of_achieves` and its two companions, and with them for
`τ < 1/18 < ε*` (`Corollary40.fail_mono`, `wordRam_corollary_40_fail`).

| Lemma or definition | What it says | File |
|---|---|---|
| `ThreeSumApsp.WordRam.AchievesVHinted.mono` | v-hinted Mv: larger exponents for Phases 2 and 3 are easier to achieve. | `ThreeSumApsp/RunningTimes/Sec5/Corollary40.lean` |
| `ThreeSumApsp.not_conjecture52_of_achieves` | Corollary 40: "In each case the phases beat the conjectured bounds". | `ThreeSumApsp/Sec5/Corollary40.lean` |
| `ThreeSumApsp.Corollary40.fail_mono` | Conjectures that fail up to `τ₀` fail up to every smaller bound. | `ThreeSumApsp/RunningTimes/Sec5/Corollary40.lean` |
| `Light.Sec5.achievesVHinted_of_lt_eighteenth` | Corollary 40, Conjecture 5.2, 0 < τ < 1/18: v-hinted Mv is solved on the word RAM with Phase 2 in O(n^{2−0.063τ}) and Phase 3 in O(n^{1+0.437τ}) time. | `ThreeSumApsp/RunningTimes/Sec5/Corollary40/VHintedTimes.lean` |
| `Light.Sec5.achievesMvHinted_of_lt_eighteenth` | Corollary 40, Conjecture 5.7, 0 < τ < 1/18: Mv-hinted Mv is solved on the word RAM with Phase 2 in O(n^{2−0.063τ}) and Phase 3 in O(n^{1+0.437τ}) time. | `ThreeSumApsp/RunningTimes/Sec5/Corollary40/MvHintedTimes.lean` |
| `Light.Sec5.achievesUMvHinted_of_lt_eighteenth` | Corollary 40, Conjecture 5.12, 0 < τ₁ < τ₂/18, τ₂ < 1: uMv-hinted uMv is solved on the word RAM with Phase 2 in O(n^{τ₁}), Phase 3 in O(n^{1+τ₂−0.063τ₁}) and Phase 4 in O(n^{τ₂+0.437τ₁}) time. | `ThreeSumApsp/RunningTimes/Sec5/Corollary40/UMvHintedTimes.lean` |
| `Light.Sec5.achievesUMvHinted_of_lt_epsStar` | The uMv part of Corollary 40, "General τ": for 0 < τ₁ < ε* τ₂ and τ₂ < 1 there is a saving γ > 0. | `ThreeSumApsp/RunningTimes/Sec5/Corollary40/UMvHintedTimes.lean` |
| `Light.Sec5.achievesVHinted_of_genParams` | Corollary 40, Conjecture 5.2, general τ: for parameters c, θ, ε, γ as in `GenParams` and every 0 < τ < ε, v-hinted Mv is solved on the word RAM with Phase 2 in O(n^{2−γτ}) and Phase 3 in O(n^{1+τ/2}) time. | `ThreeSumApsp/RunningTimes/Sec5/Corollary40/VHintedTimes.lean` |
| `Light.Sec5.achievesMvHinted_of_genParams` | Corollary 40, Conjecture 5.7, general τ: for parameters c, θ, ε, γ as in `GenParams` and every 0 < τ < ε with τ ≤ 1/2, Mv-hinted Mv is solved on the word RAM with Phase 2 in O(n^{2−γτ}) and Phase 3 in O(n^{1+τ/2}) time. | `ThreeSumApsp/RunningTimes/Sec5/Corollary40/MvHintedTimes.lean` |
| `ThreeSumApsp.Corollary40.fail_general` | For `τ < ε*` every exponent is below the conjectured one. | `ThreeSumApsp/RunningTimes/Sec5/Corollary40.lean` |
| `Light.Sec5.columnRates_of_lt_eighteenth` | The rates of Corollary 26, for 0 < τ < 1/18: "in O(n²/D^0.063) = O(n^{2−0.063τ}) time" and "O(n D^0.437) = O(n^{1+0.437τ}) time". | `ThreeSumApsp/RunningTimes/Sec5/Corollary40/ColumnTimes.lean` |
| `Light.Sec5.achievesVHinted_of_rates` | v-hinted Mv over a data structure with given rates. | `ThreeSumApsp/RunningTimes/Sec5/Corollary40/VHintedTimes.lean` |
| `Light.Sec5.achievesMvHinted_of_rates` | Mv-hinted Mv over a data structure with given rates. | `ThreeSumApsp/RunningTimes/Sec5/Corollary40/MvHintedTimes.lean` |
| `Light.Sec5.kitRates_corollary26` | Corollary 26's data structure as a kit: for N ≥ D^18 the preprocessing takes O(N²/D^{0.063}) steps and a query O(D^{0.437}). | `ThreeSumApsp/Programs/Sec5/Corollary40/DataStructureBounds.lean` |
| `Light.Sec5.achievesUMvHinted_of_rates` | uMv-hinted uMv over a data structure with given rates. | `ThreeSumApsp/RunningTimes/Sec5/Corollary40/UMvHintedTimes.lean` |
| `Light.Sec5.achievesUMvHinted_of_genParams` | Corollary 40, Conjecture 5.12, general τ: for parameters c, θ, ε, γ as in `GenParams`, 0 < τ₁ < ε τ₂ and 0 < τ₂ < 1, uMv-hinted uMv is solved on the word RAM with Phase 2 in O(n^{τ₁}), Phase 3 in O(n^{1+τ₂−γτ₁}) and Phase 4 in O(n^{τ₂+τ₁/2}) time. | `ThreeSumApsp/RunningTimes/Sec5/Corollary40/UMvHintedTimes.lean` |
| `Light.Sec5.columnRates_of_genParams` | The rates of Corollary 31, for parameters c, θ, ε, γ as in `GenParams` and 0 < τ < ε: "Phase 2 in O(n²/D^γ) = O(n^{2−γτ}) time and Phase 3 in O(n D^{1/2}) = O(n^{1+τ/2}) time". | `ThreeSumApsp/RunningTimes/Sec5/Corollary40/ColumnTimes.lean` |

| Routine | What is proved about it | Lemma | Stated with | Time | Files |
|---|---|---|---|---|---|
| `colBody` | col writes, for every row r, whether the entry (XY)[r, j] is positive. | `col_meets` |  | `tCol` | `ThreeSumApsp/Programs/Sec5/Corollary40/Column.lean` |
| `mvPhase1Body` | Mv-hinted Mv runs in phases, with explicit numbers of steps. | `mv_lightPhases` |  | `tMvGather` | `ThreeSumApsp/Programs/Sec5/Corollary40/MvHinted.lean` |
| `mvPhase2Body` | Phase 2 writes X and preprocesses X and V: the data structure is ready, and no cell below X has changed. | `mvPhase2_meets` |  | `tMvGather` | `ThreeSumApsp/Programs/Sec5/Corollary40/MvHinted.lean` |
| `mvPhase3Body` | Phase 3 asks the n queries for column j: output cell r tells whether the entry (r, j) of the product of X and V over the integers is positive. | `mvPhase3_meets` |  |  | `ThreeSumApsp/Programs/Sec5/Corollary40/MvHinted.lean` |
| `uMvPhase3Body` | Phase 3 writes Y and builds the structures of the blocks and the table of their first rows. | `uMvPhase3_meets` |  |  | `ThreeSumApsp/Programs/Sec5/Corollary40/UMvHinted.lean` |
| `uMvPhase4Body` | Phase 4 writes the entry (i, j) of U N_{I,J} V, as 0 or 1, into the output cell. | `uMvPhase4_meets` |  | `tScan` | `ThreeSumApsp/Programs/Sec5/Corollary40/UMvHinted.lean` |
| `blocksBody` | blocks builds the structures of the blocks and the table of their first rows. | `blocks_meets` |  | `tBlocks` | `ThreeSumApsp/Programs/Sec5/Corollary40/UMvRoutines.lean` |
| `gatherBody` | gather writes the submatrix N_{I,J} and changes nothing else. | `gather_meets` |  | `tGather` | `ThreeSumApsp/Programs/Sec5/Corollary40/UMvRoutines.lean` |
| `scanBody` | scan returns 1 if some ℓ has V[ℓ, j] = 1 and (XY)[off, ℓ] ≠ 0, and 0 if not. | `scan_meets` |  | `tScan` | `ThreeSumApsp/Programs/Sec5/Corollary40/UMvRoutines.lean` |
| `vPhase1Body` | v-hinted Mv runs in phases, with explicit numbers of steps. | `v_lightPhases` |  |  | `ThreeSumApsp/Programs/Sec5/Corollary40/VHinted.lean` |
| `vPhase2Body` | Phase 2 preprocesses M and V where they lie: the data structure is ready, and only its cells have changed. | `vPhase2_meets` |  |  | `ThreeSumApsp/Programs/Sec5/Corollary40/VHinted.lean` |
| `vPhase3Body` | Phase 3 asks the n queries for column i: output cell r tells whether the entry (r, i) of the product of M and V over the integers is positive. | `vPhase3_meets` |  |  | `ThreeSumApsp/Programs/Sec5/Corollary40/VHinted.lean` |

The programs also run routines that are listed under other items: 29 under Theorem 5, 12 under Corollary 26, 18 under Theorem 30.

## The five claims of EndStatement.lean

Statements: `endStatement_theorem_19`, `endStatement_theorem_22_3SUM`, `endStatement_theorem_22_MinPlus`, `endStatement_theorem_22_APSP`, `endStatement_corollary_39_zeroWeight`, proved in `ThreeSumApsp/Statements/EndStatement.lean`.

The item statements for Theorems 19 and 22 and Corollary 39 speak of the problems of the end
statement and contain the five bounds, with real exponents.  `SolvedInTime.endStatement` turns such
a bound into the form of the end statement, with the same program: a step bound with natural values,
and a rational exponent.

Which bound each claim takes, and on which of the paper's two routes it rests:

* Theorem 19: the third bound of `Items.Theorem_19`.  It follows from the second bound, so it rests
  on Theorem 17 with Corollary 16, that is, on Corollary 26 (Section 4), and not on the time bound
  of Theorem 5.
* 3SUM, the (min,+)-product and APSP: the first and the last two bounds of
  `Items.Theorem_22_second`, "using Corollary 26".
* Zero-Weight k-Clique: `Items.Corollary_39_zero`, from Theorem 19 using Corollary 26.

| Lemma or definition | What it says | File |
|---|---|---|
| `ThreeSumApsp.WordRam.SolvedInTime.endStatement` | A bound `O(n^a)` of an item statement, with `a` the rational `r`, is the bound `O(n^r)` of the end statement, with the same program and the same slope. | `ThreeSumApsp/Statements/Exponents.lean` |
| `ThreeSumApsp.WordRam.Items.Theorem_19` | Theorem 19: "For every constant ν ≥ 1, Exact Triangle on n vertices per part with integer weights of absolute value at most n^ν can be solved by a deterministic algorithm in O(n^{3−1/648} log² n) time [...], and in O(n^{3−ε'} log n) ≤ O(n^{3−ε_T}) time", with `ε' = 0.00175` and `ε_T = 0.0017`. | `PaperStatements.lean` |
| `ThreeSumApsp.WordRam.Items.Theorem_22_second` | Theorem 22, the bounds "Using Corollary 26 instead": 3SUM in `O(n^{1.9992})` time, the (min,+)-product and APSP in "Õ(n^{3−ε'/3}) ≤ O(n^{2.99942})" time, with `ε' = 0.00175`. | `PaperStatements.lean` |
| `ThreeSumApsp.WordRam.Items.Corollary_39_zero` | Corollary 39, the case of Zero-Weight k-Clique. | `PaperStatements.lean` |
| `ThreeSumApsp.wordRam_theorem_19` | Theorem 19, on the word RAM. | `ThreeSumApsp/RunningTimes/Sec3/Theorem19.lean` |
| `ThreeSumApsp.wordRam_theorem_22_second` | Theorem 22, on the word RAM: the bounds using Corollary 26. | `ThreeSumApsp/RunningTimes/Sec3/Theorem22.lean` |
| `ThreeSumApsp.wordRam_corollary_39_zero` | Corollary 39, the zero-weight case, on the word RAM. | `ThreeSumApsp/RunningTimes/Sec5/Corollary39.lean` |


The programs also run routines that are listed under other items: 29 under Theorem 5, 45 under Theorem 22, 34 under Theorem 19, 1 under Corollaries 15 and 16, 12 under Corollary 26, 18 under Theorem 30, 1 under Corollary 39.
