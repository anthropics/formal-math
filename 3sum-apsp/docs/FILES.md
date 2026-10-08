# The files

This file is written by `scripts/index.py`; do not edit it.

`EndStatement.lean`, `PaperStatements.lean` and every Lean file of `Challenge/` and the library, with the title of its
header, folder by folder. The header of a file says what the file proves and how. (The files of `Solution/` only
import the library, and `scripts/PrintAxioms.lean` is generated; they are not listed.)


## the top level

| file | title |
|---|---|
| `EndStatement.lean` | (no title: the file only imports others, or explains itself) |
| `PaperStatements.lean` | Further statements of the paper |
| `ThreeSumApsp.lean` | The library |

## `Challenge/`

| file | title |
|---|---|
| `EndStatement.lean` | The five claims of EndStatement.lean |
| `PaperStatements.lean` | The statements of `PaperStatements.lean` |

## `ThreeSumApsp/`

| file | title |
|---|---|
| `ConditionalTimes.lean` | The three conditional lemmas |
| `ModelChecks.lean` | Checks of the model |
| `RunningTimes.lean` | The running times on the word RAM |
| `Sec1.lean` | Section 1 without a machine |
| `Sec2.lean` | Section 2 without a machine |
| `Sec3.lean` | Section 3: all files of the folder `Sec3` |
| `Sec4.lean` | Section 4 without a machine |
| `Sec5.lean` | Section 5 without a machine |
| `Statements.lean` | The theorems that are compared |

## `ThreeSumApsp/ConditionalTimes/`

| file | title |
|---|---|
| `Corollary38.lean` | Corollary 38 from Lemma 37 and Corollary 26 |
| `Definitions.lean` | Running times of Theorems 34 and 35 and Corollary 38, given what their proofs use: definitions |
| `SmallFacts.lean` | Small facts for the deductions of Sections 5.1 and 5.2 |
| `Theorem34.lean` | Theorem 34 from Theorems 22 and 33 |
| `Theorem35.lean` | Theorem 35 from Corollary 38, Lemma 36 and the restart argument |

## `ThreeSumApsp/Lang/`

| file | title |
|---|---|
| `Assigns.lean` | A statement changes only the local variables that it assigns |
| `Calls.lean` | Calls |
| `Frames.lean` | Local variables as a list |
| `Logic.lean` | Proof rules for the light language |
| `Phases.lean` | Programs that receive their input in phases |
| `PolyBounded.lean` | Polynomially bounded needs |
| `Regions.lean` | Regions of the memory, and the cells that a step leaves alone |
| `Renumber.lean` | Two programs in one: relocation of procedures |
| `RowMajor.lean` | Reading the trusted layout |
| `Rules.lean` | Derived rules: time that is not typed, blocks, counting loops |
| `RunsStayInLimits.lean` | Runs stay within their limits |
| `Syntax.lean` | The light language |
| `Tactics.lean` | Tactics for proofs about programs |
| `Tasks.lean` | Problems, solvers, and the interpretation of "is solved in time T" in the light language |
| `ToMachine.lean` | From runs of light programs to the running-time notions of the word RAM |
| `TopProcedure.lean` | From a solver of a task to a program for the layout of the end statement |
| `WordSize.lean` | A polynomial bound in the parameters fits in a word |

## `ThreeSumApsp/Lang/Compiler/`

| file | title |
|---|---|
| `CallFrames.lean` | Pieces of a call: the arguments and the new frame |
| `Cells.lean` | The cells of the compiled code, and the memories that represent a state |
| `Conditions.lean` | The compiler is correct on tests |
| `Dispatcher.lean` | The dispatcher |
| `Expressions.lean` | The compiler is correct on expressions |
| `ProgramCode.lean` | The code of a whole program |
| `Simulation.lean` | The compiler is correct on statements: the simulation theorem |
| `StartUp.lean` | The start-up code |
| `StatementCode.lean` | The compiler from the light language to the word RAM: cells, and the code of statements |
| `WholeProgram.lean` | The compiler is correct on whole programs |

## `ThreeSumApsp/Lang/Lib/`

| file | title |
|---|---|
| `ArrayAt.lean` | Arrays in the memory |
| `Copy.lean` | Copying and filling a segment |
| `CountSort.lean` | Counting sort of a list of items by a key that is read through the item |
| `Emod.lean` | The remainder of a division |
| `Logs.lean` | Logarithms, the cube root and halves, without division |
| `Merge.lean` | Merging two segments |
| `MergeSort.lean` | Merge sort |
| `NextPair.lean` | From a pair to the next pair |
| `Odometer.lean` | An odometer in the memory |
| `Pass.lean` | A pass over an array |
| `PowTable.lean` | Tables of powers |
| `RadixPass.lean` | One pass of a radix sort on a list of indices |
| `Seg.lean` | Segments of the memory |
| `Sieve.lean` | The sieve of Eratosthenes |
| `Sqrt.lean` | The integer square root by counting up |

## `ThreeSumApsp/Machine/`

| file | title |
|---|---|
| `Footprint.lean` | What a run of the word RAM reads and writes |
| `PolylogIsLittleO.lean` | A bound with polylogarithmic factors is a bound n^{a+o(1)} |
| `Realized.lean` | A running time that is realized on the word RAM |
| `Solving.lean` | The notions of solving are monotone |
| `Steps.lean` | Running the word RAM: words, steps, pieces of code, straight-line code, branches |

## `ThreeSumApsp/ModelChecks/`

| file | title |
|---|---|
| `Counting.lean` | Two counting facts for the lower bounds |
| `ThreeSumLowerBound.lean` | 3SUM needs linear time on the word RAM |
| `VHintedLowerBound.lean` | Phase 3 of v-hinted Mv needs linear time on the word RAM |

## `ThreeSumApsp/Programs/`

| file | title |
|---|---|
| `LightModel.lean` | "Is solved in time T", read as a statement about programs of the light language |
| `Tasks.lean` | The problems of the paper as tasks |

## `ThreeSumApsp/Programs/Sec2/Theorem5/`

| file | title |
|---|---|
| `CellDependencies.lean` | The memory map of Theorem 5: what depends on which cells |
| `Contracts.lean` | Theorem 5 in the light language: the map |
| `Instance.lean` | Theorem 5: an instance of the task, in the terms of Section 2 |
| `LibraryContracts.lean` | Three routines of the library, as their callers see them |
| `Places.lean` | Theorem 5 in the light language: sizes and places |
| `Program.lean` | Theorem 5: the program |
| `SharedStage.lean` | The shared stage: everything up to the encodings of all bands |
| `Solver.lean` | Theorem 5: the solver |
| `Stages.lean` | Theorem 5: the solver, stage by stage |
| `Time.lean` | Theorem 5 in the light language: the running time, added up |
| `WordSize.lean` | Theorem 5 in the light language: the limits |

## `ThreeSumApsp/Programs/Sec2/Theorem5/AllInstances/`

| file | title |
|---|---|
| `BruteForce.lean` | The wanted entries of a thin matrix product, as inner products |
| `Program.lean` | The running-time claim "Theorem 5" for the light model, for the program of Theorem 5 |
| `RegimeTest.lean` | The regime of Theorem 5 |
| `Solver.lean` | The thin matrix product, on all instances |

## `ThreeSumApsp/Programs/Sec2/Theorem5/Encode/`

| file | title |
|---|---|
| `AllBands.lean` | The encodings of all bands of one matrix (Section 2.4.1) |
| `BandArray.lean` | The input array of a band (Section 2.3.4) |
| `BandArrayFacts.lean` | The input array of a band: what the loops compute |
| `Contract.lean` | What the callers of encode assume |
| `Meaning.lean` | What encode computes, in the paper's terms |
| `Recursion.lean` | The encoding of an array by the recursion of Section 2.4.1 |
| `Step.lean` | One encoding step (step (2) of Full, Section 2.3.1) |

## `ThreeSumApsp/Programs/Sec2/Theorem5/Pruned/`

| file | title |
|---|---|
| `AllTiles.lean` | Theorem 5 as a program: the pruned recursion on every tile |
| `Contract.lean` | The pruned recursion with its helpers |
| `Memory.lean` | The pruned recursion: what one round does to the memory (Section 2.4.2, steps (2) to (4)) |
| `Recursion.lean` | The pruned recursion (Section 2.4.2), recursive as printed |
| `Restrict.lean` | Restricting an array on a set of codes to a subset (step (4) of Pruned, Section 2.4.2) |
| `SliceFacts.lean` | The pruned recursion: the pure side |
| `Slices.lean` | Cutting an increasing list of codes into its ten slices (step (2) of Pruned, Section 2.4.2) |
| `Union.lean` | The merge of two lists (Section 2.4.4: "a union of slices is a merge") |

## `ThreeSumApsp/Programs/Sec2/Theorem5/Tables/`

| file | title |
|---|---|
| `BandCounters.lean` | Band and block of every row, by counting (Section 2.3.4) |
| `Binomials.lean` | A binomial coefficient, by Pascal's triangle |
| `Coefficients.lean` | The tables of the coefficients of Schönhage's identity |
| `Digits.lean` | Tables of digits, by an odometer |
| `Subsets.lean` | The table of subsets |

## `ThreeSumApsp/Programs/Sec2/Theorem5/Wanted/`

| file | title |
|---|---|
| `Codes.lean` | The tile and the output string of each wanted position |
| `Gather.lean` | Theorem 5 in the light language: gathering the codes in sorted order |
| `Report.lean` | Theorem 5 as a program: the report |
| `Sort.lean` | Theorem 5 in the light language: sorting the wanted positions |
| `SortedFacts.lean` | After the sort: the codes of a tile are a segment (pure) |

## `ThreeSumApsp/Programs/Sec3/Corollary15_16/`

| file | title |
|---|---|
| `CountAndDetect.lean` | Corollary 15: counting triangles with the thin matrix product, and detecting with counting |
| `Split.lean` | Corollary 15: splitting the set of query pairs |

## `ThreeSumApsp/Programs/Sec3/Theorem17/`

| file | title |
|---|---|
| `Claim.lean` | Theorem 17 as a claim about programs of the light language |
| `ClaimAtParameters.lean` | Theorem 17 for programs of the light language, with the two choices of parameters of Section 3.3 |

## `ThreeSumApsp/Programs/Sec3/Theorem17/Hashing/`

| file | title |
|---|---|
| `ChoosePrime.lean` | The choice of the prime (proof of Theorem 17, "Hashing modulo a prime") |
| `Count.lean` | The count of the proof of Theorem 17, read off the product PQ |
| `CountPrime.lean` | The count for one prime (proof of Theorem 17, "Hashing modulo a prime") |
| `RingOps.lean` | Vectors: sums, differences, and the product in ℤ[x]/(x^p - 1) |
| `SizeTable.lean` | The table of the sizes of Strassen's recursion |
| `Strassen.lean` | Strassen's algorithm for matrices over ℤ[x]/(x^p - 1) in Z-order |
| `StrassenFacts.lean` | Strassen's algorithm in seven uniform phases: the pure side |
| `StrassenTime.lean` | The steps and the scratch space of Strassen's recursion |
| `ZOrder.lean` | Matrices over ℤ[x]/(x^p - 1) in Z-order: the table of places, and P and Q of Theorem 17's proof |
| `ZOrderFacts.lean` | The table of `spread`: small facts |

## `ThreeSumApsp/Programs/Sec3/Theorem17/Host/`

| file | title |
|---|---|
| `Arrays.lean` | The host of Theorem 17: the arrays and the loop |
| `Correct.lean` | The host of Theorem 17: et17 decides Exact Triangle |
| `FailedScans.lean` | The host of Theorem 17: failed scans and false positives |
| `InstanceCount.lean` | The number of instances of the host of Theorem 17 |
| `InstanceData.lean` | The host of Theorem 17: the list of its instances, as pure data |
| `InstanceFacts.lean` | The host of Theorem 17: what is true of the list of its instances |
| `Loop.lean` | The host of Theorem 17: the loop over the instances |
| `Need.lean` | The host of Theorem 17: the limits |
| `NeedPolynomial.lean` | The host of Theorem 17: the need stays polynomial |
| `ParametersStage.lean` | The host of Theorem 17: the parameters and the small case |
| `PrimeStage.lean` | The host of Theorem 17: the prime, the sizes, the addresses |
| `Program.lean` | The host of Theorem 17: the program, assembled |
| `Text.lean` | The host of Theorem 17: the top procedure |
| `Time.lean` | The host of Theorem 17: the time of a run is within the worst case |

## `ThreeSumApsp/Programs/Sec3/Theorem17/Instances/`

| file | title |
|---|---|
| `Chunks.lean` | The table of the chunks |
| `Classes.lean` | The classes W_ϱ of the pairs (proof of Theorem 17) |
| `WriteMatrices.lean` | The two matrices of an instance (proof of Theorem 17) |

## `ThreeSumApsp/Programs/Sec3/Theorem17/Parameters/`

| file | title |
|---|---|
| `Primes.lean` | The primes of the window (proof of Theorem 17) |
| `Residues.lean` | Residues without division |
| `Sizes.lean` | The parameters of Theorems 17 and 19, without division and without roots |

## `ThreeSumApsp/Programs/Sec3/Theorem17/TimeBound/`

| file | title |
|---|---|
| `Terms.lean` | Theorem 17: the time of each routine, up to a constant |
| `Total.lean` | The time of the host of Theorem 17 obeys the bound of Theorem 17 |

## `ThreeSumApsp/Programs/Sec3/Theorem17/Witnesses/`

| file | title |
|---|---|
| `BruteForce.lean` | Brute force (the proof of Theorem 19) |
| `Scan.lean` | Scanning a piece (the proof of Theorem 17) |
| `ScanPairs.lean` | Reading the answers of one instance and scanning for witnesses |

## `ThreeSumApsp/Programs/Sec3/Theorem19/`

| file | title |
|---|---|
| `BruteForceClaim.lean` | The running time of brute force (the proof of Theorem 19) |
| `ChooseBySize.lean` | Two algorithms for Exact Triangle and a threshold on the number of vertices |
| `Graphs.lean` | Exact Triangle on n-vertex graphs, from the tripartite form |

## `ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/`

| file | title |
|---|---|
| `Bits.lean` | 3SUM from Convolution-3SUM: binary digits of the labels, and selection by digits |
| `Buckets.lean` | 3SUM from Convolution-3SUM: remainders, counts, collisions, heavy elements |
| `Contracts.lean` | The reduction from 3SUM to Convolution-3SUM after Chan and He, as a program.  Specifications |
| `Distinct.lean` | 3SUM from Convolution-3SUM: distinct values, doubles of repeated values, a triple zero |
| `FrontFacts.lean` | 3SUM from Convolution-3SUM: what the lists that the first routines produce stand for |
| `Grid.lean` | The reduction from 3SUM to Convolution-3SUM: the loop over the splittings.  row and grid |
| `GridContracts.lean` | 3SUM from Convolution-3SUM: the loop over the splittings.  Specifications |
| `Host.lean` | The host of the reduction from 3SUM to Convolution-3SUM |
| `HostContracts.lean` | 3SUM from Convolution-3SUM: the memory map of core; specifications of params, prep, core |
| `LibraryContracts.lean` | 3SUM from Convolution-3SUM: the routines of the general library |
| `Modulus.lean` | The reduction from 3SUM to Convolution-3SUM: the modulus of a node |
| `NodeArray.lean` | The reduction from 3SUM to Convolution-3SUM: the array of a node |
| `NodeMemory.lean` | The reduction from 3SUM to Convolution-3SUM: the memory of a node, and what fits in a word |
| `Nodes.lean` | The recursion tree of the reduction from 3SUM to Convolution-3SUM |
| `Parameters.lean` | The parameters of the reduction from 3SUM to Convolution-3SUM |
| `Prepare.lean` | 3SUM from Convolution-3SUM: filling the arrays of the host |
| `Program.lean` | The program of the reduction from 3SUM to Convolution-3SUM, assembled |
| `Reduction.lean` | 3SUM from Convolution-3SUM: the core of the host |
| `Round.lean` | The reduction from 3SUM to Convolution-3SUM: one splitting |
| `Time.lean` | 3SUM from Convolution-3SUM: the time and the need of the host |
| `TimeBound.lean` | The arithmetic of the reduction from 3SUM to Convolution-3SUM |

## `ThreeSumApsp/Programs/Sec3/Theorem21a/Convolution/`

| file | title |
|---|---|
| `Fill.lean` | Convolution-3SUM from Exact Triangle: writing one instance |
| `Host.lean` | Convolution-3SUM from Exact Triangle: the host |
| `TimeBound.lean` | Convolution-3SUM from Exact Triangle: the claim |

## `ThreeSumApsp/Programs/Sec3/Theorem21b/Apsp/`

| file | title |
|---|---|
| `Host.lean` | APSP from the (min,+)-product |
| `Passes.lean` | APSP by repeated squaring: the three passes over the matrix |
| `TimeBound.lean` | APSP from the (min,+)-product: the claim |

## `ThreeSumApsp/Programs/Sec3/Theorem21b/MinPlus/`

| file | title |
|---|---|
| `AllPairs.lean` | All pairs with a witness, with an algorithm that finds a negative triangle |
| `BitSearch.lean` | The (min,+)-product from "all pairs", bit by bit |
| `CopyBlock.lean` | Copying a block of a matrix |
| `FindNegativeTriangle.lean` | Finding a negative triangle with an algorithm that decides whether there is one |
| `Passes.lean` | Two passes over an array, for the (min,+)-product found bit by bit |
| `Tasks.lean` | The two tasks between Negative Triangle and the (min,+)-product |
| `TimeBound.lean` | The (min,+)-product from Negative Triangle: the claim |

## `ThreeSumApsp/Programs/Sec3/Theorem21b/NegativeTriangle/`

| file | title |
|---|---|
| `Host.lean` | Negative Triangle from Exact Triangle, as a host |
| `Passes.lean` | Two loops over arrays for the reduction from Negative Triangle to Exact Triangle |
| `TimeBound.lean` | The claim [VW13, Theorem 3.3] in the light language |

## `ThreeSumApsp/Programs/Sec4/ChoosingParameters/`

| file | title |
|---|---|
| `Ceiling.lean` | Corollaries 26 and 31 in the light language: ⌈a m / b⌉ by counting |
| `Contracts.lean` | Corollaries 26 and 31 in the light language: procedure numbers, time functions and interfaces |
| `Costs.lean` | Section 4.4: the costs of the programs with rational parameters |
| `InnerProduct.lean` | An entry of the product as an inner product |
| `Layout.lean` | Section 4.4, the data structure: the two main procedures for the layout of the statements |
| `Limits.lean` | Section 4.4: the limits of the programs with rational parameters |
| `Offline.lean` | Section 4.4, the offline form: preprocess, then one query for each wanted position |
| `OfflineLayout.lean` | Section 4.4, the offline form: the main procedure for the layout of the statements |
| `OfflineStatement.lean` | Section 4.4, the offline form as a light program |
| `Pad.lean` | Padding X with zero columns |
| `Parameters.lean` | Corollaries 26 and 31 in the light language: rational parameters in the program text |
| `Preprocessing.lean` | Corollaries 26 and 31 in the light language: the preprocessing, with rational parameters |
| `Program.lean` | Corollaries 26, 31 and 32: the concrete program for given parameters |
| `RealParameters.lean` | Corollaries 31 and 32: the parameters of the program, and where its costs are bounded |
| `Setup.lean` | Corollaries 26 and 31 in the light language: m, the places of the padded matrices, the query |
| `Statement.lean` | Section 4.4, the data structure as a light program |

## `ThreeSumApsp/Programs/Sec4/Corollary26/`

| file | title |
|---|---|
| `AllInstances.lean` | Corollary 26, the offline form, on all instances |
| `Claim.lean` | Corollary 26, the offline form, for programs of the light language |
| `Program.lean` | Corollary 26: the program |
| `Regime.lean` | Corollary 26: the parameters 21, 1/9 and 60, and the regime N ≥ D^18 |

## `ThreeSumApsp/Programs/Sec4/Theorem30/`

| file | title |
|---|---|
| `AllTiles.lean` | The tries of all tiles |
| `Areas.lean` | The block of Theorem 30: the directory, sizes and limits |
| `Contracts.lean` | Theorem 30 in the light language: procedure numbers, time functions, specifications |
| `Directory.lean` | The cells of the directory, by name |
| `FillList.lean` | The boxes with e stars go into the trie of their tile (Lemma 29) |
| `Horner.lean` | Horner's rule: the code of a string of decimal digits |
| `Insert.lean` | Inserting a string into a trie (Lemma 29) |
| `Layout.lean` | Theorem 30 on the word RAM: the two main procedures for the trusted layout |
| `Lookup.lean` | Looking up a string in a trie (Section 4.3) |
| `Memory.lean` | Theorem 30 in the light language: the memory map and the invariant of the data structure |
| `NineFirst.lean` | The least string with a given number of nines |
| `NineNext.lean` | The next string of the enumeration |
| `Offline.lean` | Theorem 30, the offline form (9): preprocess, then one query for each wanted position |
| `OfflineLayout.lean` | Theorem 30, the offline form: the main procedure for the trusted layout |
| `OfflineStatement.lean` | Theorem 30, the offline form (9), on the word RAM |
| `OutDigits.lean` | The digits of the output string of a position |
| `Preprocessing.lean` | The preprocessing of Theorem 30, at a given place of the memory |
| `Program.lean` | Theorem 30 on the word RAM: the program |
| `Query.lean` | A query, from the block that holds the data structure (proof of Theorem 30, "Query") |
| `QuerySum.lean` | A query, once the digits of its output string are known |
| `RoutineFacts.lean` | What outDigits writes is the output string of the position |
| `Routines.lean` | The routines of Section 4, assembled |
| `Scatter.lean` | A string put at the levels of the inner set |
| `StarFirst.lean` | The lowest symbols P₀ of a leaf turned into stars |
| `SumTen.lean` | The value of a box with stars (proof of Lemma 29, "The values") |
| `ThinLayout.lean` | The input of a thin matrix product in the memory |
| `Tile.lean` | The trie of one tile |
| `Time.lean` | Theorem 30 in the light language: the tiles and a query against the expressions (8) and L ∑ α_d |
| `TimeOfBlock.lean` | Theorem 30 in the light language: the two routines against the expressions (8) and L ∑ α_d |
| `WordSize.lean` | Theorem 30 in the light language: limits that are polynomial in N |

## `ThreeSumApsp/Programs/Sec5/Corollary39/`

| file | title |
|---|---|
| `Tasks.lean` | Corollary 39: the tasks |

## `ThreeSumApsp/Programs/Sec5/Corollary39/GraphH/`

| file | title |
|---|---|
| `Build.lean` | Corollary 39 in the light language: what the hosts for k-Clique share |
| `Fill.lean` | Corollary 39 in the light language: filling a weight matrix of H |
| `FillMeaning.lean` | Corollary 39 in the light language: from the memory to the graph H |
| `PairCount.lean` | Corollary 39 in the light language: the number of pairs of parts |

## `ThreeSumApsp/Programs/Sec5/Corollary39/MinMaxWeight/`

| file | title |
|---|---|
| `Host.lean` | Corollary 39, minimum and maximum weight: the host |
| `MaxTriangle.lean` | Max-Weight Triangle from Exact Triangle, as a host |
| `MinTriangle.lean` | Min-Weight Triangle from Max-Weight Triangle, as a host |
| `SearchRoutines.lean` | Max-Weight Triangle from Exact Triangle: two routines |
| `TimeBound.lean` | Corollary 39, minimum and maximum weight: the two claims about triangles in the light language |

## `ThreeSumApsp/Programs/Sec5/Corollary39/ZeroWeight/`

| file | title |
|---|---|
| `Host.lean` | Corollary 39, weight zero, in the light language: the host |

## `ThreeSumApsp/Programs/Sec5/Corollary40/`

| file | title |
|---|---|
| `Column.lean` | Corollary 40: what the programs for v-hinted Mv and Mv-hinted Mv share |
| `DataStructure.lean` | A data structure for the entries of a thin matrix product, placed anywhere in the memory |
| `DataStructureBounds.lean` | Time, space and limits of the relocatable data structure |
| `Gather.lean` | Writing selected entries of a matrix |
| `MvHinted.lean` | Corollary 40: Mv-hinted Mv as a light program that runs in phases |
| `PhaseLayout.lean` | The three hinted problems: where the inputs of the phases lie |
| `UMvHinted.lean` | uMv-hinted uMv over a kit: the four phases |
| `UMvRoutines.lean` | uMv-hinted uMv: the routines of Phases 3 and 4 |
| `VHinted.lean` | Corollary 40: v-hinted Mv as a light program that runs in phases |

## `ThreeSumApsp/RunningTimes/`

| file | title |
|---|---|
| `FromClaims.lean` | From running-time claims to programs: Theorem 5, Corollaries 15 and 16, Theorem 19 |

## `ThreeSumApsp/RunningTimes/FromClaims/`

| file | title |
|---|---|
| `Bounds.lean` | From a realized running time to a program with the paper's bound |

## `ThreeSumApsp/RunningTimes/Sec1/`

| file | title |
|---|---|
| `Theorems1_4.lean` | Theorems 1 to 4 on the word RAM |

## `ThreeSumApsp/RunningTimes/Sec2/`

| file | title |
|---|---|
| `Theorem5.lean` | Theorem 5 on the word RAM |

## `ThreeSumApsp/RunningTimes/Sec3/`

| file | title |
|---|---|
| `Corollary15_16.lean` | Corollaries 15 and 16 on the word RAM |
| `Theorem19.lean` | Theorem 19 on the word RAM |
| `Theorem22.lean` | Theorem 22 on the word RAM |

## `ThreeSumApsp/RunningTimes/Sec3/Corollary15_16/`

| file | title |
|---|---|
| `Layout.lean` | The thin matrix product and the lopsided triangle problems in the layout of the word RAM |

## `ThreeSumApsp/RunningTimes/Sec3/Theorem19/`

| file | title |
|---|---|
| `GraphsLayout.lean` | Exact Triangle on n-vertex graphs on the word RAM |
| `Layout.lean` | Exact Triangle: from a solver of the task to a program for the layout of the end statement |

## `ThreeSumApsp/RunningTimes/Sec3/Theorem22/`

| file | title |
|---|---|
| `ApspLayout.lean` | APSP: from a solver of the task to a program for the layout of the end statement |
| `MinPlusLayout.lean` | The (min,+)-product: from a solver of the task to a program for the layout of the end statement |
| `ThreeSumLayout.lean` | 3SUM: from a solver of the task to a program for the layout of the end statement |
| `ThreeSumPolylog.lean` | 3SUM with polylogarithmic factors only |

## `ThreeSumApsp/RunningTimes/Sec4/`

| file | title |
|---|---|
| `Corollary26.lean` | Corollary 26 on the word RAM |
| `Corollary31_32.lean` | Corollaries 31 and 32 on the word RAM |
| `Theorem24_25.lean` | Theorems 24 and 25 on the word RAM |
| `Theorem30.lean` | Theorem 30 on the word RAM |

## `ThreeSumApsp/RunningTimes/Sec4/Corollary31_32/`

| file | title |
|---|---|
| `Arithmetic.lean` | Changing the bounds of the running-time statements of Section 4 |

## `ThreeSumApsp/RunningTimes/Sec5/`

| file | title |
|---|---|
| `Corollary39.lean` | Corollary 39 on the word RAM |
| `Corollary40.lean` | Corollary 40 on the word RAM |

## `ThreeSumApsp/RunningTimes/Sec5/Corollary39/`

| file | title |
|---|---|
| `MinMaxWeight.lean` | Corollary 39, minimum and maximum weight, on the word RAM |
| `ZeroWeight.lean` | Corollary 39, the zero-weight case, on the word RAM |
| `ZeroWeightLayout.lean` | Zero-Weight k-Clique: from a solver of the task to a program for the layout of the end statement |

## `ThreeSumApsp/RunningTimes/Sec5/Corollary40/`

| file | title |
|---|---|
| `ColumnTimes.lean` | Corollary 40: what the running times of v-hinted Mv and Mv-hinted Mv have in common |
| `MvHintedTimes.lean` | Corollary 40, Conjecture 5.7: the running times of Mv-hinted Mv |
| `ToMachine.lean` | The three hinted problems: from a program that runs in phases to the word RAM |
| `UMvHintedTimes.lean` | Corollary 40, Conjecture 5.12: the running times of uMv-hinted uMv |
| `VHintedTimes.lean` | Corollary 40, Conjecture 5.2: the running times of v-hinted Mv |

## `ThreeSumApsp/Sec1/`

| file | title |
|---|---|
| `MonoConvolution.lean` | The introduction: the exponent of MonoConvolution (Section 1.2) |

## `ThreeSumApsp/Sec2/`

| file | title |
|---|---|
| `Lemma10.lean` | Sections 2.4.1 and 2.4.2: the encodings, the recursion `Pruned`, and Lemma 10 |
| `Lemma11.lean` | Section 2.4.3, second half: Lemma 11 |
| `Lemma6.lean` | Lemma 6: Schönhage's identity |
| `Lemma7_8.lean` | Lemmas 7 and 8: what `Full` computes |
| `Lemma9.lean` | Lemma 9: one run of `Full` computes all the products `X_Q Y_Q` |
| `Levels.lean` | Strings cut along a set of levels |
| `Orders.lean` | Section 2.4.3, first half: the orders of the leaves and equation (5) |
| `Recursion.lean` | Strings, vertices and the coefficients of the encoding |
| `Theorem5.lean` | Section 2.4.4: the algorithm of Theorem 5, its correctness and its three totals |
| `Tiling.lean` | The tiling of the `N × D × N` product |

## `ThreeSumApsp/Sec2/Lemma6/`

| file | title |
|---|---|
| `Monomials.lean` | The monomials of Schönhage's identity |

## `ThreeSumApsp/Sec2/Theorem5/`

| file | title |
|---|---|
| `Equation6.lean` | Section 2.4.4: the two consequences of `N ≥ D^18` |
| `WordSize.lean` | Section 2.4.4: the remaining minutiae and the word size |

## `ThreeSumApsp/Sec2/Tiling/`

| file | title |
|---|---|
| `Definitions.lean` | Definitions for the tiling of the `N × D × N` product |

## `ThreeSumApsp/Sec3/`

| file | title |
|---|---|
| `Chunks.lean` | Cutting a set of pairs into chunks |
| `Corollary15_16.lean` | Corollaries 15 and 16: the number of pieces, and the bound for few query pairs |
| `MatrixLanguage.lean` | Section 3.1: the lopsided problem in matrix language, and footnote 8 |
| `Parameters.lean` | The parameters and model running times of Sections 3.1 to 3.4 |
| `Theorem17.lean` | Theorem 17: Exact Triangle reduces to Lop-AE-SparseTri |
| `Theorem19.lean` | Theorem 19 and Remark 20: Exact Triangle in truly subcubic time (Section 3.3) |
| `Theorem21.lean` | Theorem 21: 3SUM, the (min,+)-product and APSP reduce to Exact Triangle |
| `Theorem21a.lean` | Theorem 21(a): from 3SUM to Convolution-3SUM, and on to Exact Triangle |
| `TripartiteOfGraph.lean` | Section 3.2: from an arbitrary graph to a tripartite one |

## `ThreeSumApsp/Sec3/Theorem17/`

| file | title |
|---|---|
| `Hashing.lean` | Theorem 17, first step: hashing modulo a prime |
| `Instances.lean` | Theorem 17, second step: the instances |
| `Witnesses.lean` | Theorem 17, third step: witnesses |

## `ThreeSumApsp/Sec3/Theorem19/`

| file | title |
|---|---|
| `Choice.lean` | The cost analysis of Theorem 19 for a general choice of the parameters |

## `ThreeSumApsp/Sec3/Theorem21a/`

| file | title |
|---|---|
| `Convolution.lean` | Theorem 21(a): Convolution-3SUM reduces to Exact Triangle |

## `ThreeSumApsp/Sec3/Theorem21a/ChanHe/`

| file | title |
|---|---|
| `Collisions.lean` | Theorem 21(a), the reduction of Chan and He: the choice of the modulus |
| `Definitions.lean` | Theorem 21(a), the reduction of Chan and He: the problems on three sets and on arrays |
| `FromNumbers.lean` | Theorem 21(a), the reduction of Chan and He: from n numbers to one-array Convolution-3SUM |
| `Recursion.lean` | Theorem 21(a), the reduction of Chan and He: one node, and the recursion for three sets |
| `Sizes.lean` | Theorem 21(a), the reduction of Chan and He: inputs of absolute value at most n ^ κ |

## `ThreeSumApsp/Sec3/Theorem21b/`

| file | title |
|---|---|
| `NegativeTriangle.lean` | Theorem 21(b): Negative Triangle reduces to Exact Triangle |
| `PathsAndWalks.lean` | Paths of the end statement and walks with weights in `WithTop ℤ` |
| `RepeatedSquaring.lean` | Theorem 21(b): repeated squaring computes the distances |

## `ThreeSumApsp/Sec4/`

| file | title |
|---|---|
| `BoxExamples.lean` | The two worked examples of Section 4.2 |
| `Boxes.lean` | Cubes and boxes (Section 4.2) |
| `BoxesFromLeaves.lean` | The boxes of an output string, from its leaves of order exactly `t` (Section 4.2) |
| `ChoosingParameters.lean` | 4.4 Choosing the parameters: the entropy function, the exponents `γ` and `q`, equation (11) |
| `Corollary26.lean` | Corollary 26: the parameters `L = 21m`, `t = ⌈m/9⌉` |
| `Corollary31.lean` | Corollary 31: the costs of Theorem 30 as powers of `D` |
| `Corollary32.lean` | Corollary 32 and the proof of Theorem 25: the time for `\|W\| ≤ N²/D^κ` wanted entries |
| `Lemma27_28.lean` | Lemmas 27 and 28: the boxes of an output string (Section 4.2) |
| `Lemma29.lean` | Lemma 29: the number of boxes, and their values (Section 4.3) |
| `ParameterSteps.lean` | Section 4.4: the steps of the proof of Corollary 26 that hold for all parameters |
| `Table2.lean` | Table 2 |
| `Theorem30.lean` | Equation (7) and Theorem 30: the data structure (Section 4.3) |

## `ThreeSumApsp/Sec4/Corollary31/`

| file | title |
|---|---|
| `Limit.lean` | Corollary 31: the limit `ε*`; the choice of `c` and `θ` in the proof of Theorem 24 |
| `RationalParameters.lean` | Rational parameters for Corollary 31 |

## `ThreeSumApsp/Sec4/Table2/`

| file | title |
|---|---|
| `Captions.lean` | The captions of Tables 1 and 2 |
| `LogBounds.lean` | The numerical toolkit for Table 2 |

## `ThreeSumApsp/Sec5/`

| file | title |
|---|---|
| `Corollary38.lean` | Corollary 38 |
| `Corollary39.lean` | Corollary 39: from weighted k-Clique to triangles |
| `Corollary40.lean` | Corollary 40: the hinted Mv conjectures |
| `Lemma36a.lean` | Lemma 36(a) |
| `Lemma36b.lean` | Lemma 36(b) |
| `Lemma37.lean` | Lemma 37, after Matoušek |
| `Theorem34.lean` | Theorem 34: directed unweighted APSP |
| `Theorem35.lean` | Proof of Theorem 35: the arithmetic |

## `ThreeSumApsp/Sec5/Corollary39/`

| file | title |
|---|---|
| `Definitions.lean` | Corollary 39: the graph `H` of the reduction from k-Clique to triangles |

## `ThreeSumApsp/Sec5/Corollary40/`

| file | title |
|---|---|
| `GeneralParameters.lean` | Corollary 40, "General τ": the choice of the parameters |
| `HintSizeArithmetic.lean` | The arithmetic of t = ⌊n^τ⌋ |
| `RoundingThreshold.lean` | Corollary 40, "General τ", Conjecture 5.12: rounding does no harm for large t₁ |

## `ThreeSumApsp/Spec/Sec2/Theorem5/`

| file | title |
|---|---|
| `Alphabets.lean` | The alphabets of Schönhage's identity as digits |
| `Arrays.lean` | Arrays on strings as lists |
| `Counters.lean` | Quotients and remainders by counters |
| `Layout.lean` | One computable layout of the tiling |
| `PrunedList.lean` | The pruned recursion on lists |
| `SortedSets.lean` | Sets of output strings as increasing lists of codes |
| `SubsetTable.lean` | The table of subsets: how a row is made from the row before it |
| `Subsets.lean` | The subsets of size `m` of `{1, …, L}`, enumerated |

## `ThreeSumApsp/Spec/Sec3/`

| file | title |
|---|---|
| `Problems.lean` | The problems for Section 3.4, read from lists of integers |

## `ThreeSumApsp/Spec/Sec3/Theorem17/`

| file | title |
|---|---|
| `Choice.lean` | The prime that is chosen (proof of Theorem 17) |
| `Chunks.lean` | The table of the chunks (proof of Theorem 17) |
| `ClassStarts.lean` | Pure facts about the starts of the classes and the table of chunks |
| `Classes.lean` | The number of chunks, on lists and on sets of pairs (proof of Theorem 17) |
| `Cyclic.lean` | The ring `ℤ[x]/(x^p − 1)` as vectors of `p` integers |
| `Hashing.lean` | Hashing modulo a prime (proof of Theorem 17), on numbers and lists |
| `Instances.lean` | The instances and the scans (proofs of Theorems 17 and 19), as functions on lists |
| `Parameters.lean` | The parameters of Theorems 17 and 19 in integer arithmetic |
| `Strassen.lean` | Strassen's algorithm on lists, and the count of the proof of Theorem 17 |
| `ZOrder.lean` | Matrices in Z-order (Morton order) |

## `ThreeSumApsp/Spec/Sec3/Theorem21a/`

| file | title |
|---|---|
| `Convolution.lean` | Convolution-3SUM reduces to Exact Triangle, on lists |
| `NodeArray.lean` | The array of a node of the reduction after Chan and He, from lists |
| `Passes.lean` | One pass over a list |

## `ThreeSumApsp/Spec/Sec3/Theorem21b/`

| file | title |
|---|---|
| `AllPairs.lean` | All pairs with a witness, by marking |
| `BitSearch.lean` | The entries of a (min,+)-product, found bit by bit |
| `FindNegativeTriangle.lean` | Finding a negative triangle by halving |
| `NegativeTriangle.lean` | Negative Triangle from Exact Triangle, on lists of integers |
| `RepeatedSquaring.lean` | Repeated squaring on lists of integers |

## `ThreeSumApsp/Spec/Sec4/Theorem30/`

| file | title |
|---|---|
| `Cubes.lean` | Cubes, leaves and output strings as lists of digits (Sections 4.2 and 4.3) |
| `NineScan.lean` | The successor of a string, as two passes from left to right |
| `NineStrings.lean` | Strings of digits with a bounded number of nines (Section 4.2, proofs of Lemma 29, Theorem 30) |
| `PartialSums.lean` | Bounds on the partial sums (proof of Theorem 30, "Word size") |
| `QueryLists.lean` | What a query reads (proof of Theorem 30, "Query") |
| `StarBoxes.lean` | The boxes with e stars, as a list (proof of Lemma 29) |
| `TileTries.lean` | The trie of a tile, and the tries of all tiles (Lemma 29) |
| `Trie.lean` | Tries in one array (Section 4.3) |

## `ThreeSumApsp/Spec/Sec5/Corollary39/`

| file | title |
|---|---|
| `AuxiliaryGraph.lean` | The weights of the graph H as sums over lists of pairs of parts (proof of Corollary 39) |
| `MaxTriangleSearch.lean` | Max-Weight Triangle from Exact Triangle (proof of Corollary 39) |

## `ThreeSumApsp/Spec/Sec5/Corollary40/`

| file | title |
|---|---|
| `Outputs.lean` | The output of uMv-hinted uMv, in terms of integer matrix products |

## `ThreeSumApsp/Statements/`

| file | title |
|---|---|
| `Agreement.lean` | The notions that are defined twice agree |
| `EndStatement.lean` | The five claims of the end statement |
| `Exponents.lean` | From a real exponent to a rational one |
| `PaperStatements.lean` | The propositions of `PaperStatements.lean` hold |

## `ThreeSumApsp/TimeClaims/Sec3/`

| file | title |
|---|---|
| `Arithmetic.lean` | The arithmetic behind the running-time claims of Section 3 |
| `Corollary15_16.lean` | Running-time claims of Section 3.1: Corollaries 15 and 16 |
| `Definitions.lean` | Running-time claims of Sections 2 to 4, for an abstract notion of "solved in time T" |
| `Theorem19.lean` | Theorem 19 from Theorem 17 and Corollaries 15 and 16 |
| `Theorem21_22.lean` | Running-time claims of Section 3.4: Theorems 21 and 22 |

## `ThreeSumApsp/TimeClaims/Sec5/`

| file | title |
|---|---|
| `Corollary39.lean` | Corollary 39 from Theorem 19 |
| `Definitions.lean` | Running-time claims for Corollary 39: the definitions |

## `ThreeSumApsp/Util/`

| file | title |
|---|---|
| `Average.lean` | Few indices are far above the average |
| `Basic.lean` | What most files use of Mathlib |
| `BinaryPrefixes.lean` | The prefixes of a binary representation, one bit at a time |
| `Ceil.lean` | Ceilings of quotients and logarithms, floors and ceilings of roots |
| `Choose.lean` | Binomial coefficients |
| `Counting.lean` | Cardinalities of finite sets |
| `CountingSort.lean` | The pure side of counting sort |
| `Digits.lean` | Strings of digits as numbers |
| `Flag.lean` | The answer of a decision problem as a number |
| `Index.lean` | Index arithmetic: a pair of numbers as one number |
| `List.lean` | Lists: entries with a default, blocks, sums, counting, sorted lists |
| `Log.lean` | Logarithms and real powers |
| `Odometer.lean` | Counting in base `b` without division: an odometer |
| `PrimeCounting.lean` | Counting the primes up to m, in natural numbers |
| `PrimesInWindow.lean` | Counting the primes in a window of ratio two |
| `StablePass.lean` | One stable pass of a radix sort, on lists |
| `Sum.lean` | Bounds on finite sums and products |
| `Weave.lean` | Interleaving two strings of digits along a mask |

## `ThreeSumApsp/Util/Asymptotics/`

| file | title |
|---|---|
| `Dominated.lean` | Bounds up to a constant factor, in several parameters |
| `LogExponent.lean` | Powers of the logarithm as powers of n with an exponent that tends to 0 |
| `LogU.lean` | `logU`, the paper's `log U` |
| `Logarithms.lean` | Logarithms up to a constant factor |
| `PowLittleO.lean` | Calculating with `n^{a+o(1)}` |
| `PowPolylog.lean` | Calculating with `O(n^a)` and `Õ(n^a)` |
| `Powers.lean` | Powers of `n` and of `log n` for large `n` |
| `Scale.lean` | Orders of growth of counts |
| `SoftOSqrtPow.lean` | Bounds of the form "a polylogarithm times a power of √n" |
| `UpperBounds.lean` | One-sided bounds `O(n^a)`, `Õ(n^a)` and `n^{a+o(1)}` |
