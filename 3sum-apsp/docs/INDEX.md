# Index: the items of the paper and the Lean statements

This file is written by `scripts/index.py` from `docs/paper-items.json`; do not edit it.

For each numbered item, table and figure of the paper, in the order of the pages, a table names the statements and their
files, and the list below the table says what the statements render and what is not stated.

* A **statement** is a proposition that `EndStatement.lean` or `PaperStatements.lean` defines, such as `Lemma_6`. These two
  files are what a reader has to read and trust: for the five claims `EndStatement.lean` alone, for a further statement
  `PaperStatements.lean` as well. The tables name the theorem which says that the statement holds, such as `lemma_6`; the
  tool Comparator can check that the theorem of this name in the library (the folder `ThreeSumApsp/`), which has a proof,
  says exactly that (see `README.md`).
* A **lemma** is a theorem of the library that is not one of these. It is proved, and a reader need not read it.
* **About programs** marks a statement whose theorem has the prefix `wordRam_` or `endStatement_`: it says that there is
  a program of the word RAM of `EndStatement.lean` that solves a problem within a time bound.

There are 137 statements, in 2 files.

## Section 1 (introduction)

| Item | Page | Statements | Proved in |
|---|---|---|---|
| **Theorem 1**<br>Wanted entries of a thin matrix product (restates Corollary 26 and Theorem 25) | 5 | `wordRam_theorem_1` | [`ThreeSumApsp/RunningTimes/Sec1/Theorems1_4.lean`](../ThreeSumApsp/RunningTimes/Sec1/Theorems1_4.lean) |
| **Theorem 2**<br>Exact Triangle, APSP, (min,+)-product and 3SUM, integer and real inputs (restates Theorems 19, 22, 35) | 7 | `wordRam_theorem_2`, `wordRam_theorem_2_graphs`, `endStatement_theorem_19`, `endStatement_theorem_22_3SUM`, `endStatement_theorem_22_MinPlus`, `endStatement_theorem_22_APSP` | [`ThreeSumApsp/RunningTimes/Sec1/Theorems1_4.lean`](../ThreeSumApsp/RunningTimes/Sec1/Theorems1_4.lean)<br>[`ThreeSumApsp/Statements/EndStatement.lean`](../ThreeSumApsp/Statements/EndStatement.lean) |
| **Theorem 3**<br>The data structure (restates Theorem 24 and Corollary 26) | 7 | `wordRam_theorem_3` | [`ThreeSumApsp/RunningTimes/Sec1/Theorems1_4.lean`](../ThreeSumApsp/RunningTimes/Sec1/Theorems1_4.lean) |
| **Theorem 4**<br>The hinted Mv conjectures for thin hints (restates Corollary 40) | 8 | `wordRam_theorem_4` | [`ThreeSumApsp/RunningTimes/Sec1/Theorems1_4.lean`](../ThreeSumApsp/RunningTimes/Sec1/Theorems1_4.lean) |
| **Figure 1**<br>Problems affected by the algorithm (diagram) | 9 | none |  |

* **Theorem 1.** *Stated:* The whole item, about programs (D ≥ 1 is assumed, and N ≥ 1 in the last sentence: NOTE at `Items.Theorem_1`). *Not stated:* Nothing.
* **Theorem 2.** *Stated:* The four deterministic lines about programs (tripartite form, and n-vertex graphs for the first line); again as four of the five headline claims. *Not stated:* The lines on real inputs are not proved for any machine: Las Vegas algorithms on a real RAM, from results cited from [CVX22]. They occur only as the conclusion of the conditional deduction of Theorem 35, a lemma of the library (`conditional_theorem_35`).
* **Theorem 3.** *Stated:* The whole item, about programs (D ≥ 1 is assumed, and N ≥ 1 in the last sentence; the space of the preprocessing is bounded like its time, where the paper bounds only the time: NOTE at `Items.Theorem_3`). *Not stated:* "Space" is read as the extent of the memory in which the preprocessing leaves the data structure: cells farther from the input than the bound are unchanged at its end. Cells that are restored, and cells that queries write, are not constrained (see the docstring of `IsDataStructure`).
* **Theorem 4.** *Stated:* The whole item, about programs (for the uMv version τ₂ < 1 is assumed, the standing assumption of Section 5.4: NOTE at `Items.Corollary_40_times`). *Not stated:* The rectangular exponents of matrix multiplication are arbitrary real numbers subject to the lower bounds that Corollary 40 states; that the true exponents satisfy these bounds is not stated.
* **Figure 1.** *Stated:* Nothing. *Not stated:* A diagram of known reductions and equivalences. The running times in its boxes are those of Section 1; see the rows of Theorem 2 and of the items that it restates. Those that follow through cited reductions only, such as the one on the (min,+)-Convolution class, are not stated.

## Section 2

| Item | Page | Statements | Proved in |
|---|---|---|---|
| **Theorem 5**<br>Wanted entries for N ≥ D^18 and at most N²/√D positions | 13 | `wordRam_theorem_5` | [`ThreeSumApsp/RunningTimes/Sec2/Theorem5.lean`](../ThreeSumApsp/RunningTimes/Sec2/Theorem5.lean) |
| **Equation (1)**<br>Strassen's seven products | 14 | `eq_1` | [`ThreeSumApsp/Sec2/Lemma6.lean`](../ThreeSumApsp/Sec2/Lemma6.lean) |
| **Figure 2**<br>Strassen's recursion | 15 | none |  |
| **Lemma 6**<br>Schönhage's ten-term identity | 16 | `lemma_6` | [`ThreeSumApsp/Sec2/Lemma6.lean`](../ThreeSumApsp/Sec2/Lemma6.lean) |
| **Figure 3**<br>One level of the recursion | 19 | `figure_3` | [`ThreeSumApsp/Sec2/Recursion.lean`](../ThreeSumApsp/Sec2/Recursion.lean) |
| **Equation (2)**<br>Definition of Mult | 19 | `lemma_7`, `lemma_8`, `lemma_9` | [`ThreeSumApsp/Sec2/Lemma7_8.lean`](../ThreeSumApsp/Sec2/Lemma7_8.lean)<br>[`ThreeSumApsp/Sec2/Lemma9.lean`](../ThreeSumApsp/Sec2/Lemma9.lean) |
| **Lemma 7**<br>What Full multiplies at a leaf, and what it returns | 19 | `lemma_7` | [`ThreeSumApsp/Sec2/Lemma7_8.lean`](../ThreeSumApsp/Sec2/Lemma7_8.lean) |
| **Equation (3)**<br>Definition of γ(s, t, z) | 20 | `lemma_8` | [`ThreeSumApsp/Sec2/Lemma7_8.lean`](../ThreeSumApsp/Sec2/Lemma7_8.lean) |
| **Lemma 8**<br>Mult as a sum over pairs of strings | 20 | `lemma_8` | [`ThreeSumApsp/Sec2/Lemma7_8.lean`](../ThreeSumApsp/Sec2/Lemma7_8.lean) |
| **Lemma 9**<br>Mult computes the batch of matrix products; contains equation (4) | 21 | `lemma_9` | [`ThreeSumApsp/Sec2/Lemma9.lean`](../ThreeSumApsp/Sec2/Lemma9.lean) |
| **Equation (4)**<br>The display of Lemma 9 | 21 | `lemma_9` | [`ThreeSumApsp/Sec2/Lemma9.lean`](../ThreeSumApsp/Sec2/Lemma9.lean) |
| **Figure 4**<br>Inner and outer parts of strings | 22 | `figure_4` | [`ThreeSumApsp/Sec2/Lemma9.lean`](../ThreeSumApsp/Sec2/Lemma9.lean) |
| **Figure 5**<br>The tiling | 23 | none |  |
| **Lemma 10**<br>Pruned: values, leaves visited, total size of the sets | 25 | `lemma_10` | [`ThreeSumApsp/Sec2/Lemma10.lean`](../ThreeSumApsp/Sec2/Lemma10.lean) |
| **Equation (5)**<br>β_d / β_{d-1} < 1/2 at L = 19m | 26 | `eq_5_ratio`, `eq_5_bound`, `eq_5` | [`ThreeSumApsp/Sec2/Orders.lean`](../ThreeSumApsp/Sec2/Orders.lean) |
| **Figure 6**<br>The leaves that contribute to an output string | 27 | `figure_6`, `sec2_card_contributing_of_order`, `sec2_card_outStr_of_leaf` | [`ThreeSumApsp/Sec2/Orders.lean`](../ThreeSumApsp/Sec2/Orders.lean) |
| **Lemma 11**<br>Few leaves contribute to a sparse set of entries | 27 | `lemma_11` | [`ThreeSumApsp/Sec2/Lemma11.lean`](../ThreeSumApsp/Sec2/Lemma11.lean) |
| **Figure 7**<br>The count of Lemma 11 | 28 | `lemma_11` | [`ThreeSumApsp/Sec2/Lemma11.lean`](../ThreeSumApsp/Sec2/Lemma11.lean) |
| **Equation (6)**<br>10^L ≤ 2^{-m/9} N N₀ | 29 | `eq_6` | [`ThreeSumApsp/Sec2/Theorem5/Equation6.lean`](../ThreeSumApsp/Sec2/Theorem5/Equation6.lean) |
| **Remark 12**<br>Related techniques | 29 | none |  |

* **Theorem 5.** *Stated:* The whole item, about programs. *Not stated:* The correctness and the counts of the proof in the terms of Section 2 are lemmas (`Theorem5.correctness`, `encodings_total_le`, `Theorem5.total_leaves`, `Theorem5.total_sets`, `minutiae_total_le`, the statements on word size). As a statement that a program exists, the item follows from `wordRam_corollary_26_wanted`; that the algorithm of Section 2 achieves the bound is shown by the proofs of the library only.
* **Equation (1).** *Stated:* The identity. *Not stated:* Nothing.
* **Figure 2.** *Stated:* Nothing. *Not stated:* Strassen's recursion, recalled "for intuition": for Section 2.1 only identity (1) is stated. The recursion occurs as a program for Theorem 17.
* **Lemma 6.** *Stated:* The whole item. *Not stated:* The two observations after it are lemmas.
* **Figure 3.** *Stated:* The two worked examples of the caption. *Not stated:* The rest of the caption describes steps (2) to (4) of Full, which are the trusted definition `Full.run`. "each of the ten terms λ combines at most three of the seven slices" is a lemma (`card_support_phi_le`).
* **Equation (2).** *Stated:* A definition: the trusted `Mult`, which these three statements mention.
* **Lemma 7.** *Stated:* The whole item. *Not stated:* Nothing.
* **Equation (3).** *Stated:* A definition: the trusted `gamma`, which `lemma_8` mentions. *Not stated:* "it is also the coefficient of stz in G + E" is a lemma (`gamma_eq_coeff`).
* **Lemma 8.** *Stated:* The whole item. *Not stated:* Nothing.
* **Lemma 9.** *Stated:* The whole item, with equation (4). *Not stated:* Nothing.
* **Equation (4).** *Stated:* It is the display of Lemma 9. *Not stated:* Nothing.
* **Figure 4.** *Stated:* The worked example (L = 6, m = 2): inner sets, inner and outer parts, row and column. *Not stated:* The sentences of Section 2.3.3 that the figure illustrates ("the left strings with inner set Q index the entries of such a matrix", …) are lemmas (`existsUnique_leftStr`, `existsUnique_rightStr`, `existsUnique_outStr`). The sizes 81 × 16, 16 × 81 and 81 × 81 of the drawing and the number binom(6, 2) = 15 of products are not evaluated; the general counts are lemmas (`card_outerStr`, `card_innerStr`, `card_subsets_eq_K`).
* **Figure 5.** *Stated:* Nothing of its own. *Not stated:* The caption repeats sentences of Section 2.3.4, which are lemmas (`K0_sq_le_K`, `Full_bandArray_eq_block_mul`).
* **Lemma 10.** *Stated:* The whole item (the second claim with the hypothesis 0 < L ∨ U ≠ ∅: NOTE). *Not stated:* The sentence of Section 2.4.2 on the sets that are passed to the calls ("S will consist of the suffixes …") is a lemma (`Pruned.mem_passed_iff`).
* **Equation (5).** *Stated:* In three pieces: the ratio, the two inequalities at L = 19m, the conclusion. *Not stated:* What β_d counts ("The total number of leaves of order d in the entire recursion tree is β_d", Section 2.4.3) is a lemma (`card_filter_order_eq`). That there are M output strings of the required kind is not stated.
* **Figure 6.** *Stated:* The private leaf and the numbers of the drawing, evaluated (all but one), and the two general counts of the caption that say what the numbers count. *Not stated:* The "1 output string" of the private leaf, binom(4, 0) = 1, is not among the evaluated numbers; it is a case of `sec2_card_outStr_of_leaf`.
* **Lemma 11.** *Stated:* The whole item. *Not stated:* Nothing.
* **Figure 7.** *Stated:* Nothing of its own; it draws the count of Lemma 11 "schematically". *Not stated:* The bound per order, min{|U| α_d, β_d}, is a lemma (`card_Leaves_filter_order_le`). Two remarks of the caption are not stated: "the bound |U|α_d grows with d up to d ≈ 0.9m", and that the proof splits at a point "which is not necessarily where the two bounds cross".
* **Equation (6).** *Stated:* The inequality. *Not stated:* Nothing.
* **Remark 12.** *Stated:* Nothing. *Not stated:* The remark makes no mathematical claim.

## Section 3

| Item | Page | Statements | Proved in |
|---|---|---|---|
| **Figure 8**<br>The reductions of Section 3 (diagram) | 31 | none |  |
| **Definition 13**<br>Lop-AE-SparseTri(n, D) | 31 | `wordRam_corollary_15`, `wordRam_corollary_16`, `theorem_17` | [`ThreeSumApsp/RunningTimes/Sec3/Corollary15_16.lean`](../ThreeSumApsp/RunningTimes/Sec3/Corollary15_16.lean)<br>[`ThreeSumApsp/Sec3/Theorem17.lean`](../ThreeSumApsp/Sec3/Theorem17.lean) |
| **Definition 14**<br>#Lop-AE-SparseTri(n, D) | 32 | `wordRam_corollary_15`, `wordRam_corollary_16` | [`ThreeSumApsp/RunningTimes/Sec3/Corollary15_16.lean`](../ThreeSumApsp/RunningTimes/Sec3/Corollary15_16.lean) |
| **Corollary 15**<br>The lopsided problem by Theorem 5 | 32 | `wordRam_corollary_15` | [`ThreeSumApsp/RunningTimes/Sec3/Corollary15_16.lean`](../ThreeSumApsp/RunningTimes/Sec3/Corollary15_16.lean) |
| **Corollary 16**<br>The lopsided problem by Corollary 26 | 32 | `wordRam_corollary_16` | [`ThreeSumApsp/RunningTimes/Sec3/Corollary15_16.lean`](../ThreeSumApsp/RunningTimes/Sec3/Corollary15_16.lean) |
| **Theorem 17**<br>Exact Triangle reduces to lopsided instances | 33 | `theorem_17`, `theorem_17_scanOrder_exists`, `theorem_17_hashing_sum_sq_le`, `theorem_17_write_cost` | [`ThreeSumApsp/Sec3/Theorem17.lean`](../ThreeSumApsp/Sec3/Theorem17.lean) |
| **Remark 18**<br>Comparison with earlier reductions | 34-35 | `remark_18_block` | [`ThreeSumApsp/Sec3/Theorem17.lean`](../ThreeSumApsp/Sec3/Theorem17.lean) |
| **Theorem 19**<br>Exact Triangle in truly subcubic time | 35 | `wordRam_theorem_19`, `endStatement_theorem_19` | [`ThreeSumApsp/RunningTimes/Sec3/Theorem19.lean`](../ThreeSumApsp/RunningTimes/Sec3/Theorem19.lean)<br>[`ThreeSumApsp/Statements/EndStatement.lean`](../ThreeSumApsp/Statements/EndStatement.lean) |
| **Remark 20**<br>Balancing the parameter g | 35 | `remark_20_balance`, `remark_20_brute_force` | [`ThreeSumApsp/Sec3/Theorem19.lean`](../ThreeSumApsp/Sec3/Theorem19.lean) |
| **Theorem 21**<br>Known reductions to Exact Triangle (cited) | 35-36 | `theorem_21a_threeSum_to_convolution`, `theorem_21a_convolution_to_exact`, `theorem_21a_threeSum_to_exact`, `theorem_21a_compose`, `theorem_21b_repeated_squaring`, `theorem_21b_entries_bounded`, `theorem_21b_negative_to_exact`, `theorem_21b_log_factors` | [`ThreeSumApsp/Sec3/Theorem21a.lean`](../ThreeSumApsp/Sec3/Theorem21a.lean)<br>[`ThreeSumApsp/Sec3/Theorem21a/Convolution.lean`](../ThreeSumApsp/Sec3/Theorem21a/Convolution.lean)<br>[`ThreeSumApsp/Sec3/Theorem21.lean`](../ThreeSumApsp/Sec3/Theorem21.lean)<br>[`ThreeSumApsp/Sec3/Theorem21b/RepeatedSquaring.lean`](../ThreeSumApsp/Sec3/Theorem21b/RepeatedSquaring.lean)<br>[`ThreeSumApsp/Sec3/Theorem21b/NegativeTriangle.lean`](../ThreeSumApsp/Sec3/Theorem21b/NegativeTriangle.lean) |
| **Theorem 22**<br>3SUM and APSP | 36 | `wordRam_theorem_22_first`, `wordRam_theorem_22_second`, `wordRam_theorem_22_threeSum`, `endStatement_theorem_22_3SUM`, `endStatement_theorem_22_MinPlus`, `endStatement_theorem_22_APSP` | [`ThreeSumApsp/RunningTimes/Sec3/Theorem22.lean`](../ThreeSumApsp/RunningTimes/Sec3/Theorem22.lean)<br>[`ThreeSumApsp/Statements/EndStatement.lean`](../ThreeSumApsp/Statements/EndStatement.lean) |
| **Remark 23**<br>3XOR | 36 | none |  |

* **Figure 8.** *Stated:* Nothing. *Not stated:* A diagram of the reductions of Section 3; each box names numbered items and gives two running times, which are stated with those items.
* **Definition 13.** *Stated:* A definition: the trusted problem `lopDetect` (about programs) and `LopInstance.IsDetectionAnswer` (in `theorem_17`).
* **Definition 14.** *Stated:* A definition: the trusted problem `lopCount`, built on `LopInstance.numTriangles`.
* **Corollary 15.** *Stated:* The whole item, about programs. *Not stated:* The number of the pieces in its proof and their cost are lemmas of the library: `Corollary15.split`, `Corollary15.pieces_cost`. As a statement that a program exists, the item follows from `wordRam_corollary_16`; that the route through Theorem 5 achieves the bound is shown by the proofs of the library only.
* **Corollary 16.** *Stated:* The whole item, about programs (D ≥ 1: NOTE). *Not stated:* Nothing.
* **Theorem 17.** *Stated:* Everything but the time: the selected prime exists, at most 4ng instances, at most n²/√D query pairs, middle part at most D, non-adaptivity, correctness for every oracle and every order of the scans (and such an order exists); the three terms of the additional time as counts: triples looked at, ∑ p² ≤ D^{3/2}, entries written. *Not stated:* No statement is about the running time of the reduction. A program of the machine cannot simply be called as a subroutine: the definition of solving does not say which cells a program reads or writes, and a program may rely on zeros outside its input. The factor n^{ω+o(1)} is not stated (ω is not defined; Strassen's exponent is used). For programs that call an arbitrary solver the time bound is proved in the library, and is used for Theorem 19.
* **Remark 18.** *Stated:* The half of one sentence that is about the paper's own instance. *Not stated:* The comparison with [CX24] and [VX20], which would need the constructions of those papers.
* **Theorem 19.** *Stated:* The whole item, about programs; the last bound again as a headline claim. *Not stated:* The cost analysis of the proof is lemmas. "Using Theorem 5" cannot be said by "there is a program": as a statement of existence the first bound follows from the second. That the route through Theorem 5 achieves it is shown by the proofs of the library only.
* **Remark 20.** *Stated:* The balance at η = γ/2, the arithmetic of the brute-force bound. *Not stated:* The four numbers are a lemma (`remark_20_numbers`). "every vertex of A has O(√D/g) neighbors in the middle part" is a lemma (`TriangleInstance.ncard_nbr_lopInstance_le`). The sentences on possible improvements are prose.
* **Theorem 21.** *Stated:* Correctness, numbers and sizes of the instances of the reductions of [CH20], [VW13, Theorems 4.3 and 3.3] and of repeated squaring; an auxiliary count in place of the running time of the reduction of [CH20]; the arithmetic behind the printed forms n^{1/2+o(1)}, n^{3/2+o(1)}, log² U, log³ n, for arbitrary functions (it is not applied to the reductions). *Not stated:* Theorem 21(b), "If a deterministic algorithm solves Exact Triangle […] in time T(s) […], then […]", and the time bound of 21(a) have no statement of their own, for the same reason as the running time of Theorem 17; the theorem is cited from the literature, without a proof. The deductions between running-time claims are lemmas (`Theorem21a.of_CH20_VW13`, `Theorem21b.minPlus_of_VW13_VW18`, `Theorem21b.apsp_of_minPlus`); for programs over an arbitrary solver the claims are proved in the library; their use is covered by Theorem 22 about programs. [VW18, Theorem 4.2] has no mathematical statement; it is a program with a proof.
* **Theorem 22.** *Stated:* The whole item, about programs: both printed pairs of bounds (the statements do not say by which route a program goes), with the bounds n^{…+o(1)} for 3SUM; three headline claims. *Not stated:* The bound for 3SUM with (log n)^{O(1)}, from which the printed form follows, is a lemma. The further step that the formal rendering of "Plug Theorem 19 into Theorem 21" needs is a lemma (`exactTriangleUniform_of_explicit`).
* **Remark 23.** *Stated:* Nothing. *Not stated:* 3XOR: the paper indicates the method in one sentence and gives no proof.

## Section 4

| Item | Page | Statements | Proved in |
|---|---|---|---|
| **Table 1**<br>Parameters | 37 | `table_1_section_2_column`, `eq_5`, `eq_7`, `sec4_rho_lt_one`, `sec4_Rc_lt_epsStar` | [`ThreeSumApsp/Sec4/Table2/Captions.lean`](../ThreeSumApsp/Sec4/Table2/Captions.lean)<br>[`ThreeSumApsp/Sec2/Orders.lean`](../ThreeSumApsp/Sec2/Orders.lean)<br>[`ThreeSumApsp/Sec4/Theorem30.lean`](../ThreeSumApsp/Sec4/Theorem30.lean)<br>[`ThreeSumApsp/Sec4/Corollary31/Limit.lean`](../ThreeSumApsp/Sec4/Corollary31/Limit.lean) |
| **Theorem 24**<br>The data structure for every ε < ε* and q > 0 | 39 | `wordRam_theorem_24` | [`ThreeSumApsp/RunningTimes/Sec4/Theorem24_25.lean`](../ThreeSumApsp/RunningTimes/Sec4/Theorem24_25.lean) |
| **Theorem 25**<br>Wanted entries for every ε < ε* and κ > 0 | 39 | `wordRam_theorem_25` | [`ThreeSumApsp/RunningTimes/Sec4/Theorem24_25.lean`](../ThreeSumApsp/RunningTimes/Sec4/Theorem24_25.lean) |
| **Table 2**<br>Explicit exponents | 40 | `table_2_c40`, `table_2_c21`, `table_2_c19`, `table_2_c15`, `table_2_c12`, `table_2_c10_5`, `table_2_query_valid`, `table_2_ninth_valid`, `table_2_density_valid`, `table_2_larger_c` | [`ThreeSumApsp/Sec4/Table2.lean`](../ThreeSumApsp/Sec4/Table2.lean)<br>[`ThreeSumApsp/Sec4/Table2/Captions.lean`](../ThreeSumApsp/Sec4/Table2/Captions.lean) |
| **Corollary 26**<br>N ≥ D^18: preprocessing N²/D^0.063, query D^0.437 | 40 | `wordRam_corollary_26`, `wordRam_corollary_26_wanted`, `corollary_26_W` | [`ThreeSumApsp/RunningTimes/Sec4/Corollary26.lean`](../ThreeSumApsp/RunningTimes/Sec4/Corollary26.lean)<br>[`ThreeSumApsp/Sec4/Corollary26.lean`](../ThreeSumApsp/Sec4/Corollary26.lean) |
| **Figure 9**<br>The cube and the boxes of an output string in the recursion tree, for L = 3, t = 1 | 41 | none |  |
| **Figure 10**<br>The boxes for m = 4, t = 2 | 42 | `figure_10_counts`, `figure_10_rows`, `figure_10_Vof` | [`ThreeSumApsp/Sec4/Lemma27_28.lean`](../ThreeSumApsp/Sec4/Lemma27_28.lean) |
| **Lemma 27**<br>The unique V with V \ F_V ⊆ Z ⊆ V | 44 | `lemma_27` | [`ThreeSumApsp/Sec4/Lemma27_28.lean`](../ThreeSumApsp/Sec4/Lemma27_28.lean) |
| **Lemma 28**<br>Boxes partition the leaves of order at least t | 44 | `lemma_28_leaves`, `lemma_28_unique`, `lemma_28`, `lemma_28_counts`, `lemma_28_boxes` | [`ThreeSumApsp/Sec4/Lemma27_28.lean`](../ThreeSumApsp/Sec4/Lemma27_28.lean) |
| **Lemma 29**<br>The number of boxes, and the dynamic program | 45 | `lemma_29_count`, `lemma_29_values`, `lemma_29_split` | [`ThreeSumApsp/Sec4/Lemma29.lean`](../ThreeSumApsp/Sec4/Lemma29.lean) |
| **Equation (7)**<br>β_d ≤ ρ^d M | 46 | `eq_7_ratio`, `eq_7` | [`ThreeSumApsp/Sec4/Theorem30.lean`](../ThreeSumApsp/Sec4/Theorem30.lean) |
| **Theorem 30**<br>The data structure in terms of m, L, t; contains equations (8) and (9) | 46-47 | `wordRam_theorem_30`, `wordRam_theorem_30_wanted` | [`ThreeSumApsp/RunningTimes/Sec4/Theorem30.lean`](../ThreeSumApsp/RunningTimes/Sec4/Theorem30.lean) |
| **Equations (8), (9)**<br>The cost expressions of Theorem 30 | 46-47 | `wordRam_theorem_30`, `wordRam_theorem_30_wanted` | [`ThreeSumApsp/RunningTimes/Sec4/Theorem30.lean`](../ThreeSumApsp/RunningTimes/Sec4/Theorem30.lean) |
| **Equation (10)**<br>D^γ · 10^L / (√K N₀) ≤ N | 48 | `eq_10_corollary_26`, `eq_10` | [`ThreeSumApsp/Sec4/Corollary26.lean`](../ThreeSumApsp/Sec4/Corollary26.lean)<br>[`ThreeSumApsp/Sec4/Corollary31.lean`](../ThreeSumApsp/Sec4/Corollary31.lean) |
| **Equation (11)**<br>R_c(γ) | 48 | `eq_11_iff` | [`ThreeSumApsp/Sec4/ChoosingParameters.lean`](../ThreeSumApsp/Sec4/ChoosingParameters.lean) |
| **Corollary 31**<br>Exponents γ and q, the condition ε < R_c(γ), the limit ε* | 49 | `wordRam_corollary_31`, `corollary_31_gamma_pos`, `sec4_Rc_strictAntiOn`, `sec4_Rc_zero_tendsto`, `sec4_epsStar_numeric` | [`ThreeSumApsp/RunningTimes/Sec4/Corollary31_32.lean`](../ThreeSumApsp/RunningTimes/Sec4/Corollary31_32.lean)<br>[`ThreeSumApsp/Sec4/ChoosingParameters.lean`](../ThreeSumApsp/Sec4/ChoosingParameters.lean)<br>[`ThreeSumApsp/Sec4/Corollary31/Limit.lean`](../ThreeSumApsp/Sec4/Corollary31/Limit.lean) |
| **Corollary 32**<br>Wanted entries for \|W\| ≤ N²/D^κ | 49 | `wordRam_corollary_32`, `corollary_32_saving` | [`ThreeSumApsp/RunningTimes/Sec4/Corollary31_32.lean`](../ThreeSumApsp/RunningTimes/Sec4/Corollary31_32.lean)<br>[`ThreeSumApsp/Sec4/Corollary32.lean`](../ThreeSumApsp/Sec4/Corollary32.lean) |

* **Table 1.** *Stated:* Every cell that is a claim: ρ < 1/2, γ = 1/18, ε = 1/18 and β_d ≤ 2^{-d} M in Section 2; β_d ≤ ρ^d M, ρ < 1, R_c(γ) < 0.1204… in Section 4. *Not stated:* The other cells are choices or definitions. "M = β₀ ≤ 10^L" (Section 4) is two lemmas (`beta_zero_eq_M`, `M_le_ten_pow`).
* **Theorem 24.** *Stated:* The whole item, about programs. *Not stated:* "Space" is read as under Theorem 3.
* **Theorem 25.** *Stated:* The whole item, about programs. *Not stated:* Nothing.
* **Table 2.** *Stated:* All 66 entries, row by row; that every entry is computed as Section 4.4 prescribes and is rounded down; that the ε of a row is rounded down; that Corollary 31 or 32 then gives what the caption claims for the entry; "A larger c gives a larger γ but a smaller ε", at a fixed θ, that is, column by column in the left half of the table. *Not stated:* "A larger c gives a larger γ but a smaller ε" for the right half of the table, where θ moves with c, and for the ε of a row, which is the smallest R_c(γ) over all its entries: the statement has R_c(γ) decreasing in each column of the left half. That the bold entry of the row c = 21 is Corollary 26 has no statement of its own; `table_2_c21` and `table_2_ninth_valid` give γ ≥ 0.0640 > 0.063, q ≤ 0.43 < 0.437 and ε = 0.056 > 1/18. "a slower query or a sparser W allows a larger γ" (caption) has no statement of its own. That "the θ that gives the q of the column" and "the θ at which γ = κ − q" (Section 4.4) are unique is shown by lemmas: q increases on (0, 0.9) (`qOf_strictMonoOn`), and the balancing θ exists, is unique and is optimal (`exists_gammaOf_eq_sub_qOf`); the statements say "there is a θ". The entries are not instantiated about programs one by one.
* **Corollary 26.** *Stated:* The whole item: the data structure and the bound for a set W about programs (D ≥ 1 is assumed: NOTE at `Items.Corollary_26`), and the last clause as arithmetic. *Not stated:* "Space" is read as under Theorem 3.
* **Figure 9.** *Stated:* Nothing. *Not stated:* An illustration of the definitions of Section 4.2 in a small example. That w has α₁ = 18 boxes, and that these contain exactly its leaves of orders 1 and 2, are instances of Lemma 28.
* **Figure 10.** *Stated:* The numbers 486 and 9963, the sets F_V of the six rows, and the rows of the sets Z of at most one level. *Not stated:* That a row stands for the 9^t = 81 boxes of 𝓑_V and that a box has 10^{|F_V|} leaves: in the statements 81 and the powers of ten are numerals, and the general counts are lemmas (`card_BV`, `Cube.card_leaves`). The six sets Z of two levels, which appear in the row V = Z, are not written out. The two worked examples of Section 4.2 in the setting of the figure are lemmas (`BoxExamples.boxOfLeaf_example_first`, `BoxExamples.leaves_example_first`, `BoxExamples.boxOfLeaf_example_second`).
* **Lemma 27.** *Stated:* The whole item. *Not stated:* Nothing.
* **Lemma 28.** *Stated:* In four pieces, and that the cubes of 𝓑_V are boxes, with stars at the levels of F_V (Section 4.2). *Not stated:* That the sets 𝓑_V are disjoint is a lemma (`BV_pairwiseDisjoint`); it also follows from `lemma_28_counts`. The second description of the boxes of w, by the leaves of order exactly t (Section 4.2), is a lemma (`existsUnique_starBelow_eq`; for the list of boxes that a query reads, `mem_boxesOf_iff`). That the boxes of an output string "all have exactly m - t symbols that are P₀ or stars" (Section 4.2) is a lemma (`card_starLevels_add_card_P0Levels`).
* **Lemma 29.** *Stated:* The number of boxes; the recurrence of the dynamic program returns the values; the ten strings that it looks up are boxes with e − 1 stars. *Not stated:* "in O(L) time and space per box" has no statement. Theorem 30 about programs has its consequence, the first term of (8); the step bounds of the routines are lemmas. That the trie of a tile holds the value of each of its boxes is a lemma (`lookup_allTries_eq_val`).
* **Equation (7).** *Stated:* Both halves. *Not stated:* Nothing.
* **Theorem 30.** *Stated:* The whole item, about programs, with (8) and (9) as the trusted expressions `cost8` and `cost9`. *Not stated:* The correctness of a query in the terms of Section 4 is a lemma (`Theorem30.correct`), as are the summands of (8). "Space" is read as under Theorem 3.
* **Equations (8), (9).** *Stated:* Expressions inside Theorem 30: the trusted `cost8` and `cost9`. *Not stated:* How (8) is assembled from its summands is a lemma (`Theorem30.cost8_assembly`); (9) = |W| queries + (8) is a lemma (`Theorem30.cost9_eq`).
* **Equation (10).** *Stated:* The inequality with the numbers of the proof of Corollary 26, where it is printed (L = 21m, γ = ln(20/9)/(9 ln 4), N ≥ 4^{18(m-1)}), for all m ≥ 60; and with the parameters of Corollary 31 (L = ⌈cm⌉, γ = θ ln(1/ρ_c)/ln 4, D ≤ N^ε), for all large m. *Not stated:* Nothing.
* **Equation (11).** *Stated:* The definition `Rc`, with the equivalence that the proof of Corollary 31 draws from it: ε < R_c(γ) says that Λ < 4^{1/ε}. *Not stated:* Nothing.
* **Corollary 31.** *Stated:* Every clause: γ > 0; the times, about programs; R_c(0) increases to ε* = 0.1204…. *Not stated:* "Space" is read as under Theorem 3.
* **Corollary 32.** *Stated:* Every clause. *Not stated:* Nothing.

## Section 5

| Item | Page | Statements | Proved in |
|---|---|---|---|
| **Theorem 33**<br>Zwick's algorithm as a deterministic reduction | 51 | none |  |
| **Theorem 34**<br>Directed unweighted APSP | 53 | `theorem_34_blocks`, `theorem_34_entries`, `theorem_34_total`, `theorem_34_absorb` | [`ThreeSumApsp/Sec5/Theorem34.lean`](../ThreeSumApsp/Sec5/Theorem34.lean) |
| **Theorem 35**<br>Real inputs: 3SUM, APSP, (min,+)-product, Exact Triangle | 54 | `theorem_35_d`, `theorem_35_counting_call`, `theorem_35_forming_lists`, `theorem_35_min_plus_total`, `theorem_35_further_time`, `theorem_35_three_sum_count`, `theorem_35_three_sum_total`, `theorem_35_one_run`, `theorem_35_restarts` | [`ThreeSumApsp/Sec5/Theorem35.lean`](../ThreeSumApsp/Sec5/Theorem35.lean) |
| **Lemma 36**<br>Reductions to comparison counts | 54-55 | `lemma_36a_exact_triangle`, `lemma_36a_min_plus_below`, `lemma_36a_min_plus_successor`, `lemma_36a_min_plus_blocks`, `lemma_36a_count`, `lemma_36a_valid`, `lemma_36a_colors`, `lemma_36a_pairs`, `lemma_36a_subtractions`, `lemma_36b_count`, `lemma_36b_lists`, `lemma_36b_subtractions`, `theorem_21b_repeated_squaring` | [`ThreeSumApsp/Sec5/Lemma36a.lean`](../ThreeSumApsp/Sec5/Lemma36a.lean)<br>[`ThreeSumApsp/Sec5/Lemma36b.lean`](../ThreeSumApsp/Sec5/Lemma36b.lean)<br>[`ThreeSumApsp/Sec3/Theorem21b/RepeatedSquaring.lean`](../ThreeSumApsp/Sec3/Theorem21b/RepeatedSquaring.lean) |
| **Lemma 37**<br>Comparison counts as a thin product plus corrections | 56 | `lemma_37`, `lemma_37_order_exists`, `lemma_37_index_exists`, `lemma_37_enumerated` | [`ThreeSumApsp/Sec5/Lemma37.lean`](../ThreeSumApsp/Sec5/Lemma37.lean) |
| **Corollary 38**<br>Comparison counts solved | 57 | `corollary_38_bound`, `corollary_38_correct` | [`ThreeSumApsp/Sec5/Corollary38.lean`](../ThreeSumApsp/Sec5/Corollary38.lean) |
| **Corollary 39**<br>Zero-, Min- and Max-Weight k-Clique | 58 | `wordRam_corollary_39_zero`, `wordRam_corollary_39_min_max`, `endStatement_corollary_39_zeroWeight` | [`ThreeSumApsp/RunningTimes/Sec5/Corollary39.lean`](../ThreeSumApsp/RunningTimes/Sec5/Corollary39.lean)<br>[`ThreeSumApsp/Statements/EndStatement.lean`](../ThreeSumApsp/Statements/EndStatement.lean) |
| **Corollary 40**<br>The hinted Mv conjectures | 59 | `wordRam_corollary_40_times`, `wordRam_corollary_40_general_times`, `wordRam_corollary_40_fail` | [`ThreeSumApsp/RunningTimes/Sec5/Corollary40.lean`](../ThreeSumApsp/RunningTimes/Sec5/Corollary40.lean) |

* **Theorem 33.** *Stated:* Nothing. *Not stated:* The paper proves it in Section 5.1; it is not proved here. It occurs only as a hypothesis (`Claim.Theorem_33`) of the conditional deduction of Theorem 34, a lemma of the library (`conditional_theorem_34`).
* **Theorem 34.** *Stated:* The cutting into blocks and the arithmetic of the proof. *Not stated:* Not proved for any machine: it rests on Theorem 33, which is not proved here, and on μ, which is defined through ω(1, μ, 1). The deduction from Theorem 22 and Theorem 33, for an arbitrary meaning of "is solved in time T", is a lemma of the library (`conditional_theorem_34`).
* **Theorem 35.** *Stated:* The main displays and bounds of the proof as arithmetic; the probability of the restarts. *Not stated:* Not proved for any machine (Las Vegas, real RAM). The deduction from Corollary 38, Lemma 36 and restarts, for an arbitrary meaning of "is solved in time T", is a lemma of the library (`conditional_theorem_35`). The side bounds n^{2.0219} and n^{2.0228} of the proof are not stated on their own. The opening clause, on the real RAM and its operations, belongs to the intended meaning of that lemma and is not expressed by it.
* **Lemma 36.** *Stated:* What the paper itself argues: how the problems are read off predecessors and successors, that a counting call is d comparison counts (one for 3SUM), and the clauses of the lemma on the lists, colors and subtractions, and for part (a) on the pair sets. *Not stated:* The randomized reductions of [CVX22] to the counting problems are cited; the lemma as a whole is a hypothesis (`Claim.Lemma_36a`, `Claim.Lemma_36b`) of the conditional deduction of Theorem 35. The clause of part (b) on a pair set of size O(n²/d), and the last sentence, on the operations on real numbers, are not stated. That the n/d blocks of n² entries make n³/d ("Õ(n³/d) further time") is arithmetic, and a lemma of the library (`Lemma36a.mul_sq_eq_cube_div`).
* **Lemma 37.** *Stated:* The identity for the matrices that the proof constructs, with < and with ≤; its hypotheses can be met; the number of pairs enumerated. *Not stated:* The running time is a hypothesis (`Claim.Lemma_37`, with log n + 1 for log n: NOTE) of the conditional deduction of Corollary 38.
* **Corollary 38.** *Stated:* The arithmetic of the bound, with the time of Lemma 37 as in `Claim.Lemma_37`; the correctness with the hypotheses of Corollary 26, and D″ ≤ D*, so that the padding cuts nothing off. *Not stated:* Not proved for any machine (comparisons of real numbers). The deduction from Lemma 37 and Corollary 26, for an arbitrary meaning of "is solved in time T", is a lemma of the library (`conditional_corollary_38`). The clause "by an algorithm whose only operations on real numbers are comparisons" belongs to the intended meaning of that lemma and is not expressed by it. The bounds D″ ≤ 3d²n^{1/440} and D* ≤ 4n^{23/440} of the proof are lemmas.
* **Corollary 39.** *Stated:* The whole item, about programs; zero weight again as a headline claim. *Not stated:* The reduction in the terms of Section 5.3 is lemmas.
* **Corollary 40.** *Stated:* The whole item, about programs, and the running times of the paragraph "General τ" of its proof (for Conjecture 5.12, τ₂ < 1 is assumed, the standing assumption of Section 5.4: NOTE at `Items.Corollary_40_times`). *Not stated:* The rectangular exponents of matrix multiplication are arbitrary real numbers subject to the lower bounds of Corollary 40; that the true exponents satisfy these bounds is not stated.

## No item of the paper: definitions that are written twice

| Item | Page | Statements | Proved in |
|---|---|---|---|
| **Definitions that are written twice**<br>The notions that `EndStatement.lean` and `PaperStatements.lean` each define in their own words |  | `agreement_exactTriangle`, `agreement_minPlusProduct`, `agreement_apsp_noNegativeCycle`, `agreement_apsp_output`, `agreement_rowByRow`, `agreement_cliqueWeight`, `agreement_solves`, `agreement_bigO`, `agreement_solvedInTime` | [`ThreeSumApsp/Statements/Agreement.lean`](../ThreeSumApsp/Statements/Agreement.lean) |

* **Definitions that are written twice.** *Stated:* That the two texts agree: Exact Triangle, the (min,+)-product, APSP (the promise that there is no negative cycle, and the output), a matrix written row by row, the weight of a k-clique, "a program solves a problem", O(n^r), and "solved in time", for rational exponents r ≥ 0 and no logarithmic factor. *Not stated:* Nothing.
