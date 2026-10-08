# Remarks on the statements

This document is for a reader who compares the Lean statements with the sentences of the paper. It says where the two differ and why, and what is not proved. None of the differences affects a result of the paper or changes one of its bounds.

Most remarks of this document record what a formal text has to settle and a paper need not: hypotheses that the paper leaves implicit, such as m ≤ L in Section 2 or ν ≥ 0 in Theorems 21 and 22; choices between two readings, such as whether the three numbers in 3SUM must come from three different positions, the zero diagonal of a weight matrix, or n^{a+o(1)} as an upper bound; the direction in which n^μ, n^τ, n^{1/3} and n/d are rounded to integers; and steps and costs that a program has to pay for and a proof need not count, or that the library writes out as lemmas, each within the printed bound.

The first section is meant to be read. The others are for looking things up.

* **What is not proved.** Which sentences of the paper have no proof here, or only a conditional one.
* **Sections 2 to 5**, one group for each section of the paper; Theorems 1 to 4 go with Section 5. *Differences* says where a statement or a lemma differs from the printed sentence, and what the Lean text does there. *Running times* is a table of the sentences about time or space and the statements about programs that state them. *Cited results* (Sections 3 and 5) says which results from the literature are proved here, which are hypotheses, and which are left out.
* **The conditional lemmas: what is assumed.** The hypotheses of the three conditional lemmas.
* **Every NOTE.** In the Lean files, a paragraph of a comment that begins with the word NOTE marks a place where the Lean text departs from the printed text. The last section lists all of them. It is written by `scripts/index.py`; no script writes the rest of this document.

Docstrings point into this document by the title of a section, for example: `docs/REMARKS.md`, "Section 4: running times".

**Other documents.** `README.md` explains the words *statement*, *lemma*, *library* and *statement about programs*. `docs/INDEX.md` says for each numbered item, table and figure of the paper what is stated, where, and what is not stated. `docs/MACHINE.md` describes the machine and the meaning of "solved in time T" (Part 1), and says where the programs depart from the paper (Part 3).

**Conventions.** "Section 2", "Theorem 5", "(8)" refer to the paper. Quotations have the paper's letters. The Lean text writes `κ` for the ν of Sections 3 and 5; in Section 4 and in Theorem 1, κ is the paper's κ (`docs/MACHINE.md`, "References and letters"). `Items.Theorem_5` stands for `ThreeSumApsp.WordRam.Items.Theorem_5`, a proposition in `PaperStatements.lean`. A *claim* `Claim.…` is a proposition about an arbitrary meaning of "is solved in time T"; the five claims are those of `EndStatement.lean`. The claims (for instance `Claim.Lemma_37` and `Claim.Theorem_17`) are definitions of the library. The prefixes `wordRam_` and `endStatement_` mark statements, and `conditional_` marks the three conditional lemmas. Of the other theorems of Lean that a point names, it says which are statements; the rest are lemmas.

## What is not proved

* **Real inputs, and Section 5.1.** Theorem 35 and the half of Theorem 2 on real inputs are about Las Vegas algorithms on a real RAM. Corollary 38 and Lemma 37 are deterministic, but their inputs are real numbers. The machine has integer words and no random bits, so these running times are not proved for any machine. Theorem 34 is about a deterministic algorithm with integer inputs. But it rests on Theorem 33, which the paper proves and which is not proved here, and its bound is written with μ, an exponent of rectangular matrix multiplication, which is not defined here. So its running time is not proved for any machine either. Two things are stated about these items. The statements for Section 5 have what the paper itself argues and what needs no machine: correctness of the constructions, counts, and the arithmetic of the bounds; none of them is about Theorem 33 or its proof. And there are the three conditional lemmas, described next.
* **What the three conditional lemmas do and do not say.** They are lemmas of the library, not statements. They check the paper's deductions from one running-time sentence to the next, for an arbitrary meaning of "is solved in time T". None of the three proves a running time, and none is a theorem of the paper. Every claim that a deduction starts from is a hypothesis; the section "The conditional lemmas: what is assumed" lists them. For Theorem 34 the conclusion is that of Theorem 33, so the lemma checks that the premise of Theorem 33 holds.
* **Theorem 33, and cited results.** Theorem 33, which the paper proves, is not proved here; it occurs only as a hypothesis. Lemma 36 restates randomized reductions of [CVX22]; as a sentence about running times it occurs only as a hypothesis, and the part that the paper itself argues is among the statements for Section 5.
* **Theorems 17 and 21 in their printed form.** They say that an algorithm for one problem gives an algorithm for another. They are not stated about programs of the machine, because such a program cannot simply be called as a subroutine: the definition of solving does not say which cells a program reads or writes, and a program may rely on zeros outside its input. Theorem 17 is stated without its running time (`theorem_17`), and so are parts of Theorem 21. For programs of the language that call an arbitrary solver, the library proves versions of both; for Theorem 17 this is done for the two choices of its parameters D and g in the proof of Theorem 19, and with Strassen's exponent in place of ω. The statements for Theorems 19, 22 and 2 and Corollary 39 rest on these lemmas.
* **The programs for [VW13] and [VW18] are not compared with their sources.** The paper cites the reductions of Theorem 21, and that of [VW13] in the proof of Corollary 39, without proofs. The construction for [CH20] follows the proof in that paper, with changes that "Section 3: cited results" lists; the programs for [VW13] and [VW18] are constructions of this formalization for the cited statements, and are not compared with the constructions in those papers.
* **Exponents of matrix multiplication** (ω, α, μ and the rectangular exponents) are not defined. Where the paper uses a bound on them, the bound is an explicit hypothesis or a numeral. In Corollary 40, that one of the three conjectures of [vdBNS19] fails means this: put arbitrary real numbers in place of the rectangular exponents in the conjecture, subject only to the lower bounds that Corollary 40 names; then programs achieve smaller exponents than the conjecture allows. That the true exponents satisfy these lower bounds is not proved.
* **Running-time sentences inside lemmas and proofs**, such as the second sentence of Lemma 29 and the cost paragraphs of Section 2.4.4 and of the proof of Theorem 30, have no statement of their own. Inside the proofs, the bounds on the steps of the individual routines correspond to them.
* **The hypotheses that the paper calls refuted** (3SUM, APSP, Exact Triangle, k-Clique and others) are not defined; only running times are stated. The conjectures of [vdBNS19] are the exception.
* **The triangle problems for a middle part of more than n^{1/18} and up to n^{0.12} vertices** (Section 1.1, "for every ε < 0.1204"). Up to n^{1/18} they are Corollary 16; beyond that, Theorem 25 and Corollary 32 are stated for matrices only.
* **Consequences through reductions that the paper only names**: the list "More new algorithms" of Section 1.2, "also on general graphs" after Corollary 39, the variant of Conjecture 5.7 at the end of Section 5.4, and the discussion of which results of [vdBNS19] rely on the conjectures in the refuted regime.
* **Search versions** of the decision problems, and instances with N = 0 or D = 0 in the statements with two sizes.
* **Remark 12** makes no mathematical claim. **Remark 23**, on 3XOR, indicates the method in one sentence and gives no proof. Figures 1, 2, 5 and 8 make no claim of their own. Figure 7 draws the count of Lemma 11; two remarks of its caption are not stated. Figure 9 illustrates the definitions of Section 4.2 in a small example and has no statement.

## Section 2: differences

The statements for Section 2 are in the part "Section 2: statements" of `PaperStatements.lean`.

1. **Lemma 10, second claim, and its proof.** The second claim of the statement `lemma_10`, "The leaves it visits are exactly those of Leaves(U)", carries the hypothesis 0 < L ∨ U ≠ ∅; the first and the third claim are stated for every L and U. `Lemma10.leaves_visited` carries the same hypothesis, and `Pruned.called_iff`, for "the vertex is called if and only if this set is nonempty" in the proof, carries `1 ≤ k ∨ U.Nonempty`. In the paper L ≥ m ≥ 1, and the algorithm of Section 2.4.4 runs Pruned on nonempty sets only.
2. **Section 2.4.2, Pruned.** In step (1) of Pruned, Lean returns the product as an array on S, like every other result of the procedure. Step (3) makes a call for each term λ "with S_λ ≠ ∅". In Lean, the array C_λ of a term with S_λ = ∅ is written as the zero array, so that the sum "c_{z₀} := ∑_λ C_λ" of step (4) has ten summands in every case. The choice of the zero array has no effect.
3. **Section 2.4.3: m ≤ L is not stated.** The inequality is implied by L = 19m and by L ≥ 10m. It is needed for two counts of that section and for the ratio in (5), which the paper prints under L = 19m and Lean states for every L ≥ m. Lemma 9 and both inequalities of Lemma 11 hold without it. In Lean, the hypothesis m ≤ L is written out where it is needed, and the structure that holds the layout of the tiling has it as a field. The statements that carry it are `sec2_card_outStr_of_leaf` and `eq_5_ratio`.
4. **Section 2.4.3: range of d.** The order of a leaf is negative when it chooses P₀ at more than m levels; "the total number of leaves of order d" and β_d are meant for 0 ≤ d ≤ m. In Lean, the order of a leaf is integer valued, and `card_filter_order_eq`, which gives the count, carries the hypothesis d ≤ m.
5. **The display in the proof of Lemma 11.** The strict inequality "(72·(9/8)^9)^{m/9} < 256^{m/9}" needs m ≥ 1, which is fixed in Section 2.3.3; `sum_alpha_small_orders_lt` carries `1 ≤ m`. The same holds for "more than the M = binom(L, m) 9^{L−m} entries" in Section 2.4.1, which is not stated in Lean.
6. **Sections 2.3.3 and 2.3.4: which string indexes which row.** Strings index the N₀ rows of a row block, the N₀ columns of a column block and the D columns of X (= rows of Y). Any bijections work, provided that the same one is used for the columns of X and the rows of Y. In Lean, these bijections are fields of one structure, the layout, together with the K₀² subsets, and every lemma about the tiling is proved for every layout.
7. **Section 2.4.4: N after padding.** The paper writes N for both sizes ("we continue to write N for the padded size"). In Lean, the original size and the padded size are written differently.
8. **Section 2.4.4: small hypotheses.** See the NOTEs at `K_le_pow`, `abs_bandArrayL_le` and `abs_bandArrayR_le`.

### Left out on purpose

The following passages of Section 2 have no Lean counterpart.

* Section 2.1, "7^L = N^{log₂ 7} < N^{2.81}". The sentence recalls the number of multiplications of Strassen's algorithm. Of it, only log₂ 7 < 2.81 is a lemma (`logb_two_seven_lt`), which the proof for Theorem 19 uses.
* Section 2.2, footnote 6 (the border-rank form). The claim is true, follows from Lemma 6 by substitution, and is used nowhere.
* Section 2.3.4, "(at best D ≈ N^{0.1204} rather than N^{0.1402} [Cop82])". The first number is the ε* of Section 4.1; the second is cited.
* Section 2.3.4, "about N² D^{0.2} for our choice L = 19m"; Section 2.4.3, "D^{log₄ 10} ≈ D^{1.66}"; Section 2.4.3, "about N₀^{0.07}". These are approximate remarks with no exact reading, and they are used nowhere.
* Section 2.4.3, "The private leaf contributes to no other output string". The sentence is about the output strings of that subsection, whose inner sets have exactly m elements.

## Section 2: running times

The sentences refer to the machine model of Section 2: "the standard word RAM model with O(log N)-bit words, and thus count operations on O(log N)-bit integers". Only Theorem 5 has a statement about programs. The other sentences are intermediate costs or exposition.

| The sentence | Statement about programs | Remark |
|---|---|---|
| Theorem 5 | `wordRam_theorem_5` | The whole sentence. Inequality (6) of the proof is the statement `eq_6`. |
| Section 2.1, Strassen: "O(7^L)", "multiplications in total" | — | Exposition. For Section 2.1 only identity (1) is stated; the recursion occurs as a program for Theorem 17 (see "Section 3: cited results"). |
| Section 2.3.1, Full: "O(L · 10^L) operations in total"; Section 2.3.4, tiling: "O((N²/M) L · 10^L) operations"; Section 2.4.1, encodings: "O(10^L) operations" | — | Intermediate costs on the way to Theorem 5. |
| Section 2.4.4, the cost: the encodings, a call of Pruned, the pruned recursions, "The remaining minutiae", and the total | `wordRam_theorem_5`, for the total | The other sentences are the costs of the parts of the algorithm. They correspond to the proved bounds on the steps of the routines of the program for Theorem 5, which `docs/PROGRAMS.md` lists. |
| Section 2.4.4, word size: "Hence every integer has O(log N) bits" | — | The word size appears as proved limits on the numbers that the routines of that program handle. The magnitudes of the numbers, in the terms of Section 2, are lemmas. |

## Section 3: differences

The points about the reduction of [CH20] are in "Section 3: cited results".

**Sentences that need one more argument.** The first two need an argument that is not printed. For the last, the extra step is needed by the formal rendering.

1. **Proof of Theorem 17, "There are at most p + √D ≤ 2√D chunks in all".** `TriangleInstance.totalChunks_le` has the printed bound. Its proof uses that the number of chunks and D are integers and that D ≤ n.
2. **Proof of Theorem 17, "By the prime number theorem".** `exists_le_card_primesInRange` says that there is a constant c > 0 such that there are at least c √D/ln D primes in [√D/2, √D) for every D ≥ 16. It is proved by a counting form of Bertrand's postulate.
3. **Proof of Theorem 22, "Plug Theorem 19 into Theorem 21".** Theorem 21(b) asks for a bound T(s) for every s at one fixed bound on the weights, while Theorem 19 gives a bound where the weights are at most s^ν. At s = n^{1/3} the two fit together. In the claims of the library, running times have two arguments, size and magnitude. `Claim.ExactTriangleUniform` is a bound for all sizes and all magnitudes. By `exactTriangleUniform_of_explicit` it follows from the explicit form of Theorem 19, brute force for small sizes and two closure properties; this works because the bound of Theorem 17 is polynomial in κ with a constant that does not depend on κ. Whether sizes much smaller than n^{1/3} occur depends on the proof of [VW18, Theorem 4.2], which has not been compared; the programs of this formalization do use them, when they find a triangle by halving.

**Hypotheses and conventions made explicit.** Most of these places carry a NOTE, which has the reason.

4. **Section 3.2, general graphs, "(this replaces ν by ν + 1)".** `hasZeroTriangle_tripartiteOfGraph_iff` is about an integer bound U, and `weightsBoundedBy_tripartiteOfGraph` is about natural κ and n ≥ 4.
5. **Section 3.2, "the search version […] is equivalent to the decision version via a simple self-reduction".** No statement uses the equivalence: the statement `theorem_17` is about the search version, and the statements about programs decide. Lean has neither a statement nor a lemma for it.
6. **Theorem 17, statement.** In Lean, D is a natural number, ω is not defined, and Strassen's exponent log₂ 7 is used in its place; the proof of Theorem 19 uses only Strassen's bound.
7. **Proof of Theorem 17, choices left open:** which prime if several have the smallest count, how C is split, how W_ϱ is cut, the order of the scans. The Lean text holds for every selected prime and every order of the scans (`IsScanOrder`). Pieces are blocks of consecutive vertices, and W_ϱ is cut in row-major order.
8. **Proof of Theorem 19, "Assume n is larger than a constant depending on ν".** The two choices of D are stated for n ≥ 16^18 (`Theorem19.choice_theorem_5`, `Theorem19.choice_corollary_26`).
9. **Theorem 21(b).** For the clause on APSP, `Claim.Theorem_21b_apsp` has c·n^{κ+1} for cU, because n^{κ+1} bounds the entries during the repeated squaring, and ⌈n^{1/3}⌉ for n^{1/3}. A missing edge is the entry +∞ (`minPlus` allows such entries). `GoodTime`, a definition of the library, asks for T(s) ≥ s²(1 + log u). This is an upper bound for the time to write down an instance; for u = s^ν it is larger than the time to read the input by a factor of up to log s.
10. **Theorem 21(b), "log² U".** A formal bound has to be positive at U = 1 as well. `logU` is log max(U, 2). The statement `theorem_21b_negative_to_exact` counts 2⌊log₂ U⌋ + 6 instances.
11. **Theorem 21(a), "in n^{3/2+o(1)} time".** A formal deduction of this time needs a bound on the time of the reduction of [VW13, Theorem 4.3]. The statement `theorem_21a_compose` and `Claim.VW13_Theorem_4_3` carry a term N^{3/2+o(1)} for it.
12. **3SUM (Section 1, Theorems 21 and 22, and the proof of Lemma 36(b)).** "three of them sum to 0" does not say whether the three positions are distinct. `ThreeSum` has one list and three distinct positions. The proof of Lemma 36(b) uses the form a + b = c on three sets and adds: "The 3SUM version with one set and a + b + c = 0 reduces to this version in the standard way."
13. **Convolution-3SUM.** The Lean definition, `Convolution3SUM`, follows the printed one (Section 1.2): the indices start at 0.
14. **Theorem 21, "For every constant ν"; Theorem 22, "Let ν be a constant".** A formal version needs ν ≥ 0 (for negative ν the bound n^ν is below 1). The claims assume κ ≥ 0 and bounds on numbers of at least 1.
15. **Corollaries 16 and 26.** The statement `wordRam_corollary_16`, the lemma `Corollary16.bound_le_of_card_le` and `Claim.Corollary_26_wanted` have D ≥ 1.
16. **The notation n^{a+o(1)}.** It is an upper bound for times and numbers of instances, and can be read as an order of magnitude in other places (for example "on n^{1/2+o(1)} vertices", where the application of Theorem 19 needs a lower bound too). `IsPowLittleO` is an upper bound.

**The claims of the library.** The deductions of Section 3 and of Corollary 39 are lemmas about an arbitrary meaning of "is solved by a deterministic algorithm in time T", for instance `minPlus_of_uniform_theorem_21b` and `zeroClique_of_theorem_19`. These lemmas are not meant to be read on their own. They are applied to the meaning given by programs, for which their hypotheses are proved as lemmas. The results are the statements about programs, which have no hypotheses. The additive overheads of the claims, the factors 1 + log u, and the constants are not in the paper; the headers and docstrings of `ThreeSumApsp/TimeClaims/Sec3/Definitions.lean` and `ThreeSumApsp/TimeClaims/Sec5/Definitions.lean` describe each claim.

**The printed numbers.** `Items.Theorem_22_first` and `Items.Theorem_22_second` contain the sharp forms (3 − 1/1944 = 2.99948…, 3 − ε′/3 = 2.99941…) and the printed roundings. Theorem 2 prints O(n^{2.9995}), a coarser rounding, and `Items.Theorem_2` has this numeral. `Items.Theorem_22_threeSum` has the printed form n^{a+o(1)}. The programs give factors (log n)^{O(1)}; this is the lemma `Theorem22.threeSum_polylog`, from which the printed form follows.

**Not stated.** Footnote 9 (proof of Theorem 17), Remark 23, and the comparison with [CX24] and [VX20] in Remark 18, which would need the constructions of those papers.

## Section 3: running times

The statements of the part "Section 3: statements" of `PaperStatements.lean` do not speak of time. They state correctness, numbers and sizes of instances, counts, and some of the arithmetic of the cost analysis; `docs/INDEX.md` lists these statements item by item. The sentences about time themselves are statements about programs.

| The sentence | Statement about programs | Remark |
|---|---|---|
| Corollary 15, both bounds | `wordRam_corollary_15` | — |
| Corollary 16 | `wordRam_corollary_16` | — |
| Theorem 17, "plus O(ν n³ log n/g + n^{ω+o(1)} D^{3/2} + n² D g) additional time" | — | See "What is not proved". The time bound is `Claim.Theorem_17`. It is proved in the library for programs over an arbitrary solver (see point 6 of "Section 3: differences") and is used for `wordRam_theorem_19`. The statement `theorem_17` has everything but the time. |
| Theorem 19, all three bounds | `wordRam_theorem_19`; the last bound is also `endStatement_theorem_19` | — |
| Theorem 21 | — | As for Theorem 17. The time bounds are `Claim.Theorem_21a`, `Claim.Theorem_21b_minPlus` and `Claim.Theorem_21b_apsp`. Their use is covered by the statements about programs for Theorem 22. |
| Theorem 22, the bounds by both routes | `wordRam_theorem_22_first`, `wordRam_theorem_22_second`; `wordRam_theorem_22_threeSum` has the bounds for 3SUM before rounding | One bound for each of the three problems is also a claim of `EndStatement.lean`. |
| Section 3.1, equivalence of the counting version with the matrix problem, "up to polylogarithmic factors"; footnote 8 | — | Unnumbered sentences. Only their content without the time is proved, as lemmas. |
| Section 3.1, brute force in O(\|W\|D); rectangular matrix multiplication for D ≤ n^{0.321}; Remark 20 | — | Exposition; no result of the paper uses them. Statements `remark_20_…` give the arithmetic of Remark 20. |

## Section 3: cited results

Theorem 21 is cited from the literature, part (a) from [CH20, VW13] and part (b) from [VW10, VW18, VW13], and the paper gives no proof. The first six rows of the table name the results by which it is obtained here. Each reduction among them says "problem A reduces to few small instances of problem B in little time". Without the words "in little time" such a sentence is nearly empty, since a map that solves A by itself and outputs a trivial instance of B satisfies it. So each cited reduction is a program with a proof: it works over an arbitrary solver and establishes a claim about running times. Where the reduction has combinatorial content that is not empty, there is also a statement for Section 3. As a result, no statement about programs has a cited result among its hypotheses. "What is not proved" says which of the constructions are compared with their sources.

| Citation | Used in | Here | Lean names |
|---|---|---|---|
| [CH20, Theorem 5.1]: 3SUM to Convolution-3SUM | Theorem 21(a) | a program with a proof; see below | `Claim.CH20_Theorem_5_1`; statements `theorem_21a_threeSum_to_convolution`, `theorem_21a_threeSum_to_exact`; lemmas `ChanHe.reduction_correct`, `ChanHe.instances_correct` |
| [VW13, Theorem 4.3]: Convolution-3SUM to Exact Triangle | Theorem 21(a) | a program with a proof | `Claim.VW13_Theorem_4_3`; statement `theorem_21a_convolution_to_exact` |
| [VW13, Theorem 3.3]: Negative Triangle to Exact Triangle | Theorem 21(b) | a program with a proof | `Claim.VW13_Theorem_3_3`; statement `theorem_21b_negative_to_exact` |
| [VW13, Proposition 3.4]: an inequality between integers, expressed by equations between their binary prefixes | Theorem 21(b) | a lemma, in a form chosen for this formalization; used in the proof about the program of the row above | `Theorem21.lt_iff_exists_prefixGap` |
| [VW18, Theorem 4.2]: the (min,+)-product from Negative Triangle; [VW18, Lemma 4.1]: finding from deciding | Theorem 21(b) | a program with a proof, in three layers: finding from deciding, all pairs from finding, the product from all pairs; no statement | `Claim.VW18_Theorem_4_2` |
| repeated squaring, with entries bounded by n^{ν+1} | Theorem 21(b) | a program with a proof | `Claim.ApspFromMinPlus`; statements `theorem_21b_repeated_squaring`, `theorem_21b_entries_bounded` |
| the prime number theorem | proof of Theorem 17 | replaced by a lemma, which is proved | `exists_le_card_primesInRange` |
| hashing modulo a prime, and the other tools | proof of Theorem 17 | the arguments are given in the paper and are proved in Lean, partly as statements and partly as lemmas | — |
| [Str69]: O(n^{log₂ 7}) ring operations | proof of Theorem 17 | Strassen's algorithm is a program with a proof | — |
| ω < 2.372; α ≥ 0.321 | Theorem 17; Section 3.1 | left out; these bounds are not used | — |

**[CH20].** Theorem 5.1 of [CH20] is a statement about running times. By Definitions 2.1 and 2.2 of that paper it is about 3SUM on three sets and Convolution-3SUM on three arrays. The construction in Lean follows its proof, with changes, and adds three steps that are not in that proof: from one set to three, from positions to values, and from three arrays to one. For the first, [CH20] has a different reduction (Lemma A.3 in its appendix); of the third it says that the versions are equivalent; the second it does not treat.

### The reduction after Chan and He, compared with [CH20]

The definitions are in the namespace `ChanHe`. Theorem 5.1 of [CH20] is about integers bounded by U: from a deterministic algorithm for Convolution-3SUM with running time O(n^(2-ε)), for a constant ε with 0 < ε ≤ 1/2, it obtains a deterministic algorithm for 3SUM whose running time is larger only by a factor polylogarithmic in U.

**How `reduction` relates to the proof of Theorem 5.1 of [CH20].** The construction follows the proof of Theorem 5.1. As in Pătraşcu's reduction ([Păt10] in the paper), which [CH20] follows, elements are hashed into arrays, and the elements that are well hashed are sent to Convolution-3SUM. Three ideas are Chan and He's. (1) Hash by x ↦ x mod pq for two primes p and q, each at most √n polylog(nU). (2) Choose p, and then q, by exhaustive search. (3) Do not treat the badly hashed elements directly, but recurse on them, once for each of the three sets. The bound on the primes is fixed by the original n at every node of the recursion. So a set of n/k elements leaves at most n/(2k²) badly hashed ones, the sizes fall doubly exponentially, and the ternary recursion tree has depth O(log log n).

The details differ from [CH20] as follows. Logarithmic factors are not optimized.

* We count colliding ordered pairs. [CH20] bounds the number of elements in buckets of size at least τ, for every power of two τ.
* Where [CH20] uses Markov's inequality and a union bound, we count.
* We take all primes up to m, so that a Chebyshev-type bound that is already in Mathlib suffices. [CH20] takes the primes in [m/2, m). So our modulus M is only bounded above, by m², and it can be much smaller; all instances are read at a common length N ≥ 2m², and beyond 2M they hold padding. Also, we bound the number of our candidates that divide a difference by log₂(2U), where [CH20] has O(log U / log m) because its primes are at least m/2. This makes m larger by a logarithmic factor.
* We never need p ≠ q. [CH20] invokes the Chinese remainder theorem.
* An element is well hashed (light, in the words of the definitions) when it is alone in its bucket, so a node makes one instance. [CH20] allows one companion.
* The third array is written twice in a row, which absorbs the carry of (a mod M) + (b mod M). [CH20] allows for a constant number of offsets (almost linearity).
* The numbers lie in [-U, U]. [CH20] defines its hash functions on {0, ..., U-1}.
* A cell that receives no element, because its bucket is empty or has several elements, holds the padding value ±(2U + 1).
* The recursion stops at an empty set. [CH20] stops at constant size and solves what is left directly. The definition also cuts the tree off after `fuel n` levels; if the three sets have at most n ≥ 1 elements each, all of absolute value at most U, no node lies deeper (this is part of the proof of the library's lemma `ChanHe.reduction_correct`, which has these hypotheses).
* All constants are explicit.

**What `instances` adds to the proof of Theorem 5.1 of [CH20].** Theorem 5.1 is about three sets and three arrays. For the passage to n numbers and to one array we use elementary devices.

* One set, three distinct elements. We split the set by two binary digits (`splitA`, `splitB`), which multiplies the number of instances by `2 (Lam (2U))²`, about 2 log² U. Lemma A.3 of [CH20] uses a recursive partition instead. Under a monotonicity assumption, this costs only a constant factor in the running time, but it makes polynomially many calls, on smaller and smaller sets.
* Positions instead of values. The inputs of [CH20] are sets. A solution that repeats a value has the form a, a, -2a or 0, 0, 0, and two further three-set inputs take care of these (`twiceSet`, `zeroSet`).
* Three arrays to one (`oneArray`). [CH20] notes that the versions are equivalent.

## Section 4: differences

The differences concern constants, degenerate parameter values, and small steps that the library writes out as lemmas.

1. **Theorem 30.** "The constants hidden in the O(·) depend only on the exponent in N^{O(1)}." In `Items.Theorem_30` there is, for each exponent, one constant for all m, L, t, and also one pair of programs: m, L, t are part of the input.

2. **Corollary 26.** The statements about programs, `wordRam_corollary_26` and `wordRam_corollary_26_wanted`, are for D ≥ 1.

3. **Theorems 24 and 25; Corollary 31.** The statements are for every real ε below ε*, or below R_c(γ), as printed, and have no hypothesis ε > 0: for ε ≤ 0 no D and N satisfy 2 ≤ D ≤ N^ε, so this case is empty. The statement `eq_11_iff`, which does not speak of D and N, has the hypothesis ε > 0.

4. **Lemma 28.** The third clause of the statement `lemma_28_counts` says that the union ⋃_V 𝓑_V has α_t elements; this is the sentence of Section 4.2 that "w has exactly α_t boxes". Together with the second clause it says that the sets 𝓑_V are pairwise disjoint. The disjointness by itself is the lemma `BV_pairwiseDisjoint`.

5. **The case D = 1, and bounds without logarithms.** Section 4.1, after Theorem 25: "The logarithmic factors in both theorems can be removed by halving γ and applying Theorem 24 with q/2 in place of q; for D = 1 the bounds are trivial." This is the step to the last sentences of Theorems 1 and 3 ("More generally, …"); in the library it is the lemma `dataStructureBelow_wantedBelow_epsStar`. It holds for every ε < ε*, all D ≥ 1 and all N ≥ 1, and gives away half of the exponent γ, and the margin between the q of the chosen θ and the given q, to absorb the factors log² D and log D of Theorems 25 and 24, which assume D ≥ 2. In a statement about programs, one program has to serve all D, so the case D = 1 cannot be added by arithmetic to a statement about D ≥ 2. This is why the programs are proved correct in a form that includes D = 1 and has log D + 1 in place of log D (the lemmas `Corollary31.from_one` and `Corollary32.from_one`).

6. **Proof of Theorem 30, the count behind (8).** The library writes out four small steps of this count as lemmas.
   - The numbers of bands and of tiles, "at most 4N/(√K N₀)" and "at most 4N²/M", are proved with N the given size, by a slightly finer count than K₀ ≥ √K/2 gives (the lemma `Theorem30.numBands_mul_le`); the padded size has a name of its own in Lean.
   - Forming the input array of a band is within the O(10^L) operations of its encoding (`Theorem30.form_array`).
   - The O(10^L) operations for storing the K₀² subsets are within the last term of (8) (`Theorem30.subsets_absorbed`).
   - The factor m + 1 of Lemma 29 becomes the factor m of (8), because m + 1 ≤ 2m (`Theorem30.boxes_cost`).

## Section 4: running times

The theorems and corollaries have statements about programs; the docstrings of their propositions `Items.…` quote the sentences. The entries of Tables 1 and 2 are arithmetic and are among the statements for Section 4.

| The sentence | Statement about programs | Remark |
|---|---|---|
| Theorem 30, the time and space bound (8) and the query time | `wordRam_theorem_30` | See point 1 of "Section 4: differences". The expressions (8) and (9) are definitions of `PaperStatements.lean`. |
| Theorem 30, the offline form (9) | `wordRam_theorem_30_wanted` | (9) is \|W\| queries plus the preprocessing. |
| Proof of Theorem 30: storing the K₀² subsets, forming the input array of a band, its encoding, the boxes of a tile, locating (I, J), finding and enumerating the numbers of a query; "every integer we use has O(log N) bits" | — | Intermediate costs; see "Intermediate costs" below. |
| Lemma 29, second sentence, "in O(L) time and space per box", and the two costs in its proof; Section 4.3, look-ups: "reading the product at a leaf, or looking up or inserting a box, takes O(L) operations" | — | Intermediate costs. Theorem 30 about programs has the consequence of Lemma 29, the first term of (8). |
| Corollary 31 | `wordRam_corollary_31` | The bounds are in the given D, not in the padded 4^m. The parameters c, θ, ε of the statement are real; the programs contain rational parameters. |
| Proof of Corollary 31, "for smaller m the corollary again holds trivially" | — | One case of the proof of the corollary. In the programs a query then computes an inner product. |
| Corollary 32 | `wordRam_corollary_32` | The offline program does not depend on κ. The clause about the saving is arithmetic: the statement `corollary_32_saving`. |
| Theorem 24 | `wordRam_theorem_24` | As in the paper's proof, from Corollary 31, with c and θ chosen for ε and q (`exists_admissible`). |
| Theorem 25 | `wordRam_theorem_25` | See "Theorem 25" below. |
| Corollary 26, first two sentences | `wordRam_corollary_26` | — |
| Corollary 26, the bound for a set W | `wordRam_corollary_26_wanted` | The last clause, "which is O(N²/D^{0.063}) whenever \|W\| ≤ N²/√D", is arithmetic: the statement `corollary_26_W`. |
| Table 2, the caption: what an entry means for Theorems 24 and 25 | — | Each entry is an instance of `Items.Corollary_31` or `Items.Corollary_32`, at the parameters certified by the statements `table_2_query_valid`, `table_2_ninth_valid` and `table_2_density_valid`. The instantiation itself is not written out. |
| The opening of Section 4, its technique overview, and the discussion of Figure 7 in Section 4.3 | — | Comparisons for orientation; nothing depends on them. |

**Intermediate costs.** The statements for Theorem 30 have the consequences of these sentences, the bound (8) and the bound L ∑_{d=0}^{t} α_d on a query, and not the steps themselves: a program that meets these bounds need not spend O(L) steps on each box. In the library they appear as specifications of individual routines, with explicit step counts, which `docs/PROGRAMS.md` lists.

**The order of the quantifiers** can be read off the propositions `Items.…`; `docs/MACHINE.md`, Part 1, describes it.

**Theorem 25.** As in the paper's proof, the program preprocesses and asks one query for each position of W. Theorem 24 enters through the lemma `Theorem24.with_queries` and not as the statement `wordRam_theorem_24`. That statement says that two programs exist, which gives no program that another one could call.

**The proofs of Corollaries 26 and 31.** The library follows the printed steps, with one or more lemmas for each. The headers of `ThreeSumApsp/Sec4/Corollary26.lean` and `ThreeSumApsp/Sec4/Corollary31.lean` name them; the results are `Corollary26.costs`, for m ≥ 60, and `Corollary31.costs`. What the programs do for smaller m is described in `docs/MACHINE.md`, Part 3.

## Section 5 and the introduction: differences

The statements for Section 5 and the definitions that they use are in the parts "Section 5: statements" and "Section 5: definitions" of `PaperStatements.lean`. Theorems 1 to 4 are stated about programs.

1. **Sections 5.1, 5.2 and 5.4: n^μ, n^{1−μ}, n/d, n^τ and n/t₂ are treated as integers.** Sizes are written as products: n = b · d, n = b · m, n = b · t₂ (the statements `theorem_34_blocks` and `lemma_36a_min_plus_blocks`, the lemma `Corollary40.mul_apply_eq_blockOfRows_mul`). Where a running time is stated, n^μ is ⌈n^μ⌉ (`thinDim`), n^τ is ⌊n^τ⌋ (`hintSize`), and numbers of blocks are rounded up. A matrix has an integer number of rows.
2. **Section 5.2, comparison counts.** `comparisonCount` counts pairs of places in the two lists. A list may contain the same real number twice, with equal or different colors; the proof of Lemma 37 counts occurrences.
3. **Proof of Lemma 36(a), the predecessor and the successor of C[i, j].** `IsPredecessor` and `IsSuccessor` are relations, so that "there is none" can be expressed.
4. **Proof of Lemma 36, the counting problems of [CVX22].** The counting problems of the statements `lemma_36a_count` and `lemma_36b_count` follow the paper's versions; there is one pair of subsets for each call. This is the form in which the proof of Lemma 36 uses them.
5. **Lemma 37, statement.** The statement `lemma_37` is about the matrices X and Y and the integers γ₂ (`sameBlockCount`) that the proof constructs. Without its time bound the sentence is met by X = Y = 0 and γ₂ = γ; the content lies in the construction and in its cost.
6. **Proof of Lemma 37, pos(x).** In `SortedOrder`, positions count from 0, and every outcome of the sort is allowed for equal numbers: ties among numbers of row lists, or among numbers of column lists, are not specified, and any rule works.
7. **Lemma 37, time.** `Claim.Lemma_37` has log n + 1 for log n, and the statement `corollary_38_bound` adds up the same time. A formal bound has to be positive at n = 1 as well.
8. **Corollary 38.** There is a hypothesis 1 ≤ d, the standing assumption of Section 5.2 ("Throughout, d ∈ [n] is a parameter"), and the constant is "there is an n₀" (the lemma `Corollary38.exists_regime`, the statement `corollary_38_bound`). The step 4^18 n^{0.941} ≤ n needs n above about 2^610, and the step 2d²n^{1/440} + d + 1 ≤ 3d²n^{1/440} needs n ≥ 2^440 at d = 1.
9. **Proof of Theorem 35, "Las Vegas, and high probability".** Independence of the runs is a hypothesis of the statement `theorem_35_restarts`. c log₂ n restarts cost a factor log n, which is absorbed because the expected times are Õ(n^{2.9979}) and Õ(n^{1.9979}) (the statements `theorem_35_min_plus_total` and `theorem_35_three_sum_total`).
10. **Proof of Theorem 34, "Õ(n^{1−μ}) ≤ Õ(n^μ), because μ ≥ 1/2".** The statement `theorem_34_entries` is the inequality n^{1−μ} ≤ n^μ between the two powers. The lemma `conditional_theorem_34` uses n^{1−μ} (log n + 1)^e ≤ n ≤ (n^μ)² for large n; its docstring has the reason.
11. **Proof of Corollary 39, "Split the k parts into three groups".** The fixed parts come first, then three groups of consecutive parts (`fixedPart`, `groupPart`); i = 0, 1, 2, and the paper's i = 1 is 0 (`weightH`). Every split works.
12. **Corollary 39.** The time bound stands grammatically with "decide" only. `Items.Corollary_39_min_max` has the same bound for finding a clique of minimum or maximum weight. This is the reading that the last paragraph of the proof confirms.
13. **Corollary 40, the inequalities after "In each case the phases beat the conjectured bounds".** The inequalities are not stated on their own; the failure of the conjectures is the statement `wordRam_corollary_40_fail`. For Conjecture 5.12 the argument also uses τ₁ < 1, because Phase 2 (time O(n^{τ₁})) has to beat n^{ω(1,τ₁,1)−ε} as well. Section 5.4 has "constants τ, τ_i ∈ (0, 1)".
14. **Proof of Corollary 40, "General τ": "there is, after absorbing the logarithmic factors, a γ > 0 such that […] Phase 2 in O(n²/D^γ) = O(n^{2−γτ}) time".** γ is taken at most 1, and below the γ of Corollary 31. With γ ≤ 1 the program's reading of V and writing of X (n^{1+τ} entries) fit within the bound. A number below the γ of Corollary 31 absorbs the logarithmic factors of that corollary.
15. **"General τ", Conjecture 5.12: "we use the same blocks, which requires n^{τ₁} ≤ n^{ετ₂}".** `Items.Corollary_40_general_times` is stated for all n ≥ 1, and it is proved in this form (the statement `wordRam_corollary_40_general_times`). Its three bounds are those that the argument gives with D^γ and D^{1/2} in place of D^{0.063} and D^{0.437}. For the integers t₁ = ⌊n^{τ₁}⌋ and t₂ = ⌊n^{τ₂}⌋ the condition of the data structure is t₁ ≤ t₂^ε, which can fail for finitely many n although τ₁ < ε*τ₂ (n = 2^100, τ₁ = 1/100, τ₂ = log₂(316.5)/100 give t₁ = 2, t₂ = 316, and 316^{ε*} < 2). The printed argument works with an ε strictly between τ₁/τ₂ and ε*, for large n. `docs/MACHINE.md`, Part 3, says how the program avoids the condition for small t₁.
16. **Section 5.4, last paragraph: "Our proof applies to this variant as well".** The lemma `boolMul_boolMul_eq_boolMul_submatrix` proves the step behind this sentence. In [vdBSZ24, Definition 5.2] (arXiv version) M and V are n × n matrices, Phase 2 gives an n × n matrix P with at most n^τ nonzero entries, and the output is a column of MPV; each nonzero entry of P selects a column of M and a row of V, so that MPV is a product with inner dimension at most n^τ.
17. **Theorems 1 and 3, the sentences "More generally, …".** `Items.Theorem_1` and `Items.Theorem_3` assume D ≥ 1 and N ≥ 1; see point 5 of "Section 4: differences".
18. **Theorem 3** speaks of time only. In `Items.Theorem_3` the space of the preprocessing has the same bound as its time; Theorem 24 and Corollary 26, which Theorem 3 restates, say "time and space".
19. **Section 1.2, MonoConvolution, the exponent 1.4999.** The lemma `monoConvolution_exponent_lt` checks the number. With ε = 0.0008 the exponent 3/2 − ε/(8 − 2ε) is 1.49989998: below 1.4999, by 2 · 10⁻⁸.

## Section 5 and the introduction: running times

The statements for Section 5 contain no running time: they state correctness, sizes, counts and the arithmetic of the exponents. For Theorems 34 and 35 and Corollary 38 there are only the three conditional lemmas; "What is not proved" has the reasons.

| The sentence | Statement about programs | Remark |
|---|---|---|
| Theorem 1 | `wordRam_theorem_1` | The "operations on O(log N)-bit integers" are read as running time. |
| Theorem 2, integer inputs | `wordRam_theorem_2`, `wordRam_theorem_2_graphs` | Four of the five claims of `EndStatement.lean` bound the same four problems. |
| Theorem 2, real inputs; Theorem 35 | — | Real RAM, Las Vegas, expected time. Conditional: `conditional_theorem_35`. |
| Theorem 3 | `wordRam_theorem_3` | — |
| Theorem 4 | `wordRam_theorem_4` | With the times of the uMv version, which are printed in Corollary 40 only. |
| Theorem 33 | — | Proved in the paper, not here. It is the hypothesis `Claim.Theorem_33` of `conditional_theorem_34`. |
| Theorem 34 | — | Conditional: `conditional_theorem_34`. |
| Lemma 36(a) and (b) | — | Real RAM with an oracle for comparison counts. They are the hypotheses `Claim.Lemma_36a` and `Claim.Lemma_36b` of `conditional_theorem_35`. |
| Lemma 37 | — | Real RAM, deterministic. It is the hypothesis `Claim.Lemma_37` of `conditional_corollary_38`. |
| Corollary 38 | — | Real RAM, deterministic. Conditional: `conditional_corollary_38`. |
| Corollary 39, weight zero | `wordRam_corollary_39_zero`, `endStatement_corollary_39_zeroWeight` | — |
| Corollary 39, minimum and maximum weight | `wordRam_corollary_39_min_max` | — |
| Corollary 40, first paragraph | `wordRam_corollary_40_times`; "fail" is `wordRam_corollary_40_fail` | The input arrives in phases. |
| Corollary 40, second paragraph, and "General τ" | `wordRam_corollary_40_general_times`, `wordRam_corollary_40_fail` | — |
| Section 1.2, the obvious algorithm that waits: "compute one matrix–vector product in O(nt) time" | — | The lemma `not_achievesVHinted` is a lower bound n for Phase 3 of v-hinted Mv. |

The running times that the paper only recalls or cites are not stated: Zwick's algorithm in Sections 1 and 5.1, the bounds for All-Edges Sparse Triangle in Section 1, and the two comparisons after Theorem 1 in Section 1.1. The sentence of Section 1.1 on counting triangles restates Corollary 16 and Theorem 25.

## Section 5: cited results

| Citation | Used in | Here | Lean names |
|---|---|---|---|
| [CVX21, Theorem 3.1], [Zwi02]: Zwick's algorithm as a reduction | Theorems 33 and 34 | Theorem 33 is its deterministic form, which the paper proves and which is not proved here; it is a hypothesis of `conditional_theorem_34` | `Claim.Theorem_33` |
| [Zwi02, Sections 6 and 7; Lemma 3.3], [YZ05a, Section 8], [Sei95], [AGMN92], [GM93], [AN96], [Lov75], [Chv79]: bridging sets, (min,+)-products with witnesses, greedy hitting sets | Section 5.1 and the proof of Theorem 33 | left out, with the proof | — |
| [ADV+25]: μ < 0.5275, for the number n^{2.5275} of Section 1 only | Sections 1 and 5.1 | left out | — |
| no citation ("because of the input and output sizes"): ω(1,μ,1) ≥ 2; ω(1,1,τ) = ω(1,τ,1) ≥ 2; ω(τ₂,τ₁,1) ≥ 1 + τ₂ | Section 5.1; Corollary 40 | For Corollary 40, explicit hypotheses on free real numbers ω, ω₂ ≥ 2 and ω₃ ≥ 1 + τ₂. In `conditional_theorem_34`, μ is a real parameter with 1/2 ≤ μ ≤ 1, and ω(1,μ,1) does not occur. | `Items.Corollary_40_fail` |
| [CVX22, Section 3.2, Problem 3.2; Problem 4.1]: the two problems | Lemma 36(a) | defined | `IsPredecessor`, `IsSuccessor`; statement `lemma_36a_count` |
| [CVX22, Lemmas 3.4 and 4.2]: one pair of blocks reduces to counting calls | Lemma 36(a) | part of a hypothesis of `conditional_theorem_35`. What the paper adds (a counting call is d comparison counts, sizes of lists and pair sets, encodings of Exact Triangle and of the (min,+)-product) is proved. | `Claim.Lemma_36a`; the statements `lemma_36a_…` |
| [CVX22, Section 3.3, Lemmas 3.9 and 4.6; Problem 4.5]: 3SUM reduces to counting calls | Lemma 36(b) | The problem is defined. The reduction is part of a hypothesis of `conditional_theorem_35`. The translation into comparison counts is proved. | `Claim.Lemma_36b`; statements `lemma_36b_count`, `lemma_36b_lists` |
| no citation: APSP is ⌈log₂ n⌉ (min,+)-products, by repeated squaring | Lemma 36(a) | proved for every linearly ordered commutative group of weights, hence for real weights | statement `theorem_21b_repeated_squaring` |
| [VW13, Theorem 3.3]: "finding a maximum weight triangle costs O(log² n) times as much" | Corollary 39 | proved for programs, over an arbitrary solver of Exact Triangle, which only decides; the NOTE at the claim says how the factor is read | `Claim.VW13_Theorem_3_3_max`, which the lemma `minMaxClique_of_theorem_19_VW13` takes as a hypothesis |
| [NP85]: folding a k-clique into a triangle | Corollary 39 | an attribution; the construction is proved in full | `Corollary39.bijective_fixedOf_groupOf`, `Corollary39.S_graphH_eq_cliqueWeight`, `Corollary39.hasZeroClique_iff`, `Corollary39.isMaxWeightClique_iff`, `Corollary39.isMinWeightClique_iff` |
| [vdBNS19, Definitions 5.1, 5.6, 5.11; Conjectures 5.2, 5.7, 5.12] | Section 5.4 | defined; see below | `vHintedOutput`, `MvHintedOutput`, `uMvHintedOutput`; `AchievesVHinted`, `AchievesMvHinted`, `AchievesUMvHinted` |
| [vdBNS19, Theorems 5.3, 5.8; Corollaries 5.4, 5.5, 5.9, 5.10, 5.15, 5.16], [San04], [HLS24], [vdBSZ24]: which published lower bounds rely on the conjectures in the refuted regime | Section 5.4 | left out, except for the step for the variant of [vdBSZ24] | `boolMul_boolMul_eq_boolMul_submatrix` |
| [Mat91]: the dominance-product technique | Lemma 37 | an attribution; the construction of Lemma 37 is proved correct, and its running time is a hypothesis of `conditional_corollary_38` | statement `lemma_37`; `Claim.Lemma_37` |
| [Fre76]: Fredman's trick | Section 5.2 | proved | `fredman_trick`, `fredman_trick_le` |

**The conjectures of [vdBNS19].** They are defined relative to a parameter that says which exponents are achieved; on the machine the parameter is given by the three definitions `Achieves…`. In [vdBNS19] the bounds are worded as lower bounds Ω(n^{x−ε}) on the time of a phase. Here a conjecture says that no algorithm has time O(n^{x−ε}) in every listed phase. The original wording implies this (apply it with ε/2), so a refutation of the form used here refutes the original.

## The conditional lemmas: what is assumed

The library has three conditional lemmas. Each is an implication between running-time claims, for an arbitrary interpretation `M : ConditionalTimes.TimeModel` of sentences such as "is solved by a deterministic algorithm in time T" or "is solved by a Las Vegas algorithm in expected time T". "Deterministic", "Las Vegas", "expected time" and "real RAM" belong to the intended meaning of `M` and are not modeled. In this section `Claim.…` and `Closure.…` stand for `ConditionalTimes.Claim.…` and `ConditionalTimes.Closure.…`, definitions in `ThreeSumApsp/ConditionalTimes/Definitions.lean`. A *transfer claim* has the form "if B is solved in time T, then A is solved in time extra + calls · T". The header of that file says how the claims are written, and their NOTEs say where they depart from the printed text.

**`conditional_theorem_34`**, with the conclusion `Claim.Theorem_34 M μ`:

| Hypothesis | Kind | The paper |
|---|---|---|
| `Claim.MinPlusInPolylog M (3 − 0.00175/3)` | time sentence of the paper | Theorem 22, with ε′ = 0.00175 from Theorem 19: the bound Õ(n^{3−ε′/3}) for the (min,+)-product, for entries up to n^ν for every constant ν. About programs this sentence is `wordRam_theorem_22_second`. |
| `Claim.RectMinPlusFromSquare M` | transfer claim that the paper argues | Proof of Theorem 34: an n × m by m × n (min,+)-product is ⌈n/m⌉² products of m × m matrices. |
| `Closure.RelaxMinPlusBound M` | closure property | Not in the paper: an algorithm for entries up to f(n, u) ≥ u can be run on entries up to u. |
| `Claim.Theorem_33 M μ` | theorem of the paper, not proved here | Theorem 33. The conclusion of `conditional_theorem_34` is literally the conclusion of this hypothesis, so the lemma checks that the premise of Theorem 33 holds for some ε₁ > 0. |
| 1/2 ≤ μ ≤ 1 | — | It holds for the paper's μ (Section 5.1). |

**`conditional_corollary_38`**, with the conclusion `Claim.Corollary_38 M`:

| Hypothesis | Kind | The paper |
|---|---|---|
| `Claim.Corollary_26_wanted M` | time sentence of the paper | Corollary 26, last sentence. About programs this sentence is `wordRam_corollary_26_wanted`. |
| `Claim.Lemma_37 M`, with s = ⌈n^{1−1/440}/d⌉ and D* = ⌈3d²n^{1/440}⌉ | transfer claim that the paper argues | Lemma 37, with the padding of Corollary 38: comparison counts are obtained from a thin matrix product, plus O(nD* + (nds + ds² + p)(log n + 1)) time. |

**`conditional_theorem_35`**, with the conclusion `Claim.Theorem_35 M`:

| Hypothesis | Kind | The paper |
|---|---|---|
| `Claim.Corollary_38 M` | the conclusion of `conditional_corollary_38` | Corollary 38 |
| `Claim.Lemma_36a M`, for the (min,+)-product, for APSP and for Exact Triangle, and `Claim.Lemma_36b M`, all with d = ⌊n^{1/40}⌋ | cited in part | Lemma 36: numbers of counting calls, subtractions and further time; expected time. See "Section 5: cited results". |
| `Claim.Restart M` | transfer claim that the paper argues | Proof of Theorem 35, "Las Vegas, and high probability": expected time T gives time O((c log₂ n + 1)(T + 1)) with probability 1 − n^{−c}. The factor log n and the "+ 1" are absorbed by `ConditionalTimes.lasVegasIn_and_whpIn_of_polylog`. |

No link from the two statements about programs to the two time sentences about `M` is stated or checked: `M` is arbitrary, and these two hypotheses are assumed like all the others. What stands behind the transfer claims (correctness, numbers of instances, sizes, magnitudes) is stated without conditions among the statements for Section 5.

**Deductions between running-time claims that the conditional lemmas do not cover.** Inside the proof of Lemma 36, the adding-up over the n/d pairs of blocks is part of `Claim.Lemma_36a`. Section 5.1, "We refute this in Theorem 34", is not stated. The deductions of Section 4.4 are proved for programs, inside the proofs of the statements about programs. For those of Section 3 and Corollary 39 see "The claims of the library" in "Section 3: differences".

## Every NOTE

This list is written by `scripts/index.py`. It has every paragraph of a comment that begins with the word NOTE: first those of the statements and of the trusted definitions, then those of the library. A NOTE on a statement is listed once, at the statement.

<!-- notes:begin (generated by scripts/index.py) -->

**`Challenge/EndStatement.lean`**

* the comment "The five claims of EndStatement.lean". NOTE. On the reading of `EndStatement.lean`; some of these points are also in its comments:
  * The machine is generous on three points, none of which changes an exponent. Every cell other than cell 0 and the cells of the input, with a positive or a negative name, holds 0 at the start, and no space is charged. The finitely many cells that a program names in its text are arbitrary integers and need not be addressable by a word. The constant `b` is chosen after `κ`.
  * "O(log n)-bit words" is read as: the word size `b (⌊log₂ n⌋ + 1)` and every larger one, where ⌊log₂ 0⌋ is 0.
  * The answer has to be right at every size `n`, 0 included; the bound `T(n) = O(n^r)` binds from `n = 2` on.
  * `κ` ranges over the natural numbers, which covers every real constant ν ≥ 0, as n^ν ≤ n^⌈ν⌉. `κ = 0` is included, where Theorem 19 and Corollary 39 have ν ≥ 1.
  * The bound `n^κ` is asked of every number of the input (the `n` in cell 0 is not one of them), also of the entries 0 and 1 of APSP's matrix of edges and of the blocks of the clique problem that do not count.
  * How an instance is written into the cells is fixed in `EndStatement.lean` and not in the paper: `n` in cell 0, matrices row by row, APSP's matrix of edges and its two output cells for each pair, all `k²` blocks of the clique problem.
  * In APSP an edge may be missing, and where there is no path the cell for the distance is free.
  * Exact Triangle has a complete tripartite graph, as in Section 3.2.
  * In 3SUM the three numbers stand at three different positions of the input.
  * Theorem 22 prints two rounded exponents for each of its problems, one by the route through Theorem 5 and one by the route through Corollary 26. The claims on these three problems have the exponents of the route through Corollary 26, which are the smaller ones: 1.9992 for 3SUM (the other is 1.99923), and 2.99942 for the (min,+)-product and for APSP (the other is 2.99949). The larger exponents are stated in `Items.Theorem_22_first`. Theorem 2 prints 2.9995 for the (min,+)-product and for APSP.
  * The `ε_T` in the exponents of the claims on Exact Triangle and on `k`-Clique belongs to the route through Corollary 26 too: for this route Theorem 19 prints "O(n^{3−ε'} log n) ≤ O(n^{3−ε_T})".
  * Corollary 39 speaks also of a `k`-clique of minimum, or of maximum, total edge weight; this is stated in `Items.Corollary_39_min_max`.

**`PaperStatements.lean`**

* `Lemma_10`. NOTE. The hypothesis `0 < L ∨ U.Nonempty` of the second claim is not in the paper. It excludes only the case `L = 0`, `U = ∅`, in which the root is itself a leaf, so that the call at the root visits it, while `Leaves(∅)` is empty. In the paper `L ≥ m ≥ 1`, and `Pruned` is run only on nonempty sets (Section 2.4.4).

* `Sec2_card_outStr_of_leaf`. NOTE. `m ≤ L` is left implicit in the paper.

* `Eq_5_ratio`. NOTE. The paper prints the equality under `L = 19m` in (5) and under `L ≥ 10m` in (7); here it is stated for every `L ≥ m`.

* `ThreeSum`. NOTE. We read "three of them" as three numbers at three different positions of the input.

* `IsPowLittleO`. NOTE. We read it as an upper bound, as the paper uses it for times and for numbers and sizes of instances: there is a sequence `ε(n) → 0` with `|f(n)| ≤ n^{a+ε(n)}` for all large `n`.

* `Theorem_17_write_cost`. NOTE.
  * `g ≤ √D` is not needed.
  * `p` is any prime of the range, selected or not.

* `Theorem_17`. NOTE. The paper does not say that `D` is an integer; here it is a natural number, as in every use of the theorem, and the bound on the number of chunks uses this (see the library's lemma `TriangleInstance.totalChunks_le`).

* `Theorem_21b_entries_bounded`. NOTE. A missing edge has the weight `⊤` here, while the (min,+)-product of Theorem 21(b) is on integer matrices with entries of absolute value at most `U` (`IsMinPlusProduct`). Nothing is stated here about replacing `⊤` by a large number.

* `Theorem_21b_log_factors`. NOTE.
  * Both halves are stated for `U = n^{κ+1}`, the first one too.
  * The condition that T(s)/s is nondecreasing, and the like condition of [VW18, Theorem 4.2], do not occur.

* `Theorem_21a_compose`. NOTE. The hypothesis on `E₂` is what the time `n^{3/2+o(1)}` of Theorem 21(a) asks of the second reduction.

* `Theorem_21a_threeSum_to_convolution`. NOTE.
  * `κ` is a natural number.
  * Theorem 5.1 of [CH20] is a statement about running times, for 3SUM on three sets and Convolution-3SUM on three arrays. The reduction stated here, with its count of instances, their length and the Õ(n^{3/2}), follows the proof of that theorem, and passes to `n` numbers and to one array by elementary devices; see `docs/REMARKS.md`, "Section 3: cited results".

* `Corollary_26_W`. NOTE. The paper states no lower bound on `D`; `D ≥ 1` is assumed, as in `Items.Corollary_26`.

* `Lists`. NOTE. The color belongs to the entry (the place in the list), not to the real number: the same number may occur twice in a list, and the two occurrences are counted separately.

* `SortedOrder`. NOTE. Positions are counted from 0 within each color, so that "blk(x) := ⌊pos(x)/s⌋" gives "blocks of s consecutive positions".

* `Corollary_38_bound`. NOTE. The time of Lemma 37 is taken as in the library's `Claim.Lemma_37`, so that this is the arithmetic of `conditional_corollary_38`: it has `log n + 1` in place of `log n`, which makes the statement stronger.

* the comment "The word RAM: problems". NOTE. Eight notions are defined twice: in `EndStatement.lean`, and with Mathlib for the statements on the reductions and about programs. For each of them a statement, named in brackets, says that the two definitions agree (a further form of `O(n^a)`, the bound `Within` on the steps of a phase, is not compared):
  * "a program solves a problem": there `Problem`, `Problem.SolvedBy` and the word sizes of `Problem.SolvedInTime`, for one size `n`; here `Problem`, `Admissible`, `output` and `Solves`, for several sizes (`Agreement_solves`);
  * `O(n^r)`: there `BigO`, for a rational exponent and from `n = 2` on; in Section 3 `IsBigOPow`, for a real exponent and all large `n` (`Agreement_bigO`, for `r ≥ 0`);
  * "solved in time": there `Problem.SolvedInTime` and `BigO`, with a rational exponent and a bound `T(n)` that is `O(n^r)` from `n = 2` on; here `SolvesWithin`, `SolvedInTimeAt` and `SolvedInTime`, with a real exponent and the bound `C (n^a (log n)^e + 1)` at every size (`Agreement_solvedInTime`, for a rational exponent `r ≥ 0` and `e = 0`); both are stated through `Problem.SolvedBy`;
  * Exact Triangle: `EndStatement.ExactTriangle` and `TriangleInstance.HasZeroTriangle` (`Agreement_exactTriangle`);
  * the (min,+)-product: `EndStatement.MinPlusProduct` and `IsMinPlusProduct` (`Agreement_minPlusProduct`);
  * APSP: `EndStatement.Path` and `EndStatement.APSP`, where a missing edge is `none`, and `walkWeight`, `NoNegativeCycle` and `IsDistanceMatrix`, where it is `⊤` (`Agreement_apsp_noNegativeCycle`, `Agreement_apsp_output`);
  * a matrix written row by row: `EndStatement.rowByRow` and `rowMajor` (`Agreement_rowByRow`);
  * the weight of a `k`-clique: the sum in `EndStatement.ZeroWeightKClique` and `cliqueWeight` (`Agreement_cliqueWeight`).

* the comment "The word RAM: problems". NOTE. On four points the machine is generous; none of them changes an exponent:
  * Every cell outside the input, with a positive or a negative name, holds 0 at the start, and `Solves`, `SolvesWithin` and `RunsPhases` charge no space, so a table that is addressed directly by a number costs nothing to set up (on a machine without this, lazy initialisation costs a constant factor).
  * The finitely many cells that a program names in its text need not be addressable by a word.
  * The slope `b` of the word size is chosen after the exponent `κ` of the magnitude of the numbers.
  * The inputs of phases and the queries arrive at no cost.

* `SolvesWithin`. NOTE. As in `EndStatement.Problem.SolvedInTime`, the bound speaks of every number of the input list. Where the input contains an adjacency matrix, its entries 1 count too; `n^κ` is at least 1 as soon as there is a vertex.

* `SolvedInTime`. NOTE. `κ` is the paper's ν. Where the paper has ν ≥ 1 (Theorem 19, Corollary 39), `κ = 0` is included here.

* `SolvedInPolylogTime`. NOTE. The exponent of the logarithm may depend on `κ` too: this is the weaker reading of the Õ of Theorem 22.

* `ThinInstance`. NOTE. The paper does not say how a set is given. Here it is a list without repetitions, in any order.

* `IsDataStructure`. NOTE. The paper says "time and space" and does not define space. Here space is the extent of the memory in which the preprocessing leaves the data structure, not the number of cells written, which is at most the time anyway; a structure that is scattered over a large range of addresses does not count as small. Cells that the preprocessing restores, and cells that the queries write, are not constrained.

* `ThinInstance.lop`. NOTE. Definition 13 has "a middle part M of at most D vertices"; here the middle part has exactly `D` vertices, the columns of `X`. A smaller middle part is written with zero columns of `X` and zero rows of `Y`: vertices without edges, which lie in no triangle.

* the comment "Zero-Weight, Min-Weight and Max-Weight `k`-Clique (Corollary 39)". NOTE. All `k²` blocks are input, but only the blocks with `p < q` count; the others may hold anything within the bound on the numbers of the input. The paper does not fix a layout.

* `MinKClique`. NOTE. The parts have at least one vertex: at `n = 0` there is no clique to output.

* `hintSize`. NOTE. The paper treats `n^τ` as an integer; here it is rounded down, which keeps what the proof of Corollary 40 needs, for `n ≥ 1`: `t ≥ 1` if `τ ≥ 0`, and `t^18 ≤ n` if `0 ≤ τ ≤ 1/18`. The number `t` is given to the programs in Phase 1, after `n`; they need not compute it.

* `Corollary_16`. NOTE. The paper states no lower bound on `D`; `D ≥ 1` is assumed, as in `Corollary_26` below.

* `Corollary_26`. NOTE. The paper states no lower bound on `D`; `D ≥ 1` is assumed (for `D = 0` the bound `O(D^{0.437})` would be 0 steps).

* `DataStructureBelow`. NOTE. The paper states no lower bound on `D` and `N` here, and speaks of time only; `D ≥ 1` and `N ≥ 1` are assumed, and the space is bounded like the time. Theorem 24 has logarithmic factors and assumes `D ≥ 2`; on the step from there Section 4.1 says: "The logarithmic factors in both theorems can be removed by halving γ and applying Theorem 24 with q/2 in place of q; for D = 1 the bounds are trivial."

* `WantedBelow`. NOTE. The paper states no lower bound on `D` and `N` here; `D ≥ 1` and `N ≥ 1` are assumed. On the case `D = 1`, which Theorem 25 and Corollary 32 exclude, see the NOTE at `DataStructureBelow`.

* `Corollary_40_times`. NOTE. `τ₂ < 1` is assumed: it is the standing assumption of Section 5.4 ("for constants τ, τ_i ∈ (0,1)"). The words "only stores I" are read as `O(n^{τ₁})` time.

* `Corollary_40_general_times`. NOTE. For Conjecture 5.12 ("we use the same blocks") the three bounds are those that the argument gives, with `D^γ` and `D^{1/2}` in place of `D^{0.063}` and `D^{0.437}`. On `τ₂ < 1` see the NOTE at `Corollary_40_times`.

* `Corollary_40_fail`. NOTE. `τ₂ < 1` is assumed; see the NOTE at `Corollary_40_times`.

* `Theorem_1`. NOTE. The paper states no lower bound on `D`; `D ≥ 1` is assumed, and in the last sentence also `N ≥ 1` (see `WantedBelow`).

* `Theorem_2`. NOTE. Here Exact Triangle has the tripartite form of Section 3.2, with `n` vertices per part; for `n`-vertex graphs see `Theorem_2_graphs`.

* `Theorem_3`. NOTE. The departures are those of the two definitions: `D ≥ 1` in the first part; `D ≥ 1` and `N ≥ 1` in the second; and in both the space is bounded like the time, while the theorem speaks of time only.

* `Theorem_4`. NOTE. For the uMv version `τ₂ < 1` is assumed; see the NOTE at `Corollary_40_times`.

**`ThreeSumApsp/ConditionalTimes/Definitions.lean`**

* `rectMinPlus`. NOTE. Theorem 33 says "can be computed" and adds: "If the algorithm for the product is deterministic, then so is the algorithm for APSP." Only this case is expressed. The algorithm that the proof of Theorem 34 supplies is deterministic.

* `apsp`. NOTE. Theorem 33 says "can be solved" and adds: "If the algorithm for the product is deterministic, then so is the algorithm for APSP." Only this case is expressed. Theorem 34 says "by a deterministic algorithm".

* `RelaxMinPlusBound`. NOTE. This property is not in the paper. It is needed because `Claim.MinPlusInPolylog` bounds the time only at the bound `n^κ` on the entries (the paper's n^ν), and not at smaller bounds.

* `Corollary_26_wanted`. NOTE. The paper states no lower bound on `D`; `D ≥ 1` is assumed.

* `MinPlusInPolylog`. NOTE. `κ ≥ 0` is assumed.

* `RectMinPlusFromSquare`. NOTE. The paper treats n^μ and n^{1-μ} as integers. Here an `n × m` by `m × n` product has `⌈n/m⌉²` pairs of blocks, of which the last may have to be padded, and the claim also allows `C₀ m² (1 + log u)` for copying a pair of blocks and its product, which does not change the bound of the proof.

* `Theorem_33`. NOTE. Both algorithms are deterministic here: this is the case of the last sentence, and the only one that is expressed. "Õ(n^{1-μ})" is read as n^{1-μ}(log n + 1)^e for every natural number e, which makes the premise stronger and so the claim weaker; the algorithm may depend on e. "polylog n" is read as (log n + 1)^c for every natural number c, which covers (log n)^c for every constant c.

* `Theorem_34`. NOTE. (log n)^c is read as (log n + 1)^c with a natural number c, as in `Theorem_33`.

* `Lemma_37`. NOTE. `log n` is written `log n + 1`, and nD'' is written `n * Din`, as in the proof of Corollary 38. `1 ≤ d ≤ n` is the standing assumption of Section 5.2 ("Throughout, d ∈ [n] is a parameter"). The last two sentences of the lemma, on the operations on real numbers and on ≤, belong to the intended meaning of `M.comparisonCounts`. The time to compute `s` and `Din` is not charged separately; the statements use the claim only for `s = blockLen` and `Din = Dstar`. `M.comparisonCounts T'` speaks of an algorithm that is correct on every input, also where the hypotheses on `s` and `Din` fail.

* `Corollary_38`. NOTE. `d ≥ 1` is the standing assumption of Section 5.2 ("Throughout, d ∈ [n] is a parameter"). As in `Lemma_37`, `M.comparisonCounts T` speaks of an algorithm that is correct on every input, also where the hypotheses on `n` and `d` fail.

* `Lemma_36a`. NOTE. The clause "with at most one number of each color in a list" (left out in the quotation) is dropped: `M.comparisonCounts` speaks of arbitrary lists, so the claim is weaker without it. `calls`, `further` and `C₀` may depend on the function `d`, while the bounds of the paper are uniform in d; this too makes the claim weaker. The statements use it only for `d = listLen`, which is ⌊n^{1/40}⌋. The type does not exclude `prob = threeSum`. The last two sentences of Lemma 36, on ≤ and on the operations on real numbers, belong to the intended meaning of `M.comparisonCounts` and `M.lasVegas`; so also in `Lemma_36b`.

* `Lemma_36b`. NOTE. That the numbers are "all of the same color" is not used: the comparison counts are answered by an algorithm for arbitrary colors. `Num`, `further`, `C₀` and `K` may depend on the function `d`, as in `Lemma_36a`.

* `Restart`. NOTE. The number of runs is written `c log₂ n + 1` and the length of a run `T n + 1`, so that the bound does not vanish where `c log₂ n` or `T n` is zero. The claim is made for every `T`, whether the algorithm knows it or not; for a `T` that it does not know, a variant serves: interleave the runs step by step and stop with the first that ends. `c ≥ 0` is assumed.

* `LasVegasWhpIn`. NOTE. The algorithm may depend on `c`, and it need not be the algorithm of `LasVegasIn`: the proof of Theorem 35 obtains it from that algorithm by restarting. `c ≥ 0` is assumed.

* `Theorem_35`. NOTE. The opening clause, on the real RAM and its operations, is not expressed by the proposition; it is part of the intended meaning of `M.lasVegas` and `M.lasVegasWhp`. The two halves speak of separate algorithms; see `LasVegasWhpIn`.

**`ThreeSumApsp/RunningTimes/Sec3/Theorem22.lean`**

* `Theorem22.threeSum_polylog`. NOTE. Theorem 22 has `n^{o(1)}` here. The programs give `(log n)^{O(1)}`, and the printed form follows (`wordRam_theorem_22_threeSum`).

**`ThreeSumApsp/RunningTimes/Sec4/Corollary31_32.lean`**

* the comment "The form that includes `D = 1`". NOTE. This form is not in the paper. The last sentences of Theorems 1 and 3 have no lower bound on `D`, while Theorems 24 and 25 and Corollaries 31 and 32 assume `D ≥ 2`; Section 4.1 adds that "for D = 1 the bounds are trivial". In a statement about programs, one program has to serve all `D`, so the case `D = 1` cannot be added by arithmetic to a statement about `D ≥ 2`. Here `log D + 1` stands in place of `log D`, which is 0 at `D = 1`.

**`ThreeSumApsp/Sec2/Lemma10.lean`**

* `Pruned.called_iff`. NOTE. As printed this fails for the root when `U = ∅` (the root is always called). The hypothesis `hk` excludes only that case. `hkL` says that `τ` is a vertex of the recursion tree, whose depth is at most `L` (Section 2.3.1); the type `Vertex k` exists for every `k`.

**`ThreeSumApsp/Sec2/Lemma11.lean`**

* `sum_alpha_small_orders_lt`. NOTE. The strict inequality needs `m ≥ 1`, which is fixed in Section 2.3.3; for `m = 0` both ends are 1.

**`ThreeSumApsp/Sec2/Orders.lean`**

* `card_filter_order_eq`. NOTE. `d ≤ m` and `m ≤ L` are left implicit in the paper.

**`ThreeSumApsp/Sec2/Theorem5/Equation6.lean`**

* `K_le_pow`. NOTE. The printed bound divides by `m`. In Lean a quotient by 0 is 0 and `0^0 = 1`, so for `m = 0` both sides are 1 and no hypothesis `m ≥ 1` is needed.

**`ThreeSumApsp/Sec2/Theorem5/WordSize.lean`**

* `abs_bandArrayL_le`. NOTE. `0 ≤ A` is needed only when `N = 0`.

* `abs_bandArrayR_le`. NOTE. `0 ≤ B` is needed only when `N = 0`.

**`ThreeSumApsp/Sec2/Tiling.lean`**

* `le_padN`. NOTE. `m ≤ L` is left implicit in the paper. For `m > L` there is no subset of size `m` and `K₀ = 0`.

* `padN_lt_add_bandSize`. NOTE. `m ≤ L` is left implicit in the paper.

* `nonempty_layout`. NOTE. `m ≤ L` is left implicit in the paper; it is a field of `Layout`.

* `bandOf_lt_numBands`. NOTE. `m ≤ L` is left implicit in the paper.

**`ThreeSumApsp/Sec3/Corollary15_16.lean`**

* `Corollary16.bound_le_of_card_le`. NOTE. Corollary 16 states no lower bound on `D`; this computation is stated for `D ≥ 1`.

**`ThreeSumApsp/Sec3/Parameters.lean`**

* `GoodTime`. NOTE. We also ask that `T(s) ≥ s² (1 + log u)`, which is an upper bound for the time to write down the `3s²` weights of an instance. The paper does not say this, but its bound `O(n² T(n^{1/3}) log² U)` leaves no room for writing down the instances otherwise. The condition is a hypothesis on the running times that are fed into Theorem 21(b), so it makes the claims that use it weaker, not stronger.

**`ThreeSumApsp/Sec3/Theorem17/Hashing.lean`**

* `exists_le_card_primesInRange`. NOTE. The proof of Theorem 17 needs this for every `D ≥ 16`, not only for large `D`, and so it is stated. It follows from a counting form of Bertrand's postulate; the prime number theorem is not needed.

**`ThreeSumApsp/Sec3/Theorem17/Instances.lean`**

* `totalChunks_le`. NOTE. A chunk holds a whole number of pairs, at most `⌊n²/√D⌋`, so the count is at most `p + (n² − p)/⌊n²/√D⌋`, and the second term can exceed `√D` slightly. The printed bound is still true, because the count is an integer, `D` is an integer and `D ≤ n` (`sq_lt_mul_queryCap_add`).

**`ThreeSumApsp/Sec3/Theorem19.lean`**

* the comment "Theorem 19 and Remark 20: Exact Triangle in truly subcubic time (Section 3.3)". NOTE. "Assume n is larger than a constant depending on ν": the two choices of `D` below are stated for `n ≥ 16^18`, which makes `D ≥ 16`.

**`ThreeSumApsp/Sec3/TripartiteOfGraph.lean`**

* `hasZeroTriangle_tripartiteOfGraph_iff`. NOTE. An integer `U`, a bound on the absolute values of the weights of the edges of `G`, stands for the paper's `n^ν`, which need not be an integer.

* `weightsBoundedBy_tripartiteOfGraph`. NOTE. Stated for a natural number `κ`, so that `3n^κ + 1` is an integer, and for `n ≥ 4`: for `n ≤ 3` the weight `3n^κ + 1` exceeds `n^{κ+1}`.

**`ThreeSumApsp/TimeClaims/Sec3/Definitions.lean`**

* `VW13_Theorem_4_3`. NOTE. The time `E` of this reduction is part of the claim, because the time of Theorem 21(a) needs `E(N) = N^{3/2+o(1)}`.

* `Corollary_26_wanted`. NOTE. The paper states no lower bound on `D`; `D ≥ 1` is assumed.

* `Corollary_16`. NOTE. The paper states no lower bound on `D`; `D ≥ 1` is assumed, as in `Claim.Corollary_26_wanted`.

* `ExactTriangleUniform`. NOTE. This claim is not in the paper. It is what our rendering of "Plug Theorem 19 into Theorem 21" needs: Theorem 21(b) asks for a running time `T(s)`, with `T(s)/s` nondecreasing, at a fixed bound on the weights and for all `s`, and Theorem 21(a) produces instances whose weights are bounded in terms of `n`, not of their own size; Theorem 19 bounds the time only for weights at most `s^κ` and for large `s`. `exactTriangleUniform_of_explicit` derives it from `Claim.Theorem_19_explicit`, brute force and the two closure properties; this works because the bound in `Claim.Theorem_17` is polynomial in `κ` with a constant that does not depend on `κ`.

* `Theorem_21b_apsp`. NOTE. The printed hypothesis speaks of weights "at most cU" without saying what `U` is for APSP; here it is `U = n^{κ+1}`, with `κ` for ν, which bounds the entries during the repeated squaring.

**`ThreeSumApsp/TimeClaims/Sec3/Theorem19.lean`**

* `exactTriangleUniform_of_explicit`. NOTE. This step is not in the paper; see `Claim.ExactTriangleUniform` for why our rendering of "Plug Theorem 19 into Theorem 21" needs it.

**`ThreeSumApsp/TimeClaims/Sec5/Definitions.lean`**

* `VW13_Theorem_3_3_max`. NOTE. The paper's factor log² n is read as (log U + log s + 1)²: log² U is the number of decisions that give the weight of a maximum weight triangle, and a triangle of exactly that weight is then found by O(log s) more decisions on instances with the same s, in which vertices are switched off by a large weight. The term `s² (1 + log U)` allows for writing down an instance.

<!-- notes:end -->
