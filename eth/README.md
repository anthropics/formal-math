# A 2<sup>o(*n*)</sup> Time Algorithm for 3-SAT

A deterministic algorithm solves 3-SAT on *n* variables in time 2<sup>o(*n*)</sup>, which refutes the Exponential Time Hypothesis (ETH). The algorithm in fact solves the harder problem #3-SAT, counting the satisfying assignments, in time 2<sup>O(*n* log log *n* / √log *n*)</sup>.

The result is purely asymptotic and says nothing about solving formulas in practice.

The result was discovered by an internal research Claude model. This folder holds the paper and its Lean 4 formalization, which was written by AI models.

Research artifact. Not maintained and not accepting contributions.

## Paper

**[paper.pdf](paper.pdf)**: *A 2<sup>o(n)</sup> Time Algorithm for 3-SAT*, by Claude (Anthropic). [Hexagon](https://hexagonmath.org/) link to appear.

## Lean proof

**1. Read the statement.** One commented file, [`MainResults.lean`](MainResults.lean), states what is proved, on Mathlib's Turing machines:

- that ETH is false (`ETHIsFalse`)
- the paper's Theorem 1 (Main Theorem), the counting algorithm for *k*-CNF formulas with its time bound (`MainTheorem`)

The file contains no proofs and imports nothing but Mathlib. Lean checks the proofs, but no machine checks that this file says what the paper says; the file is kept short so that a reader can check this. Appendix E of the paper prints it and lists how it differs from the printed statements. [`proof/PaperIndex.lean`](proof/PaperIndex.lean) lists, for each numbered statement of the paper, its Lean counterpart, and says where the Lean form differs.

**2. Check the proofs.** With [elan](https://github.com/leanprover/elan) installed, in this folder (`cd eth`):

```sh
lake exe cache get
lake build
lake env lean scripts/PrintAxioms.lean
```

The first command downloads Mathlib already compiled. The build took about 8 minutes on 24 virtual CPUs, and its largest process used about 7 GB of memory. It prints two warnings `` declaration uses `sorry` ``, both from [`Challenge.lean`](Challenge.lean), which states the two theorems without proofs for the fuller check below. The last command should print:

```
'MainResults.ethIsFalse' depends on axioms: [propext, Classical.choice, Quot.sound]
'MainResults.mainTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Those are Lean's three standard axioms. Lean `v4.33.1` and the matching Mathlib, also `v4.33.1`, are pinned.

The fuller check is the one this repository's CI runs, `bash ../.github/scripts/comparator-check.sh` (Linux): [Comparator](https://github.com/leanprover/comparator) also compares the theorems' statements with [`Challenge.lean`](Challenge.lean) and re-checks the proofs with a second, independently written kernel, `nanoda`.

## The key idea, in condensed form interpretable by AI models

Claude Opus 5.5 at high effort can rederive the refutation of ETH from the following condensed description:

> The exponential time hypothesis is false!
>
> Let 2^{e(K)·K²λ}·poly(λ) be the time to contract tensor networks on K_K with λ bits per edge and arbitrary node tensors. Then e(9K^16) ≤ 0.9·e(K) + O(1/K). Put the nodes on a grid: the two diagonals of each rectangle form a swap. Per bit, SWAP = I − 2·singlet; grouping by the number of singlets gives λ+1 operators with (row rank)·(column rank) ≤ 12^λ. For each choice of operators, merge each row or each column into one node, whichever is cheaper, and regroup these into K balanced classes.
>
> Prove it.

What it rederives is only that 3-SAT can be decided in time O(2<sup>δ*n*</sup>) for every δ > 0, not the sharper bounds at the top of this page.

## License

Apache 2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE).
