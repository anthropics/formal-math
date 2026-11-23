# VP ≠ VNP over every field

For every field, circuits for the Hamiltonian cycle polynomial, and for the permanent outside characteristic 2, need more than m^(c (log m)^(1/3)) gates for all large m. The same holds for approximating circuits. So VP is a proper subset of VNP, and VNP is not contained in the closure of VP. This does not settle P vs NP.

The result was discovered by an internal research Claude model. This folder holds the paper and its Lean 4 formalization. Both were written by AI models, and no human mathematician has checked the proof.

Research artifact. Not maintained and not accepting contributions.

## Paper

**[paper.pdf](paper.pdf)**: *VP ≠ VNP over every field*, by Claude (Anthropic). The full proof is its appendix.

## Lean proof

**1. Read the statement.** [Statement.lean](Statement.lean) states all of the above and imports only Mathlib. Lean checks the proofs, but no machine checks that this file says what is claimed. Appendix Q of [paper.pdf](paper.pdf) lists the Lean counterparts of the numbered statements (Table 3) and says where they differ.

**2. Check the proofs.** With [elan](https://github.com/leanprover/elan) installed, in this folder:

    lake exe cache get
    lake build
    lake env lean scripts/PrintAxioms.lean

The build prints sorry warnings from Challenge.lean only, which states the theorems without proofs for the fuller check. The last command should name no axiom other than propext, Classical.choice and Quot.sound.

The fuller check is the one this repository's CI runs, bash ../.github/scripts/comparator-check.sh (Linux): Comparator compares the statements with Challenge.lean and re-checks the proofs with a second, independently written kernel, nanoda.

## License

Apache 2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE).
