# Truly Subquadratic 3SUM and Truly Subcubic APSP: a Lean 4 formalization

This formalization accompanies the paper *Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs* by Josh Alman and Virginia Vassilevska Williams. It states results of the paper as theorems of Lean 4, in the paper's notation and numbering, and proves these theorems.

**The five headline claims are stated in one self-contained file, [`EndStatement.lean`](EndStatement.lean).** They are about programs of a word RAM, on Exact Triangle, 3SUM, the (min,+)-product, APSP and k-Clique. The file has 139 lines, imports nothing and contains no proof. **For the five claims this one file is all that has to be read.** (Five theorems of a line or two each, the list of their names and the build files tie it to the proofs; see "What a reader must trust".)

**Everything beyond these is optional reading.** [`PaperStatements.lean`](PaperStatements.lean) imports `EndStatement.lean` and Mathlib, and nothing else. It is long. It states further results of the paper, item by item, with the definitions that they need. Only a reader who wants to believe one of these further statements needs it, and then only as far as that statement reaches.

| Status | Which items of the paper | Stated in |
|---|---|---|
| **Proved about programs of a word RAM,** and stated in one short file that imports nothing: the *five claims* | Theorem 19; Theorem 22 for 3SUM, for the (min,+)-product and for APSP; Corollary 39 for weight zero | `EndStatement.lean` |
| **Proved about programs of the same machine,** item by item, with the bounds as printed (for Corollary 40 see "What is not proved"): the *statements about programs* | Theorem 1, the deterministic half of Theorem 2, Theorems 3 to 5, Corollaries 15 and 16, Theorems 19, 22, 24 and 25, Corollary 26, Theorem 30, Corollaries 31, 32, 39 and 40 | `PaperStatements.lean` |
| **Proved as mathematics,** with no machine and no running time | the numbered lemmas and equations of Sections 2 to 5, apart from their sentences on running time; Tables 1 and 2; Figures 3, 4, 6 and 10; Remarks 18 and 20; of Theorems 17, 21, 34 and 35, Lemma 37 and Corollary 38 only correctness, counts and the arithmetic of the bounds; of Lemma 36, which restates reductions of [CVX22], only the part that the paper itself argues | `PaperStatements.lean` |
| **Proved only as implications** between running-time claims, for an arbitrary meaning of "is solved in time T": the three *conditional lemmas* | the deductions of Theorem 34, Corollary 38 and Theorem 35 | lemmas of the library, in `ThreeSumApsp/ConditionalTimes/`; they are not statements, so Comparator does not compare them, and what they say has to be read in the library |
| **Proved: definitions that are written twice agree** | the notions that both files define in their own words | `PaperStatements.lean` |
| **Not proved for any machine** | the running times for real inputs (Theorem 35, Lemmas 36 and 37, Corollary 38, and the half of Theorem 2 on real inputs) and those of Section 5.1 (Theorems 33 and 34); the running times of the two reduction theorems (Theorems 17 and 21) in their printed form | see "What is not proved" |

Every theorem that is stated is proved. "Proved" means throughout that the library contains a proof; "How to check it" says how a reader can confirm this. For every statement, the text that a reader has to read and trust is kept apart from the proofs.

**Terms.** A *statement* is a proposition such as `Lemma_6`, defined in one of the two files, for which `Challenge/` has a theorem which says that it holds, such as `lemma_6 : Lemma_6`, written with `sorry` in place of its proof. The *library*, the folder `ThreeSumApsp/`, proves a theorem of the same name, and a tool can check that the two say the same (see "How to check it"). A *lemma* is a theorem of the library that is not one of these. (A numbered lemma of the paper, such as Lemma 6, is rendered by a statement.)

Research artifact. Not maintained and not accepting contributions.

Lean `v4.33.1`, Mathlib `v4.33.1`. The text follows version 1 of the paper on arXiv (arXiv:2610.06783v1); the numbers of items and pages are those of that version. Citation keys such as [VW13] are those of the paper.

## The five claims

`EndStatement.lean` uses Lean's core library only, not even Mathlib. It defines a word RAM; it says what it means for a problem to be solved on that machine within a time bound; it writes down five problems; and it writes down five claims of the paper about them, as propositions. It can be read from top to bottom with the paper beside it. The library proves all five claims.

| Claim in `EndStatement.lean` | The paper | Problem | Bound | The theorem that says that the claim holds |
|---|---|---|---|---|
| `Theorem_19` | Theorem 19 | Exact Triangle | O(n^{3−0.0017}) | `endStatement_theorem_19` |
| `Theorem_22_3SUM` | Theorem 22 | 3SUM | O(n^{1.9992}) | `endStatement_theorem_22_3SUM` |
| `Theorem_22_MinPlus` | Theorem 22 | (min,+)-product | O(n^{2.99942}) | `endStatement_theorem_22_MinPlus` |
| `Theorem_22_APSP` | Theorem 22 | APSP | O(n^{2.99942}) | `endStatement_theorem_22_APSP` |
| `Corollary_39_ZeroWeight` | Corollary 39 | Zero-Weight k-Clique, every k ≥ 3 | O(n^{k−0.0017⌊k/3⌋}) | `endStatement_corollary_39_zeroWeight` |

This is the claim on 3SUM, with the definition of solving that all five claims use:

```lean
def Problem.SolvedInTime (Q : Problem) (r : Rat) : Prop :=
  ∀ κ : Nat, ∃ (P : List Instr) (b : Nat) (T : Nat → Nat), BigO T r ∧
    ∀ (n : Nat) (x : Q.Instance n), (∀ a ∈ Q.input x, a.natAbs ≤ n ^ κ) → ∀ W ≥ b * (Nat.log2 n + 1),
      Q.SolvedBy x P W (T n)

def ThreeSum : Problem where
  Instance n := Fin n → Int
  input x := List.ofFn x
  yes x := ∃ i j k, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ x i + x j + x k = 0

def Theorem_22_3SUM : Prop :=
  ThreeSum.SolvedInTime 1.9992
```

**How "solved in O(n^r) steps" is to be read.** The definition (`Problem.SolvedBy` for one run and `Problem.SolvedInTime`, seven lines together) renders the model of Theorem 2: "a word RAM with O(log n)-bit words", on which "all numbers in the input are integers of absolute value n^{O(1)}". For every exponent κ (the paper's ν) there are one program, one number b and one time bound T(n) = O(n^r). On every instance of every size n, the size n = 0 included, whose numbers have absolute value at most n^κ, and at every word size of at least b (⌊log₂ n⌋ + 1) bits, the program has to halt within T(n) steps with the right answer. For a decision problem, the right answer is to accept exactly if the answer is yes. For the (min,+)-product and APSP, the program has to accept and to leave the output in the cells right after the input, as signed words.

**The machine.** Memory cells are named by integers, negative ones included, and hold words of W bits. A program is a list of instructions, and there are nine kinds, each of which takes one step: write the constant 1 into a cell; add, subtract or multiply two cells modulo 2^W and write the result into a cell; load from, or store to, the cell whose name is the signed value of a word; jump to a position that is fixed in the text of the program if a word is negative; accept; reject. An instruction names its cells by integers in the text of the program. Running past the end of the program rejects. There is no division, no shift, no bitwise operation, and no constant other than 1. [`docs/MACHINE.md`](docs/MACHINE.md) compares the machine with the standard word RAM point by point.

Theorem 22 prints two numerals for each of its problems: one for the algorithm that uses Theorem 5 (1.99923 for 3SUM, 2.99949 for the other two) and one for the algorithm that uses Corollary 26 (1.9992 and 2.99942). The claims on these three problems state the numerals of the second algorithm, which are smaller. The bounds of the first algorithm are proved as well, in `wordRam_theorem_22_first`.

**The claims say that programs exist.** The proofs describe the programs, but not everything in them is computed: see `docs/MACHINE.md`, "How explicit the programs are". The constants of the time bounds are not optimized; they are large, and for most theorems no value is given.

**The claims and the statements about programs assume no cited result.** None of them has among its hypotheses a cited result or a sentence of the paper that is not proved here; the three conditional lemmas do. (Corollary 40 is stated for arbitrary numbers that satisfy the lower bounds that it names; see "What is not proved".) The reductions of [CH20], [VW13] and [VW18] that Theorem 21 and Corollary 39 cite are written as programs, with proofs; the programs for [VW13] and [VW18] are not compared with the constructions in those papers.

[`docs/MACHINE.md`](docs/MACHINE.md), Part 1, explains the rest of the model, all of which is defined in `EndStatement.lean`: how the inputs and outputs are written into the memory, what a program cannot do, and where the machine is generous. It also says how the five claims relate to the other statements.

## What is not proved

None of the three conditional lemmas proves a running time. Not proved, not stated, or stated only in part:

* **Real inputs, and Section 5.1.** Theorem 35 and the half of Theorem 2 on real inputs are about Las Vegas algorithms on a real RAM. Corollary 38 and Lemma 37 are deterministic, but their inputs are real numbers. The machine has integer words and no random bits, so these running times are not proved for any machine. Theorem 34 is about a deterministic algorithm with integer inputs. But it rests on Theorem 33, which the paper proves and which is not proved here, and its bound is written with μ, an exponent of rectangular matrix multiplication, which is not defined here. So its running time is not proved for any machine either.
* **Theorem 33, and cited results.** Theorem 33, which the paper proves, is not proved here; it occurs only as a hypothesis. Lemma 36 restates randomized reductions of [CVX22]; as a sentence about running times it occurs only as a hypothesis, and the part that the paper itself argues is stated in `PaperStatements.lean`.
* **Exponents of matrix multiplication** (ω, α, μ and the rectangular exponents) are not defined. Where the paper uses a bound on them, the bound is an explicit hypothesis or a numeral. In Corollary 40, that one of the three conjectures of [vdBNS19] fails means this: put arbitrary real numbers in place of the rectangular exponents in the conjecture, subject only to the lower bounds that Corollary 40 names; then programs achieve smaller exponents than the conjecture allows. That the true exponents satisfy these lower bounds is not proved.
* **The hypotheses that the paper calls refuted** (3SUM, APSP, Exact Triangle, k-Clique and others) are not defined; only running times are stated. The conjectures of [vdBNS19] are the exception.
* **Running-time sentences inside lemmas and proofs**, such as the second sentence of Lemma 29 and the cost paragraphs of Section 2.4.4 and of the proof of Theorem 30, have no statement of their own.
* **Search versions** of the decision problems, and instances with N = 0 or D = 0 in the statements with two sizes.

[`docs/REMARKS.md`](docs/REMARKS.md), "What is not proved", has the full list, with the reasons, among them why Theorems 17 and 21 are not stated about programs.

## What a reader must trust

To check what is claimed, a reader needs the paper and the following text.

* **For the five claims:** `EndStatement.lean`. It imports nothing. So there is no Mathlib in this text: the claims are made of notions of Lean's core library only (integers, natural and rational numbers, lists, bit vectors). This is the smallest trusted text that is offered here.
* **For any other statement:** `PaperStatements.lean` as well, as far as the statement reaches: the proposition, and the definitions that it names, which precede it. The file imports only Mathlib and `EndStatement.lean`, whose machine it uses. It has to be read. The statements and the proofs import the same definitions from it: Comparator confirms that they are the same on both sides, and no tool can tell whether they say what the paper says. The file defines only what the statements need.
* **The two files of `Challenge/`,** each of which imports the file of its own name and nothing else, and says of each of its statements, in a line or two, that it holds; and **the lists of names** `comparator-*.json`, which say which theorems are compared. A script checks the imports, and checks the lists against `Challenge/`.
* **The build files** `lakefile.toml`, `lake-manifest.json` and `lean-toolchain`, which say what is compiled, with which Lean and against which Mathlib. No script looks at them.
* **For every statement:** Lean's core library; the three standard axioms `propext`, `Classical.choice` and `Quot.sound`; Lean's kernel; and the check described in the next section. **For the statements of `PaperStatements.lean` also:** Mathlib's definitions.

The rest of the Lean text, the library and `Solution/`, need not be read: Lean checks it. In `PaperStatements.lean`, a paragraph of a comment that begins with the word NOTE marks a place where the Lean text departs from the printed text. `EndStatement.lean` has short comments only; the choices that it makes are described in `docs/MACHINE.md`, Part 1. That part also lists the notions that both files define in their own words, with the statements which say that the two agree; `PaperStatements.lean` defines them again mostly because the paper uses them also over the real numbers and for rectangular matrices, which `EndStatement.lean` has no need of.

## How to check it

    scripts/check.sh

The script needs elan, git, curl, Python 3 and a network connection. It runs `python3 scripts/generate.py --check`, `python3 scripts/index.py --check --names`, `python3 scripts/layers.py --check`, `lake exe cache get` (which fetches Mathlib's compiled files), `lake build --wfail EndStatement PaperStatements ThreeSumApsp Solution` and `lake build Challenge`, and stops at the first failure. So it fails on an error in any of these libraries and on a warning outside `Challenge/`, where each theorem has `sorry` in place of its proof. The script does not run Comparator, so it does not compare the theorems of the library with those of `Challenge/`. Expect about ten minutes on eight cores, once Mathlib's compiled files are there.

"Security considerations" below says what these commands fetch and run.

**What is compared with what.** A file of `Challenge/` has one theorem for each statement, with `sorry` in place of its proof. The library proves theorems of the same names, and the file of the same name in `Solution/` does nothing but import them. The file `comparator-*.json` of that name lists the names. `python3 scripts/generate.py --check` confirms that the lists name every theorem of `Challenge/`; it accepts only files of a simple form, and it guards against accidents, not against a file written to deceive (see `scripts/README.md`).

**Comparator.** The check that does not ask the reader to trust the library is the tool [Comparator](https://github.com/leanprover/comparator) of the Lean Focused Research Organization; what follows describes it at its tag v4.33.0. The files `comparator-endstatement.json` and `comparator-paperstatements.json` are configurations for it, one for each file of `Challenge/`. Comparator's own README gives the command and its safeguards. Build Comparator and lean4export, both at tag v4.33.0, with the Lean toolchain named in `lean-toolchain`, v4.33.1. Run the tool in a fresh clone, one for each configuration, not in one in which `lake build` or `scripts/check.sh` has run. For a configuration the tool compiles the Challenge file and the Solution file in a sandbox and then verifies, outside Lean's elaborator, that

* each listed theorem has the same statement on both sides, as a term of Lean, and every definition that the statements mention is the same on both sides;
* the proofs depend on no axiom other than `propext`, `Quot.sound` and `Classical.choice`, hence not on `sorry`;
* everything that the proofs depend on passes Lean's kernel and, as the configurations ask, a second, independent kernel (nanoda).

The field `"definition_names"` of both configurations is empty: it is for what Comparator's README calls definition holes, where a challenge wants "to leave open definitions for solutions to fill in". The files of `Challenge/` declare theorems only, so there is none to list.

What remains for the reader is to read what is claimed: `EndStatement.lean` and, for the further statements, `PaperStatements.lean`, with the few lines named under "What a reader must trust". This README records no run of the tool.

**What these checks do not cover.** Comparator follows the compared theorems and all that they depend on. For a file of the library on which no statement depends, `lake build` is the only check; a `sorry` there would show as a warning outside `Challenge/`.

## Security considerations

Building and checking this formalization downloads code from other projects and runs it on your machine.

* **Building.** `lake build` lets elan fetch the Lean toolchain named in `lean-toolchain`, and clones Mathlib and the packages on which it depends from GitHub, at the commits pinned in `lake-manifest.json`. `lake exe cache get` fetches Mathlib's compiled files from Mathlib's cache; nothing here pins or checks them. Compiling a Lean file runs the tactics and macros that the file and its imports define, with the rights of your user and outside any sandbox.
* **Comparator, on files that you do not trust.** Comparator's README assumes a tree in which none of these files has been compiled before. So use one fresh clone for each configuration. Do not use the clone for anything else afterwards.
* **The scripts.** `scripts/generate.py`, `scripts/index.py` and `scripts/layers.py` use the standard library only, open no connection and start no process. The first two overwrite the generated files that `scripts/README.md` names. `scripts/check.sh` runs the commands listed under "How to check it".

## How to find an item of the paper

[`docs/INDEX.md`](docs/INDEX.md) goes through the paper item by item. For each numbered item, table and figure it names the statements, the files in which they are stated and proved, what they say about the item, and what is not stated.

**Names.** A statement carries the number of its item: `Lemma_6` is Lemma 6, `Eq_5` is equation (5), `Table_2_c19` is a row of Table 2. `Items.Theorem_5` is a statement about programs. The prefix `Agreement_` marks a statement that two definitions agree, and `Sec2_` or `Sec4_` a sentence without a number. The theorem which says that a statement holds has the name of the statement with a lower-case first letter (`lemma_6`); for a statement about programs it has the prefix `wordRam_` (`wordRam_theorem_5`), and for one of the five claims `endStatement_`. A docstring names the item or the section and, where the statement renders a sentence of the paper, quotes it. Quotations from the paper are included with the authors' permission.

**To check one item,** say Lemma 11: find its row in `docs/INDEX.md`; read the statement `Lemma_11` in `PaperStatements.lean` and the definitions that it names (`Leaves`, `alpha`, `beta` and so on), which precede it in the same file, with the paper beside them. The proof, in `ThreeSumApsp/Sec2/Lemma11.lean`, need not be read: "How to check it" says how to make sure that it proves this statement. For a statement about programs, `docs/MACHINE.md`, "How to follow a proof from a claim down", shows the layers between the statement and the programs.

## How the running times are proved

Nothing in this section has to be trusted. Programs are written in a small imperative language with integer variables, a memory, +, −, ×, comparisons, if, while and procedure calls. Every executed operation counts as a step, and every run is subject to limits on the size of its numbers, its memory and its nesting of calls. A compiler translates a program to the machine, and a theorem says that a run of c steps becomes a run of at most A·c + A steps, where A depends on the text of the program only.

The programs follow the paper's algorithms, but not in every detail. [`docs/MACHINE.md`](docs/MACHINE.md) describes the language, the compiler and the programs for a reader who holds the paper, and lists the departures. [`docs/VERIFYING.md`](docs/VERIFYING.md) shows how a routine is verified, with one small routine explained line by line.

## How the files are laid out

| Path | What it holds |
|---|---|
| `EndStatement.lean` | the five claims, with the machine and every definition that they use |
| `PaperStatements.lean` | the further statements, with the definitions that they use, in the paper's order and names |
| `Challenge/` | for each of these two files, one theorem for each statement, with `sorry` in place of its proof |
| `comparator-*.json` | which theorems Comparator compares |
| `ThreeSumApsp/` | the library: all proofs |
| `Solution/` | one file for each file of `Challenge/`, which imports the proofs and adds nothing |
| `docs/INDEX.md` | the paper item by item: what is stated, where, and what is not |
| `docs/PROGRAMS.md` | the programs item by item: the final theorem, the routines, and the lemmas about them, with their files |
| `docs/FILES.md` | the trusted files and every file of the library, each with the title of its header, folder by folder |
| `docs/REMARKS.md` | what is not proved; where the Lean text differs from the paper's wording and why; what is cited; every NOTE |
| `docs/MACHINE.md` | the machine compared with the standard model; the language, the compiler and the programs; where the programs depart from the paper |
| `docs/VERIFYING.md` | how a routine of the language is verified: the rules, the conventions, and one routine line by line |
| `scripts/` | see `scripts/README.md` |

The first four rows, with the build files, are the trusted text; "What a reader must trust" says which part of it each statement needs. `scripts/index.py` writes `docs/INDEX.md`, `docs/PROGRAMS.md`, `docs/FILES.md` and the last section of `docs/REMARKS.md`, the first two from `docs/paper-items.json` and `docs/programs.json`; no script writes the other documents. Inside the library, the theorem that proves a statement has the name of the theorem in `Challenge/`, and `docs/INDEX.md` says in which file it is. A file such as `ThreeSumApsp/Sec2.lean`, beside the folder of the same name, imports all files of that folder and nothing else.

`docs/MACHINE.md`, "The folders and namespaces of the library", says what each folder of the library holds, which folders it may import (`python3 scripts/layers.py --check` tests this), and which namespace belongs to which folder.

## Where the Lean text departs from the paper

[`docs/REMARKS.md`](docs/REMARKS.md) records the departures section by section, with the reasons, and lists every NOTE. Most are hypotheses that the paper leaves implicit, choices between two readings, and the direction in which a quantity such as n^μ or n/d is rounded to an integer. Some steps need an argument or a hypothesis that is not printed. No bound of the paper changes.

## License

Apache 2.0; see LICENSE and NOTICE. The comments of the Lean files and the documents quote statements and sentences of the paper named at the head of this README; the quoted passages are included, under the Apache 2.0 license, with the permission of the authors of the paper.
