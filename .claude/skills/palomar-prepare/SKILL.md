---
name: palomar-prepare
description: Prepare and validate a project folder in this repo for Palomar submission (layout, toolchain pin, Challenge/Solution/comparator.json, formalization.yaml, local build + comparator check).
---

# palomar-prepare

Bring one project directory of this repository to the state the [Palomar registry](https://palomar-registry.org/)
accepts, and verify it locally the way CI and the registry will. References: Palomar
["How to submit"](https://palomar-registry.org/how-to-submit); the starter layout
[PalomarRegistry/PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate); the submission policy
(PalomarRegistry/PalomarPolicy, `CONTRIBUTING.md` §2.3); the metadata standard
[mathlib-initiative/formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) (v0.4). In this
repository `zeta23/` is the worked example of everything below.

## When to use

- A new top-level project directory is being added, or an existing one is being readied for (re)submission.
- CI failed in the "Palomar structure check" or "Palomar bar" step of `.github/workflows/lean-projects.yml`.
- Someone asks "is `<dir>` ready for Palomar?".

Input: the project directory `<dir>` (a top-level folder containing the lakefile). Work from the repository root.

## 1. Layout (the registry's rules for the selected project directory)

- [ ] exactly one of `lakefile.toml` or `lakefile.lean`, with a committed `lake-manifest.json` (required for
      `lakefile.lean` projects, strongly recommended otherwise — always commit it here);
- [ ] `lean-toolchain`, pinned to a supported Lean release or release candidate (a repository-root file may be
      shared by a nested project, but a project-local file takes precedence — here every project has its own);
- [ ] a small, readable Challenge module a mathematician should audit, conventionally `Challenge.lean`;
- [ ] a proved Solution module, conventionally `Solution.lean`;
- [ ] a Comparator JSON configuration, conventionally `comparator.json`, naming every theorem and definition
      Comparator should compare;
- [ ] `formalization.yaml` (project, result, sources, authorship, automation, review, known limitations);
- [ ] the licence file is the repository-root `LICENSE` (Apache-2.0); a project may carry its own copy and a `NOTICE`.

Run the mechanical check first and fix every `FAIL` (read the `WARN`s too):

```bash
bash .github/scripts/palomar-structure-check.sh <dir>
```

It checks the list above plus the size/import/axiom rules of §3 and the metadata keys of §4 (the registry's
hard mechanical requirements are violations, the rest warnings), offline and without a toolchain; CI runs the
same script on every changed project before anything is built.

## 2. Toolchain and dependency pins

- `lean-toolchain`: `leanprover/lean4:vX.Y.Z` or `vX.Y.Z-rcN` only — no nightlies, no custom toolchains. Prefer the
  stable release matching a Mathlib tag.
- The lakefile requires Mathlib at an immutable commit (`rev = "<40-char sha>"`, comment the tag), never a branch.
- `lake update` once, then commit `lake-manifest.json`; CI keys its caches on toolchain + manifest + lakefile.
- Dependencies used only by the Solution side may be any pinned git dependency; they never relax the Challenge
  import rule below.

## 3. Challenge.lean, Solution.lean, comparator.json

**Challenge.lean** — the trusted statement surface (pattern: `zeta23/Challenge.lean`, template `Challenge.lean`):
- imports resolve to Lean core / Mathlib (and its dependency closure) / TauCeti only — never a module of the
  project. Definitions the statements need are written out from Mathlib alone inside the file (zeta23 inlines
  its `ChallengeDeps.lean` verbatim so the module's only import is `Mathlib`);
- each compared result is a `theorem <name> : <statement> := by sorry` (the `sorry` is deliberate: this side says
  *what* is claimed); names are descriptive, globally unique, and identical to the Solution's;
- every hypothesis is an explicit binder; no hidden assumptions, no weakening of the informal result; docstrings
  say in plain words what each declaration means;
- size: hard limit 1000 lines / 100 KiB, aim for ≤ 300 lines / 32 KiB. Further result groups go in topic modules
  `Challenge/<Topic>.lean` + `Solution/<Topic>.lean` with their own `comparator-<topic>.json` (zeta23: `XiPrime`).

**Solution.lean** — untrusted, checked by Comparator: imports the project library, restates every Challenge
declaration byte-for-byte under the same name and proves it (typically a one-line delegation to the library
theorem, e.g. `theorem main_result … := Library.main_result …`). No `sorry`, no `native_decide`
(`Lean.ofReduceBool`), no `axiom`: the closure of each compared theorem may use only `propext`,
`Classical.choice`, `Quot.sound` (plain `decide` is fine). A conditional result takes its hypothesis as an
explicit argument (`theorem t (h : RiemannHypothesis) : …`) or a bundled `[LiteratureHypotheses]` instance
argument in each signature that needs it — never an `axiom`, and not a file-level `variable`.

**comparator.json** — leanprover/comparator's schema, the shape used throughout this repository:

```json
{
  "challenge_module": "Challenge",
  "solution_module": "Solution",
  "theorem_names": ["MyProject.main_result", "MyProject.corollary"],
  "definition_names": [],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "enable_nanoda": true
}
```

List every Challenge theorem in `theorem_names` and every Challenge `def` whose body must match in
`definition_names` (fully qualified names). Keep `permitted_axioms` exactly the standard three and
`enable_nanoda: true`. Add `Challenge`/`Solution` (and any `ChallengeDeps`) as `[[lean_lib]]` entries of the
lakefile so the bare module names resolve (see `zeta23/lakefile.toml`).

## 4. formalization.yaml (registry metadata)

Start from PalomarTemplate's `formalization.yaml`, keep `version: v0.4`, replace every `TEMPLATE:` value
(the registry rejects leftovers), and compare with `zeta23/formalization.yaml`. Checklist:

- `project.name`; `project.description` — the public abstract Palomar displays: a self-contained account of the
  result, the objects it is stated against, what is and is not assumed, and the proof route, readable without
  the repository (≤ 10000 chars); `project.authors` (who wrote the formalization — human names, or the AI system
  if it wrote the code, as in zeta23), `project.license: Apache-2.0`, `project.responsible_maintainers` (humans);
- `repository`: omit for a substantive development (the normal case here); a thin Comparator wrapper must name
  the substantive formalization repo at a full commit SHA;
- `classification.arxiv` (required; 1–2 arXiv categories, e.g. `math.NT`) and `classification.msc2020` (1–8
  five-character codes) — classify the mathematics, not the use of Lean or AI;
- `sources[]`: each with `title` and `relationship` ∈ `formalizes | adapts | independently-proves | background |
  other` (+ `authors`, `id`, `type`, `location`, `author_endorsement` when applicable). Original result first
  presented by the formalization: one source with `type: original-proof`, `relationship: other`, all others
  `background`/`other`. A new proof of a published result is `independently-proves`;
- `related_formalizations[]` (prior formalizations: `builds-on | adapts | independent | supersedes`) or `[]`;
- `status`: `scope` (exactly what is and is not formalized), `sorry_count: 0`, `sorry_in_definitions: 0`,
  `axioms: [propext, Classical.choice, Quot.sound]`, optional `main_results[]` (declaration, file, axioms,
  `comparator_config`);
- `automation.methods[]` (`manual | copilot | agent | autonomous | other`, `models`, `framework`, `tool_setup`,
  `cost`), `automation.notes` — the role of AI and of humans, honestly;
- `fidelity.divergences` — every known gap between the Lean statements and the source (or `none known`);
- `review.status` (required: `unchecked | self-assessed | agent-reviewed | author-verified | peer-reviewed | …` —
  the review done *before* submission), `review.reviewers`, `review.notes` — who read the Challenge statements
  against the source;
- `alignment.statements[]` — per compared theorem: source statement, Lean name, module, status, note
  (the plain-language account of every compared theorem); `acknowledgements` (libraries, adapted files, people).

## 5. Local verification (what CI and the registry run)

```bash
cd <dir>
lake exe cache get && lake build                      # no errors; sorry warnings only from Challenge*.lean
lake build Challenge Solution
# axiom audit: for each compared name, `#print axioms <name>` (e.g. a scripts/PrintAxioms.lean importing
# Solution) must list a subset of [propext, Classical.choice, Quot.sound]
bash ../.github/scripts/comparator-check.sh           # from the project dir; Linux, needs go + cargo + jq
```

`comparator-check.sh` fetches leanprover/comparator, the lean4export release matching `lean-toolchain`, the
nanoda kernel and the landrun sandbox at the registry's pins, and runs every `comparator*.json`; each must end
with `Your solution is okay!`. Do not pre-build Challenge/Solution for a run you want to rely on — Comparator
builds them in its sandbox.

## 6. Hygiene

- `.gitignore` covers `.lake/` (the root one does); no build artefacts, exports or caches committed;
- project `README.md`: abstract, table of main results (Lean name ↔ informal statement), toolchain/Mathlib pins,
  build and verification instructions, what a reader must trust; `NOTICE` for adapted third-party files;
- a row for the project in the root `README.md` table;
- no absolute paths, hostnames or machine-specific scripts in the tree.

## 7. Pull request

- CI (`lean-projects.yml`) runs, for each *changed* project folder only: structure check → `lake build` (no sorry
  outside `Challenge*.lean`) → comparator check. CI-only or docs-only changes verify nothing; a full run is
  `workflow_dispatch` with `projects=all`.
- PR description: what is proved (informal), the compared declaration names, toolchain/Mathlib pins, the output
  of the structure check, and whether the comparator check was run locally.

## 8. Submitting to Palomar (human step)

Machines should not drive the submission form. After the PR is merged:
1. copy the full 40-character commit SHA from `main` (`git rev-parse HEAD` on the merged commit);
2. open the submission form from the How-to-submit page; enter the repository, the SHA, and project path = the
   folder name (leave config/metadata paths blank for the conventional names); state whether you maintain the
   formalization or have a maintainer's approval;
3. sign in with GitHub when asked — it proves write access to the repository and the token is discarded;
4. keep the status page URL: it is the only way back to the submission (verification → review → register or
   withdraw). A revised submission is a new commit SHA.
