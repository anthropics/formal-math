# formal-math

Machine-checked Lean 4 formalizations published by Anthropic. Each subdirectory is a self-contained Lake project with its own toolchain pin, README and build instructions; build from inside the subdirectory. Projects follow the layout of the [Palomar](https://palomar-registry.org/) submission template (`Challenge.lean` / `Solution.lean` / `comparator.json` / `formalization.yaml` at the project root) and are submitted to Palomar with the subdirectory as the selected project; the licence file Palomar reads is this repository's root `LICENSE`.

| Project | Statement | Lean / Mathlib |
|---|---|---|
| [`zeta23/`](zeta23/) | More than two thirds of the zeros of the Riemann zeta function are simple and on the critical line (Alpöge–Furman, arXiv:2608.13637) | `leanprover/lean4:v4.33.0-rc2` / Mathlib `v4.33.0-rc2` |

## CI

Pull requests and pushes to `main` run [`.github/workflows/lean-projects.yml`](.github/workflows/lean-projects.yml) on each project folder whose files changed, and only on those; a change confined to CI configuration or documentation (`.github/`, this README, ...) verifies nothing, and a full run of every project is started manually from the Actions tab (`workflow_dispatch`, projects = `all`). The `verify` job runs on the runner label in the repository/organization variable `LEAN_CI_RUNNER` when it is set (e.g. a GitHub larger runner such as `ubuntu-latest-16-cores`), otherwise on `ubuntu-latest`. Pull-request runs reuse the project's previous Lake build for the same toolchain and manifest (only changed modules are rebuilt); merges to `main` and manual runs build from scratch. A project passes when

- its layout satisfies the Palomar registry's structural requirements ([`.github/scripts/palomar-structure-check.sh`](.github/scripts/palomar-structure-check.sh), run first and without a toolchain: exactly one lakefile with a committed `lake-manifest.json`, a `lean-toolchain` pinned to a Lean release or release candidate, a small Mathlib-only `Challenge` module, a `sorry`-free `Solution` module, a `comparator.json` naming every compared declaration, the required `formalization.yaml` fields, and the root `LICENSE`; run it locally with `bash .github/scripts/palomar-structure-check.sh <project>`),
- `lake build` succeeds on its pinned toolchain with no `sorry` outside the trusted comparator statement files (`Challenge.lean`, `Challenge/<Topic>.lean`), and when the [Palomar registry](https://github.com/PalomarRegistry)'s acceptance check — [`leanprover/comparator`](https://github.com/leanprover/comparator) with a toolchain-matched `lean4export`, the independent `nanoda` kernel and the `landrun` sandbox, at the registry's tool pins — prints `Your solution is okay!` for every comparator configuration the project declares ([`.github/scripts/comparator-check.sh`](.github/scripts/comparator-check.sh); run it locally with `cd <project> && bash ../.github/scripts/comparator-check.sh`).

To add a project: create a top-level directory with `lakefile.toml` (or `lakefile.lean`), `lean-toolchain`, `lake-manifest.json`, a Mathlib-only `Challenge` module stating the headline theorems, a `Solution` module proving them from the library, `formalization.yaml`, and at least one comparator configuration (`comparator.json` next to the lakefile, or `comparator/config*.json`); add a row to the table above. Contributors using Claude Code can run `/palomar-prepare` ([`.claude/skills/palomar-prepare`](.claude/skills/palomar-prepare/SKILL.md)) for the full preparation checklist.

## License

Apache-2.0 — see [LICENSE](LICENSE). Individual projects may carry additional NOTICE files.
