# formal-math

Machine-checked Lean 4 formalizations published by Anthropic. Each subdirectory is a self-contained Lake project with its own toolchain pin, README and build instructions; build from inside the subdirectory.

| Project | Statement | Lean / Mathlib |
|---|---|---|
| [`zeta23/`](zeta23/) | More than two thirds of the zeros of the Riemann zeta function are simple and on the critical line (Alpöge–Furman, arXiv:2608.13637) | `leanprover/lean4:v4.33.0-rc2` / Mathlib `v4.33.0-rc2` |

## CI

Pull requests and pushes to `main` run [`.github/workflows/lean-projects.yml`](.github/workflows/lean-projects.yml) on each project folder whose files changed, and only on those; a change confined to CI configuration or documentation (`.github/`, this README, ...) verifies nothing, and a full run of every project is started manually from the Actions tab (`workflow_dispatch`, projects = `all`). The `verify` job runs on the runner label in the repository/organization variable `LEAN_CI_RUNNER` when it is set (e.g. a GitHub larger runner such as `ubuntu-latest-16-cores`), otherwise on `ubuntu-latest`. A project passes when `lake build` succeeds on its pinned toolchain with no `sorry` outside the trusted comparator statement files (`Challenge.lean`, `Challenge/<Topic>.lean`), and when the [Palomar registry](https://github.com/PalomarRegistry)'s acceptance check — [`leanprover/comparator`](https://github.com/leanprover/comparator) with a toolchain-matched `lean4export`, the independent `nanoda` kernel and the `landrun` sandbox, at the registry's tool pins — prints `Your solution is okay!` for every comparator configuration the project declares ([`.github/scripts/comparator-check.sh`](.github/scripts/comparator-check.sh); run it locally with `cd <project> && bash ../.github/scripts/comparator-check.sh`).

To add a project: create a top-level directory with `lakefile.toml` (or `lakefile.lean`), `lean-toolchain`, `lake-manifest.json`, a Mathlib-only `Challenge` module stating the headline theorems, a `Solution` module proving them from the library, and at least one comparator configuration (`comparator.json` next to the lakefile, or `comparator/config*.json`); add a row to the table above.

## License

Apache-2.0 — see [LICENSE](LICENSE). Individual projects may carry additional NOTICE files.
