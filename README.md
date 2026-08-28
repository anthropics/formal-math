# formal-math

Machine-checked Lean 4 formalizations published by Anthropic. Each subdirectory is a self-contained Lake project with its own toolchain pin, README and build instructions; build from inside the subdirectory. Projects follow the layout of the [Palomar](https://palomar-registry.org/) submission template (`Challenge.lean` / `Solution.lean` / `comparator.json` / `formalization.yaml` at the project root) and are submitted to Palomar with the subdirectory as the selected project; the licence file Palomar reads is this repository's root `LICENSE`.

| Project | Statement | Lean / Mathlib |
|---|---|---|
| [`zeta23/`](zeta23/) | More than two thirds of the zeros of the Riemann zeta function are simple and on the critical line (Alpöge–Furman, arXiv:2608.13637) | `leanprover/lean4:v4.33.0-rc2` / Mathlib `v4.33.0-rc2` |

## License

Apache-2.0 — see [LICENSE](LICENSE). Individual projects may carry additional NOTICE files.
