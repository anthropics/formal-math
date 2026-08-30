# Independent verification with `leanprover/comparator`

This directory packages the headline theorems for [comparator](https://github.com/leanprover/comparator),
the Lean FRO's trusted-verification tool. Comparator builds a *trusted* challenge module and an
*untrusted* solution module in a sandbox, exports both, checks that the solution proves **exactly** the
challenge statements (every constant they mention must coincide), that the proofs use **only** the
axioms `propext`, `Classical.choice`, `Quot.sound`, and replays the solution through the Lean kernel
(and optionally the independent `nanoda` kernel).

| file | role | trusted? |
|---|---|---|
| `ChallengeDeps.lean` | the counting functions (nontrivial zeros of Mathlib's `riemannZeta` / `DirichletCharacter.LFunction`, multiplicity via `analyticOrderAt`, N, N₀*, N₀ˢ, N_d) and the Theorem-D constant c₁*, **defined from Mathlib alone** — exactly the definitions the challenge statements depend on, nothing else; inlined character-for-character into `Challenge.lean` (likewise `ChallengeDeps/XiPrime.lean` into `Challenge/XiPrime.lean`), so that each challenge module imports only Mathlib and can be read on its own | yes — read it (15 definitions) |
| `Challenge.lean` | seventeen theorem statements: Theorems A–E, each at the constant stated in the paper (2/3 on-line, 2/3 simple, 5/6 distinct, the optimal-window constants 2 − 1/c₁* and (3 − 1/c₁*)/2, and the Dirichlet analogues), proofs `sorry`; imports only Mathlib (the definition layer is inlined) | yes — read it |
| `ChallengeDeps/XiPrime.lean`, `Challenge/XiPrime.lean` | the counting functions for the zeros of ξ′ (defined from Mathlib alone) and six statements about them (all zeros in the open strip; Re ξ′/ξ > 0 on Re s ≥ 1; ≥ 0.85838 simple and on the line, ≥ 0.92919 distinct, and the quartic-window constants), proofs `sorry` | yes — read it |
| `ChallengeDeps/Union.lean`, `Challenge/Union.lean` | the two further counting functions N₀ (on-line, with multiplicity) and Nˢ (simple, anywhere) and four beyond-paper statements: exact and certified-decimal simple-or-on-line endpoints in dyadic and cumulative windows, with multiplicity-aware denominators and inclusion-exclusion union counts; proofs `sorry`; imports only Mathlib (definition layers inlined) | yes — read it |
| `Challenge/LineDecimal.lean` | four certified-decimal Montgomery--Taylor critical-line statements: distinct and simple on-line zeros, in dyadic and cumulative windows; proofs `sorry`; imports only Mathlib | yes — read it |
| `Challenge/Sextuple.lean` | four sextuple-improvement statements: simple on-line zeros at `0.672755620655` (ε-form) and fixed `0.6727556`, dyadic and cumulative; proofs `sorry`; imports only Mathlib | yes — read it |
| `Challenge/SextupleA1275.lean` | four refined-sextuple statements at `A = 51/4000`: simple on-line zeros at `0.6727837118`, ε-form and fixed, dyadic and cumulative; proofs `sorry`; imports only Mathlib | yes — read it |
| `Challenge/SextupleA1285.lean` | four refined-sextuple statements at `A = 257/20000`: simple on-line zeros at `0.6727949489`, ε-form and fixed, dyadic and cumulative; proofs `sorry`; imports only Mathlib | yes — read it |
| `Challenge/SextupleA1290.lean` | four refined-sextuple statements at `A = 129/10000`: simple on-line zeros at `0.6728005676`, ε-form and fixed, dyadic and cumulative; proofs `sorry`; imports only Mathlib | yes — read it |
| `Solution.lean`, `Solution/XiPrime.lean`, `Solution/Union.lean`, `Solution/LineDecimal.lean`, `Solution/Sextuple.lean`, `Solution/SextupleA1275.lean`, `Solution/SextupleA1285.lean`, `Solution/SextupleA1290.lean` | the corresponding statements, proved by delegating to the `Zeta23` library | no (checked by comparator) |
| `config.json`, `config-xiprime.json`, `config-union.json`, `config-line-decimal.json`, `config-sextuple.json`, `config-sextuple-a1275.json`, `config-sextuple-a1285.json`, `config-sextuple-a1290.json` | per-topic comparator configurations (theorem names, permitted axioms) | yes |
| `PrintAxioms.lean`, `PrintAxioms/XiPrime.lean`, `PrintAxioms/Union.lean`, `PrintAxioms/LineDecimal.lean`, `PrintAxioms/Sextuple.lean`, `PrintAxioms/SextupleA1275.lean`, `PrintAxioms/SextupleA1285.lean`, `PrintAxioms/SextupleA1290.lean`, `PrintAxioms/UnionConditional.lean`, `PrintAxioms/LineConditional.lean`, `PrintAxioms/PairCeiling.lean` | `#print axioms` for the statements — the quick check without comparator (`UnionConditional`, `LineConditional`, and `PairCeiling` are intentionally outside the trusted comparator topics; their displayed extra hypotheses are audited only with `#print axioms`; see the top-level README) | — |

What a skeptical reader has to trust: Mathlib's definitions of `riemannZeta`, `DirichletCharacter.LFunction`,
`analyticOrderAt`, `Set.ncard`, `finsum`; the trusted challenge files above; the Lean kernel; and comparator's own
assumptions (its README). Nothing under `Zeta23/` needs to be read to know *what* is proved.

Reading notes for the statements: N(T₁,T₂) on the left counts zeros **with multiplicity**. In the
Theorem A–E topics, N₀*, N₀ˢ, N_d on the right count **distinct** points — the strong direction. In the `Union`
topic, N₀ also counts with multiplicity and `N₀ + Nˢ − N₀ˢ` is natural-number inclusion-exclusion for the
simple-or-on-line union. "Nontrivial zero" is rendered as "zero with 0 < Re ρ < 1"; that every zero other than
the trivial ones lies in the open strip is classical and not needed to state anything. Finiteness of the zeros
in a window is proved on the solution side, not assumed. Windows are T₁ < Im ρ ≤ T₂ (positive ordinates), as
in the paper.

## Quick check (no extra tooling)

```bash
lake build Solution                      # builds the Zeta23 cone the seventeen theorems need (+ Mathlib)
lake env lean comparator/PrintAxioms.lean
# every line must read:  '<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Full comparator run

Prerequisites (see the comparator README for details): `elan`; [`landrun`](https://github.com/Zouuup/landrun)
built from `main`; [`lean4export`](https://github.com/leanprover/lean4export) built for the Lean version in
`../lean-toolchain`; the `comparator` binary; optionally `nanoda_bin` (set `"enable_nanoda": false` in
`config.json` if you do not have it). Then, from the **repository root** (where `lakefile.toml` is):

```bash
lake exe cache get    # optional: Mathlib build cache (acceptable per the comparator README if you trust the cache)
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory "$(pwd)" -- \
  bash -c 'lake env /path/to/comparator/.lake/build/bin/comparator comparator/config.json'
```

Runner conveniences (from the comparator release's own scripts): the binary reads `COMPARATOR_LANDRUN`,
`COMPARATOR_LEAN4EXPORT`, and `COMPARATOR_NANODA` if the tools are not on `PATH`; for a non-sandboxed trial run the
comparator checkout ships `scripts/fake-landrun.sh` (point `COMPARATOR_LANDRUN` at it) — a trusted run should use
landrun. Per-topic configs (`comparator/config-<topic>.json`, below) run the same way as `config.json`; each is
independent of the others. The Union and LineDecimal topics have completed this non-sandboxed pipeline, including
statement equality and acceptance by both nanoda and Lean's default kernel; exact versions and the trust qualification
are recorded in [`AUDIT.md`](../AUDIT.md).

Do not pre-build `Challenge`/`Solution` before a comparator run you want to rely on (comparator README,
assumption 2); let comparator build them in its sandbox. Success ends with `Your solution is okay!`.
The three `[[lean_lib]]` stanzas at the end of `lakefile.toml` (with `srcDir = "comparator"`) make the
modules `ChallengeDeps`, `Challenge`, `Solution` resolvable by those bare names, as comparator expects.

Version note: comparator adopts the *project's* toolchain (`lean --print-prefix` in the project directory),
so use a `lean4export` matching `../lean-toolchain`; if a much newer comparator binary rejects the export
(e.g. a kernel-primitive constant it expects is missing from this Lean version), build comparator from a
release of the same era as `../lean-toolchain`.

## Layout convention: one topic per file (how to add a theorem)

The base set is `Challenge.lean` / `Solution.lean` / `config.json` / `PrintAxioms.lean` (Theorems A–E, each at the
constant stated in the paper); these four files are not edited to add
results. Every further group of results is a **topic** with its own files:

| file | module | content |
|---|---|---|
| `comparator/Challenge/<Topic>.lean` | `Challenge.<Topic>` | `import Mathlib` only, with the definition layer (`ChallengeDeps.lean`, + `ChallengeDeps/<Topic>.lean` if needed) inlined verbatim as a complete block; the statements, each `:= by sorry` — **trusted** |
| `comparator/ChallengeDeps/<Topic>.lean` | `ChallengeDeps.<Topic>` | only if the statements need notions beyond `ChallengeDeps.lean`: Mathlib-only definitions, each a character-for-character copy of the corresponding definition in the Zeta23 statement layer (root namespace) — **trusted** |
| `comparator/Solution/<Topic>.lean` | `Solution.<Topic>` | the same statements byte-for-byte, proved by delegating to Zeta23 (may import `Solution` to reuse bridging lemmas such as `cStar_one_eq_cMT`) — untrusted |
| `comparator/config-<topic>.json` | — | `{"challenge_module": "Challenge.<Topic>", "solution_module": "Solution.<Topic>", "theorem_names": [...], "permitted_axioms": ["propext","Quot.sound","Classical.choice"], "enable_nanoda": true}` |
| `comparator/PrintAxioms/<Topic>.lean` | — | `import Solution.<Topic>` + one `#print axioms` per theorem |

Rules for the trusted side: (1) Mathlib only — never `import Zeta23…`; (2) theorem names in the root namespace, globally
unique and descriptive (`five_sixths_distinct`, not `thmC_mult`); (3) constants that Zeta23 carries as definitions
(`HD`, `GD`, `cStar`, window constants, …) are written out in closed Mathlib form in the challenge and bridged by a lemma on
the solution side; (4) statements are the ε-forms `∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c − ε)·N ≤ X` over the counting functions of
`ChallengeDeps`, with every hypothesis of the Zeta23 theorem (e.g. `1 < q`, `χ.IsPrimitive`) as an explicit binder;
(5) a statement enters a challenge file only when the Zeta23 theorem it delegates to is sorry-free with
`#print axioms` = the standard three; (6) a deps module contains exactly the definitions in the dependency closure of its challenge
statements — nothing is kept for parity or convenience, so every line a challenge auditor reads
is load-bearing. The lakefile needs no change: the three `[[lean_lib]]` stanzas with
`srcDir = "comparator"` cover the submodules `Challenge.*`, `Solution.*`, `ChallengeDeps.*`.
Check a topic with `lake build Solution.<Topic> && lake env lean comparator/PrintAxioms/<Topic>.lean`; run comparator with
`lake env /path/to/comparator comparator/config-<topic>.json`. This repository ships each topic's files together with the
Zeta23 import-closure of its `Solution/<Topic>.lean`; challenge and solution statements coincide textually, and every
`ChallengeDeps` definition is verbatim the corresponding definition of the Zeta23 statement layer.

Worked example: topic **XiPrime** (`Challenge/XiPrime.lean`, six statements about the zeros of ξ′, with its own
Mathlib-only definition layer in `ChallengeDeps/XiPrime.lean` and config `comparator/config-xiprime.json`).

Topics currently in the tree (each `config-<topic>.json` runs independently; the trusted files to read for a topic are
`ChallengeDeps.lean`, any `ChallengeDeps/<X>.lean` whose content its challenge inlines, and `Challenge/<Topic>.lean`):

| topic | what | trusted deps beyond ChallengeDeps.lean |
|---|---|---|
| Union | ζ: exact and certified-decimal simple-or-on-line inclusion-exclusion proportions, dyadic and cumulative (4) | — |
| LineDecimal | ζ: certified `0.672500703679` distinct-on-line and simple-on-line proportions, dyadic and cumulative (4) | — |
| Sextuple | ζ: sextuple-kernel improvement of the simple-on-line proportion, `0.672755620655` ε-form and fixed `0.6727556`, dyadic and cumulative (4); the numerical certificate is replayed in the kernel (`decide +kernel`) | — |
| SextupleA1275 | ζ: the refined sextuple certificate at `A = 51/4000`, simple-on-line proportion `0.6727837118`, ε-form and fixed, dyadic and cumulative (4); kernel replay of an 8,953-chunk exact certificate | — |
| SextupleA1285 | ζ: the refined sextuple certificate at `A = 257/20000`, simple-on-line proportion `0.6727949489`, ε-form and fixed, dyadic and cumulative (4); kernel replay of a 30,153-chunk exact certificate | — |
| SextupleA1290 | ζ: the refined sextuple certificate at `A = 129/10000` over the 666-model catalog, simple-on-line proportion `0.6728005676`, ε-form and fixed, dyadic and cumulative (4); kernel replay of a 56,924-chunk exact certificate | — |
| XiPrime | zeros of ξ′: all in the open critical strip; Re ξ′/ξ > 0 on Re s ≥ 1; ≥ 0.85838 simple and on the line, ≥ 0.92919 distinct (flat window), 0.86864 / 0.93432 (quartic window) (6) | ChallengeDeps/XiPrime.lean |

