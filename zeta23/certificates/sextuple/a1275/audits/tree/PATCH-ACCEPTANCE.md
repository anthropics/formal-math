# Patched generator acceptance criteria

Candidate scope: replacement for pinned `generate_improved_tree_artifacts.py` SHA256 `7c629e908828bb0bac67e99d71f689704d8a406bc4e7c77ad962dcad8418ff52`.

The frozen correct inputs and outputs remain the oracle. The patch must not change certificate data, the bounded plan, or emitted Lean source.

## Required successful replays

Run an audit-local route-only clone against the frozen `refined-A-0p01275` inputs under both:

1. `/Users/mdumitrean/Desktop/dev/aigent/agi/.venv/bin/python`
2. `/Users/mdumitrean/Desktop/dev/aigent/agi/.venv/bin/python -O`

Both runs must exit 0. Normal and optimized runs must be byte-identical to each other. Each of these outputs must also be byte-identical to the pinned frozen output:

- `tree-artifacts/leaf-blocks-10272le.bin` (`a0f816354c1505d96960038ced115f0c777348c0dca0a3759fdf56cad067b365`)
- `tree-artifacts/bounded-replay-plan.json` (`e33c363129cc0d2b00480a04e914a1977680265994f1bd7cd7e6fae068aeccf5`)
- `ImprovedTreeWords.lean` (`0cfb2ab70bff047ab462e59353f8ab7527ddd36fadbf0e571e34b9f8a43add39`)
- `ImprovedLayout.lean` (`c8d6874294bb87cc6309d372f2a3c5f8b08a9dd63df7b849f65045eda340fb2f`)
- `ImprovedChunkCalibration.lean` (`c286e835992b2bf5519f50ad7546695f028d5490a8ab2b7a829bdb194403f239`)
- all 31 `ImprovedWordData/ImprovedLeafBlocksNNN.lean` modules, using the pinned hash map in frozen `generation-report.json`

The successful report may differ from pinned `generation-report.json` only where it records the patched generator SHA. After substituting the candidate SHA for `generator_sha256`, the report must otherwise equal the pinned report exactly and remain canonical JSON with status `PASS`.

## Required hostile rejections

Run every case under both normal Python and `python -O`. Each must exit nonzero before a PASS report can be published:

- manifest hash mismatch and wrong A/B/cutoff/count/fuel/depth fields
- topology hash mismatch; missing/extra word; code 6; code 7; a 60th-or-higher bit; nonzero final padding slot
- missing/extra kind byte; kind 2
- missing/extra anchor halfword; anchor 16385 (one past resolution)
- missing/extra term halfword; term codes 272, 32767, 34151, and 65534
- topology that closes early, has a second root, or ends with an open split
- kind/payload underflow or overflow
- nonzero leaf padding or an extra/missing leaf block if fed back through validation
- a plan mutation with an invalid path side, axis 5, bad cursor edge, duplicate child reference, forward/cyclic node reference, missing chunk, or duplicate token coverage

It is acceptable for a pinned hash gate to reject a whole-file mutation first. At least one audit harness must inject matching test pins or call the candidate validation functions directly so the semantic range checks themselves are exercised in both modes.

## Report atomicity and stale-PASS test

For both normal and optimized mode:

1. Complete a correct PASS run in an audit-local work directory.
2. Preserve that directory, replace its input with hostile data, and rerun.
3. Require nonzero exit.
4. Require that no prior `generation-report.json` with status `PASS` remains authoritative. The report must be absent or atomically replaced by a `FAIL`/`INCOMPLETE` report tied to the hostile input and candidate SHA.
5. Require no report `.new`/staging file and no partially written PASS report after exit.

The candidate must publish `generation-report.json` only after every output is complete and rehashed. Report publication must use write-to-sibling plus `os.replace` (or an equivalent same-filesystem atomic replace). It must invalidate/remove a prior PASS report before starting a new attempt.

## Static and Lean checks

- No acceptance-critical validation may depend on Python `assert`. A full absence of `assert` is preferred and is the simplest auditable rule.
- Every emitted path axis remains `⟨n, by decide⟩`; no bare numeric `Fin 5` literal is allowed.
- The audit-local hostile `Fin 5` one-past probe must fail with `5 < 5` and create no `.olean`.
- Candidate source, both successful run reports, hostile matrix report, and all logs must receive SHA256 inventory entries.

Passing these criteria repairs generator fail-closed behavior. It does not by itself confer full Lean replay authority, which still requires inspection of every owner chunk/assembly/root build log and artifact.
