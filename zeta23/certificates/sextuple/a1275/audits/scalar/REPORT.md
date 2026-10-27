# Lean25 A=51/4000 scalar audit

## Verdict

**PASS** for the patched explicit-`Fin` scalar artifact. No remaining scalar-layer blocker.

The requested bare-`Fin` source `6791d1ff415bdabeb7feea0d534f04e293ca41d565d2935a2515ea2efd8ab7d0` was first reconstructed and checked exactly. That audit found that bare Lean numerals wrap modulo a `Fin` bound. The owner preserved that artifact under `superseded-scalar-bare-fin/` and replaced only its 2,979 `pieceIndex` encodings. The final source is `1ae4e940ffa5860768c7756ac4b60a0bde643db3140ad14c070f94e3a8a94adc` and uses `⟨index, by decide⟩` everywhere.

This verdict does **not** certify the downstream 5D tree. It certifies the combined catalog, scalar certificates, fail-closed source admission, and the scalar theorem dependency.

## Pinned and final inputs

| Input | SHA-256 |
|---|---|
| Combined catalog source | `04f0f5215abfa69fd00e83e25d7db6ce53aabdfa2c44c5b87019d60fd4d86652` |
| Original requested scalar source, superseded | `6791d1ff415bdabeb7feea0d534f04e293ca41d565d2935a2515ea2efd8ab7d0` |
| Patched scalar source, final | `1ae4e940ffa5860768c7756ac4b60a0bde643db3140ad14c070f94e3a8a94adc` |
| Scalar source JSON | `66264d3d9bc6cd0cde88f4d1bdb946ad3c8a64053d73d45a29176cdb8611dfe7` |
| Deterministic patched generator | `6ad0eedbd054b11f7fd387dbebf5878f5f9d201114fff948aaf75987fce29f08` |
| Patched generation report | `54ae911c3ff5dd59863b3126fbd2b6ed26cca30f68c40e807ae83adbfa22b3dd` |

The combined catalog and source JSON retained their requested hashes.

## Results

| Requirement | Result | Evidence |
|---|---|---|
| Catalog codes `0..271` | PASS | Parsed all 56 stable and 216 refinement declarations against exact JSON. Verified the stable/refinement tables, code order, final bounded cases, every catalog-check branch, and the two-level `i < 56` dispatch. |
| Scalar mapping and order | PASS | All 1,383 definitions, checks, table cases, and aggregate branches occur once and in order. All certificate intervals are unique. |
| Exact scalar arithmetic | PASS | Recomputed all 2,979 segments with `Fraction`. Verified every seam, strict interval order, piece containment, nonnegative weight, stored model minimum, `a <= minimum`, and `a = min(segment minima)`. Independent interval-image and clamped-center formulas agree on every segment. |
| Lean reconstruction | PASS | The patched generator copy reproduced `1ae4e940ffa5860768c7756ac4b60a0bde643db3140ad14c070f94e3a8a94adc` byte-for-byte from source JSON `66264d3d9bc6cd0cde88f4d1bdb946ad3c8a64053d73d45a29176cdb8611dfe7`. Removing the explicit constructors restores the superseded source byte-for-byte; exactly 2,979 lines differ. |
| Full aggregate check | PASS | Owner build and audit-local direct build both exit 0. Their 102,718,416-byte `.olean` files are byte-identical at `0d563050370f994bc59370878a6e75201a4cf26398f630781a08bc812472b14d`. |
| Fail-closed bounds | PASS after patch | Zero bare `pieceIndex` numerals remain. All 2,979 fields use proof-bearing constructors. Independent hostile replay rejects piece `272`, term-piece `272`, and scalar `1383`, exits 1, and creates no `.olean`. |
| Decoder admission | PASS | Exhaustively partitioned all 65,536 `UInt16` values: 272 piece, 1,383 scalar, one zero, and 63,880 rejected. All 2,872,110 stored term codes decode; none is invalid. This is admission/provenance evidence, not 5D theorem authority. |
| Refinement import delta | PASS | `ImprovedRefinementData.lean` differs from the independently audited source only in `import MacroEnvelopeData` becoming `import Zeta23.ThmD.Sextuple.Macro.EnvelopeData`. |
| Provenance | PASS | Generator `6ad0eedbd054b11f7fd387dbebf5878f5f9d201114fff948aaf75987fce29f08` and audit-local copy produced identical source and compact report. The pinned serialized exact replay also passes; it is classified only as source/mapping provenance. |
| Accepted axioms | PASS | `refinementTable_check`, `improvedCatalog_check`, `improvedScalarTable_check`, and `improvedConcreteLeafCheck_sound` report exactly `propext`, `Classical.choice`, and `Quot.sound`. |
| Forbidden scan | PASS | Zero hits for the forbidden set across the 18-file, 42,006-line project-local import closure. |
| Stable repository | PASS | Read-only, clean at `5e9617d84ece3aeecdf983a8e7e9bfa50f413e5a` before finalization. |

## Build evidence

### Owner patched build

- Source: `1ae4e940ffa5860768c7756ac4b60a0bde643db3140ad14c070f94e3a8a94adc`
- `.olean`: `0d563050370f994bc59370878a6e75201a4cf26398f630781a08bc812472b14d` (102718416 bytes)
- Log: `c88bca0a506eb1140e5fcb0a9309c79a4a5f3912d47b7615f204a7805f03aad3`
- Time: 240.08 seconds
- Maximum RSS: 20,147,191,808 bytes

### Audit-local direct rebuild

- Source: `1ae4e940ffa5860768c7756ac4b60a0bde643db3140ad14c070f94e3a8a94adc`
- `.olean`: `0d563050370f994bc59370878a6e75201a4cf26398f630781a08bc812472b14d` (102718416 bytes)
- Axiom stdout: `8ddb5ccd56c938282343b547293f71b35ebff8ba730e4f4b64c6d05fe51d98ba`
- Timing stderr: `7b1c89d32bd74fad5857875ea50b1b3e14c041b4548aef837ce1fc5df9631947`
- Time: 236.05 seconds
- Maximum RSS: 20,059,930,624 bytes

The direct rebuild passed after a recorded resource gate. It was not rerun.

## Primary audit artifacts

- Patched exact audit: `patched-exact-audit.json` — `ae63e636df5ad6371ddc0c4932e96da651e17acf609be1a33eb955120311e0d0`
- Full evidence: `FINAL-EVIDENCE.json` — `5c28ee69f83933637f8409e8b4b51f18edcc7ef6962574a25d01e9bf9985096a`
- Exact provenance replay: `provenance-replay/report.json` — `2585829b0afe59a33f1345dd17dad7a5fbca7f41abfc230bc2461c65abcdf308`
- Artifact/axiom probe stdout: `patched-lean-probes/PatchedArtifactAudit.stdout.log` — `12cacbb81184395328b562f32dc8df93d2629e305e1132f072d6a7a7e520979c`
- Hostile replay stderr: `patched-lean-probes/HostileOutOfRangeFinProbe.stderr.log` — `014a5801d1cd62c999f4ed35490fe2dbf9691daf991eb11b841d114bcee204fa`
- Audit-local `.olean`: `patched-native-rebuild/ImprovedScalarData.audit.olean` — `0d563050370f994bc59370878a6e75201a4cf26398f630781a08bc812472b14d`

## Authority boundary

The scalar theorem proves the 1D lower bounds used by scalar term references. The physical decoder admits only bounded references. Neither fact proves that a downstream serialized 5D tree exhausts its streams, checks every leaf, reconstructs the root, or yields the global target theorem. Those remain separate tree-authority obligations.
