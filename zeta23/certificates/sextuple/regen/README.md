# Regenerating the macro Lean data files from JSON

`regenerate_macro_lean_data.py` rebuilds three committed Lean sources byte-for-byte
from their JSON sources and verifies SHA-256 equality. Standard library only
(`argparse`, `fractions`, `hashlib`, `json`, `pathlib`); no network; deterministic;
the originals are never written.

```
cd <prototype dir>/bench/regen
/Users/mdumitrean/Desktop/dev/aigent/agi/.venv/bin/python regenerate_macro_lean_data.py --check
```

Output goes to `bench/regen/out/`. The JSON report lists, per file, the expected SHA-256,
the regenerated SHA-256, the byte length and PASS/FAIL; exit status is 0 only if all PASS.
`--root DIR` / `--out DIR` override the prototype directory and output directory.

| Target | Source | SHA-256 | Bytes |
|---|---|---|---|
| `MacroEnvelopeData.lean` | `macro-data-exact.json` (56 pieces) | `632d7214…26690b5` | 52,764 |
| `MacroScalarData.lean` | `macro-scalar-tree/scalar-certificates.json` (871 certs) | `532dc8f4…42e359` | 689,247 |
| `MacroScalarDataPrefix.lean` | same JSON, first 16 certs | `9c22df71…1492604` | 15,234 |

## Format rules recovered

### Rationals
JSON rationals are strings (`"2"`, `"475723/160000"`), already in lowest terms and never
negative. Integers are emitted bare (`0`, `2`, `59`); non-integers as `(num/den)`.
Boxes are `⟨lo, hi⟩`. Integer-valued `turn` / `piece_index` are emitted as plain ints.

### `MacroEnvelopeData.lean`
* JSON kind → Lean constructor:
  * `low`  → `.base { box := …, q := 0, a := A, c := 0, kind := .low }`
  * `zero` → `.base { …, kind := .zero }` (always `a := 0`)
  * `barrier` → `.base { …, kind := .numeric [` then one cell per line
    (6-space indent, `{ box := ⟨lo, hi⟩, turn := T }`, comma-separated) and a closing
    `    ] }` on its own 4-space-indented line.
  * `well` → `.well { box := …, side := .left|.right, positive := true|false, q := …, v := …, m := …, turn := T }`
  * `q := 0` and `c := 0` are constants for every base piece (not in the JSON).
* Per-piece `macroPieceN_check` lemma, `norm_num [macroPieceN, …]` with a simp list chosen by kind:
  * `low` / `zero`: `MacroPiece.check, LowerPiece.check` (one line).
  * `barrier`: `MacroPiece.check, LowerPiece.check, LowerPiece.coverFrom, LowerPiece.cellCheck, LowerPiece.cellModelUpper, LowerPiece.absLower, kernelRange, …, List.cons_ne_nil` (6 lines, exact text in `ENV_SIMP_NUMERIC`).
  * `well`: `MacroPiece.check, WellCert.check, WellCert.analyticPrereq, …, mtDenSecondRange, kernelRange, …, List.cons_ne_nil` (8 lines, exact text in `ENV_SIMP_WELL`).
* `macroPieces` list, `macroPieces_cover` (`macroCoverFrom LO HI`, `norm_num [macroPieces, macroCoverFrom, MacroPiece.box, macroPiece0, …]`),
  `macroPieces_all` (`simp [macroPieces, macroPiece0_check, …]`), `macroPieces_check`,
  `macroEnvelope_sound`. `LO`/`HI` (= `0`/`59`) are the first piece's `lo` and last piece's `hi`;
  the hypothesis name `hx59` is derived from `HI`.
* `#print axioms` trailer: `macroEnvelope_sound`, blank line, then `macroPiece0_check`,
  `macroPiece3_check`, `macroPieces_check`. The choice of pieces 0 and 3 is a fixed spot-check, not data-derived.
* No blank lines between consecutive piece defs or between consecutive check lemmas; one blank line between sections.

### `MacroScalarData.lean`
* `stableMacroTable (i : Fin 56)` is a `match i.val with` table `| k => macroPiecek` for
  k = 0..54 and `| _ => macroPiece55` for the last entry. Same `| _ =>` convention for
  `scalarCertTable (i : Fin 871)` (`| _ => scalarCert870`).
* `stableMacroTable_check` / `scalarCertTable_check`: `fin_cases i` followed by one
  `  · exact …_check` bullet per entry (`·` is U+00B7).
* Each `scalarCertN : MacroScalarCert 56 := { box := …\n  a := …\n  segments := [ … ]\n}`;
  segments are `{ box := ⟨lo, hi⟩, pieceIndex := K }` (4-space indent, comma-separated).
  The JSON `model_min` field is NOT emitted. Every cert def is followed by a blank line.
* **Per-certificate `norm_num` name list**: fixed head
  `scalarCertN, MacroScalarCert.check, MacroScalarSegment.check, scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage, RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box, wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable`
  followed by `macroPiece{piece_index}` for the certificate's segments **in segment order,
  first occurrence only**. On this data every certificate's `piece_index` sequence is
  strictly increasing with no repeats, so "in order, deduplicated", "sorted unique" and
  "raw sequence" all coincide (verified for all 871 certs); the script implements
  first-occurrence dedup.
* Trailer: blank, `/-- Deduplicated positive seam bounds, addressed by the serialized UInt16 term stream. -/`,
  `scalarCertTable`, blank, `set_option maxHeartbeats 0 in` / `set_option maxRecDepth 100000 in`,
  `scalarCertTable_check` (two-line signature), bullets, blank, two `#print axioms` lines, blank, `end …`.

### `MacroScalarDataPrefix.lean`
Same generator with the first 16 certificates and `with_table=False`: identical header,
`stableMacroTable`, `stableMacroTable_check`, `scalarCert0..15` defs and `scalarCert0..15_check`
lemmas, then directly a blank line and `end Zeta23.ThmD.Sextuple.MacroPrototype`. It has no
`scalarCertTable`, no `scalarCertTable_check`, and no `#print axioms` lines. Lines 1–280 are
byte-identical to the full file.
