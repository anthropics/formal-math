# Sextuple certificate: provenance, generators, audits, logs

Supporting material for the unconditional sextuple improvement
`Zeta23.ThmD.Sextuple.thmD₀_sextuple` (`0.67275562065609…`) and its kernel-checked
five-dimensional certificate `Zeta23.ThmD.Sextuple.Certificate.sextuple_affine`.
Nothing here is proof authority: the proof is the Lean code under `Zeta23/ThmD/Sextuple/`
and the axioms it depends on. These files let a reader regenerate the data modules and
re-run every external consistency check.

| path | content |
|---|---|
| `STATE.md` | design, measurements, hashes, and the completion record |
| `audits/` | independent read-only audits: non-certificate chain, generic affine tree, one-dimensional envelope, concrete tree/certificate layer, scalar adapter (with exact re-verification of all 871 certificates) |
| `macro-data-exact.json` | the exact 56-piece one-dimensional envelope (`Macro/EnvelopeData.lean` is generated from it) |
| `macro-envelope-data-generation-report.json` | envelope generation report |
| `macro-scalar-tree/` | the canonical serialized tree: packed topology, terminal kinds, anchors, term codes, the 871 scalar seam certificates, manifest and raw-byte verification report |
| `tools/serialize_macro_scalar_cache_tree.py` | exact-rational branch-and-bound that produced the tree (float coordinate descent proposes anchors only; every accepted leaf is an exact `Fraction` check) |
| `tools/verify_macro_scalar_tree.py` | independent serialized-only exact verifier of the streams |
| `tools/gen_packed.py` | deterministic generator of `Macro/TreeWords.lean`, `Macro/Chunks/ChunkNNNN.lean`, `Macro/Assembly/PartNNN.lean`, `Macro/TreeAssembly.lean` from the streams |
| `tools/decode_tree.py` | stream decoder used by the generator |
| `tools/verify_packed_words.py` | decodes the Lean literals of `Macro/TreeWords.lean` back to the four byte streams and compares SHA-256 with `macro-scalar-tree/manifest.json` |
| `tools/verify_scalar_adapter.py` | exact-rational replay of the Lean definitions of `Macro/ScalarAdapter.lean` on all 56 pieces / 871 certificates parsed from the Lean sources |
| `tools/forbidden_scan.sh`, `tools/run_audits.sh` | forbidden-construct scan and `#print axioms` audit runner |
| `regen/` | byte-for-byte regeneration of the envelope and scalar data modules from the JSON sources (see `regen/README.md`; the in-tree modules differ from the regenerated prototype files only in their `import` lines) |
| `logs/` | durable logs: clean from-scratch rebuild of the chain, scalar-data rebuild, comparator topic build, `#print axioms` outputs, audit report, scalar re-verification report |
| `a1275/` | the refined `A = 51/4000` certificate (`Zeta23/ThmD/Sextuple/A1275/`): canonical streams, refinement catalog, generators, two-level word tools, batched chunk build driver, manifests and independent audits — see `a1275/README.md` |

Regeneration / re-verification (Python 3, standard library only; run from this directory):

```bash
python3 tools/verify_macro_scalar_tree.py --data macro-data-exact.json --tree-dir macro-scalar-tree --report /dev/stdout
python3 tools/verify_packed_words.py ../../Zeta23/ThmD/Sextuple/Macro/TreeWords.lean
python3 tools/verify_scalar_adapter.py
python3 tools/gen_packed.py stats --max-tokens 100       # 2,969 chunks, 2,968 internal nodes
python3 tools/gen_packed.py data --out <dir>             # regenerates TreeWords.lean
python3 tools/gen_packed.py chunks --max-tokens 100 --out <dir>
python3 tools/gen_packed.py assembly --max-tokens 100 --group-size 100 --out <dir>
```

Building the chain: `LEAN_NUM_THREADS=10 lake build Zeta23.ThmD.Sextuple.LineDecimal`. Each `lean`
process loads ~6 GB of oleans and a chunk needs 1–3 GB of kernel working memory; Lake 5.0 has no `-j`,
so on machines with less than ~128 GB reduce `LEAN_NUM_THREADS`. The scalar-data module alone needs
~13 GB. A clean build of the whole chain took 73 minutes wall / 7.8 CPU-hours at ten builders.
