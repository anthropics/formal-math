# Lean25 scalar adapter + 871 scalar certificates: independent audit

Date: 2026-08-22. Auditor: independent read-only pass (no `lake`, no `lean`, no edits in the Lean tree; Python exact-`Fraction` checks only).
Repository: `/Users/mdumitrean/Desktop/dev/aigent/math/prime/_exp_rh89_zeta23_lean` (HEAD `45ff289`, Lean `v4.33.0-rc2`).
Scope (handoff obligation "Independently audit MacroScalarAdapter.lean and all 871 scalar certificate checks"): the one-dimensional model layer
`Macro/ScalarAdapter.lean`, `Macro/AffineAdapter.lean`, `Macro/LeafCheck.lean`, `Macro/Layout.lean`, `Macro/ScalarData.lean` (structure), plus an exact re-derivation of all 871 `MacroScalarCert.check` instances from the JSON sources.
Trusted, not re-audited here: `Macro/Analytic.lean` (`WellCert.check_sound`, audited in `lean24c-macro-analytic-audit.md`), `PieceCert.lean` (`LowerPiece.check_sound`), `Interval.lean`, `AffineTree.lean` (`relativeRankTangentCheck_sound`, `rankObjective_le_energy_of_pairwise`), `Macro/EnvelopeData.lean` piece checks (`macroPieceN_check`).
Complements `lean25-concrete-certificate-static-audit.md` (tree/certificate layer).

Audited source hashes (SHA-256, identical to `bench/audit-report.txt` and to the bench copies `MacroScalarAdapter.lean`/`MacroAffineAdapter.lean`/`MacroScalarData.lean` modulo `import` lines):

| file | sha256 |
|---|---|
| `Macro/ScalarAdapter.lean` | `1908a966957c61555f16a0ce0c400a9712f199b0a453d9c9ef230c50696f1301` |
| `Macro/AffineAdapter.lean` | `61c2adce61a763582895d124eac67f37eb204a5844a19cca62b08a12994cb217` |
| `Macro/LeafCheck.lean` | `4923c164a493b6a1f89fec68889fbd85bb7d402a5adfef3159c40897080ad4ad` |
| `Macro/Layout.lean` | `a81a80f869716c2ef47580d97eb352b1ed7bb386692a772b00d4ee90d58893b9` |
| `Macro/ScalarData.lean` | `0b8d55345d942a11af83ca6ff6698c3c562eea360307f6091bd7433bced8bb7f` |
| `Macro/EnvelopeData.lean` | `44a3295dbf1eb76b5ae99263d282ac2397bc6b0953c8456632768476f25ee052` |
| `macro-scalar-tree/scalar-certificates.json` | `2d322e4a35f7c61ac093684f39503c76e4ac5ada8dbb9a95892aea1718e302e0` (= `manifest.json: scalar_certificates_sha256`) |
| `macro-data-exact.json` | `961a0281a134382f9c2678cc49487839d2b9c2cbd9df382871f2c7b706552a5b` (= `scalar-certificates.json: data_sha256`) |

## Verdict: PASS-WITH-NOTES

The key question is answered affirmatively: `MacroScalarCert.check table cert = true` together with `∀ i, (table i).check = true` implies `(cert.a : ℝ) ≤ 2 * mtKernel x ^ 2` for every real `x` with `Holds cert.box x` (`ScalarAdapter.lean:137-154`), and every link of that implication is a correct, kernel-checked proof whose hypotheses are exactly the Boolean conjuncts evaluated on the data. The exact Python re-derivation of all 871 certificates (1932 segments) from the JSON sources, using a literal reimplementation of the Lean definitions (`macroAffineOne -> scale/add -> absLower -> base + weight*absLower^2`), finds zero failures and zero mismatches between `ScalarData.lean` and the JSON. The notes are low-severity observations (one redundant hypothesis, tactic style, an inverted-interval corner that the proof already handles), none of which affects soundness.

## 1. ScalarAdapter.lean (line-by-line)

### 1.1 `AffineOneModel`, `macroAffineOne`, `macroAffineOne_value` (`:10-32`)
- `macroAffineOne (.base p) = ⟨p.a, p.c, 1, -p.q⟩`: `a + c*(1*x + (-q))^2 = a + c*(x-q)^2 = LowerPiece.model p x` (`PieceCert.lean:37`). Correct.
- `macroAffineOne (.well p) = ⟨0, 2, wellSlope p, wellOffset p⟩` with `wellSlope/wellOffset` from `AffineAdapter.lean:30-39`:
  - left: `slope = -m`, `offset = v + m*q`, so `slope*x + offset = v + m*(q - x)`; model `2*(v + m*(q-x))^2` = `WellCert.model` left branch (`Analytic.lean:493-496`). Correct.
  - right: `slope = m`, `offset = v - m*q`, so `slope*x + offset = v + m*(x - q)`; model `2*(v + m*(x-q))^2` = right branch. Correct.
- `macroAffineOne_value` (`:22-32`) proves the identity by `cases`, `simp only`/`simp` with the definitions, and `ring` in all three cases; this is a mechanically checked polynomial identity, so the sign/orientation question for wells is settled by the kernel, not by inspection. The generator's `Piece` conversion (`serialize_macro_scalar_cache_tree.py`, `read_pieces`: centre `q + v/m` for left, `q - v/m` for right, `c = 2m^2`) is the same quadratic expanded, consistent with the Lean model.

### 1.2 `affineOneImage`, `macroModelMin`, `macroModelMin_le` (`:35-62`)
- `affineOneImage m i = add (scale m.slope i) ⟨m.offset, m.offset⟩`. `RatInterval.scale` (`Interval.lean:28-29`) swaps endpoints for negative scalars, so for left wells (`slope = -m < 0`) the image is `[-m*hi + offset, -m*lo + offset]`, the correct enclosure; `holds_scale` (`Interval.lean:55-63`) proves both signs.
- `macroModelMin p i = base + weight * absLower(image)^2` with `LowerPiece.absLower` (`PieceCert.lean:39-40`): `lo` if `0 ≤ lo`, `-hi` if `hi ≤ 0`, else `0`, i.e. the distance from `0` to the interval. `absLower_le_abs` (`PieceCert.lean:70-79`) gives `absLower(image) ≤ |slope*x + offset|`; `absLower_nonneg` (`:66-68`) lets `pow_le_pow_left₀` square the inequality; `hweight : 0 ≤ weight` lets it multiply. The lemma then rewrites the target through `macroAffineOne_value`. This is a true lower bound of `p.model x` over `Holds i x` for every `x`, with no ordering hypothesis needed on `i` (an empty `i` makes `Holds` vacuous).
- Note the weight sign is decided *inside* `MacroScalarSegment.check` (`:77`) rather than being imported from `LowerPiece.check`'s `0 ≤ p.c` (`PieceCert.lean:59`), so `macroModelMin_le` does not depend on the table check at all. Well weight is the literal `2`.

### 1.3 `MacroScalarSegment.check` / `check_sound` (`:65-90`)
Five conjuncts: `s.lo ≤ s.hi`, `piece.box.lo ≤ s.lo`, `s.hi ≤ piece.box.hi`, `0 ≤ weight`, `a ≤ macroModelMin piece s.box`. `check_sound` uses only the last two (`hweight`, `ha`) and concludes `(a : ℝ) ≤ piece.model x` for `Holds s.box x` via `exact_mod_cast` + `macroModelMin_le`. Correct; the containment conjuncts are consumed later (1.5).

### 1.4 `scalarSegmentsCoverFrom` / `_sound` (`:93-119`): closed-seam coverage
- Bool: `[] ↦ cur = last`; `s :: ss ↦ s.lo = cur ∧ s.lo ≤ s.hi ∧ coverFrom s.hi last ss`. So the segments tile `[cur, last]` exactly: first `lo = cur`, each `lo` equals the previous `hi`, final `hi = last`.
- Proof (induction generalising `cur`): after `subst cur`, if `x ≤ s.hi` the head segment holds `x` (lower bound from `hxlo`). Otherwise, if `ss = []` then `s.hi = last` contradicts `x ≤ last`; if `ss = next :: rest`, the IH applies with `cur := s.hi`, `hxlo := le_of_not_ge hx`, and `hne` discharged by `by simp`. The shared seam point `x = s.hi` is caught by the head segment (`x ≤ s.hi` is non-strict), so closed seams are handled and no point of `[cur,last]` falls through. Correct. Textually identical in structure to the already-audited `macroCoverFrom_sound` (`Analytic.lean:669-688`) and `LowerPiece.coverFrom_sound` (`PieceCert.lean:81-99`).

### 1.5 `MacroScalarCert.check` / `check_sound` (`:122-156`)
`check = lo ≤ hi ∧ 0 ≤ a ∧ segments ≠ [] ∧ coverFrom lo hi segments ∧ segments.all (Segment.check table a)`. `check_sound`: from `Holds cert.box x`, 1.4 yields a segment `s` holding `x`; the segment's containment conjuncts (cast to ℝ) give `Holds (table s.pieceIndex).box x`; then `(a : ℝ) ≤ piece.model x` (1.3) `.trans` `MacroPiece.check_sound (htable s.pieceIndex) hpiece` (`Analytic.lean:653-657`) gives `≤ 2 * mtKernel x ^ 2`. This is exactly the claimed implication. Hypotheses `_hord`, `_ha` are unused (see F1).

### 1.6 `scalarRankModel`, `macroScalarTerm`, `macroScalarTermsFit` (`:171-199`)
- `scalarRankModel a = ⟨a, 0, 0, fun _ => 0⟩`; `RankOneModel.value` (`AffineTree.lean:293-295`) evaluates to `a + 0*(0+0)^2 = a`; the soundness proof closes it with `simpa [..., RankOneModel.value, RankOneModel.dot]` (`:279-280`). Weight `0` satisfies the `∀ p, 0 ≤ weight` conjunct of `relativeRankTangentCheck` (`AffineTree.lean:993`).
- `.piece i ↦ macroPieceRankModel (fun _ => table i) p`, whose value is `(table i).model (gapDistance g p)` by the `@[simp]` lemma `macroPieceRankModel_value` (`AffineAdapter.lean:59-68`).
- `macroScalarTermsFit` is `by classical; exact decide (...)`; it is only a Prop carrier here, the kernel-reducible replacement is in LeafCheck (section 3).

### 1.7 `macroScalarDyadic14LeafCheck_sound` (`:213-284`)
Mirror of `macroOptionalDyadic14LeafCheck_sound` (section 2.3) with the three-way `MacroTermRef` split. Verified: (a) `hg0` from `∀ i, 0 ≤ box.lo i`; (b) tail case `A6 ≤ B6 * span` closes with `sextupleEnergy_nonneg`; (c) otherwise `span < macroCutoff`, and for every `p`, `gapDistance g p ≤ span` (subset sum of nonnegatives, `Finset.sum_le_sum_of_subset_of_nonneg`) so `gapDistance` lies in `clippedDistanceInterval`; fit conjuncts transport it into the piece/scalar box; `MacroPiece.check_sound` / `MacroScalarCert.check_sound` give the pairwise bound; `relativeRankTangentCheck_sound` + `rankObjective_le_energy_of_pairwise` finish. The scalar case passes the *same* `table` to `MacroScalarCert.check_sound htable (hscalars i)`, so the scalar certificates are only ever used with the table they were checked against; `TreeReader.lean:80-87` instantiates both with `stableMacroTable`/`scalarCertTable` and `stableMacroTable_check`/`scalarCertTable_check`, and `scalarCertTable_check` is stated against `stableMacroTable` (`ScalarData.lean:13391-13392`).

## 2. AffineAdapter.lean

### 2.1 `wellRankModel`, `macroPieceRankModel(_value)` (`:42-68`)
`wellRankModel piece p = ⟨0, 2, wellOffset piece, fun i => wellSlope piece * consecutiveCoeff p i⟩`; `wellRankModel_dot` (`:54-57`) reduces the dot product to `wellSlope * gapDistance g p` through `scaledConsecutive_dot` (`:19-28`, which piggybacks on `lowerPieceRankModel_dot` with a dummy `zeroLowerPiece`, a legitimate trick). `macroPieceRankModel_value` then closes both well orientations by `simp ... <;> ring`, the same identity as 1.1 in five variables. Correct.

### 2.2 `clippedDistanceInterval` and `macroCutoff` (`:165-166, :189-191`)
- `macroCutoff = 62500000 / 1094977`. Exact check: `A/B = (1/80) / (1094977/5000000000) = 5000000000/(80*1094977) = 62500000/1094977`. Verified equal in Python (`macroCutoff_equals_A_over_B: true`); the Lean proofs re-derive it with `norm_num [A6, B6, macroCutoff]` (`:269`, `ScalarAdapter.lean:233`), so a typo would have failed elaboration.
- `clippedDistanceInterval cutoff box p = ⟨(distanceInterval box p).lo, min (distanceInterval box p).hi cutoff⟩`. It can be an inverted interval when the lower partial sum exceeds the cutoff (see F3); the soundness proof never needs it ordered.

### 2.3 `macroOptionalDyadic14LeafCheck_sound` case split (`:252-284`)
`by_cases htail : A6 ≤ B6 * sextupleSpan g`. Tail branch: `affineEnergyGoal (1/80) (1094977/5000000000) g` unfolds to `(1/80 : ℚ) ≤ energy + (1094977/5000000000 : ℚ) * span`; with `energy ≥ 0` and `htail` (after `norm_num [A6, B6]`) `linarith` closes. Other branch: `¬(1/80 ≤ 1094977/5000000000 * span)` gives `span < 62500000/1094977` by `nlinarith` after `norm_num`; then `clippedDistance_holds_selected` (`:222-249`) does exactly the transport described in 1.7(c), and the `none` case is `zeroRankModel` with value `0 ≤ 2*k^2` by `positivity`. The split is exhaustive (classical `by_cases`) and both branches reach the same goal. Correct.

## 3. LeafCheck.lean
Re-confirmed (previously F3 of the static audit): `termRefFits` (`:20-30`) is the explicit Bool form of the three match arms of `macroScalarTermsFit` (`ScalarAdapter.lean:195-199`); `leafTermsFit` decides `∀ p : Fin 15`; `decideEqTrueOf` (`:50-53`) handles *any* `Decidable` instance by `cases inst`, so the classically chosen instance inside `macroScalarTermsFit` is not an obstacle; `macroScalarTermsFit_of_leafTermsFit` (`:56-76`) does `unfold; refine decideEqTrueOf ?_; intro p; split` and discharges each arm from `termRefFits ... = true`; `macroScalarDyadic14LeafCheck_of_fastLeafCheck` (`:79-88`) rebuilds the conjunction; `fastLeafCheck_sound` (`:91-100`) composes with 1.7. The fast check has the same first and third conjuncts (`decide (∀ i, 0 ≤ box.lo i)`, `relativeRankTangentCheck 16384 (1/80) (1094977/5000000000) ...`) as the prototype. Sound.

## 4. Layout.lean
- `allBelow_sound` (`:25-32`): structural recursion on the list, `List.mem_cons` split. Correct.
- `topologyLayoutBool_sound` (`:47-62`): target `PackedTopologyLayoutValid` is exactly `AffineTree.lean:700-705` (size `(tokenCount+19)/20`, all words `< 2^60`, `tokenCount % 20 = 0 ∨ ∃ word, words[tokenCount/20]? = some word ∧ word < 2^(3*(tokenCount%20))`). `finalWordBelow` (`:35-38`) returns `false` on `none`, so `split at hf` + `simp at hf` kills the `none` branch and the `some w` branch yields the witness. Correct.
- `leafLayoutBool_sound` (`:80-95`): same shape against the locally defined `PackedLeafLayoutValid` (`:65-70`, with `leafWordBits = 321`, `leafBlockSize = 256` from `TreeReader.lean:30-33`). Correct; non-load-bearing for `sextuple_affine` (static audit F8).

## 5. ScalarData.lean (structure, 14,269 lines, 689 KB)
- `stableMacroTable : Fin 56 → MacroPiece` (`:10-68`): `match i.val with | 0 => macroPiece0 ... | 54 => macroPiece54 | _ => macroPiece55`. Arms verified programmatically: `k ↦ macroPiecek` for `k = 0..54`, wildcard `↦ macroPiece55` (only `55` reaches it for `Fin 56`).
- `stableMacroTable_check` (`:69-127`): `fin_cases i` then 56 `· exact macroPiecek_check` in order `0..55` (verified).
- `scalarCertN : MacroScalarCert 56` for `N = 0..870` (`:129-8156`): `{ box := ⟨lo, hi⟩, a := ..., segments := [ { box := ⟨lo, hi⟩, pieceIndex := k }, ... ] }`; 871 definitions, 2-4 segments each.
- `scalarCertN_check` (`:8158-12512`): 871 lemmas, every one the same script `norm_num [scalarCertN, MacroScalarCert.check, MacroScalarSegment.check, scalarSegmentsCoverFrom, macroModelMin, macroAffineOne, affineOneImage, RatInterval.scale, RatInterval.add, LowerPiece.absLower, MacroPiece.box, wellSlope, wellOffset, List.cons_ne_nil, stableMacroTable, macroPiece_i, ...]`; verified programmatically that lemma index = cert index in all three positions and that the listed `macroPiece` constants are exactly the piece indices used by that certificate's segments (871/871).
- `scalarCertTable : Fin 871 → MacroScalarCert 56` (`:12515-13387`): arms `k ↦ scalarCertk` for `k = 0..869`, `_ ↦ scalarCert870` (verified). `scalarCertTable_check` (`:13389-14264`): `fin_cases i` + 871 `· exact scalarCertk_check` in order (verified). `#print axioms` at `:14266-14267`.
- Forbidden-construct scan over the five audited files + `EnvelopeData.lean` + `Analytic.lean`: no `sorry|admit|axiom|native_decide|ofReduceBool|unsafe|implemented_by|partial|opaque|extern` (only the docstring word "padding" in `Layout.lean:34`).
- Build evidence (not re-run by me, read-only mandate): `.lake/build/lib/lean/Zeta23/ThmD/Sextuple/Macro/ScalarData.olean` (64.8 MB, 16:19, after the 16:16 source); `bench/audit-report.txt` (`lake env lean AxiomAudit.lean`) and seven build logs record `'...scalarCertTable_check' depends on axioms: [propext, Classical.choice, Quot.sound]` and the same for `stableMacroTable_check`, with file hashes equal to those audited here. `MacroScalarData.rebuild.build.log`: 108 s wall, 12.9 GB peak RSS for the standalone module.

## 6. Independent exact re-verification (Python, `fractions.Fraction`)

Script: `checkers/lean-sextuple-certificate-prototype/bench/audit2/verify_scalar_adapter.py`; output `verify_scalar_adapter_report.json`. Elapsed: **0.09 s**. It parses `EnvelopeData.lean` (56 `macroPieceN` literals) and `ScalarData.lean` (871 `scalarCertN` literals, both tables, both `fin_cases` scripts, all 871 lemma headers) directly from the Lean text, then reimplements `RatInterval.scale/add`, `LowerPiece.absLower`, `wellSlope/wellOffset`, `macroAffineOne`, `affineOneImage`, `macroModelMin`, `MacroScalarSegment.check`, `scalarSegmentsCoverFrom`, `MacroScalarCert.check` literally (not the generator's `model_min`).

| check | result |
|---|---|
| `macroPieceN` (Lean) vs `macro-data-exact.json` pieces[N]: box, kind, `a`, `c`, `q`, cells/turns, well `side/positive/q/v/m/turn` | 56/56 match; envelope tiles `[0, 59]` with shared endpoints |
| `stableMacroTable` arms / `stableMacroTable_check` order | ok / ok |
| `scalarCertN` (Lean) vs `scalar-certificates.json` certificates[N]: box, `a`, segment boxes, `piece_index` | 871/871 match, 0 mismatches |
| `scalarCertTable` arms / `scalarCertTable_check` order / lemma headers and simp sets | ok / ok / 871 ok |
| (i) segments tile `[lo, hi]` with closed seams (`scalarSegmentsCoverFrom`) | 871/871 |
| (ii) each segment inside its piece's box | 1932/1932 |
| (iii) `a ≤ macroModelMin(piece, segment)` via Lean definitions | 1932/1932 |
| `0 ≤ weight` | 1932/1932 |
| (iv) `a > 0`; `lo ≤ hi` | 871/871; 871/871 |
| full `MacroScalarCert.check` replay = `true` | **871/871, 0 failures** |
| `macroCutoff = A/B` exactly | true (`62500000/1094977`) |

Additional facts (informational): 1932 segments total (1352 on well pieces, 580 on base pieces; 2-4 per certificate); every segment is the full intersection of the certificate box with its piece box; every certificate has `hi ≤ A/B`; in every certificate `a` equals the minimum of `macroModelMin` over its segments exactly (minimum slack `0`, attained at exactly one segment per certificate; the check is `≤`, so equality is fine and there is no rounding anywhere); `a` ranges over `[9576976453294042395280846609/8e34 ≈ 1.197e-7, 14630385677/1e12 ≈ 0.01463]`; the JSON `model_min` field (computed by the generator's clamp formula) coincides with the Lean `macroModelMin` on all 1932 segments, which is expected algebraically (distance from `0` to the affine image = `|slope|` times the distance from the well centre) but is not consumed by Lean.

## 7. Numbered findings

### F1 (Low, no soundness impact): redundant conjunct `0 ≤ cert.a`
`MacroScalarCert.check` decides `0 ≤ cert.a` (`ScalarAdapter.lean:132`) but `check_sound` discards it (`_ha`, `:142`), and nothing downstream needs it (`scalarRankModel` has weight `0`, so the tangent checker's weight test is independent of `a`). Harmless over-checking; all 871 values are in fact positive. Could be dropped or documented as a sanity guard.

### F2 (Info): proofs are `norm_num`, not `decide +kernel`
The 871 `scalarCertN_check` lemmas and the 56 `macroPieceN_check` lemmas are closed by `norm_num [...]` with an explicit simp set. The produced proof terms are still kernel-checked and the logged `#print axioms` is `[propext, Classical.choice, Quot.sound]`, so this is a style/robustness remark only: the scripts depend on `norm_num`/`simp` successfully unfolding the `match` in `stableMacroTable` on a `Fin` literal and on `Rat` normalisation, and they are heavier (12.9 GB peak RSS for the module) than a `decide +kernel` on a computable `Bool` would be. Not a soundness concern.

### F3 (Info): `clippedDistanceInterval` may be inverted; proof already covers it
If `(distanceInterval box p).lo > macroCutoff` then `clippedDistanceInterval` has `lo > hi`. The soundness proofs (`AffineAdapter.lean:241-249`, `ScalarAdapter.lean:245-250`) only ever derive `Holds clipped (gapDistance g p)` from `hd.1` and `le_min hd.2 hcut`, which is consistent because in the non-tail branch `gapDistance ≤ span < cutoff`; and if some partial lower sum exceeds the cutoff then `B6 * span ≥ A6` for every `g` in the box and the tail branch fires. No action needed; a fit check passing on an inverted interval cannot be exploited.

### F4 (Info): well orientation is kernel-verified, not inspected
The question "is the sign of `wellSlope`/`wellOffset` right for `WellCert.model`?" is answered by `macroAffineOne_value` (`ScalarAdapter.lean:22-32`) and `macroPieceRankModel_value` (`AffineAdapter.lean:59-68`), both closed by `ring` after unfolding; the Python reimplementation reproduces the same expansion and all 1352 well segments pass. The `WellCert.check`/`check_sound` orientation logic itself (`q = box.hi` for left, `q = box.lo` for right; `derivativePositive = !positive` on the left) lives in `Analytic.lean` and was audited in `lean24c-macro-analytic-audit.md`; nothing in the adapter layer re-interprets it.

### F5 (Info): `MacroScalarSegment.check` does not (and need not) select the "right" piece
Any table piece whose box contains the segment is acceptable; soundness needs only containment plus `(table i).check = true`. The data in fact always uses the unique envelope piece containing the segment (every segment equals the full intersection with that piece's box).

### F6 (Info): provenance
The Sextuple tree is now committed (`45ff289`), which resolves the static audit's F9 pinning note. The working tree has uncommitted edits relative to HEAD in `Zeta23/ThmD/Sextuple/LineDecimal.lean` (4 lines) and `Macro/TreeReader.lean` (working-tree sha256 `c97d8d9c5614dbd3f19fe34cd23b25dc813e04ca43885f9b20b5b173c388178e` vs `59ba89aa...` in `bench/audit-report.txt`); `git diff HEAD` for `TreeReader.lean` shows only the deletion of the unused `packedLeafLayoutCheck` (the static audit's F8 cleanup) and a docstring edit, so the `concreteLeafCheck`/`concreteLeafCheck_sound` wiring cited above (`:80-87` in the working tree) is unchanged. The `#print axioms` evidence in `bench/audit-report.txt` predates these two edits and should be regenerated once they are committed. All five in-scope files and `EnvelopeData.lean` are unmodified relative to HEAD and hash-identical to `bench/audit-report.txt`.

## 8. Answers to the stated questions
1. Does `MacroScalarCert.check table cert = true` plus `∀ i, (table i).check = true` imply `cert.a ≤ 2 * mtKernel x ^ 2` on `cert.box`? **Yes** (sections 1.3-1.5); re-verified on all 871 instances (section 6).
2. Closed-seam coverage (`scalarSegmentsCoverFrom_sound`): **correct**; the head segment absorbs seam points (1.4), and the data tiles every certificate box exactly (871/871).
3. `macroModelMin` a true lower bound: **yes** via `absLower_le_abs` on `affineOneImage` and `pow_le_pow_left₀` with `0 ≤ weight` decided in the check (1.2); 1932/1932 segments satisfy `a ≤ macroModelMin`.
4. Well sign/orientation: **consistent**, proved by `ring` in `macroAffineOne_value` (F4).
5. `macroCutoff = 62500000/1094977 = A/B` **exactly** (2.2); the `A6 ≤ B6 * span` case split is exhaustive and both branches are correct (2.3, 1.7).
6. `ScalarData.lean` matches the JSON: **871/871 certificates, 56/56 pieces, zero mismatches**; table arms and `fin_cases` orders are in sequence.
