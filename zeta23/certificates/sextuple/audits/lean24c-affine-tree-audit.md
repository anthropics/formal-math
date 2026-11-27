# Independent audit: `AffineTree.lean`

## Verdict

- **Generic trusted module: PASS.** No Lean patch is required for the audited snapshot.
- **Concrete certificate/data layer: OPEN.** This module does not discharge the concrete packed-payload decoder, baseline terminal-code adapter, macro affine-well adapter, or an actual serialized-tree check. Those are blockers to a concrete certificate claim, not defects in the generic soundness layer.

## Audited snapshot and scope

- Repository: `/Users/mdumitrean/Desktop/dev/aigent/math/prime/_exp_rh89_zeta23_lean`
- Target: `Zeta23/ThmD/Sextuple/AffineTree.lean`
- Audited SHA-256: `64a198e5042931f3785c440a78722e9b3f8e62cdd4843854b0acc3f470722eb3`
- The hash was checked before review and again after all commands. No Lean source was edited.
- Read in full: `AffineTree.lean` and its project-local import closure through the Mathlib boundary: `PieceCert.lean`, `Energy.lean`, `KernelInterval.lean`, `Kernel.lean`, `TrigInterval.lean`, and `Interval.lean`.

## Independent verification

- Direct elaboration passed:
  - `/Users/mdumitrean/.elan/bin/lake env lean Zeta23/ThmD/Sextuple/AffineTree.lean`
- Targeted module build passed:
  - `/Users/mdumitrean/.elan/bin/lake build Zeta23.ThmD.Sextuple.AffineTree`
  - Result: `Build completed successfully (8703 jobs).`
- `#print axioms` passed for all 56 public lemmas/theorems in `AffineTree.lean` and 17 imported load-bearing interval/kernel/piece theorems. Every declaration used a subset of the accepted set, and the union was exactly `[propext, Classical.choice, Quot.sound]`.
- An anchored forbidden-construct scan over all seven reviewed files was empty for `sorry`, `admit`, source `axiom`, `unsafe`, `partial`, `opaque`, `extern`, `native_decide`, `ofReduceBool`, `sorryAx`, and `implemented_by`.
- Lean reduction probes, using `decide`/`norm_num` rather than `native_decide`, passed for the pair table, the exact span-59 margin, all eight topology codes, canonical packed-layout edge cases, malformed/truncated/trailing streams, fuel failure, exact cursor exhaustion, and left-to-right child/payload threading.

## Seam audit

### Fifteen pairs, orientation, and distance intervals

- `pairLeft`/`pairRight` reduce to exactly
  `[(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]`.
  Thus there are no duplicates or omissions among the 15 unordered pairs.
- `gapSupport` is the adjacent-index interval `[pairLeft, pairRight)`. `gapDistance_eq_position_sub` proves that its sum is the right position minus the left position.
- `sextupleGram` uses left minus right. `mtKernel_gapDistance_eq_pair` applies the proved evenness of `mtKernel`, so the orientation reversal is sound before squaring.
- `pairKernelEnergy_eq_sextupleEnergy` proves the exact factor-2/off-diagonal identity, not only a bound.
- `distanceInterval` sums precisely the participating lower and upper gap endpoints. `distanceInterval_holds` proves both casted real inequalities, and `lowerPiecesFit` uses the correct containment direction: piece lower endpoint below the distance lower endpoint and distance upper endpoint below the piece upper endpoint.

### Span tail and global reduction

- `sextupleEnergy_nonneg` follows from the sum-of-squares definition.
- The span-59 closure has positive exact margin
  `B6 * 59 - A6 = 2103643 / 5000000000 > 0`.
  Therefore energy nonnegativity plus `span ≥ 59` suffices.
- In the complementary branch, nonnegative gaps imply each gap is at most their sum, so `span < 59` places the point in `[0,59]^5`. The equality case `span = 59` is handled by the tail branch. The premise `∀ i, 0 ≤ g i` remains explicit in the global theorem.
- The cube root is stronger than the span simplex, so this reduction is sound. Whether a concrete tree successfully certifies the whole cube is a separate data check.

### Affine-square tangent/SOS and lower-piece adapter

- `RankOneModel.value_tangent_sos` is the exact identity for
  `base + weight * (coeff·x + offset)^2`. `rankObjective_tangent_sos` sums it and adds the exact `B * span` derivative.
- Arbitrary rational bases are valid. Nonnegative weights are the only PSD condition needed for the SOS remainder, and both tangent checkers test every weight.
- `affineCoordinateLower` chooses the lower endpoint for a nonnegative slope and the upper endpoint for a negative slope. Its cast proof has the correct inequality reversal for a nonpositive multiplier.
- `rankTangentLower_sound` retains the nonnegative weighted squares. All rational-to-real casts for objectives, gradients, products, sums, and offsets are exact.
- `lowerPieceRankModel` uses `base = a`, `weight = c`, `offset = -q`, and the `0/1` distance-incidence vector. Its dot and value theorems prove exact agreement with `a + c*(distance-q)^2`.
- The standalone checked leaf verifies every selected `LowerPiece.check`, interval fit, box order, anchor membership, all weights, and the final rational tangent inequality. It therefore has no analytic table premise.

### Midpoints, recursion, cursors, and exhaustion

- Both midpoint children are closed. Parent membership implies membership in at least one child, and equality with the midpoint implies membership in both.
- The reverse child-to-parent lemmas correctly require ordered parent endpoints. Tree soundness only needs the parent-to-child coverage direction.
- `fuel` is an explicit depth bound. A split decrements it once and supplies the same remaining depth bound independently to both children. Fuel zero, including at either child, fails.
- Replay starts the left child after the split token, then threads both returned cursors into the right child. Terminals advance one topology cursor and one payload cursor.
- Out-of-range or missing reads fail. Codes 6/7 decode to `none`; malformed visited tokens therefore fail. Truncated topology or payload streams fail.
- `checkAffineTree` accepts only the exact final pair `(topology.length, payloads.length)`. Extra logical topology or payload entries therefore fail, including malformed entries trailing a complete prefix tree.

### Three-bit packing and physical canonicality

- The generic topology code is explicitly `0 = terminal`, `1..5 = split axes 0..4`, and `6/7 = invalid`. Bit extraction is little-endian in 20 three-bit slots per word.
- `packedTopologyLayoutCheck` now enforces all physical topology conditions:
  1. exactly `(tokenCount + 19) / 20` words;
  2. every word `< 2^60`;
  3. for a partial last word, value `< 2^(3 * (tokenCount % 20))`, which forces every unused high slot to zero.
- Edge cases `tokenCount = 0`, exact multiples of 20, a one-token partial word, an extra word, a `2^60` word, and nonzero final high padding reduce as intended.
- `packedTopologyStream` remains a raw constructor, while `checkedPackedTopologyStream` is the canonical checked constructor. Raw physical noncanonicality cannot invalidate the logical soundness theorem, but a concrete canonical-serialization claim must use the checked path or prove the same layout predicate.

### Payload kinds, compact boxes, and anchors

- Topology contains only terminal versus split. `AffineLeafPayload` separately and exhaustively selects `tail` or `quadratic`, and `affineLeafCheck` dispatches to the corresponding sound checker. There is no generic payload-kind confusion.
- `SharedDenomGapBox.check` requires a positive natural denominator and ordered integer numerators. `check_sound` proves exact rational endpoint order after division by that positive denominator.
- `RelativeAnchor.check` requires positive resolution and coordinates in `[0,resolution]`. Decode is exact interpolation `lo + coordinate/resolution * (hi-lo)`. `decode_holdsRat` proves inclusion for every ordered box, including both endpoints. The documented intended concrete resolution is the dyadic value `16384`.
- `relativeRankTangentCheck` includes box order, anchor validation, all weight signs, and the tangent inequality. Its mathematical tangent theorem would remain sound for an external anchor, so these extra checks do not conceal a missing premise.

## Premise inventory

No conditional premise is hidden by the public endpoints:

- `rankTangentCheck_energy_sound` and `relativeRankTangentCheck_energy_sound` explicitly require the pointwise pair-model lower bounds.
- `lowerPieceTangentCheck_sound` explicitly requires the selected piece checks; `checkedLowerPieceTangentCheck_sound` discharges them computationally.
- `checkAffineCertificate_sound` explicitly requires quadratic-leaf soundness; `checkedLowerPieceAffineTree_sound` instantiates it with the standalone checked lower-piece leaf.
- `checkedLowerPieceAffineTree_A6_global_sound` requires the computed whole-tree check and the explicit nonnegative-gap premise. It has no external analytic/table premise.

## Concrete data obligations and blockers

The following remain **open outside this generic module** and block any claim that a particular baseline payload has been formally certified:

1. Define the packed payload reader and reject extra physical bytes plus nonzero unused payload padding before exposing its logical `CursorStream`.
2. Decode the baseline format's terminal codes `5/6` as generic terminal topology plus separate tail/quadratic payload kind. The baseline words must not be passed directly to the generic `0,1..5` topology decoder.
3. Implement and verify the macro affine-well orientation adapter for `2*(v+m*(q-x))^2` and `2*(v+m*(x-q))^2`, including exact bases/weights/coefficients/offsets and the pairwise kernel lower-bound connection.
4. Validate concrete shared denominators and relative anchors at resolution `16384`, and prove that the decoded values are the intended certificate values.
5. Supply the actual topology and payload constants, use the canonical topology guard, choose sufficient depth fuel, and reduce the full root check to `true` with exact logical exhaustion.
6. At the final application site, supply the explicit nonnegativity of the five gaps.

These obligations do not require a patch to `AffineTree.lean`; they require the separate concrete adapter/data module.
