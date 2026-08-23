# Lean 24c compact macro-analytic certificate hostile audit

**Classification: PASS for the authorized stable 56-piece analytic envelope.**

**Concrete 5D integration: not established by this snapshot.** The stable theorem is only a pointwise one-dimensional lower envelope. The frozen experimental catalog/5D file is excluded from this audit.

## Authorized snapshot and scope

The final audit used only this parent-authorized, quiescent snapshot:

| artifact | SHA-256 before | SHA-256 after |
|---|---|---|
| `MacroAnalytic.lean` | `c0757a933f4c2ea2987da6e3d3dbe0d4f804c5c4a88174758e2e7c5ed8370ddf` | `c0757a933f4c2ea2987da6e3d3dbe0d4f804c5c4a88174758e2e7c5ed8370ddf` |
| `MacroEnvelopeData.lean` | `632d72144a0a62258b68e94a9da93b889a6b67c8f242e6fce1eaaa8ce26690b5` | `632d72144a0a62258b68e94a9da93b889a6b67c8f242e6fce1eaaa8ce26690b5` |
| `macro-envelope-data-generation-report.json` | `e8873255bfeb650067fafbdd46bebd36fe004b2384683a2b6c0a1ca1ee6b80e7` | `e8873255bfeb650067fafbdd46bebd36fe004b2384683a2b6c0a1ca1ee6b80e7` |
| `MacroDataReduce.lean` (diagnostic only) | `4a6162d62bd4a4ae3d74142fb9f739d5703428f23a99734141a0bb5c3f0bfff0` | `4a6162d62bd4a4ae3d74142fb9f739d5703428f23a99734141a0bb5c3f0bfff0` |

I read those files in full. I also read the complete project-local import closure in full: `PieceCert.lean`, `KernelInterval.lean`, `Kernel.lean`, `TrigInterval.lean`, and `Interval.lean`. Their SHA-256 values were unchanged before and after:

- `PieceCert.lean`: `b8e505a651d8b9b1a45da52080f6b1e86a92ea3fefbfe323a282432aef614f2f`
- `KernelInterval.lean`: `d09b9efe4a36394fa08bcc7a0e904a7eae409f0f198d8103d1522f8bbeba37fe`
- `Kernel.lean`: `e50b67ee4e267a5a50a7b4bcfcf15568f83fe4aaa45d312cb6570370988d7a7b`
- `TrigInterval.lean`: `63792e1a3f8488f8c675185601049d80c901473f5274b8e88961fc1fc707caf5`
- `Interval.lean`: `0bbb8991defb97ece3ff76ef81b3cab86bd430ada6cb933804e419774e92f866`

### Rejected concurrent snapshot

An earlier run began against the original `MacroData.lean`/report names at the intended hashes. During that run a concurrent writer replaced them with experimental hashes `da8ffa9bad51e01391c556c9cf0a9a759863d859b1b199262474bac652ad20a0` and `c96184bbf6fef293eb47e256c8c9c5d8ecbb996bfd887a13e7733dd06012632d`. I rejected every mixed-snapshot result. The parent then authorized the byte-identical intended envelope under the stable names above. All reads, builds, Fraction checks, scans, and after-hashes reported here were restarted against those stable names. The `da8f...` file and `c961...` report remain excluded as frozen experimental/internally stale artifacts.

## Native Lean replay and axioms

Environment: Lean `4.33.0-rc2`, Mathlib revision `51e6992efd06126df61a496bebf8f49482a4e129`, through the repository's `lake env`.

1. Rebuilt `MacroAnalytic.olean` explicitly from the fixed source: **PASS**, zero diagnostics, 5.76 s real. Its reproducible content hash is `098aec3856065d398fa40c311434d825f1fed0c9f22304325a572b28b90a3ef3`; its modification time changed during this run.
2. Elaborated `MacroEnvelopeData.lean` against that rebuilt local olean: **PASS**, 31.37 s real.
3. Elaborated diagnostic `MacroDataReduce.lean`: **PASS**, `#reduce checkMacroPieces 0 59 macroPieces` printed exactly `true`, 15.23 s real.
4. A separate stdin axiom probe covered the derivative lemmas, both range-soundness lemmas, both affine-square lemmas, the Lipschitz lemma, `WellCert.check_iff_valid`, `WellCert.check_sound`, `MacroPiece.check_sound`, and `checkMacroPieces_sound`: **PASS**.

`#print axioms` on `macroEnvelope_sound`, representative piece checks, `macroPieces_check`, and every critical analytic declaration in the probe reported exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No other axiom appeared.

## Formula and analytic audit

### Kernel, first derivative, and second derivative

Write `A = sqrt 2 * cos θ`, `S = sin θ`,

```text
N(x) = A*x*sin(x/2) - 2*S*cos(x/2)
D(x) = (x^2 - 2)*S.
```

The source definitions reduce to

```text
N'(x)  = (A + S)*sin(x/2) + (A*x/2)*cos(x/2)
N''(x) = (A + S/2)*cos(x/2) - (A*x/4)*sin(x/2)
D'(x)  = 2*x*S
D''(x) = 2*S.
```

For `f=N/D`, the implemented formulas are

```text
f'  = (N'*D - N*D') / D^2
f'' = N''/D - N*D''/D^2 - 2*N'*D'/D^2 + 2*N*(D')^2/D^3.
```

They are algebraically correct. The Lean `HasDerivAt` proofs connect `N/D` to `mtKernelClosed`, and `mtKernel_eq_closed` connects it to the sinc-defined `mtKernel` away from `x^2=2`. Every derivative use is on `x>2`. An independent SymPy 1.14 replay through the required interpreter returned `true` for both numerator derivatives, both denominator derivatives, the quotient derivative, and the quotient second derivative.

### Interval directions, reduction, domain, and denominator signs

- `mul` takes all four rational corners. `scale` reverses endpoints for negative factors. `invPos` correctly maps a positive `[lo,hi]` to `[1/hi,1/lo]`.
- Sine/cosine reduction uses an exact rational enclosure of pi, an exact Taylor remainder, and global sine/cosine Lipschitz widening. The supplied turn is only an index; the checker verifies the reduced-angle condition exactly.
- Barrier cells require `2 <= lo`; wells require `2 < lo`. `[0,2]` uses the sinc-based low lemma and never divides by the closed-form denominator.
- Exact replay found the smallest reduced-angle slack to be about `2.147597196153101e-1` for barrier cells and `5.388046535897932e-1` for well box/midpoint/endpoint checks.
- The smallest checked denominator lower endpoint was about `1.299273878159941` for barriers and `21.26153404248235` for wells. Every reciprocal therefore has the required sign.
- Rational-to-real order transfers use `exact_mod_cast`; there is no float-to-real cast or unproved rounding direction in Lean.

### Lipschitz step and well orientation

`mtClosedDeriv_lipschitz_on` bounds `|f'(y)-f'(mid)|` by `M*|y-mid|`, where `M=absUpper(mtClosedSecondRange ...)`. Convexity of the closed box and pointwise second-derivative enclosure supply the mean-value bound. `|y-mid| <= radius` and `M>=0` are used in the correct multiplication direction.

For a left well, `q=box.hi`, `g(y)=σ*k(y)+m*y`, and the checker makes `g'<=0`. Thus

```text
v + m*(q-x) <= σ*k(x) <= |k(x)|.
```

For a right well, `q=box.lo`, `g(y)=σ*k(y)-m*y`, and the checker makes `g'>=0`. Thus

```text
v + m*(x-q) <= σ*k(x) <= |k(x)|.
```

The Boolean `derivativePositive` has the needed polarity: `!positive` on the left and `positive` on the right. All 36 endpoint intervals strictly certify the declared sign, and all `q` values are the correct side endpoint. Across the nine zero pieces the signs alternate `+/-`, `-/+`, ..., `+/-`.

The well model retains the cross term:

```text
2*(v+m*d)^2 = 2*v^2 + 4*v*m*d + 2*m^2*d^2.
```

It is never replaced by a cross-term-free quadratic in the stable analytic source.

### Boolean consumption and soundness chain

`WellCert.check_iff_valid` is an exact equivalence between the accepted Boolean and the proposition containing:

- all four analytic prerequisites on the box, midpoint, and endpoint;
- `v>=0`, `m>=0`;
- the side endpoint equality;
- the oriented endpoint-value bound;
- the midpoint derivative/Lipschitz slope bound.

`WellCert.check_sound` uses every soundness-relevant component. The strict `2<midpoint` subcheck is redundant after the box/domain and denominator facts, so its destructured proof is not referenced; this only makes the checker stricter. Likewise, nonnegativity of a numeric barrier's constant is stronger than needed once the cell comparison is proved. No unchecked Boolean is used as if proved, and no accepted Boolean is turned into an external-success premise.

`MacroPiece.check_sound` dispatches to the base or well proof. `checkMacroPieces_sound` consumes nonemptiness, exact recursive coverage, and `List.all MacroPiece.check`. Thus every selected piece has both a membership/box proof and its local analytic inequality.

## Independent exact `Fraction` reconstruction

I parsed `MacroEnvelopeData.lean` directly with `/Users/mdumitrean/Desktop/dev/aigent/agi/.venv/bin/python` and rebuilt the rational interval engine independently with `fractions.Fraction`. No generator output was trusted. Results:

- 56 definitions, with indices exactly `0..55`.
- Counts exactly: 1 low, 10 barrier, 36 well, 9 zero.
- Exactly 46 numeric barrier cells.
- First endpoint `0`, final endpoint `59`.
- All 55 outer seams are exact equalities. All nested barrier-cell seams are exact equalities. Every interval has positive width; there are no gaps or reversed/misordered overlaps. Adjacent closed pieces meet only at their shared seam.
- All well widths are exactly `3/8`. Every barrier cell has width at most `1`.
- The nine zero-piece boxes exactly equal the report's nine bracket pairs, and every width is exactly `1/1000000`.
- `MacroDataReduce.lean` parses to exactly the same 56 data records as `MacroEnvelopeData.lean`.
- Every report count, bracket, minimum, source hash, and coverage claim matches the stable source.
- Every emitted `a`, `v`, and `m` lies on the `10^12` quantization grid.
- Exact minima match the report:
  - barrier `a`: `180593923/1000000000000`;
  - well `v`: `71/125000000000`;
  - well `m`: `13152938453/1000000000000`.
- Independent exact replay accepted all 46 barrier-cell Booleans and all 36 well Booleans, with no failure.
- Tightest comparison slacks, shown only as decimal summaries of positive exact fractions:
  - barrier cell model: about `9.932261146190989e-14` at piece 7, cell 4;
  - endpoint value: about `1.531471157136652e-14` at piece 42;
  - well slope: about `1.215734315423657e-14` at piece 5.

Zero pieces use the globally sound model `0 <= 2*k(x)^2`; their soundness does not assume a zero exists inside the labeled bracket. The opposite certified endpoint signs support the intended root interpretation, but `macroEnvelope_sound` does not export a root-existence theorem and does not need one.

## Generator and forbidden-construct audit

The envelope generator was notebook-only; no standalone project-local generator file exists. I reconstructed and read its relevant exact interval, derivative, bracket, data-generation, and emitter cells from the preserved session log. It uses `round(float(...))` only to propose range-reduction turn indices and uses float values for diagnostics. Exact rational interval calculations and exact assertions create the coefficients. More importantly, the emitted Lean checker independently verifies every turn, prerequisite, endpoint inequality, slope inequality, barrier inequality, and seam. Therefore generator float behavior is not in the theorem's trust base.

A lexical scan of both authorized Lean files, `MacroDataReduce.lean`, and the full project-local import closure found none of:

```text
sorry, admit, native_decide, Lean.ofReduceBool, ofReduceBool,
unsafe, axiom declarations, opaque declarations, extern,
implemented_by, run_tac, or external-success hypotheses.
```

The stable Lean files contain no `Float` token or decimal literal. The only metacommands are the expected `#print axioms` lines and the diagnostic `#reduce` in `MacroDataReduce.lean`.

Persisting a standalone deterministic generator would improve provenance and reproducibility, but its absence does not weaken the kernel-checked theorem.

## Exact theorem scope and blockers

The exact public conclusion audited here is:

```text
forall x : Real, 0 <= x -> x <= 59 ->
  exists p in macroPieces,
    Holds p.box x and p.model x <= 2 * mtKernel x ^ 2.
```

Its only premises are `0<=x` and `x<=59`. It has no float premise, no external-success premise, no 5D premise, and no RH premise.

**Analytic-envelope blockers: none.**

**Concrete 5D status:** this stable snapshot does not prove that a 5D objective constructed from the 15 pairwise distances is bounded by the target. It does not supply the piece-selection/catalog theorem, the global expansion including all affine-square cross terms, or the final exact 5D integration/SOS/B&B theorem. The excluded `da8f...` experimental file cannot be used to upgrade this audit. Thus the analytic envelope is PASS, while concrete 5D integration remains a separate, unestablished obligation.
