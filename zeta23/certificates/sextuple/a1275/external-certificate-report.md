# Exact sextuple-constant improvement certificate

Date: 2026-08-24

## Scope and conclusion

I kept all new work under `post-anthropic-rh-artifacts/checkers/sextuple-improvement/` and this report under `post-anthropic-rh-artifacts/reports/`. I did not edit the Lean repository or any audited stable input.

There are three completed levels of improvement at the fixed baseline

\[
B_0=\frac{1094977}{5000000000}.
\]

1. **Smallest strict certificate:**
   \(A=2500001/200000000=0.012500005\). Its independent exact replay passes and yields the certified public direct-AF bound
   \[
   R>\frac{672755621}{10^9}=0.672755621.
   \]
2. **Strongest certificate without new analytic envelope pieces:**
   \(A=63/5000=0.0126\). Its independent exact replay passes and yields
   \[
   R>\frac{6727668568}{10^{10}}=0.6727668568.
   \]
3. **Lean-checked local refinement:** the separate 216-piece catalog certifies \(A=51/4000=0.01275\) by independent exact 5D replay. It yields
   \[
   R>\frac{6727837118}{10^{10}}=0.6727837118.
   \]

The stronger \(A=129/10000=0.0129\) run is research-only. At this report snapshot it is still active at PID `95481`, with 2,225,000 exact nodes visited, 43 pending, depth 85, no exact obstruction, and no node-cap result. It is not the selected formal target. Conditional on a future replay PASS, its directed lower would be
\[
\frac{201406213933795020896911983481}{299355000000000000000000000000}
>\frac{6728005676}{10^{10}},
\]
with exact margin
`19897020896911983481/299355000000000000000000000000`.

The external BnB replays use exact rational arithmetic but have not yet been replayed by the Lean kernel. The new one-dimensional refinement catalog itself **has** been checked by Lean. Section “Lean adaptation plan” gives the remaining kernel-integration steps.

## Feedback sensitivity

Write

\[
R(A,B)=\frac{6M-10\pi B}{6-A},\qquad N(B)=6M-10\pi B.
\]

The directed input bounds prove \(N(B_0)>0\). Hence, for \(A<6\),

\[
\frac{\partial R}{\partial A}=\frac{N(B)}{(6-A)^2}>0,
\qquad
\frac{\partial R}{\partial B}=-\frac{10\pi}{6-A}<0.
\]

The exact finite change is

\[
R(A+\delta A,B+\delta B)-R(A,B)=
\frac{N(B)\delta A-10\pi(6-A)\delta B}
{(6-A)(6-A-\delta A)}.
\]

Thus a proposed move is strictly better exactly when

\[
N(B)\delta A>10\pi(6-A)\delta B
\]

under the usual positive-denominator assumptions. In particular, any \(\delta A>0\) with \(\delta B\le 0\) is strictly better.

Diagnostic sensitivities at the baseline are

- \(\partial R/\partial A\approx0.11236002015133115\);
- \(\partial R/\partial B\approx-5.246918836893183\);
- neutral trade \(dB/dA=R/(10\pi)\approx0.021414476504054713\).

These decimals are diagnostic only. The comparisons below use `fractions.Fraction`.

## Exact directed feedback bounds

The directed inputs are

- \(M>672500703679/10^{12}\), from `Zeta23.ThmD.HD_one_decimal.1`;
- \(\pi<314159265358979323847/10^{20}\), from `Real.pi_lt_d20`;
- \(\pi>3\), when the sign of a \(B\)-decrease is used.

They give the common positive numerator lower bound

\[
N(B_0)>
\frac{201406213933795020896911983481}
{50000000000000000000000000000}>0.
\]

| certificate | exact \(A\) | exact \(B\) | certified rational lower for \(R\) | public decimal rational | exact margin over public rational |
|---|---:|---:|---:|---:|---:|
| baseline | `1/80` | `1094977/5000000000` | `201406213933795020896911983481/299375000000000000000000000000` | `672755620655/10^12` | `204395896911983481/299375000000000000000000000000` |
| minimal strict | `2500001/200000000` | `1094977/5000000000` | `201406213933795020896911983481/299374999750000000000000000000` | `672755621/10^9` | `65108926146911983481/299374999750000000000000000000` |
| stable 56-piece | `63/5000` | `1094977/5000000000` | `201406213933795020896911983481/299370000000000000000000000000` | `6727668568/10^10` | `13579020896911983481/299370000000000000000000000000` |
| both strict, scaled | `62937/5000000` | `1093882023/5000000000000` | `67135519310321641958671690499173/99790210000000000000000000000000` | `6727665901/10^10` | `3258720958671690499173/99790210000000000000000000000000` |
| refined | `51/4000` | `1094977/5000000000` | `201406213933795020896911983481/299362500000000000000000000000` | `6727837118/10^10` | `10067520896911983481/299362500000000000000000000000` |
| research conditional, not yet certified | `129/10000` | `1094977/5000000000` | `201406213933795020896911983481/299355000000000000000000000000` | `6728005676/10^10` | `19897020896911983481/299355000000000000000000000000` |

The “both strict” row follows exactly from the stable certificate by scaling both constants by \(999/1000\): if \(A\le E+BS\), with \(E,S\ge0\), then \(tA\le E+tBS\) for \(0\le t\le1\). It is a certified Pareto point, although its direct-AF bound is slightly below the fixed-\(B\), \(A=63/5000\) row.

The complete computation is in `post-anthropic-rh-artifacts/checkers/sextuple-improvement/feedback-bounds.json`; its SHA-256 is `f82b8566cd049eed7066b09f6f12f111596d1f238afca37c97eece6d22c0175c`. The generating script SHA-256 is `b90ee2ea016cd99d0a2e201f5f0fe451aa40a7c278d57929ce8c2b33c5bbfd30`.

## Feasible-frontier structure

For a fixed exact lower-model catalog, write the macro objective at gaps \(g\) as

\[
\Phi_B(g)=E(g)+B S(g),\qquad A_*(B)=\inf_g\Phi_B(g).
\]

Since \(E,S\ge0\), \(A_*(B)\) is nondecreasing in \(B\), concave as an infimum of affine functions of \(B\), and obeys

\[
A_*(tB)\ge tA_*(B),\qquad 0\le t\le1.
\]

The certified and obstructed points at \(B_0\) map the practical frontier:

- \(A=63/5000\) passes with the unchanged 56-piece table.
- A direct 56-piece attempt at \(A=127/10000\) reached its exact 2,000,000-node cap with 46 nodes pending and depth 96. This is a resource result, not an obstruction.
- At \(A=51/4000\), an exact point defeats the strongest available frozen 56-piece models. Its deficit is
  `46501941575429484926214346965631584261/137438953472000000000000000000000000000000000000`. This obstructs that frozen catalog only, not the true kernel objective.
- The 216-piece narrow-well refinement removes that obstruction and certifies \(A=51/4000\).
- At the exact diagnostic point stored in `refinement-catalog-exact-replay.json`, the strongest 272-piece surrogate equals
  `12961604633647416570538272147554956896705751/1000000000000000000000000000000000000000000000` \(\approx0.012961604633647417\). Therefore the refined-catalog architecture has the rigorous upper bound \(A_*\le0.012961604633647417\) at \(B_0\).

The \(A=129/10000\) refined scalar-cache run has not produced an obstruction. It remains active at the snapshot above. It must not be classified as pass or failure until generation terminates and the independent serialized replay runs.

No claim is made that this catalog upper bound is an upper bound for the true analytic kernel.

## Exact 5D certificates

Every terminal decision in the generators and independent verifiers uses `fractions.Fraction`. Floating-point values only propose anchors and split coordinates. The verifiers read only the serialized streams, scalar certificates, stable exact input, and refinement JSON. They do not call generator proof routines.

### Minimal strict certificate

Path: `post-anthropic-rh-artifacts/checkers/sextuple-improvement/A-2500001-over-200000000_B-baseline/`

- nodes: 99,507;
- leaves: 49,754 = 48,260 quadratic + 1,494 tail;
- maximum depth: 60;
- scalar certificates: 871 with 1,932 segments;
- minimum quadratic margin:
  `11321077142144686089776740666084933541/34359738368000000000000000000000000000000000000`;
- minimum tail margin: `2712133/160000000000`;
- manifest SHA-256: `38aa2e1c646c9bd24c54b90e37e220b6d48eb39b240b442507e200c093e280a9`;
- independent replay SHA-256: `d2fb2eea2839dbd8d6924c18d02df92a094a00d5fcb0ad62a114ebb966ce364a`.

### Strong stable-table certificate

Path: `post-anthropic-rh-artifacts/checkers/sextuple-improvement/A-0p0126/`

- nodes: 127,163;
- leaves: 63,582 = 62,369 quadratic + 1,213 tail;
- maximum depth: 63;
- scalar certificates: 975 with 2,144 segments;
- minimum quadratic margin:
  `582212064159985723973137804413/1024000000000000000000000000000000000000`;
- minimum tail margin: `1603643/5000000000`;
- manifest SHA-256: `19eca1b02690db13546aee6087b0da9d8203462568019ce8d4eea798744d09d4`;
- independent replay SHA-256: `491d0c74038c2b119a1a382fbf9b41df6a201e668aabe2a844fc69308a18995e`.

### Refined \(A=51/4000\) certificate

Path: `post-anthropic-rh-artifacts/checkers/sextuple-improvement/refined-A-0p01275/`

- nodes: 385,967;
- leaves: 192,984 = 191,474 quadratic + 1,510 tail;
- maximum depth: 89;
- scalar certificates: 1,383 with 2,979 segments;
- minimum quadratic margin:
  `5627339909847066184392940685872272598458069/8589934592000000000000000000000000000000000000000000`;
- minimum tail margin: `853643/5000000000`;
- manifest SHA-256: `732a99cf5c4755ee18686f4a14669c61162bf6bdf87d7ca2d2564098e3346c30`;
- independent replay SHA-256: `391a0fdf116a4016899d0ca6821eb3d82db3dd4ffe80478225ca64f85570f1f5`.

### Research run at \(A=129/10000\)

Path: `post-anthropic-rh-artifacts/checkers/sextuple-improvement/refined-A-0p0129/`.

At the report snapshot, PID `95481` was active after 2,225,000 nodes, with 43 pending and depth 85. No exact obstruction and no node-cap result had occurred. The live generator log is `generator.stdout.log`. Its exact refined scalar-cache generator SHA-256 is `7de8e8215ffa4bd19e69b82bd5ba05455469c2730c94ef83c7e8f9120e6b0931`; the independent verifier reserved for a completed tree has SHA-256 `d4c31192a823853311494b72b900b84d34357b6f5dbbeb60a966855cf201bb83`.

This row is research state only. It is not used in the theorem selection or the unconditional bound claimed above.

## Separately audited refinement catalog

The stable 56-piece table is unchanged. The separate catalog subdivides stable pieces

`3, 9, 17, 23, 24, 27, 29, 35, 42`

into 24 cells each. There are 216 new cells, each of width \(1/64\), and 272 total selectable models.

High-precision `mpmath` only proposes conservative rational coefficients. Each emitted cell is an exact `MacroPiece.well`, and Lean proves its `WellCert.check = true`. Lean then proves

```lean
refinementCatalog.all MacroPiece.check = true
```

The final build passed. `#print axioms refinementCatalog_all` reports exactly

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, `native_decide`, `Lean.ofReduceBool`, `unsafe`, new `axiom`, `opaque`, `extern`, `implemented_by`, or `run_tac` occurs in the generated source.

Key artifacts:

- JSON: `post-anthropic-rh-artifacts/checkers/sextuple-improvement/refinement-catalog-exact.json`, SHA-256 `3f83563fb3d6f5a4e1aa0263384d0781494a672368233445a8c6e8e0e9817cb9`;
- Lean: `post-anthropic-rh-artifacts/checkers/sextuple-improvement/RefinementEnvelopeData.lean`, SHA-256 `e18afeb05ac3e56c94617ba136a61b9d79226899c5c4e192caa109aa2f9dde11`;
- Lean build report: `post-anthropic-rh-artifacts/checkers/sextuple-improvement/refinement-catalog-lean-build-report.json`, SHA-256 `e83cd151db2a28233583862f5e3046ab4953a9e4bf87e9840bb50ef596fb44bf`;
- exact structural replay: `post-anthropic-rh-artifacts/checkers/sextuple-improvement/refinement-catalog-exact-replay.json`, SHA-256 `2596dc977c0e26301bffa333c4008617769f5274890d67dd644e66179cbcb434`;
- Lean audit: `post-anthropic-rh-artifacts/checkers/sextuple-improvement/refinement-catalog-lean-audit.json`, SHA-256 `43c8d43315ad16aff43eb7f72ff5a130047aac9f938c0e6326f6574be3b68b12`.

The immutable stable data hash remains `961a0281a134382f9c2678cc49487839d2b9c2cbd9df382871f2c7b706552a5b`. The stable-table regeneration parity report is `post-anthropic-rh-artifacts/checkers/sextuple-improvement/stable-regeneration-check.stdout.json`, SHA-256 `58f8a935f8aaae40614ac68ac6ae0d05c77cd118ebe709be94e3a41e09d02624`, with all three regenerated Lean files byte-identical to their audited originals.

## Lean adaptation plan

No Lean repository file was changed. The low-risk integration order is:

1. **Minimal strict theorem first.** Point the existing macro adapter at the minimal candidate streams and its regenerated scalar certificates. Change only \(A\) to `2500001/200000000`, the derived cutoff, stream sizes, hashes, and replay fuel. Keep the 56-piece analytic table.
2. Regenerate the packed `MacroTreeWords` and scalar-data modules from the exact streams. Preserve the existing cursor-completeness and zero-padding checks. Confirm all four stream cursors end exactly at the declared sizes.
3. Replay every leaf through the existing quadratic and tail checkers. Then use the existing `Certificate.sextuple_affine` wrapper with the new exact \(A,B\).
4. Prove the direct-AF decimal line with `HD_one_decimal.1`, `Real.pi_lt_d20`, and exact `norm_num`, using the positive rational comparator margin above.
5. **Stable stronger theorem.** Repeat steps 1–4 with the \(A=63/5000\) streams and 975 scalar certificates. No analytic-data change is required.
6. **Refined theorem.** Add `RefinementEnvelopeData` as a separate table after the stable 56 entries. Do not replace or mutate the stable table. Generalize term indices to 272 models. The \(A=51/4000\) tree uses the ordinary stable seam cache; the \(A=129/10000\) tree also lets scalar-cache segments reference any of the 272 checked models.
7. Regenerate packed words and scalar certificate chunks for the chosen refined tree. Keep the scalar term-code offset `32768`; validate every segment against the 272-entry catalog and prove exact segment coverage.
8. Build the target theorem and full project without permissive flags. Run the forbidden-token scan and `#print axioms` on the final theorem. Expected analytic refinement axioms are only `[propext, Classical.choice, Quot.sound]`.

This order lands a strict unconditional improvement before taking on the larger refined catalog and tree.

## Reproduction and hashes

Run:

```bash
post-anthropic-rh-artifacts/checkers/sextuple-improvement/reproduce.sh
```

from any directory. The script uses `/Users/mdumitrean/Desktop/dev/aigent/agi/.venv/bin/python`, writes only in the owned checker directory, and does not use `/tmp`. Its SHA-256 is `854573855ee25a317dc30b68ecaa19c1d72c5a45be8b4172073d12d460f12484`.

The independent core scripts are:

- stable generator `b9ff0a1598432eed6bca626aa077dcd29ab6a388bddb432c7c3a23a42b49d2e7`;
- stable verifier `a089925e039b9cc8e8ae879b6f8ae4fb94cc34c8bb407c500d6a02ff0a98e0cd`;
- refinement generator `f0b92fe86ff346cdcdbfcfc1d21123aa3bbab2d48139493fa0bfcc77c3608857`;
- refinement structural verifier `791bc9b88a840077d17ea283033ce75ae51e1cb230a034d2ddb7e32bf27b6d06`;
- refined-tree generator `5596b3a76fefcc636bb0c940151e18a6b4032ff6747a5378cd20e2122c758c64`;
- refined-tree verifier `8279807a92e64a711ff2cba0f87ef1136460ee43a0e8ebc679d3d50aa94fec58`;
- refined scalar-cache generator `7de8e8215ffa4bd19e69b82bd5ba05455469c2730c94ef83c7e8f9120e6b0931`;
- refined scalar-cache verifier `d4c31192a823853311494b72b900b84d34357b6f5dbbeb60a966855cf201bb83`.

`SHA256SUMS` in the checker directory records the final report, summary, scripts, manifests, and replay reports.

## Trust statement

- Exact rational arithmetic decides every certificate terminal.
- Independent replayers consume serialized certificates only.
- Lean has checked all 216 new one-dimensional analytic pieces and their aggregate list.
- The 5D certificates remain external until the adaptation plan is completed in the Lean repository.
- Decimal evaluations of the transcendental formula are diagnostics. Certified public comparisons use directed rational bounds only.
