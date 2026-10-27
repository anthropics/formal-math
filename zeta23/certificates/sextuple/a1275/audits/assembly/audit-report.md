# Improved exact-constant Lean assembly audit

## Scope

This artifact checks two conditional sextuple assemblies against the existing
`Zeta23.ThmD.Sextuple.Ledger` and `Zeta23.ThmD.Sextuple.Final` infrastructure:

- `A = 63 / 5000`, `B = 1094977 / 5000000000`;
- `A = 51 / 4000`, `B = B6 = 1094977 / 5000000000`.

The source is `ImprovedAssembly.lean`. The stable Lean checkout is
`/Users/mdumitrean/Desktop/dev/aigent/math/prime/_exp_rh89_zeta23_lean` at `5e9617d84ece3aeecdf983a8e7e9bfa50f413e5a`. It was clean before and after the final build. No
stable source was edited.

## Preserved `A = 63 / 5000` assembly

The original artifact endpoints remain unchanged:

- explicit-certificate ledger adapter
  `improvedZetaSextupleLedgerInterface_of_certificate`;
- exact feedback form
  `(3000000000 * HD 1 - 1094977 * Real.pi) / 2993700000`;
- comparison `6727668568 / 10^10 < improvedSextupleLowerConstant`;
- dyadic and cumulative epsilon wrappers;
- dyadic and cumulative fixed-rational interface wrappers.

Its directed comparator lower bound and positive margin are

```text
lower  = 201406213933795020896911983481/299370000000000000000000000000
margin = 13579020896911983481/299370000000000000000000000000
```

## Added `A = 51 / 4000`, `B = B6` assembly

The new declarations are isolated in
`Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275`.

### Ledger adapter

`A1275.zetaSextupleLedgerInterface_of_certificate` specializes the existing
`zetaSextupleLedgerInterface_of_ordered_entry_close` transfer theorem. The
ordinary affine certificate stays explicit:

```lean
hcertificate : ∀ g : Fin 5 → ℝ, (∀ i, 0 ≤ g i) →
  (51 / 4000 : ℝ) ≤ sextupleEnergy g + B6 * sextupleSpan g
```

Its conclusion is the concrete zeta ledger interface at `A = 51 / 4000` and
`B = B6`. `A1275.zetaSextupleLedgerError_isLittleO` proves the transferred
error is `o(N(T,2T))` without using that certificate.

### Exact feedback and comparator

`A1275.sextupleLowerConstant` is exactly

```lean
feedbackConstant (HD 1) (51 / 4000) B6.
```

`A1275.sextupleLowerConstant_exact` proves

```lean
A1275.sextupleLowerConstant =
  (3000000000 * HD 1 - 1094977 * Real.pi) / 2993625000.
```

`A1275.sextupleLowerConstant_gt_6727837118` proves

```lean
(6727837118 / 10 ^ 10 : ℝ) < A1275.sextupleLowerConstant
```

using exactly `HD_one_decimal.1` and `Real.pi_lt_d20`. The exact directed
rational lower bound and positive margin over the comparator are

```text
lower  = 201406213933795020896911983481/299362500000000000000000000000
margin = 10067520896911983481/299362500000000000000000000000
```

### Conditional wrappers

- `A1275.sextupleDyadic_of_interfaces`;
- `A1275.sextupleCumulative_of_interfaces`;
- `A1275.sextupleDyadic_6727837118_of_interfaces`;
- `A1275.sextupleCumulative_6727837118_of_interfaces`.

The epsilon and fixed-rational wrappers all retain
`ZetaBasePenaltyInterface` and the `A = 51 / 4000`, `B = B6`
`ZetaSextupleLedgerInterface` as hypotheses.

## Native Lean and trust audit

- Native Lean: `4.33.0-rc2`, commit
  `d8b18978322de05a8f3dba51ef03cf5461676c17`.
- The exact native command is recorded in `direct-build.log`. It sets `-R` to
  this artifact directory and emits `ImprovedAssembly.olean` here.
- Direct build exit: `0`.
- The log prints the types and `#print axioms` result for all 24 public
  definition/theorem endpoints, including both constant families.
- Every endpoint reports only `[propext, Classical.choice, Quot.sound]`.
- Forbidden scan exit: `0`. The scan covers `sorry`, `admit`, declaration
  axioms, `unsafe`, `native_decide`, `ofReduceBool`, `sorryAx`,
  `implemented_by`, `partial def`, `opaque`, and `extern`.

Exact hashes for the checked source and logs:

```text
322936ef431ae96201d11a4e1d63fb7f720745fdcf2c28ae8dd707837a286a5b  ImprovedAssembly.lean
67ceee8f08259b3b94e3893d0b653720589e1c192b54f9261f86ca215659ddf3  direct-build.log
6c07fb0e8eade0cd130eec7b73c418f592675471fb684a0ca6e22245bc6072e3  forbidden-scan.log
adac3cc40a515442e9ab2b352f573195b4fe15297bbd394f01d45bf40e968f98  ImprovedAssembly.olean
321b300bbd199cdd4da58aeee67b0598f4ca3e4b16b56e6896344e1bc210e9eb  provenance.json
```

`SHA256SUMS` also records the final report and recovery-state hashes.
`provenance.json` records the imported `Ledger.lean`/`Final.lean` hashes and
both exact comparator calculations.

## Logical boundary

This artifact does **not** prove either improved final theorem. Neither concrete
affine certificate was supplied or imported. Each ledger adapter requires its
full certificate theorem as an explicit argument. The fixed headlines remain
interface theorems. No result here is named or described as unconditional.

## Integration plan after the `A = 51 / 4000` certificate exists

1. Kernel-check a theorem with exactly the `A1275` adapter hypothesis shown
   above. Do not bridge it through a global assumption.
2. Move this artifact module into the stable tree, or split the adapter into
   `Ledger.lean` and the feedback/interface wrappers into `Final.lean`.
3. In a module that also imports `Zeta23.ThmD.Sextuple.Base`, form

   ```lean
   have hledger :=
     ImprovedAssembly.A1275.zetaSextupleLedgerInterface_of_certificate
       CertificateA1275.sextuple_affine
   ```

4. Combine it with the existing proved base interface:

   ```lean
   exact ImprovedAssembly.A1275.sextupleDyadic_6727837118_of_interfaces
     zetaBasePenaltyInterface hledger
   ```

   Use `A1275.sextupleCumulative_6727837118_of_interfaces` for the cumulative
   result.
5. Only after these applications kernel-check should public final endpoints be
   added. Add those endpoints to the stable trust audit and rerun the forbidden
   scan.
