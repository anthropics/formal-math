# Lean24b direct-AF non-certificate audit

## Disposition

**PASS for the complete non-certificate chain.** The only P0 blocker to an unconditional exported `0.6727556` theorem is the missing kernel-checked five-dimensional affine certificate. I found no additional declaration-level mathematical or trust bug in the transfer, packing, ledger, base, seam, or final feedback code.

Audit snapshot: `2026-08-22T08:28:43.624709+00:00`

Lean project:
`/Users/mdumitrean/Desktop/dev/aigent/math/prime/_exp_rh89_zeta23_lean`

No Lean source was edited by this audit.

## Exact source identities

| file | lines | SHA-256 |
|---|---:|---|
| `Zeta23/ThmD/Sextuple/Transfer.lean` | 698 | `1090ef0bfa82ed56d3629fbf85faeb1aa44316bdcc0b582097ff044598bd3328` |
| `Zeta23/ThmD/Sextuple/Packing.lean` | 470 | `378c044ff85cbdb657524183662911fa860ac65db6062c269804cb9d7d763d48` |
| `Zeta23/ThmD/Sextuple/Ledger.lean` | 308 | `b87b71ff4b52213b9626ab4bb634dc5d919da40e8e3a9a4417707287078a4fe4` |

The non-certificate audit set contains 17 files and 5,181 lines: `LinAlg/Sextuple*`, `ZeroSide/SextuplePenalty`, `Assembly/SeamSextuple`, and the `ThmD/Sextuple` files other than the six interval/certificate files. An exact token scan found no `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, or `Lean.ofReduceBool`.

## Builds

From the Lean project root, I ran:

```text
lake build Zeta23.LinAlg.SextuplePenalty Zeta23.LinAlg.SextuplePenaltyConvex Zeta23.LinAlg.SextupleBlockPinching Zeta23.ZeroSide.SextuplePenalty Zeta23.Assembly.SeamSextuple Zeta23.ThmD.Sextuple.Base Zeta23.ThmD.Sextuple.Ledger Zeta23.ThmD.Sextuple.Final
```

Result: exit code 0; `Build completed successfully (8861 jobs)`. The output contained inherited deprecation/linter warnings and no error.

I also ran the focused concrete-chain command:

```text
lake build Zeta23.ThmD.Sextuple.Ledger
```

Result: exit code 0; `Build completed successfully (8861 jobs)`. The `Transfer`, `Packing`, and `Ledger` `.olean` files were all newer than the exact source bytes hashed above.

A `lake env lean /dev/stdin` axiom audit also exited 0.

## Transfer and normalization

The current declarations establish the required scaling, rather than comparing the Gram entry to a raw autocorrelation:

- `simpleZeroGram_interior_apply_eq_Kfun` identifies an actual normalized entry as `Kfun/(a*L^2)`.
- `Kinf = L*Phi`, so its normalized value is `Phi/(a*L)`.
- `paperFT_sharpW_one_eq_mtKernel` and `normalized_localFunD_Phi_sub_mtKernel_le` prove the factor-`1/2` sinc arguments and the sharp-window normalization. The latter gives
  `|Phi/(aL) - mtKernel(Lr)| <= 12w/L`.
- `normalized_Kfun_sub_Kinf_le` gives the omitted-grid bound `12*c^2/L` for both ordinates in `(T+1,2T-1]`.
- `simpleZeroGram_atD_interior_sub_mtKernel_le` combines the two bounds into
  `(12*cDT^2 + 12*w)/L` at the exact argument `L*(gamma_i-gamma_j)`.
- `gramTransferError_tendsto_zero`, `gramTransferError_eventually_nonneg`, and `eventually_zeta_simpleZeroGram_interior_sub_mtKernel_le` supply the uniform eventual form used by the ledger.
- `abs_mtKernel_le_one` proves the ideal-entry bound. Poisson-normalized column Cauchy--Schwarz supplies the actual-entry bound.

Thus the concrete transfer has the correct Fourier-transform object, denominator, sign, and physical scaling.

## PSD, trace, and `min(E,6/5)`

- `interiorPrincipalBlock_posSemidef` uses the injective six-point embedding into the actual simple-zero Gram.
- `interiorPrincipalBlock_rtrace_le_six` sums six diagonal entry bounds obtained from normalized column norms.
- `min_offDiagEnergy_six_fifths_le_blockSpectralPenalty` proves the exact local floor. In the low-spectrum branch the spectral penalty controls the off-diagonal energy. In the high branch, the eigenvalue above 2 and the trace-at-most-6 constraint give the additional `1/5`, for the total `1+1/5=6/5`.
- `sextupleEnergy_le_offDiagEnergy_add_error` has the correct `60*epsilon` loss: 15 unordered pairs, the square difference contributes `2*epsilon`, and Hermitian orientation contributes a second factor 2.
- The affine certificate is combined with `A <= 6/5`, not substituted for the local spectral floor.

The convex spectral pinching declarations then allow the global simple-zero penalty to dominate sums of disjoint actual principal blocks.

## Six-offset packing and signs

The finite packing chain has the following exact accounting:

- `pointCount_le_six_mul_blockCount_add_ten` loses at most ten points.
- `exists_offsetSpan_le_five_sixths` supplies the span coefficient `5/6`.
- The blockwise `60*epsilon` loss becomes `10*s*epsilon` after division over six-point blocks.
- `simpleSextuplePenalty_packing_of_ordered_entry_close_poisson` concludes

```text
A/6*(s-10) - 5B/6*totalGap - 10*s*epsilon <= simpleSextuplePenalty.
```

All three subtraction signs are correct for a lower bound.

The ordered interior is exactly `(T+1,2T-1]`: the lower endpoint is strict and the upper endpoint is retained. The omitted count is the complement of this interior inside the global simple Gram window and is proved negligible, so the collars and taper fringe are charged rather than silently discarded. `sInterior_eq_N0s` also resolves the base-parameter versus `P.atD T` cardinality without an asymptotic substitution.

`sum_adjacentGap_le` gives `totalGap <= L*T`. The asymptotic span comparison then yields the ledger term

```text
-5*pi*B/3 * Ncount(T,2T).
```

This is exactly the numerator contribution `-10*pi*B` after multiplying the final inequality by 6.

## Concrete ledger and final boundary

`zetaSextupleLedgerInterface_of_ordered_entry_close` discharges the transfer, Poisson normalization, ideal-kernel bound, packing, span, count, and little-o bookkeeping from an ordinary affine-certificate theorem.

The current `Ledger.lean` adds:

- `zetaSextupleLedgerError := zetaLedgerError A6 (fun T => 10*gramTransferError T)`;
- `zetaSextupleLedgerInterface_of_certificate`, whose sole substantive argument is
  `A6 <= sextupleEnergy g + B6*sextupleSpan g` for nonnegative gaps;
- `zetaSextupleLedgerError_isLittleO`.

`zetaBasePenaltyInterface` is unconditional. `Final.lean` correctly keeps its headline theorems conditional on both the base and sextuple-ledger interfaces. Combining the two interfaces gives

```text
(6*B_MT - 10*pi*B6)/(6-A6),
```

and `sextupleLowerConstant_gt_6727556` proves the fixed-decimal comparison. This conditional/unconditional boundary is honest in the current sources.

## Axiom audit

`#print axioms` was run for these declarations:

- `min_offDiagEnergy_six_fifths_le_blockSpectralPenalty`
- `sextupleEnergy_le_offDiagEnergy_add_error`
- `interiorPrincipalBlock_posSemidef`
- `interiorPrincipalBlock_rtrace_le_six`
- `simpleSextuplePenalty_packing_of_ordered_entry_close_poisson`
- `normalized_localFunD_Phi_sub_mtKernel_le`
- `normalized_Kfun_sub_Kinf_le`
- `simpleZeroGram_atD_interior_sub_mtKernel_le`
- `eventually_zeta_simpleZeroGram_interior_sub_mtKernel_le`
- `zetaSextupleLedgerInterface_of_certificate`
- `zetaSextupleLedgerError_isLittleO`
- `zetaBasePenaltyInterface`
- `thmD₀_sextuple_6727556_of_interfaces`

Every declaration depends on exactly the allowed standard set:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` or computation escape hatch appears.

## Sole P0 blocker: affine certificate

At this snapshot:

- `Zeta23/ThmD/Sextuple/Certificate.lean` does not exist.
- No declaration named `sextuple_affine` exists.
- `CertificateData.lean` contains the 74-piece, 7,266-cell one-dimensional table, but ends in two `#reduce` commands. It does not promote either check to a theorem.
- No sound total five-dimensional checker covers all nonnegative five-gap inputs, the `span >= 59` tail, all 15 partial-sum distances, and every closed boundary.
- Therefore `zetaSextupleLedgerInterface_of_certificate` cannot yet be instantiated, and no unconditional public/comparator theorem exists.

The exact one-dimensional data replay had 0 rational `cellCheck` failures and contiguous coverage of `[0,59]`. That validates the table data only; it does not replace the missing five-dimensional theorem.

## Scalability finding

A clean build of the current flat `CertificateData.lean` is itself a serious operational blocker before adding the five-dimensional proof:

- my orphaned clean build ran for 5 hours at 100% CPU, reached 28,534,864 KiB RSS (about 28.5 GB as reported), produced no output, and was terminated after the source became obsolete;
- the parent's independent clean build eventually completed in 17,998 seconds, also about 5 hours.

This does not create a logical trust failure, but a final certificate cannot be called build-ready until clean-byte build time and memory are measured. The replacement must use compact, chunked kernel checks and a sound structural certificate rather than one enormous flat reduction/proof term.
