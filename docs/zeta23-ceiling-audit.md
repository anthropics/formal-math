# Reproducing the Zeta23 bandwidth-one ceiling

[`ceiling_law256`](../zeta23/Zeta23/PairCeiling/CeilingLaw256.lean) takes `EnclOK LawN256.K S 0 LawN256.encl`. For the concrete law, this means the j-th published interval `[lo_j, hi_j]` contains `K * S(j)` for every `j` from 1 to 256, with `K = 2^140`. The zero in `EnclOK` is the starting offset. The values at positive frequencies start with the first list entry. [Lean definition](../zeta23/Zeta23/PairCeiling/NumericCert.lean#L71)

## Check the law and its enclosures

1. Obtain `cert_N256_blk_b128m.json` from the authors. [`LawN256.lean`](../zeta23/Zeta23/PairCeiling/LawN256.lean) records the SHA-256 below. The public checkout contains the resulting intervals. Reproducing their derivation requires the matching certificate.

   ```text
   cc3de9917db4d14d844630a4e97dda8387fd6e257e52b6967f430b8914584eb8
   ```

2. Read the weights `w_c` and positions `x_ci` as exact rationals. Check that the weights are nonnegative and sum to one. In each configuration, check that positions are distinct in `[0, 256)`, each mark `m_ci` is 1 or 2, and the marks sum to 256. The weighted simple-point fraction is the weighted count of mark-1 positions divided by 256. Check it against the exact fraction in `LawN256.lean` before specializing the theorem's validity premise to this law.
3. For each `j` from 1 to 256, compute a rigorous interval `[L_j, U_j]` for the following real number. Use outward-rounded interval arithmetic for the trigonometric values and all subsequent operations.

   ```text
   S(j) = (1/256) * sum_c w_c * (
             (sum_i m_ci * cos(2*pi*j*x_ci/256))^2
           + (sum_i m_ci * sin(2*pi*j*x_ci/256))^2
          )
   ```

4. Verify `lo_j <= K * L_j` and `K * U_j <= hi_j` against all 256 published pairs. Increase the precision when a comparison is inconclusive. A value on a published endpoint may require a separate exact argument. The full set of successful containment checks establishes the numerical premise for this law.

## Replay the Lean checks

Run the project's existing checks with its pinned toolchain.

```sh
cd zeta23
lake build
lake env lean scripts/PrintAxioms/PairCeiling.lean
```

`LawN256_check` evaluates the published table with exact integer arithmetic. The row checker verifies the near-CUE bound at frequencies 1 through 255 and the edge bound for `D(1) = (sum_{j=1}^256 S(j))/256 - 1/2`. The Lean audit checks the downstream implications with `EnclOK` supplied as a hypothesis. See the [row checker](../zeta23/Zeta23/PairCeiling/RowCert.lean) and the [project's axiom audit](../zeta23/AUDIT.md).
