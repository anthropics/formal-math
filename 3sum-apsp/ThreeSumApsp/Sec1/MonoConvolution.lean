/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Asymptotics.Powers

/-!
# The introduction: the exponent of MonoConvolution (Section 1.2)

The consequence of Theorem 2 for MonoConvolution, by a cited reduction: the exponent
`3/2 - ε/(8 - 2ε)` with `ε = 0.0008` is below 1.4999 (`monoConvolution_exponent_lt`), so the
logarithmic factors are absorbed (`monoConvolution_isBigO`). No other file uses this one.
-/

public section

namespace ThreeSumApsp

/-- Section 1.2, MonoConvolution: "an O(n^{2-ε})-time algorithm for 3SUM gives an
Õ(n^{3/2-ε/(8-2ε)})-time algorithm for MonoConvolution. Our approach gives O(n^{1.4999}) time for
MonoConvolution".  With the bound O(n^{1.9992}) of Theorem 2, ε = 0.0008, and the exponent is
1.49989998: below 1.4999 by 2 · 10⁻⁸. -/
theorem monoConvolution_exponent_lt : (3 / 2 - 0.0008 / (8 - 2 * 0.0008) : ℝ) < 1.4999 := by
  norm_num

/-- Section 1.2, MonoConvolution: the bound `Õ(n^{3/2-ε/(8-2ε)})` with `ε = 0.0008` is
`O(n^{1.4999})`, whatever the power `c` of the logarithm that `Õ` hides. -/
theorem monoConvolution_isBigO (c : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ (3 / 2 - 0.0008 / (8 - 2 * 0.0008) : ℝ) * Real.log n ^ c)
      =O[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ (1.4999 : ℝ)) :=
  isBigO_rpow_mul_log_pow_rpow monoConvolution_exponent_lt c

end ThreeSumApsp
