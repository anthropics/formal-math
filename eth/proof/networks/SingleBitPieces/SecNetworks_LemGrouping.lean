/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Paper.SecNetworks_Networks

/-! # The exponent of Lemma 1 in two forms: e·U + (e + 2)·gP/K = e(U + gP/K) + 2gP/K

The paper's Lemma 1 has the exponent e(U + gP/K) + 2gP/K, for every e ≥ 0. `exponent_eq` shows that
it equals e·U + (e + 2)·gP/K. -/

public section

namespace SingleBitPieces.SecNetworks_LemGrouping

open Groundwork

end SingleBitPieces.SecNetworks_LemGrouping

namespace SingleBitPieces

open Groundwork Groundwork.Prog Finset Paper NetE Stepped

/-- The exponent e·U + (e + 2)·gP/K equals the paper's exponent e(U + gP/K) + 2gP/K of Lemma 1. -/
theorem exponent_eq (e U g P K : ℝ) : e * U + (e + 2) * (g * P) / K = e * (U + g * P / K) + 2 * g * P / K := by ring

end SingleBitPieces
