/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Boson.Defs

/-! # Two facts on binomial coefficients with an integer upper entry

For an integer r and natural numbers k, n: C(r, k) = 0 when 0 ≤ r < k, and (n + 1)·C(r, n + 1) =
r·C(r − 1, n). -/

public section

namespace ClauseBound.Boson.Scalars

open Finset

/-- C(r, k) = 0 for 0 ≤ r < k. -/
theorem choose_eq_zero {r : ℤ} {k : ℕ} (h0 : 0 ≤ r) (h : r < k) : Ring.choose r k = 0 := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by exact_mod_cast h)]
  simp

/-- (n + 1)·C(r, n + 1) = r·C(r − 1, n). -/
theorem succ_mul_choose (r : ℤ) (n : ℕ) : ((n : ℤ) + 1) * Ring.choose r (n + 1) = r * Ring.choose (r - 1) n := by
  have h := Ring.choose_smul_choose r (n := n + 1) (k := 1) (by omega)
  simpa [Ring.choose_one_right] using h

end ClauseBound.Boson.Scalars

namespace ClauseBound.Boson

open Finset Scalars

namespace Scalars

end Scalars

end ClauseBound.Boson
