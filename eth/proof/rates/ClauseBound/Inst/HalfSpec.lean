/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Inst.HalfIfc

/-! # The pieces with ρ = 1/√2 as programs: auxiliary lemmas

Lemmas on the pieces of Appendix B, with ρ = 1/√2, as programs with a pad. The pieces are numbered
0, …, 4h, and the piece number i is the piece A_s, s = i − 2h, made from the operators
on the polynomial ring. The lemmas: a sum over i = 0, …, 4h of a function of i − 2h is the sum over
s = −2h, …, 2h; the number of all partitions of 0, …, 4h; |s| ≤ 2h; and a pad of length 2^{cλ}
is long enough for all tables when the constants are large enough at the length λ.
They are in the namespace `ClauseBound.Inst.Half.Spec`. -/

public section

namespace ClauseBound.Inst.Half

open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec Finset

namespace Spec

/-- A sum over i = 0, …, 4h of a function of i − 2h is the sum over −2h, …, 2h. -/
theorem sum_range_shift (h : ℕ) (f : ℤ → ℤ) : ∑ i ∈ range (4 * h + 1), f ((i : ℤ) - 2 * h) = ∑ s ∈ Icc (-(2 * h : ℤ)) (2 * h), f s := by
  refine Finset.sum_nbij' (fun i : ℕ => (i : ℤ) - 2 * h) (fun s => (s + 2 * h).toNat) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    rw [mem_range] at hi
    rw [mem_Icc]
    omega
  · intro s hs
    rw [mem_Icc] at hs
    rw [mem_range]
    omega
  · intro i _
    omega
  · intro s hs
    rw [mem_Icc] at hs
    omega
  · intro i _
    rfl

/-- The number of all partitions of 0, …, 4h. -/
theorem deltaF_eq (h : ℕ) : deltaF h = ∑ E ∈ range (4 * h + 1), Partitions.p E := by
  rw [deltaF, pTab_eq, sum_map_range]

/-- |s| ≤ 2h. -/
theorem abs_sOf_le (h i : ℕ) : |sOf h i| ≤ 2 * (h : ℤ) := by
  rw [sOf, abs_le]
  omega

/-- A pad of length 2^{cλ} is long enough for all tables. -/
theorem padLen_le {c₀ c lam : ℕ} (hC : Cst c₀ c lam) : padLen (ClauseBound.Part.hOf lam) ≤ 2 ^ (c * lam) := by
  rw [padLen, deltaF_eq]
  exact hC.pad

end Spec

open Spec

end ClauseBound.Inst.Half
