/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Paper.SecNetworks_Networks
public import Paper.SecLevel_Grid
public import StepMachines.Prog.GridLoop
public import StepMachines.Prog.SidePresents
public import ToTuring.Poly.GridSide
public import NetworkStatements
public import Mathlib.Algebra.Polynomial.Coeff

/-! # Section 5 of the paper: two facts on e*, the infimum defined after Definition 4, from the last paragraph of the proof of Proposition 3

If e > e*, then (K, e) is achievable for infinitely many K; and if (K, e) is achievable for
infinitely many K, then e* ≤ e. -/

@[expose] public section

namespace Paper

open Groundwork Groundwork.Prog

/-! ### e*, as in the last paragraph of the proof of Proposition 3 -/

/-- "Let e > e*; then (K, e) is achievable for infinitely many K." -/
theorem achievable_of_eStar_lt {e : ℝ} (he : eStar < e) (K₀ : ℕ) : ∃ K, K₀ ≤ K ∧ Achievable K e := by
  obtain ⟨e₀, ⟨-, h⟩, hlt⟩ := exists_lt_of_csInf_lt
    (s := {e : ℝ | 0 ≤ e ∧ ∀ K₀ : ℕ, ∃ K, K₀ ≤ K ∧ Achievable K e})
    ⟨1 / 2, by norm_num, fun K₀ => ⟨K₀, le_rfl, achievable_half K₀⟩⟩ he
  obtain ⟨K, hK, hA⟩ := h K₀
  exact ⟨K, hK, hA.mono hlt.le⟩

/-- If (K, e) is achievable for infinitely many K, then e* ≤ e. -/
theorem eStar_le {e : ℝ} (h0 : 0 ≤ e) (h : ∀ K₀ : ℕ, ∃ K, K₀ ≤ K ∧ Achievable K e) : eStar ≤ e :=
  csInf_le ⟨0, fun _ he => he.1⟩ ⟨h0, h⟩

end Paper
