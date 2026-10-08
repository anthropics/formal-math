/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.Theorem30.Memory
public import ThreeSumApsp.Sec2.Theorem5.WordSize

/-!
# The block of Theorem 30: the directory, sizes and limits

Facts about the memory map and the invariant DSReady that the preprocessing and the query (proof of
Theorem 30) share.

* `dir_cell` gives a cell of the directory.
* The roots fill their area and the tries fit into theirs (`length_dsTries_roots`,
  `length_dsTries_le`).
* The limits: 10^L fits in a word (`Lim30.pow_le`), and the encoded numbers are at most 7^L U
  (`abs_enc_le`).
-/

public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {U : ℤ}
  {μ μ' : ℕ → ℤ}

/-! ## The directory -/

/-- A cell of the directory. -/
theorem dir_cell (h : Sec2.SharedReady p hmL aX aY b0 X Y μ) {j : ℕ} (hj : j < 31) :
    μ (b0 + j) = (((Sec2.dirList p aX aY b0).getD j 0 : ℕ) : ℤ) :=
  h.dir.read (by simpa [Sec2.dirList] using hj)

/-! ## Sizes and limits -/

/-- The number of roots: one for each tile. -/
theorem length_dsTries_roots (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L)
    (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ) (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) :
    (dsTries p t hmL X Y).roots.length = p.nB * p.nB := by
  unfold dsTries
  rw [length_roots_allTries, length_tileList]

/-- The trie array fits into the trie area. -/
theorem length_dsTries_le (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L)
    (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ) (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) :
    (dsTries p t hmL X Y).cells.length ≤ trieCap p t := by
  unfold dsTries trieCap
  have hle := length_allTries_le p.L p.m t (tileList p.nB (encRow p hmL X) (encCol p hmL Y))
  rwa [length_tileList] at hle

/-- The number 10^L of leaves fits in a word. -/
theorem Lim30.pow_le (h : Lim30 lim p t b0 U) : (10 : ℤ) ^ p.L ≤ lim.word := by
  refine le_trans ?_ h.pow
  push_cast
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- Proof of Theorem 30, "Word size": the encoded numbers are at most 7^L U in absolute value. -/
theorem abs_enc_le (hmL : p.m ≤ p.L) (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ)
    (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) (U : ℤ) (hU : 0 ≤ U) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (β β' : ℕ) :
    (∀ τ, |encRow p hmL X β τ| ≤ 7 ^ p.L * U) ∧ ∀ τ, |encCol p hmL Y β' τ| ≤ 7 ^ p.L * U := by
  exact ⟨abs_encodingL_le (abs_bandArrayL_le (stdLayout hmL) hU hX β),
    abs_encodingR_le (abs_bandArrayR_le (stdLayout hmL) hU hY β')⟩

end Light.Sec4
