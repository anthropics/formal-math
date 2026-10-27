/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PiecesCountedStatement
import Mathlib.Tactic

/-! # From the padding string to counted operations: the data

`AppRunningTime.IsPieces` (`AppRunningTimeStatement.lean`) numbers 𝓘 from 0, and three of its
programs (the two functions of a factorization and the values of the A_i) read a padding string.
`ofPadded P A c shift` (`PiecesCountedStatement.lean`) are the data with 𝓘 shifted and the padding
string fixed at 2^{cλ} units.
They have clauses (a), (b) and the sizes of (c) with the same ρ and c (`ofPadded_is`). Before that,
side lemmas on lists of bits, lists of units and the sorted list of a shifted range. -/

public section

namespace PiecesCounted

open Finset Groundwork Groundwork.Prog ClauseBound.Alg

/-! ### Side lemmas -/

/-- A list of bits of the right length, read as a string and written as a list again. -/
theorem bitsOf_toBits {n : ℕ} {l : List Bool} (h : l.length = n) : bitsOf (toBits n l) = l := by
  subst h
  refine List.ext_getElem (by simp [bitsOf]) fun i h1 h2 => ?_
  simp [bitsOf, toBits, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- A list of units is determined by its length. -/
theorem units_eq (u : List Unit) : List.replicate u.length () = u := (List.eq_replicate_iff.2 ⟨rfl, fun _ _ => rfl⟩).symm

/-- {0, …, n − 1} shifted by s, in increasing order. -/
theorem sort_image_shift (n : ℕ) (s : ℤ) : ((range n).image fun i : ℕ => (i : ℤ) + s).sort = (List.range n).map fun i : ℕ => (i : ℤ) + s := by
  have h := StrictMonoOn.map_finsetSort (⟨fun i : ℕ => (i : ℤ) + s, fun a b e => by simpa using e⟩ : ℕ ↪ ℤ) (range n) fun a _ b _ hab => by
    change (a : ℤ) + s < (b : ℤ) + s
    omega
  rw [sort_range, Finset.map_eq_image] at h
  exact h.symm

/-- The number of a piece in `P` from its number in the shifted index set. -/
theorem toNat_shift (j : ℕ) (s : ℤ) : ((j : ℤ) + s - s).toNat = j := by simp

/-- The elements of the shifted index set. -/
theorem mem_ofPadded {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {c : ℕ} {shift : ℕ → ℤ} {lam : ℕ} {i : ℤ} (hi : i ∈ ((ofPadded P A c shift).fam lam).I) :
    ∃ j < P.cnt 0 lam, i = (j : ℤ) + shift lam := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
  exact ⟨j, Finset.mem_range.1 hj, rfl⟩

/-! ### Clauses (a), (b) and the sizes of (c) -/

/-- The data made from pieces with a padding string have clauses (a), (b) and the sizes of (c), with
the same ρ and c. -/
theorem ofPadded_is {ρ : ℝ} {c : ℕ} {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : AppRunningTime.ValQ → ℤ} {shift : ℕ → ℤ} (h : AppRunningTime.IsPieces ρ c P A val)
    (hs : ∀ lam, 1 ≤ lam → |shift lam| + (2 * lam) ^ c < 2 ^ (2 * lam) ^ c) : (ofPadded P A c shift).Is ρ c := by
  have hp : ∀ lam, 2 ^ (c * lam) ≤ (List.replicate (2 ^ (c * lam)) ()).length := fun lam => by rw [List.length_replicate]
  refine ⟨h.rho_ge, h.rho_lt, h.c_pos, fun lam hl => ?_, fun lam hl x y u v => ?_, fun lam hl i hi x y u v => ?_, fun lam hl i hi x y u v => ?_, fun lam hl i hi => ?_, fun lam hl => ?_,
    fun lam hl => ?_, fun lam hl i hi => ?_, fun lam hl i hi x y u v => ?_, fun lam hl i hi tr side z θ _ => ?_⟩
  · change (1 : ℤ) ≤ (P.d 0 lam : ℤ)
    exact_mod_cast h.d_pos lam hl
  · refine Eq.trans ?_ (h.sum lam hl x y u v)
    exact (Finset.sum_image fun a _ b _ e => by simpa using e).trans (Finset.sum_congr rfl fun j _ => by
      change A lam ((j : ℤ) + shift lam - shift lam).toNat x y u v = _
      rw [toNat_shift])
  · obtain ⟨j, hj, rfl⟩ := mem_ofPadded hi
    change A lam ((j : ℤ) + shift lam - shift lam).toNat x y u v = ∑ θ ∈ words (P.cap false 0 lam ((j : ℤ) + shift lam - shift lam).toNat),
      P.top ((List.replicate (2 ^ (c * lam)) (), false), (0, ((j : ℤ) + shift lam - shift lam).toNat), (bitsOf x, bitsOf y, θ)) *
        P.bot ((List.replicate (2 ^ (c * lam)) (), false), (0, ((j : ℤ) + shift lam - shift lam).toNat), (bitsOf u, bitsOf v, θ))
    rw [toNat_shift]
    exact h.row lam hl _ (hp lam) j hj x y u v
  · obtain ⟨j, hj, rfl⟩ := mem_ofPadded hi
    change A lam ((j : ℤ) + shift lam - shift lam).toNat x y u v = ∑ θ ∈ words (P.cap true 0 lam ((j : ℤ) + shift lam - shift lam).toNat),
      P.top ((List.replicate (2 ^ (c * lam)) (), true), (0, ((j : ℤ) + shift lam - shift lam).toNat), (bitsOf x, bitsOf u, θ)) *
        P.bot ((List.replicate (2 ^ (c * lam)) (), true), (0, ((j : ℤ) + shift lam - shift lam).toNat), (bitsOf y, bitsOf v, θ))
    rw [toNat_shift]
    exact h.col lam hl _ (hp lam) j hj x y u v
  · obtain ⟨j, hj, rfl⟩ := mem_ofPadded hi
    change ((P.cap false 0 lam ((j : ℤ) + shift lam - shift lam).toNat + P.cap true 0 lam ((j : ℤ) + shift lam - shift lam).toNat : ℕ) : ℝ) ≤ _
    rw [toNat_shift]
    exact h.caps lam hl j hj
  · exact Finset.card_image_le.trans (by rw [Finset.card_range]; exact h.card lam hl)
  · change (P.d 0 lam : ℤ) < 2 ^ (2 * lam) ^ c
    exact_mod_cast h.size_d lam hl
  · obtain ⟨j, hj, rfl⟩ := mem_ofPadded hi
    have h1 : (j : ℤ) < (2 * (lam : ℤ)) ^ c := by exact_mod_cast hj.trans_le (h.card lam hl)
    have h2 := hs lam hl
    have h3 := le_abs_self (shift lam)
    have h4 := neg_abs_le (shift lam)
    have h5 : (0 : ℤ) ≤ j := Int.natCast_nonneg j
    rw [abs_lt]
    constructor <;> linarith
  · obtain ⟨j, hj, rfl⟩ := mem_ofPadded hi
    change |A lam ((j : ℤ) + shift lam - shift lam).toNat x y u v| < _
    rw [toNat_shift]
    exact h.size_A lam hl j hj x y u v
  · obtain ⟨j, hj, rfl⟩ := mem_ofPadded hi
    have h1 := h.size_f lam hl _ (hp lam) j hj tr z.1 z.2 θ
    cases side
    · change |P.top ((List.replicate (2 ^ (c * lam)) (), tr), (0, ((j : ℤ) + shift lam - shift lam).toNat), (bitsOf z.1, bitsOf z.2, θ))| < _
      rw [toNat_shift]
      exact h1.1
    · change |P.bot ((List.replicate (2 ^ (c * lam)) (), tr), (0, ((j : ℤ) + shift lam - shift lam).toNat), (bitsOf z.1, bitsOf z.2, θ))| < _
      rw [toNat_shift]
      exact h1.2

end PiecesCounted
