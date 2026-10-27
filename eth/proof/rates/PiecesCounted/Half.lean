/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PiecesCountedStatement
import PiecesCounted.Padded
import PiecesCounted.PaddedData
import GeneralPieces.Main
import ToTuring.Lib.Int
import ToTuring.Lib.Unary
import Mathlib.Tactic

/-! # Pieces with ρ = 1/√2 on counted operations

Theorem B: «There are pieces with parameters (1/√2, c), for an absolute constant c.»
`AppRunningTimeStatement.lean` states this with a padding string and with 𝓘 = {−2h, …, 2h} numbered
from 0 to 4h (`AppRunningTime.thmHalfPieces`). `FromPadded` carries it over, with the index set
shifted by −2h.
The shift has to be computed in polynomial time from λ in unary. It is taken as −⌊(|𝓘| − 1)/2⌋,
where |𝓘| = 4h + 1 is computed by one of the programs of the pieces, so that h itself need not be
computed. This form claims no more about the running time than `AppRunningTime.ThmHalfPieces` does:
the work is done in one step once the padding string is written. -/

public section

namespace PiecesCounted

open Finset Groundwork Groundwork.Prog ClauseBound.Alg

/-- The shift of the index set: −⌊(|𝓘| − 1)/2⌋. -/
@[expose] def halfShift (P : PiecesF) (lam : ℕ) : ℤ := -(((P.cnt 0 lam - 1) / 2 : ℕ) : ℤ)

/-- −⌊(f − 1)/2⌋ is polynomial-time if f is. -/
theorem neg_half_polyT {f : List Unit → ℕ} (hf : PolyT f) : PolyT fun u => -(((f u - 1) / 2 : ℕ) : ℤ) := by fun_prop

/-- (n − 1)/2 + N < 2^N for n ≤ N, N ≥ 1. -/
theorem half_add_lt {n N : ℕ} (hn : n ≤ N) (hN : 1 ≤ N) : (n - 1) / 2 + N < 2 ^ N := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have := Nat.lt_two_pow_self (n := k)
  rw [pow_succ]
  omega

/-- `HalfPiecesFrom`. -/
theorem halfPiecesFrom : HalfPiecesFrom := by
  rintro ⟨c, P, A, val, h, hB⟩ hF
  have hb : ∀ lam, 1 ≤ lam → |halfShift P lam| + (2 * lam) ^ c < 2 ^ (2 * lam) ^ c := fun lam hl => by
    have h1 := half_add_lt (h.card lam hl) (Nat.pow_pos (by omega))
    rw [halfShift, abs_neg, Nat.abs_cast]
    exact_mod_cast h1
  obtain ⟨c', Alg, -, hP⟩ := hF _ c P A val (halfShift P) h (neg_half_polyT h.time_cnt.poly) hb
  refine ⟨c', ofPadded P A c (halfShift P), Alg, hP, fun lam hl => ?_⟩
  obtain ⟨mu, hmu, hcnt, hd, hrest⟩ := hB lam hl
  have hs : halfShift P lam = -(2 * (AppHalfPieces.hOf lam : ℤ)) := by
    have e : (4 * AppHalfPieces.hOf lam + 1 - 1) / 2 = 2 * AppHalfPieces.hOf lam := by omega
    rw [halfShift, hcnt, e]
    push_cast
    ring
  refine ⟨mu, hmu, ?_, ?_, fun s hs' => ?_⟩
  · change ((range (P.cnt 0 lam)).image fun i : ℕ => (i : ℤ) + halfShift P lam) = _
    rw [hcnt, hs]
    ext z
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨j, hj, rfl⟩
      constructor <;> omega
    · rintro ⟨h0, h1⟩
      exact ⟨(z + 2 * (AppHalfPieces.hOf lam : ℤ)).toNat, by omega, by omega⟩
  · change ((P.d 0 lam : ℕ) : ℤ) = _
    rw [hd]
  · obtain ⟨j, hj, rfl⟩ := mem_ofPadded hs'
    obtain ⟨hA, hr, hc⟩ := hrest j hj
    have e : (j : ℤ) + halfShift P lam = (j : ℤ) - 2 * AppHalfPieces.hOf lam := by rw [hs, sub_eq_add_neg]
    refine ⟨fun x y u v => ?_, ?_, ?_⟩
    · change ((A lam ((j : ℤ) + halfShift P lam - halfShift P lam).toNat x y u v : ℤ) : ℚ) = _
      rw [toNat_shift, e]
      exact hA x y u v
    · change P.cap false 0 lam ((j : ℤ) + halfShift P lam - halfShift P lam).toNat = _
      rw [toNat_shift, e]
      exact hr
    · change P.cap true 0 lam ((j : ℤ) + halfShift P lam - halfShift P lam).toNat = _
      rw [toNat_shift, e]
      exact hc

/-- `HalfPieces`: Theorem B, for the functions of its proof. -/
theorem halfPieces : HalfPieces := halfPiecesFrom AppRunningTime.thmHalfPieces fromPadded

/-- `HalfPiecesExist`: Theorem B in the paper's words. -/
theorem halfPiecesExist : HalfPiecesExist :=
  let ⟨c, D, Alg, h, _⟩ := halfPieces
  ⟨c, D, Alg, h⟩

end PiecesCounted
