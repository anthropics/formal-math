/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PiecesCounted.Padded
import PiecesCounted.PaddedData
import PiecesCounted.Sizes
import PiecesFromEightSquares.LemPieces
import Mathlib.Tactic

/-! # The pieces made from the eight-square identity

After Definition 7 the paper notes that, by Lemma 2, the functions A_0, …, A_t of Definition 5 are
pieces with parameters (11/12, c) for every large enough integer c ≥ 8, with 𝓘 = {0, …, t}, d = 2^t.
`PiecesFromEightSquaresStatement.lean` states this with a padding string, for every c ≥ 8
(`AppRunningTime.lemPiecesPieces`). The programs do not read the padding string (`ofPadded_eight`,
`answerOf_eight`: by unfolding `Eight.eightF` and `AppRunningTime.valEight`), so ONE algorithm,
which writes a single unit and then answers in one step, serves for every c ≥ 8. It takes two steps;
each state of the run holds either the question, with at most one unit of the padding string, or the
answer, and these fit `room c λ` by the size bounds of part (c) of Definition 7. So c₀ = 8. -/

public section

namespace PiecesCounted

open Finset Groundwork Groundwork.Prog ClauseBound.Alg

/-- The programs of these functions do not read the padding string: the data are the same for every
c. -/
theorem ofPadded_eight (c : ℕ) : ofPadded Eight.eightF Eight.A c (fun _ => 0) = ofPadded Eight.eightF Eight.A 0 fun _ => 0 := rfl

/-- Nor does the function that answers all questions. -/
theorem answerOf_eight (g : List Unit × Question) (pad pad' : List Unit) :
    answerOf Eight.eightF AppRunningTime.valEight (fun _ => 0) (g, pad) = answerOf Eight.eightF AppRunningTime.valEight (fun _ => 0) (g, pad') := by
  obtain ⟨u, q⟩ := g
  rcases q with q | q | q | q | q <;> rfl

/-- The condition on the shift, for the shift 0. -/
theorem shift_zero_lt (c lam : ℕ) : |(0 : ℤ)| + (2 * lam) ^ c < 2 ^ (2 * lam) ^ c := by
  have := Nat.lt_two_pow_self (n := (2 * lam) ^ c)
  rw [abs_zero, zero_add]
  exact_mod_cast this

/-- Clauses (a), (b) and the sizes of (c), for every c ≥ 8. -/
theorem eight_is {c : ℕ} (hc : 8 ≤ c) : (ofPadded Eight.eightF Eight.A 0 fun _ => 0).Is (11 / 12) c :=
  ofPadded_eight c ▸ ofPadded_is (AppRunningTime.lemPiecesPieces c hc).1 fun lam _ => shift_zero_lt c lam

/-- The one algorithm, within 2^{cλ} operations for every c ≥ 8. -/
theorem eight_computes {c : ℕ} (hc : 8 ≤ c) : Computes (algOf Eight.eightF AppRunningTime.valEight 0 fun _ => 0) (ofPadded Eight.eightF Eight.A 0 fun _ => 0) c :=
  computes_of_answer (eight_is hc) (Nat.zero_le c) le_rfl (by omega) fun g _ hg =>
    (answerOf_eight g _ _).trans (answerOf_eq (c := c) (shift := fun _ => 0) (AppRunningTime.lemPiecesPieces c hc).1 hg)

/-- `EightSquarePieces`, with c₀ = 8. -/
theorem eightSquarePieces : EightSquarePieces := by
  refine ⟨⟨8, algOf Eight.eightF AppRunningTime.valEight 0 fun _ => 0, le_rfl, fun c hc => ?_⟩, fun lam hl => ⟨?_, ?_, fun i hi => ⟨?_, ?_, ?_, ?_⟩⟩⟩
  · exact ⟨eight_is hc, algOf_polyT (AppRunningTime.lemPiecesPieces 8 le_rfl).1 (PolyT.const 0) 0, eight_computes hc⟩
  · change ((range (Eight.tOf lam + 1)).image fun i : ℕ => (i : ℤ) + 0) = _
    ext z
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨j, hj, rfl⟩
      constructor <;> omega
    · rintro ⟨h0, h1⟩
      exact ⟨z.toNat, by omega, by omega⟩
  · change ((2 ^ Eight.tOf lam : ℕ) : ℤ) = 2 ^ Eight.tOf lam
    simp
  · change Eight.A lam ((i : ℤ) - 0).toNat = Eight.A lam i
    rw [sub_zero, Int.toNat_natCast]
  · change Eight.eightF.cap false 0 lam ((i : ℤ) - 0).toNat = Eight.crow lam i
    rw [sub_zero, Int.toNat_natCast]
    rfl
  · change Eight.eightF.cap true 0 lam ((i : ℤ) - 0).toNat = Eight.ccol lam i
    rw [sub_zero, Int.toNat_natCast]
    rfl
  · exact (((AppRunningTime.lemPiecesPieces 8 le_rfl).2 lam hl).2.2 i hi).2.2

end PiecesCounted
