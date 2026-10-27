/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.Level.Defs
public import SingleBitPieces.Level.Pieces
import Mathlib.Tactic

/-! # Lemma 2 from the eight-square identity in the form that the networks of a grid need

The counterpart of proof/networks/SingleBitPieces/Level/Pieces.lean for the pieces of Lemma 2 from
the eight-square identity. `stPieces_of`: the functions A_0, …, A_t, t = ⌈λ/3⌉, add up to 2^t·[x =
v][y = u] (Lemma 2(a)); the programs `Eight.fTop`, `Eight.fBot` factorize A_i over all words of
c_i^row bits row-wise and of c_i^col bits column-wise (Lemma 2(b), in the form `Eight.StFact`);
these numbers of bits are at most 2λ (Lemma 2(c)); and all values are at most 2^t in absolute value
(Lemma 2(a) and (b)).
Parts (a) and (b) are hypotheses here; `stPieces_of_lemPieces` takes part (a) from `LemPieces`. From
proof/networks/SingleBitPieces/Level/Pieces.lean only `sum_ofFn` is used, which does not speak of
any pieces. -/

public section

namespace Eight.Level

open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Finset

/-- Lemma 2 in the form that the networks of a grid need, from Lemma 2(a), that A_0 + … + A_t =
2^t·[x = v][y = u] and |A_i| ≤ 2^t (`ha_sum`, `ha_abs`: the fields `a_sum` and `a_abs` of
`Eight.LemPieces`), and Lemma 2(b) for the
programs (`hF`). The bounds c_i^row ≤ 2λ and c_i^col ≤ 2λ of Lemma 2(c) hold by the definition of
the two numbers as minima. -/
theorem stPieces_of (hF : StFact)
    (ha_sum : ∀ lam : ℕ, 1 ≤ lam → ∀ x y u v : Pieces.Bits lam, ∑ i ∈ range (tOf lam + 1), A lam i x y u v = 2 ^ tOf lam * Pieces.cross x y u v)
    (ha_abs : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → ∀ x y u v : Pieces.Bits lam, |A lam i x y u v| ≤ 2 ^ tOf lam) : StPieces := by
  intro lam hlam
  refine ⟨ha_sum lam hlam, ?_⟩
  have hb : ∀ i, i < eightF.cnt 0 lam → _ := fun i hi => hF lam hlam i (Nat.lt_succ_iff.1 hi)
  refine ⟨Nat.succ_pos _, le_rfl, fun tr i hi x y u v => ?_, fun tr i _ => ?_, fun i hi x y u v => ?_, fun tr i hi x y θ => ?_, fun tr i hi x y θ => ?_⟩
  · cases tr
    · exact ((hb i hi).1 x y u v).trans
        (SingleBitPieces.Level.Pieces.sum_ofFn _ fun θ => fTop (false, i, List.ofFn x, List.ofFn y, θ) * fBot (false, i, List.ofFn u, List.ofFn v, θ))
    · exact ((hb i hi).2.1 x u y v).trans
        (SingleBitPieces.Level.Pieces.sum_ofFn _ fun θ => fTop (true, i, List.ofFn x, List.ofFn y, θ) * fBot (true, i, List.ofFn u, List.ofFn v, θ))
  · cases tr
    · exact (min_le_left _ _).trans_eq (by change 2 * lam = 2 * 1 * lam; rw [mul_one])
    · exact (min_le_left _ _).trans_eq (by change 2 * lam = 2 * 1 * lam; rw [mul_one])
  · exact ha_abs lam i hlam (Nat.lt_succ_iff.1 hi) x y u v
  · exact ((hb i hi).2.2 tr x y θ).1
  · exact ((hb i hi).2.2 tr x y θ).2

/-- The same, with part (a) taken from `LemPieces` (its fields `a_sum` and `a_abs`); part (b) for
the programs stays a hypothesis (`hF`). -/
theorem stPieces_of_lemPieces (h2 : LemPieces) (hF : StFact) : StPieces := stPieces_of hF h2.a_sum h2.a_abs

end Eight.Level
