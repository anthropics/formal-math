/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PiecesFromEightSquaresStatement
public import GeneralPieces.ThmRunningTime
public import ClauseBoundStatement
public import Eight.SecCrossing_LemPieces
public import ClauseBound.Gen.Defs
import Eight.App_Pieces
import Eight.App_Rate

/-! # The pieces of Lemma 2 in Appendix A

`AppRunningTime.lemPiecesPieces`: the sentences after the definition of pieces with parameters (ρ,
c), clause by clause from Lemma 2 as it is proved from the eight-square identity (`Eight.lemPieces`,
`Eight.stFact`, `Eight.stAMul`) and from
«computable in time poly(λ)» (`Eight.stKeeps`, `Eight.stPoly`). `GeneralPieces.eight_isPieces`: the
functions A_0, …, A_t of Lemma 2, with their programs, are pieces with parameters (11/12, c) for
every c ≥ 8. -/

public section

namespace GeneralPieces

open Finset Groundwork PaddedDescent.F ClauseBound.Alg AppRunningTime Eight

/-- The functions A_0, …, A_t of Lemma 2, with their programs, are pieces with parameters (11/12, c)
for every c ≥ 8. -/
theorem eight_isPieces {c : ℕ} (hc : 8 ≤ c) : IsPieces (11 / 12) c eightF Eight.A valEight where
  rho_ge := by norm_num
  rho_lt := by norm_num
  c_pos := by omega
  d_pos _ _ := Nat.one_le_two_pow
  sum lam hl x y u v := by
    change ∑ i ∈ range (tOf lam + 1), Eight.A lam i x y u v = ((2 ^ tOf lam : ℕ) : ℤ) * Pieces.cross x y u v
    rw [lemPieces.a_sum lam hl]
    push_cast
    rfl
  row lam hl pad _ i hi x y u v :=
    ((stFact lam hl i (Nat.lt_succ_iff.1 hi)).1 x y u v).trans
      (sum_ofFn (crow lam i) fun θ => fTop (false, i, List.ofFn x, List.ofFn y, θ) * fBot (false, i, List.ofFn u, List.ofFn v, θ))
  col lam hl pad _ i hi x y u v :=
    ((stFact lam hl i (Nat.lt_succ_iff.1 hi)).2.1 x y u v).trans
      (sum_ofFn (ccol lam i) fun θ => fTop (true, i, List.ofFn x, List.ofFn u, θ) * fBot (true, i, List.ofFn y, List.ofFn v, θ))
  caps lam hl i hi := by
    have h1 := lemPieces.c_sum lam i hl (Nat.lt_succ_iff.1 hi)
    have h3 := one_le_logb hl
    have h4 : (8 : ℝ) ≤ c := by exact_mod_cast hc
    unfold rho at h1
    change ((crow lam i + ccol lam i : ℕ) : ℝ) ≤ _
    nlinarith
  card lam hl := by
    have h1 := tOf_le hl
    have h3 := two_mul_le_pow lam (c := c) (by omega)
    change tOf lam + 1 ≤ (2 * lam) ^ c
    omega
  size_d lam hl := by
    have h1 := tOf_le hl
    have h3 := two_mul_le_pow lam (c := c) (by omega)
    change 2 ^ tOf lam < 2 ^ (2 * lam) ^ c
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  size_A lam hl i hi x y u v := (lemPieces.a_abs lam i hl (Nat.lt_succ_iff.1 hi) x y u v).trans_lt (two_pow_tOf_lt hl (by omega))
  size_f lam hl pad _ i hi tr x y θ :=
    ⟨(((stFact lam hl i (Nat.lt_succ_iff.1 hi)).2.2 tr x y θ).1).trans_lt (two_pow_tOf_lt hl (by omega)),
      (((stFact lam hl i (Nat.lt_succ_iff.1 hi)).2.2 tr x y θ).2).trans_lt (two_pow_tOf_lt hl (by omega))⟩
  time_cnt := stKeeps.cnt.comp (h := fun lam : U => (([] : U), lam)) (by fun_prop)
  time_d := stKeeps.d.comp (g := fun lam : U => (([] : U), lam)) (by fun_prop)
  time_cap := stKeeps.cap.comp (h := fun p : Bool × U × ℕ => (p.1, ([] : U), p.2.1, p.2.2)) (by fun_prop)
  time_top := stKeeps.top
  time_bot := stKeeps.bot
  time_val := stPoly.1.comp (g := fun q : ValQ => (q.2.1.2, q.2.2)) (by fun_prop)
  val_eq lam _ _ _ i _ x y u v := stAMul lam i x y u v

end GeneralPieces

namespace AppRunningTime

open Eight GeneralPieces

/-- The sentences after the definition of pieces, as stated in
`PiecesFromEightSquaresStatement.lean`. -/
theorem lemPiecesPieces : LemPiecesPieces := fun c hc =>
  ⟨eight_isPieces hc, fun lam hl => ⟨rfl, rfl, fun i hi => ⟨rfl, rfl, by
    have h1 := lemPieces.c_sum lam i hl hi
    unfold rho at h1
    linarith⟩⟩⟩

end AppRunningTime
