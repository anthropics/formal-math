/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.DefGenPieces.Conv
import PaddedDescent.F.FuelCert

/-! # «We may and do assume c_row, c_col ≤ 2λ», for the definition as stated

The remark after the definition of pieces with parameters (ρ, c) in Appendix A, proved as there: any
F : {0,1}^{2λ} × X' → ℤ factors through 2λ bits, as F(z,z') = Σ_θ [z = θ]·F(θ,z'), and a longer
factorization is replaced by this one. The second function, F(θ,z'), is computed by the program for
the values of the pieces, which is part of the definition.

One thing differs. The paper replaces c by c + 2, «which pays for computing c_row or c_col first».
Here the two new programs do not compute these numbers: they look at the length of the label θ,
which on the labels of min(c_row, 2λ) bits is the same choice, except that a factorization through
exactly 2λ bits is replaced as well. So the constant c stays the same. The new programs, `trimV`,
are defined in `DefGenPieces/Progs.lean`. -/

@[expose] public section

namespace GeneralPieces

open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen AppRunningTime

namespace DefGenPieces

open Trim

/-- Σ_θ [w = θ]·G(θ) = G(w) over the words of 2λ bits, and nothing changes over shorter words: a sum
t·b over the words of c₀ bits with the value V = G(w) is also the sum over the words of
min(c₀, 2λ) bits of the two functions that are [w = θ] and G on words of 2λ bits and t and b on all
others. -/
theorem sum_min_words {lam c₀ : ℕ} {w : List Bool} (hw : w.length = 2 * lam) (t b G : List Bool → ℤ) {V : ℤ} (h1 : V = ∑ θ ∈ words c₀, t θ * b θ) (h2 : G w = V) :
    V = ∑ θ ∈ words (min c₀ (2 * lam)),
      (bif decide (θ.length = 2 * lam) then (if w = θ then 1 else 0) else t θ) * (bif decide (θ.length = 2 * lam) then G θ else b θ) := by
  rcases lt_or_ge c₀ (2 * lam) with hc | hc
  · rw [min_eq_left hc.le, h1]
    refine Finset.sum_congr rfl fun θ hθ => ?_
    have : ¬ θ.length = 2 * lam := by rw [mem_words.1 hθ]; omega
    simp [this]
  · rw [min_eq_right hc, Finset.sum_eq_single_of_mem w (mem_words.2 hw)]
    · simp [hw, h2]
    · intro θ hθ hne
      simp [mem_words.1 hθ, hne.symm]

end DefGenPieces

open DefGenPieces Trim

section

variable {ρ : ℝ} {c : ℕ} {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : ValQ → ℤ}

/-- «We may and do assume c_row, c_col ≤ 2λ»: the new programs are pieces with the same parameters
(ρ, c), the same functions A_i and the same program for their values. -/
theorem trimV_isPieces (h : IsPieces ρ c P A val) : IsPieces ρ c (trimV P val c) A val := by
  have hb : ∀ lam, 1 ≤ lam → (1 : ℤ) < 2 ^ (2 * lam) ^ c := fun lam hl => one_lt_pow₀ (by norm_num) (pow_pos (by omega) c).ne'
  have ht := h.time_top
  have hbt := h.time_bot
  have hv := h.time_val
  have hlong : PolyT isLong := by unfold isLong; fun_prop
  have hask : PolyT askAt := by unfold askAt; fun_prop
  exact {
    rho_ge := h.rho_ge
    rho_lt := h.rho_lt
    c_pos := h.c_pos
    d_pos := h.d_pos
    sum := h.sum
    row := fun lam hl pad hp i hi x y u v => by
      have := sum_min_words (w := bitsOf x ++ bitsOf y) (lam := lam) (by simp; omega)
        (fun θ => P.top ((pad, false), (0, i), (bitsOf x, bitsOf y, θ))) (fun θ => P.bot ((pad, false), (0, i), (bitsOf u, bitsOf v, θ)))
        (fun θ => val (pad, (List.replicate lam (), i), (θ.take lam, θ.drop lam, bitsOf u, bitsOf v))) (h.row lam hl pad hp i hi x y u v)
        (by
          rw [List.take_left' (length_bitsOf x), List.drop_left' (length_bitsOf x)]
          exact h.val_eq lam hl pad hp i hi x y u v)
      simpa only [trimV, isLong, askAt, length_bitsOf, cond_false] using this
    col := fun lam hl pad hp i hi x y u v => by
      have := sum_min_words (w := bitsOf x ++ bitsOf u) (lam := lam) (by simp; omega)
        (fun θ => P.top ((pad, true), (0, i), (bitsOf x, bitsOf u, θ))) (fun θ => P.bot ((pad, true), (0, i), (bitsOf y, bitsOf v, θ)))
        (fun θ => val (pad, (List.replicate lam (), i), (θ.take lam, bitsOf y, θ.drop lam, bitsOf v))) (h.col lam hl pad hp i hi x y u v)
        (by
          rw [List.take_left' (length_bitsOf x), List.drop_left' (length_bitsOf x)]
          exact h.val_eq lam hl pad hp i hi x y u v)
      simpa only [trimV, isLong, askAt, length_bitsOf, cond_true] using this
    caps := fun lam hl i hi => le_trans
      (by exact_mod_cast Nat.add_le_add (min_le_left (P.cap false 0 lam i) (2 * lam)) (min_le_left (P.cap true 0 lam i) (2 * lam))) (h.caps lam hl i hi)
    card := h.card
    size_d := h.size_d
    size_A := h.size_A
    size_f := fun lam hl pad hp i hi tr x y θ => by
      cases hl' : isLong ((pad, tr), (0, i), (bitsOf x, bitsOf y, θ))
      · simp only [trimV, hl', cond_false]
        exact h.size_f lam hl pad hp i hi tr x y θ
      · have hθ : θ.length = 2 * lam := by simpa [isLong] using hl'
        simp only [trimV, hl', cond_true, length_bitsOf, askAt]
        constructor
        · split_ifs
          · simpa using hb lam hl
          · simp
        · obtain ⟨a, ha⟩ := exists_bitsOf (n := lam) (w := θ.take lam) (by simp; omega)
          obtain ⟨b, hb'⟩ := exists_bitsOf (n := lam) (w := θ.drop lam) (by simp; omega)
          rw [← ha, ← hb']
          cases tr
          · rw [cond_false, h.val_eq lam hl pad hp i hi]
            exact h.size_A lam hl i hi _ _ _ _
          · rw [cond_true, h.val_eq lam hl pad hp i hi]
            exact h.size_A lam hl i hi _ _ _ _
    time_cnt := h.time_cnt
    time_d := h.time_d
    time_cap := unary_min' h.time_cap.poly (by fun_prop)
    time_top := by unfold trimV; dsimp only; fun_prop
    time_bot := by unfold trimV; dsimp only; fun_prop
    time_val := h.time_val
    val_eq := h.val_eq }

/-- All numbers of bits of the new programs are at most 2λ. -/
theorem trimV_cap_le (P : PiecesF) (val : ValQ → ℤ) (c : ℕ) (tr : Bool) (h lam i : ℕ) : (trimV P val c).cap tr h lam i ≤ 2 * lam := min_le_right _ _

end

/-- «We may and do assume c_row, c_col ≤ 2λ», as stated in `AppRunningTimeStatement.lean`: the same
constant c, the same d, 𝓘 and A_i and the same program for the values. -/
theorem mayAssume : MayAssume := fun _ c P _ val h =>
  ⟨trimV P val c, trimV_isPieces h, fun _ => ⟨rfl, rfl⟩, fun tr lam i => trimV_cap_le P val c tr 0 lam i⟩

/-- What the proof of Theorem A uses: if there are pieces with parameters (ρ, c), there are programs
`P` with `Par P ρ c`, `P.Keeps` and `P.m = 1` (here `m` is a field of `PiecesF`, not a number of
clauses), with the same constant c. -/
theorem exist_par_one {ρ : ℝ} {c : ℕ} (h : Exist ρ c) : ∃ P : PiecesF, Par P ρ c ∧ P.Keeps ∧ P.m = 1 :=
  let ⟨P, A', val, hP⟩ := h
  let ⟨_, hP', _, hcap⟩ := mayAssume ρ c P A' val hP
  ⟨_, to_par_one hP' fun tr lam i _ _ => hcap tr lam i⟩

end GeneralPieces
