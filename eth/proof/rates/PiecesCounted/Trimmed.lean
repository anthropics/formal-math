/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PiecesCountedStatement
import PiecesCounted.Sizes
import ToTuring.Poly.Comb
import GeneralPieces.Trim.Prog
import Mathlib.Tactic

/-! # All numbers of bits at most 2λ

In the pieces of Definition 7 one may assume c^row_i, c^col_i ≤ 2λ: any F : {0,1}^{2λ} × 𝒳' → ℤ
factors through 2λ bits, as F(z, z') = Σ_{θ ∈ {0,1}^{2λ}} [z = θ] F(θ, z'), and a longer
factorization is replaced by this one, with c replaced by c + 2, which pays for computing c^row_i or
c^col_i first.
`trimmed D` are the data with every longer factorization replaced; d, 𝓘 and the A_i stay.
`assumeAlg Alg` is the new algorithm. It runs Alg once on a first question (`firstQ`): the question
itself, or, for a value of a function of a factorization, the number of bits of that factorization.
Then one step hands the answer of Alg to `afterFirst`, which either has the final answer (put out in
one more step) or a second question, on which Alg runs a second time: on the question itself if the
factorization was kept, on a question for a value of A_i if the value F(θ, z') is asked for. That
makes 2·2^{cλ} + 1 steps at most (2^{cλ} + 2 if the answer is there after the first run), which is
at most 2^{(c+2)λ};
the states hold the question beside a state of Alg, and fit `room (c + 2) λ`. This file has the
data, the algorithm with its certificate and its two kinds of run, and the arithmetic; `Assume.lean`
puts them together. -/

public section

namespace PiecesCounted

open Finset Groundwork Groundwork.Prog ClauseBound.Alg

/-! ### The new data -/

/-- Every factorization through more than 2λ bits is replaced by F(z, z') = Σ_θ [z = θ]·F(θ, z'), θ
a string of 2λ bits. -/
@[expose] def trimmed (D : Data) : Data where
  fam lam :=
    { d := (D.fam lam).d
      I := (D.fam lam).I
      A := (D.fam lam).A
      crow := fun i => min ((D.fam lam).crow i) (2 * lam)
      ccol := fun i => min ((D.fam lam).ccol i) (2 * lam) }
  fn lam tr side i z θ :=
    if D.cap lam tr i ≤ 2 * lam then D.fn lam tr side i z θ
    else if side then
      (if tr then (D.fam lam).A i (toBits lam (θ.take lam)) z.1 (toBits lam (θ.drop lam)) z.2
      else (D.fam lam).A i (toBits lam (θ.take lam)) (toBits lam (θ.drop lam)) z.1 z.2)
    else if bitsOf z.1 ++ bitsOf z.2 = θ then 1 else 0

/-- The new numbers of bits. -/
theorem trimmed_cap (D : Data) (lam : ℕ) (tr : Bool) (i : ℤ) : (trimmed D).cap lam tr i = min (D.cap lam tr i) (2 * lam) := by cases tr <;> rfl

/-- A factorization through at most 2λ bits is kept. -/
theorem trimmed_fn_of_le {D : Data} {lam : ℕ} {tr : Bool} {i : ℤ} (hc : D.cap lam tr i ≤ 2 * lam) (side : Bool) (z : Pieces.Bits lam × Pieces.Bits lam) (θ : List Bool) :
    (trimmed D).fn lam tr side i z θ = D.fn lam tr side i z θ := if_pos hc

/-- The function of the first pair in the new factorization: [z = θ]. -/
theorem trimmed_fn_first {D : Data} {lam : ℕ} {tr : Bool} {i : ℤ} (hc : ¬ D.cap lam tr i ≤ 2 * lam) (z : Pieces.Bits lam × Pieces.Bits lam) (θ : List Bool) :
    (trimmed D).fn lam tr false i z θ = if bitsOf z.1 ++ bitsOf z.2 = θ then 1 else 0 := (if_neg hc).trans (if_neg (by simp))

/-- The function of the second pair in the new factorization, as a function of (x, y) and (u, v):
F(θ, z') = A_i(θ₁, θ₂, u, v). -/
theorem trimmed_fn_row {D : Data} {lam : ℕ} {i : ℤ} (hc : ¬ D.cap lam false i ≤ 2 * lam) (z : Pieces.Bits lam × Pieces.Bits lam) (θ : List Bool) :
    (trimmed D).fn lam false true i z θ = (D.fam lam).A i (toBits lam (θ.take lam)) (toBits lam (θ.drop lam)) z.1 z.2 := ((if_neg hc).trans (if_pos rfl)).trans (if_neg (by simp))

/-- The same as a function of (x, u) and (y, v): F(θ, z') = A_i(θ₁, y, θ₂, v). -/
theorem trimmed_fn_col {D : Data} {lam : ℕ} {i : ℤ} (hc : ¬ D.cap lam true i ≤ 2 * lam) (z : Pieces.Bits lam × Pieces.Bits lam) (θ : List Bool) :
    (trimmed D).fn lam true true i z θ = (D.fam lam).A i (toBits lam (θ.take lam)) z.1 (toBits lam (θ.drop lam)) z.2 := ((if_neg hc).trans (if_pos rfl)).trans (if_pos rfl)

/-- A string written as a list and read again. -/
theorem toBits_bitsOf {n : ℕ} (x : Pieces.Bits n) : toBits n (bitsOf x) = x := by
  funext j
  simp [toBits, bitsOf, List.getD_eq_getElem?_getD, j.isLt]

/-- The first half of two strings written one after the other. -/
theorem toBits_take {n : ℕ} (x y : Pieces.Bits n) : toBits n ((bitsOf x ++ bitsOf y).take n) = x := by
  rw [List.take_left' (GeneralPieces.Trim.length_bitsOf x), toBits_bitsOf]

/-- The second half. -/
theorem toBits_drop {n : ℕ} (x y : Pieces.Bits n) : toBits n ((bitsOf x ++ bitsOf y).drop n) = y := by
  rw [List.drop_left' (GeneralPieces.Trim.length_bitsOf x), toBits_bitsOf]

/-- F(z, z') = Σ_θ [z = θ]·F(θ, z'), over the strings θ of 2λ bits. -/
theorem sum_indicator {n : ℕ} (x y : Pieces.Bits n) (F : List Bool → ℤ) : ∑ θ ∈ words (2 * n), (if bitsOf x ++ bitsOf y = θ then 1 else 0) * F θ = F (bitsOf x ++ bitsOf y) := by
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (mem_words.2 (by rw [List.length_append, GeneralPieces.Trim.length_bitsOf, GeneralPieces.Trim.length_bitsOf]; omega))]

/-- The new data have clauses (a), (b) and the sizes of (c), with the same ρ and c. -/
theorem trimmed_is {D : Data} {ρ : ℝ} {c : ℕ} (h : D.Is ρ c) : (trimmed D).Is ρ c := by
  have hX : ∀ lam, 1 ≤ lam → (1 : ℤ) < 2 ^ (2 * lam) ^ c := fun lam hl => one_lt_pow₀ (by norm_num) (Nat.pos_iff_ne_zero.1 (Nat.pow_pos (by omega)))
  refine ⟨h.rho_ge, h.rho_lt, h.c_pos, h.d_pos, h.sum, fun lam hl i hi x y u v => ?_, fun lam hl i hi x y u v => ?_, fun lam hl i hi => ?_, h.card, h.size_d, h.size_I, h.size_A,
    fun lam hl i hi tr side z θ hθ => ?_⟩
  · change (D.fam lam).A i x y u v = _
    rw [trimmed_cap]
    by_cases hc : D.cap lam false i ≤ 2 * lam
    · rw [min_eq_left hc]
      simp only [trimmed_fn_of_le hc]
      exact h.row lam hl i hi x y u v
    · rw [min_eq_right (by omega)]
      simp only [trimmed_fn_first hc, trimmed_fn_row hc]
      rw [sum_indicator x y fun θ => (D.fam lam).A i (toBits lam (θ.take lam)) (toBits lam (θ.drop lam)) u v, toBits_take, toBits_drop]
  · change (D.fam lam).A i x y u v = _
    rw [trimmed_cap]
    by_cases hc : D.cap lam true i ≤ 2 * lam
    · rw [min_eq_left hc]
      simp only [trimmed_fn_of_le hc]
      exact h.col lam hl i hi x y u v
    · rw [min_eq_right (by omega)]
      simp only [trimmed_fn_first hc, trimmed_fn_col hc]
      rw [sum_indicator x u fun θ => (D.fam lam).A i (toBits lam (θ.take lam)) y (toBits lam (θ.drop lam)) v, toBits_take, toBits_drop]
  · refine le_trans ?_ (h.caps lam hl i hi)
    rw [trimmed_cap, trimmed_cap]
    exact_mod_cast Nat.add_le_add (min_le_left _ _) (min_le_left _ _)
  · by_cases hc : D.cap lam tr i ≤ 2 * lam
    · rw [trimmed_fn_of_le hc]
      rw [trimmed_cap, min_eq_left hc] at hθ
      exact h.size_f lam hl i hi tr side z θ hθ
    · cases side
      · rw [trimmed_fn_first hc]
        have := hX lam hl
        split
        · simpa using this
        · simp
      · cases tr
        · rw [trimmed_fn_row hc]
          exact h.size_A lam hl i hi _ _ _ _
        · rw [trimmed_fn_col hc]
          exact h.size_A lam hl i hi _ _ _ _

/-! ### The new algorithm -/

/-- The first question: the question itself; for a value of a function of a factorization, the
number of bits of that factorization. -/
@[expose] def firstQ (g : List Unit × Question) : List Unit × Question :=
  (g.1, g.2.elim (fun _ => g.2) fun q => q.elim (fun _ => g.2) fun q => q.elim (fun _ => g.2) fun q => q.elim (fun _ => g.2) fun q => .inr (.inr (.inl (q.1.1, q.2.1))))

/-- After the first answer: the answer to the question (left), or the second question (right). -/
@[expose] def afterFirst (p : (List Unit × Question) × Answer) : Answer ⊕ (List Unit × Question) :=
  p.1.2.elim (fun _ => .inl p.2) fun q => q.elim (fun _ => .inl p.2) fun q =>
    q.elim (fun _ => .inl (p.2.elim (fun z => .inl (if z ≤ ((2 * p.1.1.length : ℕ) : ℤ) then z else ((2 * p.1.1.length : ℕ) : ℤ))) fun l => .inr l)) fun q =>
      q.elim (fun _ => .inl p.2) fun q =>
        if p.2.elim (fun z => z) (fun _ => 0) ≤ ((2 * p.1.1.length : ℕ) : ℤ) then .inr p.1
        else bif q.1.2 then
          .inr (p.1.1, .inr (.inr (.inr (.inl (q.2.1, bif q.1.1 then (q.2.2.2.2.take p.1.1.length, q.2.2.1, q.2.2.2.2.drop p.1.1.length, q.2.2.2.1)
            else (q.2.2.2.2.take p.1.1.length, q.2.2.2.2.drop p.1.1.length, q.2.2.1, q.2.2.2.1))))))
        else .inl (.inl (if q.2.2.1 ++ q.2.2.2.1 = q.2.2.2.2 then 1 else 0))

/-- The new algorithm: Alg on the first question; one step for the hand-over; then the answer in one
more step, or Alg on the second question. -/
@[expose] def assumeAlg (Alg : Stepped (List Unit × Question) Answer) : Stepped (List Unit × Question) Answer :=
  Stepped.bind (Stepped.mapIn firstQ Alg) (Stepped.branch afterFirst (Stepped.ofFun fun a : Answer => a) Alg)

/-- The first question is computed in polynomial time. -/
theorem firstQ_polyT : PolyT firstQ := by unfold firstQ; fun_prop

/-- So is what follows the first answer. -/
theorem afterFirst_polyT : PolyT afterFirst := by unfold afterFirst; fun_prop

/-- The new algorithm has polynomial-time steps. -/
theorem assumeAlg_polyT {Alg : Stepped (List Unit × Question) Answer} (h : Nonempty (IsPolyT Alg)) : Nonempty (IsPolyT (assumeAlg Alg)) := by
  obtain ⟨hA⟩ := h
  have : IsPolyT (Stepped.mapIn firstQ Alg) := IsPolyT.mapIn firstQ_polyT
  have : IsPolyT (Stepped.ofFun fun a : Answer => a) := IsPolyT.ofFun (by fun_prop)
  have : IsPolyT (Stepped.branch afterFirst (Stepped.ofFun fun a : Answer => a) Alg) := IsPolyT.branch afterFirst_polyT
  exact ⟨IsPolyT.bind⟩

/-- The run in which the answer is there after the first run of Alg. -/
theorem assumeAlg_runs_one {Alg : Stepped (List Unit × Question) Answer} {g : List Unit × Question} {a₀ a : Answer} {t S : ℕ} (h1 : Alg.Runs (firstQ g) t S a₀) (h2 : afterFirst (g, a₀) = .inl a) :
    (assumeAlg Alg).Runs g (t + 1 + 1) (max (size g + S) (max (size a) (size a) + 1 + 1) + 1) a :=
  Stepped.bind_runs (Stepped.mapIn_runs h1) (Stepped.branch_runs_inl h2 (Stepped.ofFun_runs (fun a : Answer => a) a))

/-- The run with a second run of Alg. -/
theorem assumeAlg_runs_two {Alg : Stepped (List Unit × Question) Answer} {g g' : List Unit × Question} {a₀ a : Answer} {t t' S S' : ℕ} (h1 : Alg.Runs (firstQ g) t S a₀)
    (h2 : afterFirst (g, a₀) = .inr g') (h3 : Alg.Runs g' t' S' a) : (assumeAlg Alg).Runs g (t + 1 + t') (max (size g + S) (S' + 1) + 1) a :=
  Stepped.bind_runs (Stepped.mapIn_runs h1) (Stepped.branch_runs_inr h2 h3)

/-! ### What the oracle answers -/

/-- The answer to the question for a number of bits. -/
theorem oracle_cap {D : Data} {u : List Unit} (hl : 1 ≤ u.length) {i : ℤ} (hi : i ∈ (D.fam u.length).I) (tr : Bool) :
    D.oracle (u, .inr (.inr (.inl (tr, i)))) = some (.inl (D.cap u.length tr i)) := (if_pos hl).trans (if_pos hi)

/-- The answer to the question for a value of A_i. -/
theorem oracle_value {D : Data} {u : List Unit} (hl : 1 ≤ u.length) {i : ℤ} (hi : i ∈ (D.fam u.length).I) {l1 l2 l3 l4 : List Bool} (e1 : l1.length = u.length) (e2 : l2.length = u.length)
    (e3 : l3.length = u.length) (e4 : l4.length = u.length) :
    D.oracle (u, .inr (.inr (.inr (.inl (i, l1, l2, l3, l4))))) = some (.inl ((D.fam u.length).A i (toBits _ l1) (toBits _ l2) (toBits _ l3) (toBits _ l4))) :=
  (if_pos hl).trans (if_pos ⟨hi, e1, e2, e3, e4⟩)

/-- The answer to the question for a value of a function of a factorization. -/
theorem oracle_fn {D : Data} {u : List Unit} (hl : 1 ≤ u.length) {i : ℤ} (hi : i ∈ (D.fam u.length).I) {tr : Bool} (side : Bool) {l1 l2 θ : List Bool} (e1 : l1.length = u.length)
    (e2 : l2.length = u.length) (e3 : θ.length = D.cap u.length tr i) :
    D.oracle (u, .inr (.inr (.inr (.inr ((tr, side), i, l1, l2, θ))))) = some (.inl (D.fn u.length tr side i (toBits _ l1, toBits _ l2) θ)) :=
  (if_pos hl).trans (if_pos ⟨hi, e1, e2, e3⟩)

/-! ### The bounds -/

/-- 4·2^{cλ} ≤ 2^{(c+2)λ} for λ ≥ 1. -/
theorem four_steps_le (c : ℕ) {lam : ℕ} (hl : 1 ≤ lam) : 4 * steps c lam ≤ steps (c + 2) lam := by
  have h1 : 2 ^ ((c + 2) * lam) = 2 ^ (c * lam) * 2 ^ (2 * lam) := by rw [Nat.add_mul, pow_add]
  have h2 : 2 ^ 2 ≤ 2 ^ (2 * lam) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 := Nat.mul_le_mul_left (2 ^ (c * lam)) h2
  unfold steps
  omega

/-- 2·room c λ + 3 ≤ room (c + 2) λ for c, λ ≥ 1. -/
theorem two_room_le {c lam : ℕ} (hc : 1 ≤ c) (hl : 1 ≤ lam) : 2 * room c lam + 3 ≤ room (c + 2) lam := by
  have h1 : 4 * 2 ^ (c * lam) ≤ 2 ^ ((c + 2) * lam) := four_steps_le c hl
  have h2 : 4 * (2 * lam) ^ c ≤ (2 * lam) ^ (c + 2) := by
    have e : (2 * lam) ^ (c + 2) = (2 * lam) ^ c * (2 * lam) ^ 2 := pow_add _ _ _
    have e2 : 2 ^ 2 ≤ (2 * lam) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have := Nat.mul_le_mul_left ((2 * lam) ^ c) e2
    omega
  have h3 : (4 * 2 ^ (c * lam) + 4 * (2 * lam) ^ c + 8) * (4 * (2 * lam) ^ c + 8) ≤ room (c + 2) lam :=
    Nat.mul_le_mul (by omega) (by omega)
  have h4 : (4 * 2 ^ (c * lam) + 4 * (2 * lam) ^ c + 8) * (4 * (2 * lam) ^ c + 8) =
      16 * (2 ^ (c * lam) * (2 * lam) ^ c) + 32 * 2 ^ (c * lam) + 16 * ((2 * lam) ^ c * (2 * lam) ^ c) + 64 * (2 * lam) ^ c + 64 := by ring
  have h5 := room_eq c lam
  have h6 := two_mul_le_pow hc lam
  have h7 : 1 ≤ 2 ^ (c * lam) := Nat.one_le_two_pow
  omega

end PiecesCounted
