/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PiecesCounted.PadThen
import PiecesCounted.PaddedData
import PiecesCounted.Sizes
import ToTuring.Lib.Int
import ToTuring.Lib.Unary
import Mathlib.Tactic

/-! # From the padding string to counted operations

`AppRunningTime.IsPieces` (`AppRunningTimeStatement.lean`) has six programs and a padding string of
2^{cλ} units, and numbers the index set 𝓘 from 0. The data are treated in `PaddedData.lean`. Here:
ONE function `answerOf` of (λ in unary, question) and a padding string, made from the six programs
and the shift of the index set; it is polynomial-time (`answerOf_polyT`) and gives the right answer
when the padding string has 2^{cλ} units (`answerOf_eq`).
The algorithm is `padThen` of it (`algOf`): it writes the padding string, one unit in each step, and
answers in one more step. It halts within 2^{cλ} + 1 steps, which is at most 2^{(c+1)λ}, and its
states fit `room c λ` ≤ `room (c + 1) λ` (`computes_of_answer`). So c' = c + 1 (`fromPadded`).
`computes_of_answer` is stated for a string of 2^{kλ} units with any k ≤ c, and for every c' ≥ c
with c' > k, since the pieces made from the eight-square identity (Lemma 2) take k = 0. -/

public section

namespace PiecesCounted

open Finset Groundwork Groundwork.Prog ClauseBound.Alg

/-! ### One function for all questions -/

/-- The answer to a question, from the six programs and the shift: a function of ((λ in unary,
question), padding string). -/
@[expose] def answerOf (P : PiecesF) (val : AppRunningTime.ValQ → ℤ) (shift : ℕ → ℤ) (x : (List Unit × Question) × List Unit) : Answer :=
  x.1.2.elim (fun _ => .inl (P.d 0 x.1.1.length : ℤ)) fun q =>
    q.elim (fun _ => .inr ((List.range (P.cnt 0 x.1.1.length)).map fun i : ℕ => (i : ℤ) + shift x.1.1.length)) fun q =>
      q.elim (fun q => .inl (P.cap q.1 0 x.1.1.length (q.2 - shift x.1.1.length).toNat : ℤ)) fun q =>
        q.elim (fun q => .inl (val (x.2, (x.1.1, (q.1 - shift x.1.1.length).toNat), q.2))) fun q =>
          .inl (bif q.1.2 then P.bot ((x.2, q.1.1), (0, (q.2.1 - shift x.1.1.length).toNat), q.2.2) else P.top ((x.2, q.1.1), (0, (q.2.1 - shift x.1.1.length).toNat), q.2.2))

/-- The shape of `answerOf`, for any polynomial-time parts. -/
theorem answer_polyT {dF : List Unit → ℕ} {rg : List Unit → List ℕ} {capF : Bool × List Unit × ℕ → ℕ} {sh : List Unit → ℤ} {top bot : PQ → ℤ} {val : AppRunningTime.ValQ → ℤ}
    (hd : PolyT dF) (hr : PolyT rg) (hc : PolyT capF) (hs : PolyT sh) (ht : PolyT top) (hb : PolyT bot) (hv : PolyT val) :
    PolyT fun x : (List Unit × Question) × List Unit =>
      x.1.2.elim (fun _ => (.inl (dF x.1.1 : ℤ) : Answer)) fun q =>
        q.elim (fun _ => (.inr ((rg x.1.1).map fun i : ℕ => (i : ℤ) + sh x.1.1) : Answer)) fun q =>
          q.elim (fun q => (.inl (capF (q.1, x.1.1, (q.2 - sh x.1.1).toNat) : ℤ) : Answer)) fun q =>
            q.elim (fun q => (.inl (val (x.2, (x.1.1, (q.1 - sh x.1.1).toNat), q.2)) : Answer)) fun q =>
              (.inl (bif q.1.2 then bot ((x.2, q.1.1), (0, (q.2.1 - sh x.1.1).toNat), q.2.2) else top ((x.2, q.1.1), (0, (q.2.1 - sh x.1.1).toNat), q.2.2)) : Answer) := by
  fun_prop

/-- `answerOf` is polynomial-time in the question and the padding string. -/
theorem answerOf_polyT {ρ : ℝ} {c : ℕ} {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : AppRunningTime.ValQ → ℤ} {shift : ℕ → ℤ} (h : AppRunningTime.IsPieces ρ c P A val)
    (hs : PolyT fun u : List Unit => shift u.length) : PolyT (answerOf P val shift) :=
  answer_polyT (dF := fun u => P.d 0 u.length) (rg := fun u => List.range (P.cnt 0 u.length)) (capF := fun p => P.cap p.1 0 p.2.1.length p.2.2) (sh := fun u => shift u.length)
    h.time_d (PolyT.range h.time_cnt) h.time_cap.poly hs h.time_top h.time_bot h.time_val

/-- `answerOf` gives the right answer when the padding string has 2^{cλ} units. -/
theorem answerOf_eq {ρ : ℝ} {c : ℕ} {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : AppRunningTime.ValQ → ℤ} {shift : ℕ → ℤ} (h : AppRunningTime.IsPieces ρ c P A val)
    {g : List Unit × Question} {a : Answer} (hg : (ofPadded P A c shift).oracle g = some a) : answerOf P val shift (g, List.replicate (2 ^ (c * g.1.length)) ()) = a := by
  obtain ⟨hl, ha⟩ := oracle_eq_some hg
  obtain ⟨u, q⟩ := g
  dsimp only at hl ha ⊢
  rcases q with q | q | q | q | q
  · obtain rfl := Option.some.inj ha
    rfl
  · obtain rfl := Option.some.inj ha
    exact congrArg Sum.inr (sort_image_shift _ _).symm
  · simp only [Data.answer] at ha
    split at ha
    · obtain rfl := Option.some.inj ha
      obtain ⟨tr, i⟩ := q
      cases tr <;> rfl
    · cases ha
  · simp only [Data.answer] at ha
    split at ha
    · rename_i hi
      obtain rfl := Option.some.inj ha
      obtain ⟨i, l1, l2, l3, l4⟩ := q
      obtain ⟨hi, e1, e2, e3, e4⟩ := hi
      dsimp only at hi e1 e2 e3 e4
      obtain ⟨j, hj, rfl⟩ := mem_ofPadded hi
      have h1 := h.val_eq u.length hl (List.replicate (2 ^ (c * u.length)) ()) (by rw [List.length_replicate]) j hj (toBits _ l1) (toBits _ l2) (toBits _ l3) (toBits _ l4)
      rw [bitsOf_toBits e1, bitsOf_toBits e2, bitsOf_toBits e3, bitsOf_toBits e4, units_eq] at h1
      change Sum.inl (val (List.replicate (2 ^ (c * u.length)) (), (u, ((j : ℤ) + shift u.length - shift u.length).toNat), (l1, l2, l3, l4))) =
        Sum.inl (A u.length ((j : ℤ) + shift u.length - shift u.length).toNat (toBits _ l1) (toBits _ l2) (toBits _ l3) (toBits _ l4))
      rw [toNat_shift, h1]
    · cases ha
  · simp only [Data.answer] at ha
    split at ha
    · rename_i hi
      obtain rfl := Option.some.inj ha
      obtain ⟨⟨tr, side⟩, i, l1, l2, θ⟩ := q
      obtain ⟨hi, e1, e2, e3⟩ := hi
      dsimp only at hi e1 e2 e3
      cases side
      · change Sum.inl (P.top ((List.replicate (2 ^ (c * u.length)) (), tr), (0, (i - shift u.length).toNat), (l1, l2, θ))) =
          Sum.inl (P.top ((List.replicate (2 ^ (c * u.length)) (), tr), (0, (i - shift u.length).toNat), (bitsOf (toBits u.length l1), bitsOf (toBits u.length l2), θ)))
        rw [bitsOf_toBits e1, bitsOf_toBits e2]
      · change Sum.inl (P.bot ((List.replicate (2 ^ (c * u.length)) (), tr), (0, (i - shift u.length).toNat), (l1, l2, θ))) =
          Sum.inl (P.bot ((List.replicate (2 ^ (c * u.length)) (), tr), (0, (i - shift u.length).toNat), (bitsOf (toBits u.length l1), bitsOf (toBits u.length l2), θ)))
        rw [bitsOf_toBits e1, bitsOf_toBits e2]
    · cases ha

/-! ### The algorithm -/

/-- The algorithm: write 2^{kλ} units, one in each step, then answer in one step. -/
@[expose] def algOf (P : PiecesF) (val : AppRunningTime.ValQ → ℤ) (k : ℕ) (shift : ℕ → ℤ) : Stepped (List Unit × Question) Answer :=
  padThen (fun g => 2 ^ (k * g.1.length)) (answerOf P val shift)

/-- 2^{kλ} is computed in polynomial time from λ in unary. -/
theorem two_pow_polyT (k : ℕ) : PolyT fun g : List Unit × Question => 2 ^ (k * g.1.length) :=
  PolyT.two_pow (e := fun g : List Unit × Question => k * g.1.length) ((Unary.const k).mul (Unary.of_length (by fun_prop)))

/-- The algorithm has polynomial-time steps. -/
theorem algOf_polyT {ρ : ℝ} {c : ℕ} {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : AppRunningTime.ValQ → ℤ} {shift : ℕ → ℤ} (h : AppRunningTime.IsPieces ρ c P A val)
    (hs : PolyT fun u : List Unit => shift u.length) (k : ℕ) : Nonempty (IsPolyT (algOf P val k shift)) :=
  ⟨padThenIsPolyT (two_pow_polyT k) (answerOf_polyT h hs)⟩

/-- A function of the question and a padding string that gives the right answer at 2^{kλ} units, k ≤
c, gives an algorithm within 2^{c'λ} operations, for every c' ≥ c with c' > k. -/
theorem computes_of_answer {D : Data} {ρ : ℝ} {c c' k : ℕ} (hD : D.Is ρ c) (hk : k ≤ c) (hc : c ≤ c') (hk' : k + 1 ≤ c') {f : (List Unit × Question) × List Unit → Answer}
    (hf : ∀ g a, D.oracle g = some a → f (g, List.replicate (2 ^ (k * g.1.length)) ()) = a) : Computes (padThen (fun g => 2 ^ (k * g.1.length)) f) D c' := by
  intro g a hg
  have hl := (oracle_eq_some hg).1
  have h1 := hD.size_question_le' hg
  have h2 := hD.size_answer_le' hg
  have h3 : 2 ^ (k * g.1.length) ≤ 2 ^ (c * g.1.length) := steps_le_of_le _ hk
  have h4 := room_eq c g.1.length
  have h5 := room_le_of_le hl hc
  have h6 : size (2 ^ (k * g.1.length)) ≤ 2 ^ (k * g.1.length) + 1 := by
    have := Nat.size_le.2 (Nat.lt_two_pow_self (n := 2 ^ (k * g.1.length)))
    rw [size_nat]
    omega
  have r := padThen_runs (fun g : List Unit × Question => 2 ^ (k * g.1.length)) f g (S := room c' g.1.length) (by omega) (by rw [hf g a hg]; omega)
  rw [hf g a hg] at r
  refine r.mono ?_ le_rfl
  have h7 : 2 ^ ((k + 1) * g.1.length) = 2 ^ (k * g.1.length) * 2 ^ g.1.length := by rw [Nat.add_mul, Nat.one_mul, pow_add]
  have h8 : 2 ≤ 2 ^ g.1.length := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ g.1.length := Nat.pow_le_pow_right (by norm_num) hl
  have h9 := Nat.mul_le_mul_left (2 ^ (k * g.1.length)) h8
  have h10 : 1 ≤ 2 ^ (k * g.1.length) := Nat.one_le_two_pow
  have h11 : 2 ^ ((k + 1) * g.1.length) ≤ 2 ^ (c' * g.1.length) := steps_le_of_le _ hk'
  change 2 ^ (k * g.1.length) + 1 ≤ 2 ^ (c' * g.1.length)
  omega

/-- `FromPadded`, with c' = c + 1. -/
theorem fromPadded : FromPadded := fun _ c P _ val shift h hsh hs =>
  ⟨c + 1, algOf P val c shift, Nat.le_succ c, (ofPadded_is h hs).grow le_rfl h.rho_lt (Nat.le_succ c), algOf_polyT h hsh c,
    computes_of_answer (ofPadded_is h hs) le_rfl (Nat.le_succ c) le_rfl fun _ _ hg => answerOf_eq h hg⟩

end PiecesCounted
