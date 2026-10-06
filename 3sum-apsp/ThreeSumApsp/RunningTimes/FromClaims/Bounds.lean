/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Machine.Realized
public import ThreeSumApsp.TimeClaims.Sec3.Definitions

/-!
# From a realized running time to a program with the paper's bound

A claim gives a running time `T` with `T ≤ C X`, where `X` is the bound that the paper prints, and
`RealizedWithin` gives a program that takes `c T + c` steps.  This file puts the two together.

* Bounds in several parameters, valid on a domain on which `X ≥ 1`: `exists_solves`, and
  `exists_solves_nonneg` with `exists_solves_pair` for two programs with one slope and one constant.
* Bounds `O(n^a (log n)^e)` in one size, valid for all large `n`: `solvedAt_of_realized`, and for
  every exponent `κ` of the magnitude `solvedInTime_of_claim` and `solvedInPolylogTime_of_claim`.
* An instance with numbers bounded by `n^κ` is also one with numbers bounded by `n^κ'`, `κ ≤ κ'`
  (`solvedInTimeAt_mono`), so that a bound for all `κ ≥ 1` is a bound for all `κ`
  (`solvedInTime_of_one_le`).
-/

public section

namespace ThreeSumApsp.FromClaims

open ThreeSumApsp.WordRam
open EndStatement (Instr)

/-! ## Bounds on a domain -/

/-- `c T + c ≤ (c |C| + c) X` if `T ≤ C X`, `X ≥ 1` and `c ≥ 0`. -/
private theorem mul_add_le_of_le_mul {c C T X : ℝ} (hc : 0 ≤ c) (hT : T ≤ C * X) (hX : 1 ≤ X) :
    c * T + c ≤ (c * |C| + c) * X := by
  have hCX : C * X ≤ |C| * X := mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
  have hcT : c * T ≤ c * (|C| * X) := mul_le_mul_of_nonneg_left (hT.trans hCX) hc
  have hcX : c ≤ c * X := le_mul_of_one_le_right hc hX
  linarith

/-- The bound `U = N^c` on the numbers, as a real number. -/
theorem cast_pow_eq (N c : ℕ) : ((N ^ c : ℕ) : ℝ) = (N : ℝ) ^ ((c : ℕ) : ℝ) := by
  rw [Real.rpow_natCast]
  push_cast
  rfl

/-- If the running time `T` is realized, and `T ≤ C X` and `X ≥ 1` on the instances in `dom'`, whose
numbers are bounded by the `κ`-th power of the size, then a program solves them in `O(X)` steps. -/
theorem exists_solves_nonneg {prob : Problem} {size bound : prob.Inst → ℕ}
    {dom dom' : prob.Inst → Prop} {T X : prob.Inst → ℝ} (hR : RealizedWithin prob size bound dom T)
    (κ : ℕ) {C : ℝ} (hdom : ∀ x, dom' x → dom x ∧ 1 ≤ size x ∧ bound x = size x ^ κ)
    (hT : ∀ x, dom' x → T x ≤ C * X x) (hX : ∀ x, dom' x → 1 ≤ X x) :
    ∃ (P : List Instr) (b : ℕ) (K : ℝ), 0 ≤ K ∧ Solves prob P b dom' fun x => K * X x := by
  obtain ⟨P, b, c, hc, hS⟩ := hR κ
  exact ⟨P, b, c * |C| + c, by positivity,
    hS.mono le_rfl hdom fun x hx => mul_add_le_of_le_mul hc (hT x hx) (hX x hx)⟩

/-- `exists_solves_nonneg` without the sign of the constant: the form of the items with one program.
-/
theorem exists_solves {prob : Problem} {size bound : prob.Inst → ℕ} {dom dom' : prob.Inst → Prop}
    {T X : prob.Inst → ℝ} (hR : RealizedWithin prob size bound dom T) (κ : ℕ) {C : ℝ}
    (hdom : ∀ x, dom' x → dom x ∧ 1 ≤ size x ∧ bound x = size x ^ κ)
    (hT : ∀ x, dom' x → T x ≤ C * X x) (hX : ∀ x, dom' x → 1 ≤ X x) :
    ∃ (P : List Instr) (b : ℕ) (K : ℝ), Solves prob P b dom' fun x => K * X x := by
  obtain ⟨P, b, K, -, hS⟩ := exists_solves_nonneg hR κ hdom hT hX
  exact ⟨P, b, K, hS⟩

/-- Two programs, each with its slope and its constant, have one slope and one constant in common.
-/
theorem exists_solves_pair {prob₁ prob₂ : Problem} {dom₁ : prob₁.Inst → Prop}
    {dom₂ : prob₂.Inst → Prop} {X₁ : prob₁.Inst → ℝ} {X₂ : prob₂.Inst → ℝ}
    (h₁ : ∃ (P : List Instr) (b : ℕ) (K : ℝ), 0 ≤ K ∧ Solves prob₁ P b dom₁ fun x => K * X₁ x)
    (h₂ : ∃ (P : List Instr) (b : ℕ) (K : ℝ), 0 ≤ K ∧ Solves prob₂ P b dom₂ fun x => K * X₂ x)
    (hX₁ : ∀ x, dom₁ x → 1 ≤ X₁ x) (hX₂ : ∀ x, dom₂ x → 1 ≤ X₂ x) :
    ∃ (P₁ P₂ : List Instr) (b : ℕ) (K : ℝ),
      Solves prob₁ P₁ b dom₁ (fun x => K * X₁ x) ∧ Solves prob₂ P₂ b dom₂ (fun x => K * X₂ x) := by
  obtain ⟨P₁, b₁, K₁, hK₁, hS₁⟩ := h₁
  obtain ⟨P₂, b₂, K₂, hK₂, hS₂⟩ := h₂
  refine ⟨P₁, P₂, max b₁ b₂, K₁ + K₂, hS₁.mono (le_max_left _ _) (fun _ hx => hx) fun x hx => ?_,
    hS₂.mono (le_max_right _ _) (fun _ hx => hx) fun x hx => ?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans (hX₁ x hx))
  · exact mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans (hX₂ x hx))

/-! ## Bounds in one size, for all large sizes -/

/-- From a realized running time with a bound for all large sizes to a program with that bound. -/
theorem solvedAt_of_realized {Q : EndStatement.Problem} (T : ℕ → ℝ → ℝ) (κ : ℕ)
    (hR : Realized Q T) {C a : ℝ} {e : ℕ}
    (hev : ∀ᶠ n : ℕ in Filter.atTop,
      T n ((n : ℝ) ^ ((κ : ℕ) : ℝ)) ≤ C * ((n : ℝ) ^ a * Real.log n ^ e)) :
    SolvedInTimeAt Q κ a e := by
  obtain ⟨P, b, c, hc, hS⟩ := hR κ
  have hg : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ a * Real.log n ^ e := fun n =>
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Real.log_natCast_nonneg _) _)
  -- a bound for all large `n` gives a bound for all `n`
  obtain ⟨C', hC', hb⟩ := Dominated.of_eventually_add_one hev hg
  refine solvedInTimeAt_iff.2 ⟨P, b, c * C' + c, hS.mono le_rfl (fun x hx => hx) fun x hx => ?_⟩
  have hU : ((x.U : ℕ) : ℝ) = (x.n : ℝ) ^ ((κ : ℕ) : ℝ) := by
    rw [hx]
    exact cast_pow_eq _ _
  change c * max (T x.n ((x.U : ℕ) : ℝ)) 0 + c ≤ _
  rw [hU]
  -- `c max(T, 0) + c ≤ c C' (X + 1) + c ≤ (c C' + c) (X + 1)`, where `X = n^a (log n)^e ≥ 0`
  have hcT : c * max (T x.n ((x.n : ℝ) ^ ((κ : ℕ) : ℝ))) 0 ≤
      c * (C' * ((x.n : ℝ) ^ a * Real.log x.n ^ e + 1)) :=
    mul_le_mul_of_nonneg_left (max_le (hb x.n trivial) (mul_nonneg hC' (by linarith [hg x.n]))) hc
  linarith [mul_nonneg hc (hg x.n)]

/-- A claim "solved in `O(n^a)` time on numbers of absolute value at most `n^κ`, for every `κ`", in
a reading `S` of "is solved in time T" that is realized, gives programs. -/
theorem solvedInTime_of_claim {S : (ℕ → ℝ → ℝ) → Prop} {Q : EndStatement.Problem}
    (hR : ∀ T, S T → Realized Q T) {a : ℝ} (h : Claim.SolvedAlongPow S UpperBigOPow a) :
    SolvedInTime Q a 0 := by
  intro κ
  obtain ⟨T, hT, C, hb⟩ := h κ (Nat.cast_nonneg κ)
  exact solvedAt_of_realized T κ (hR T hT) (C := C)
    (by simpa only [pow_zero, mul_one] using hb)

/-- A claim "solved in `O(n^a (log n)^{O(1)})` time on numbers of absolute value at most `n^κ`, for
every `κ`", in a reading `S` of "is solved in time T" that is realized, gives programs. -/
theorem solvedInPolylogTime_of_claim {S : (ℕ → ℝ → ℝ) → Prop} {Q : EndStatement.Problem}
    (hR : ∀ T, S T → Realized Q T) {a : ℝ} (h : Claim.SolvedAlongPow S UpperPowPolylog a) :
    SolvedInPolylogTime Q a := by
  intro κ
  obtain ⟨T, hT, C, e, hb⟩ := h κ (Nat.cast_nonneg κ)
  exact ⟨e, solvedAt_of_realized T κ (hR T hT) hb⟩

/-- The bound `U` is not in the memory: a program for numbers within `n^κ'` serves numbers within
`n^κ`, for `κ ≤ κ'`.  (At size 0, where `0^0 > 0^1`, the input is empty.) -/
theorem solvedInTimeAt_mono {Q : EndStatement.Problem} (hempty : ∀ x : Q.Instance 0, Q.input x = [])
    {κ κ' : ℕ} (hκ : κ ≤ κ') {a : ℝ} {e : ℕ} (h : SolvedInTimeAt Q κ' a e) :
    SolvedInTimeAt Q κ a e := by
  obtain ⟨P, b, C, hS⟩ := h
  refine ⟨P, b, C, fun n x hx W hW => hS n x (fun a ha => ?_) W hW⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [hempty x] at ha
    cases ha
  · exact (hx a ha).trans (Nat.pow_le_pow_right hn hκ)

/-- Some claims of the paper are about `κ ≥ 1`; the items are about all `κ`. -/
theorem solvedInTime_of_one_le {Q : EndStatement.Problem}
    (hempty : ∀ x : Q.Instance 0, Q.input x = []) {a : ℝ} {e : ℕ}
    (h : ∀ κ : ℕ, 1 ≤ κ → SolvedInTimeAt Q κ a e) : SolvedInTime Q a e := by
  intro κ
  rcases Nat.eq_zero_or_pos κ with rfl | hκ
  · exact solvedInTimeAt_mono hempty (Nat.zero_le 1) (h 1 le_rfl)
  · exact h κ hκ

end ThreeSumApsp.FromClaims
