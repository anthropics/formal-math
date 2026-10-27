/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.SecCrossing_PolyDefs
import Eight.SecCrossing_Blocks
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Lemma 2(a): «multiplying them out one at a time»: what the program computes, and how large its lists are

The proof of Lemma 2(a) in Section 4 says: «The t factors are polynomials in T of degree at most 1
with coefficients in {−1, 0, 1}, so multiplying them out one at a time takes time poly(λ), and |A_i|
≤ C(t, i) ≤ 2^t.»
The program is in proof/networks/Eight/SecCrossing_PolyDefs.lean. A polynomial in T is kept as the
list of its coefficients, lowest first. mulStep r c l is the list of (r + T·c)·(polynomial of l);
mulUpTo q n is the list after the first n
factors, starting from the list [1]; mulOut q is the list after all t factors; aMul (i, q) is its
entry number i.

What is proved here:
* getD_mulUpTo: the entry number i after n factors is the coefficient of T^i in the product of the
  first n factors; mulOut_eq_A, stAMul: on four strings of λ bits the entry number i of mulOut is
  A_i.
* length_mulUpTo, abs_getD_mulUpTo_le_choose, abs_getD_mulUpTo_le: after n factors the list has n +
  1 entries, the entry number j is at most C(n, j) ≤ 2^n in absolute value. So every list that
  occurs is short (len_mulUpTo_le), and the values of the program are at most 2^t in absolute value
  (abs_aMul_le).
Small auxiliary statements are in the namespace Eight.MulOut. -/

public section

namespace Eight

open Groundwork PaddedDescent.F Finset Polynomial

/-! ### Lists and strings -/

/-- A position of the list of a string holds the bit of the string, and 0 beyond the end («Append 3t
− λ zeros to each of x, y, u, v»). -/
theorem MulOut.getD_ofFn {lam : ℕ} (x : Pieces.Bits lam) (j : ℕ) : (List.ofFn x).getD j false = bitAt x j := by
  unfold bitAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> rfl

/-- The block number s of the list of a string is the block number s of the string. -/
theorem MulOut.blkL_ofFn {lam : ℕ} (x : Pieces.Bits lam) (s : ℕ) : blkL (List.ofFn x) s = blockAt x s := by
  simp only [blkL, blkAt, blockAt, MulOut.getD_ofFn]

/-! ### One multiplication -/

/-- One multiplication makes the list longer by one entry. -/
theorem length_mulStep (r c : ℤ) (l : List ℤ) : (mulStep r c l).length = l.length + 1 := by
  simp [mulStep]

/-- The entry number j after one multiplication is r·l_j + c·l_{j−1}, also beyond the end of the
list, where all three entries count as 0. -/
theorem getD_mulStep (r c : ℤ) (l : List ℤ) (j : ℕ) : (mulStep r c l).getD j 0 = r * l.getD j 0 + c * (0 :: l).getD j 0 := by
  unfold mulStep
  by_cases h : j < l.length + 1
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using h), List.getD_eq_default l _ (by omega), List.getD_eq_default (0 :: l) _ (by simpa using h)]
    simp

/-- The factor number n is multiplied in after the factors number 0, …, n − 1. -/
theorem mulUpTo_succ (q : FourL) (n : ℕ) : mulUpTo q (n + 1) = mulStep (rAt q n) (cAt q n) (mulUpTo q n) := by
  simp [mulUpTo, List.range_succ]

/-! ### The lists hold the coefficients of the products -/

/-- After n factors the entry number i is the coefficient of T^i in the product of the first n
factors. -/
theorem getD_mulUpTo (q : FourL) (n i : ℕ) : (mulUpTo q n).getD i 0 = (∏ s ∈ range n, (C (rAt q s) + X * C (cAt q s))).coeff i := by
  induction n generalizing i with
  | zero =>
    cases i with
    | zero => simp [mulUpTo]
    | succ i => simp [mulUpTo, Polynomial.coeff_one]
  | succ n ih =>
    rw [mulUpTo_succ, getD_mulStep, Finset.prod_range_succ, mul_add, Polynomial.coeff_add, Polynomial.coeff_mul_C, ← mul_assoc, Polynomial.coeff_mul_C, ih]
    cases i with
    | zero => simp [mul_comm]
    | succ i =>
      rw [Polynomial.coeff_mul_X, List.getD_cons_succ, ih]
      ring

/-- On four strings of λ bits, written as lists, the entry number i of mulOut is A_i, for every λ
and every i (for i > t both are 0). Same as in the paper: A_i is the coefficient of T^i in the
product of the t factors. -/
theorem mulOut_eq_A (lam i : ℕ) (x y u v : Pieces.Bits lam) : (mulOut (List.ofFn x, List.ofFn y, List.ofFn u, List.ofFn v)).getD i 0 = A lam i x y u v := by
  have ht : tL (List.ofFn x, List.ofFn y, List.ofFn u, List.ofFn v) = tOf lam := by simp [tL]
  unfold mulOut A prodRC
  rw [getD_mulUpTo, ht]
  simp only [rAt, cAt, MulOut.blkL_ofFn]

/-- The program aMul computes A_i, for every λ and every i. -/
theorem stAMul : StAMul := mulOut_eq_A

/-! ### The lists stay short -/

/-- After n factors the list has n + 1 entries. -/
theorem length_mulUpTo (q : FourL) (n : ℕ) : (mulUpTo q n).length = n + 1 := by
  induction n with
  | zero => simp [mulUpTo]
  | succ n ih => rw [mulUpTo_succ, length_mulStep, ih]

/-- «coefficients in {−1, 0, 1}»: |R| ≤ 1 at every block. -/
theorem MulOut.abs_rAt_le (q : FourL) (s : ℕ) : |rAt q s| ≤ 1 := abs_Rb_le _ _ _ _

/-- «coefficients in {−1, 0, 1}»: |C| ≤ 1 at every block. -/
theorem MulOut.abs_cAt_le (q : FourL) (s : ℕ) : |cAt q s| ≤ 1 := abs_Cb_le _ _ _ _

/-- After n factors the entry number j is at most C(n, j) in absolute value, by Pascal's rule. At n =
t this is the paper's «|A_i| ≤ C(t, i)». -/
theorem abs_getD_mulUpTo_le_choose (q : FourL) (n j : ℕ) : |(mulUpTo q n).getD j 0| ≤ (n.choose j : ℤ) := by
  induction n generalizing j with
  | zero =>
    cases j with
    | zero => simp [mulUpTo]
    | succ j => simp [mulUpTo]
  | succ n ih =>
    rw [mulUpTo_succ, getD_mulStep]
    have h1 : ∀ a b : ℤ, |a| ≤ 1 → |a * b| ≤ |b| := fun a b ha => by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg b) ha
    refine (abs_add_le _ _).trans ?_
    have hr := h1 _ ((mulUpTo q n).getD j 0) (MulOut.abs_rAt_le q n)
    have hc := h1 _ ((0 :: mulUpTo q n).getD j 0) (MulOut.abs_cAt_le q n)
    cases j with
    | zero =>
      have := ih 0
      simp only [List.getD_cons_zero, abs_zero, Nat.choose_zero_right, Nat.cast_one] at *
      linarith
    | succ j =>
      have e1 := ih (j + 1)
      have e2 := ih j
      rw [List.getD_cons_succ] at hc ⊢
      rw [Nat.choose_succ_succ]
      push_cast
      linarith

/-- After n factors every entry is at most 2^n in absolute value. -/
theorem abs_getD_mulUpTo_le (q : FourL) (n j : ℕ) : |(mulUpTo q n).getD j 0| ≤ 2 ^ n :=
  (abs_getD_mulUpTo_le_choose q n j).trans (by exact_mod_cast Nat.choose_le_two_pow n j)

/-- The paper's «|A_i| ≤ 2^t», read off the program, for all inputs. -/
theorem abs_aMul_le (p : ℕ × FourL) : |aMul p| ≤ 2 ^ tL p.2 := abs_getD_mulUpTo_le _ _ _

/-- The word of a list of k integers whose words have length at most b has length at most k·(b + 2) + 2. -/
theorem MulOut.len_listZ_le (b : ℕ) : ∀ l : List ℤ, (∀ z ∈ l, len z ≤ b) → len l ≤ l.length * (b + 2) + 2
  | [], _ => by simp [len_nil]
  | z :: l, h => by
    have h1 := MulOut.len_listZ_le b l fun w hw => h w (List.mem_cons_of_mem _ hw)
    have h2 := h z List.mem_cons_self
    rw [len_cons, List.length_cons, Nat.succ_mul]
    omega

/-- The word of an integer of absolute value at most 2^n has length at most 3n + 8. -/
theorem MulOut.len_int_le {z : ℤ} {n : ℕ} (h : |z| ≤ 2 ^ n) : len z ≤ 3 * n + 8 := by
  have h1 : z.natAbs < 2 ^ (n + 1) := by
    have : (z.natAbs : ℤ) ≤ 2 ^ n := by rwa [Int.natCast_natAbs]
    have h2 : z.natAbs ≤ 2 ^ n := by exact_mod_cast this
    rw [pow_succ]
    have := Nat.two_pow_pos n
    omega
  have h2 := Nat.size_le.2 h1
  rw [len_int]
  omega

/-- The word of the list after n factors has length at most (n + 1)(3n + 10) + 2: the list has n + 1
entries, and each is an integer of at most n + 1 binary digits whose word has at most 3n + 8 bits. -/
theorem len_mulUpTo_le (q : FourL) (n : ℕ) : len (mulUpTo q n) ≤ (n + 1) * (3 * n + 10) + 2 := by
  have h := MulOut.len_listZ_le (3 * n + 8) (mulUpTo q n) fun z hz => by
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hz
    rw [← List.getD_eq_getElem _ 0 hj]
    exact MulOut.len_int_le (abs_getD_mulUpTo_le q n j)
  rwa [length_mulUpTo] at h

/-- The number of blocks is at most the length of the word of the four strings. -/
theorem MulOut.tL_le_len (q : FourL) : tL q ≤ len q := by
  have h1 : tL q ≤ q.1.length := by unfold tL tOf; omega
  have h2 := length_le_len q.1
  have h3 : len q = len q.1 + len q.2 + 2 := len_pair q.1 q.2
  omega

end Eight
