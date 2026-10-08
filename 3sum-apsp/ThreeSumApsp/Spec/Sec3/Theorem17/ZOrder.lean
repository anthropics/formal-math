/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.List
public import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Matrices in Z-order (Morton order)

The count of the proof of Theorem 17 needs a product of matrices over `ℤ[x]/(x^p - 1)`, "O(n^{log₂
7}) with Strassen's algorithm".  For the recursion of that algorithm a `2^K × 2^K` matrix is stored
in Z-order: the entry `(a, c)` stands at the place whose digits in base 4 are `2 a_i + c_i`, where
`a_i` and `c_i` are the binary digits of `a` and `c`.

* Places: `zIdx` maps a pair to its place, `zRow` and `zCol` map back (`zRow_zIdx`, `zCol_zIdx`,
  `zIdx_zRow_zCol`).  All three are computed one digit in base 4 at a time (`zIdx_eq`, `zRow_eq`,
  `zCol_eq`), and every proof is an induction along these equations.
* Lists: the entry `(a, c)` of `zList K M` starts at `zIdx a c * p` (`getD_zList`).
* **The four quadrants of a matrix are the four quarters of its list** (`quarter_zList`,
  `zList_succ`), which is what the recursion needs.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Places -/

/-- The binary digits of `i`, moved to the even places: the number with the same digits in
base 4. -/
def spread (i : ℕ) : ℕ := Nat.ofDigits 4 (Nat.digits 2 i)

/-- The table of `spread`. -/
def spreadList (N2 : ℕ) : List ℤ := (List.range N2).map fun i : ℕ => ((spread i : ℕ) : ℤ)

/-- The place of the entry `(a, c)` in Z-order. -/
def zIdx (a c : ℕ) : ℕ := 2 * spread a + spread c

/-- The row of the entry at place `z`. -/
def zRow (z : ℕ) : ℕ := Nat.ofDigits 2 ((Nat.digits 4 z).map (· / 2))

/-- The column of the entry at place `z`. -/
def zCol (z : ℕ) : ℕ := Nat.ofDigits 2 ((Nat.digits 4 z).map (· % 2))

/-- The last binary digit goes to the last digit in base 4. -/
theorem spread_eq (i : ℕ) : spread i = i % 2 + 4 * spread (i / 2) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [spread]
  · unfold spread
    rw [Nat.digits_eq_cons_digits_div (by norm_num) hi.ne', Nat.ofDigits_cons]

/-- The number 0 has no digits to move. -/
theorem spread_zero : spread 0 = 0 := by simp [spread]

/-- The row, one digit in base 4 at a time. -/
theorem zRow_eq (z : ℕ) : zRow z = z % 4 / 2 + 2 * zRow (z / 4) := by
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · simp [zRow]
  · unfold zRow
    rw [Nat.digits_eq_cons_digits_div (by norm_num) hz.ne', List.map_cons, Nat.ofDigits_cons]

/-- The column, one digit in base 4 at a time. -/
theorem zCol_eq (z : ℕ) : zCol z = z % 4 % 2 + 2 * zCol (z / 4) := by
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · simp [zCol]
  · unfold zCol
    rw [Nat.digits_eq_cons_digits_div (by norm_num) hz.ne', List.map_cons, Nat.ofDigits_cons]

/-- The place 0 is in row 0. -/
theorem zRow_zero : zRow 0 = 0 := by simp [zRow]

/-- The place 0 is in column 0. -/
theorem zCol_zero : zCol 0 = 0 := by simp [zCol]

/-- The place, one digit in base 4 at a time. -/
theorem zIdx_eq (a c : ℕ) : zIdx a c = (2 * (a % 2) + c % 2) + 4 * zIdx (a / 2) (c / 2) := by
  unfold zIdx
  rw [spread_eq a, spread_eq c]
  ring

/-- The places of a `2^K × 2^K` matrix are below `4^K`. -/
theorem zIdx_lt {K a c : ℕ} (ha : a < 2 ^ K) (hc : c < 2 ^ K) : zIdx a c < 4 ^ K := by
  induction K generalizing a c with
  | zero =>
    obtain rfl : a = 0 := by simpa using ha
    obtain rfl : c = 0 := by simpa using hc
    simp [zIdx, spread_zero]
  | succ K ih =>
    rw [pow_succ] at ha hc
    have h := ih (a := a / 2) (c := c / 2) (by omega) (by omega)
    rw [zIdx_eq, pow_succ]
    omega

/-- The row and the column of the place of `(a, c)` are `a` and `c`. -/
private theorem zRow_zCol_zIdx (a c : ℕ) : zRow (zIdx a c) = a ∧ zCol (zIdx a c) = c := by
  induction hm : a + c using Nat.strong_induction_on generalizing a c with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos (a + c) with h0 | hpos
    · obtain ⟨rfl, rfl⟩ : a = 0 ∧ c = 0 := by omega
      simp [zIdx, spread_zero, zRow_zero, zCol_zero]
    · obtain ⟨hrow, hcol⟩ := ih (a / 2 + c / 2) (by omega) (a / 2) (c / 2) rfl
      rw [zRow_eq, zCol_eq, zIdx_eq]
      generalize zIdx (a / 2) (c / 2) = z at hrow hcol
      rw [show (2 * (a % 2) + c % 2 + 4 * z) / 4 = z by omega, hrow, hcol]
      omega

/-- The row of the place of `(a, c)` is `a`. -/
theorem zRow_zIdx (a c : ℕ) : zRow (zIdx a c) = a := (zRow_zCol_zIdx a c).1

/-- The column of the place of `(a, c)` is `c`. -/
theorem zCol_zIdx (a c : ℕ) : zCol (zIdx a c) = c := (zRow_zCol_zIdx a c).2

/-- A place is the place of its row and its column. -/
theorem zIdx_zRow_zCol (z : ℕ) : zIdx (zRow z) (zCol z) = z := by
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    rcases Nat.eq_zero_or_pos z with rfl | hz
    · simp [zRow_zero, zCol_zero, zIdx, spread_zero]
    · have h := ih (z / 4) (by omega)
      rw [zIdx_eq, zRow_eq z, zCol_eq z]
      generalize zRow (z / 4) = a at h
      generalize zCol (z / 4) = c at h
      rw [show (z % 4 / 2 + 2 * a) / 2 = a by omega, show (z % 4 % 2 + 2 * c) / 2 = c by omega, h]
      omega

/-- The places of the quadrant number `t`: their rows and columns are those of the first quadrant,
moved by `2^K` down if `t ≥ 2` and to the right if `t` is odd. -/
theorem zRow_zCol_quadrant {K t z : ℕ} (ht : t < 4) (hz : z < 4 ^ K) :
    zRow (t * 4 ^ K + z) = zRow z + t / 2 * 2 ^ K ∧
      zCol (t * 4 ^ K + z) = zCol z + t % 2 * 2 ^ K := by
  induction K generalizing z with
  | zero =>
    obtain rfl : z = 0 := by simpa using hz
    rw [zRow_eq, zCol_eq, pow_zero, pow_zero, Nat.mul_one, Nat.add_zero, Nat.mod_eq_of_lt ht,
      Nat.div_eq_of_lt ht, zRow_zero, zCol_zero]
    omega
  | succ K ih =>
    obtain ⟨hrow, hcol⟩ := ih (z := z / 4) (by rw [pow_succ] at hz; omega)
    have hpow : t * 4 ^ (K + 1) = 4 * (t * 4 ^ K) := by rw [pow_succ]; ring
    rw [zRow_eq, zCol_eq, zRow_eq z, zCol_eq z, hpow,
      show (4 * (t * 4 ^ K) + z) % 4 = z % 4 by omega,
      show (4 * (t * 4 ^ K) + z) / 4 = t * 4 ^ K + z / 4 by omega, hrow, hcol, pow_succ 2]
    constructor <;> ring

/-! ## Matrices as lists -/

/-- A `2^K × 2^K` matrix of vectors, as one list, entry after entry in Z-order. -/
def zList (K : ℕ) (M : ℕ → ℕ → List ℤ) : List ℤ :=
  (List.range (4 ^ K)).flatMap fun z => M (zRow z) (zCol z)

/-- The quarter number `t` of a list of length `4 q`. -/
def quarter (q t : ℕ) (l : List ℤ) : List ℤ := (l.drop (t * q)).take q

/-- A matrix of vectors of length `p` has `4^K p` numbers. -/
theorem length_zList {p : ℕ} (K : ℕ) (M : ℕ → ℕ → List ℤ) (hM : ∀ a c, (M a c).length = p) :
    (zList K M).length = 4 ^ K * p :=
  List.length_flatMap_range _ _ fun _ _ => hM _ _

/-- The entry `(a, c)` of the matrix stands at the place `zIdx a c`. -/
theorem getD_zList {p K a c r : ℕ} (M : ℕ → ℕ → List ℤ) (hM : ∀ a c, (M a c).length = p)
    (ha : a < 2 ^ K) (hc : c < 2 ^ K) (hr : r < p) :
    (zList K M).getD (zIdx a c * p + r) 0 = (M a c).getD r 0 := by
  rw [zList, List.getD_flatMap_range _ (fun _ _ => hM _ _) (zIdx_lt ha hc) hr, zRow_zIdx, zCol_zIdx]

/-- **The quadrants of a matrix are the quarters of its list.** -/
theorem quarter_zList {p K t : ℕ} (M : ℕ → ℕ → List ℤ) (hM : ∀ a c, (M a c).length = p)
    (ht : t < 4) :
    quarter (4 ^ K * p) t (zList (K + 1) M) =
      zList K fun a c => M (a + t / 2 * 2 ^ K) (c + t % 2 * 2 ^ K) := by
  have hsplit : 4 ^ (K + 1) = t * 4 ^ K + 4 ^ K + (3 - t) * 4 ^ K := by
    calc 4 ^ (K + 1) = (t + 1 + (3 - t)) * 4 ^ K := by
          rw [show t + 1 + (3 - t) = 4 by omega, pow_succ, Nat.mul_comm]
      _ = _ := by ring
  rw [quarter, zList, hsplit, ← Nat.mul_assoc,
    List.take_drop_flatMap_range _ _ _ _ fun _ _ => hM _ _,
    zList]
  refine List.flatMap_congr fun z hz => ?_
  obtain ⟨hrow, hcol⟩ := zRow_zCol_quadrant ht (List.mem_range.1 hz)
  rw [hrow, hcol]

/-- A list of length `4 q` is put together from its four quarters. -/
private theorem eq_append_quarters {q : ℕ} {l : List ℤ} (hl : l.length = 4 * q) :
    l = quarter q 0 l ++ quarter q 1 l ++ quarter q 2 l ++ quarter q 3 l := by
  unfold quarter
  refine List.ext_getElem (by simp; omega) fun i _ _ => ?_
  simp only [List.getElem_append, List.length_append, List.length_take, List.length_drop,
    List.getElem_take, List.getElem_drop]
  split_ifs <;> congr 1 <;> omega

/-- A matrix is put together from its four quadrants. -/
theorem zList_succ {p K : ℕ} (M : ℕ → ℕ → List ℤ) (hM : ∀ a c, (M a c).length = p) :
    zList (K + 1) M = zList K (fun a c => M a c) ++ zList K (fun a c => M a (c + 2 ^ K)) ++
      zList K (fun a c => M (a + 2 ^ K) c) ++ zList K fun a c => M (a + 2 ^ K) (c + 2 ^ K) := by
  have hlen : (zList (K + 1) M).length = 4 * (4 ^ K * p) := by
    rw [length_zList _ _ hM, pow_succ]
    ring
  conv_lhs => rw [eq_append_quarters hlen]
  rw [quarter_zList M hM (by norm_num), quarter_zList M hM (by norm_num),
    quarter_zList M hM (by norm_num), quarter_zList M hM (by norm_num)]
  simp only [Nat.reduceDiv, Nat.reduceMod, Nat.zero_mul, Nat.one_mul, Nat.add_zero]

end ThreeSumApsp.Spec
