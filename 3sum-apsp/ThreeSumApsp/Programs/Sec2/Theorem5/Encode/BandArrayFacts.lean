/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

/-!
# The input array of a band: what the loops compute

The input array of a band (Sections 2.3.3 and 2.3.4) holds entries of the matrix at the codes of
certain strings and 0 elsewhere.  The table of subsets lists subsets of size m of the L levels:
`Spec.unrank L m s` is the mask of subset number s, and the block product (g, h) of a tile uses
subset number g K₀ + h.  No program text occurs here.  `BandArgs` collects the arguments of
bandArray: the number of a row, the address of a mask and the code of a string are functions of
them.

* The code of a left or right string is computed level by level: `codeUpTo` is the code of the first
  l levels.  One more level appends the next outer digit, or 3 plus the next inner digit
  (`codeUpTo_succ`), and after all levels the code is `Spec.gluedCode` (`codeUpTo_unrank`).
* The numbers that occur are small (`BandArgs.rowNo_lt`, `subsetIndex_lt`, `BandArgs.code_lt`).
* The array is filled in the order of the tuples (g, h, r, k), not of the codes.  `OverwrittenWith`
  says of two memories that cells of the array were overwritten only with the entries of the target
  list, so that a cell that is right stays right.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec2

/-! ## The code of a string, level by level -/

section code
variable {bs : List Bool} {o i : List ℕ} {l : ℕ}

/-- The code of the first l levels: Horner's rule in base 7 on the outer digits o and 3 plus the
inner digits i, interleaved along the mask bs. -/
def codeUpTo (bs : List Bool) (o i : List ℕ) (l : ℕ) : ℕ :=
  ThreeSumApsp.ofDigitList 7 ((Spec.gluedDigits bs o i).take l)

/-- One more level. -/
theorem codeUpTo_succ (hl : l < bs.length) :
    codeUpTo bs o i (l + 1) = codeUpTo bs o i l * 7 +
      if bs.getD l false then (i.map (3 + ·)).getD ((bs.take l).count true) 0
      else o.getD ((bs.take l).count false) 0 := by
  rw [codeUpTo, ThreeSumApsp.ofDigitList_take_succ 7 _ (by rwa [Spec.length_gluedDigits]),
    Spec.gluedDigits, ThreeSumApsp.getD_weaveList, if_pos hl]
  rfl

/-- The code of l levels is below 7^l. -/
theorem codeUpTo_lt (ho : ∀ x ∈ o, x < 3) (hi : ∀ x ∈ i, x < 4) (hl : l ≤ bs.length) :
    codeUpTo bs o i l < 7 ^ l := by
  have hlt := ThreeSumApsp.ofDigitList_lt ((Spec.gluedDigits bs o i).take l) fun d hd =>
    Spec.lt_of_mem_gluedDigits ho hi d (List.mem_of_mem_take hd)
  rwa [List.length_take, Spec.length_gluedDigits, Nat.min_eq_left hl] at hlt

end code

/-- On the mask of a subset of the table and the digits of a row and a column, the code of all
levels is `Spec.gluedCode`. -/
theorem codeUpTo_unrank (L m s r k : ℕ) :
    codeUpTo (Spec.unrank L m s) (ThreeSumApsp.digitList 3 (L - m) r) (ThreeSumApsp.digitList 4 m k)
        L
      = Spec.gluedCode L m (Spec.unrank L m s) r k := by
  rw [codeUpTo, List.take_of_length_le (by simp [Spec.length_unrank]), Spec.gluedCode]

/-! ## Sizes -/

/-- A band has at most 7^L rows. -/
private theorem bandSize_le (L m : ℕ) : bandSize L m ≤ 7 ^ L := by
  have hK0 : ThreeSumApsp.K0 L m ≤ 2 ^ L := (Nat.sqrt_le_self _).trans (Nat.choose_le_two_pow _ _)
  have hN0 : ThreeSumApsp.N0 L m ≤ 3 ^ L := Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
  calc bandSize L m ≤ 2 ^ L * 3 ^ L := Nat.mul_le_mul hK0 hN0
    _ = 6 ^ L := by rw [← Nat.mul_pow]
    _ ≤ 7 ^ L := Nat.pow_le_pow_left (by omega) _

/-- The arguments of bandArray. -/
structure BandArgs where
  /-- The parameters L, m, N. -/
  p : Par
  /-- The number of the band. -/
  β : ℕ
  /-- 0 for a row band of X, 1 for a column band of Y. -/
  side : ℕ
  /-- The address of the matrix. -/
  aA : ℕ
  /-- The step from a row (of X, or column of Y) to the next. -/
  sI : ℕ
  /-- The step from a column of X (or row of Y) to the next. -/
  sK : ℕ
  /-- The address of the table of subsets. -/
  mask : ℕ
  /-- The address of the table of digits in base 3. -/
  dig3 : ℕ
  /-- The address of the table of digits in base 4. -/
  dig4 : ℕ
  /-- The address of the array. -/
  arr : ℕ

namespace BandArgs
variable (A : BandArgs)

/-- The number of the block of rows of the matrix `X` (`side = 0`), or of columns of the matrix `Y`
(any other side), for the block product `(g, h)`. -/
def blockNo (g h : ℕ) : ℕ := A.β * A.p.K0 + if A.side = 0 then g else h

/-- The number of the row of `X` (or column of `Y`) for the block product `(g, h)` and the row `r`
of the block. -/
def rowNo (g h r : ℕ) : ℕ := A.blockNo g h * A.p.N0 + r

/-- The address of the mask of the subset of the block product `(g, h)`. -/
def maskRow (g h : ℕ) : ℕ := A.mask + (g * A.p.K0 + h) * A.p.L

/-- The code of the string for the block product `(g, h)`, the row `r` and the column `k`. -/
def code (g h r k : ℕ) : ℕ :=
  Spec.gluedCode A.p.L A.p.m (Spec.unrank A.p.L A.p.m (g * A.p.K0 + h)) r k

/-- A code is below `7^L`. -/
theorem code_lt (g h r k : ℕ) : A.code g h r k < A.p.S7 :=
  Spec.gluedCode_lt A.p.m (Spec.length_unrank ..) r k

variable {A}

/-- The numbers of the rows, and of the blocks, of the padded matrix stay small. -/
theorem rowNo_lt {g h r : ℕ} (hβ : A.β < A.p.nB) (hg : g < A.p.K0) (hh : h < A.p.K0)
    (hr : r < A.p.N0) :
    A.rowNo g h r < A.p.N + A.p.S7 ∧ A.blockNo g h * A.p.N0 < A.p.N + A.p.S7 ∧
      A.blockNo g h < A.p.N + A.p.S7 ∧ A.β * A.p.K0 < A.p.N + A.p.S7 := by
  -- row < nB K₀ N₀ ≤ N + K₀ N₀ - 1 < N + 7^L, and the other three numbers are at most the row.
  have hposition : (if A.side = 0 then g else h) < A.p.K0 := by split <;> assumption
  have hblock : A.β * A.p.K0 + A.p.K0 ≤ A.p.nB * A.p.K0 := Nat.mul_add_le_mul hβ le_rfl
  have hrow : A.blockNo g h * A.p.N0 + A.p.N0 ≤ A.p.nB * A.p.K0 * A.p.N0 :=
    Nat.mul_add_le_mul (show A.blockNo g h < A.p.nB * A.p.K0 by unfold blockNo; omega) le_rfl
  have hbands : A.p.nB * A.p.K0 * A.p.N0 = numBands A.p.L A.p.m A.p.N * bandSize A.p.L A.p.m := by
    rw [Nat.mul_assoc]
    rfl
  have hpad : numBands A.p.L A.p.m A.p.N * bandSize A.p.L A.p.m
      ≤ A.p.N + bandSize A.p.L A.p.m - 1 := Nat.div_mul_le_self _ _
  have hsize := bandSize_le A.p.L A.p.m
  have hsize_pos : 0 < bandSize A.p.L A.p.m :=
    Nat.mul_pos (by change 0 < A.p.K0; omega) (N0_pos _ _)
  have hle : A.blockNo g h ≤ A.blockNo g h * A.p.N0 := Nat.le_mul_of_pos_right _ (by omega)
  have hS7 : A.p.S7 = 7 ^ A.p.L := rfl
  have hfirst : A.β * A.p.K0 ≤ A.blockNo g h := Nat.le_add_right ..
  unfold rowNo
  omega

/-- The offset of a row in its block. -/
theorem rowNo_mod (g h : ℕ) {r : ℕ} (hr : r < A.p.N0) : A.rowNo g h r % A.p.N0 = r := by
  unfold rowNo
  rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hr]

end BandArgs

/-- g K₀ + h is the number of a subset of the table. -/
theorem subsetIndex_lt (p : Par) {g h : ℕ} (hg : g < p.K0) (hh : h < p.K0) :
    g * p.K0 + h < p.KK ∧ g * p.K0 + h < p.L.choose p.m :=
  ⟨Nat.mul_add_lt_mul hg hh, Spec.tableIndex_lt p.L p.m (⟨g, hg⟩, ⟨h, hh⟩)⟩

/-- `binom(L, m)`, `K₀`, `N₀` and `L` are at most `7^L`. -/
theorem Par.sizes_le_S7 (p : Par) :
    p.L.choose p.m ≤ p.S7 ∧ p.K0 ≤ p.S7 ∧ p.N0 ≤ p.S7 ∧ p.L < p.S7 := by
  have hchoose : p.L.choose p.m ≤ 2 ^ p.L := Nat.choose_le_two_pow _ _
  have hpow : 2 ^ p.L ≤ 7 ^ p.L := Nat.pow_le_pow_left (by omega) _
  have hK0 : p.K0 ≤ p.L.choose p.m := Nat.sqrt_le_self _
  have hN0 : p.N0 ≤ 7 ^ p.L :=
    (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)).trans (Nat.pow_le_pow_left (by omega) _)
  have hL : p.L < 7 ^ p.L := Nat.lt_pow_self (by omega)
  have hS7 : p.S7 = 7 ^ p.L := rfl
  omega

/-! ## Overwriting with the entries of a target list -/

section ext
variable {T : List ℤ} {arr n : ℕ} {μ μ' μ'' : ℕ → ℤ}

/-- The memory μ' agrees with μ outside the n cells from arr, and each of these cells holds what it
held in μ or the entry of the target T. -/
def OverwrittenWith (T : List ℤ) (arr n : ℕ) (μ μ' : ℕ → ℤ) : Prop :=
  SameOutside μ μ' arr n ∧ ∀ c < n, μ' (arr + c) = μ (arr + c) ∨ μ' (arr + c) = T.getD c 0

/-- Nothing has been written. -/
theorem OverwrittenWith.refl : OverwrittenWith T arr n μ μ := ⟨.refl, fun _ _ => Or.inl rfl⟩

/-- First some writes, then more. -/
theorem OverwrittenWith.trans (h₁ : OverwrittenWith T arr n μ μ')
    (h₂ : OverwrittenWith T arr n μ' μ'') : OverwrittenWith T arr n μ μ'' := by
  refine ⟨h₁.1.trans h₂.1, fun c hc => ?_⟩
  rcases h₂.2 c hc with h | h
  · exact (h₁.2 c hc).imp h.trans h.trans
  · exact Or.inr h

/-- One write of an entry of the target. -/
theorem OverwrittenWith.write {c : ℕ} (hc : c < n) :
    OverwrittenWith T arr n μ (Function.update μ (arr + c) (T.getD c 0)) := by
  refine ⟨SameOutside.refl.update ⟨by omega, by omega⟩ _, fun x _ => ?_⟩
  by_cases hx : x = c
  · exact Or.inr (hx ▸ Function.update_self ..)
  · exact Or.inl (Function.update_of_ne (by omega) _ _)

/-- A cell that is right stays right. -/
theorem OverwrittenWith.keep (h : OverwrittenWith T arr n μ μ') {c : ℕ} (hc : c < n)
    (hr : μ (arr + c) = T.getD c 0) :
    μ' (arr + c) = T.getD c 0 :=
  (h.2 c hc).elim (·.trans hr) id

end ext

end Light.Sec2
