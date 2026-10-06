/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.CellDependencies
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.AllBands

/-!
# The shared stage: everything up to the encodings of all bands

shared(L, m, N, D, aX, aY, b0) fills the shared block of the memory map: the tables of powers, the
coefficients φ and ψ of Schönhage's identity (Section 2.2), the table of the K₀² subsets (Section
2.3.4), band, block and digits of every row, the digits of every column, the encodings of all row
bands of X and of all column bands of Y (Section 2.4.1), and the directory. Theorem 5 and the data
structure of Section 4 both start with it.

The body is a straight line of 36 statements and the 31 stores of the directory. It is cut into
three parts (sharedA, sharedB, sharedC). For each part there are two lemmas: one runs the text
(sharedA_spec, sharedB_spec, sharedC_spec), and one, about memories only, says that what the calls
have written is all there at the end, because each call writes above the areas of the calls before
it (SharedA.of_calls, SharedB.of_calls, SharedReady.of_calls). shared_entry puts the parts together:
if every callee meets its entry with the constant c, then shared runs within 12 c + 600 times
sharedShape (sharedTime_le). The places of the areas are those of Par.places, and their sizes those
of Par.sizes.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program}

/-! ## The local variables -/

namespace Shared

/-- Local 0 of shared: L. -/
abbrev Levels : ℕ := 0
/-- Local 1 of shared: m. -/
abbrev Inner : ℕ := 1
/-- Local 2 of shared: N. -/
abbrev Rows : ℕ := 2
/-- Local 3 of shared: D. -/
abbrev Cols : ℕ := 3
/-- Local 4 of shared: the address of X. -/
abbrev AdrX : ℕ := 4
/-- Local 5 of shared: the address of Y. -/
abbrev AdrY : ℕ := 5
/-- Local 6 of shared: the base address b0 of the block. -/
abbrev Base : ℕ := 6
/-- Local 7 of shared: the address of the powers of 3. -/
abbrev AdrP3 : ℕ := 7
/-- Local 8 of shared: the address of the powers of 4. -/
abbrev AdrP4 : ℕ := 8
/-- Local 9 of shared: the address of the powers of 7. -/
abbrev AdrP7 : ℕ := 9
/-- Local 10 of shared: the address of the powers of 10. -/
abbrev AdrP10 : ℕ := 10
/-- Local 11 of shared: the address of the scratch row of Pascal's triangle. -/
abbrev AdrPas : ℕ := 11
/-- Local 12 of shared: the address of the coefficients φ. -/
abbrev AdrPhi : ℕ := 12
/-- Local 13 of shared: the address of the coefficients ψ. -/
abbrev AdrPsi : ℕ := 13
/-- Local 14 of shared: the address of the table of subsets. -/
abbrev AdrMask : ℕ := 14
/-- Local 15 of shared: the address of the bands of the rows. -/
abbrev AdrBand : ℕ := 15
/-- Local 16 of shared: the address of the blocks of the rows. -/
abbrev AdrBlock : ℕ := 16
/-- Local 17 of shared: the address of the base-3 digits. -/
abbrev AdrDig3 : ℕ := 17
/-- Local 18 of shared: the address of the base-4 digits. -/
abbrev AdrDig4 : ℕ := 18
/-- Local 19 of shared: the address of the encodings of the row bands. -/
abbrev AdrEncA : ℕ := 19
/-- Local 20 of shared: the address of the encodings of the column bands. -/
abbrev AdrEncB : ℕ := 20
/-- Local 21 of shared: the address of the input array of a band. -/
abbrev AdrArr : ℕ := 21
/-- Local 22 of shared: the address of the scratch array of encode. -/
abbrev AdrZs : ℕ := 22
/-- Local 23 of shared: the end of the block. -/
abbrev AdrEnd : ℕ := 23
/-- Local 24 of shared: L - m. -/
abbrev Outer : ℕ := 24
/-- Local 25 of shared: N₀. -/
abbrev BlockRows : ℕ := 25
/-- Local 26 of shared: K. -/
abbrev Subsets : ℕ := 26
/-- Local 27 of shared: K₀. -/
abbrev Root : ℕ := 27
/-- Local 28 of shared: K₀². -/
abbrev Table : ℕ := 28
/-- Local 29 of shared: the number of bands. -/
abbrev Bands : ℕ := 29
/-- Local 30 of shared: 10^L. -/
abbrev Leaves : ℕ := 30
/-- Local 31 of shared: 7^L. -/
abbrev Strings : ℕ := 31
/-- Local 32 of shared: takes the results of calls that return nothing. -/
abbrev Void : ℕ := 32

end Shared

open Shared

/-! ## The text -/

/-- Stores the locals of the list xs into the cells from b0 + i on. -/
def storeLocals : ℕ → List ℕ → Stmt
  | _, [] => .skip
  | i, x :: xs => .store (v Base +' k i) (v x) ;; storeLocals (i + 1) xs

/-- **storeLocals** writes the values of the locals to the cells from base + i on, changes nothing
else, and takes 5 steps for each. -/
theorem storeLocals_spec {d : ℕ} (hw : (lim.space : ℤ) ≤ lim.word) {base : ℕ} (loc : ℕ → ℤ)
    (hbase : loc Base = base) (xs : List ℕ) :
    ∀ (i : ℕ) (μ : ℕ → ℤ), base + i + xs.length ≤ lim.space →
      Ends lim P d (storeLocals i xs) ⟨loc, μ⟩ (5 * xs.length) fun σ' =>
        Seg σ'.mem (base + i) (xs.map loc) ∧ SameOutside μ σ'.mem (base + i) xs.length := by
  induction xs with
  | nil => exact fun i μ _ => Ends.skip ⟨Seg.nil, SameOutside.refl⟩
  | cons x xs ih =>
    intro i μ hsp
    rw [List.length_cons] at hsp ⊢
    have haddr : ((v Base +' k i).val ⟨loc, μ⟩).toNat = base + i := by simp [hbase]
    -- mem[base + i] := x
    refine Ends.storeThen ?_ (by light_side [hbase])
    rw [haddr]
    refine (ih (i + 1) _ (by omega)).mono (by simp; omega) ?_
    rintro σ' ⟨hs, hf⟩
    refine ⟨seg_cons.2 ⟨?_, by rw [Nat.add_assoc]; exact hs⟩, fun b hb => ?_⟩
    · rw [hf (base + i) (Or.inl (by omega)), Function.update_self]
      rfl
    · rw [hf b (by omega), Function.update_of_ne (by omega)]

/-- The first part of shared: the addresses of the first areas, the four tables of powers, and
L - m, N₀, 10^L, 7^L. -/
def sharedA : Stmt :=
  .set AdrP3 (v Base +' k 32) ;;
  .set AdrP4 (v AdrP3 +' (v Levels +' k 1)) ;;
  .set AdrP7 (v AdrP4 +' (v Levels +' k 1)) ;;
  .set AdrP10 (v AdrP7 +' (v Levels +' k 1)) ;;
  .set AdrPas (v AdrP10 +' (v Levels +' k 1)) ;;
  .set AdrPhi (v AdrPas +' (v Levels +' k 2)) ;;
  .set AdrPsi (v AdrPhi +' k 70) ;;
  .set AdrMask (v AdrPsi +' k 70) ;;
  .call pPow [k 3, v Levels, v AdrP3] Void ;;
  .call pPow [k 4, v Levels, v AdrP4] Void ;;
  .call pPow [k 7, v Levels, v AdrP7] Void ;;
  .call pPow [k 10, v Levels, v AdrP10] Void ;;
  .set Outer (v Levels -' v Inner) ;;
  .set BlockRows (M (v AdrP3 +' v Outer)) ;;
  .set Leaves (M (v AdrP10 +' v Levels)) ;;
  .set Strings (M (v AdrP7 +' v Levels)) ;;
  .skip

/-- The second part of shared: K, K₀, K₀², the coefficients, the table of subsets, band, block and
digits of every row, the digits of every column. -/
def sharedB : Stmt :=
  .call pBinom [v Levels, v Inner, v AdrPas] Subsets ;;
  .call pSqrt [v Subsets] Root ;;
  .set Table (v Root *' v Root) ;;
  .call pCoef [v AdrPhi] Void ;;
  .call pSubsets [v Levels, v Inner, v Table, v AdrMask] Void ;;
  .set AdrBand (v AdrMask +' v Table *' v Levels) ;;
  .set AdrBlock (v AdrBand +' v Rows) ;;
  .set AdrDig3 (v AdrBlock +' v Rows) ;;
  .call pCounters [v Rows, v Root, v BlockRows, v AdrBand] Void ;;
  .call pDigits [v Rows, k 3, v Outer, v AdrDig3] Void ;;
  .set AdrDig4 (v AdrDig3 +' v Rows *' v Outer) ;;
  .call pDigits [v Cols, k 4, v Inner, v AdrDig4] Void ;;
  .set AdrEncA (v AdrDig4 +' v Cols *' v Inner) ;;
  .skip

/-- The number of bands: 0 if there is no row, and else one more than the band of the last row. -/
def sharedBands : Stmt :=
  .ite (v Rows =' k 0) (.set Bands (k 0)) (.set Bands (M (v AdrBand +' (v Rows -' k 1)) +' k 1))

/-- The third part of shared: the number of bands, the last addresses, the encodings of all bands,
and the directory. -/
def sharedC : Stmt :=
  sharedBands ;;
  .set AdrEncB (v AdrEncA +' v Bands *' v Leaves) ;;
  .set AdrArr (v AdrEncB +' v Bands *' v Leaves) ;;
  .set AdrZs (v AdrArr +' v Strings) ;;
  .set AdrEnd (v AdrZs +' v Strings) ;;
  .call pEncodeBands [v Levels, v Inner, v Rows, v Cols, v Root, v BlockRows, v Strings, v Leaves,
    v Bands, k 0, v AdrX, v Cols, k 1, v AdrMask, v AdrDig3, v AdrDig4, v AdrArr, v AdrZs, v AdrPhi,
    v AdrP7, v AdrP10, v AdrEncA] Void ;;
  .call pEncodeBands [v Levels, v Inner, v Rows, v Cols, v Root, v BlockRows, v Strings, v Leaves,
    v Bands, k 1, v AdrY, k 1, v Rows, v AdrMask, v AdrDig3, v AdrDig4, v AdrArr, v AdrZs, v AdrPsi,
    v AdrP7, v AdrP10, v AdrEncB] Void ;;
  storeLocals 0 [Levels, Inner, Rows, Cols, Outer, BlockRows, Subsets, Root, Table, Bands, Leaves,
    Strings, AdrX, AdrY, AdrP3, AdrP4, AdrP7, AdrP10, AdrPas, AdrPhi, AdrPsi, AdrMask, AdrBand,
    AdrBlock, AdrDig3, AdrDig4, AdrEncA, AdrEncB, AdrArr, AdrZs, AdrEnd]

/-- shared(L, m, N, D, aX, aY, b0). -/
def sharedBody : Stmt := sharedA ;; sharedB ;; sharedC

/-- The time of the first part, if every callee meets its entry with the constant c. -/
def sharedTimeA (c : ℕ) (p : Par) : ℕ := 4 * (c * (p.L + 1)) + 81

/-- The time of the second part. -/
def sharedTimeB (c : ℕ) (p : Par) : ℕ :=
  c * (p.L + 1) ^ 2 + c * (Nat.sqrt p.K + 1) + c + c * ((p.KK + 1) * (p.L + 1)) + c * (p.N + 1)
    + c * ((p.N + 1) * (p.Lo + 1)) + c * ((p.D + 1) * (p.m + 1)) + 65

/-- The time of the third part. -/
def sharedTimeC (c : ℕ) (p : Par) : ℕ := 2 * (c * (p.nB * (p.T + bandArrayShape p) + 1)) + 236

/-- The locals at the start: the arguments, then zeros. -/
def sharedLoc0 (p : Par) (aX aY b0 : ℕ) : List ℤ :=
  [(p.L : ℤ), (p.m : ℤ), (p.N : ℤ), (p.D : ℤ), (aX : ℤ), (aY : ℤ), (b0 : ℤ), 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The locals after the first part; r is what the last call left in local 32. -/
def sharedLocA (p : Par) (aX aY b0 : ℕ) (r : ℤ) : List ℤ :=
  [(p.L : ℤ), (p.m : ℤ), (p.N : ℤ), (p.D : ℤ), (aX : ℤ), (aY : ℤ), (b0 : ℤ), (p.aP3 b0 : ℤ),
    (p.aP4 b0 : ℤ), (p.aP7 b0 : ℤ), (p.aP10 b0 : ℤ), (p.aPAS b0 : ℤ), (p.aPHI b0 : ℤ),
    (p.aPSI b0 : ℤ), (p.aMASK b0 : ℤ), 0, 0, 0, 0, 0, 0, 0, 0, 0, (p.Lo : ℤ), (p.N0 : ℤ), 0, 0, 0,
    0, (p.T : ℤ), (p.S7 : ℤ), r]

/-- The locals after the second part. -/
def sharedLocB (p : Par) (aX aY b0 : ℕ) (r : ℤ) : List ℤ :=
  [(p.L : ℤ), (p.m : ℤ), (p.N : ℤ), (p.D : ℤ), (aX : ℤ), (aY : ℤ), (b0 : ℤ), (p.aP3 b0 : ℤ),
    (p.aP4 b0 : ℤ), (p.aP7 b0 : ℤ), (p.aP10 b0 : ℤ), (p.aPAS b0 : ℤ), (p.aPHI b0 : ℤ),
    (p.aPSI b0 : ℤ), (p.aMASK b0 : ℤ), (p.aBAND b0 : ℤ), (p.aBLOCK b0 : ℤ), (p.aDIG3 b0 : ℤ),
    (p.aDIG4 b0 : ℤ), (p.aENCA b0 : ℤ), 0, 0, 0, 0, (p.Lo : ℤ), (p.N0 : ℤ), (p.K : ℤ), (p.K0 : ℤ),
    (p.KK : ℤ), 0, (p.T : ℤ), (p.S7 : ℤ), r]

/-- What the first part leaves in the memory. -/
structure SharedA (p : Par) (b0 : ℕ) (μ μ' : ℕ → ℤ) : Prop extends PowTables p b0 μ' where
  same : SameOutside μ μ' (p.aP3 b0) (p.aPAS b0 - p.aP3 b0)

/-- What the second part leaves in the memory. -/
structure SharedB (p : Par) (b0 : ℕ) (μ μ' : ℕ → ℤ) : Prop extends RowTables p b0 μ' where
  same : SameOutside μ μ' (p.aPAS b0) (p.aENCA b0 - p.aPAS b0)

/-- The entries of the routines that the shared stage calls, with their constants. -/
structure SharedCallees (lim : Limits) (P : Program) (c : ℕ) : Prop where
  pow : PowSpec lim P c
  binom : BinomSpec lim P c
  sqrt : SqrtSpec lim P c
  coef : CoefSpec lim P c
  subsets : SubsetsSpec lim P c
  counters : CountersSpec lim P c
  digits : DigitsSpec lim P c
  bandsL : EncodeBandsLSpec lim P c
  bandsR : EncodeBandsRSpec lim P c

/-- The assumption on the word size, in terms of `T = 10^L`. -/
theorem Par.ten_T_le {p : Par} (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word) :
    10 * (p.T : ℤ) ≤ lim.word := by
  rw [pow_succ, Nat.mul_comm] at h10
  exact_mod_cast h10

/-- What the four calls of the first part leave in the memory: each writes its own area, above the
areas of the calls before it. -/
theorem SharedA.of_calls {p : Par} {b0 : ℕ} {μ μP3 μP4 μP7 μP10 : ℕ → ℤ}
    (sP3 : Seg μP3 (p.aP3 b0) (powList 3 (p.L + 1))) (fP3 : SameOutside μ μP3 (p.aP3 b0) (p.L + 1))
    (sP4 : Seg μP4 (p.aP4 b0) (powList 4 (p.L + 1)))
    (fP4 : SameOutside μP3 μP4 (p.aP4 b0) (p.L + 1))
    (sP7 : Seg μP7 (p.aP7 b0) (powList 7 (p.L + 1)))
    (fP7 : SameOutside μP4 μP7 (p.aP7 b0) (p.L + 1))
    (sP10 : Seg μP10 (p.aP10 b0) (powList 10 (p.L + 1)))
    (fP10 : SameOutside μP7 μP10 (p.aP10 b0) (p.L + 1)) : SharedA p b0 μ μP10 := by
  have hplaces := p.places b0
  have lp : ∀ b, (powList b (p.L + 1)).length = p.L + 1 := fun b => length_powList b _
  refine
    { p3 := sP3.keep (by light_keep [lp])
      p4 := sP4.keep (by light_keep [lp])
      p7 := sP7.keep (by light_keep [lp])
      p10 := sP10
      same := fun x hx => ?_ }
  rw [fP10 x (by omega), fP7 x (by omega), fP4 x (by omega), fP3 x (by omega)]

/-- The entry of pow, for a table of the powers b^0, …, b^L of a base b ≤ 10. -/
theorem SharedCallees.powTable {c : ℕ} (C : SharedCallees lim P c) {p : Par}
    (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word) (b dst : ℕ) (μ : ℕ → ℤ)
    (one_le : 1 ≤ b := by omega) (le_ten : b ≤ 10 := by omega) (dst_pos : 1 ≤ dst := by omega)
    (dst_le : dst + (p.L + 1) ≤ lim.space := by omega) :
    ∀ d, d ≤ lim.depth → Meets lim P pPow d [b, p.L, dst] μ (c * (p.L + 1)) fun _ μ' =>
      Seg μ' dst (powList b (p.L + 1)) ∧ SameOutside μ μ' dst (p.L + 1) :=
  C.pow b p.L dst μ dst_pos dst_le one_le
    (le_trans (by exact_mod_cast Nat.pow_le_pow_left le_ten _) h10)

/-- **The first part of shared.** -/
theorem sharedA_spec (std : Std lim) {c : ℕ} (C : SharedCallees lim P c) {d : ℕ} {p : Par}
    (hmL : p.m ≤ p.L) {aX aY b0 : ℕ} (hd : d + (p.L + 3) ≤ lim.depth)
    (hsp : p.sharedEnd b0 ≤ lim.space) (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word)
    (μ : ℕ → ℤ) :
    Ends lim P d sharedA ⟨frame (sharedLoc0 p aX aY b0), μ⟩ (sharedTimeA c p) fun σ' =>
      (∃ r, σ'.loc = frame (sharedLocA p aX aY b0 r)) ∧ SharedA p b0 μ σ'.mem := by
  have hw := std.space_le
  have h100 := std.const_le
  have hplaces := p.places b0
  have hsizes := p.sizes hmL
  have hTw := Par.ten_T_le h10
  unfold sharedA sharedTimeA sharedLoc0
  -- the addresses of the first eight areas
  light_set (p.aP3 b0 : ℕ)
  light_set (p.aP4 b0 : ℕ)
  light_set (p.aP7 b0 : ℕ)
  light_set (p.aP10 b0 : ℕ)
  light_set (p.aPAS b0 : ℕ)
  light_set (p.aPHI b0 : ℕ)
  light_set (p.aPSI b0 : ℕ)
  light_set (p.aMASK b0 : ℕ)
  -- the powers of 3, 4, 7 and 10
  light_call (C.powTable h10 3 (p.aP3 b0) μ) with rP3 μP3 ⟨sP3, fP3⟩
  light_call (C.powTable h10 4 (p.aP4 b0) μP3) with rP4 μP4 ⟨sP4, fP4⟩
  light_call (C.powTable h10 7 (p.aP7 b0) μP4) with rP7 μP7 ⟨sP7, fP7⟩
  light_call (C.powTable h10 10 (p.aP10 b0) μP7) with rP10 μP10 ⟨sP10, fP10⟩
  have hA := SharedA.of_calls sP3 fP3 sP4 fP4 sP7 fP7 sP10 fP10
  -- L - m, and then N₀ = 3^{L-m}, 10^L and 7^L from the tables
  have read : ∀ {b a i : ℕ}, Seg μP10 a (powList b (p.L + 1)) → i ≤ p.L →
      μP10 (a + i) = (b ^ i : ℕ) :=
    fun h hi => by rw [h.get (by rw [length_powList]; omega), getElem_powList]
  have hN0 : μP10 (p.aP3 b0 + p.Lo) = (p.N0 : ℕ) := read hA.p3 (by omega)
  have hT : μP10 (p.aP10 b0 + p.L) = (p.T : ℕ) := read hA.p10 le_rfl
  have hS7 : μP10 (p.aP7 b0 + p.L) = (p.S7 : ℕ) := read hA.p7 le_rfl
  light_set (p.Lo : ℕ)
  light_set (p.N0 : ℕ) using hN0
  light_set (p.T : ℕ) using hT
  light_set (p.S7 : ℕ) using hS7
  exact ⟨⟨rP10, rfl⟩, hA⟩

/-- What the six calls of the second part that write to the memory leave in it (the square root
writes nothing): each writes its own area, above the areas of the calls before it, so that all the
tables are there at the end. -/
theorem SharedB.of_calls {p : Par} {b0 : ℕ} {μ μPas μPhi μMask μBand μDig3 μDig4 : ℕ → ℤ}
    (fPas : SameOutside μ μPas (p.aPAS b0) (p.L + 2))
    (sphi : Seg μPhi (p.aPHI b0) Spec.phiFlat)
    (spsi : Seg μPhi (p.aPHI b0 + 70) Spec.psiFlat)
    (fPhi : SameOutside μPas μPhi (p.aPHI b0) 140)
    (smask : ∀ s < p.KK, SegB μMask (p.aMASK b0 + s * p.L) (Spec.unrank p.L p.m s))
    (fMask : SameOutside μPhi μMask (p.aMASK b0) (p.KK * p.L))
    (sband : ∀ I < p.N, μBand (p.aBAND b0 + I) = (I / (p.K0 * p.N0) : ℕ)
      ∧ μBand (p.aBAND b0 + p.N + I) = (I / p.N0 % p.K0 : ℕ))
    (fBand : SameOutside μMask μBand (p.aBAND b0) (2 * p.N))
    (sdig3 : ∀ I < p.N, SegN μDig3 (p.aDIG3 b0 + I * p.Lo) (ThreeSumApsp.digitList 3 p.Lo (I % 3 ^
        p.Lo)))
    (fDig3 : SameOutside μBand μDig3 (p.aDIG3 b0) (p.N * p.Lo))
    (sdig4 : ∀ x < p.D, SegN μDig4 (p.aDIG4 b0 + x * p.m) (ThreeSumApsp.digitList 4 p.m (x % 4 ^
        p.m)))
    (fDig4 : SameOutside μDig3 μDig4 (p.aDIG4 b0) (p.D * p.m)) : SharedB p b0 μ μDig4 := by
  have hplaces := p.places b0
  have lphi := Spec.length_phiFlat
  have lpsi := Spec.length_psiFlat
  -- The last memory agrees with each earlier one below the area that was written next.
  have lowDig3 : ∀ x < p.aDIG4 b0, μDig4 x = μDig3 x := fun x hx => fDig4 x (Or.inl hx)
  have lowBand : ∀ x < p.aDIG3 b0, μDig4 x = μBand x := fun x hx => by
    rw [lowDig3 x (by omega), fDig3 x (Or.inl hx)]
  have lowMask : ∀ x < p.aBAND b0, μDig4 x = μMask x := fun x hx => by
    rw [lowBand x (by omega), fBand x (Or.inl hx)]
  have lowPhi : ∀ x < p.aMASK b0, μDig4 x = μPhi x := fun x hx => by
    rw [lowMask x (by omega), fMask x (Or.inl hx)]
  refine
    { phi := sphi.congr fun i hi => lowPhi _ (by omega)
      psi := spsi.congr fun i hi => lowPhi _ (by omega)
      mask := fun s hs => (smask s hs).congr fun i hi => lowMask _ ?_
      band := fun I hI => (lowBand _ (by omega)).trans (sband I hI).1
      block := fun I hI => (lowBand _ (by omega)).trans (sband I hI).2
      dig3 := fun I hI => (sdig3 I hI).congr fun i hi => lowDig3 _ ?_
      dig4 := fun x hx => ?_
      same := fun x hx => ?_ }
  · rw [List.length_map, Spec.length_unrank] at hi
    have := Nat.mul_add_lt_mul hs hi
    omega
  · have hi' : i < p.Lo := by simpa [ThreeSumApsp.digitList] using hi
    have := Nat.mul_add_lt_mul hI hi'
    omega
  · have h := sdig4 x hx
    rwa [Nat.mod_eq_of_lt (show x < 4 ^ p.m from hx)] at h
  · show μDig4 x = μ x
    rw [fDig4 x (by omega), fDig3 x (by omega), fBand x (by omega), fMask x (by omega),
      fPhi x (by omega), fPas x (by omega)]

/-- **The second part of shared.** -/
theorem sharedB_spec (std : Std lim) {c : ℕ} (C : SharedCallees lim P c) {d : ℕ} {p : Par}
    (hmL : p.m ≤ p.L) {aX aY b0 : ℕ} (hd : d + (p.L + 3) ≤ lim.depth)
    (hsp : p.sharedEnd b0 ≤ lim.space) (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word)
    (μ : ℕ → ℤ) (r0 : ℤ) :
    Ends lim P d sharedB ⟨frame (sharedLocA p aX aY b0 r0), μ⟩ (sharedTimeB c p) fun σ' =>
      (∃ r, σ'.loc = frame (sharedLocB p aX aY b0 r)) ∧ SharedB p b0 μ σ'.mem := by
  have hw := std.space_le
  have h100 := std.const_le
  have hplaces := p.places b0
  have hsizes := p.sizes hmL
  have eKK : p.KK = p.K0 * p.K0 := rfl
  have hTw := Par.ten_T_le h10
  unfold sharedB sharedTimeB sharedLocA
  -- K := binom(L, m)
  light_call (C.binom p.L p.m (p.aPAS b0) μ (by omega) hmL
    (le_trans (by exact_mod_cast p.two_pow_le_T) (by omega : (p.T : ℤ) ≤ lim.word)))
    with r μPas ⟨hr, fPas⟩
  obtain rfl : r = (p.K : ℕ) := hr
  -- K₀ := ⌊√K⌋ and K₀²
  light_call (C.sqrt p.K μPas (by push_cast; omega)) with r μPas' ⟨hr, hμ⟩
  obtain rfl : r = (p.K0 : ℕ) := hr
  obtain rfl : μPas = μPas' := hμ.symm
  light_set (p.KK : ℕ)
  -- the coefficients and the table of subsets
  light_call (C.coef (p.aPHI b0) μPas (by omega)) with rPhi μPhi ⟨sphi, spsi, fPhi⟩
  light_call (C.subsets p.L p.m p.KK (p.aMASK b0) μPhi (by omega) hmL p.KK_le_K
    (by push_cast; omega)) with rMask μMask ⟨smask, fMask⟩
  -- band and block of every row
  light_set (p.aBAND b0 : ℕ)
  light_set (p.aBLOCK b0 : ℕ)
  light_set (p.aDIG3 b0 : ℕ)
  light_call (C.counters p.N p.K0 p.N0 (p.aBAND b0) μMask (by omega) (by omega)
    (by omega) (by push_cast; omega)) with rBand μBand ⟨sband, fBand⟩
  -- the digits of every row and of every column
  light_call (C.digits p.N 3 p.Lo (p.aDIG3 b0) μBand (by omega) (by norm_num)
    (by push_cast; omega) (by omega)) with rDig3 μDig3 ⟨sdig3, fDig3⟩
  light_set (p.aDIG4 b0 : ℕ)
  light_call (C.digits p.D 4 p.m (p.aDIG4 b0) μDig3 (by omega) (by norm_num)
    (by push_cast; omega) (by omega)) with rDig4 μDig4 ⟨sdig4, fDig4⟩
  light_set (p.aENCA b0 : ℕ)
  exact ⟨⟨rDig4, rfl⟩,
    .of_calls fPas sphi spsi fPhi smask fMask sband fBand sdig3 fDig3 sdig4 fDig4⟩

/-- What bandArray reads of the tables. -/
theorem SharedTables.bandTables {p : Par} {b0 : ℕ} {μ : ℕ → ℤ} (h : SharedTables p b0 μ) :
    BandTables p μ (p.aMASK b0) (p.aDIG3 b0) (p.aDIG4 b0) (p.aENCA b0) := by
  have hplaces := p.places b0
  exact ⟨h.mask, h.dig3, h.dig4, by omega, by omega, by omega⟩

/-- The addresses that the shared stage hands to encodeBands: the coefficients stand at tab, and the
encodings are written from enc on. -/
@[simp] def Par.bandsArgs (p : Par) (b0 tab enc : ℕ) : BandsArgs where
  mask := p.aMASK b0
  dig3 := p.aDIG3 b0
  dig4 := p.aDIG4 b0
  arr := p.aARR b0
  zs := p.aZS b0
  tab := tab
  p7 := p.aP7 b0
  p10 := p.aP10 b0
  enc := enc

/-- What encodeBands assumes holds once the tables are there, for either of the two areas enc of
encodings. -/
theorem SharedTables.bandsPre {p : Par} {b0 tab enc : ℕ} {μ : ℕ → ℤ} {coefs : List ℤ} {V : ℤ}
    (h : SharedTables p b0 μ) (hsp : p.sharedEnd b0 ≤ lim.space) (hV0 : 0 ≤ V)
    (hVB : 7 ^ (p.L + 1) * V ≤ lim.word) (coef : Seg μ tab coefs) (coef_le : tab + 70 ≤ enc)
    (le_enc : p.aENCA b0 ≤ enc) (enc_le : enc + p.nB * p.T ≤ p.aARR b0) :
    BandsPre lim p μ (p.bandsArgs b0 tab enc) coefs V := by
  have hplaces := p.places b0
  exact
    { tables := h.bandTables.mono le_enc
      coef := coef
      coef_le := coef_le
      p7 := h.p7
      p7_le := show p.aP7 b0 + (p.L + 1) ≤ enc by omega
      p10 := h.p10
      p10_le := show p.aP10 b0 + (p.L + 1) ≤ enc by omega
      enc_le := enc_le
      arr_le := show p.aARR b0 + p.S7 ≤ p.aZS b0 by omega
      zs_le := show p.aZS b0 + p.S7 ≤ lim.space by omega
      V_nonneg := hV0
      word := hVB }

/-- The number of bands, from the band of the last row. -/
theorem nB_eq (p : Par) (hmL : p.m ≤ p.L) :
    (p.N = 0 → p.nB = 0) ∧ (0 < p.N → p.nB = (p.N - 1) / (p.K0 * p.N0) + 1) := by
  have hb : 0 < p.K0 * p.N0 := Nat.mul_pos (K0_pos hmL) (N0_pos _ _)
  have e : p.nB = (p.N + p.K0 * p.N0 - 1) / (p.K0 * p.N0) := rfl
  constructor
  · intro h
    rw [e, h, Nat.zero_add]
    exact Nat.div_eq_of_lt (by omega)
  · intro h
    rw [e, ← Nat.add_div_right _ hb]
    congr 1
    omega

/-- **The number of bands**: 0 if there is no row, and else one more than the band of the last
row. -/
theorem sharedBands_spec (std : Std lim) {d : ℕ} {p : Par} (hmL : p.m ≤ p.L) {aX aY b0 : ℕ}
    (hsp : p.sharedEnd b0 ≤ lim.space) (μ : ℕ → ℤ) (r0 : ℤ) (tb : SharedTables p b0 μ) :
    Ends lim P d sharedBands ⟨frame (sharedLocB p aX aY b0 r0), μ⟩ 13 fun σ' =>
      σ' = ⟨frame (setLocal (sharedLocB p aX aY b0 r0) Bands (p.nB : ℕ)), μ⟩ := by
  have hw := std.space_le
  have h100 := std.const_le
  have hplaces := p.places b0
  obtain ⟨hnB0, hnB1⟩ := nB_eq p hmL
  unfold sharedBands sharedLocB
  refine Ends.iteLast (fun hN => ?_) (fun hN => ?_)
  · -- nB := 0
    have hNzero : p.N = 0 := by simpa using hN
    exact Ends.setTo (p.nB : ℕ) rfl (by simp [hnB0 hNzero]; omega)
  · -- nB := mem[BAND + (N - 1)] + 1
    have hNpos : 0 < p.N := Nat.pos_of_ne_zero (by simpa using hN)
    have hlast := tb.band (p.N - 1) (by omega)
    have haddr : ((p.aBAND b0 : ℤ) + ((p.N : ℤ) - 1)).toNat = p.aBAND b0 + (p.N - 1) := by omega
    have hle : (p.N - 1) / (p.K0 * p.N0) ≤ p.N := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
    have hnB := hnB1 hNpos
    generalize (p.N - 1) / (p.K0 * p.N0) = q at hlast hle hnB
    exact Ends.setTo (p.nB : ℕ) rfl (by light_side [haddr, hlast, hnB])

/-- What the two calls of encodeBands and the stores of the directory leave in the memory. -/
theorem SharedReady.of_calls {p : Par} (hmL : p.m ≤ p.L) {aX aY b0 : ℕ}
    {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
    {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {μ μEncA μEncB μDir : ℕ → ℤ}
    (tb : SharedTables p b0 μ)
    (sA : ∀ β < p.nB, Seg μEncA (p.aENCA b0 + β * p.T)
      (Spec.arrT (encodingL (bandArrayL (Spec.stdLayout hmL) X β))))
    (fEncA : SameOutside μ μEncA (p.aENCA b0) (p.sharedEnd b0 - p.aENCA b0))
    (sB : ∀ β < p.nB, Seg μEncB (p.aENCB b0 + β * p.T)
      (Spec.arrT (encodingR (bandArrayR (Spec.stdLayout hmL) Y β))))
    (fEncB : SameOutside μEncA μEncB (p.aENCB b0) (p.sharedEnd b0 - p.aENCB b0))
    (sdir : SegN μDir b0 (dirList p aX aY b0)) (fDir : SameOutside μEncB μDir b0 31) :
    SharedReady p hmL aX aY b0 X Y μDir ∧ SameOutside μ μDir b0 (p.sharedEnd b0 - b0) := by
  have hplaces := p.places b0
  have above : ∀ x, p.aP3 b0 ≤ x → μDir x = μEncB x := fun x hx => fDir x (Or.inr (by omega))
  have tbDir : SharedTables p b0 μDir := tb.congr fun x h1 h2 => by
    rw [above x h1, fEncB x (Or.inl (by omega)), fEncA x (Or.inl h2)]
  refine ⟨{ tbDir with
    dir := sdir
    encA := fun β hβ => (sA β hβ).congr fun i hi => ?_
    encB := fun β hβ => (sB β hβ).congr fun i hi => above _ (by omega) }, fun x hx => ?_⟩
  · rw [Spec.length_arrT] at hi
    have := Nat.mul_add_lt_mul hβ (show i < p.T from hi)
    rw [above _ (by omega), fEncB _ (Or.inl (by omega))]
  · show μDir x = μ x
    rw [fDir x (by omega), fEncB x (by omega), fEncA x (by omega)]

/-- **The third part of shared.** -/
theorem sharedC_spec (std : Std lim) {c : ℕ} (C : SharedCallees lim P c) {d : ℕ} {p : Par}
    (hmL : p.m ≤ p.L) {aX aY b0 : ℕ} (hd : d + (p.L + 3) ≤ lim.depth)
    (hsp : p.sharedEnd b0 ≤ lim.space) (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word)
    (μ : ℕ → ℤ) (r0 : ℤ) {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
    {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {V : ℤ} (hX : MatAt μ aX X)
    (hY : MatAt μ aY Y) (hXle : aX + p.N * p.D ≤ b0) (hYle : aY + p.D * p.N ≤ b0) (hV0 : 0 ≤ V)
    (hVX : ∀ i j, |X i j| ≤ V) (hVY : ∀ i j, |Y i j| ≤ V) (hVB : 7 ^ (p.L + 1) * V ≤ lim.word)
    (tb : SharedTables p b0 μ) :
    Ends lim P d sharedC ⟨frame (sharedLocB p aX aY b0 r0), μ⟩ (sharedTimeC c p) fun σ' =>
      SharedReady p hmL aX aY b0 X Y σ'.mem ∧ SameOutside μ σ'.mem b0 (p.sharedEnd b0 - b0) := by
  have hw := std.space_le
  have h100 := std.const_le
  have hplaces := p.places b0
  have hsizes := p.sizes hmL
  have hTw := Par.ten_T_le h10
  unfold sharedC sharedTimeC
  -- the number of bands
  refine Ends.next 13 ((sharedBands_spec std hmL hsp μ r0 tb).mono le_rfl ?_)
  rintro _ rfl
  unfold sharedLocB
  -- the last four addresses
  light_set (p.aENCB b0 : ℕ)
  light_set (p.aARR b0 : ℕ)
  light_set (p.aZS b0 : ℕ)
  light_set (p.sharedEnd b0 : ℕ)
  -- the encodings of the row bands of X
  have preA : BandsPre lim p μ (p.bandsArgs b0 (p.aPHI b0) (p.aENCA b0)) Spec.phiFlat V :=
    tb.bandsPre hsp hV0 hVB tb.phi (coef_le := by omega) (le_enc := le_rfl) (enc_le := by omega)
  light_call (C.bandsL p hmL _ aX μ X V preA hX
    (hXle.trans (show b0 ≤ p.aENCA b0 by omega)) hVX) with rEncA μEncA ⟨sA, fEncA⟩
  -- the encodings of the column bands of Y
  have lowEncA : ∀ x < p.aENCA b0, μEncA x = μ x := fun x hx => fEncA x (Or.inl hx)
  have tbEncA : SharedTables p b0 μEncA := tb.congr fun x _ hx => lowEncA x hx
  have hYle' : aY + ThreeSumApsp.D p.m * p.N ≤ p.aENCA b0 := le_trans hYle (by omega)
  have preB : BandsPre lim p μEncA (p.bandsArgs b0 (p.aPSI b0) (p.aENCB b0)) Spec.psiFlat V :=
    tbEncA.bandsPre hsp hV0 hVB tbEncA.psi (coef_le := by omega) (le_enc := by omega)
      (enc_le := by omega)
  light_call (C.bandsR p hmL _ aY μEncA Y V preB (hY.congr_below lowEncA hYle')
    (hYle.trans (show b0 ≤ p.aENCB b0 by omega)) hVY) with rEncB μEncB ⟨sB, fEncB⟩
  -- the directory
  refine (storeLocals_spec hw (base := b0) _ (by simp) _ 0 μEncB (by simp; omega)).mono
    (by simp; omega) ?_
  rintro ⟨_, μDir⟩ ⟨sdir, fDir⟩
  exact SharedReady.of_calls hmL tb sA fEncA sB fEncB (by simpa [SegN, dirList] using sdir)
    (by simpa using fDir)

/-- The time of the shared stage has the shape of its entry. -/
theorem sharedTime_le (c : ℕ) (p : Par) :
    sharedTimeA c p + (sharedTimeB c p + sharedTimeC c p) ≤ (12 * c + 600) * sharedShape p := by
  unfold sharedTimeA sharedTimeB sharedTimeC sharedShape
  -- The terms that are not in the shape: L + 1 ≤ (L + 1)², N + 1 ≤ (N + 1) (L - m + 1), 1 ≤ (L +
  -- 1)².
  have hL : p.L + 1 ≤ (p.L + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN : p.N + 1 ≤ (p.N + 1) * (p.Lo + 1) := Nat.le_mul_of_pos_right _ (by omega)
  generalize (p.L + 1) ^ 2 = s, Nat.sqrt p.K + 1 = q, (p.KK + 1) * (p.L + 1) = u,
    (p.N + 1) * (p.Lo + 1) = w, (p.D + 1) * (p.m + 1) = x,
    p.nB * (p.T + bandArrayShape p) = y at hL hN ⊢
  have hcL := Nat.mul_le_mul_left c hL
  have hcN := Nat.mul_le_mul_left c hN
  have hc1 := Nat.mul_le_mul_left c (show 1 ≤ s by omega)
  have hy : c * (y + 1) = c * y + c := Nat.mul_succ c y
  have hright : (12 * c + 600) * (s + q + u + w + x + y) = 12 * (c * s) + 12 * (c * q)
      + 12 * (c * u) + 12 * (c * w) + 12 * (c * x) + 12 * (c * y)
      + 600 * (s + q + u + w + x + y) := by ring
  omega

/-- The tables of the first part are still there after the second part. -/
theorem SharedTables.of_parts {p : Par} {b0 : ℕ} {μ μA μB : ℕ → ℤ} (hA : SharedA p b0 μ μA)
    (hB : SharedB p b0 μA μB) : SharedTables p b0 μB := by
  have hplaces := p.places b0
  have lp : ∀ b, (powList b (p.L + 1)).length = p.L + 1 := fun b => length_powList b _
  exact
    { hB.toRowTables with
      p3 := hA.p3.keep (by light_keep [hB.same, lp])
      p4 := hA.p4.keep (by light_keep [hB.same, lp])
      p7 := hA.p7.keep (by light_keep [hB.same, lp])
      p10 := hA.p10.keep (by light_keep [hB.same, lp]) }

/-- **shared** meets its entry of the map: if every callee meets its entry with the constant c, then
shared does with the constant 12 c + 600. -/
theorem shared_entry (std : Std lim) (hP : P[pShared]? = some sharedBody) {c : ℕ}
    (C : SharedCallees lim P c) {c' : ℕ} (hc : 12 * c + 600 ≤ c') : SharedSpec lim P c' := by
  intro p hmL aX aY b0 μ X Y V pre d hd
  have hplaces := p.places b0
  refine .mono_const (.of_body hP (Ends.mono ?_ (sharedTime_le c p) fun _ h => h)) hc
  rw [← frame_append_zeros [(p.L : ℤ), p.m, p.N, p.D, aX, aY, b0] 26]
  unfold sharedBody
  -- the first part
  light_piece (sharedA_spec std C hmL hd pre.space pre.ten μ) with ⟨locA, μA⟩ ⟨⟨rA, hlocA⟩, hA⟩
  obtain rfl : locA = _ := hlocA
  dsimp only at hA
  -- the second part
  light_piece (sharedB_spec std C hmL hd pre.space pre.ten μA rA) with ⟨locB, μB⟩ ⟨⟨rB, hlocB⟩, hB⟩
  obtain rfl : locB = _ := hlocB
  dsimp only at hB
  -- the third part; the matrices lie below the block, and max V 0 bounds their entries as well
  have low : ∀ x < b0, μB x = μ x := fun x hx => by
    rw [hB.same x (Or.inl (by omega)), hA.same x (Or.inl (by omega))]
  have hVB' : 7 ^ (p.L + 1) * max V 0 ≤ lim.word := by
    rcases le_total V 0 with h | h
    · rw [max_eq_right h, mul_zero]
      exact le_trans (by norm_num) std.const_le
    · rw [max_eq_left h]
      exact pre.seven
  refine (sharedC_spec std C hmL hd pre.space pre.ten μB rB (pre.matX.congr_below low pre.belowX)
    (pre.matY.congr_below low pre.belowY) pre.belowX pre.belowY (le_max_right V 0)
    (fun i j => (pre.absX i j).trans (le_max_left _ _))
    (fun i j => (pre.absY i j).trans (le_max_left _ _)) hVB' (.of_parts hA hB)).mono (by omega) ?_
  rintro σ' ⟨hR, hf⟩
  exact ⟨hR, fun x hx => by rw [hf x hx, hB.same x (by omega), hA.same x (by omega)]⟩

end Light.Sec2
