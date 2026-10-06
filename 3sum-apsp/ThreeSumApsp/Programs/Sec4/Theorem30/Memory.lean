/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.CellDependencies
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts

/-!
# Theorem 30 in the light language: the memory map and the invariant of the data structure

The data structure occupies one block of the memory, from a base address b0 on. First comes the
shared block of Section 2 (directory, tables, the encodings of all bands), and behind it the areas
of Section 4:

    WD (L) | CUR (L) | BOX (L) | SS (m) | FP (1) | ROOTS (nB²) | TR (cap)

WD holds the digits of the output string of a query; CUR, BOX and SS are scratch strings; FP holds
the length of the trie array; ROOTS holds the roots of the tries, that of tile (β, β') in the cell
β nB + β'; TR is the trie area. Cell 31 of the directory holds t. `Areas` says where the tables that
the routines of Section 4 read and the areas of Section 4 lie, and `areas` proves it.

Two routines know this map: preCore(L, m, t, N, D, aX, aY, b0) builds the block from the matrices at
aX and aY, which lie below b0, and queryAt(I, J, b0) answers a query from it. They are relocatable,
so that Theorem 30, its offline form and Corollary 26 use the same two routines. The main procedures
of Theorem 30's programs only read the sizes from the input and compute the addresses. For Corollary
26 a routine of its own stands in between: it finds m and, from the threshold of the proof on, L and
t, writes padded copies of the matrices, and runs `preCore` on them.

Section 4.3: "Our data structure consists of three components: the list of the K₀² subsets Q
assigned to the block products of a tile […], the encodings of all row bands and all column bands,
and for every tile, the values of all its boxes". In the invariant DSReady the field shared holds
the first two, and the fields roots and trie hold the third: "for each tile we store its boxes, with
their values, in a standard trie on their strings of L symbols". The tries of all tiles lie in one
array (trie), and the table roots has the root of the trie of each tile. The invariant depends only
on the cells from b0 on, without the scratch strings (`DSReady.congr`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The map -/

/-- The digits of the output string of a query: L cells. -/
def aWD (p : Sec2.Par) (b0 : ℕ) : ℕ := p.sharedEnd b0
/-- Scratch of the preprocessing, the current leaf: L cells. -/
def aCUR (p : Sec2.Par) (b0 : ℕ) : ℕ := aWD p b0 + p.L
/-- Scratch, the current box: L cells. -/
def aBOX (p : Sec2.Par) (b0 : ℕ) : ℕ := aCUR p b0 + p.L
/-- Scratch of a query, the current string on the levels of Q: m cells. -/
def aSS (p : Sec2.Par) (b0 : ℕ) : ℕ := aBOX p b0 + p.L
/-- The cell that holds the length of the trie array. -/
def aFP (p : Sec2.Par) (b0 : ℕ) : ℕ := aSS p b0 + p.m
/-- The roots of the tries: one cell for each tile. -/
def aROOTS (p : Sec2.Par) (b0 : ℕ) : ℕ := aFP p b0 + 1
/-- The trie area. -/
def aTR (p : Sec2.Par) (b0 : ℕ) : ℕ := aROOTS p b0 + p.nB * p.nB
/-- The capacity of the trie area (`Spec.length_allTries_le`). -/
def trieCap (p : Sec2.Par) (t : ℕ) : ℕ :=
  1 + p.nB * p.nB * (11 * (1 + p.L * (boxes p.L p.m t).card))
/-- The first address behind the block (one cell is left unused, so that every address of the block
is strictly below it). -/
def top (p : Sec2.Par) (t b0 : ℕ) : ℕ := aTR p b0 + trieCap p t + 1

/-! ## Where the areas lie -/

/-- What the routines of Section 4 need of the map: the tables that they read lie one behind the
other between the directory and WD, and the areas of Section 4 behind WD. -/
structure Areas (p : Sec2.Par) (t b0 : ℕ) : Prop where
  dir : b0 + 32 ≤ p.aMASK b0
  mask : p.aMASK b0 + p.KK * p.L = p.aBAND b0
  band : p.aBAND b0 + p.N = p.aBLOCK b0
  block : p.aBLOCK b0 + p.N = p.aDIG3 b0
  dig3 : p.aDIG3 b0 + p.N * p.Lo ≤ p.aENCA b0
  enca : p.aENCA b0 + p.nB * p.T = p.aENCB b0
  encb : p.aENCB b0 + p.nB * p.T ≤ aWD p b0
  cur : aCUR p b0 = aWD p b0 + p.L
  box : aBOX p b0 = aWD p b0 + 2 * p.L
  ss : aSS p b0 = aWD p b0 + 3 * p.L
  fp : aFP p b0 = aWD p b0 + 3 * p.L + p.m
  roots : aROOTS p b0 = aWD p b0 + 3 * p.L + p.m + 1
  tr : aTR p b0 = aROOTS p b0 + p.nB * p.nB
  top : top p t b0 = aTR p b0 + trieCap p t + 1

/-- The tables and the areas lie as Areas says. -/
theorem areas (p : Sec2.Par) (t b0 : ℕ) : Areas p t b0 := by
  have hplaces := p.places b0
  have hWD : aWD p b0 = p.sharedEnd b0 := rfl
  have hCUR : aCUR p b0 = aWD p b0 + p.L := rfl
  have hBOX : aBOX p b0 = aCUR p b0 + p.L := rfl
  have hSS : aSS p b0 = aBOX p b0 + p.L := rfl
  have hFP : aFP p b0 = aSS p b0 + p.m := rfl
  have hROOTS : aROOTS p b0 = aFP p b0 + 1 := rfl
  have hTR : aTR p b0 = aROOTS p b0 + p.nB * p.nB := rfl
  have hTOP : top p t b0 = aTR p b0 + trieCap p t + 1 := rfl
  constructor <;> omega

/-- The directory lies before the areas of Section 4. -/
theorem wd_ge (p : Sec2.Par) (b0 : ℕ) : b0 + 32 ≤ aWD p b0 := by
  obtain ⟨⟩ := areas p 0 b0
  omega

/-- The shared block ends behind its base address. -/
theorem base_le_sharedEnd (p : Sec2.Par) (b0 : ℕ) : b0 ≤ p.sharedEnd b0 :=
  (Nat.le_add_right b0 32).trans (wd_ge p b0)

/-- The block holds more than its directory. -/
theorem base_add_lt_top (p : Sec2.Par) (t b0 : ℕ) : b0 + 32 < top p t b0 := by
  obtain ⟨⟩ := areas p t b0
  omega

/-- The block is not empty. -/
theorem base_lt_top (p : Sec2.Par) (t b0 : ℕ) : b0 < top p t b0 :=
  (Nat.le_add_right b0 32).trans_lt (base_add_lt_top p t b0)

/-- The block ends behind its base address. -/
theorem base_le_top (p : Sec2.Par) (t b0 : ℕ) : b0 ≤ top p t b0 := (base_lt_top p t b0).le

/-- The scratch strings of a query lie in the block. -/
theorem scratch_in_block (p : Sec2.Par) (t b0 : ℕ) :
    b0 ≤ aWD p b0 ∧ aWD p b0 + (3 * p.L + p.m) ≤ top p t b0 := by
  obtain ⟨⟩ := areas p t b0
  omega

/-! ## The directory -/

namespace Dir

/-- The cells of the directory, the first 32 cells of the block, that the routines of Section 4 use.
They hold L, m, L - m, K₀, nB, 10^L, the addresses of the tables MASK, BAND, BLOCK, DIG3 and of the
encodings ENCA, ENCB, the end of the shared block (which is the address of WD), and t. All but the
last are written by the shared stage. -/
abbrev levels : ℕ := 0
@[inherit_doc levels] abbrev inner : ℕ := 1
@[inherit_doc levels] abbrev outer : ℕ := 4
@[inherit_doc levels] abbrev blocks : ℕ := 7
@[inherit_doc levels] abbrev bands : ℕ := 9
@[inherit_doc levels] abbrev leaves : ℕ := 10
@[inherit_doc levels] abbrev mask : ℕ := 21
@[inherit_doc levels] abbrev band : ℕ := 22
@[inherit_doc levels] abbrev block : ℕ := 23
@[inherit_doc levels] abbrev digits : ℕ := 24
@[inherit_doc levels] abbrev encA : ℕ := 26
@[inherit_doc levels] abbrev encB : ℕ := 27
@[inherit_doc levels] abbrev sharedEnd : ℕ := 30
@[inherit_doc levels] abbrev switch : ℕ := 31

end Dir

/-! ## The invariant -/

/-- The encoding of the row band β. -/
def encRow (p : Sec2.Par) (hmL : p.m ≤ p.L) (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ)
    (β : ℕ) : Leaf p.L → ℤ :=
  encodingL (bandArrayL (stdLayout hmL) X β)

/-- The encoding of the column band β. -/
def encCol (p : Sec2.Par) (hmL : p.m ≤ p.L) (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ)
    (β : ℕ) : Leaf p.L → ℤ :=
  encodingR (bandArrayR (stdLayout hmL) Y β)

/-- The tries of all tiles, and their roots. -/
def dsTries (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ)
    (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) :
    TrieStore :=
  allTries p.L p.m t (tileList p.nB (encRow p hmL X) (encCol p hmL Y))

/-- **The block from b0 on holds the data structure for X and Y.** The preprocessing establishes
this, and every query needs it and keeps it. -/
structure DSReady (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ)
    (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ)
    (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) (μ : ℕ → ℤ) : Prop where
  shared : Sec2.SharedReady p hmL aX aY b0 X Y μ
  cellT : μ (b0 + 31) = t
  roots : SegN μ (aROOTS p b0) (dsTries p t hmL X Y).roots
  trie : Seg μ (aTR p b0) (dsTries p t hmL X Y).cells

section

variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}

/-- The invariant depends only on the cells from b0 on, without the scratch strings WD, CUR, BOX,
SS. -/
theorem DSReady.congr (h : DSReady p t hmL aX aY b0 X Y μ)
    (he : ∀ a, b0 ≤ a → Outside (aWD p b0) (3 * p.L + p.m) a → μ' a = μ a) :
    DSReady p t hmL aX aY b0 X Y μ' := by
  have hend : p.sharedEnd b0 = aWD p b0 := rfl
  obtain ⟨⟩ := areas p t b0
  exact ⟨h.shared.congr fun a ha hlt _ => he a ha (by omega),
    by rw [he _ (by omega) (by omega)]; exact h.cellT,
    h.roots.congr fun i _ => he _ (by omega) (by omega),
    h.trie.congr fun i _ => he _ (by omega) (by omega)⟩

/-- A memory that differs from one that holds the data structure only on the scratch strings WD,
CUR, BOX, SS holds it too. -/
theorem DSReady.of_same (h : DSReady p t hmL aX aY b0 X Y μ)
    (hs : SameOutside μ μ' (aWD p b0) (3 * p.L + p.m)) : DSReady p t hmL aX aY b0 X Y μ' :=
  h.congr fun a _ ha => hs a ha

/-- The invariant of the data structure only depends on the cells from b0 on. -/
theorem dsReady_congr (h : DSReady p t hmL aX aY b0 X Y μ) (he : ∀ a, b0 ≤ a → μ' a = μ a) :
    DSReady p t hmL aX aY b0 X Y μ' :=
  h.congr fun a ha _ => he a ha

end

/-- The limits that the two routines need: U bounds the entries of X and Y. -/
structure Lim30 (lim : Limits) (p : Sec2.Par) (t b0 : ℕ) (U : ℤ) : Prop where
  std : Std lim
  space : top p t b0 ≤ lim.space
  /-- Every value and every partial sum fits in a word. -/
  value : 10 ^ p.m * ((7 ^ p.L * U) * (7 ^ p.L * U)) ≤ lim.word
  /-- The shared stage can compute the encodings. -/
  enc : 7 ^ (p.L + 1) * U ≤ lim.word
  /-- The shared stage can compute the table of the powers of 10. -/
  pow : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word

/-! ## The two routines that know the map -/

/-- The numbers of the two routines. -/
abbrev Proc.preCore : ℕ := 54
@[inherit_doc Proc.preCore] abbrev Proc.queryAt : ℕ := 55

/-- The time of `queryAt`. -/
def tQueryAt (L m t : ℕ) : ℕ := tOutDigits L + tQueryCore L m t + 400

/-- The time of `preCore`; c is the constant of the shared stage (`Sec2.SharedSpec`). -/
def tPreCore (c : ℕ) (p : Sec2.Par) (t : ℕ) : ℕ :=
  c * Sec2.sharedShape p + tAllTiles p.L p.m t p.nB + 300

/-- queryAt(I, J, b0) returns (XY)[I, J] from the block at b0, of which it changes only cells of the
scratch strings WD to SS. -/
def QueryAtSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ) (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ)
    (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) (U : ℤ) (μ : ℕ → ℤ) (I J : Fin p.N),
    t ≤ p.m → Lim30 lim p t b0 U → (∀ i j, |X i j| ≤ U) → (∀ i j, |Y i j| ≤ U) →
    DSReady p t hmL aX aY b0 X Y μ →
    ∀ d, d + 2 ≤ lim.depth →
    Meets lim P Proc.queryAt d [(I : ℕ), (J : ℕ), b0] μ (tQueryAt p.L p.m t) fun r μ' =>
      r = (X * Y) I J ∧ DSReady p t hmL aX aY b0 X Y μ' ∧
        SameOutside μ μ' (aWD p b0) (3 * p.L + p.m)

/-- preCore(L, m, t, N, D, aX, aY, b0) builds the data structure for the matrices at aX and aY in
the block from b0 on. Nothing is assumed about the content of the block. -/
def PreCoreSpec (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ) (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ)
    (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) (U : ℤ) (μ : ℕ → ℤ),
    t ≤ p.m → Lim30 lim p t b0 U → (∀ i j, |X i j| ≤ U) → (∀ i j, |Y i j| ≤ U) →
    MatAt μ aX X → MatAt μ aY Y → aX + p.N * p.D ≤ b0 → aY + p.D * p.N ≤ b0 →
    ∀ d, d + (p.L + 6) ≤ lim.depth →
    Meets lim P Proc.preCore d [p.L, p.m, t, p.N, p.D, aX, aY, b0] μ
      (tPreCore c p t) fun _ μ' =>
      DSReady p t hmL aX aY b0 X Y μ' ∧ SameOutside μ μ' b0 (top p t b0 - b0)

end Light.Sec4
