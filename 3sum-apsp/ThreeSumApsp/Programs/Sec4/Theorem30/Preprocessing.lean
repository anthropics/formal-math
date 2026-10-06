/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.Theorem30.Directory

/-!
# The preprocessing of Theorem 30, at a given place of the memory

Proof of Theorem 30, "Preprocessing". The routine first runs the stage that it shares with
Theorem 5: the list of the subsets, the tables for the rows and columns, and the encodings of all
row bands and column bands. It notes t in the directory, computes the addresses of the areas of
Section 4 (preCoreAddr), starts the trie area with the array [0], and computes the values of all the
boxes of all tiles, by Lemma 29 (preCoreFinish). There is one lemma for each of the two named parts;
preCore_spec puts them behind the shared stage.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The program -/

namespace PreCore

/-- The local variables of preCore: the arguments L, m, t, N, D, aX, aY, b0; a local for results
that are not used; the address of WD, the number nB, the addresses of CUR, BOX, FP, ROOTS, the
number m - t, and the address of TR. -/
abbrev Levels : ℕ := 0
@[inherit_doc Levels] abbrev Inner : ℕ := 1
@[inherit_doc Levels] abbrev Switch : ℕ := 2
@[inherit_doc Levels] abbrev Size : ℕ := 3
@[inherit_doc Levels] abbrev Width : ℕ := 4
@[inherit_doc Levels] abbrev MatX : ℕ := 5
@[inherit_doc Levels] abbrev MatY : ℕ := 6
@[inherit_doc Levels] abbrev Base : ℕ := 7
@[inherit_doc Levels] abbrev Void : ℕ := 8
@[inherit_doc Levels] abbrev Digits : ℕ := 9
@[inherit_doc Levels] abbrev Bands : ℕ := 10
@[inherit_doc Levels] abbrev Cur : ℕ := 11
@[inherit_doc Levels] abbrev Box : ℕ := 12
@[inherit_doc Levels] abbrev Free : ℕ := 13
@[inherit_doc Levels] abbrev Roots : ℕ := 14
@[inherit_doc Levels] abbrev Last : ℕ := 15
@[inherit_doc Levels] abbrev Tries : ℕ := 16

end PreCore

open PreCore in
/-- The addresses of the areas of Section 4, which lie one behind the other from WD on. -/
def preCoreAddr : Stmt :=
  .set Digits (M (v Base +' k Dir.sharedEnd)) ;;
  .set Bands (M (v Base +' k Dir.bands)) ;;
  .set Cur (v Digits +' v Levels) ;;
  .set Box (v Cur +' v Levels) ;;
  .set Free (v Box +' v Levels +' v Inner) ;;
  .set Roots (v Free +' k 1) ;;
  .set Last (v Inner -' v Switch) ;;
  .set Tries (v Roots +' v Bands *' v Bands)

open PreCore in
/-- The trie array starts as [0], of length 1; then the tries of all tiles. -/
def preCoreFinish : Stmt :=
  .store (v Tries) (k 0) ;;
  .store (v Free) (k 1) ;;
  .call Proc.allTiles [M (v Base +' k Dir.encA), M (v Base +' k Dir.encB), v Bands,
    M (v Base +' k Dir.leaves), v Roots, v Tries, v Free, v Cur, v Box, v Levels, v Last] Void

open PreCore in
/-- preCore(L, m, t, N, D, aX, aY, b0) builds the data structure for the matrices at aX and aY in
the block from b0 on. -/
def preCoreBody : Stmt :=
  .call Sec2.pShared [v Levels, v Inner, v Size, v Width, v MatX, v MatY, v Base] Void ;;
  .store (v Base +' k Dir.switch) (v Switch) ;;
  preCoreAddr ;;
  preCoreFinish

/-- What the locals hold after the shared stage; r is its result. -/
def preShared (p : Sec2.Par) (t aX aY b0 : ℕ) (r : ℤ) : List ℤ :=
  [p.L, p.m, t, p.N, p.D, aX, aY, b0, r]

/-- What the locals hold after the addresses have been computed. -/
def preLocals (p : Sec2.Par) (t aX aY b0 : ℕ) (r : ℤ) : List ℤ :=
  preShared p t aX aY b0 r ++ [(aWD p b0 : ℤ), p.nB, aCUR p b0, aBOX p b0, aFP p b0, aROOTS p b0,
    (p.m - t : ℕ), aTR p b0]

variable {lim : Limits} {P : Program} {d : ℕ} {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L}
  {aX aY b0 : ℕ} {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {U : ℤ} {μ : ℕ → ℤ}

/-! ## The addresses -/

/-- The addresses of the areas of Section 4 are computed as the map says. -/
theorem preCoreAddr_spec (ht : t ≤ p.m) (hlim : Lim30 lim p t b0 U)
    (hSR : Sec2.SharedReady p hmL aX aY b0 X Y μ) (r : ℤ) :
    Ends lim P d preCoreAddr ⟨frame (preShared p t aX aY b0 r), μ⟩ 38
      (· = ⟨frame (preLocals p t aX aY b0 r), μ⟩) := by
  have dir := hSR.dirCells
  light_facts hlim hlim.std
  obtain ⟨⟩ := areas p t b0
  unfold preLocals preShared
  -- the product nB², in the integers
  have hsq : ((p.nB * p.nB : ℕ) : ℤ) ≤ lim.space := by
    exact_mod_cast (by omega : p.nB * p.nB ≤ lim.space)
  have htr : ((aROOTS p b0 + p.nB * p.nB : ℕ) : ℤ) = aTR p b0 := by
    exact_mod_cast (by omega : aROOTS p b0 + p.nB * p.nB = aTR p b0)
  have hsq0 : (0 : ℤ) ≤ (p.nB : ℤ) * p.nB := by positivity
  push_cast at hsq htr
  -- digits := dir[30]; bands := dir[9]
  light_set (aWD p b0 : ℕ) using dir.sharedEnd
  light_set (p.nB : ℕ) using dir.bands
  -- cur := digits + L; box := cur + L; free := box + L + m; roots := free + 1
  light_set (aCUR p b0 : ℕ)
  light_set (aBOX p b0 : ℕ)
  light_set (aFP p b0 : ℕ)
  light_set (aROOTS p b0 : ℕ)
  -- last := m - t; tries := roots + nB nB
  light_set (p.m - t : ℕ)
  light_set (aTR p b0 : ℕ)
  rfl

/-! ## The tries -/

/-- The arguments of the call of allTiles, and the data behind them. -/
def allArgs (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (b0 : ℕ)
    (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ) (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) :
    AllTilesArgs where
  L := p.L
  m := p.m
  t := t
  nB := p.nB
  encA := encRow p hmL X
  encB := encCol p hmL Y
  aENCA := p.aENCA b0
  aENCB := p.aENCB b0
  aR := aROOTS p b0
  tr := aTR p b0
  cap := trieCap p t
  fp := aFP p b0
  cur := aCUR p b0
  box := aBOX p b0

/-- The block, after the shared stage and with the trie array [0], holds what allTiles assumes. -/
theorem allArgs_pre (h : Lim30 lim p t b0 U) (ht : t ≤ p.m) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (hSR : Sec2.SharedReady p hmL aX aY b0 X Y μ)
    (hTM : TrieMem μ (aTR p b0) (trieCap p t) (aFP p b0) [0]) :
    AllTilesPre lim μ (allArgs p t hmL b0 X Y) := by
  -- a negative bound U is possible only if there are no entries; then 0 is a bound as well
  obtain ⟨U', hU0, hX', hY', hvalue⟩ : ∃ U' : ℤ, 0 ≤ U' ∧ (∀ i j, |X i j| ≤ U') ∧
      (∀ i j, |Y i j| ≤ U') ∧ 10 ^ p.m * ((7 ^ p.L * U') * (7 ^ p.L * U')) ≤ lim.word := by
    rcases le_or_gt 0 U with h0 | h0
    · exact ⟨U, h0, hX, hY, h.value⟩
    · have hword : (0 : ℤ) ≤ lim.word := le_trans (by norm_num) h.std.const_le
      exact ⟨0, le_rfl, fun i j => absurd ((abs_nonneg _).trans (hX i j)) (not_le.mpr h0),
        fun i j => absurd ((abs_nonneg _).trans (hY i j)) (not_le.mpr h0), by simpa using hword⟩
  have hsp := h.space
  have hT : 10 ^ p.L = p.T := rfl
  obtain ⟨⟩ := areas p t b0
  exact
    { std := h.std
      t_le := ht
      m_le := hmL
      value_le := ⟨7 ^ p.L * U', 7 ^ p.L * U',
        fun β τ => (abs_enc_le hmL X Y U' hU0 hX' hY' β β).1 τ,
        fun β τ => (abs_enc_le hmL X Y U' hU0 hX' hY' β β).2 τ, hvalue⟩
      pow_le := h.pow_le
      cap_ge := le_rfl
      order := by simp only [allArgs]; rw [hT]; omega
      segA := fun β hβ => hSR.encA β hβ
      segB := fun β hβ => hSR.encB β hβ
      trie := hTM }

/-- The trie area with the array [0], after the two stores. -/
theorem trieMem_start (p : Sec2.Par) (t b0 : ℕ) (μ : ℕ → ℤ) :
    TrieMem (Function.update (Function.update μ (aTR p b0) 0) (aFP p b0) 1) (aTR p b0)
      (trieCap p t) (aFP p b0) [0] := by
  obtain ⟨⟩ := areas p t b0
  refine ⟨fun i hi => ?_, Function.update_self .., by simp [trieCap], Or.inl (by omega)⟩
  obtain rfl : i = 0 := by simpa using hi
  rw [Nat.add_zero, Function.update_of_ne (by omega), Function.update_self]
  rfl

/-- After the shared stage, the last part completes the data structure; it changes only cells from
CUR to the end of the block. -/
theorem preCoreFinish_spec (hAll : AllTilesSpec lim P) (hlim : Lim30 lim p t b0 U) (ht : t ≤ p.m)
    (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U) (hd : d + 5 ≤ lim.depth) (r : ℤ)
    (hSR : Sec2.SharedReady p hmL aX aY b0 X Y μ) (hcellT : μ (b0 + 31) = t) :
    Ends lim P d preCoreFinish ⟨frame (preLocals p t aX aY b0 r), μ⟩
      (tAllTiles p.L p.m t p.nB + 28) fun σ' =>
      DSReady p t hmL aX aY b0 X Y σ'.mem ∧
        SameOutside μ σ'.mem (aCUR p b0) (top p t b0 - aCUR p b0) := by
  light_facts hlim hlim.std
  have hend : p.sharedEnd b0 = aWD p b0 := rfl
  obtain ⟨⟩ := areas p t b0
  unfold preLocals preShared
  -- TR[0] := 0; FP := 1
  light_store (aTR p b0) 0
  light_store (aFP p b0) 1
  have hTM := trieMem_start p t b0 μ
  have same : SameOutside μ (Function.update (Function.update μ (aTR p b0) 0) (aFP p b0) 1)
      (aCUR p b0) (top p t b0 - aCUR p b0) :=
    (SameOutside.refl.update (by omega) 0).update (by omega) 1
  generalize Function.update (Function.update μ (aTR p b0) 0) (aFP p b0) 1 = μ₁ at *
  have hSR₁ : Sec2.SharedReady p hmL aX aY b0 X Y μ₁ :=
    hSR.of_agree fun b hb _ => same b (Or.inl (by omega))
  have dir := hSR₁.dirCells
  -- the tries of all tiles
  light_call (hAll _ μ₁ (allArgs_pre hlim ht hX hY hSR₁ hTM))
    using allArgs, dir.encA, dir.encB, dir.leaves, Sec2.Par.T with r' μ₂ ⟨hTM₂, hroots, same₂⟩
  have same' : SameOutside μ μ₂ (aCUR p b0) (top p t b0 - aCUR p b0) :=
    same.then same₂ fun b hb =>
      ⟨hb, by change b < aCUR p b0 ∨ aTR p b0 + trieCap p t ≤ b; omega⟩
  exact ⟨⟨hSR.of_agree fun b hb _ => same' b (Or.inl (by omega)),
    (same' _ (Or.inl (by omega))).trans hcellT, hroots, hTM₂.seg⟩, same'⟩

/-! ## The routine -/

/-- **preCore** meets its specification. -/
theorem preCore_spec {c : ℕ} (hP : P[Proc.preCore]? = some preCoreBody)
    (hShared : Sec2.SharedSpec lim P c) (hAll : AllTilesSpec lim P) : PreCoreSpec lim P c := by
  intro p t hmL aX aY b0 X Y U μ ht hlim hX hY hMX hMY haX haY
  refine fun d hd => ⟨preCoreBody, hP, ?_⟩
  light_facts hlim hlim.std
  have hend : p.sharedEnd b0 = aWD p b0 := rfl
  obtain ⟨⟩ := areas p t b0
  unfold tPreCore
  -- the shared stage
  light_call (hShared p hmL aX aY b0 μ X Y U
    { space := by omega, matX := hMX, matY := hMY, belowX := haX, belowY := haY, absX := hX
      absY := hY, seven := hlim.enc, ten := hlim.pow }) with r μ₁ ⟨hSR₁, same₁⟩
  -- dir[31] := t
  light_store (b0 + 31) t
  have hSR₂ : Sec2.SharedReady p hmL aX aY b0 X Y (Function.update μ₁ (b0 + 31) t) :=
    hSR₁.of_agree fun b _ hb => Function.update_of_ne hb ..
  -- the addresses
  light_piece (preCoreAddr_spec ht hlim hSR₂ r) with _ rfl
  -- the tries
  refine (preCoreFinish_spec hAll hlim ht hX hY (by omega) r hSR₂ (Function.update_self ..)).mono
    (by simp; omega) ?_
  rintro σ' ⟨hDS, same₂⟩
  refine ⟨hDS, fun b hb => ?_⟩
  rw [same₂ b (by omega), Function.update_of_ne (by omega), same₁ b (by omega)]

end Light.Sec4
