/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec5.Corollary40.DataStructure
public import ThreeSumApsp.Programs.Sec5.Corollary40.Gather
public import ThreeSumApsp.Programs.Sec5.Corollary40.PhaseLayout

/-!
# uMv-hinted uMv: the routines of Phases 3 and 4

Proof of Corollary 40.  Phase 3 writes Y := N_{I,J} and builds, for blocks of t₂
consecutive rows of U, the data structure for the product of the block with Y.  Phase 4 asks it for
the entries (i, ℓ) of U N_{I,J} with V[ℓ, j] = 1.

The blocks are aligned at the end: block number k has the rows from n - (k + 1) t₂ on, and the last
block starts at row 0, so that it may overlap the one before.  So every block is a contiguous piece
of U, and nothing is copied or padded.  The structure of the block with the first row s lies at
base + s Sz, where Sz is an upper bound on the number of cells of a structure.  The blocks are
handled in the order of decreasing first rows, so that a new structure lies below all earlier ones.
A table tells for every row the first row of its block.

* gather(n, t₁, t₂, aN, aI, aJ, aY) writes N_{I,J} (`gather_meets`).
* blocks(n, t₁, t₂, aY, aS, base, Sz) builds the structures and the table (`blocks_meets`).
* scan(off, j, t₂, t₁, aX, aY, fr, aV, n): off is a row, counted from the first row of its block;
  aX, aY, fr are the addresses of the block, of Y and of the structure of the block.  It returns 1
  if for some ℓ < t₂ both V[ℓ, j] = 1 and the entry (off, ℓ) of the product of the block with Y is
  not 0, and 0 if not (`scan_meets`).
-/

@[expose] public section

namespace Light.Sec5

open ThreeSumApsp ThreeSumApsp.Spec.Sec5 Light.Sec4

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Writing a submatrix -/

namespace Gather

/-- The locals of gather(n, t₁, t₂, aN, aI, aJ, aY).  The arguments: the size n of N, the numbers t₁
of rows and t₂ of columns of the submatrix, the addresses of N, I, J and of the submatrix Y.  Then
the row a and the column b, and the addresses of row I_a of N and of row a of Y. -/
abbrev Size : ℕ := 0
@[inherit_doc Size] abbrev Rows : ℕ := 1
@[inherit_doc Size] abbrev Cols : ℕ := 2
@[inherit_doc Size] abbrev AddrN : ℕ := 3
@[inherit_doc Size] abbrev AddrI : ℕ := 4
@[inherit_doc Size] abbrev AddrJ : ℕ := 5
@[inherit_doc Size] abbrev AddrY : ℕ := 6
@[inherit_doc Size] abbrev Row : ℕ := 7
@[inherit_doc Size] abbrev Col : ℕ := 8
@[inherit_doc Size] abbrev RowN : ℕ := 9
@[inherit_doc Size] abbrev Dst : ℕ := 10

end Gather

open Gather in
/-- gather(n, t₁, t₂, aN, aI, aJ, aY): for a < t₁, b < t₂: Y[a, b] := N[I_a, J_b]. -/
def gatherBody : Stmt :=
  .for Row (v Rows) (
    .set RowN (v AddrN +' M (v AddrI +' v Row) *' v Size) ;;
    .set Dst (v AddrY +' v Row *' v Cols) ;;
    pick Col Cols Dst RowN AddrJ)

/-- The time of gather: t₁ rows of t₂ entries. -/
def tGather (t₁ t₂ : ℕ) : ℕ := t₁ * (19 * t₂ + 29) + 6

open Gather in
/-- **gather** writes the submatrix N_{I,J} and changes nothing else. -/
theorem gather_meets {p : ℕ} (hp : P[p]? = some gatherBody) {μ : ℕ → ℤ}
    {n t₁ t₂ aN aI aJ aY : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} {I : Fin t₁ → Fin n}
    {J : Fin t₂ → Fin n} (hw : (lim.space : ℤ) ≤ lim.word) (mN : MatAt μ aN A)
    (vI : VecAt μ aI I) (vJ : VecAt μ aJ J) (hNY : aN + n * n ≤ aY) (hIY : aI + t₁ ≤ aY)
    (hJY : aJ + t₂ ≤ aY) (hsp : aY + t₁ * t₂ < lim.space) :
    Meets lim P p d [(n : ℤ), t₁, t₂, aN, aI, aJ, aY] μ (tGather t₁ t₂) fun _ μ' =>
      MatAt μ' aY (A.submatrix I J) ∧ SameOutside μ μ' aY (t₁ * t₂) := by
  refine .of_body hp ?_
  unfold gatherBody tGather
  -- for a < t₁: the rows below a are written
  refine Ends.forScratch [RowN, Dst, Col] (RowsWritten μ aY (A.submatrix I J)) t₁ (19 * t₂ + 21)
    .zero (fun a _ μ' ha hrows => ?_) fun _ _ h => ⟨h.matAt, h.same⟩
  have hsame := hrows.same
  have hat : a * t₂ + t₂ ≤ t₁ * t₂ := Nat.mul_add_le_mul ha le_rfl
  have hIn : (I ⟨a, ha⟩ : ℕ) * n + n ≤ n * n := Nat.mul_add_le_mul (I ⟨a, ha⟩).isLt le_rfl
  have hI : μ' (aI + a) = (I ⟨a, ha⟩ : ℕ) := (hsame _ (.inl (by omega))).trans (vI ⟨a, ha⟩)
  -- the addresses of row I_a of N and of row a of Y
  light_set (aN + (I ⟨a, ha⟩ : ℕ) * n : ℕ) using hI
  light_set (aY + a * t₂ : ℕ)
  -- for b < t₂: Y[a, b] := N[I_a, J_b]
  refine Ends.pick (aRow := aN + (I ⟨a, ha⟩ : ℕ) * n) (rowFn (A.submatrix I J) a) vJ.keep
    (fun b => ?_) (by omega) (by omega) (by omega) hw (hrows.succ ha)
  have := (J b).isLt
  rw [hsame _ (.inl (by omega)), rowFn_eq _ ha]
  exact mN (I ⟨a, ha⟩) (J b)

/-! ## The blocks -/

namespace Blocks

/-- The locals of blocks(n, t₁, t₂, aY, aS, base, Sz).  The arguments: the sizes n, t₁, t₂, the
addresses of Y, of the table and of the structures, and the distance of the structures.  Then the
first row of the block before (n at the beginning), the first row s of the block, a counter, a
result that is not used, and the number and the address of the cells of the table that belong to the
block. -/
abbrev Size : ℕ := 0
@[inherit_doc Size] abbrev Inner : ℕ := 1
@[inherit_doc Size] abbrev Height : ℕ := 2
@[inherit_doc Size] abbrev AddrY : ℕ := 3
@[inherit_doc Size] abbrev Table : ℕ := 4
@[inherit_doc Size] abbrev Base : ℕ := 5
@[inherit_doc Size] abbrev Dist : ℕ := 6
@[inherit_doc Size] abbrev Prev : ℕ := 7
@[inherit_doc Size] abbrev First : ℕ := 8
@[inherit_doc Size] abbrev Row : ℕ := 9
@[inherit_doc Size] abbrev Result : ℕ := 10
@[inherit_doc Size] abbrev Len : ℕ := 11
@[inherit_doc Size] abbrev Dst : ℕ := 12

end Blocks

open Blocks in
/-- The block with the first row s: build its structure, and write s into the cells s, …, prev - 1
of the table. -/
def blocksBuild : Stmt :=
  .call Proc.pre31 [v Height, v Inner, k 3 +' v First *' v Inner, v AddrY,
    v Base +' v First *' v Dist] Result ;;
  .set Len (v Prev -' v First) ;;
  .set Dst (v Table +' v First) ;;
  pass Row (v Len) (v Dst) (v First) ;;
  .set Prev (v First)

open Blocks in
/-- blocks(n, t₁, t₂, aY, aS, base, Sz): the blocks in the order of decreasing first rows. -/
def blocksBody : Stmt :=
  .set Prev (v Size) ;;
  .while (k 0 <' v Prev) (
    .ite (v Prev <' v Height) (.set First (k 0)) (.set First (v Prev -' v Height)) ;;
    blocksBuild)

/-- The structure of the block with the first row s is ready. -/
def BlockReady (K : DsKit P) {n t₁ t₂ : ℕ} (Um : Matrix (Fin n) (Fin t₁) ℤ)
    (Y : Matrix (Fin t₁) (Fin t₂) ℤ) (aY base Sz s : ℕ) (μ : ℕ → ℤ) : Prop :=
  ∃ h : s + t₂ ≤ n, K.Ready (rowsFrom Um s t₂ h) Y (3 + s * t₁) aY (base + s * Sz) μ

/-- The structure of a block stays ready if neither U, nor Y, nor the cells from its address on
change. -/
theorem BlockReady.keep {K : DsKit P} {n t₁ t₂ : ℕ} {Um : Matrix (Fin n) (Fin t₁) ℤ}
    {Y : Matrix (Fin t₁) (Fin t₂) ℤ} {aY base Sz s : ℕ} {μ μ' : ℕ → ℤ}
    (h : BlockReady K Um Y aY base Sz s μ)
    (hs : SameOn (fun b => b < 3 + n * t₁ ∨ Inside aY (t₁ * t₂) b ∨ base + s * Sz ≤ b) μ μ' := by
      light_keep) :
    BlockReady K Um Y aY base Sz s μ' := by
  obtain ⟨hrows, hR⟩ := h
  have hle : s * t₁ + t₂ * t₁ ≤ n * t₁ := (Nat.add_mul _ _ _).symm.trans_le
    (Nat.mul_le_mul_right _ hrows)
  exact ⟨hrows, hR.keep⟩

/-- The rows from lo on are served: the table has the first row s ≥ lo of a block that contains the
row, and the structure of this block is ready. -/
def Served (K : DsKit P) {n t₁ t₂ : ℕ} (Um : Matrix (Fin n) (Fin t₁) ℤ)
    (Y : Matrix (Fin t₁) (Fin t₂) ℤ) (aY aS base Sz lo : ℕ) (μ : ℕ → ℤ) : Prop :=
  ∀ i, lo ≤ i → i < n → ∃ s : ℕ, μ (aS + i) = s ∧ s ≤ i ∧ i < s + t₂ ∧ lo ≤ s ∧
    BlockReady K Um Y aY base Sz s μ

/-- The time of blocks: ⌈n / t₂⌉ rounds, each with one preprocessing and at most t₂ entries of the
table. -/
def tBlocks (K : DsKit P) (n t₁ t₂ : ℕ) : ℕ :=
  ((n + t₂ - 1) / t₂) * (K.tPre t₂ t₁ + 13 * t₂ + 50) + 8

/-- What blocks asks of its arguments and of the memory: 1 ≤ t₁ and 1 ≤ t₂ ≤ n; U lies at 3 and Y at
aY, with entries of absolute value at most 1; then follow the table and the structures, which are Sz
cells apart and have at most Sz cells each; the limits suffice for all of them. -/
structure BlocksPre (K : DsKit P) (lim : Limits) {n t₁ t₂ : ℕ} (Um : Matrix (Fin n) (Fin t₁) ℤ)
    (Y : Matrix (Fin t₁) (Fin t₂) ℤ) (aY aS base Sz : ℕ) (μ : ℕ → ℤ) : Prop where
  inner_pos : 1 ≤ t₁
  height_pos : 1 ≤ t₂
  height_le : t₂ ≤ n
  size_le : K.size t₂ t₁ ≤ Sz
  matU : MatAt μ 3 Um
  matY : MatAt μ aY Y
  absU : ∀ a b, |Um a b| ≤ 1
  absY : ∀ a b, |Y a b| ≤ 1
  belowY : 3 + n * t₁ ≤ aY
  belowTable : aY + t₁ * t₂ ≤ aS
  belowBase : aS + n ≤ base
  lims : ∀ s, s + t₂ ≤ n → K.Lim lim t₂ t₁ (base + s * Sz) 1
  space : base + n * Sz < lim.space

section blocks

variable {K : DsKit P} {n t₁ t₂ aY aS base Sz : ℕ} {Um : Matrix (Fin n) (Fin t₁) ℤ}
  {Y : Matrix (Fin t₁) (Fin t₂) ℤ} {μ : ℕ → ℤ}

/-- What the routines of the kit are given for the block with the first row s. -/
theorem BlocksPre.input (h : BlocksPre K lim Um Y aY aS base Sz μ) {s : ℕ} (hs : s + t₂ ≤ n) :
    K.Input lim (rowsFrom Um s t₂ hs) Y (3 + s * t₁) aY (base + s * Sz) 1 := by
  light_facts h
  have hst : s * t₁ + t₂ * t₁ ≤ n * t₁ := (Nat.add_mul _ _ _).symm.trans_le
    (Nat.mul_le_mul_right _ hs)
  exact { one_le_D := h.inner_pos, one_le_N := h.height_pos, lim := h.lims s hs
          absX := abs_rowsFrom_le h.absU s t₂ hs, absY := h.absY
          belowX := by omega, belowY := by omega }

/-- **What a round does to the memory.**  The rows from prev on are served.  The structure of the
block with the first row s is built below the earlier ones, and s is written into the cells
s, …, prev - 1 of the table.  Then the rows from s on are served. -/
theorem Served.step {μ₁ μ₂ : ℕ → ℤ} {s prev : ℕ} (h : Served K Um Y aY aS base Sz prev μ₁)
    (hsize : K.size t₂ t₁ ≤ Sz) (hUY : 3 + n * t₁ ≤ aY) (hYS : aY + t₁ * t₂ ≤ aS)
    (hSB : aS + n ≤ base) (hs : s + t₂ ≤ n) (hsp : s < prev) (hps : prev ≤ s + t₂)
    (hready : K.Ready (rowsFrom Um s t₂ hs) Y (3 + s * t₁) aY (base + s * Sz) μ₂)
    (hsame : SameOutside μ₁ μ₂ (base + s * Sz) (K.size t₂ t₁)) :
    Served K Um Y aY aS base Sz s (wrote μ₂ (aS + s) (fun _ => s) (prev - s)) := by
  intro i hlo hin
  by_cases hip : i < prev
  · -- a row of the new block
    refine ⟨s, ?_, hlo, by omega, le_rfl, BlockReady.keep (μ := μ₂) ⟨hs, hready⟩⟩
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hlo
    rw [← Nat.add_assoc]
    exact wrote_done (by omega)
  · -- a row of an earlier block, whose structure lies above the new one
    obtain ⟨s', htab, hle, hlt, hprev, hblock⟩ := h i (by omega) hin
    have habove : s * Sz + Sz ≤ s' * Sz := Nat.mul_add_le_mul (show s < s' by omega) le_rfl
    exact ⟨s', Eq.trans (by light_keep) htab, hle, hlt, by omega, hblock.keep⟩

open Blocks in
/-- The state before round c of blocks: the first row of the block before is n - c t₂, the rows from
there on are served, and no cell below the table has changed. -/
structure BlocksInv (K : DsKit P) (Um : Matrix (Fin n) (Fin t₁) ℤ) (Y : Matrix (Fin t₁) (Fin t₂) ℤ)
    (aY aS base Sz : ℕ) (μ : ℕ → ℤ) (c : ℕ) (σ : State) : Prop where
  locals : LocalsBut [First, Row, Result, Len, Dst]
    [(n : ℤ), t₁, t₂, aY, aS, base, Sz, (n - c * t₂ : ℕ)] σ.loc
  served : Served K Um Y aY aS base Sz (n - c * t₂) σ.mem
  kept : Kept μ σ.mem aS

open Blocks in
/-- **One block.**  The first row n - (c + 1) t₂ of the block has been computed.  The structure of
the block is built, and its first row is written into the table for the rows that it serves. -/
theorem blocksBuild_spec {loc μ₁ : ℕ → ℤ} {c : ℕ} (hpre : BlocksPre K lim Um Y aY aS base Sz μ)
    (hd : d + 1 + K.depPre t₁ ≤ lim.depth) (hc : c * t₂ < n)
    (hloc : LocalsBut [Row, Result, Len, Dst]
      [(n : ℤ), t₁, t₂, aY, aS, base, Sz, (n - c * t₂ : ℕ), (n - (c + 1) * t₂ : ℕ)] loc)
    (hserved : Served K Um Y aY aS base Sz (n - c * t₂) μ₁) (hkept : Kept μ μ₁ aS) :
    Ends lim P d blocksBuild ⟨loc, μ₁⟩ (K.tPre t₂ t₁ + 13 * t₂ + 31)
      (BlocksInv K Um Y aY aS base Sz μ (c + 1)) := by
  light_facts hpre
  obtain ⟨hw, h100, -, -⟩ := K.basics (hpre.lims 0 (by omega))
  have hsucc : (c + 1) * t₂ = c * t₂ + t₂ := Nat.succ_mul _ _
  generalize hprev : n - c * t₂ = prev at *
  generalize hs : n - (c + 1) * t₂ = s at *
  have hs2 : s + t₂ ≤ n := by omega
  have hst : s * t₁ ≤ n * t₁ := Nat.mul_le_mul_right _ (by omega)
  have hsSz : s * Sz + Sz ≤ n * Sz := Nat.mul_add_le_mul (show s < n by omega) le_rfl
  rw [hloc.eq_frame]
  unfold blocksBuild
  -- pre(t₂, t₁, 3 + s t₁, aY, base + s Sz)
  light_call (K.pre (hpre.input hs2) (matAt_rowsFrom hpre.matU.keep s t₂ hs2) hpre.matY.keep _
    (by omega)) with r μ₂ ⟨hready, hsame⟩
  light_set (prev - s : ℕ)
  light_set (aS + s : ℕ)
  -- for r < prev - s: table[s + r] := s
  refine Ends.next _ (Ends.pass (dst := aS + s) (n := prev - s) (fun _ => s) (fun _ _ => by simp)
    ?_ hw (by omega) rfl rfl (hT := le_rfl))
  rw [update_frame_setLocal]
  -- prev := s
  have hkept₂ : Kept μ (wrote μ₂ (aS + s) (fun _ => (s : ℤ)) (prev - s)) aS := by light_keep
  light_set s
  subst hs
  exact ⟨LocalsBut.of_eq (by simp), hserved.step hpre.size_le hpre.belowY hpre.belowTable
    hpre.belowBase hs2 (by omega) (by omega) hready hsame, hkept₂⟩

open Blocks in
/-- **blocks** builds the structures of the blocks and the table of their first rows.  It changes no
cell below the table. -/
theorem blocks_meets {p : ℕ} (hp : P[p]? = some blocksBody)
    (hpre : BlocksPre K lim Um Y aY aS base Sz μ) (hd : d + 1 + K.depPre t₁ ≤ lim.depth) :
    Meets lim P p d [(n : ℤ), t₁, t₂, aY, aS, base, Sz] μ (tBlocks K n t₁ t₂) fun _ μ' =>
      (∀ i < n, ∃ s : ℕ, μ' (aS + i) = s ∧ s ≤ i ∧ i < s + t₂ ∧
        BlockReady K Um Y aY base Sz s μ') ∧ Kept μ μ' aS := by
  light_facts hpre
  obtain ⟨hw, h100, -, -⟩ := K.basics (hpre.lims 0 (by omega))
  refine .of_body hp ?_
  unfold blocksBody tBlocks
  light_set n
  -- while 0 < prev: ⌈n / t₂⌉ rounds
  refine Ends.whileConst (BlocksInv K Um Y aY aS base Sz μ) ((n + t₂ - 1) / t₂)
    (K.tPre t₂ t₁ + 13 * t₂ + 46) ?start ?round ?done (by light_time)
  case start =>
    exact ⟨fun _ _ => by simp, fun i hlo hin => absurd hin (by omega), .refl⟩
  case done =>
    rintro ⟨loc, μ'⟩ ⟨hloc, hserved, hkept⟩
    have hzero : n - (n + t₂ - 1) / t₂ * t₂ = 0 :=
      Nat.sub_eq_zero_of_le (Nat.le_ceilDiv_mul (by omega))
    rw [hzero] at hloc hserved
    rw [LocalsBut.eq_frame (loc := loc) hloc]
    refine ⟨by light_side, by simp, fun i hi => ?_, hkept⟩
    obtain ⟨s, htab, hle, hlt, -, hblock⟩ := hserved i (Nat.zero_le _) hi
    exact ⟨s, htab, hle, hlt, hblock⟩
  case round =>
    rintro c ⟨loc, μ'⟩ hc ⟨hloc, hserved, hkept⟩
    have hct : c * t₂ < n := (Nat.lt_ceilDiv_iff (by omega)).1 hc
    have hsucc : (c + 1) * t₂ = c * t₂ + t₂ := Nat.succ_mul _ _
    have hbuild {loc' : ℕ → ℤ} hloc' :=
      blocksBuild_spec (loc := loc') hpre hd hct hloc' hserved hkept
    rw [LocalsBut.eq_frame (loc := loc) hloc]
    refine ⟨by light_side, by light_side, ?_⟩
    -- s := max (prev - t₂) 0
    light_if hlt hge : n - c * t₂ < t₂
    · light_set (n - (c + 1) * t₂ : ℕ)
      light_piece (hbuild (LocalsBut.of_eq (by simp)))
    · light_set (n - (c + 1) * t₂ : ℕ)
      light_piece (hbuild (LocalsBut.of_eq (by simp)))

end blocks

/-! ## The queries of Phase 4 -/

/-- Some ℓ below l is a hit. -/
def HitBelow {t : ℕ} (hit : Fin t → Prop) (l : ℕ) : Prop := ∃ l' : Fin t, l'.val < l ∧ hit l'

/-- There is no hit below 0. -/
theorem not_hitBelow_zero {t : ℕ} (hit : Fin t → Prop) : ¬ HitBelow hit 0 :=
  fun ⟨_, h, _⟩ => absurd h (Nat.not_lt_zero _)

/-- A hit below l + 1 is a hit below l or a hit at l. -/
theorem hitBelow_succ {t l : ℕ} (hit : Fin t → Prop) (hl : l < t) :
    HitBelow hit (l + 1) ↔ HitBelow hit l ∨ hit ⟨l, hl⟩ := by
  constructor
  · rintro ⟨l', hlt, h⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
    · exact .inl ⟨l', hlt, h⟩
    · obtain rfl : l' = ⟨l, hl⟩ := Fin.ext heq
      exact .inr h
  · rintro (⟨l', hlt, h⟩ | h)
    · exact ⟨l', by omega, h⟩
    · exact ⟨⟨l, hl⟩, Nat.lt_succ_self l, h⟩

/-- A hit below t is any hit. -/
theorem hitBelow_all {t : ℕ} (hit : Fin t → Prop) : HitBelow hit t ↔ ∃ l, hit l :=
  ⟨fun ⟨l, _, h⟩ => ⟨l, h⟩, fun ⟨l, h⟩ => ⟨l, l.isLt, h⟩⟩

namespace Scan

/-- The locals of scan(off, j, t₂, t₁, aX, aY, fr, aV, n).  The arguments: the row off of the block
(this local also takes the result), the column j, the sizes t₂ and t₁, the addresses of the block,
of Y, of the structure and of V, and the size n.  Then ℓ, the result so far, and the answer to a
query. -/
abbrev RowOff : ℕ := 0
@[inherit_doc RowOff] abbrev Column : ℕ := 1
@[inherit_doc RowOff] abbrev Height : ℕ := 2
@[inherit_doc RowOff] abbrev Inner : ℕ := 3
@[inherit_doc RowOff] abbrev AddrX : ℕ := 4
@[inherit_doc RowOff] abbrev AddrY : ℕ := 5
@[inherit_doc RowOff] abbrev Free : ℕ := 6
@[inherit_doc RowOff] abbrev AddrV : ℕ := 7
@[inherit_doc RowOff] abbrev Size : ℕ := 8
@[inherit_doc RowOff] abbrev Ell : ℕ := 9
@[inherit_doc RowOff] abbrev Found : ℕ := 10
@[inherit_doc RowOff] abbrev Entry : ℕ := 11

end Scan

open Scan in
/-- One ℓ: if V[ℓ, j] = 1 and the entry (off, ℓ) of the product is not 0, then the result is 1. -/
def scanStep : Stmt :=
  .ite (M (v AddrV +' v Ell *' v Size +' v Column) =' k 1)
    (.call Proc.query31 [v RowOff, v Ell, v Height, v Inner, v AddrX, v AddrY, v Free] Entry ;;
      .ite (v Entry =' k 0) .skip (.set Found (k 1)))
    .skip

open Scan in
/-- scan(off, j, t₂, t₁, aX, aY, fr, aV, n): the steps for ℓ < t₂. -/
def scanBody : Stmt :=
  .set Found (k 0) ;;
  .for Ell (v Height) scanStep ;;
  .set RowOff (v Found)

/-- The time of scan: t₂ rounds with at most one query each. -/
def tScan {P : Program} (K : DsKit P) (t₁ t₂ : ℕ) : ℕ := t₂ * (K.tQ t₁ + 40) + 12

/-- The locals of scan in the round for ℓ: the arguments, ℓ, the result b so far, and the answer q
to the last query. -/
@[simp] abbrev scanLoc {n t₂ : ℕ} (off : Fin t₂) (j : Fin n) (t₁ aX aY fr aV l : ℕ) (b : Bool)
    (q : ℤ) : List ℤ :=
  [((off : ℕ) : ℤ), ((j : ℕ) : ℤ), t₂, t₁, aX, aY, fr, aV, n, l, WordRam.bit b, q]

section scan

variable (K : DsKit P) {n t₁ t₂ aX aY fr aV : ℕ} {X : Matrix (Fin t₂) (Fin t₁) ℤ}
  {Y : Matrix (Fin t₁) (Fin t₂) ℤ} {Vm : Matrix (Fin t₂) (Fin n) ℤ}

open Classical in
/-- **One ℓ.**  The result so far tells whether there is a hit below ℓ; afterwards it tells whether
there is one below ℓ + 1.  Only cells of the structure change, and it stays ready. -/
theorem scanStep_spec {μ : ℕ → ℤ} (off : Fin t₂) (j : Fin n) (hin : K.Input lim X Y aX aY fr 1)
    (hV : MatAt μ aV Vm) (rV : aV + t₂ * n ≤ fr) (hR : K.Ready X Y aX aY fr μ)
    (hd : d + 4 ≤ lim.depth) {hit : Fin t₂ → Prop}
    (hhit : ∀ l, hit l ↔ Vm l j = 1 ∧ (X * Y) off l ≠ 0) {l : ℕ} (hl : l < t₂) (q : ℤ) :
    Ends lim P d scanStep ⟨frame (scanLoc off j t₁ aX aY fr aV l (decide (HitBelow hit l)) q), μ⟩
      (K.tQ t₁ + 32) fun σ' => ∃ (q' : ℤ) (μ' : ℕ → ℤ),
        σ' = ⟨frame (scanLoc off j t₁ aX aY fr aV l (decide (HitBelow hit (l + 1))) q'), μ'⟩ ∧
        K.Ready X Y aX aY fr μ' ∧ SameOutside μ μ' fr (K.size t₂ t₁) := by
  obtain ⟨hw, h100, hsp, -⟩ := K.basics hin.lim
  have hj := j.isLt
  have hln : l * n + n ≤ t₂ * n := Nat.mul_add_le_mul hl le_rfl
  have haddr : ((aV : ℤ) + l * n + (j : ℕ)).toNat = aV + l * n + j := by omega
  have hread : μ (aV + l * n + j) = Vm ⟨l, hl⟩ j := hV ⟨l, hl⟩ j
  have hsucc := hitBelow_succ hit hl
  unfold scanStep scanLoc
  -- if V[ℓ, j] = 1
  light_if hV1 hV0 : Vm ⟨l, hl⟩ j = 1 using haddr, hread
  · -- entry := query(off, ℓ, t₂, t₁, aX, aY, fr)
    light_call (K.query hin hR off ⟨l, hl⟩ _ (by omega)) with _ μ₂ ⟨rfl, hready₂, hsame₂⟩
    -- if entry ≠ 0 then the result is 1
    light_if hzero hne : (X * Y) off ⟨l, hl⟩ = 0
    · have hno : ¬ hit ⟨l, hl⟩ := fun h => ((hhit _).1 h).2 hzero
      light_skip
      exact ⟨_, μ₂, by simp only [hsucc, hno, or_false]; rfl, hready₂, hsame₂⟩
    · have hyes : hit ⟨l, hl⟩ := (hhit _).2 ⟨hV1, hne⟩
      light_set 1
      exact ⟨(X * Y) off ⟨l, hl⟩, μ₂, by simp [WordRam.bit, hsucc, hyes], hready₂, hsame₂⟩
  · have hno : ¬ hit ⟨l, hl⟩ := fun h => hV0 ((hhit _).1 h).1
    light_skip
    exact ⟨q, μ, by simp only [hsucc, hno, or_false], hR, fun _ _ => rfl⟩

/-- **scan** returns 1 if some ℓ has V[ℓ, j] = 1 and (XY)[off, ℓ] ≠ 0, and 0 if not.  It changes
only cells of the structure. -/
theorem scan_meets {p : ℕ} (hp : P[p]? = some scanBody) {μ : ℕ → ℤ} (off : Fin t₂) (j : Fin n)
    (hin : K.Input lim X Y aX aY fr 1) (hV : MatAt μ aV Vm) (rV : aV + t₂ * n ≤ fr)
    (hR : K.Ready X Y aX aY fr μ) (hd : d + 4 ≤ lim.depth) :
    Meets lim P p d [((off : ℕ) : ℤ), ((j : ℕ) : ℤ), t₂, t₁, aX, aY, fr, aV, n] μ (tScan K t₁ t₂)
      fun r μ' => r = WordRam.bit (decide (∃ l : Fin t₂, Vm l j = 1 ∧ (X * Y) off l ≠ 0)) ∧
        SameOutside μ μ' fr (K.size t₂ t₁) := by
  classical
  obtain ⟨hw, h100, hsp, -⟩ := K.basics hin.lim
  have hbelowX := hin.belowX
  have ht₂ : t₂ ≤ t₂ * t₁ := Nat.le_mul_of_pos_right _ hin.one_le_D
  refine .of_body hp ?_
  unfold scanBody tScan
  light_set 0
  -- for ℓ < t₂: the result so far tells whether there is a hit below ℓ
  refine Ends.next _ (Ends.for (fun l σ => ∃ (q : ℤ) (μ' : ℕ → ℤ),
      σ = ⟨frame (scanLoc off j t₁ aX aY fr aV l
        (decide (HitBelow (fun l => Vm l j = 1 ∧ (X * Y) off l ≠ 0) l)) q), μ'⟩ ∧
      K.Ready X Y aX aY fr μ' ∧ SameOutside μ μ' fr (K.size t₂ t₁))
    t₂ (K.tQ t₁ + 32) ?start ?round ?done ?bound (hT := le_rfl))
  case start =>
    exact ⟨0, μ, by rw [update_frame_setLocal, ← frame_append_zeros _ 1]
                    simp [WordRam.bit, not_hitBelow_zero], hR, fun _ _ => rfl⟩
  case bound =>
    rintro l _ - - ⟨q, μ', rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨q, μ', rfl, -, hsame⟩
    -- the result
    light_set (WordRam.bit (decide
      (HitBelow (fun l => Vm l j = 1 ∧ (X * Y) off l ≠ 0) t₂)))
    refine ⟨?_, hsame⟩
    simp [hitBelow_all]
  case round =>
    rintro l _ hl - ⟨q, μ', rfl, hready, hsame⟩
    light_piece (scanStep_spec K off j hin hV.keep rV hready hd (fun _ => Iff.rfl) hl q)
      with _ ⟨q', μ₂, rfl, hready₂, hsame₂⟩
    exact ⟨by simp, q', μ₂, by rw [update_frame_setLocal]; rfl, hready₂, by light_keep⟩

end scan

end Light.Sec5
