/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.CellDependencies
public import ThreeSumApsp.Programs.Sec2.Theorem5.Pruned.AllTiles
public import ThreeSumApsp.Programs.Sec2.Theorem5.Wanted.Report
public import ThreeSumApsp.Programs.Sec2.Theorem5.Wanted.SortedFacts
public import ThreeSumApsp.Programs.Tasks

/-!
# Theorem 5: the solver, stage by stage

The text of the solver after the search for m ("The algorithm", Section 2.4.4), cut into six parts:
the shared stage; tiles, codes and digits of the wanted positions (the code of a position is its
output string, read as a number); the sort; the codes in sorted order; the pruned recursions; the
report. There is one lemma for each part together with everything that follows it (fromShared_ends
to reportCall_ends), so that each lemma ends with the lemma of the next part. The lemmas are stated
for arbitrary parameters p, matrices X, Y and positions (I i, J i) (WantedJob). The result is
fromShared_ends: from the state after the search for m the solver ends within timeFromShared steps,
with the entries of XY at the w wanted positions in the cells from out on, and nothing else below
the free pointer changed (Reported).

Every stage writes above everything that the stages before it have written, except the report, which
writes the output. So each lemma hands on what the earlier stages have left, in a memory that agrees
with the earlier one below the area just written.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec2

open ThreeSumApsp.Spec

/-! ## The local variables and the cells of the directory -/

namespace Solver

/-- Local 10 of the solver: m. -/
abbrev Expo : ℕ := 10
/-- Local 11 of the solver: a power of four. -/
abbrev Pow4 : ℕ := 11
/-- Local 12 of the solver: L = 19 m. -/
abbrev Levels : ℕ := 12
/-- Local 13 of the solver: takes the results of the calls. -/
abbrev Void : ℕ := 13
/-- Local 14 of the solver: the address of TID. -/
abbrev AdrTid : ℕ := 14
/-- Local 16 of the solver: the number of bands. -/
abbrev Bands : ℕ := 16
/-- Local 22 of the solver: the address of PERM. -/
abbrev AdrPerm : ℕ := 22
/-- Local 23 of the solver: the number of tiles. -/
abbrev Tiles : ℕ := 23
/-- Local 26 of the solver: the address of SC. -/
abbrev AdrSc : ℕ := 26

/-- Cell 4 of the directory: L - m. -/
abbrev DirOuter : ℕ := 4
/-- Cell 7 of the directory: K₀. -/
abbrev DirRoot : ℕ := 7
/-- Cell 9 of the directory: the number of bands. -/
abbrev DirBands : ℕ := 9
/-- Cell 10 of the directory: 10^L. -/
abbrev DirLeaves : ℕ := 10
/-- Cell 17 of the directory: the address of the powers of ten. -/
abbrev DirP10 : ℕ := 17
/-- Cell 21 of the directory: the address of the table of subsets. -/
abbrev DirMask : ℕ := 21
/-- Cell 22 of the directory: the address of the bands of the rows. -/
abbrev DirBand : ℕ := 22
/-- Cell 24 of the directory: the address of the base-3 digits. -/
abbrev DirDig3 : ℕ := 24
/-- Cell 26 of the directory: the address of the encodings of the row bands. -/
abbrev DirEncA : ℕ := 26
/-- Cell 27 of the directory: the address of the encodings of the column bands. -/
abbrev DirEncB : ℕ := 27
/-- Cell 30 of the directory: the end of the shared block. -/
abbrev DirEnd : ℕ := 30

end Solver

open ThinArg Solver

/-! ## The text -/

/-- The report. -/
def reportCall : Stmt :=
  .call pReport [v Wanted, v AdrPerm, v AdrSc +' v Wanted, v AdrOut] Void

/-- The pruned recursions, and what follows. -/
def fromTiles : Stmt :=
  .call pRunTiles [v Bands, v Levels, M (v Free +' k DirLeaves), M (v Free +' k DirEncA),
    M (v Free +' k DirEncB), v AdrPerm +' v Wanted +' v Wanted +' v Tiles +' k 11, v AdrSc,
    v AdrSc +' v Wanted, v AdrSc +' v Wanted +' v Wanted, M (v Free +' k DirP10)] Void ;;
  reportCall

/-- The codes in sorted order, and what follows. -/
def fromGather : Stmt :=
  .set AdrSc (v AdrPerm +' v Wanted +' v Wanted +' v Tiles +' k 11 +' v Tiles +' k 1) ;;
  .call pGather [v Wanted, v AdrPerm, v AdrTid +' v Wanted, v AdrSc] Void ;;
  fromTiles

/-- The sort, and what follows. -/
def fromSort : Stmt :=
  .set AdrPerm (v AdrTid +' v Wanted +' v Wanted +' v Wanted *' v Levels) ;;
  .set Tiles (v Bands *' v Bands) ;;
  .call pSortWanted [v Wanted, v Levels, v Tiles, v AdrTid, v AdrTid +' v Wanted +' v Wanted,
    v AdrPerm] Void ;;
  fromGather

/-- Tiles, codes and digits of the wanted positions, and what follows. -/
def fromWanted : Stmt :=
  .set AdrTid (M (v Free +' k DirEnd)) ;;
  .set Bands (M (v Free +' k DirBands)) ;;
  .call pWanted [v Wanted, v Levels, M (v Free +' k DirOuter), v Rows, M (v Free +' k DirRoot),
    v Bands, v AdrWI, v AdrWJ, M (v Free +' k DirBand), M (v Free +' k DirDig3),
    M (v Free +' k DirMask), v AdrTid] Void ;;
  fromSort

/-- The shared stage, and what follows. -/
def fromShared : Stmt :=
  .set Levels (k 19 *' v Expo) ;;
  .call pShared [v Levels, v Expo, v Rows, v Cols, v AdrX, v AdrY, v Free] Void ;;
  fromWanted

/-- The local variables after the search for m.  Local 1 is D, which only the shared stage reads;
locals 3 (the bound on the entries) and 11 (a power of four) are never read.  The last seven
arguments are the values of Levels, Void, AdrTid, Bands, AdrPerm, Tiles and AdrSc. -/
def solverLocals (p : Par) (w : ℕ) (u e1 e11 : ℤ) (ax ay wi wj out fr : ℕ)
    (levels₀ void₀ tid₀ bands₀ perm₀ tiles₀ sc₀ : ℤ) : List ℤ :=
  [(p.N : ℤ), e1, (w : ℤ), u, (ax : ℤ), (ay : ℤ), (wi : ℤ), (wj : ℤ), (out : ℤ), (fr : ℤ),
    (p.m : ℤ),
    e11, levels₀, void₀, tid₀, 0, bands₀, 0, 0, 0, 0, 0, perm₀, tiles₀, 0, 0, sc₀]

/-- The entries of the procedures that the solver calls, all with one constant. -/
structure MainCallees (lim : Limits) (P : Program) (c : ℕ) : Prop where
  shared : SharedSpec lim P c
  wanted : WantedSpec lim P c
  sort : SortWantedSpec lim P c
  gather : GatherSpec lim P c
  tiles : RunTilesSpec lim P c
  report : ReportSpec lim P c

/-- What the stages ask of the limits; A bounds the encoded numbers. -/
structure StageLimits (lim : Limits) (p : Par) (hmL : p.m ≤ p.L)
    (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ)
    (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) (w fr d : ℕ) (A : ℤ) : Prop where
  depth : d + p.L + 5 ≤ lim.depth
  space : p.end5 fr w ≤ lim.space
  ten : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word
  bands : (((p.nB + 1) * (p.nB + 1) : ℕ) : ℤ) ≤ lim.word
  encA : ∀ β, ∀ e ∈ arrT (encodingL (bandArrayL (stdLayout hmL) X β)), |e| ≤ A
  encB : ∀ β, ∀ e ∈ arrT (encodingR (bandArrayR (stdLayout hmL) Y β)), |e| ≤ A
  room : 10 ^ p.L * (A * A) ≤ lim.word

/-- What the proofs use of the limits. -/
theorem StageLimits.arith {lim : Limits} {p : Par} {hmL : p.m ≤ p.L}
    {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {w fr d : ℕ}
    {A : ℤ} (lims : StageLimits lim p hmL X Y w fr d A) (std : Std lim) :
    (lim.space : ℤ) ≤ lim.word ∧ 100 ≤ lim.word ∧ p.end5 fr w ≤ lim.space
      ∧ d + p.L + 5 ≤ lim.depth :=
  ⟨std.space_le, std.const_le, lims.space, lims.depth⟩

/-- The task of the stages: the w wanted positions (I i, J i) are positions of the product, no two
are equal, V i is the entry of XY at the i-th of them, and the output lies below the free pointer.
-/
structure WantedJob (p : Par) (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ)
    (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) (w out fr : ℕ) (I J : ℕ → ℕ) (V : ℕ → ℤ) : Prop where
  hI : ∀ i < w, I i < p.N
  hJ : ∀ i < w, J i < p.N
  inj : ∀ i < w, ∀ j < w, I i = I j → J i = J j → i = j
  hV : ∀ i (hi : i < w), V i = (X * Y) ⟨I i, hI i hi⟩ ⟨J i, hJ i hi⟩
  hout : out + w ≤ fr

/-- What the solver has to reach: the values V are in the cells from out on, and nothing else below
the free pointer has changed since the memory μ of the call. -/
def Reported (μ : ℕ → ℤ) (fr out w : ℕ) (V : ℕ → ℤ) (σ' : State) : Prop :=
  (∀ j < w, σ'.mem (out + j) = V j) ∧ KeptBut μ σ'.mem fr out w

/-! ## The times: each stage with everything that follows it -/

/-- The report. -/
def timeReport (c w : ℕ) : ℕ := 8 + c * (w + 1)
/-- The pruned recursions, whose work is at most work, and what follows. -/
def timeFromTiles (c w work : ℕ) : ℕ := 38 + c * work + timeReport c w
/-- The codes in sorted order, and what follows. -/
def timeFromGather (c w work : ℕ) : ℕ := 22 + c * (w + 1) + timeFromTiles c w work
/-- The sort, and what follows. -/
def timeFromSort (c : ℕ) (p : Par) (w work : ℕ) : ℕ :=
  26 + c * ((p.L + 1) * (w + 10) + p.nB * p.nB + 1) + timeFromGather c w work
/-- Tiles, codes and digits of the wanted positions, and what follows. -/
def timeFromWanted (c : ℕ) (p : Par) (w work : ℕ) : ℕ :=
  39 + c * ((w + 1) * (p.L + 1)) + timeFromSort c p w work
/-- The shared stage, and what follows. -/
def timeFromShared (c : ℕ) (p : Par) (w work : ℕ) : ℕ :=
  13 + c * sharedShape p + timeFromWanted c p w work

variable {lim : Limits} {P : Program} {c d : ℕ} {p : Par} {hmL : p.m ≤ p.L}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {w : ℕ}
  {u e1 e11 : ℤ} {ax ay wi wj out fr : ℕ} {A : ℤ} {I J : ℕ → ℕ} {V : ℕ → ℤ} {μ : ℕ → ℤ}

/-! ## The report -/

/-- **The report**: the values stand in sorted order in the cells from SV on, and π is the sorting
permutation. -/
theorem reportCall_ends (std : Std lim) (C : MainCallees lim P c) (hd : d + 1 ≤ lim.depth)
    {levels₀ void₀ tid₀ bands₀ tiles₀ : ℤ} {μ5 : ℕ → ℤ} {π : List ℕ} (hsp : p.end5 fr w ≤ lim.space)
    (hπ : SegN μ5 (p.aPERM fr w) π) (hperm : π.Perm (List.range w))
    (hval : ∀ i < w, μ5 (p.aSV fr w + i) = V (π.getD i 0)) (kept : ∀ a < fr, μ5 a = μ a)
    (hout : out + w ≤ fr) :
    Ends lim P d reportCall
      ⟨frame (solverLocals p w u e1 e11 ax ay wi wj out fr levels₀ void₀ tid₀ bands₀ (p.aPERM fr w)
        tiles₀ (p.aSC fr w)), μ5⟩ (timeReport c w) (Reported μ fr out w V) := by
  have hw := std.space_le
  have hplaces := p.places fr
  have hplaces5 := p.places5 fr w
  have hlen : π.length = w := by rw [hperm.length_eq, List.length_range]
  have hmem : ∀ i, i ∈ π ↔ i < w := fun i => by rw [hperm.mem_iff, List.mem_range]
  unfold reportCall solverLocals timeReport
  -- report(w, PERM, SV, out)
  light_call (C.report w (p.aPERM fr w) (p.aSV fr w) out π (readSeg μ5 (p.aSV fr w) w) μ5 hπ
    seg_readSeg hlen (by simp) (hperm.symm.nodup List.nodup_range) (fun i hi => (hmem i).mp hi)
    (by omega) (by omega) (by omega) (by omega)) with r μ6 ⟨hwritten, hfr⟩
  refine ⟨fun j hj => ?_, fun a ⟨ha, ho⟩ => (hfr a ho).trans (kept a ha)⟩
  -- position j is the i-th in sorted order for some i
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ((hmem j).mpr hj)
  have hcell := hwritten i (by omega)
  rw [List.getD_eq_getElem _ _ hi] at hcell
  change μ6 (out + π[i]) = _
  rw [hcell, ← List.getD_eq_getElem π 0 hi, ← hval i (by omega)]
  simp [readSeg, show i < w by omega]

/-! ## The pruned recursions -/

/-- What the pruned recursions ask for is there after the sort: the encodings and the powers of ten
from the shared stage, the first position of each tile, and the codes in sorted order. -/
theorem tilesPre (lims : StageLimits lim p hmL X Y w fr d A) {μ4 : ℕ → ℤ} {π : List ℕ}
    (h : SortedPre p w I J π) (shared : SharedReady p hmL ax ay fr X Y μ4)
    (hstart : ∀ t ≤ p.nB * p.nB, μ4 (p.aSTART fr w + t) = startNo p w I J t)
    (hsc : ∀ i (hi : i < π.length), μ4 (p.aSC fr w + i) = codeNo p I J π[i]) :
    TilesPre lim μ4
      { nB := p.nB, L := p.L, enca := p.aENCA fr, encb := p.aENCB fr, start := p.aSTART fr w
        sc := p.aSC fr w, sv := p.aSV fr w, sp := p.aSTK fr w, p10 := p.aP10 fr, w := w
        EA := fun β => arrT (encodingL (bandArrayL (stdLayout hmL) X β))
        EB := fun β => arrT (encodingR (bandArrayR (stdLayout hmL) Y β))
        s := startNo p w I J, codes := tileCodes p w I J π, A := A, B := A } := by
  have hsp := lims.space
  have hplaces := p.places fr
  have hplaces5 := p.places5 fr w
  simp only [Par.T] at hplaces
  exact
    { hp10 := shared.p10
      hea := shared.encA
      heb := shared.encB
      lea := fun β _ => length_arrT _
      leb := fun β _ => length_arrT _
      hstart := hstart
      mono := fun t _ => startNo_mono p w I J t
      s_le := h.startNo_last.le
      hcodes := fun t _ k hk => by
        obtain ⟨hlt, hcode, -⟩ := h.getElem_tileCodes t (show k < _ by simpa using hk)
        rw [Nat.add_assoc, hsc _ hlt, List.getElem_map, hcode]
      lcodes := fun t _ => h.length_tileCodes t
      sorted := fun t _ => h.tileCodes_sorted t
      small := fun t _ => h.tileCodes_lt t
      boundA := fun β _ => lims.encA β
      boundB := fun β _ => lims.encB β
      room := lims.room
      ten := lims.ten }

/-- After the pruned recursions the cells of SV hold the wanted entries in sorted order: the i-th
position in sorted order is the k-th of some tile, and there the pruned recursion returns the entry
of XY. -/
theorem sorted_values (job : WantedJob p X Y w out fr I J V) {μ5 : ℕ → ℤ} {π : List ℕ} {sv : ℕ}
    (h : SortedPre p w I J π)
    (hvals : ∀ β < p.nB, ∀ β' < p.nB, Seg μ5 (sv + startNo p w I J (β * p.nB + β'))
      (prunedList (arrT (encodingL (bandArrayL (stdLayout hmL) X β)))
        (arrT (encodingR (bandArrayR (stdLayout hmL) Y β'))) p.L 0
        (tileCodes p w I J π (β * p.nB + β')))) :
    ∀ i < w, μ5 (sv + i) = V (π.getD i 0) := by
  intro i hi
  have hlen := h.length_eq
  obtain ⟨β, hβ, β', hβ', k, hk, rfl⟩ := h.exists_place hi
  have hlt : startNo p w I J (β * p.nB + β') + k < π.length := by omega
  have hiw : π[startNo p w I J (β * p.nB + β') + k] < w := h.mem_iff.mp (List.getElem_mem hlt)
  have hkl : k < (prunedList (arrT (encodingL (bandArrayL (stdLayout hmL) X β)))
      (arrT (encodingR (bandArrayR (stdLayout hmL) Y β'))) p.L 0
      (tileCodes p w I J π (β * p.nB + β'))).length := by
    rw [h.length_prunedList _ _ hβ']
    exact hk
  have hval := h.tile_value X Y hβ' hk (List.getElem?_eq_getElem hlt) hiw
  rw [List.getD_eq_getElem _ _ hkl] at hval
  rw [List.getD_eq_getElem _ _ hlt, job.hV _ hiw, ← hval, ← hvals β hβ β' hβ' k hkl, Nat.add_assoc]

/-- **The pruned recursions**, and what follows. -/
theorem fromTiles_ends (std : Std lim) (C : MainCallees lim P c)
    (lims : StageLimits lim p hmL X Y w fr d A)
    (job : WantedJob p X Y w out fr I J V) {void₀ tid₀ : ℤ} {μ4 : ℕ → ℤ} {π : List ℕ}
    (h : SortedPre p w I J π) (shared : SharedReady p hmL ax ay fr X Y μ4)
    (kept : ∀ a < fr, μ4 a = μ a) (hπ : SegN μ4 (p.aPERM fr w) π)
    (hstart : ∀ t ≤ p.nB * p.nB, μ4 (p.aSTART fr w + t) = startNo p w I J t)
    (hsc : ∀ i (hi : i < π.length), μ4 (p.aSC fr w + i) = codeNo p I J π[i]) :
    Ends lim P d fromTiles
      ⟨frame (solverLocals p w u e1 e11 ax ay wi wj out fr p.L void₀ tid₀ p.nB (p.aPERM fr w)
        ((p.nB * p.nB : ℕ) : ℤ) (p.aSC fr w)), μ4⟩
      (timeFromTiles c w (tilesShape p.nB p.L (tileCodes p w I J π))) (Reported μ fr out w V) := by
  have hlim := lims.arith std
  have hplaces := p.places fr
  have hplaces5 := p.places5 fr w
  have hlen := h.length_eq
  unfold fromTiles solverLocals timeFromTiles
  -- runTiles(nB, L, 10^L, ENCA, ENCB, START, SC, SV, STK, P10)
  light_call (C.tiles _ μ4 (tilesPre lims h shared hstart hsc) _ (by light_arith))
    using shared.dirs, Par.T with r μ5 ⟨hvals, hfr⟩
  dsimp only at hvals hfr
  have low : ∀ a, a < p.aSV fr w → μ5 a = μ4 a := fun a ha => hfr a (by omega)
  exact (reportCall_ends std C (by omega) lims.space
    (hπ.congr fun i hi => low _ (by simp at hi; omega))
    h.perm (sorted_values job h hvals) (fun a ha => (low a (by omega)).trans (kept a ha))
    job.hout).mono (by light_time) fun _ hq => hq

/-! ## The codes in sorted order -/

/-- **The codes in sorted order**, and what follows. -/
theorem fromGather_ends (std : Std lim) (C : MainCallees lim P c)
    (lims : StageLimits lim p hmL X Y w fr d A)
    (job : WantedJob p X Y w out fr I J V) {void₀ sc₀ : ℤ} {μ3 : ℕ → ℤ} {π : List ℕ}
    (h : SortedPre p w I J π) (shared : SharedReady p hmL ax ay fr X Y μ3)
    (kept : ∀ a < fr, μ3 a = μ a) (hπ : SegN μ3 (p.aPERM fr w) π)
    (hstart : ∀ t ≤ p.nB * p.nB, μ3 (p.aSTART fr w + t) = startNo p w I J t)
    (hcode : ∀ i < w, μ3 (p.aCODE fr w + i) = codeNo p I J i) :
    Ends lim P d fromGather
      ⟨frame (solverLocals p w u e1 e11 ax ay wi wj out fr p.L void₀ (p.aTID fr w) p.nB
        (p.aPERM fr w) ((p.nB * p.nB : ℕ) : ℤ) sc₀), μ3⟩
      (timeFromGather c w (tilesShape p.nB p.L (tileCodes p w I J π))) (Reported μ fr out w V) := by
  have hlim := lims.arith std
  have hplaces := p.places fr
  have hplaces5 := p.places5 fr w
  have hlen := h.length_eq
  unfold fromGather solverLocals timeFromGather
  -- SC := PERM + w + w + nT + 11 + nT + 1
  light_set (p.aSC fr w : ℕ)
  -- gather(w, PERM, CODE, SC)
  light_call (C.gather w (p.aPERM fr w) (p.aCODE fr w) (p.aSC fr w) μ3 π (by omega) hlen
    hπ (fun i hi => h.mem_iff.mp hi) (by omega) (by omega)) with r μ4 ⟨hg, hfr⟩
  have low : ∀ a, a < p.aSC fr w → μ4 a = μ3 a := fun a ha => hfr a (Or.inl ha)
  light_piece (fromTiles_ends std C lims job h (shared.of_agree fun a ha _ => low a (by omega))
    (fun a ha => (low a (by omega)).trans (kept a ha))
    (hπ.congr fun i hi => low _ (by simp at hi; omega))
    (fun t ht => (low _ (by omega)).trans (hstart t ht))
    fun i hi => (hg i hi).trans (hcode _ (h.mem_iff.mp (List.getElem_mem hi))))

/-! ## The sort -/

/-- **The sort**, and what follows. -/
theorem fromSort_ends (std : Std lim) (C : MainCallees lim P c)
    (lims : StageLimits lim p hmL X Y w fr d A)
    (job : WantedJob p X Y w out fr I J V) {void₀ perm₀ tiles₀ sc₀ : ℤ} {μ2 : ℕ → ℤ} {work : ℕ}
    (hwork : ∀ π, SortedPre p w I J π → tilesShape p.nB p.L (tileCodes p w I J π) ≤ work)
    (shared : SharedReady p hmL ax ay fr X Y μ2) (kept : ∀ a < fr, μ2 a = μ a)
    (hrows : ∀ i < w, μ2 (p.aTID fr w + i) = tileNo p I J i
      ∧ μ2 (p.aTID fr w + w + i) = codeNo p I J i
      ∧ SegN μ2 (p.aTID fr w + 2 * w + i * p.L) (digitList 10 p.L (codeNo p I J i))) :
    Ends lim P d fromSort
      ⟨frame (solverLocals p w u e1 e11 ax ay wi wj out fr p.L void₀ (p.aTID fr w) p.nB perm₀ tiles₀
        sc₀), μ2⟩
      (timeFromSort c p w work) (Reported μ fr out w V) := by
  have hlim := lims.arith std
  have hplaces := p.places fr
  have hplaces5 := p.places5 fr w
  unfold fromSort solverLocals timeFromSort
  -- PERM := TID + w + w + w L, and the number nT = nB² of tiles
  light_set (p.aPERM fr w : ℕ)
  light_set (p.nB * p.nB : ℕ)
  -- sortWanted(w, L, nT, TID, DGT, PERM)
  light_call (C.sort
    { w := w, L := p.L, nT := p.nB * p.nB, tid := p.aTID fr w, dgt := p.aTID fr w + 2 * w
      perm := p.aPERM fr w } μ2 (tileNo p I J) (codeNo p I J)
    { space := by simp only [SortWanted.Args.room]; omega
      tidBefore := by light_arith
      dgtBefore := by light_arith
      tiles := fun i hi => (hrows i hi).1
      tileLt := fun i hi => tileNo_lt_nT hmL (job.hI i hi) (job.hJ i hi)
      codes := fun i hi => (hrows i hi).2.2
      codeLt := fun i _ => codeNo_lt_pow hmL i })
    with r μ3 ⟨⟨π, hperm, hπ, hsorted⟩, hst, hfr⟩
  dsimp only at hperm hπ hsorted hst
  have low : ∀ a, a < p.aPERM fr w → μ3 a = μ2 a := fun a ha => hfr a (Or.inl ha)
  have h : SortedPre p w I J π := ⟨hmL, job.hI, job.hJ, job.inj, hperm, hsorted⟩
  have hc := Nat.mul_le_mul_left c (hwork π h)
  refine (fromGather_ends std C lims job h (shared.of_agree fun a ha _ => low a (by omega))
    (fun a ha => (low a (by omega)).trans (kept a ha)) hπ (fun t ht => ?_)
    fun i hi => ?_).mono (by unfold timeFromGather timeFromTiles; light_time) fun _ hq => hq
  · rw [show p.aSTART fr w + t = p.aPERM fr w + 2 * w + (p.nB * p.nB + 11) + t by omega, hst t ht]
    rfl
  · exact (low _ (by omega)).trans (hrows i hi).2.1

/-! ## Tiles, codes and digits of the wanted positions -/

/-- **Tiles, codes and digits of the wanted positions**, and what follows. -/
theorem fromWanted_ends (std : Std lim) (C : MainCallees lim P c)
    (lims : StageLimits lim p hmL X Y w fr d A)
    (job : WantedJob p X Y w out fr I J V) {void₀ tid₀ bands₀ perm₀ tiles₀ sc₀ : ℤ} {μ1 : ℕ → ℤ}
    {work : ℕ}
    (hwork : ∀ π, SortedPre p w I J π → tilesShape p.nB p.L (tileCodes p w I J π) ≤ work)
    (shared : SharedReady p hmL ax ay fr X Y μ1) (kept : ∀ a < fr, μ1 a = μ a)
    (hWI : ∀ i < w, μ1 (wi + i) = I i) (hWJ : ∀ i < w, μ1 (wj + i) = J i) (hwi : wi + w ≤ fr)
    (hwj : wj + w ≤ fr) :
    Ends lim P d fromWanted
      ⟨frame (solverLocals p w u e1 e11 ax ay wi wj out fr p.L void₀ tid₀ bands₀ perm₀ tiles₀ sc₀),
        μ1⟩
      (timeFromWanted c p w work) (Reported μ fr out w V) := by
  have hlim := lims.arith std
  have hplaces := p.places fr
  have hplaces5 := p.places5 fr w
  have tab : WantedTables p μ1 (p.aBAND fr) (p.aDIG3 fr) (p.aMASK fr) (p.sharedEnd fr) :=
    { hband := shared.band
      hblock := shared.block
      hdig3 := shared.dig3
      hmask := shared.mask
      band_le := by omega
      dig3_le := by omega
      mask_le := by omega }
  unfold fromWanted solverLocals timeFromWanted
  -- TID and the number of bands, from the directory
  light_set (p.aTID fr w : ℕ) using shared.dirs
  light_set (p.nB : ℕ) using shared.dirs
  -- wanted(w, L, L - m, N, K₀, nB, WI, WJ, BAND, DIG3, MASK, TID)
  refine Ends.callToThen (C.wanted p w wi wj (p.aBAND fr) (p.aDIG3 fr) (p.aMASK fr) (p.sharedEnd fr)
    μ1 I J
    { hmL := hmL
      tab := tab
      hI := fun i hi => ⟨hWI i hi, job.hI i hi⟩
      hJ := fun i hi => ⟨hWJ i hi, job.hJ i hi⟩
      hpow := lims.ten
      hnB := lims.bands } _ (by omega)) ?_
    (by light_side [shared.dirs])
  rintro r μ2 ⟨hrows, hfr2⟩
  have low : ∀ a, a < p.sharedEnd fr → μ2 a = μ1 a := fun a ha => hfr2 a (Or.inl ha)
  light_piece (fromSort_ends std C lims job hwork (shared.of_agree fun a ha _ => low a ha)
    (fun a ha => (low a (by omega)).trans (kept a ha)) hrows)

/-! ## The shared stage -/

/-- **The shared stage**, and what follows: the whole solver after the search for m. -/
theorem fromShared_ends (std : Std lim) (C : MainCallees lim P c) (hL : p.L = 19 * p.m)
    (lims : StageLimits lim p hmL X Y w fr d A) (job : WantedJob p X Y w out fr I J V)
    {levels₀ void₀ tid₀ bands₀ perm₀ tiles₀ sc₀ U : ℤ} {work : ℕ}
    (hwork : ∀ π, SortedPre p w I J π → tilesShape p.nB p.L (tileCodes p w I J π) ≤ work)
    (pre : SharedPre lim p ax ay fr X Y U μ) (hWI : ∀ i < w, μ (wi + i) = I i)
    (hWJ : ∀ i < w, μ (wj + i) = J i) (hwi : wi + w ≤ fr) (hwj : wj + w ≤ fr) :
    Ends lim P d fromShared
      ⟨frame (solverLocals p w u p.D e11 ax ay wi wj out fr levels₀ void₀ tid₀ bands₀ perm₀ tiles₀
        sc₀), μ⟩
      (timeFromShared c p w work) (Reported μ fr out w V) := by
  have hlim := lims.arith std
  have hplaces := p.places fr
  have hplaces5 := p.places5 fr w
  unfold fromShared solverLocals timeFromShared
  -- L := 19 m
  light_set (p.L : ℕ)
  -- shared(L, m, N, D, x, y, fr)
  light_call (C.shared p hmL ax ay fr μ X Y U pre) with r μ1 ⟨shared, hfr⟩
  have low : ∀ a, a < fr → μ1 a = μ a := fun a ha => hfr a (Or.inl ha)
  exact (fromWanted_ends std C lims job hwork shared low
    (fun i hi => (low _ (by omega)).trans (hWI i hi))
    (fun i hi => (low _ (by omega)).trans (hWJ i hi)) hwi hwj).mono (by light_time) fun _ hq => hq

end Light.Sec2
