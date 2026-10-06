/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Instances.Classes

/-!
# The table of the chunks

Proof of Theorem 17: "cut it into chunks of at most n²/√D query pairs".  chunks(cls, p, cap, cr, cl,
cw) goes through the `p` classes, whose starts are in the `p + 1` cells from `cls`, cuts each of
them into chunks of at most `cap` places, and writes the residues, the starts and the lengths of the
chunks to `cr`, `cl` and `cw`; the residue of a chunk is the number `rho < p` of its class.  It
returns the number of chunks (`chunks_meets`).  The proof follows the program: one chunk
(`chunksRound_runs`), the chunks of one class (`chunksClass_ends`), all classes.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Chunks

/-- The locals of `chunks`.  The arguments: the address of the starts of the classes, the number `p`
of classes, the largest size `cap` of a chunk, and the addresses of the three tables.  Then the
residue, the start of the next chunk, the end of the class, the number of chunks so far, and the
length of the chunk. -/
abbrev Cls : ℕ := 0
@[inherit_doc Cls] abbrev Num : ℕ := 1
@[inherit_doc Cls] abbrev Cap : ℕ := 2
@[inherit_doc Cls] abbrev TabR : ℕ := 3
@[inherit_doc Cls] abbrev TabL : ℕ := 4
@[inherit_doc Cls] abbrev TabW : ℕ := 5
@[inherit_doc Cls] abbrev Rho : ℕ := 6
@[inherit_doc Cls] abbrev Pos : ℕ := 7
@[inherit_doc Cls] abbrev End : ℕ := 8
@[inherit_doc Cls] abbrev Cnt : ℕ := 9
@[inherit_doc Cls] abbrev Len : ℕ := 10

end Chunks

open Chunks in
/-- One chunk: len := min(cap, end - pos); the three tables get (rho, pos, len) at place cnt;
cnt := cnt + 1; pos := pos + len. -/
def chunksRound : Stmt :=
  .set Len (v End -' v Pos) ;;
  .ite (v Cap <' v Len) (.set Len (v Cap)) .skip ;;
  .store (v TabR +' v Cnt) (v Rho) ;;
  .store (v TabL +' v Cnt) (v Pos) ;;
  .store (v TabW +' v Cnt) (v Len) ;;
  .set Cnt (v Cnt +' k 1) ;;
  .set Pos (v Pos +' v Len)

open Chunks in
/-- The chunks of the class rho: pos := cls[rho]; end := cls[rho + 1]; while pos < end: one
chunk. -/
def chunksClass : Stmt :=
  .set Pos (M (v Cls +' v Rho)) ;;
  .set End (M (v Cls +' v Rho +' k 1)) ;;
  .while (v Pos <' v End) chunksRound

open Chunks in
/-- chunks(cls, p, cap, cr, cl, cw). -/
def chunksBody : Stmt :=
  .set Rho (k 0) ;;
  .set Cnt (k 0) ;;
  .while (v Rho <' v Num) (chunksClass ;; .set Rho (v Rho +' k 1)) ;;
  .set 0 (v Cnt)

/-- The time of chunks, for p classes and nCh chunks. -/
def tChunks (p nCh : ℕ) : ℕ := 37 * nCh + 24 * p + 10

/-- The arguments of chunks; the room `R` of each of the three tables; the list `C` of the starts of
the classes, which stands at `cls`, and a bound `B` on them. -/
structure ChunksArgs : Type where
  (cls p cap cr cl cw : ℕ)
  (R B : ℕ) (C : List ℕ)

/-- The values of the arguments of chunks. -/
abbrev ChunksArgs.vals (x : ChunksArgs) : List ℤ := [x.cls, x.p, x.cap, x.cr, x.cl, x.cw]

/-- The locals of chunks: the arguments and the five locals that change. -/
abbrev ChunksArgs.locals (x : ChunksArgs) (rho pos hi cnt len : ℤ) : List ℤ :=
  [x.cls, x.p, x.cap, x.cr, x.cl, x.cw, rho, pos, hi, cnt, len]

/-- The table that chunks writes. -/
abbrev ChunksArgs.table (x : ChunksArgs) : List Chunk := chunkTabOf x.p x.cap x.C

/-- Only cells of the three tables have changed. -/
abbrev ChunksArgs.Same (x : ChunksArgs) (μ μ' : ℕ → ℤ) : Prop :=
  SameOutside3 μ μ' x.cr x.R x.cl x.R x.cw x.R

/-- What chunks assumes: the starts, at most B, at cls; room for R chunks in each of the three
tables; the areas lie apart and inside the memory. -/
structure ChunksPre (lim : Limits) (μ : ℕ → ℤ) (x : ChunksArgs) : Prop where
  seg : SegN μ x.cls x.C
  len : x.C.length = x.p + 1
  le : ∀ s ∈ x.C, s ≤ x.B
  room : (chunkTabOf x.p x.cap x.C).length ≤ x.R
  hcap : 1 ≤ x.cap := by light_arith
  hB : x.B < lim.space := by light_arith
  cls_le : x.cls + (x.p + 1) < lim.space := by light_arith
  cr_le : x.cr + x.R < lim.space := by light_arith
  cl_le : x.cl + x.R < lim.space := by light_arith
  cw_le : x.cw + x.R < lim.space := by light_arith
  cls_cr : Apart x.cls (x.p + 1) x.cr x.R := by light_arith
  cls_cl : Apart x.cls (x.p + 1) x.cl x.R := by light_arith
  cls_cw : Apart x.cls (x.p + 1) x.cw x.R := by light_arith
  cr_cl : Apart x.cr x.R x.cl x.R := by light_arith
  cr_cw : Apart x.cr x.R x.cw x.R := by light_arith
  cl_cw : Apart x.cl x.R x.cw x.R := by light_arith

/-! ## The pure side -/

section pure

/-- A class of `hi - lo` places has `⌈(hi - lo)/cap⌉` chunks. -/
theorem length_chunksOf (cap lo hi rho : ℕ) :
    (chunksOf cap lo hi rho).length = (hi - lo) ⌈/⌉ cap := by
  simp [chunksOf]

/-- The chunks of the class number rho. -/
def chunkRow (cap : ℕ) (C : List ℕ) (rho : ℕ) : List Chunk :=
  chunksOf cap (C.getD rho 0) (C.getD (rho + 1) 0) rho

theorem length_chunkRow (cap : ℕ) (C : List ℕ) (rho : ℕ) :
    (chunkRow cap C rho).length = (C.getD (rho + 1) 0 - C.getD rho 0) ⌈/⌉ cap :=
  length_chunksOf _ _ _ _

/-- The table when the classes before rho and i chunks of the class rho have been handled. -/
def tabAt (cap : ℕ) (C : List ℕ) (rho i : ℕ) : List Chunk :=
  (List.range rho).flatMap (chunkRow cap C) ++ (chunkRow cap C rho).take i

/-- At the start the table is empty. -/
theorem tabAt_zero_zero (cap : ℕ) (C : List ℕ) : tabAt cap C 0 0 = [] := by simp [tabAt]

/-- After all classes the table is complete. -/
theorem tabAt_end (p cap : ℕ) (C : List ℕ) : tabAt cap C p 0 = chunkTabOf p cap C := by
  rw [tabAt, List.take_zero, List.append_nil]
  rfl

/-- After the last chunk of a class the next class begins. -/
theorem tabAt_row (cap : ℕ) (C : List ℕ) (rho : ℕ) :
    tabAt cap C rho ((C.getD (rho + 1) 0 - C.getD rho 0) ⌈/⌉ cap)
      = tabAt cap C (rho + 1) 0 := by
  rw [tabAt, ← length_chunkRow, List.take_length, tabAt, List.range_succ, List.flatMap_append]
  simp

/-- One more chunk of the class `rho`. -/
theorem tabAt_succ (cap : ℕ) (C : List ℕ) (rho : ℕ) {i : ℕ}
    (hi : i < (C.getD (rho + 1) 0 - C.getD rho 0) ⌈/⌉ cap) :
    tabAt cap C rho (i + 1) = tabAt cap C rho i ++
      [⟨rho, C.getD rho 0 + i * cap, min cap (C.getD (rho + 1) 0 - C.getD rho 0 - i * cap)⟩] := by
  have hrow : i < (chunkRow cap C rho).length := by rw [length_chunkRow]; exact hi
  rw [tabAt, tabAt, ← List.take_append_getElem hrow, List.append_assoc]
  simp [chunkRow, chunksOf]

/-- As long as a chunk is missing, the table is shorter than the complete one. -/
theorem length_tabAt_lt {p cap : ℕ} (C : List ℕ) {rho i : ℕ} (hrho : rho < p)
    (hi : i < (C.getD (rho + 1) 0 - C.getD rho 0) ⌈/⌉ cap) :
    (tabAt cap C rho i).length < (chunkTabOf p cap C).length := by
  have hrow := length_chunkRow cap C rho
  have hrows :=
    List.sum_map_range_mono (fun r => (chunkRow cap C r).length) (show rho + 1 ≤ p by omega)
  rw [List.range_succ, List.map_append, List.sum_append] at hrows
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hrows
  have hall : (chunkTabOf p cap C).length
      = ((List.range p).map fun r => (chunkRow cap C r).length).sum := by
    rw [chunkTabOf, List.length_flatMap]
    rfl
  rw [hall, tabAt, List.length_append, List.length_flatMap, List.length_take]
  omega

/-- The time of the rounds, added up: 37 steps for each chunk and 24 for each class. -/
theorem sum_chunks_rounds (cap : ℕ) (C : List ℕ) (q : ℕ) :
    ∑ rho ∈ Finset.range q, (4 + (37 * ((C.getD (rho + 1) 0 - C.getD rho 0) ⌈/⌉ cap) + 20))
      = 37 * (tabAt cap C q 0).length + 24 * q := by
  induction q with
  | zero => simp [tabAt]
  | succ q ih =>
    have hrow : (tabAt cap C (q + 1) 0).length
        = (tabAt cap C q 0).length + (C.getD (q + 1) 0 - C.getD q 0) ⌈/⌉ cap := by
      rw [← tabAt_row cap C q]
      simp [tabAt, length_chunkRow]
    rw [Finset.sum_range_succ, ih, hrow]
    omega

end pure

/-! ## The tables in the memory -/

variable {μ μ' : ℕ → ℤ} {x : ChunksArgs}

/-- The three tables hold the list T, and nothing else has changed. -/
structure TabInv (μ μ' : ℕ → ℤ) (x : ChunksArgs) (T : List Chunk) : Prop where
  sr : SegN μ' x.cr (T.map (·.residue))
  sl : SegN μ' x.cl (T.map (·.start))
  sw : SegN μ' x.cw (T.map (·.len))
  same : x.Same μ μ'

/-- One more chunk: each table gets one more entry, and the writes to the other two tables do not
touch it. -/
theorem TabInv.push {T : List Chunk} (h : TabInv μ μ' x T) (pre : ChunksPre lim μ x)
    (hlen : T.length < x.R) (c : Chunk) :
    TabInv μ (Function.update (Function.update (Function.update μ' (x.cr + T.length) c.residue)
      (x.cl + T.length) c.start) (x.cw + T.length) c.len) x (T ++ [c]) := by
  light_facts pre
  have hr := h.sr.snoc c.residue
  have hl :=
    SegN.snoc (h.sl.update_out (b := x.cr + T.length) (by simp; omega) (c.residue : ℤ)) c.start
  have hw := SegN.snoc
    ((h.sw.update_out (b := x.cr + T.length) (by simp; omega) (c.residue : ℤ)).update_out
      (b := x.cl + T.length) (by simp; omega) (c.start : ℤ)) c.len
  simp only [List.length_map] at hr hl hw
  refine ⟨?_, ?_, ?_, fun b hb => ?_⟩
  · rw [List.map_append]
    exact (hr.update_out (by simp; omega) _).update_out (by simp; omega) _
  · rw [List.map_append]
    exact hl.update_out (by simp; omega) _
  · rw [List.map_append]
    exact hw
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact h.same b hb

/-- A start of a class, read from a memory in which only the tables have changed. -/
theorem ChunksPre.start (pre : ChunksPre lim μ x) (hsame : x.Same μ μ') {t : ℕ} (ht : t ≤ x.p) :
    μ' (x.cls + t) = ((x.C.getD t 0 : ℕ) : ℤ) ∧ x.C.getD t 0 ≤ x.B := by
  light_facts pre
  have hlen : t < x.C.length := by omega
  rw [hsame _ ⟨by omega, by omega, by omega⟩, pre.seg.read hlen]
  exact ⟨rfl, by rw [List.getD_eq_getElem _ 0 hlen]; exact pre.le _ (List.getElem_mem hlen)⟩

/-! ## The program -/

variable (hw : (lim.space : ℤ) ≤ lim.word)

include hw

/-- One chunk. -/
theorem chunksRound_runs {rho pos hi cnt : ℕ} {len : ℤ} (hpos : pos < hi) (hhi : hi < lim.space)
    (hr : x.cr + cnt < lim.space) (hl : x.cl + cnt < lim.space) (hc : x.cw + cnt < lim.space) :
    chunksRound.Runs lim ⟨frame (x.locals rho pos hi cnt len), μ'⟩
      (· = ⟨frame (x.locals rho (pos + min x.cap (hi - pos) : ℕ) hi (cnt + 1 : ℕ)
          (min x.cap (hi - pos) : ℕ)),
        Function.update (Function.update (Function.update μ' (x.cr + cnt) rho) (x.cl + cnt) pos)
          (x.cw + cnt) (min x.cap (hi - pos) : ℕ)⟩) := by
  by_cases hcap : x.cap < hi - pos
  · have htest : (x.cap : ℤ) < (hi : ℤ) - pos := by omega
    rw [show min x.cap (hi - pos) = x.cap by omega]
    exact ⟨by light_side [chunksRound, update_frame_setLocal, htest],
      by simp [chunksRound, update_frame_setLocal, htest]⟩
  · have htest : ¬ (x.cap : ℤ) < (hi : ℤ) - pos := by omega
    rw [show min x.cap (hi - pos) = hi - pos by omega]
    exact ⟨by light_side [chunksRound, update_frame_setLocal, htest],
      by simp [chunksRound, update_frame_setLocal, htest, Nat.cast_sub hpos.le]⟩

/-- The state of `chunks` when the residue is `rho` and the three tables hold the list `T`. -/
def ChunksInv (μ : ℕ → ℤ) (x : ChunksArgs) (rho : ℕ) (T : List Chunk) (σ : State) : Prop :=
  ∃ (pos hi len : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame (x.locals rho pos hi T.length len), μ'⟩ ∧ TabInv μ μ' x T

/-- The chunks of one class. -/
theorem chunksClass_ends {rho : ℕ} {σ : State} (pre : ChunksPre lim μ x) (hrho : rho < x.p)
    (hσ : ChunksInv μ x rho (tabAt x.cap x.C rho 0) σ) :
    Ends lim P d chunksClass σ (37 * ((x.C.getD (rho + 1) 0 - x.C.getD rho 0) ⌈/⌉ x.cap) + 16)
      (ChunksInv μ x rho (tabAt x.cap x.C (rho + 1) 0)) := by
  obtain ⟨pos₀, end₀, len₀, μ', rfl, hT⟩ := hσ
  light_facts pre
  have hroom : x.table.length ≤ x.R := pre.room
  obtain ⟨hreadLo, hloB⟩ := pre.start hT.same (show rho ≤ x.p by omega)
  obtain ⟨hreadHi, hhiB⟩ := pre.start hT.same (show rho + 1 ≤ x.p by omega)
  have hsucc := fun i hlt => tabAt_succ x.cap x.C rho (i := i) hlt
  have hlenlt : ∀ i, i < (x.C.getD (rho + 1) 0 - x.C.getD rho 0) ⌈/⌉ x.cap →
      (tabAt x.cap x.C rho i).length < x.table.length := fun i hlt => length_tabAt_lt x.C hrho hlt
  have hiff : ∀ i, i < (x.C.getD (rho + 1) 0 - x.C.getD rho 0) ⌈/⌉ x.cap ↔
      i * x.cap < x.C.getD (rho + 1) 0 - x.C.getD rho 0 := fun i => Nat.lt_ceilDiv_iff pre.hcap
  rw [← tabAt_row x.cap x.C rho]
  generalize x.C.getD rho 0 = lo at *
  generalize x.C.getD (rho + 1) 0 = hi at *
  generalize (hi - lo) ⌈/⌉ x.cap = rounds at *
  have haddr : ((x.cls : ℤ) + rho + 1).toNat = x.cls + (rho + 1) := by omega
  -- pos := cls[rho]; end := cls[rho + 1]
  light_set lo using hreadLo
  light_set hi using haddr, hreadHi
  -- while pos < end.  Before round i, the first i chunks of the class are in the tables.
  refine Ends.whileBlock (fun i σ => ∃ (len : ℤ) (μ₁ : ℕ → ℤ),
    σ = ⟨frame (x.locals rho (lo + min (i * x.cap) (hi - lo) : ℕ) hi
      (tabAt x.cap x.C rho i).length len), μ₁⟩ ∧
    TabInv μ μ₁ x (tabAt x.cap x.C rho i)) rounds ?start ?round ?done
    (by simp [chunksRound]; omega)
  case start => exact ⟨len₀, μ', by simp, hT⟩
  case round =>
    rintro i _ hround ⟨len, μ₁, rfl, hT₁⟩
    have hlt : i * x.cap < hi - lo := (hiff i).1 hround
    have hlen := hlenlt i hround
    have hpush := hT₁.push pre (by omega) ⟨rho, lo + i * x.cap, min x.cap (hi - lo - i * x.cap)⟩
    rw [← hsucc i hround] at hpush
    rw [show lo + min (i * x.cap) (hi - lo) = lo + i * x.cap by omega]
    refine ⟨by simp, by simp; omega, (chunksRound_runs hw (by omega) (by omega) (by omega)
      (by omega) (by omega)).mono ?_⟩
    rintro _ rfl
    have hleft : hi - (lo + i * x.cap) = hi - lo - i * x.cap := by omega
    have hnext : lo + i * x.cap + min x.cap (hi - lo - i * x.cap) =
        lo + min ((i + 1) * x.cap) (hi - lo) := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have hlength : (tabAt x.cap x.C rho (i + 1)).length = (tabAt x.cap x.C rho i).length + 1 := by
      rw [hsucc i hround, List.length_append, List.length_singleton]
    exact ⟨(min x.cap (hi - lo - i * x.cap) : ℕ), _, by rw [hleft, hnext, hlength], hpush⟩
  case done =>
    rintro _ ⟨len, μ₁, rfl, hT₁⟩
    have hge : ¬ rounds * x.cap < hi - lo := fun h => absurd ((hiff rounds).2 h) (lt_irrefl _)
    exact ⟨by simp, by simp; omega, _, _, _, _, rfl, hT₁⟩

omit hw in
/-- **chunks** writes the table of the chunks and returns their number. -/
theorem chunks_meets {pChunks : ℕ} (hP : P[pChunks]? = some chunksBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (x : ChunksArgs) (μ : ℕ → ℤ) (pre : ChunksPre lim μ x) :
    Meets lim P pChunks d x.vals μ (tChunks x.p x.table.length) fun r μ' =>
      r = (x.table.length : ℕ) ∧ SegN μ' x.cr (x.table.map (·.residue)) ∧
        SegN μ' x.cl (x.table.map (·.start)) ∧ SegN μ' x.cw (x.table.map (·.len)) ∧
        x.Same μ μ' := by
  refine .of_body hP ?_
  light_facts pre
  have hsum := sum_chunks_rounds x.cap x.C x.p
  rw [tabAt_end, ← ChunksArgs.table] at hsum
  unfold tChunks
  -- rho := 0; cnt := 0
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  -- while rho < p
  refine Ends.next _ (Ends.while (fun rho σ => ChunksInv μ x rho (tabAt x.cap x.C rho 0) σ) x.p
    (fun rho => 37 * ((x.C.getD (rho + 1) 0 - x.C.getD rho 0) ⌈/⌉ x.cap) + 20) ?start ?round ?done)
    (by simp only [Cond.cost, Expr.cost, Nat.reduceAdd]; omega)
  case start =>
    refine ⟨0, 0, 0, μ, ?_, by simp [tabAt_zero_zero, SegN], by simp [tabAt_zero_zero, SegN],
      by simp [tabAt_zero_zero, SegN], .refl⟩
    simpa [tabAt_zero_zero] using
      (frame_append_zeros [(x.cls : ℤ), x.p, x.cap, x.cr, x.cl, x.cw, 0, 0, 0, 0] 1).symm
  case round =>
    rintro rho σ hrho hσ
    have hclass := chunksClass_ends (P := P) (d := d) hw pre hrho hσ
    obtain ⟨pos, hi, len, μ', rfl, -⟩ := hσ
    -- the chunks of the class rho; then rho := rho + 1
    refine ⟨by simp, by simp; omega, Ends.next _ (hclass.mono le_rfl ?_) (by omega)⟩
    rintro _ ⟨pos₁, hi₁, len₁, μ₁, rfl, hT⟩
    light_set (rho + 1 : ℕ)
    exact ⟨pos₁, hi₁, len₁, μ₁, by simp, hT⟩
  case done =>
    rintro _ ⟨pos, hi, len, μ', rfl, hT⟩
    rw [tabAt_end] at hT
    -- return cnt
    exact ⟨by simp, by simp, Ends.setTo ((tabAt x.cap x.C x.p 0).length : ℕ)
      ⟨by simp [tabAt_end], hT.sr, hT.sl, hT.sw, hT.same⟩ (by simp)
      (by simp only [Cond.cost, Expr.cost, Nat.reduceAdd]; omega)⟩

end Light.Sec3
