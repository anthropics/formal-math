/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Spec.Sec3.Theorem17.Instances

/-!
# The two matrices of an instance (proof of Theorem 17)

"a ∼ (c, σ) ⟺ σ ≡ w(a,c) + ϱ, (c, σ) ∼ b ⟺ σ ≡ -w(b,c) (mod p)."

writeY(y, rbc, n, D, p, c0, len) writes the D × n matrix Y of the instances for the piece
{c0, …, c0 + len - 1} of C: the middle vertex (c, σ) is the row (c - c0) p + σ.  The n² cells from
rbc hold the residues of the weights w(b,c) mod p, that of (b, c) at place b n + c.
writeX(x, rac, n, D, p, c0, len, rho) writes the n × D matrix X for the residue rho; the cells from
rac hold the residues of the weights w(a,c), that of (a, c) at place a n + c.  In the statements and
docstrings below, c counts from 0 within the piece: the c-th member of the piece is the vertex
c0 + c.

Both clear the matrix and then run through the pairs of a vertex and a member of the piece; each
pair marks one cell with a 1.  So both are instances of one pair of loops:

* `markVal` says what a cell holds when the pairs before (u, w) have been handled, and `Marked` says
  it of the memory;
* `markPairs` runs the two loops, given what the body does for one pair (`MarkCtx`);
* `writeYCell_spec` and `writeXCell_spec` treat the bodies: read a residue, form the label, mark the
  cell;
* `getElem_yList` and `getElem_xList` identify the marks of all pairs with the matrices.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Marking cells: the pure side -/

section marks

/-- The cell i has been marked when the pairs (u', w'), w' < W, before (u, w) in lexicographic order
have been handled; the pair (u', w') marks the cell pos u' w'. -/
def CellMarked (pos : ℕ → ℕ → ℕ) (W u w i : ℕ) : Prop :=
  ∃ u' w', (u' < u ∨ (u' = u ∧ w' < w)) ∧ w' < W ∧ pos u' w' = i

open Classical in
/-- The content of the cell i when the pairs before (u, w) have been handled: 1 if it has been
marked, else 0. -/
noncomputable def markVal (pos : ℕ → ℕ → ℕ) (W u w i : ℕ) : ℤ :=
  if CellMarked pos W u w i then 1 else 0

variable {pos : ℕ → ℕ → ℕ} {W u w i : ℕ}

theorem markVal_zero : markVal pos W 0 0 i = 0 := by
  unfold markVal
  rw [if_neg]
  rintro ⟨u', w', h, -, -⟩
  omega

theorem markVal_step (hlt : w < W) :
    markVal pos W u (w + 1) i = if i = pos u w then 1 else markVal pos W u w i := by
  unfold markVal
  by_cases h : i = pos u w
  · rw [if_pos h, if_pos ⟨u, w, Or.inr ⟨rfl, by omega⟩, hlt, h.symm⟩]
  · rw [if_neg h]
    congr 1
    refine propext ⟨?_, ?_⟩
    · rintro ⟨u', w', h1, h2, h3⟩
      refine ⟨u', w', ?_, h2, h3⟩
      rcases h1 with h1 | ⟨rfl, h1⟩
      · exact Or.inl h1
      · refine Or.inr ⟨rfl, ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h4 | rfl
        · exact h4
        · exact absurd h3.symm h
    · rintro ⟨u', w', h1, h2, h3⟩
      exact ⟨u', w', by omega, h2, h3⟩

theorem markVal_row : markVal pos W u W i = markVal pos W (u + 1) 0 i := by
  unfold markVal
  congr 1
  refine propext ⟨?_, ?_⟩
  · rintro ⟨u', w', h1, h2, h3⟩
    exact ⟨u', w', by omega, h2, h3⟩
  · rintro ⟨u', w', h1, h2, h3⟩
    exact ⟨u', w', by omega, h2, h3⟩

/-- At the end, a cell is marked iff it is the cell of one of the pairs. -/
theorem markVal_end {U : ℕ} (q : Prop) [Decidable q] (h : q ↔ ∃ u' < U, ∃ w' < W, pos u' w' = i) :
    markVal pos W U 0 i = if q then 1 else 0 := by
  unfold markVal
  have : CellMarked pos W U 0 i ↔ q := by
    rw [h]
    constructor
    · rintro ⟨u', w', h1, h2, h3⟩
      exact ⟨u', by omega, w', h2, h3⟩
    · rintro ⟨u', h1, w', h2, h3⟩
      exact ⟨u', w', Or.inl h1, h2, h3⟩
  by_cases hq : q
  · rw [if_pos hq, if_pos (this.2 hq)]
  · rw [if_neg hq, if_neg fun h' => hq (this.1 h')]

end marks

/-! ## Marking cells: the memory -/

/-- The m cells from base hold the marks of the pairs before (u, w), and no other cell has
changed. -/
structure Marked (μ μ' : ℕ → ℤ) (base m : ℕ) (pos : ℕ → ℕ → ℕ) (W u w : ℕ) : Prop where
  cells : ∀ i < m, μ' (base + i) = markVal pos W u w i
  rest : SameOutside μ μ' base m

namespace Marked

variable {μ μ' : ℕ → ℤ} {base m : ℕ} {pos : ℕ → ℕ → ℕ} {U W u w : ℕ}

/-- After the clearing no pair has been handled. -/
theorem start (hzero : ∀ i < m, μ' (base + i) = 0) (hrest : SameOutside μ μ' base m) :
    Marked μ μ' base m pos W 0 0 :=
  ⟨fun i hi => by rw [markVal_zero]; exact hzero i hi, hrest⟩

/-- The pair (u, w) marks its cell. -/
theorem step (h : Marked μ μ' base m pos W u w) (hlt : w < W) (hpos : pos u w < m) :
    Marked μ (Function.update μ' (base + pos u w) 1) base m pos W u (w + 1) := by
  refine ⟨fun i hi => ?_, h.rest.update ⟨by omega, by omega⟩ _⟩
  rw [markVal_step hlt]
  split_ifs with e
  · rw [e, Function.update_self]
  · rw [Function.update_of_ne (by omega)]
    exact h.cells i hi

/-- The end of a row of pairs is the beginning of the next row. -/
theorem row (h : Marked μ μ' base m pos W u W) : Marked μ μ' base m pos W (u + 1) 0 :=
  ⟨fun i hi => by rw [← markVal_row]; exact h.cells i hi, h.rest⟩

/-- When all pairs have been handled, the cells hold the list of all marks. -/
theorem seg {l : List ℤ} (h : Marked μ μ' base m pos W U 0) (hlen : l.length = m)
    (hget : ∀ i (hi : i < l.length), l[i] = markVal pos W U 0 i) : Seg μ' base l :=
  fun i hi => by rw [hget i hi]; exact h.cells i (hlen ▸ hi)

end Marked

/-! ## Marking cells: the two loops -/

/-- What the two loops `for u < U: for w < W: cell` need.  L u w t is the list of the locals: u and
w are the counters, in the locals cu and cw, and t is a temporary of the body.  The body takes at
most b steps and marks the cell of the pair (u, w). -/
structure MarkCtx (lim : Limits) (P : Program) (d : ℕ) (μ : ℕ → ℤ) (base m U W b : ℕ)
    (pos : ℕ → ℕ → ℕ) (cu cw : ℕ) (hiU hiW : Expr) (cell : Stmt) (L : ℤ → ℤ → ℤ → List ℤ) :
    Prop where
  wordU : (U : ℤ) ≤ lim.word
  wordW : (W : ℤ) ≤ lim.word
  atU : ∀ u w t, frame (L u w t) cu = u
  atW : ∀ u w t, frame (L u w t) cw = w
  setU : ∀ u w t z, setLocal (L u w t) cu z = L z w t
  setW : ∀ u w t z, setLocal (L u w t) cw z = L u z t
  boundU : ∀ u w t μ', hiU.Gives lim ⟨frame (L u w t), μ'⟩ U
  boundW : ∀ u w t μ', hiW.Gives lim ⟨frame (L u w t), μ'⟩ W
  pos_lt : ∀ u w, u < U → w < W → pos u w < m
  cell_spec : ∀ (u w : ℕ) (t : ℤ) (μ' : ℕ → ℤ), u < U → w < W → SameOutside μ μ' base m →
    Ends lim P d cell ⟨frame (L u w t), μ'⟩ b fun σ' =>
      ∃ t', σ' = ⟨frame (L u w t'), Function.update μ' (base + pos u w) 1⟩

section loops

variable {μ μ' : ℕ → ℤ} {base m U W b : ℕ} {pos : ℕ → ℕ → ℕ} {cu cw : ℕ} {hiU hiW : Expr}
  {cell : Stmt} {L : ℤ → ℤ → ℤ → List ℤ}

/-- The inner loop: the pairs (u, 0), …, (u, W - 1) mark their cells. -/
theorem markRow (C : MarkCtx lim P d μ base m U W b pos cu cw hiU hiW cell L) {u : ℕ} (hu : u < U)
    (w₀ t₀ : ℤ) (h : Marked μ μ' base m pos W u 0) :
    Ends lim P d (.for cw hiW cell) ⟨frame (L u w₀ t₀), μ'⟩ (W * (hiW.cost + b + 7) + hiW.cost + 5)
      fun σ' => ∃ w t μ'', σ' = ⟨frame (L u w t), μ''⟩ ∧ Marked μ μ'' base m pos W (u + 1) 0 := by
  refine Ends.for
    (fun w σ => ∃ t μ'', σ = ⟨frame (L u w t), μ''⟩ ∧ Marked μ μ'' base m pos W u w) W b
    ?start ?round ?done ?bound C.wordW le_rfl
  case start => exact ⟨t₀, μ', by simp only [update_frame_setLocal, C.setW, Nat.cast_zero], h⟩
  case bound =>
    rintro w _ - - ⟨t, μ'', rfl, -⟩
    exact C.boundW _ _ _ _
  case round =>
    rintro w _ hlt - ⟨t, μ'', rfl, hm⟩
    refine (C.cell_spec u w t μ'' hu hlt hm.rest).mono le_rfl ?_
    rintro _ ⟨t', rfl⟩
    exact ⟨C.atW _ _ _, t', _,
      by simp only [update_frame_setLocal, C.setW, Nat.cast_add, Nat.cast_one],
      hm.step hlt (C.pos_lt u w hu hlt)⟩
  case done =>
    rintro _ - ⟨t, μ'', rfl, hm⟩
    exact ⟨W, t, μ'', rfl, hm.row⟩

/-- **The two loops**: all pairs mark their cells. -/
theorem markPairs (C : MarkCtx lim P d μ base m U W b pos cu cw hiU hiW cell L) (u₀ w₀ t₀ : ℤ)
    (h : Marked μ μ' base m pos W 0 0) :
    Ends lim P d (.for cu hiU (.for cw hiW cell)) ⟨frame (L u₀ w₀ t₀), μ'⟩
      (U * (hiU.cost + (W * (hiW.cost + b + 7) + hiW.cost + 5) + 7) + hiU.cost + 5)
      fun σ' => Marked μ σ'.mem base m pos W U 0 := by
  refine Ends.for
    (fun u σ => ∃ w t μ'', σ = ⟨frame (L u w t), μ''⟩ ∧ Marked μ μ'' base m pos W u 0) U _
    ?start ?round ?done ?bound C.wordU le_rfl
  case start => exact ⟨w₀, t₀, μ', by simp only [update_frame_setLocal, C.setU, Nat.cast_zero], h⟩
  case bound =>
    rintro u _ - - ⟨w, t, μ'', rfl, -⟩
    exact C.boundU _ _ _ _
  case round =>
    rintro u _ hu - ⟨w, t, μ'', rfl, hm⟩
    refine (markRow C hu w t hm).mono le_rfl ?_
    rintro _ ⟨w', t', μ₃, rfl, hm'⟩
    exact ⟨C.atU _ _ _, w', t', μ₃,
      by simp only [update_frame_setLocal, C.setU, Nat.cast_add, Nat.cast_one], hm'⟩
  case done =>
    rintro _ - ⟨w, t, μ'', rfl, hm⟩
    exact hm

end loops

/-! ## Clearing the matrix -/

/-- The loop that clears a matrix: local 0 holds its address base, local t the number m of its
cells, and local c is the counter.  Afterwards the m cells hold 0, and no other cell has changed. -/
theorem clear_spec {μ : ℕ → ℤ} {l : List ℤ} {c t base m : ℕ} {Q : State → Prop}
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : base + m < lim.space) (hc : 0 ≠ c) (ht : t ≠ c)
    (hbase : frame l 0 = base) (hm : frame l t = m)
    (h : ∀ μ', (∀ i < m, μ' (base + i) = 0) → SameOutside μ μ' base m →
      Q ⟨frame (setLocal l c m), μ'⟩) :
    Ends lim P d (.for c (v t) (.store (v 0 +' v c) (k 0))) ⟨frame l, μ⟩ (13 * m + 6) Q := by
  refine Ends.pass (x := t) (y := 0) (dst := base) (n := m) (fun _ => 0)
    (fun j _ => ⟨?_, by simp⟩) ?_ hw (by omega) hm hbase ht hc
  · change ((0 : ℕ) : ℤ) ≤ lim.word
    omega
  · rw [update_frame_setLocal]
    exact h _ (fun i hi => wrote_done hi) (sameOutside_wrote le_rfl)

/-! ## What both routines assume -/

/-- The residues R of the n² weights, all below p, stand at res.  The matrix has m = D n cells at
base, apart from the residues.  The piece {c0, …, c0 + len - 1} lies within the n vertices, and its
len p labels within the D middle vertices. -/
structure WritePre (lim : Limits) (μ : ℕ → ℤ) (base m res n D p c0 len : ℕ) (R : List ℕ) :
    Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  seg : SegN μ res R
  length : R.length = n * n
  lt : ∀ r ∈ R, r < p
  fits : len * p ≤ D
  piece : c0 + len ≤ n
  size : m = D * n
  spaceM : base + m < lim.space
  spaceR : res + n * n < lim.space
  spaceP : 2 * p < lim.space
  apart : Apart base m res (n * n)

namespace WritePre

variable {μ μ' : ℕ → ℤ} {base m res n D p c0 len : ℕ} {R : List ℕ}

/-- The number n of vertices fits in a word. -/
theorem n_le_word (pre : WritePre lim μ base m res n D p c0 len R) : (n : ℤ) ≤ lim.word := by
  have := pre.hw
  have := pre.spaceR
  have := Nat.le_mul_self n
  omega

/-- The length of the piece fits in a word. -/
theorem len_le_word (pre : WritePre lim μ base m res n D p c0 len R) : (len : ℤ) ≤ lim.word := by
  have := pre.n_le_word
  have := pre.piece
  omega

/-- The place of the weight between the vertex u and the c-th member c0 + c of the piece. -/
theorem index_lt (pre : WritePre lim μ base m res n D p c0 len R) {u c : ℕ} (hu : u < n)
    (hc : c < len) : u * n + c0 + c < n * n := by
  have := pre.piece
  have := Nat.mul_add_lt_mul hu (show c0 + c < n by omega)
  omega

/-- The residues can be read at any time. -/
theorem read (pre : WritePre lim μ base m res n D p c0 len R) (h : SameOutside μ μ' base m) {i : ℕ}
    (hi : i < n * n) : μ' (res + i) = (R.getD i 0 : ℕ) := by
  have hap := pre.apart
  have hil : i < R.length := pre.length ▸ hi
  rw [h _ (by omega), pre.seg _ (by simpa using hil), List.getElem_map,
    List.getD_eq_getElem _ 0 hil]

/-- The residues are below p. -/
theorem getD_lt (pre : WritePre lim μ base m res n D p c0 len R) {i : ℕ} (hi : i < n * n) :
    R.getD i 0 < p := by
  have hil : i < R.length := pre.length ▸ hi
  rw [List.getD_eq_getElem _ 0 hil]
  exact pre.lt _ (List.getElem_mem hil)

/-- The label s of the c-th member of the piece is one of the D middle vertices. -/
theorem middle_lt (pre : WritePre lim μ base m res n D p c0 len R) {c s : ℕ} (hc : c < len)
    (hs : s < p) : c * p + s < D :=
  (Nat.mul_add_lt_mul hc hs).trans_le pre.fits

end WritePre

/-! ## The matrix Y -/

namespace WriteY

/-- The local variables of writeY: the arguments y, rbc, n, D, p, c0, len; the number c of the
member of the piece (before that, the counter of the clearing); the vertex b; the residue, then the
label, r; the number D n of cells. -/
abbrev Y : ℕ := 0
@[inherit_doc Y] abbrev RES : ℕ := 1
@[inherit_doc Y] abbrev N : ℕ := 2
@[inherit_doc Y] abbrev DD : ℕ := 3
@[inherit_doc Y] abbrev PR : ℕ := 4
@[inherit_doc Y] abbrev C0 : ℕ := 5
@[inherit_doc Y] abbrev LEN : ℕ := 6
@[inherit_doc Y] abbrev C : ℕ := 7
@[inherit_doc Y] abbrev B : ℕ := 8
@[inherit_doc Y] abbrev R : ℕ := 9
@[inherit_doc Y] abbrev SZ : ℕ := 10

end WriteY

open WriteY in
/-- The pair (c, b) marks its cell: r := rbc[b n + c0 + c]; if r ≠ 0 then r := p - r;
y[(c p + r) n + b] := 1. -/
def writeYCell : Stmt :=
  .set R (M (v RES +' v B *' v N +' v C0 +' v C)) ;;
  .ite (v R =' k 0) .skip (.set R (v PR -' v R)) ;;
  .store (v Y +' (v C *' v PR +' v R) *' v N +' v B) (k 1)

open WriteY in
/-- writeY(y, rbc, n, D, p, c0, len). -/
def writeYBody : Stmt :=
  .set SZ (v DD *' v N) ;;
  .for C (v SZ) (.store (v Y +' v C) (k 0)) ;;
  .for C (v LEN) (.for B (v N) writeYCell)

/-- The time of writeY. -/
def tWriteY (n D len : ℕ) : ℕ := 13 * (D * n) + len * (40 * n + 14) + 16

/-- The label of the row that the pair (c, b) marks. -/
def labY (n p c0 : ℕ) (RBC : List ℕ) (c b : ℕ) : ℕ := (p - RBC.getD (b * n + c0 + c) 0) % p

/-- The cell that the pair (c, b) marks. -/
def posY (n p c0 : ℕ) (RBC : List ℕ) (c b : ℕ) : ℕ := (c * p + labY n p c0 RBC c b) * n + b

/-- Entry i of yList, the matrix Y row by row, is 1 if one of the pairs (c, b) marks the cell i, and
0 if not. -/
theorem getElem_yList {n D p c0 len : ℕ} {RBC : List ℕ} (hp : 0 < p) {i : ℕ}
    (hi : i < (yList n D p c0 len RBC).length) :
    (yList n D p c0 len RBC)[i] = markVal (posY n p c0 RBC) n len 0 i := by
  have hi' : i < D * n := by simpa [yList] using hi
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hi'
  rw [markVal_end
    (i / n / p < len ∧ i / n % p = (p - RBC.getD (i % n * n + c0 + i / n / p) 0) % p)]
  · simp [yList]
  · constructor
    · rintro ⟨h1, h2⟩
      refine ⟨i / n / p, h1, i % n, Nat.mod_lt _ hn, ?_⟩
      rw [posY, labY, ← h2, Nat.mul_comm (i / n / p) p, Nat.div_add_mod, Nat.mul_comm (i / n) n,
        Nat.div_add_mod]
    · rintro ⟨c, hc, b, hb, rfl⟩
      have hl : labY n p c0 RBC c b < p := Nat.mod_lt _ hp
      rw [posY, Nat.mul_add_div_of_lt hb, Nat.mul_add_mod_of_lt hb, Nat.mul_add_div_of_lt hl,
        Nat.mul_add_mod_of_lt hl]
      exact ⟨hc, rfl⟩

section writeY

variable {μ μ' : ℕ → ℤ} {y rbc n D p c0 len : ℕ} {RBC : List ℕ}

/-- The cell of a pair lies in the matrix. -/
theorem posY_lt (pre : WritePre lim μ y (D * n) rbc n D p c0 len RBC) {c b : ℕ} (hc : c < len)
    (hb : b < n) : posY n p c0 RBC c b < D * n := by
  have hp := pre.getD_lt (pre.index_lt hb hc)
  exact Nat.mul_add_lt_mul (pre.middle_lt hc (Nat.mod_lt _ (by omega))) hb

/-- The label, as the program computes it. -/
theorem labY_eq {c b : ℕ} (hr : RBC.getD (b * n + c0 + c) 0 < p) : labY n p c0 RBC c b =
    if RBC.getD (b * n + c0 + c) 0 = 0 then 0 else p - RBC.getD (b * n + c0 + c) 0 := by
  unfold labY
  split_ifs with h
  · rw [h, Nat.sub_zero, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

open WriteY in
/-- **One pair of writeY.** -/
theorem writeYCell_spec (pre : WritePre lim μ y (D * n) rbc n D p c0 len RBC) {c b : ℕ} (t : ℤ)
    (hc : c < len) (hb : b < n) (hrest : SameOutside μ μ' y (D * n)) :
    Ends lim P d writeYCell ⟨frame [y, rbc, n, D, p, c0, len, c, b, t, (D * n : ℕ)], μ'⟩ 32
      fun σ' => ∃ t', σ' = ⟨frame [y, rbc, n, D, p, c0, len, c, b, t', (D * n : ℕ)],
        Function.update μ' (y + posY n p c0 RBC c b) 1⟩ := by
  light_facts pre
  have hidx := pre.index_lt hb hc
  have hread := pre.read hrest hidx
  have hr := pre.getD_lt hidx
  have hlab := labY_eq hr
  have hpos : (c * p + labY n p c0 RBC c b) * n + b < D * n := posY_lt pre hc hb
  have hrow : c * p + labY n p c0 RBC c b < D := pre.middle_lt hc (Nat.mod_lt _ (by omega))
  have hDn : D ≤ D * n := Nat.le_mul_of_pos_right D (by omega)
  have hposZ : ((c : ℤ) * p + labY n p c0 RBC c b) * n + b < D * n := by exact_mod_cast hpos
  have hpos0 : 0 ≤ ((c : ℤ) * p + labY n p c0 RBC c b) * n := by positivity
  have haddr : ((rbc : ℤ) + b * n + c0 + c).toNat = rbc + (b * n + c0 + c) := by omega
  generalize RBC.getD (b * n + c0 + c) 0 = r at hread hr hlab
  -- y[(c p + r) n + b] := 1, once r is the label
  have mark : ∀ s : ℕ, labY n p c0 RBC c b = s →
      Ends lim P d (.store (v Y +' (v C *' v PR +' v R) *' v N +' v B) (k 1))
        ⟨frame [y, rbc, n, D, p, c0, len, c, b, s, (D * n : ℕ)], μ'⟩ 13 fun σ' =>
          ∃ t', σ' = ⟨frame [y, rbc, n, D, p, c0, len, c, b, t', (D * n : ℕ)],
            Function.update μ' (y + posY n p c0 RBC c b) 1⟩ := by
    rintro _ rfl
    exact Ends.storeTo (y + posY n p c0 RBC c b) 1 ⟨_, rfl⟩
      (by light_side [posY])
  -- r := rbc[b n + c0 + c]
  light_set (r : ℕ) using haddr, hread
  -- if r ≠ 0 then r := p - r
  refine Ends.next 8 (Ends.iteLast (fun h0 => Ends.skip (mark _ ?_)) fun h0 =>
    Ends.setTo (p - r : ℕ) (mark _ ?_))
  · have h0 : r = 0 := by simpa using h0
    rw [hlab, if_pos h0, h0]
  · have h0 : r ≠ 0 := by simpa using h0
    rw [hlab, if_neg h0]

open WriteY in
/-- The two loops of writeY are loops that mark cells. -/
theorem writeY_markCtx (pre : WritePre lim μ y (D * n) rbc n D p c0 len RBC) :
    MarkCtx lim P d μ y (D * n) len n 32 (posY n p c0 RBC) C B (v LEN) (v N) writeYCell
      fun c b t => [y, rbc, n, D, p, c0, len, c, b, t, (D * n : ℕ)] where
  wordU := pre.len_le_word
  wordW := pre.n_le_word
  atU _ _ _ := rfl
  atW _ _ _ := rfl
  setU _ _ _ _ := rfl
  setW _ _ _ _ := rfl
  boundU _ _ _ _ := by simp
  boundW _ _ _ _ := by simp
  pos_lt _ _ hc hb := posY_lt pre hc hb
  cell_spec _ _ t _ hc hb hrest := writeYCell_spec pre t hc hb hrest

open WriteY in
/-- **writeY** writes the matrix Y and changes nothing else. -/
theorem writeY_spec (pre : WritePre lim μ y (D * n) rbc n D p c0 len RBC) :
    Ends lim P d writeYBody ⟨frame [y, rbc, n, D, p, c0, len], μ⟩ (tWriteY n D len) fun σ' =>
      Seg σ'.mem y (yList n D p c0 len RBC) ∧ SameOutside μ σ'.mem y (D * n) := by
  light_facts pre
  unfold tWriteY
  -- sz := D n
  light_set (D * n : ℕ)
  -- for c < sz: y[c] := 0
  refine Ends.next _
    (clear_spec pre.hw pre.spaceM (by decide) (by decide) rfl rfl fun μ' hzero hrest => ?_)
  -- for c < len: for b < n: the pair (c, b) marks its cell
  refine ((markPairs (writeY_markCtx pre) _ _ _ (.start hzero hrest)).mono ?_ fun σ' hm =>
    ⟨hm.seg (by simp [yList]) fun i hi => getElem_yList ?_ hi, hm.rest⟩)
  · light_time
  · have hi' : i < D * n := by simpa [yList] using hi
    have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hi'
    have hl : 0 < RBC.length := by rw [pre.length]; exact Nat.mul_pos hn hn
    have := pre.lt _ (List.getElem_mem hl)
    omega

end writeY

/-! ## The matrix X -/

namespace WriteX

/-- The local variables of writeX: the arguments x, rac, n, D, p, c0, len, rho; the vertex a (before
that, the counter of the clearing); the number c of the member of the piece; the label t; the number
n D of cells. -/
abbrev X : ℕ := 0
@[inherit_doc X] abbrev RES : ℕ := 1
@[inherit_doc X] abbrev N : ℕ := 2
@[inherit_doc X] abbrev DD : ℕ := 3
@[inherit_doc X] abbrev PR : ℕ := 4
@[inherit_doc X] abbrev C0 : ℕ := 5
@[inherit_doc X] abbrev LEN : ℕ := 6
@[inherit_doc X] abbrev RHO : ℕ := 7
@[inherit_doc X] abbrev A : ℕ := 8
@[inherit_doc X] abbrev C : ℕ := 9
@[inherit_doc X] abbrev T : ℕ := 10
@[inherit_doc X] abbrev SZ : ℕ := 11

end WriteX

open WriteX in
/-- The pair (a, c) marks its cell: t := rac[a n + c0 + c] + rho; if p ≤ t then t := t - p;
x[a D + c p + t] := 1. -/
def writeXCell : Stmt :=
  .set T (M (v RES +' v A *' v N +' v C0 +' v C) +' v RHO) ;;
  .ite (v T <' v PR) .skip (.set T (v T -' v PR)) ;;
  .store (v X +' v A *' v DD +' v C *' v PR +' v T) (k 1)

open WriteX in
/-- writeX(x, rac, n, D, p, c0, len, rho). -/
def writeXBody : Stmt :=
  .set SZ (v N *' v DD) ;;
  .for A (v SZ) (.store (v X +' v A) (k 0)) ;;
  .for A (v N) (.for C (v LEN) writeXCell)

/-- The time of writeX. -/
def tWriteX (n D len : ℕ) : ℕ := 13 * (n * D) + n * (42 * len + 14) + 16

/-- The label of the column that the pair (a, c) marks. -/
def labX (n p c0 rho : ℕ) (RAC : List ℕ) (a c : ℕ) : ℕ := (RAC.getD (a * n + c0 + c) 0 + rho) % p

/-- The cell that the pair (a, c) marks. -/
def posX (n D p c0 rho : ℕ) (RAC : List ℕ) (a c : ℕ) : ℕ :=
  a * D + (c * p + labX n p c0 rho RAC a c)

/-- Entry i of xList, the matrix X row by row, is 1 if one of the pairs (a, c) marks the cell i, and
0 if not. -/
theorem getElem_xList {n D p c0 len rho : ℕ} {RAC : List ℕ} (hp : 0 < p) (hD : len * p ≤ D) {i : ℕ}
    (hi : i < (xList n D p c0 len rho RAC).length) :
    (xList n D p c0 len rho RAC)[i] = markVal (posX n D p c0 rho RAC) len n 0 i := by
  have hi' : i < n * D := by simpa [xList] using hi
  rw [markVal_end
    (i % D / p < len ∧ i % D % p = (RAC.getD (i / D * n + c0 + i % D / p) 0 + rho) % p)]
  · simp [xList]
  · constructor
    · rintro ⟨h1, h2⟩
      refine ⟨i / D, Nat.div_lt_of_lt_mul' hi', i % D / p, h1, ?_⟩
      rw [posX, labX, ← h2, Nat.mul_comm (i % D / p) p, Nat.div_add_mod, Nat.mul_comm (i / D) D,
        Nat.div_add_mod]
    · rintro ⟨a, ha, c, hc, rfl⟩
      have hl : labX n p c0 rho RAC a c < p := Nat.mod_lt _ hp
      have hcol : c * p + labX n p c0 rho RAC a c < D := (Nat.mul_add_lt_mul hc hl).trans_le hD
      rw [posX, Nat.mul_add_div_of_lt hcol, Nat.mul_add_mod_of_lt hcol, Nat.mul_add_div_of_lt hl,
        Nat.mul_add_mod_of_lt hl]
      exact ⟨hc, rfl⟩

section writeX

variable {μ μ' : ℕ → ℤ} {x rac n D p c0 len rho : ℕ} {RAC : List ℕ}

/-- The cell of a pair lies in the matrix. -/
theorem posX_lt (pre : WritePre lim μ x (n * D) rac n D p c0 len RAC) {a c : ℕ} (ha : a < n)
    (hc : c < len) : posX n D p c0 rho RAC a c < n * D := by
  have hp := pre.getD_lt (pre.index_lt ha hc)
  exact Nat.mul_add_lt_mul ha (pre.middle_lt hc (Nat.mod_lt _ (by omega)))

/-- The label, as the program computes it. -/
theorem labX_eq {a c : ℕ} (hr : RAC.getD (a * n + c0 + c) 0 < p) (hrho : rho < p) :
    labX n p c0 rho RAC a c = if RAC.getD (a * n + c0 + c) 0 + rho < p
      then RAC.getD (a * n + c0 + c) 0 + rho else RAC.getD (a * n + c0 + c) 0 + rho - p := by
  unfold labX
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

open WriteX in
/-- **One pair of writeX.** -/
theorem writeXCell_spec (pre : WritePre lim μ x (n * D) rac n D p c0 len RAC) (hrho : rho < p)
    {a c : ℕ} (t : ℤ) (ha : a < n) (hc : c < len) (hrest : SameOutside μ μ' x (n * D)) :
    Ends lim P d writeXCell ⟨frame [x, rac, n, D, p, c0, len, rho, a, c, t, (n * D : ℕ)], μ'⟩ 34
      fun σ' => ∃ t', σ' = ⟨frame [x, rac, n, D, p, c0, len, rho, a, c, t', (n * D : ℕ)],
        Function.update μ' (x + posX n D p c0 rho RAC a c) 1⟩ := by
  light_facts pre
  have hidx := pre.index_lt ha hc
  have hread := pre.read hrest hidx
  have hr := pre.getD_lt hidx
  have hlab := labX_eq hr hrho
  have hpos : a * D + (c * p + labX n p c0 rho RAC a c) < n * D := posX_lt pre ha hc
  have haddr : ((rac : ℤ) + a * n + c0 + c).toNat = rac + (a * n + c0 + c) := by omega
  generalize RAC.getD (a * n + c0 + c) 0 = r at hread hr hlab
  -- x[a D + c p + t] := 1, once t is the label
  have mark : ∀ s : ℕ, labX n p c0 rho RAC a c = s →
      Ends lim P d (.store (v X +' v A *' v DD +' v C *' v PR +' v T) (k 1))
        ⟨frame [x, rac, n, D, p, c0, len, rho, a, c, s, (n * D : ℕ)], μ'⟩ 13 fun σ' =>
          ∃ t', σ' = ⟨frame [x, rac, n, D, p, c0, len, rho, a, c, t', (n * D : ℕ)],
            Function.update μ' (x + posX n D p c0 rho RAC a c) 1⟩ := by
    rintro _ rfl
    exact Ends.storeTo (x + posX n D p c0 rho RAC a c) 1 ⟨_, rfl⟩ (by light_side [posX])
  -- t := rac[a n + c0 + c] + rho
  light_set (r + rho : ℕ) using haddr, hread
  -- if p ≤ t then t := t - p
  refine Ends.next 8 (Ends.iteLast (fun h0 => Ends.skip (mark _ ?_)) fun h0 => ?_)
  · have h0 : r + rho < p := by simp at h0; omega
    rw [hlab, if_pos h0]
  · have h0 : ¬ r + rho < p := by simp at h0; omega
    exact Ends.setTo (r + rho - p : ℕ) (mark _ (by rw [hlab, if_neg h0]))

open WriteX in
/-- The two loops of writeX are loops that mark cells. -/
theorem writeX_markCtx (pre : WritePre lim μ x (n * D) rac n D p c0 len RAC) (hrho : rho < p) :
    MarkCtx lim P d μ x (n * D) n len 34 (posX n D p c0 rho RAC) A C (v N) (v LEN) writeXCell
      fun a c t => [x, rac, n, D, p, c0, len, rho, a, c, t, (n * D : ℕ)] where
  wordU := pre.n_le_word
  wordW := pre.len_le_word
  atU _ _ _ := rfl
  atW _ _ _ := rfl
  setU _ _ _ _ := rfl
  setW _ _ _ _ := rfl
  boundU _ _ _ _ := by simp
  boundW _ _ _ _ := by simp
  pos_lt _ _ ha hc := posX_lt pre ha hc
  cell_spec _ _ t _ ha hc hrest := writeXCell_spec pre hrho t ha hc hrest

open WriteX in
/-- **writeX** writes the matrix X and changes nothing else. -/
theorem writeX_spec (pre : WritePre lim μ x (n * D) rac n D p c0 len RAC) (hrho : rho < p) :
    Ends lim P d writeXBody ⟨frame [x, rac, n, D, p, c0, len, rho], μ⟩ (tWriteX n D len) fun σ' =>
      Seg σ'.mem x (xList n D p c0 len rho RAC) ∧ SameOutside μ σ'.mem x (n * D) := by
  light_facts pre
  unfold tWriteX
  -- sz := n D
  light_set (n * D : ℕ)
  -- for a < sz: x[a] := 0
  refine Ends.next _
    (clear_spec pre.hw pre.spaceM (by decide) (by decide) rfl rfl fun μ' hzero hrest => ?_)
  -- for a < n: for c < len: the pair (a, c) marks its cell
  refine ((markPairs (writeX_markCtx pre hrho) _ _ _ (.start hzero hrest)).mono ?_ fun σ' hm =>
    ⟨hm.seg (by simp [xList]) fun i hi => getElem_xList (by omega) pre.fits hi, hm.rest⟩)
  light_time

end writeX

end Light.Sec3
