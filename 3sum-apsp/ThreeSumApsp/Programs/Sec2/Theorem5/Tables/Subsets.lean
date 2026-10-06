/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
public import ThreeSumApsp.Spec.Sec2.Theorem5.SubsetTable

/-!
# The table of subsets

Section 2.3.4: "We fix K₀² ≤ K distinct subsets of {1, …, L} of size m, one for each block product
of the grid, the same in every tile."  Section 2.4.4 counts the time to "list the K₀² subsets".
subsets(L, m, KK, mask), which is called with KK = K₀², writes the first KK masks of the enumeration
`Spec.unrank`, one after the other, as 0/1 cells from mask.  Row 0 is m ones followed by zeros
(`firstRow_spec`).  Each further row is made from the row before it: one pass from the end of the
old row finds the last 1 that is followed by a 0 (`scan_spec`), and one pass writes the new row
(`write_spec`).  There is no arithmetic on the entries, and a row takes O(L) steps.  What the two
passes compute is described without a program by `scanAt` and `newCell`, with the facts
`bit_unrank_succ` and `scanAt_fits`; here each pass is connected with this description,
`tableRow_spec` treats one row, and `subsetTable_spec` runs through the rows.  `subsets_entry` is
the specification that the callers of the procedure assume.
-/

@[expose] public section

open ThreeSumApsp.Spec.Subsets

namespace Light.Sec2.Subsets

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

/-- The local variables of subsets: Levels = L, Size = m, Rows = KK, Table = mask (the arguments);
Row is the number of the current row and Addr its address; Phase, Ones and Pos are the state of the
scan (phase, number of ones at the end, position found); Cell is the counter of the inner loops. -/
abbrev Levels : ℕ := 0
@[inherit_doc Levels] abbrev Size : ℕ := 1
@[inherit_doc Levels] abbrev Rows : ℕ := 2
@[inherit_doc Levels] abbrev Table : ℕ := 3
@[inherit_doc Levels] abbrev Row : ℕ := 4
@[inherit_doc Levels] abbrev Addr : ℕ := 5
@[inherit_doc Levels] abbrev Phase : ℕ := 6
@[inherit_doc Levels] abbrev Ones : ℕ := 7
@[inherit_doc Levels] abbrev Pos : ℕ := 8
@[inherit_doc Levels] abbrev Cell : ℕ := 9

/-- One cell of the first row: 1 for the first m cells, then 0. -/
def firstRowRound : Stmt :=
  .ite (v Cell <' v Size) (.store (v Addr +' v Cell) (k 1)) (.store (v Addr +' v Cell) (k 0))

/-- The first row: m ones, then zeros. -/
def firstRowLoop : Stmt := .for Cell (v Levels) firstRowRound

/-- One round of the scan: the cell number Cell from the end of the row before the current one. -/
def scanRound : Stmt :=
  .ite (v Phase <' k 1)
    (.ite (M (v Addr -' k 1 -' v Cell) <' k 1) (.set Phase (k 1)) (.set Ones (v Ones +' k 1)))
    (.ite (v Phase <' k 2)
      (.ite (M (v Addr -' k 1 -' v Cell) <' k 1) .skip
        (.set Phase (k 2) ;; .set Pos (v Levels -' k 1 -' v Cell)))
      .skip)

/-- The scan of the row before the current one, from its end. -/
def scanLoop : Stmt :=
  .set Phase (k 0) ;; .set Ones (k 0) ;; .set Pos (k 0) ;; .for Cell (v Levels) scanRound

/-- One cell of the new row, from the row before it and the result of the scan. -/
def writeRound : Stmt :=
  .ite (v Cell <' v Pos) (.store (v Addr +' v Cell) (M (v Addr -' v Levels +' v Cell)))
    (.ite (v Cell <' v Pos +' k 1) (.store (v Addr +' v Cell) (k 0))
      (.ite (v Cell <' v Pos +' k 2 +' v Ones) (.store (v Addr +' v Cell) (k 1))
        (.store (v Addr +' v Cell) (k 0))))

/-- The new row, from the row before it and the result of the scan. -/
def writeLoop : Stmt := .for Cell (v Levels) writeRound

/-- A further row, from the row before it. -/
def nextRow : Stmt := scanLoop ;; writeLoop

/-- One round of the loop over the rows. -/
def tableRow : Stmt :=
  .ite (v Row <' k 1) firstRowLoop nextRow ;;
  .set Row (v Row +' k 1) ;; .set Addr (v Addr +' v Levels)

/-- subsets(L, m, KK, mask). -/
def subsetTableBody : Stmt :=
  .set Row (k 0) ;; .set Addr (v Table) ;; .while (v Row <' v Rows) tableRow

/-! ## The three passes -/

/-- The list of the local variables. -/
abbrev locals (L m KK mask s a : ℕ) (S : Scan) (j : ℤ) : List ℤ :=
  [L, m, KK, mask, s, a, S.phase, S.ones, S.pos, j]

/-- The row of L cells that ends just before the address a. -/
abbrev prevRow (μ : ℕ → ℤ) (a L : ℕ) : ℕ → ℤ := fun q => μ (a - L + q)

/-- The row that the writing pass forms from the row before the address a and the result S of its
scan. -/
abbrev newRow (μ : ℕ → ℤ) (a L : ℕ) (S : Scan) : ℕ → ℤ := fun r => newCell S (prevRow μ a L r) r

variable {μ : ℕ → ℤ} {L m KK mask s a : ℕ} {S : Scan} {j₀ : ℤ} {T : ℕ} {Q : State → Prop}

/-- **The first row**: the pass writes m ones and then zeros to the L cells from a. -/
theorem firstRow_spec (std : Std lim) (ha : a + L ≤ lim.space)
    (done : Q ⟨frame (locals L m KK mask s a S L), wrote μ a (fun r => if r < m then 1 else 0) L⟩)
    (hT : 17 * L + 6 ≤ T) :
    Ends lim P d firstRowLoop ⟨frame (locals L m KK mask s a S j₀), μ⟩ T Q := by
  light_facts std
  -- for Cell < L
  refine Ends.forFrame (fun j μ' => μ' = wrote μ a (fun r => if r < m then 1 else 0) j) L
    wrote_zero.symm ?round (fun μ' h => h ▸ done) (hT := by simp [firstRowRound]; omega)
  rintro j _ hj rfl
  unfold firstRowRound
  -- if Cell < m then mem[Addr + Cell] := 1 else mem[Addr + Cell] := 0
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_)
  · light_store (a + j) 1
    exact ⟨rfl, by rw [← wrote_succ, if_pos (by simpa using hc)]⟩
  · light_store (a + j) 0
    exact ⟨rfl, by rw [← wrote_succ, if_neg (by simpa using hc)]⟩

/-- One round of the scan does to the local variables what `scanStep` says of the cell number j from
the end of the row of L cells that ends just before the address a. -/
theorem scanRound_runs (std : Std lim) (hLa : L ≤ a) (ha : a ≤ lim.space) {j : ℕ} (hj : j < L)
    (hones : 0 ≤ S.ones ∧ S.ones ≤ j) :
    scanRound.Runs lim ⟨frame (locals L m KK mask s a S j), μ⟩ fun σ' => σ' =
      ⟨frame (locals L m KK mask s a (scanStep (μ (a - 1 - j)) ((L : ℤ) - 1 - j) S) j), μ⟩ := by
  light_facts std
  have haddr : ((a : ℤ) - 1 - j).toNat = a - 1 - j := by omega
  unfold scanRound scanStep
  by_cases hcount : S.phase < 1
  · -- Phase 0: a zero ends the counting, a one is counted.
    rw [if_pos hcount]
    refine .ite_pos ?_
    by_cases hx : μ (a - 1 - j) < 1
    · rw [if_pos hx]
      exact .ite_pos ⟨by light_side, by simp [update_frame_setLocal]⟩ (by simpa [haddr] using hx)
    · rw [if_neg hx]
      exact .ite_neg ⟨by light_side, by simp [update_frame_setLocal]⟩ (by simpa [haddr] using hx)
  · rw [if_neg hcount]
    refine .ite_neg ?_
    by_cases hpass : S.phase < 2
    · -- Phase 1: a zero is passed, a one is what the scan looks for.
      rw [if_pos hpass]
      refine .ite_pos ?_
      by_cases hx : μ (a - 1 - j) < 1
      · rw [if_pos hx]
        exact .ite_pos ⟨trivial, rfl⟩ (by simpa [haddr] using hx)
      · rw [if_neg hx]
        exact .ite_neg ⟨by light_side, by simp [update_frame_setLocal]⟩ (by simpa [haddr] using hx)
    · -- Phase 2: nothing is left to do.
      rw [if_neg hpass]
      exact .ite_neg ⟨trivial, rfl⟩

/-- **The scan** of the row of L cells that ends just before the address a changes no cell and
leaves its result in the local variables. -/
theorem scan_spec (std : Std lim) (hLa : L ≤ a) (ha : a ≤ lim.space)
    (done : Q ⟨frame (locals L m KK mask s a (scanAt (prevRow μ a L) L L) L), μ⟩)
    (hT : 33 * L + 12 ≤ T) :
    Ends lim P d scanLoop ⟨frame (locals L m KK mask s a S j₀), μ⟩ T Q := by
  light_facts std
  -- Phase := 0; Ones := 0; Pos := 0
  light_set 0
  light_set 0
  light_set 0
  -- for Cell < L
  refine Ends.for (fun j σ =>
      σ = ⟨frame (locals L m KK mask s a (scanAt (prevRow μ a L) L j) j), μ⟩)
    L _ ?start (fun j σ hj _ hσ => Ends.block ?round le_rfl) ?done ?bound
    (hT := by simp [scanRound]; omega)
  case start => simp [update_frame_setLocal, scanAt]
  case round =>
    subst hσ
    refine (scanRound_runs std hLa ha hj (scanAt_ones_le _ L j)).mono ?_
    rintro _ rfl
    rw [scanAt, prevRow, show a - L + (L - 1 - j) = a - 1 - j by omega]
    simp [update_frame_setLocal]
  case done => exact fun _ _ h => h ▸ done
  case bound => exact fun j _ _ _ h => h ▸ by light_side

/-- **The writing pass** writes the new row to the L cells from a, from the row of L cells before
it and the result S of the scan. -/
theorem write_spec (std : Std lim) (hLa : L ≤ a) (ha : a + L ≤ lim.space)
    (hS : S.Fits L) (done : Q ⟨frame (locals L m KK mask s a S L), wrote μ a (newRow μ a L S) L⟩)
    (hT : 31 * L + 6 ≤ T) :
    Ends lim P d writeLoop ⟨frame (locals L m KK mask s a S j₀), μ⟩ T Q := by
  light_facts std
  unfold Scan.Fits at hS
  -- for Cell < L
  refine Ends.forFrame (fun j μ' => μ' = wrote μ a (newRow μ a L S) j) L wrote_zero.symm
    ?round (fun μ' h => h ▸ done) (hT := by simp [writeRound]; omega)
  rintro j _ hj rfl
  -- The cell of the old row has not been overwritten.
  have haddr : ((a : ℤ) - L + j).toNat = a - L + j := by omega
  have hold : wrote μ a (newRow μ a L S) j (a - L + j) = μ (a - L + j) :=
    wrote_rest (Or.inl (by omega))
  unfold writeRound
  rw [← wrote_succ, newRow, newCell]
  -- if Cell < Pos then mem[Addr + Cell] := mem[Addr - L + Cell] else if Cell < Pos + 1 then 0
  -- else if Cell < Pos + 2 + Ones then 1 else 0: the four cases of newCell
  refine Ends.iteLast (fun c₁ => ?_) fun c₁ => Ends.iteLast (fun c₂ => ?_) fun c₂ =>
    Ends.iteLast (fun c₃ => ?_) fun c₃ => ?_
  · light_store (a + j) (μ (a - L + j)) using haddr, hold
    exact ⟨rfl, by rw [if_pos (by simpa using c₁)]⟩
  · light_store (a + j) 0
    exact ⟨rfl, by rw [if_neg (by simpa using c₁), if_pos (by simpa using c₂)]⟩
  · light_store (a + j) 1
    exact ⟨rfl, by
      rw [if_neg (by simpa using c₁), if_neg (by simpa using c₂), if_pos (by simpa using c₃)]⟩
  · light_store (a + j) 0
    exact ⟨rfl, by
      rw [if_neg (by simpa using c₁), if_neg (by simpa using c₂), if_neg (by simpa using c₃)]⟩

/-- **A further row**: the two passes write the new row to the L cells from a, from the row of L
cells before it, if the result of the scan leaves room. -/
theorem nextRow_spec (std : Std lim) (hLa : L ≤ a) (ha : a + L ≤ lim.space)
    (hroom : (scanAt (prevRow μ a L) L L).Fits L)
    (done : Q ⟨frame (locals L m KK mask s a (scanAt (prevRow μ a L) L L) L),
      wrote μ a (newRow μ a L (scanAt (prevRow μ a L) L L)) L⟩)
    (hT : 64 * L + 18 ≤ T) :
    Ends lim P d nextRow ⟨frame (locals L m KK mask s a S j₀), μ⟩ T Q :=
  Ends.next _ (scan_spec std hLa (by omega) (write_spec std hLa ha hroom done (by omega)) le_rfl)

/-! ## The loop over the rows -/

/-- The state before row number s is written: the rows before it stand in the table, and no cell
outside the table has changed. -/
def RowsDone (μ : ℕ → ℤ) (L m KK mask s : ℕ) (σ : State) : Prop :=
  ∃ (S : Scan) (j : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame (locals L m KK mask s (mask + s * L) S j), μ'⟩ ∧
    (∀ t < s, SegB μ' (mask + t * L) (Spec.unrank L m t)) ∧ SameOutside μ μ' mask (KK * L)

/-- The time of one round of the loop over the rows. -/
def tRow (L : ℕ) : ℕ := 64 * L + 30

/-- The end of a round: row number s has been written, and the number and the address of the row
move on. -/
private theorem rowDone_spec (std : Std lim) (hmask : mask + KK * L ≤ lim.space)
    (hKK : (KK : ℤ) ≤ lim.word) (hs : s < KK) {μ' : ℕ → ℤ} {f : ℕ → ℤ} {j : ℤ}
    (hrows : ∀ t < s, SegB μ' (mask + t * L) (Spec.unrank L m t))
    (same : SameOutside μ μ' mask (KK * L))
    (hf : ∀ r < L, f r = bit ((Spec.unrank L m s).getD r false))
    (hT : 8 ≤ T := by light_time) :
    Ends lim P d (.set Row (v Row +' k 1) ;; .set Addr (v Addr +' v Levels))
      ⟨frame (locals L m KK mask s (mask + s * L) S j), wrote μ' (mask + s * L) f L⟩ T
      (RowsDone μ L m KK mask (s + 1)) := by
  light_facts std
  have hroom : s * L + L ≤ KK * L := Nat.mul_add_le_mul hs le_rfl
  -- Row := Row + 1; Addr := Addr + L
  light_set (s + 1 : ℕ)
  light_set (mask + (s + 1) * L : ℕ) using Nat.succ_mul
  refine ⟨S, j, _, rfl, fun t ht => ?_,
      same.trans ((sameOutside_wrote le_rfl).mono (by omega) (by omega))⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
  · -- An earlier row lies before the cells that were written.
    have hbefore : t * L + L ≤ s * L := Nat.mul_add_le_mul ht le_rfl
    refine Seg.of_sameOutside (hrows t ht) (sameOutside_wrote le_rfl) (Or.inl ?_)
    rw [List.length_map, Spec.length_unrank]
    omega
  · -- The new row.
    intro r hr
    rw [List.length_map, Spec.length_unrank] at hr
    rw [wrote_done hr, hf r hr, List.getElem_map,
      List.getD_eq_getElem _ _ (by rwa [Spec.length_unrank])]
    rfl

/-- **One round of the loop over the rows** writes row number `s`, the mask number `s`. -/
theorem tableRow_spec (std : Std lim) (hmask : mask + KK * L ≤ lim.space) (hm : m ≤ L)
    (hKK : KK ≤ L.choose m) (hKL : ((KK + L : ℕ) : ℤ) ≤ lim.word) (hs : s < KK) {σ : State}
    (h : RowsDone μ L m KK mask s σ) :
    Ends lim P d tableRow σ (tRow L) (RowsDone μ L m KK mask (s + 1)) := by
  obtain ⟨S, j, μ', rfl, hrows, same⟩ := h
  light_facts std
  push_cast at hKL
  have hroom : s * L + L ≤ KK * L := Nat.mul_add_le_mul hs le_rfl
  unfold tableRow tRow
  -- if Row < 1
  refine Ends.iteThen (fun hc => ?_) (fun hc => ?_)
  · -- The first row.
    obtain rfl : s = 0 := by simp at hc; omega
    refine Ends.next _ (firstRow_spec std (by omega) ?_ le_rfl)
    exact rowDone_spec std hmask (by omega) hs hrows same fun r hr => (bit_unrank_zero hm hr).symm
  · -- A further row, from the row before it.
    obtain ⟨p, rfl⟩ : ∃ p, s = p + 1 := ⟨s - 1, by simp at hc; omega⟩
    have hsucc : (p + 1) * L = p * L + L := Nat.succ_mul p L
    have hprev : ∀ q < L, prevRow μ' (mask + (p + 1) * L) L q
        = bit ((Spec.unrank L m p).getD q false) := fun q hq => by
      rw [prevRow, show mask + (p + 1) * L - L + q = mask + p * L + q by omega]
      exact SegB.get (hrows p (by omega)) (by rwa [Spec.length_unrank])
    have hnext : p + 1 < L.choose m := by omega
    refine Ends.next _ (nextRow_spec std (by omega) (by omega) (scanAt_fits hnext hprev) ?_ le_rfl)
    exact rowDone_spec std hmask (by omega) hs hrows same fun r hr =>
      (bit_unrank_succ hnext hprev hr).symm

/-- **subsets** writes the table and changes nothing else. -/
theorem subsetTable_spec (std : Std lim) (hmask : mask + KK * L ≤ lim.space) (hm : m ≤ L)
    (hKK : KK ≤ L.choose m) (hKL : ((KK + L : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d subsetTableBody ⟨frame [L, m, KK, mask], μ⟩ (64 * ((KK + 1) * (L + 1))) fun σ' =>
      (∀ s < KK, SegB σ'.mem (mask + s * L) (Spec.unrank L m s)) ∧
        SameOutside μ σ'.mem mask (KK * L) := by
  light_facts std
  -- Row := 0; Addr := mask
  light_set 0
  light_set mask
  -- while Row < KK; the KK rounds take KK (64 L + 34) steps
  refine Ends.whileConst (RowsDone μ L m KK mask) KK (tRow L) ?start ?round ?done
    (by simp [tRow]; ring_nf; omega)
  case start =>
    refine ⟨⟨0, 0, 0⟩, 0, μ, ?_, fun t ht => absurd ht (by omega), .refl⟩
    -- The state of the scan and the counter of the inner loops start at 0.
    simp only [setLocal, Nat.zero_mul, Nat.add_zero]
    rw [← frame_append_zeros _ 4]
    rfl
  case round =>
    intro s σ hs h
    have hrow := tableRow_spec (P := P) (d := d) std hmask hm hKK hKL hs h
    obtain ⟨S, j, μ', rfl, -⟩ := h
    push_cast at hKL
    exact ⟨by light_side, by light_side, hrow⟩
  case done =>
    rintro _ ⟨S, j, μ', rfl, hrows, same⟩
    push_cast at hKL
    exact ⟨by light_side, by light_side, hrows, same⟩

end Light.Sec2.Subsets

namespace Light.Sec2

open ThreeSumApsp Subsets

variable {lim : Limits} {P : Program}

/-- **The specification that the callers of subsets assume.** -/
theorem subsets_entry (std : Std lim) (hP : P[pSubsets]? = some subsetTableBody) {c : ℕ}
    (hc : 64 ≤ c) : SubsetsSpec lim P c :=
  fun _ _ _ _ _ hmask hm hKK hKL _ _ =>
    .mono_const (.of_body hP (subsetTable_spec std hmask hm hKK hKL)) hc

end Light.Sec2
