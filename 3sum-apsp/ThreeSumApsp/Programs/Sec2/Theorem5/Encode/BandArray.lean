/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.BandArrayFacts

/-!
# The input array of a band (Section 2.3.4)

Section 2.3.3: "a[u] := X_Q[u], b[v] := Y_Q[v] for all the left strings u and the right strings v
whose inner set Q has exactly m elements, and a[u] := 0, b[v] := 0 at every other string"; in
Section 2.3.4, X_Q and Y_Q are the row block and the column block of the block product with subset
Q.  bandArray writes this input array for a row band of X or a column band of Y.  The array is
laid out by the codes of the left (right) strings and filled in the order of the tuples: the
procedure clears the array, and then, for every block product (g, h) of a tile, every row r of the
block and every column k, it computes the code of the string digit by digit and copies one entry of
the matrix.

The proof goes from the inside to the outside, one lemma for the body of each loop and one for the
loop: a level of the code (`bandLevel_spec`, `bandCodeLoop_spec`), an entry (`bandCell_spec`,
`bandColLoop_spec`), a row of a block (`bandRow_spec`, `bandRowLoop_spec`), a block product
(`bandRows_spec`, `bandBlock_spec`, `bandHLoop_spec`, `bandGLoop_spec`), and the whole procedure
(`bandArray_spec`, within the time `bandArray_time`).  The four outer loops keep the same fact about
the memory: cells of the array are overwritten only with entries of the target list
(`OverwrittenWith`), and the cells of the tuples handled so far are right (`Covered`).  So they are
four cases of one lemma, `coverLoop`.  `bandArrayL_entry` and `bandArrayR_entry`, the cases of X and
of Y, are the specifications that the callers of the procedure assume.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec2

/-! ## The program -/

namespace Band

/-- The local variables of bandArray.  The arguments: `Levels` = L, `Size` = m, `Rows` = N, `Cols` =
D, `NumBlocks` = K0, `Width` = N0, `Cells` = S7, `BandNo` = β, `Side` = side; `Source` is the
address of the matrix, `StepRow` and `StepCol` the steps from row to row and from column to column;
`MaskTable`, `Digits3`, `Digits4` and `Dest` are the addresses of the table of subsets, of the two
tables of digits and of the array.  Then, by the depth of the loop that uses them: `PosG` = g (also
the counter of the clearing loop); `PosH` = h, `BlockIdx` the number of the block, `MaskRow` the
address of the mask of the subset; `Offset` = r, `Row` the number of the row of the matrix; `Col` =
k, `CodeAcc` the code, `Outer` and `Inner` the addresses of the next outer and of the next inner
digit, `CurLevel` the level. -/
abbrev Levels : ℕ := 0
@[inherit_doc Levels] abbrev Size : ℕ := 1
@[inherit_doc Levels] abbrev Rows : ℕ := 2
@[inherit_doc Levels] abbrev Cols : ℕ := 3
@[inherit_doc Levels] abbrev NumBlocks : ℕ := 4
@[inherit_doc Levels] abbrev Width : ℕ := 5
@[inherit_doc Levels] abbrev Cells : ℕ := 6
@[inherit_doc Levels] abbrev BandNo : ℕ := 7
@[inherit_doc Levels] abbrev Side : ℕ := 8
@[inherit_doc Levels] abbrev Source : ℕ := 9
@[inherit_doc Levels] abbrev StepRow : ℕ := 10
@[inherit_doc Levels] abbrev StepCol : ℕ := 11
@[inherit_doc Levels] abbrev MaskTable : ℕ := 12
@[inherit_doc Levels] abbrev Digits3 : ℕ := 13
@[inherit_doc Levels] abbrev Digits4 : ℕ := 14
@[inherit_doc Levels] abbrev Dest : ℕ := 15
@[inherit_doc Levels] abbrev PosG : ℕ := 16
@[inherit_doc Levels] abbrev PosH : ℕ := 17
@[inherit_doc Levels] abbrev BlockIdx : ℕ := 18
@[inherit_doc Levels] abbrev MaskRow : ℕ := 19
@[inherit_doc Levels] abbrev Offset : ℕ := 20
@[inherit_doc Levels] abbrev Row : ℕ := 21
@[inherit_doc Levels] abbrev Col : ℕ := 22
@[inherit_doc Levels] abbrev CodeAcc : ℕ := 23
@[inherit_doc Levels] abbrev Outer : ℕ := 24
@[inherit_doc Levels] abbrev Inner : ℕ := 25
@[inherit_doc Levels] abbrev CurLevel : ℕ := 26

end Band

open Band

/-- One level: Horner's rule in base 7, with the next outer digit, or 3 plus the next inner
digit. -/
def bandLevel : Stmt :=
  .ite (M (v MaskRow +' v CurLevel) =' k 0)
    (.set CodeAcc (v CodeAcc *' k 7 +' M (v Outer)) ;; .set Outer (v Outer +' k 1))
    (.set CodeAcc (v CodeAcc *' k 7 +' k 3 +' M (v Inner)) ;; .set Inner (v Inner +' k 1))

/-- The loop over the levels. -/
def bandCodeLoop : Stmt := .for CurLevel (v Levels) bandLevel

/-- One entry: the code of the string, and the entry copied. -/
def bandCell : Stmt :=
  .set CodeAcc (k 0) ;;
  .set Outer (v Digits3 +' v Row *' (v Levels -' v Size)) ;;
  .set Inner (v Digits4 +' v Col *' v Size) ;;
  bandCodeLoop ;;
  .store (v Dest +' v CodeAcc) (M (v Source +' v Row *' v StepRow +' v Col *' v StepCol))

/-- The loop over the columns k. -/
def bandColLoop : Stmt := .for Col (v Cols) bandCell

/-- One row r of a block; rows beyond the matrix are skipped. -/
def bandRow : Stmt :=
  .set Row (v BlockIdx *' v Width +' v Offset) ;;
  .ite (v Row <' v Rows) bandColLoop .skip

/-- The loop over the rows r of a block. -/
def bandRowLoop : Stmt := .for Offset (v Width) bandRow

/-- The address of the mask of the subset of the block product (g, h), and the rows of the block. -/
def bandRows : Stmt :=
  .set MaskRow (v MaskTable +' (v PosG *' v NumBlocks +' v PosH) *' v Levels) ;; bandRowLoop

/-- One block product (g, h): the number of the block, which depends on the side, and the rest. -/
def bandBlock : Stmt :=
  .ite (v Side =' k 0) (.set BlockIdx (v BandNo *' v NumBlocks +' v PosG))
    (.set BlockIdx (v BandNo *' v NumBlocks +' v PosH)) ;;
  bandRows

/-- The loop over h. -/
def bandHLoop : Stmt := .for PosH (v NumBlocks) bandBlock

/-- The loop over g. -/
def bandGLoop : Stmt := .for PosG (v NumBlocks) bandHLoop

/-- The clearing loop. -/
def bandZeroLoop : Stmt := pass PosG (v Cells) (v Dest) (k 0)

/-- bandArray(L, m, N, D, K0, N0, S7, β, side, aA, sI, sK, mask, dig3, dig4, arr). -/
def bandArrayBody : Stmt := bandZeroLoop ;; bandGLoop

/-- The constant of the running time. -/
def cBandArray : ℕ := 120

/-! ## The local variables as a list -/

/-- The local variables of the loop over h. -/
structure BlockTmp where
  /-- h. -/
  h : ℤ
  /-- The number of the block. -/
  blk : ℤ
  /-- The address of the mask of the subset. -/
  mrow : ℤ

/-- The local variables of the loop over the rows of a block. -/
structure RowTmp where
  /-- r. -/
  r : ℤ
  /-- The number of the row of the matrix. -/
  row : ℤ

/-- The local variables of the loop over the columns. -/
structure CellTmp where
  /-- k. -/
  k : ℤ
  /-- The code. -/
  code : ℤ
  /-- The address of the next outer digit. -/
  outer : ℤ
  /-- The address of the next inner digit. -/
  inner : ℤ
  /-- The level. -/
  lev : ℤ

/-- The local variables of the three inner loops together. -/
structure InnerTmp where
  /-- Those of the loop over `h`. -/
  block : BlockTmp
  /-- Those of the loop over the rows of a block. -/
  row : RowTmp
  /-- Those of the loop over the columns. -/
  cell : CellTmp

/-- The list of the local variables. -/
abbrev Band.locals (A : BandArgs) (g : ℤ) (H : BlockTmp) (R : RowTmp) (c : CellTmp) : List ℤ :=
  [A.p.L, A.p.m, A.p.N, A.p.D, A.p.K0, A.p.N0, A.p.S7, A.β, A.side, A.aA, A.sI, A.sK, A.mask,
    A.dig3, A.dig4, A.arr, g, H.h, H.blk, H.mrow, R.r, R.row, c.k, c.code, c.outer, c.inner, c.lev]

/-- The local variables of the loop over `h` for the block product `(g, h)`. -/
abbrev Band.blockTmp (A : BandArgs) (g h : ℕ) : BlockTmp :=
  ⟨h, (A.blockNo g h : ℕ), (A.maskRow g h : ℕ)⟩

/-- The local variables of the loop over the rows for the row `r` of the block product `(g, h)`. -/
abbrev Band.rowTmp (A : BandArgs) (g h r : ℕ) : RowTmp := ⟨r, (A.rowNo g h r : ℕ)⟩

variable {lim : Limits} {P : Program} {d : ℕ} {A : BandArgs} {μ₀ μ : ℕ → ℤ} {T : List ℤ}

/-! ## The loop over the levels -/

/-- What the loop over the levels reads: the mask bs at mrow, the outer digits o at d3 and the inner
digits i at d4. -/
structure CodeCtx (lim : Limits) (μ : ℕ → ℤ) (L mrow d3 d4 : ℕ) (bs : List Bool) (o i : List ℕ) :
    Prop where
  std : Std lim
  length : bs.length = L
  outer : bs.count false = o.length
  inner : bs.count true = i.length
  outer_lt : ∀ x ∈ o, x < 3
  inner_lt : ∀ x ∈ i, x < 4
  segB : SegB μ mrow bs
  segO : SegN μ d3 o
  segI : SegN μ d4 i
  spaceB : mrow + L ≤ lim.space
  spaceO : d3 + o.length ≤ lim.space
  spaceI : d4 + i.length ≤ lim.space
  space7 : 7 ^ L ≤ lim.space

/-- The local variables of the loop over the columns after l levels. -/
abbrev Band.codeTmp (k : ℤ) (bs : List Bool) (o i : List ℕ) (d3 d4 l : ℕ) (lev : ℤ) : CellTmp :=
  ⟨k, (codeUpTo bs o i l : ℕ), (d3 + (bs.take l).count false : ℕ),
    (d4 + (bs.take l).count true : ℕ), lev⟩

section levels
variable {mrow d3 d4 : ℕ} {bs : List Bool} {o i : List ℕ} {g h blk k : ℤ} {R : RowTmp}

/-- **One level** leads from the state after `l` levels to the state after `l + 1` levels.  No cell
changes. -/
theorem bandLevel_spec (ctx : CodeCtx lim μ A.p.L mrow d3 d4 bs o i) {l : ℕ} (hl : l < A.p.L) :
    Ends lim P d bandLevel ⟨frame (locals A g ⟨h, blk, mrow⟩ R (codeTmp k bs o i d3 d4 l l)), μ⟩
      bandLevel.blockCost fun σ' =>
        σ' = ⟨frame (locals A g ⟨h, blk, mrow⟩ R (codeTmp k bs o i d3 d4 (l + 1) l)), μ⟩ := by
  light_facts ctx.std
  have hplaces := And.intro ctx.spaceB <| And.intro ctx.spaceO <| And.intro ctx.spaceI <|
    And.intro ctx.space7 <| And.intro ctx.outer ctx.inner
  have hlen : l < bs.length := ctx.length ▸ hl
  have hbit := ctx.segB.get hlen
  have hcode := codeUpTo_succ (o := o) (i := i) hlen
  have hlt := codeUpTo_lt ctx.outer_lt ctx.inner_lt (show l + 1 ≤ bs.length from hlen)
  have hpow : 7 ^ (l + 1) ≤ 7 ^ A.p.L := Nat.pow_le_pow_right (by omega) hl
  have hfalse := List.count_take_succ_getD bs false hlen false
  have htrue := List.count_take_succ_getD bs true hlen false
  unfold bandLevel
  cases hb : bs.getD l false
  · -- A level outside the set: the next outer digit.
    have hroom := List.count_take_lt hlen false hb
    have hcell := ctx.segO.read (ctx.outer ▸ hroom)
    rw [hb] at hbit hcode hfalse htrue
    simp only [Bool.false_eq_true, if_false, if_true] at hbit hcode hfalse htrue
    rw [hcode] at hlt
    generalize o.getD ((bs.take l).count false) 0 = digit at hcell hcode hlt
    refine Ends.iteLast (fun _ => ?_) (fun hc => absurd (by simp [hbit]) hc)
    -- CodeAcc := CodeAcc * 7 + mem[Outer]; Outer := Outer + 1
    light_set (codeUpTo bs o i (l + 1) : ℕ) using hcell, hcode
    light_set (d3 + (bs.take (l + 1)).count false : ℕ) using hfalse
    simp only [locals, setLocal, htrue, Nat.add_zero]
  · -- A level of the set: 3 plus the next inner digit.
    have hroom := List.count_take_lt hlen false hb
    have hcell := ctx.segI.read (ctx.inner ▸ hroom)
    rw [hb] at hbit hcode hfalse htrue
    simp only [if_true, reduceCtorEq, if_false,
      List.getD_map_of_lt (3 + ·) (ctx.inner ▸ hroom) 0 0] at hbit hcode hfalse htrue
    rw [hcode] at hlt
    generalize i.getD ((bs.take l).count true) 0 = digit at hcell hcode hlt
    refine Ends.iteLast (fun hc => absurd hc (by simp [hbit])) (fun _ => ?_)
    -- CodeAcc := CodeAcc * 7 + 3 + mem[Inner]; Inner := Inner + 1
    light_set (codeUpTo bs o i (l + 1) : ℕ) using hcell, hcode
    light_set (d4 + (bs.take (l + 1)).count true : ℕ) using htrue
    simp only [locals, setLocal, hfalse, Nat.add_zero]

/-- **The loop over the levels** leaves the code of the string in the local `CodeAcc` and changes no
cell. -/
theorem bandCodeLoop_spec (ctx : CodeCtx lim μ A.p.L mrow d3 d4 bs o i) {lev₀ : ℤ} {T' : ℕ}
    {Q : State → Prop}
    (done : ∀ c : CellTmp, c.k = k → c.code = (codeUpTo bs o i A.p.L : ℕ) →
      Q ⟨frame (locals A g ⟨h, blk, mrow⟩ R c), μ⟩)
    (hT : 28 * A.p.L + 6 ≤ T') :
    Ends lim P d bandCodeLoop ⟨frame (locals A g ⟨h, blk, mrow⟩ R ⟨k, 0, d3, d4, lev₀⟩), μ⟩ T'
      Q := by
  light_facts ctx ctx.std
  -- for CurLevel < L
  refine Ends.for (fun l σ =>
      σ = ⟨frame (locals A g ⟨h, blk, mrow⟩ R (codeTmp k bs o i d3 d4 l l)), μ⟩) A.p.L
    bandLevel.blockCost ?start ?round ?done ?bound (by omega) (by simp [bandLevel]; omega)
  case start => simp [update_frame_setLocal, locals, codeUpTo, ThreeSumApsp.ofDigitList]
  case done => exact fun _ _ hσ => hσ ▸ done _ rfl rfl
  case bound => exact fun l _ _ _ hσ => hσ ▸ by light_side
  case round =>
    rintro l _ hl - rfl
    refine (bandLevel_spec ctx hl).mono le_rfl ?_
    rintro _ rfl
    exact ⟨by simp, by simp [update_frame_setLocal, locals]⟩

end levels

/-! ## The surroundings -/

/-- Everything that the loops assume: the limits, the places of the tables and of the matrix in the
memory μ₀ at the start, and what is known about the list T that has to be produced. -/
structure BandCtx (lim : Limits) (A : BandArgs) (μ₀ : ℕ → ℤ) (T : List ℤ) : Prop where
  std : Std lim
  hmL : A.p.m ≤ A.p.L
  space : A.arr + A.p.S7 ≤ lim.space
  aA_le : A.aA + A.p.N * A.p.D ≤ A.arr
  tabs : BandTables A.p μ₀ A.mask A.dig3 A.dig4 A.arr
  β_lt : A.β < A.p.nB
  idx : ∀ row < A.p.N, ∀ k < A.p.D, row * A.sI + k * A.sK < A.p.N * A.p.D
  T_len : T.length = A.p.S7
  entry : ∀ g < A.p.K0, ∀ h < A.p.K0, ∀ r < A.p.N0, ∀ k < A.p.D, T.getD (A.code g h r k) 0
    = if A.rowNo g h r < A.p.N
      then μ₀ (A.aA + (A.rowNo g h r * A.sI + k * A.sK)) else 0
  zero : ∀ c : ℕ, (∀ g < A.p.K0, ∀ h < A.p.K0, ∀ r < A.p.N0, ∀ k < A.p.D,
    c ≠ A.code g h r k) → T.getD c 0 = 0

/-- The cell of the tuple (g, h, r, k) is right. -/
def Covered (A : BandArgs) (T : List ℤ) (μ : ℕ → ℤ) (g h r k : ℕ) : Prop :=
  μ (A.arr + A.code g h r k) = T.getD (A.code g h r k) 0

/-- A cell that is right stays right. -/
theorem Covered.keep {μ' : ℕ → ℤ} {g h r k : ℕ} (hc : Covered A T μ g h r k)
    (hext : OverwrittenWith T A.arr A.p.S7 μ μ') : Covered A T μ' g h r k :=
  hext.keep (BandArgs.code_lt ..) hc

namespace BandCtx

/-- Inequalities between the numbers: where the tables, the matrix and the array lie, and bounds on
the sizes. -/
theorem places (C : BandCtx lim A μ₀ T) :
    (lim.space : ℤ) ≤ lim.word ∧ 100 ≤ lim.word ∧ A.p.m ≤ A.p.L ∧ A.arr + A.p.S7 ≤ lim.space ∧
      A.aA + A.p.N * A.p.D ≤ A.arr ∧ A.mask + A.p.KK * A.p.L ≤ A.arr ∧
      A.dig3 + A.p.N * A.p.Lo ≤ A.arr ∧ A.dig4 + A.p.D * A.p.m ≤ A.arr ∧
      A.p.N ≤ A.p.N * A.p.D ∧ A.p.L.choose A.p.m ≤ A.p.S7 ∧ A.p.K0 ≤ A.p.S7 ∧ A.p.N0 ≤ A.p.S7 ∧
      A.p.L < A.p.S7 :=
  ⟨C.std.space_le, C.std.const_le, C.hmL, C.space, C.aA_le, C.tabs.mask_le, C.tabs.dig3_le,
    C.tabs.dig4_le, Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)), A.p.sizes_le_S7⟩

/-- What the loop over the levels reads for the tuple (g, h, r, k), in a memory in which only cells
of the array have changed. -/
private theorem codeCtx (C : BandCtx lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    {g h r k : ℕ} (hg : g < A.p.K0) (hh : h < A.p.K0) (hr : r < A.p.N0)
    (hrow : A.rowNo g h r < A.p.N) (hk : k < A.p.D) :
    CodeCtx lim μ A.p.L (A.maskRow g h)
      (A.dig3 + A.rowNo g h r * A.p.Lo) (A.dig4 + k * A.p.m)
      (Spec.unrank A.p.L A.p.m (g * A.p.K0 + h)) (ThreeSumApsp.digitList 3 (A.p.L - A.p.m) r)
      (ThreeSumApsp.digitList 4 A.p.m k) := by
  have hplaces := C.places
  obtain ⟨hKK, hchoose⟩ := subsetIndex_lt A.p hg hh
  have hmask := Nat.mul_add_le_mul hKK (le_refl A.p.L)
  have hdig3 := Nat.mul_add_le_mul hrow (le_refl A.p.Lo)
  have hdig4 := Nat.mul_add_le_mul hk (le_refl A.p.m)
  have hLo : A.p.Lo = A.p.L - A.p.m := rfl
  have hS7 : A.p.S7 = 7 ^ A.p.L := rfl
  have hmaskRow : A.maskRow g h = A.mask + (g * A.p.K0 + h) * A.p.L := rfl
  -- The table of digits in base 3 is indexed by the row of the matrix and holds the digits of the
  -- offset of the row in its block, which is r.
  have hdigits := C.tabs.hdig3 _ hrow
  rw [BandArgs.rowNo_mod g h hr] at hdigits
  exact
    { std := C.std
      length := Spec.length_unrank ..
      outer := by rw [Spec.count_false_unrank hchoose, ThreeSumApsp.length_digitList]
      inner := by rw [Spec.count_unrank hchoose, ThreeSumApsp.length_digitList]
      outer_lt := fun _ => ThreeSumApsp.lt_of_mem_digitList (by omega)
      inner_lt := fun _ => ThreeSumApsp.lt_of_mem_digitList (by omega)
      segB := (C.tabs.hmask _ hKK).keep
      segO := hdigits.keep
      segI := (C.tabs.hdig4 k hk).keep
      spaceB := by omega
      spaceO := by rw [ThreeSumApsp.length_digitList]; omega
      spaceI := by rw [ThreeSumApsp.length_digitList]; omega
      space7 := by omega }

end BandCtx

/-! ## A loop that fills cells -/

/-- **The four loops at once.**  shape z x is the list of the local variables, with z in the counter
and the local variables x of the loops inside.  If round j overwrites cells only with entries of the
target and establishes fact j, which such writes keep, then the loop establishes fact j for all
j < rounds. -/
theorem coverLoop {X : Type} {arr n rounds b cnt T' : ℕ} {hi : Expr} {body : Stmt}
    (shape : ℤ → X → List ℤ) (fact : ℕ → (ℕ → ℤ) → Prop)
    (keep : ∀ j μ' μ'', fact j μ' → OverwrittenWith T arr n μ' μ'' → fact j μ'')
    (round : ∀ j < rounds, ∀ x μ', OverwrittenWith T arr n μ μ' →
      Ends lim P d body ⟨frame (shape j x), μ'⟩ b fun σ' => ∃ x' μ'',
        σ' = ⟨frame (shape j x'), μ''⟩ ∧ OverwrittenWith T arr n μ' μ'' ∧ fact j μ'')
    (z₀ : ℤ) (x₀ : X)
    (hset : ∀ z x z', setLocal (shape z x) cnt z' = shape z' x := by intros; rfl)
    (hat : ∀ z x, frame (shape z x) cnt = z := by intros; rfl)
    (hbound : ∀ z x μ', hi.Gives lim ⟨frame (shape z x), μ'⟩ rounds := by intros; light_side)
    (hrounds : (rounds : ℤ) ≤ lim.word := by omega)
    (hT : rounds * (hi.cost + b + 7) + hi.cost + 5 ≤ T' := by light_time) :
    Ends lim P d (.for cnt hi body) ⟨frame (shape z₀ x₀), μ⟩ T' fun σ' => ∃ x μ',
      σ' = ⟨frame (shape rounds x), μ'⟩ ∧ OverwrittenWith T arr n μ μ' ∧
        ∀ j < rounds, fact j μ' := by
  refine Ends.forShape (fun j x μ' => ⟨frame (shape j x), μ'⟩)
    (fun j μ' => OverwrittenWith T arr n μ μ' ∧ ∀ j' < j, fact j' μ') rounds b x₀
    ⟨.refl, fun j' hj' => absurd hj' (by omega)⟩ ?round (fun x μ' h => ⟨x, μ', rfl, h⟩)
    (by simp only [update_frame_setLocal, hset, Nat.cast_zero]) (fun _ _ _ _ _ => hbound _ _ _)
    (fun _ _ _ => hat _ _)
    (fun _ _ _ => by simp only [update_frame_setLocal, hset, Nat.cast_add, Nat.cast_one]) hrounds hT
  rintro j x μ' hj ⟨hext, hcov⟩
  refine (round j hj x μ' hext).mono le_rfl ?_
  rintro _ ⟨x', μ'', rfl, hext', hnew⟩
  refine ⟨x', μ'', rfl, hext.trans hext', fun j' hj' => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
  · exact keep j' _ _ (hcov j' hj') hext'
  · exact hnew

/-! ## The loop over the columns -/

/-- The time of one entry. -/
def tBandCell (p : Par) : ℕ := 28 * p.L + 36

section cell
variable {g h r k : ℕ}

/-- **One entry**: the code of the string is computed, and the entry of the matrix is copied to its
cell. -/
theorem bandCell_spec (C : BandCtx lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (hh : h < A.p.K0) (hr : r < A.p.N0)
    (hrow : A.rowNo g h r < A.p.N) (hk : k < A.p.D) (c : CellTmp) :
    Ends lim P d bandCell
      ⟨frame (locals A g (blockTmp A g h) (rowTmp A g h r) { c with k := k }), μ⟩ (tBandCell A.p)
      fun σ' => ∃ c' : CellTmp, σ' =
        ⟨frame (locals A g (blockTmp A g h) (rowTmp A g h r) { c' with k := k }),
          Function.update μ (A.arr + A.code g h r k) (T.getD (A.code g h r k) 0)⟩ := by
  have hplaces := C.places
  have hdig3 := Nat.mul_add_le_mul hrow (le_refl A.p.Lo)
  have hdig4 := Nat.mul_add_le_mul hk (le_refl A.p.m)
  have hidx := C.idx _ hrow k hk
  have hcode := A.code_lt g h r k
  have hval : μ (A.aA + (A.rowNo g h r * A.sI + k * A.sK))
      = T.getD (A.code g h r k) 0 := by
    rw [C.entry g hg h hh r hr k hk, if_pos hrow]
    exact same _ (Or.inl (by omega))
  have ctx := C.codeCtx same hg hh hr hrow hk
  unfold rowTmp
  generalize A.rowNo g h r = row at *
  have houter : (row : ℤ) * ((A.p.L : ℤ) - A.p.m) = ((row * A.p.Lo : ℕ) : ℤ) := by
    rw [Nat.cast_mul, show A.p.Lo = A.p.L - A.p.m from rfl, Nat.cast_sub C.hmL]
  have haddr : ((A.aA : ℤ) + row * A.sI + k * A.sK).toNat = A.aA + (row * A.sI + k * A.sK) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_add, Int.toNat_natCast,
      Nat.add_assoc]
  unfold bandCell tBandCell
  -- CodeAcc := 0; Outer := dig3 + Row (L - m); Inner := dig4 + Col m
  light_set 0
  light_set (A.dig3 + row * A.p.Lo : ℕ) using houter
  light_set (A.dig4 + k * A.p.m : ℕ)
  -- The code.
  refine Ends.next _ (bandCodeLoop_spec ctx ?_ le_rfl)
  rintro ⟨_, _, outer, inner, lev⟩ rfl rfl
  rw [show codeUpTo _ _ _ A.p.L = A.code g h r k from codeUpTo_unrank ..]
  -- mem[arr + CodeAcc] := mem[aA + Row sI + Col sK]
  light_store (A.arr + A.code g h r k) (T.getD (A.code g h r k) 0) using haddr, hval
  exact ⟨⟨k, (A.code g h r k : ℕ), outer, inner, lev⟩, rfl⟩

/-- The time of the loop over the columns. -/
def tBandCol (p : Par) : ℕ := p.D * (tBandCell p + 8) + 6

/-- **The loop over the columns** fills the cells of the tuples (g, h, r, k), k < D. -/
theorem bandColLoop_spec (C : BandCtx lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (hh : h < A.p.K0) (hr : r < A.p.N0)
    (hrow : A.rowNo g h r < A.p.N) (c : CellTmp) :
    Ends lim P d bandColLoop ⟨frame (locals A g (blockTmp A g h) (rowTmp A g h r) c), μ⟩
      (tBandCol A.p) fun σ' => ∃ (c' : CellTmp) (μ' : ℕ → ℤ),
        σ' = ⟨frame (locals A g (blockTmp A g h) (rowTmp A g h r) c'), μ'⟩ ∧
        OverwrittenWith T A.arr A.p.S7 μ μ' ∧ ∀ k < A.p.D, Covered A T μ' g h r k := by
  have hplaces := C.places
  have hD : A.p.D ≤ A.p.N * A.p.D := Nat.le_mul_of_pos_left _ (by omega)
  -- for Col < D
  refine (coverLoop (b := tBandCell A.p) (rounds := A.p.D)
    (shape := fun z (c : CellTmp) => locals A g (blockTmp A g h) (rowTmp A g h r) { c with k := z })
    (fact := fun k μ' => Covered A T μ' g h r k) (keep := fun _ _ _ hc => hc.keep) (round := ?_)
    c.k c (hT := by simp [tBandCol]; ring_nf; omega)).mono le_rfl
    fun σ' ⟨c', μ', hσ, hfacts⟩ => ⟨_, μ', hσ, hfacts⟩
  intro k hk c' μ' hext
  refine (bandCell_spec C (same.trans hext.1) hg hh hr hrow hk c').mono le_rfl ?_
  rintro _ ⟨c'', rfl⟩
  exact ⟨c'', _, rfl, .write (BandArgs.code_lt ..), Function.update_self ..⟩

end cell

/-! ## The loop over the rows of a block -/

/-- The cells of the row r of the block product (g, h) are right, if the row lies in the matrix. -/
def CoveredRow (A : BandArgs) (T : List ℤ) (μ : ℕ → ℤ) (g h r : ℕ) : Prop :=
  A.rowNo g h r < A.p.N → ∀ k < A.p.D, Covered A T μ g h r k

/-- The time of one row of a block. -/
def tBandRow (p : Par) : ℕ := tBandCol p + 10

/-- The time of the loop over the rows of a block. -/
def tBandRows (p : Par) : ℕ := p.N0 * (tBandRow p + 8) + 6

section rows
variable {g h r : ℕ}

/-- **One row of a block**: if the row lies in the matrix, the cells of the tuples `(g, h, r, k)`,
`k < D`, are filled. -/
theorem bandRow_spec (C : BandCtx lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (hh : h < A.p.K0) (hr : r < A.p.N0) (R : RowTmp) (c : CellTmp) :
    Ends lim P d bandRow ⟨frame (locals A g (blockTmp A g h) { R with r := r } c), μ⟩
      (tBandRow A.p) fun σ' => ∃ (x : RowTmp × CellTmp) (μ' : ℕ → ℤ),
        σ' = ⟨frame (locals A g (blockTmp A g h) { x.1 with r := r } x.2), μ'⟩ ∧
        OverwrittenWith T A.arr A.p.S7 μ μ' ∧ CoveredRow A T μ' g h r := by
  have hplaces := C.places
  have hsmall := BandArgs.rowNo_lt C.β_lt hg hh hr
  have hrowNo : A.rowNo g h r = A.blockNo g h * A.p.N0 + r := rfl
  unfold bandRow tBandRow
  -- Row := BlockIdx N0 + Offset
  light_set (A.rowNo g h r : ℕ) using hrowNo
  -- if Row < N
  refine Ends.iteLast (fun hc => ?_) fun hc => Ends.skip ?_
  · have hrow : A.rowNo g h r < A.p.N := by simp at hc; omega
    refine (bandColLoop_spec C same hg hh hr hrow c).mono (by simp) ?_
    rintro _ ⟨c', μ', rfl, hext, hcov⟩
    exact ⟨(rowTmp A g h r, c'), μ', rfl, hext, fun _ => hcov⟩
  · exact ⟨(rowTmp A g h r, c), μ, rfl, .refl,
      fun hrow => absurd hrow (by simp at hc; omega)⟩

/-- **The loop over the rows of a block** fills the cells of the tuples `(g, h, r, k)`, `r < N₀`,
whose row lies in the matrix. -/
theorem bandRowLoop_spec (C : BandCtx lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (hh : h < A.p.K0) (R : RowTmp) (c : CellTmp) :
    Ends lim P d bandRowLoop ⟨frame (locals A g (blockTmp A g h) R c), μ⟩ (tBandRows A.p)
      fun σ' => ∃ (x : RowTmp × CellTmp) (μ' : ℕ → ℤ),
        σ' = ⟨frame (locals A g (blockTmp A g h) x.1 x.2), μ'⟩ ∧
        OverwrittenWith T A.arr A.p.S7 μ μ' ∧ ∀ r < A.p.N0, CoveredRow A T μ' g h r := by
  have hplaces := C.places
  -- for Offset < N0
  exact (coverLoop (b := tBandRow A.p) (rounds := A.p.N0)
    (shape := fun z (x : RowTmp × CellTmp) =>
      locals A g (blockTmp A g h) { x.1 with r := z } x.2)
    (fact := fun r μ' => CoveredRow A T μ' g h r)
    (keep := fun _ _ _ hc hext hrow k hk => (hc hrow k hk).keep hext)
    (round := fun r hr x μ' hext => bandRow_spec C (same.trans hext.1) hg hh hr x.1 x.2)
    R.r (R, c) (hT := by simp [tBandRows]; ring_nf; omega)).mono le_rfl
    fun σ' ⟨x, μ', hσ, hfacts⟩ => ⟨(_, x.2), μ', hσ, hfacts⟩

end rows

/-! ## The loops over h and g -/

/-- The time of one block product. -/
def tBandBlock (p : Par) : ℕ := tBandRows p + 20

/-- The time of the loop over h. -/
def tBandH (p : Par) : ℕ := p.K0 * (tBandBlock p + 8) + 6

/-- The time of the loop over g. -/
def tBandG (p : Par) : ℕ := p.K0 * (tBandH p + 8) + 6

section blocks
variable {g h : ℕ}

/-- **The rows of the block product (g, h)**, once the number of the block is known. -/
theorem bandRows_spec (C : BandCtx lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (hh : h < A.p.K0) (mrow : ℤ) (R : RowTmp) (c : CellTmp) {T' : ℕ}
    (hT : tBandRows A.p + 10 ≤ T') :
    Ends lim P d bandRows
      ⟨frame (locals A g ⟨h, (A.blockNo g h : ℕ), mrow⟩ R c), μ⟩ T'
      fun σ' => ∃ (x : InnerTmp) (μ' : ℕ → ℤ),
        σ' = ⟨frame (locals A g { x.block with h := h } x.row x.cell), μ'⟩ ∧
        OverwrittenWith T A.arr A.p.S7 μ μ' ∧ ∀ r < A.p.N0, CoveredRow A T μ' g h r := by
  have hplaces := C.places
  -- The address of the mask fits in a word.
  obtain ⟨hKK, hchoose⟩ := subsetIndex_lt A.p hg hh
  have hmask := Nat.mul_add_le_mul hKK (le_refl A.p.L)
  have hprod : (((g * A.p.K0 + h) * A.p.L : ℕ) : ℤ) = ((g : ℤ) * A.p.K0 + h) * A.p.L := by
    push_cast
    rfl
  -- MaskRow := mask + (g K0 + h) L
  light_set (A.maskRow g h : ℕ) using BandArgs.maskRow
  refine (bandRowLoop_spec C same hg hh R c).mono (by simp; omega) ?_
  rintro _ ⟨x, μ', rfl, hfacts⟩
  exact ⟨⟨blockTmp A g h, x.1, x.2⟩, μ', rfl, hfacts⟩

/-- **One block product**: the number of the block is formed, and the cells of the tuples
`(g, h, r, k)` whose row lies in the matrix are filled. -/
theorem bandBlock_spec (C : BandCtx lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (hh : h < A.p.K0) (H : BlockTmp) (R : RowTmp) (c : CellTmp) :
    Ends lim P d bandBlock ⟨frame (locals A g { H with h := h } R c), μ⟩ (tBandBlock A.p)
      fun σ' => ∃ (x : InnerTmp) (μ' : ℕ → ℤ),
        σ' = ⟨frame (locals A g { x.block with h := h } x.row x.cell), μ'⟩ ∧
        OverwrittenWith T A.arr A.p.S7 μ μ' ∧ ∀ r < A.p.N0, CoveredRow A T μ' g h r := by
  have hplaces := C.places
  have hsmall := BandArgs.rowNo_lt C.β_lt hg hh (N0_pos A.p.L A.p.m)
  have hrows := fun T' hT' => bandRows_spec (P := P) (d := d) (T' := T') C same hg hh H.mrow R c hT'
  unfold bandBlock tBandBlock
  -- if side = 0 then BlockIdx := β K0 + g else BlockIdx := β K0 + h
  refine Ends.iteThen (fun hc => ?_) fun hc => ?_
  · have hside : A.side = 0 := by simpa using hc
    exact Ends.setToThen _ (hrows _ (by simp))
      (by simp [abs_le, BandArgs.blockNo, hside] at hsmall ⊢; omega)
  · have hside : ¬ A.side = 0 := by simpa using hc
    exact Ends.setToThen _ (hrows _ (by simp))
      (by simp [abs_le, BandArgs.blockNo, hside] at hsmall ⊢; omega)

/-- **The loop over `h`** fills the cells of the tuples `(g, h, r, k)`, `h < K₀`, whose row lies in
the matrix. -/
theorem bandHLoop_spec (C : BandCtx lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7)
    (hg : g < A.p.K0) (x : InnerTmp) :
    Ends lim P d bandHLoop ⟨frame (locals A g x.block x.row x.cell), μ⟩ (tBandH A.p)
      fun σ' => ∃ (x' : InnerTmp) (μ' : ℕ → ℤ),
        σ' = ⟨frame (locals A g x'.block x'.row x'.cell), μ'⟩ ∧
        OverwrittenWith T A.arr A.p.S7 μ μ' ∧
        ∀ h < A.p.K0, ∀ r < A.p.N0, CoveredRow A T μ' g h r := by
  have hplaces := C.places
  -- for PosH < K0
  exact (coverLoop (b := tBandBlock A.p) (rounds := A.p.K0)
    (shape := fun z (x : InnerTmp) =>
      locals A g { x.block with h := z } x.row x.cell)
    (fact := fun h μ' => ∀ r < A.p.N0, CoveredRow A T μ' g h r)
    (keep := fun _ _ _ hc hext r hr hrow k hk => (hc r hr hrow k hk).keep hext)
    (round := fun h hh x μ' hext => bandBlock_spec C (same.trans hext.1) hg hh x.block x.row x.cell)
    x.block.h x (hT := by simp [tBandH]; ring_nf; omega)).mono le_rfl
    fun σ' ⟨x', μ', hσ, hfacts⟩ => ⟨⟨_, x'.row, x'.cell⟩, μ', hσ, hfacts⟩

/-- **The loop over `g`** fills the cells of all tuples `(g, h, r, k)` whose row lies in the
matrix. -/
theorem bandGLoop_spec (C : BandCtx lim A μ₀ T) (same : SameOutside μ₀ μ A.arr A.p.S7) (g₀ : ℤ)
    (x : InnerTmp) :
    Ends lim P d bandGLoop ⟨frame (locals A g₀ x.block x.row x.cell), μ⟩ (tBandG A.p)
      fun σ' => OverwrittenWith T A.arr A.p.S7 μ σ'.mem ∧
        ∀ g < A.p.K0, ∀ h < A.p.K0, ∀ r < A.p.N0, CoveredRow A T σ'.mem g h r := by
  have hplaces := C.places
  -- for PosG < K0
  refine (coverLoop (b := tBandH A.p) (rounds := A.p.K0)
    (shape := fun z (x : InnerTmp) => locals A z x.block x.row x.cell)
    (fact := fun g μ' => ∀ h < A.p.K0, ∀ r < A.p.N0, CoveredRow A T μ' g h r)
    (keep := fun _ _ _ hc hext h hh r hr hrow k hk => (hc h hh r hr hrow k hk).keep hext)
    (round := fun g hg x μ' hext => bandHLoop_spec C (same.trans hext.1) hg x)
    g₀ x (hT := by simp [tBandG]; ring_nf; omega)).mono le_rfl ?_
  rintro _ ⟨x', μ', rfl, hfacts⟩
  exact hfacts

end blocks

/-! ## The whole procedure -/

/-- The time of the whole procedure is within the bound that its callers assume. -/
private theorem bandArray_time (p : Par) :
    p.S7 * 13 + 6 + tBandG p ≤ cBandArray * bandArrayShape p := by
  have hD : 1 ≤ p.D := Nat.pow_pos (by omega)
  have hN0 : 1 ≤ p.N0 := N0_pos _ _
  have hK0 : p.K0 ≤ p.K0 * p.K0 := Nat.le_mul_self _
  have hKK : p.K0 * p.K0 ≤ p.K0 * p.K0 * p.N0 := Nat.le_mul_of_pos_right _ hN0
  have hrows : p.K0 * p.K0 * p.N0 ≤ p.K0 * p.K0 * p.N0 * p.D := Nat.le_mul_of_pos_right _ hD
  have htime : tBandG p = 28 * (p.K0 * p.K0 * p.N0 * p.D * p.L) + 44 * (p.K0 * p.K0 * p.N0 * p.D)
      + 24 * (p.K0 * p.K0 * p.N0) + 34 * (p.K0 * p.K0) + 14 * p.K0 + 6 := by
    unfold tBandG tBandH tBandBlock tBandRows tBandRow tBandCol tBandCell
    ring
  have hshape : cBandArray * bandArrayShape p = 120 * p.S7
      + 120 * (p.K0 * p.K0 * p.N0 * p.D * p.L) + 120 * (p.K0 * p.K0 * p.N0 * p.D) + 120 * p.L
      + 120 := by
    unfold cBandArray bandArrayShape Par.KK
    ring
  omega

/-- The arguments of bandArray as a list. -/
abbrev Band.args (A : BandArgs) : List ℤ :=
  [A.p.L, A.p.m, A.p.N, A.p.D, A.p.K0, A.p.N0, A.p.S7, A.β, A.side, A.aA, A.sI, A.sK, A.mask,
    A.dig3, A.dig4, A.arr]

/-- **bandArray** writes the list T to the array and changes nothing else. -/
theorem bandArray_spec (C : BandCtx lim A μ₀ T) :
    Ends lim P d bandArrayBody ⟨frame (args A), μ₀⟩ (cBandArray * bandArrayShape A.p) fun σ' =>
      Seg σ'.mem A.arr T ∧ SameOutside μ₀ σ'.mem A.arr A.p.S7 := by
  have hplaces := C.places
  have htime := bandArray_time A.p
  have hcleared : SameOutside μ₀ (wrote μ₀ A.arr (fun _ => 0) A.p.S7) A.arr A.p.S7 :=
    sameOutside_wrote le_rfl
  -- The array is cleared.
  refine Ends.next _ (Ends.pass (x := Cells) (y := Dest) (dst := A.arr) (n := A.p.S7) (fun _ => 0)
    (fun j _ => by light_side) ?_ C.std.space_le C.space rfl rfl (hT := le_rfl)) (by simp; omega)
  -- The loops over the tuples (g, h, r, k); the ten local variables of the inner loops start at 0.
  rw [update_frame_setLocal, ← frame_append_zeros _ 10]
  refine (bandGLoop_spec C hcleared A.p.S7 ⟨⟨0, 0, 0⟩, ⟨0, 0⟩, ⟨0, 0, 0, 0, 0⟩⟩).mono
    (by simp; omega) ?_
  rintro ⟨_, μ'⟩ ⟨hext, hcov⟩
  dsimp only at hext hcov ⊢
  refine ⟨fun c hc => ?_, hcleared.trans hext.1⟩
  have hc7 : c < A.p.S7 := C.T_len ▸ hc
  rw [← List.getD_eq_getElem T 0 hc]
  -- A cell whose entry is 0 is right, whether it has been overwritten or not.
  have hzero : T.getD c 0 = 0 → μ' (A.arr + c) = T.getD c 0 := fun h0 =>
    (hext.2 c hc7).elim (fun h => by rw [h, wrote_done hc7, h0]) id
  by_cases hx : ∃ g < A.p.K0, ∃ h < A.p.K0, ∃ r < A.p.N0, ∃ k < A.p.D, c = A.code g h r k
  · obtain ⟨g, hg, h, hh, r, hr, k, hk, rfl⟩ := hx
    by_cases hrow : A.rowNo g h r < A.p.N
    · exact hcov g hg h hh r hr hrow k hk
    · exact hzero (by rw [C.entry g hg h hh r hr k hk, if_neg hrow])
  · exact hzero (C.zero c fun g hg h hh r hr k hk hce => hx ⟨g, hg, h, hh, r, hr, k, hk, hce⟩)

/-! ## What the callers assume -/

/-- The arguments of `bandArray` for the row band `β` of `X`, which stands at `aX` row by row. -/
abbrev BandArgs.ofX (p : Par) (β aX mask dig3 dig4 arr : ℕ) : BandArgs :=
  { p := p, β := β, side := 0, aA := aX, sI := p.D, sK := 1, mask := mask, dig3 := dig3,
    dig4 := dig4, arr := arr }

/-- The arguments of `bandArray` for the column band `β` of `Y`, which stands at `aY` row by row. -/
abbrev BandArgs.ofY (p : Par) (β aY mask dig3 dig4 arr : ℕ) : BandArgs :=
  { p := p, β := β, side := 1, aA := aY, sI := 1, sK := p.N, mask := mask, dig3 := dig3,
    dig4 := dig4, arr := arr }

/-- **The specification that the callers of bandArray assume, for a row band of X.** -/
theorem bandArrayL_entry (std : Std lim) (hP : P[pBandArray]? = some bandArrayBody) :
    BandArrayLSpec lim P cBandArray := by
  intro p hmL β aX mask dig3 dig4 arr μ X hsp hX hXle htab hβ d _
  refine ⟨bandArrayBody, hP, bandArray_spec (A := .ofX p β aX mask dig3 dig4 arr)
    { std := std, hmL := hmL, space := hsp, aA_le := hXle, tabs := htab, β_lt := hβ
      T_len := Spec.length_arrL _
      idx := fun row hrow k hk => ?_
      entry := fun g hg h hh r hr k hk => ?_
      zero := fun c hc =>
        Spec.bandArrayL_eq_zero hmL X β c fun g h r k => hc g g.2 h h.2 r r.2 k k.2 }⟩
  · -- The entry (row, k) of X stands at row D + k.
    dsimp only at hrow hk ⊢
    have hroom := Nat.mul_add_le_mul hrow (le_refl p.D)
    omega
  · refine (Spec.bandArrayL_at hmL X β ⟨g, hg⟩ ⟨h, hh⟩ ⟨r, hr⟩ ⟨k, hk⟩).trans ?_
    change padRows X ((BandArgs.ofX p β aX mask dig3 dig4 arr).rowNo g h r) ⟨k, hk⟩ = _
    generalize (BandArgs.ofX p β aX mask dig3 dig4 arr).rowNo g h r = row
    unfold padRows
    by_cases hrow : row < p.N
    · rw [dif_pos hrow, if_pos hrow, ← hX ⟨_, hrow⟩ ⟨k, hk⟩]
      refine congrArg μ ?_
      change aX + row * p.D + k = aX + (row * p.D + k * 1)
      omega
    · rw [dif_neg hrow, if_neg hrow]

/-- **The specification that the callers of bandArray assume, for a column band of Y.** -/
theorem bandArrayR_entry (std : Std lim) (hP : P[pBandArray]? = some bandArrayBody) :
    BandArrayRSpec lim P cBandArray := by
  intro p hmL β aY mask dig3 dig4 arr μ Y hsp hY hYle htab hβ d _
  refine ⟨bandArrayBody, hP, bandArray_spec (A := .ofY p β aY mask dig3 dig4 arr)
    { std := std, hmL := hmL, space := hsp, aA_le := by rwa [Nat.mul_comm], tabs := htab
      β_lt := hβ, T_len := Spec.length_arrR _
      idx := fun row hrow k hk => ?_
      entry := fun g hg h hh r hr k hk => ?_
      zero := fun c hc =>
        Spec.bandArrayR_eq_zero hmL Y β c fun g h r k => hc g g.2 h h.2 r r.2 k k.2 }⟩
  · -- The entry (k, row) of Y stands at k N + row.
    dsimp only at hrow hk ⊢
    have hroom := Nat.mul_add_le_mul hk (le_refl p.N)
    rw [Nat.mul_comm p.N p.D]
    omega
  · refine (Spec.bandArrayR_at hmL Y β ⟨g, hg⟩ ⟨h, hh⟩ ⟨r, hr⟩ ⟨k, hk⟩).trans ?_
    change padCols Y ⟨k, hk⟩ ((BandArgs.ofY p β aY mask dig3 dig4 arr).rowNo g h r) = _
    generalize (BandArgs.ofY p β aY mask dig3 dig4 arr).rowNo g h r = row
    unfold padCols
    by_cases hrow : row < p.N
    · rw [dif_pos hrow, if_pos hrow, ← hY ⟨k, hk⟩ ⟨_, hrow⟩]
      refine congrArg μ ?_
      change aY + k * p.N + row = aY + (row * 1 + k * p.N)
      omega
    · rw [dif_neg hrow, if_neg hrow]

end Light.Sec2
