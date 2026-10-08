/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Instance

/-!
# The wanted entries of a thin matrix product, as inner products

X is an N × D matrix at the address x and Y a D × N matrix at y, both row by row, with entries of
absolute value at most U; the cells from wi and from wj on hold the rows and the columns of w wanted
positions.  thinBrute(N, D, w, U, x, y, wi, wj, out, fr) computes every wanted entry (XY)[I, J] as
the inner product of row I of X and column J of Y, and writes it to the cells from out on.  It is
right on every instance for which D U² fits in a word, so that no partial sum overflows; it is what
the solver of Theorem 5 falls back to outside the regime of the theorem.  At most
40 (w + 1) (D + 1) steps.

bruteInner_spec treats the inner product: after t rounds the sum holds the first t terms
(brutePartial), which stay within a word (abs_brutePartial_le).  bruteRound_spec treats one wanted
position, and thinBrute_spec the loop over the positions.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Brute

/-- Local 10 of thinBrute: the number of the position. -/
abbrev Pos : ℕ := 10
/-- Local 11 of thinBrute: the index t of the inner product. -/
abbrev Idx : ℕ := 11
/-- Local 12 of thinBrute: the address of X[I, t]. -/
abbrev CellX : ℕ := 12
/-- Local 13 of thinBrute: the address of Y[t, J]. -/
abbrev CellY : ℕ := 13
/-- Local 14 of thinBrute: the sum. -/
abbrev Sum : ℕ := 14

end Brute

open ThinArg Brute

/-- The inner product. -/
def bruteInner : Stmt :=
  .while (v Idx <' v Cols) (
    .set Sum (v Sum +' M (v CellX) *' M (v CellY)) ;;
    .set CellX (v CellX +' k 1) ;;
    .set CellY (v CellY +' v Rows) ;;
    .set Idx (v Idx +' k 1))

/-- One wanted position: the inner product, the store, and the step to the next position. -/
def bruteRound : Stmt :=
  .set Idx (k 0) ;;
  .set CellX (v AdrX +' M (v AdrWI +' v Pos) *' v Cols) ;;
  .set CellY (v AdrY +' M (v AdrWJ +' v Pos)) ;;
  .set Sum (k 0) ;;
  bruteInner ;;
  .store (v AdrOut +' v Pos) (v Sum) ;;
  .set Pos (v Pos +' k 1)

/-- thinBrute(N, D, w, U, x, y, wi, wj, out, fr). -/
def thinBruteBody : Stmt :=
  .while (v Pos <' v Wanted) bruteRound

/-- The locals of thinBrute: the arguments, the number i of the position, the index t, the two
addresses px and py, and the sum s.  In the place of U stands whatever number u has been passed: the
program never reads it. -/
def bruteLocs (x : ThinInst) (u : ℤ) (fr i t px py : ℕ) (s : ℤ) : List ℤ :=
  [(x.N : ℤ), (x.D : ℤ), (x.w : ℤ), u, (x.x : ℤ), (x.y : ℤ), (x.wi : ℤ), (x.wj : ℤ), (x.out : ℤ),
    (fr : ℤ), (i : ℤ), (t : ℤ), (px : ℤ), (py : ℤ), s]

/-! ## The partial sums -/

/-- The first n terms of the inner product. -/
def brutePartial (N D : ℕ) (X Y : List ℤ) (I J n : ℕ) : ℤ :=
  ((List.range n).map fun t => X.getD (I * D + t) 0 * Y.getD (t * N + J) 0).sum

/-- One more term. -/
theorem brutePartial_succ (N D : ℕ) (X Y : List ℤ) (I J n : ℕ) :
    brutePartial N D X Y I J (n + 1)
      = brutePartial N D X Y I J n + X.getD (I * D + n) 0 * Y.getD (n * N + J) 0 := by
  simp [brutePartial, List.range_succ]

/-- A term of the inner product is at most U². -/
theorem abs_bruteTerm_le {X Y : List ℤ} {U : ℕ} (hX : AbsLe X U) (hY : AbsLe Y U) (a b : ℕ) :
    |X.getD a 0 * Y.getD b 0| ≤ (U * U : ℕ) := by
  rw [abs_mul]
  push_cast
  exact mul_le_mul (hX.abs_getD_le (by positivity) a) (hY.abs_getD_le (by positivity) b)
    (abs_nonneg _) (by positivity)

/-- The first n terms add up to at most n U². -/
theorem abs_brutePartial_le {N D : ℕ} {X Y : List ℤ} {U : ℕ} (hX : AbsLe X U) (hY : AbsLe Y U)
    (I J n : ℕ) : |brutePartial N D X Y I J n| ≤ n * (U * U : ℕ) := by
  induction n with
  | zero => simp [brutePartial]
  | succ n ih =>
    rw [brutePartial_succ]
    calc |brutePartial N D X Y I J n + X.getD (I * D + n) 0 * Y.getD (n * N + J) 0|
        ≤ |brutePartial N D X Y I J n| + |X.getD (I * D + n) 0 * Y.getD (n * N + J) 0| :=
          abs_add_le _ _
      _ ≤ n * (U * U : ℕ) + (U * U : ℕ) := add_le_add ih (abs_bruteTerm_le hX hY _ _)
      _ = ((n + 1 : ℕ) : ℤ) * (U * U : ℕ) := by push_cast; ring

/-! ## The program -/

/-- **The inner product** of row I of X and column J of Y. -/
theorem bruteInner_spec (std : Std lim) (x : ThinInst) {μ : ℕ → ℤ} {fr i I J : ℕ} {u : ℤ}
    (segX : Seg μ x.x x.X) (segY : Seg μ x.y x.Y) (lX : x.X.length = x.N * x.D)
    (lY : x.Y.length = x.D * x.N) (bX : AbsLe x.X x.U) (bY : AbsLe x.Y x.U) (hI : I < x.N)
    (hJ : J < x.N) (roomX : x.x + x.N * x.D < lim.space) (roomY : x.y + x.D * x.N + x.N < lim.space)
    (hword : ((x.D * (x.U * x.U) : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d bruteInner ⟨frame (bruteLocs x u fr i 0 (x.x + I * x.D) (x.y + J) 0), μ⟩
      (24 * x.D + 4) fun σ' => σ' = ⟨frame (bruteLocs x u fr i x.D (x.x + I * x.D + x.D)
        (x.y + x.D * x.N + J) (brutePartial x.N x.D x.X x.Y I J x.D)), μ⟩ := by
  have hw := std.space_le
  have h100 := std.const_le
  have hID := Nat.mul_add_le_mul hI (le_refl x.D)
  unfold bruteInner
  refine Ends.whileBlock (fun t σ => σ = ⟨frame (bruteLocs x u fr i t (x.x + I * x.D + t)
    (x.y + t * x.N + J) (brutePartial x.N x.D x.X x.Y I J t)), μ⟩) x.D
    (by simp [brutePartial]) ?round ?done
  case round =>
    rintro t _ ht rfl
    have htN := Nat.mul_add_le_mul ht (le_refl x.N)
    have rX : μ (x.x + I * x.D + t) = x.X.getD (I * x.D + t) 0 := by
      rw [Nat.add_assoc]
      exact segX.getD (by omega) 0
    have rY : μ (x.y + t * x.N + J) = x.Y.getD (t * x.N + J) 0 := by
      rw [Nat.add_assoc]
      exact segY.getD (by omega) 0
    have hmono : ∀ n ≤ x.D, ((n : ℤ) * (x.U * x.U : ℕ)) ≤ lim.word := fun n hn =>
      le_trans (by exact_mod_cast Nat.mul_le_mul_right (x.U * x.U) hn) hword
    have hsum := abs_le.mp ((abs_brutePartial_le (N := x.N) (D := x.D) bX bY I J (t + 1)).trans
      (by exact_mod_cast hmono (t + 1) (by omega)))
    have hterm := abs_le.mp ((abs_bruteTerm_le bX bY (I * x.D + t) (t * x.N + J)).trans
      (by simpa using hmono 1 (by omega)))
    have hnext := brutePartial_succ x.N x.D x.X x.Y I J t
    rw [hnext] at hsum
    generalize x.X.getD (I * x.D + t) 0 = a, x.Y.getD (t * x.N + J) 0 = b at *
    generalize hpx : x.x + I * x.D + t = px at *
    generalize hpy : x.y + t * x.N + J = py at *
    have hpx' : (px : ℤ) + 1 = x.x + I * x.D + (t + 1) := by rw [← hpx]; push_cast; ring
    have hpy' : (py : ℤ) + x.N = x.y + (t + 1) * x.N + J := by rw [← hpy]; push_cast; ring
    exact ⟨by simp, by simp [bruteLocs]; omega,
      by light_side [bruteLocs, rX, rY],
      by simp [bruteLocs, update_frame_setLocal, rX, rY, hnext, hpx', hpy']⟩
  case done =>
    rintro _ rfl
    exact ⟨by simp, by simp [bruteLocs], rfl⟩

/-- Before position i: the locals are as in bruteLocs, with anything in the scratch locals, the
entries of the positions before i are in the output, and nothing else has changed. -/
def BruteInv (x : ThinInst) (μ : ℕ → ℤ) (u : ℤ) (fr i : ℕ) (σ : State) : Prop :=
  ∃ (t px py : ℕ) (s : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame (bruteLocs x u fr i t px py s), μ'⟩
    ∧ (∀ j < i, μ' (x.out + j) = thinEntry x.N x.D x.X x.Y (thinI x j) (thinJ x j))
    ∧ SameOutside μ μ' x.out x.w

/-- **One wanted position.** -/
theorem bruteRound_spec (std : Std lim) {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ} {u : ℤ}
    (hpre : x.Pre μ fr) (hsp : fr + x.N + 1 ≤ lim.space)
    (hword : ((x.D * (x.U * x.U) : ℕ) : ℤ) ≤ lim.word) {i : ℕ} (hi : i < x.w) {σ : State}
    (h : BruteInv x μ u fr i σ) :
    Ends lim P d bruteRound σ (24 * x.D + 33) (BruteInv x μ u fr (i + 1)) := by
  obtain ⟨t, px, py, s, μ', rfl, hdone, hfr⟩ := h
  have hw := std.space_le
  have h100 := std.const_le
  have hbelow := And.intro hpre.belowX (And.intro hpre.belowY (And.intro hpre.belowWI
    (And.intro hpre.belowWJ hpre.belowOut)))
  have hI := thinI_lt hpre hi
  have hJ := thinJ_lt hpre hi
  have segX : Seg μ' x.x x.X :=
    hpre.segX.of_sameOutside hfr (by rw [hpre.lenX]; exact hpre.apartX.symm)
  have segY : Seg μ' x.y x.Y :=
    hpre.segY.of_sameOutside hfr (by rw [hpre.lenY]; exact hpre.apartY.symm)
  have rI : μ' (x.wi + i) = (thinI x i : ℕ) := by
    rw [hfr _ (by rcases hpre.apartWI with h | h <;> omega)]
    exact mem_thinI hpre hi
  have rJ : μ' (x.wj + i) = (thinJ x i : ℕ) := by
    rw [hfr _ (by rcases hpre.apartWJ with h | h <;> omega)]
    exact mem_thinJ hpre hi
  have hID := Nat.mul_add_le_mul hI (le_refl x.D)
  have hND : x.N ≤ x.D * x.N := Nat.le_mul_of_pos_left _ hpre.D_pos
  unfold bruteRound bruteLocs
  -- t := 0; px := x + mem[wi + i] * D; py := y + mem[wj + i]; s := 0
  light_set 0
  light_set (x.x + thinI x i * x.D : ℕ) using rI
  light_set (x.y + thinJ x i : ℕ) using rJ
  light_set 0
  -- the inner product
  refine Ends.next (24 * x.D + 4) ((bruteInner_spec std x (i := i) segX segY hpre.lenX hpre.lenY
    hpre.leX hpre.leY hI hJ (by omega) (by omega) hword).mono le_rfl ?_)
  rintro _ rfl
  unfold bruteLocs
  -- mem[out + i] := s; i := i + 1
  light_store (x.out + i) (brutePartial x.N x.D x.X x.Y (thinI x i) (thinJ x i) x.D)
  light_set (i + 1 : ℕ)
  refine ⟨_, _, _, _, _, rfl, fun j hj => ?_,
    hfr.update ⟨by omega, by omega⟩ _⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
  · rw [Function.update_of_ne (by omega)]
    exact hdone j hlt
  · rw [Function.update_self]
    rfl

/-- **The brute force is right on every instance** for which D U² fits in a word.  It needs N + 1
cells above the free pointer only as room for addresses that are formed and never used. -/
theorem thinBrute_spec (std : Std lim) (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) (u : ℤ)
    (hpre : x.Pre μ fr) (hsp : fr + x.N + 1 ≤ lim.space)
    (hword : ((x.D * (x.U * x.U) : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d thinBruteBody
      ⟨frame [(x.N : ℤ), (x.D : ℤ), (x.w : ℤ), u, (x.x : ℤ), (x.y : ℤ), (x.wi : ℤ), (x.wj : ℤ),
        (x.out : ℤ), (fr : ℤ)], μ⟩
      (40 * ((x.w + 1) * (x.D + 1))) fun σ' => thinTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  unfold thinBruteBody
  refine Ends.whileConst (BruteInv x μ u fr) x.w (24 * x.D + 33) ?start ?round ?done ?time
  case start =>
    exact ⟨0, 0, 0, 0, μ, by rw [← frame_append_zeros _ 5]; rfl, fun j hj => absurd hj (by omega),
      SameOutside.refl⟩
  case round =>
    intro i σ hi h
    refine ⟨?_, ?_, bruteRound_spec std hpre hsp hword hi h⟩ <;>
      obtain ⟨t, px, py, s, μ', rfl, -, -⟩ := h
    · simp
    · simpa [bruteLocs] using hi
  case done =>
    rintro _ ⟨t, px, py, s, μ', rfl, hdone, hfr⟩
    refine ⟨by simp, by simp [bruteLocs], fun i hi => ?_, fun a ha => hfr a ha.2⟩
    have hi' : i < x.w := by rwa [length_thinOut hpre] at hi
    change μ' (x.out + i) = _
    rw [hdone i hi', ← getD_thinOut hpre hi', List.getD_eq_getElem _ _ hi]
  case time =>
    have hleft : x.w * (4 + (24 * x.D + 33)) = 24 * (x.w * x.D) + 37 * x.w := by ring
    have hright : (x.w + 1) * (x.D + 1) = x.w * x.D + x.w + x.D + 1 := by ring
    simp
    omega

end Light.Sec2
