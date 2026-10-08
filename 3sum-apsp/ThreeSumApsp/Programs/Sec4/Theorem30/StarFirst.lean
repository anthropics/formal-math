/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts

/-!
# The lowest symbols P₀ of a leaf turned into stars

Proof of Lemma 29: "A box in which f of the symbols are P₀ or stars is obtained from a leaf of order
m - f […] by turning the e lowest symbols P₀ of that leaf into stars, for some e ≤ f."  The routine
copies a string of L digits and writes 10 (the star) in place of its first e digits 9
(`Spec.starFirst`).  It returns the position of the last star of the copy, "the highest level at
which π has a star" (proof of Lemma 29), which the dynamic program of Lemma 29 expands
(`Spec.lastStar`).

One pass that keeps two numbers: how many nines have been turned into stars so far, and the
position of the last star so far.  The first section says how one more digit changes the copy and
the two numbers; `StarFirst.round_runs` says that a round of the program does just this;
`StarFirst.Inv` is the invariant of the loop.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## One more digit -/

/-- The last star of a list with one more digit. -/
private theorem lastStar_concat (l : List ℕ) (x : ℕ) :
    lastStar (l ++ [x]) = if x = 10 then some l.length else lastStar l := by
  induction l with
  | nil => simp [lastStar]
  | cons d l ih =>
    rw [List.cons_append, lastStar, ih, lastStar]
    by_cases hx : x = 10
    · simp [hx]
    · simp only [hx, if_false]

namespace StarFirst

variable {e i : ℕ} {l : List ℕ}

/-- The number of nines among the first i digits that are turned into stars. -/
def turned (e : ℕ) (l : List ℕ) (i : ℕ) : ℕ := min e ((l.take i).count 9)

/-- The position of the last star among the first i digits of the copy (0 if there is none). -/
def lastPos (e : ℕ) (l : List ℕ) (i : ℕ) : ℕ := (lastStar ((starFirst e l).take i)).getD 0

/-- The digit of the copy: a nine becomes a star as long as fewer than e nines have been turned. -/
private theorem getD_starFirst_eq (e : ℕ) (l : List ℕ) (i : ℕ) :
    (starFirst e l).getD i 0 = if l.getD i 0 = 9 ∧ turned e l i < e then 10 else l.getD i 0 := by
  rw [getD_starFirst, turned]
  simp

private theorem turned_zero : turned e l 0 = 0 := by simp [turned]

/-- One more digit: a nine is turned as long as fewer than e have been. -/
private theorem turned_succ (hi : i < l.length) :
    turned e l (i + 1) = if l.getD i 0 = 9 ∧ turned e l i < e then turned e l i + 1
      else turned e l i := by
  rw [turned, turned, List.count_take_succ_getD l 9 hi 0]
  split_ifs <;> omega

/-- One more digit: a star moves the position of the last star. -/
private theorem lastPos_succ (hi : i < l.length) :
    lastPos e l (i + 1) = if (starFirst e l).getD i 0 = 10 then i else lastPos e l i := by
  have hi' : i < (starFirst e l).length := by rwa [length_starFirst]
  rw [lastPos, lastPos, List.take_succ_getD _ hi' 0, lastStar_concat, List.length_take,
    Nat.min_eq_left hi'.le]
  split_ifs <;> rfl

/-! ## The program -/

/-- The local variables of starFirst: the arguments (the address of the string, the address of the
copy, the length, the number of stars), the position, the position of the last star so far, the
digit, and the number of nines turned into stars so far.  Local 0 also takes the result. -/
abbrev Src : ℕ := 0
@[inherit_doc Src] abbrev Result : ℕ := 0
@[inherit_doc Src] abbrev Dst : ℕ := 1
@[inherit_doc Src] abbrev Len : ℕ := 2
@[inherit_doc Src] abbrev Stars : ℕ := 3
@[inherit_doc Src] abbrev Pos : ℕ := 4
@[inherit_doc Src] abbrev Last : ℕ := 5
@[inherit_doc Src] abbrev Digit : ℕ := 6
@[inherit_doc Src] abbrev Turned : ℕ := 7

end StarFirst

open StarFirst

/-- One round: read a digit, turn it into a star if it is one of the first e nines, remember the
position if a star is written, write the digit, and go on. -/
def starFirstRound : Stmt :=
  .set Digit (M (v Src +' v Pos)) ;;
  .ite (v Digit =' k 9)
    (.ite (v Turned <' v Stars) (.set Digit (k 10) ;; .set Turned (v Turned +' k 1)) .skip) .skip ;;
  .ite (v Digit =' k 10) (.set Last (v Pos)) .skip ;;
  .store (v Dst +' v Pos) (v Digit) ;;
  .set Pos (v Pos +' k 1)

/-- starFirst(src, dst, len, stars): copy the string, with its first nines as stars, and return the
position of the last star.  The locals that are not arguments start at 0. -/
def starFirstBody : Stmt :=
  .while (v Pos <' v Len) starFirstRound ;;
  .set Result (v Last)

namespace StarFirst

private theorem round_cost : starFirstRound.blockCost = 34 := rfl

/-- What a round does, for the digit x that is read, with c nines turned and the last star at p. -/
private theorem round_runs {lim : Limits} (hs : Std lim) {μ : ℕ → ℤ} {cur box L e i p x dg c : ℕ}
    (hcur : cur + L < lim.space) (hbox : box + L < lim.space) (hi : i < L) (hc : c ≤ i)
    (hcell : μ (cur + i) = x) :
    starFirstRound.Runs lim ⟨frame [cur, box, L, e, i, p, dg, c], μ⟩
      (· = ⟨frame [cur, box, L, e, (i + 1 : ℕ),
          ((if (if x = 9 ∧ c < e then 10 else x) = 10 then i else p : ℕ) : ℤ),
          ((if x = 9 ∧ c < e then 10 else x : ℕ) : ℤ),
          ((if x = 9 ∧ c < e then c + 1 else c : ℕ) : ℤ)],
        Function.update μ (box + i) ((if x = 9 ∧ c < e then 10 else x : ℕ) : ℤ)⟩) := by
  light_facts hs
  have hcast9 : ((x : ℤ) = 9) = (x = 9) := by norm_cast
  have hcast10 : ((x : ℤ) = 10) = (x = 10) := by norm_cast
  have haddr : ((box : ℤ) + i).toNat = box + i := by omega
  simp only [starFirstRound]
  -- The tests of the program: a nine, fewer than e turned, a star.  In each case the block is run:
  -- the first goal says that every address is in range and every value fits in a word, the second
  -- that the last state is the one stated.
  by_cases h9 : x = 9 <;> by_cases hlt : c < e <;> by_cases h10 : x = 10 <;> constructor <;>
    simp [Limits.Addr, abs_le, update_frame_setLocal, *] <;>
    omega

/-- Before round i the first i digits of the copy have been written, and the two counters are up to
date. -/
def Inv (cur box e : ℕ) (l : List ℕ) (μ : ℕ → ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (dg : ℕ),
    σ = ⟨frame [cur, box, l.length, e, i, lastPos e l i, dg, turned e l i], μ'⟩ ∧
      SegN μ' box ((starFirst e l).take i) ∧ SameOutside μ μ' box l.length

end StarFirst

/-- **starFirst** writes the copy with the first e nines as stars, and returns the position of its
last star. -/
theorem starFirst_spec {lim : Limits} {P : Program} (hP : P[Proc.starFirst]? = some starFirstBody)
    (hs : Std lim) : StarFirstSpec lim P := by
  rintro cur box _ e l μ hseg rfl hapart hcur hbox
  refine fun d _ => ⟨starFirstBody, hP, ?_⟩
  have hlen : (starFirst e l).length = l.length := length_starFirst e l
  unfold tStarFirst
  -- while pos < len
  refine Ends.next _ (Ends.whileBlock (Inv cur box e l μ) l.length ?start ?round ?done
    (hT := le_rfl)) (by simp [round_cost]; omega)
  case start =>
    refine ⟨μ, 0, ?_, Seg.nil, .refl⟩
    rw [turned_zero]
    exact congrArg (State.mk · μ) (frame_append_zeros _ 4).symm
  case round =>
    rintro i _ hi ⟨μ', dg, rfl, hcopy, hsame⟩
    have hcell : μ' (cur + i) = (l.getD i 0 : ℕ) :=
      (hsame _ (by omega)).trans (hseg.read hi)
    have hturned : turned e l i ≤ i :=
      (min_le_right _ _).trans (List.count_le_length.trans (List.length_take_le _ _))
    refine ⟨by simp, by simp; omega,
      (round_runs hs hcur hbox hi hturned hcell).mono fun σ' hσ' => ?_⟩
    rw [← getD_starFirst_eq, ← turned_succ hi, ← lastPos_succ hi] at hσ'
    refine ⟨_, _, hσ', ?_, hsame.update ⟨by omega, by omega⟩ _⟩
    have hsnoc := hcopy.snoc ((starFirst e l).getD i 0)
    rwa [List.length_take, hlen, Nat.min_eq_left hi.le,
      ← List.take_succ_getD _ (hlen ▸ hi) 0] at hsnoc
  case done =>
    rintro _ ⟨μ', dg, rfl, hcopy, hsame⟩
    rw [← hlen, List.take_length] at hcopy
    refine ⟨by simp, by simp, ?_⟩
    simp only [round_cost]
    -- return last
    light_set (lastPos e l l.length)
    refine ⟨hcopy, ?_, hsame⟩
    rw [lastPos, ← hlen, List.take_length]
    rfl

end Light.Sec4
