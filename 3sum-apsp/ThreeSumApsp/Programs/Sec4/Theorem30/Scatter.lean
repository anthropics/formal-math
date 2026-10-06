/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts

/-!
# A string put at the levels of the inner set

Proof of Theorem 30: a query forms each leaf or box "from the private leaf".  The output string is
the list of its L digits, and the levels of its inner set are the positions of the digit 9.  The
routine copies this list and replaces its digits 9, from the left, by the digits of a second string
(`Spec.scatter`).  If star = 1, the leading digits 9 of the second string (the levels of F_V,
Section 4.2) are written as stars (`Spec.starRunIf`).

One pass, with a pointer into the second string and a flag that says whether the leading run of
nines is still going on.  `Scatter.scatter_step` says what the first digit of
`scatter w (starRunIf flag s)` is and how the rest looks, in terms of the digit, the flag and the
pointer that the program computes (`outDigit`, `nextRun`, `nextPtr`); `Scatter.round_runs` says
that a round of the program computes them.  The invariant (`Scatter.Inv`) is that the digits written
so far, followed by what is still to be written, are the whole string.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

namespace Scatter

/-! ## One more digit -/

/-- The digit written at a position where the first string has x and the pointer is at a digit y of
the second string; run = 1 says that the leading run of nines is still going on. -/
def outDigit (x y run : ℕ) : ℕ :=
  if x = 9 then (if y = 9 then (if run = 1 then 10 else 9) else y) else x

/-- The flag after that position: a digit other than 9 of the second string ends the run. -/
def nextRun (x y run : ℕ) : ℕ := if x = 9 ∧ y ≠ 9 then 0 else run

/-- The pointer after that position. -/
def nextPtr (x o : ℕ) : ℕ := if x = 9 then o + 1 else o

/-- The first digit of what is still to be written, and the rest. -/
private theorem scatter_step {w s : List ℕ} {i o : ℕ} (run : ℕ) (hi : i < w.length)
    (ho : w.getD i 0 = 9 → o < s.length) :
    scatter (w.drop i) (starRunIf (decide (run = 1)) (s.drop o)) =
      outDigit (w.getD i 0) (s.getD o 0) run :: scatter (w.drop (i + 1))
        (starRunIf (decide (nextRun (w.getD i 0) (s.getD o 0) run = 1))
          (s.drop (nextPtr (w.getD i 0) o))) := by
  rw [List.drop_eq_getElem_cons hi, ← List.getD_eq_getElem w 0 hi]
  generalize w.getD i 0 = x at ho ⊢
  by_cases hx : x = 9
  · rw [List.drop_eq_getElem_cons (ho hx), ← List.getD_eq_getElem s 0 (ho hx), hx]
    generalize s.getD o 0 = y
    by_cases hy : y = 9
    · rw [hy, starRunIf_nine_cons, scatter_nine_cons]
      by_cases hrun : run = 1 <;> simp [outDigit, nextRun, nextPtr, hrun]
    · rw [starRunIf_cons_of_ne hy, scatter_nine_cons]
      simp [outDigit, nextRun, nextPtr, hy]
  · rw [scatter_cons_of_ne hx]
    simp [outDigit, nextRun, nextPtr, hx]

/-- After i positions: the digits written so far, the flag and the pointer. -/
structure Progress (star : Bool) (wl sl : List ℕ) (i run o : ℕ) (done : List ℕ) : Prop where
  length : done.length = i
  /-- The pointer has passed one digit for each nine of the first string. -/
  ptr : o = (wl.take i).count 9
  /-- The digits written, followed by what is still to be written, are the whole string. -/
  rest : done ++ scatter (wl.drop i) (starRunIf (decide (run = 1)) (sl.drop o))
    = scatter wl (starRunIf star sl)

theorem Progress.zero (star : Bool) (wl sl : List ℕ) :
    Progress star wl sl 0 (if star then 1 else 0) 0 [] :=
  ⟨rfl, rfl, by cases star <;> rfl⟩

section

variable {star : Bool} {wl sl done : List ℕ} {i run o : ℕ}

/-- At a nine of the first string the pointer is inside the second string. -/
theorem Progress.ptr_lt (h : Progress star wl sl i run o done) (hi : i < wl.length)
    (hsl : sl.length = wl.count 9) (h9 : wl.getD i 0 = 9) : o < sl.length := by
  have hle : (wl.take (i + 1)).count 9 ≤ wl.count 9 := (List.take_sublist _ _).count_le _
  rw [List.count_take_succ_getD wl 9 hi 0, if_pos h9, ← h.ptr] at hle
  omega

/-- One more position: the digit, the flag and the pointer are those that the three functions
give. -/
theorem Progress.succ (h : Progress star wl sl i run o done) (hi : i < wl.length)
    (hsl : sl.length = wl.count 9) :
    Progress star wl sl (i + 1) (nextRun (wl.getD i 0) (sl.getD o 0) run)
      (nextPtr (wl.getD i 0) o) (done ++ [outDigit (wl.getD i 0) (sl.getD o 0) run]) where
  length := by rw [List.length_append, h.length, List.length_singleton]
  ptr := by
    rw [List.count_take_succ_getD wl 9 hi 0, ← h.ptr, nextPtr]
    split_ifs <;> rfl
  rest := by
    rw [List.append_assoc, List.singleton_append, ← scatter_step run hi (h.ptr_lt hi hsl)]
    exact h.rest

end

/-! ## The program -/

/-- The local variables of scatter: the arguments (the addresses of the two strings and of the
copy, the length, and the flag, whose first value is the argument star), the position, the pointer
into the second string, and the digit to be written. -/
abbrev First : ℕ := 0
@[inherit_doc First] abbrev Second : ℕ := 1
@[inherit_doc First] abbrev Dst : ℕ := 2
@[inherit_doc First] abbrev Len : ℕ := 3
@[inherit_doc First] abbrev Run : ℕ := 4
@[inherit_doc First] abbrev Pos : ℕ := 5
@[inherit_doc First] abbrev Ptr : ℕ := 6
@[inherit_doc First] abbrev Digit : ℕ := 7

end Scatter

open Scatter

/-- One round: read a digit of the first string; if it is a nine, take the next digit of the second
string in its place, as a star if it is a nine of the leading run; write the digit, and go on. -/
def scatterRound : Stmt :=
  .set Digit (M (v First +' v Pos)) ;;
  .ite (v Digit =' k 9) (
    .set Digit (M (v Second +' v Ptr)) ;;
    .set Ptr (v Ptr +' k 1) ;;
    .ite (v Digit =' k 9)
      (.ite (v Run =' k 1) (.set Digit (k 10)) .skip)
      (.set Run (k 0)))
    .skip ;;
  .store (v Dst +' v Pos) (v Digit) ;;
  .set Pos (v Pos +' k 1)

/-- scatter(first, second, dst, len, star): copy the first string, with the digits of the second
string in place of its nines.  The locals that are not arguments start at 0. -/
def scatterBody : Stmt := .while (v Pos <' v Len) scatterRound

namespace Scatter

private theorem round_cost : scatterRound.blockCost = 37 := rfl

/-- What a round does, for the digit x of the first string and the digit y of the second string at
the pointer. -/
private theorem round_runs {lim : Limits} (hs : Std lim) {μ : ℕ → ℤ}
    {w s out L run i o dg x y : ℕ} (hw : w + L < lim.space) (hout : out + L < lim.space)
    (hi : i < L) (hx : μ (w + i) = x) (hy : x = 9 → μ (s + o) = y ∧ s + o + 1 < lim.space) :
    scatterRound.Runs lim ⟨frame [w, s, out, L, run, i, o, dg], μ⟩
      (· = ⟨frame [w, s, out, L, nextRun x y run, (i + 1 : ℕ), nextPtr x o, outDigit x y run],
        Function.update μ (out + i) (outDigit x y run)⟩) := by
  light_facts hs
  have hcastx : ((x : ℤ) = 9) = (x = 9) := by norm_cast
  have hcasty : ((y : ℤ) = 9) = (y = 9) := by norm_cast
  have hcastr : ((run : ℤ) = 1) = (run = 1) := by norm_cast
  have haddr : ((out : ℤ) + i).toNat = out + i := by omega
  simp only [scatterRound, outDigit, nextRun, nextPtr]
  -- The tests of the program: a nine of the first string, a nine of the second, the flag.  In each
  -- case the block is run: the first goal says that every address is in range and every value fits
  -- in a word, the second that the last state is the one stated.
  by_cases h9 : x = 9
  · obtain ⟨hcell, hptr⟩ := hy h9
    by_cases hy9 : y = 9 <;> by_cases hrun : run = 1 <;> constructor <;>
      simp [Limits.Addr, abs_le, update_frame_setLocal, *] <;>
      omega
  · constructor <;> simp [Limits.Addr, abs_le, update_frame_setLocal, *]
    omega

/-- Before round i the first i digits have been written at out. -/
def Inv (w s out : ℕ) (star : Bool) (wl sl : List ℕ) (μ : ℕ → ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (run o dg : ℕ) (done : List ℕ),
    σ = ⟨frame [w, s, out, wl.length, run, i, o, dg], μ'⟩ ∧ Progress star wl sl i run o done ∧
      SegN μ' out done ∧ SameOutside μ μ' out wl.length

end Scatter

/-- **scatter** writes `Spec.scatter wl (starRunIf star sl)`. -/
theorem scatter_spec {lim : Limits} {P : Program} (hP : P[Proc.scatter]? = some scatterBody)
    (hs : Std lim) : ScatterSpec lim P := by
  rintro w s out _ star wl sl μ hfirst hsecond rfl hsl hapartW hapartS hw_in hs_in hout_in
  refine fun d _ => ⟨scatterBody, hP, ?_⟩
  unfold tScatter
  -- while pos < len
  refine Ends.whileBlock (Inv w s out star wl sl μ) wl.length ?start ?round ?done
    (by simp [round_cost]; omega)
  case start =>
    refine ⟨μ, _, 0, 0, [], ?_, Progress.zero star wl sl, Seg.nil, .refl⟩
    refine congrArg (State.mk · μ) ((frame_append_zeros _ 3).symm.trans ?_)
    cases star <;> rfl
  case round =>
    rintro i _ hi ⟨μ', run, o, dg, done, rfl, hprog, hdone, hsame⟩
    have hx : μ' (w + i) = (wl.getD i 0 : ℕ) :=
      (hsame _ (by omega)).trans (hfirst.read hi)
    have hy : wl.getD i 0 = 9 → μ' (s + o) = (sl.getD o 0 : ℕ) ∧ s + o + 1 < lim.space :=
      fun h9 => by
        have hptr := hprog.ptr_lt hi hsl h9
        exact ⟨(hsame _ (by omega)).trans (hsecond.read hptr), by omega⟩
    refine ⟨by simp, by simp; omega, (round_runs hs hw_in hout_in hi hx hy).mono fun σ' hσ' =>
      ⟨_, _, _, _, _, hσ', hprog.succ hi hsl, ?_, hsame.update ⟨by omega, by omega⟩ _⟩⟩
    have hsnoc := hdone.snoc (outDigit (wl.getD i 0) (sl.getD o 0) run)
    rwa [hprog.length] at hsnoc
  case done =>
    rintro _ ⟨μ', run, o, dg, done, rfl, hprog, hdone, hsame⟩
    have hall : done = scatter wl (starRunIf star sl) := by
      have hrest := hprog.rest
      rwa [List.drop_length, scatter, List.append_nil] at hrest
    exact ⟨by simp, by simp, hall ▸ hdone, hsame⟩

end Light.Sec4
