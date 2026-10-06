/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.Theorem30.NineFirst
public import ThreeSumApsp.Spec.Sec4.Theorem30.NineScan

/-!
# The next string of the enumeration

nineNext(a, n, lo, hi) replaces the string of n digits at a by the next string with between lo and
hi nines (`Spec.nineNext`), and returns 1; if the string is the last one, it leaves it and
returns 0.  This is the step of all three enumerations of Section 4 (proof of Lemma 29: "Generating
the boxes with e stars […] also takes O(L) operations per box"; proof of Theorem 30: "Enumerating
them also takes O(L) operations per number").

There are two passes, as in `Spec.nineNext_eq_scan`.
1. The first pass finds the last position that can be raised and the number of nines before it.  One
   round is `Spec.nineScanStep` (`scanRound_runs`), so after i rounds the locals hold
   `Spec.nineScan hi l i` (`ScanInv`).
2. The second pass computes how many nines are needed behind that position (`needStmt_runs`), raises
   the digit and writes the least admissible filling behind it (`fillTail_spec`).  What stands in
   the memory then is `Spec.raiseAt` (`segN_raiseAt`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Nine

/-- The further local variables of nineNext: the largest number of nines, the state of the scan
(whether a position that can be raised has been found, the last such position, the number of nines
before it, the number of nines seen so far), and a digit. -/
abbrev MaxNines : ℕ := 3
@[inherit_doc MaxNines] abbrev Found : ℕ := 5
@[inherit_doc MaxNines] abbrev Best : ℕ := 6
@[inherit_doc MaxNines] abbrev Before : ℕ := 7
@[inherit_doc MaxNines] abbrev Nines : ℕ := 8
@[inherit_doc MaxNines] abbrev Digit : ℕ := 9

end Nine

open Nine

/-! ## The first pass -/

/-- Remember the current position and the number of nines before it. -/
def markStmt : Stmt := .set Found (k 1) ;; .set Best (v Pos) ;; .set Before (v Nines)

/-- If the digit can be raised, remember its position. -/
def raiseTest : Stmt :=
  .ite (v Digit <' k 8) markStmt
    (.ite (v Digit =' k 8) (.ite (v Nines <' v MaxNines) markStmt .skip) .skip)

/-- One round of the scan: read the digit at the current position, remember the position if the
digit can be raised, count the digit if it is a nine, and go on. -/
def scanRound : Stmt :=
  .set Digit (M (v Str +' v Pos)) ;;
  raiseTest ;;
  .ite (v Digit =' k 9) (.set Nines (v Nines +' k 1)) .skip ;;
  .set Pos (v Pos +' k 1)

private theorem scanRound_cost : scanRound.blockCost = 35 := rfl

/-- The locals during the scan: the arguments, the position i, the state s of the scan, and the
digit read last. -/
def scanFrame (a n lo hi i : ℕ) (s : NineScan) (dg : ℕ) : ℕ → ℤ :=
  frame [a, n, lo, hi, i, s.found, s.pos, s.before, s.nines, dg]

/-- One round of the scan is `Spec.nineScanStep`. -/
private theorem scanRound_runs (hs : Std lim) {μ : ℕ → ℤ} {a n lo hi i dg dg' : ℕ} {s : NineScan}
    (ha : a + n < lim.space) (hi' : i < n) (hcell : μ (a + i) = dg) (hnines : s.nines ≤ i) :
    scanRound.Runs lim ⟨scanFrame a n lo hi i s dg', μ⟩
      (· = ⟨scanFrame a n lo hi (i + 1) (nineScanStep hi i dg s) dg, μ⟩) := by
  light_facts hs
  have hcast8 : ((dg : ℤ) = 8) = (dg = 8) := by norm_cast
  have hcast9 : ((dg : ℤ) = 9) = (dg = 9) := by norm_cast
  simp only [scanRound, raiseTest, markStmt, scanFrame, nineScanStep, canRaise]
  -- The tests of the program tell five cases apart: the digit is below 8; it is 8, and one more
  -- nine is allowed or not; it is 9; it is above 9.  In each case the block is run: the first goal
  -- says that every address is in range and every value fits in a word, the second that the last
  -- state is the one stated.
  have hcases : (dg < 8 ∧ dg ≠ 8 ∧ dg ≠ 9) ∨ (dg = 8 ∧ s.nines < hi) ∨ (dg = 8 ∧ ¬ s.nines < hi) ∨
      dg = 9 ∨ (¬ dg < 8 ∧ dg ≠ 8 ∧ dg ≠ 9) := by omega
  rcases hcases with ⟨h₁, h₂, h₃⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl | ⟨h₁, h₂, h₃⟩ <;> constructor <;>
    simp [Limits.Addr, abs_le, update_frame_setLocal, *] <;>
    omega

/-- Before round i the locals hold the state of the scan after i cells.  The memory is not
changed. -/
def ScanInv (a lo hi : ℕ) (l : List ℕ) (μ : ℕ → ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ dg : ℕ, σ = ⟨scanFrame a l.length lo hi i (nineScan hi l i) dg, μ⟩

/-! ## The second pass -/

/-- The digit at the position found, and the number of nines that have to be written behind it:
lo - before, less one if the digit becomes a nine, and not below 0. -/
def needStmt : Stmt :=
  .set Digit (M (v Str +' v Best)) ;;
  .set Need (v MinNines -' v Before) ;;
  .ite (v Digit =' k 8) (.set Need (v Need -' k 1)) .skip ;;
  .ite (v Need <' k 0) (.set Need (k 0)) .skip

private theorem needStmt_cost : needStmt.blockCost = 23 := rfl

/-- needStmt computes the subtraction of natural numbers in `Spec.raiseAt`. -/
private theorem needStmt_runs (hs : Std lim) {μ : ℕ → ℤ} {a n lo hi i dg dg' : ℕ} {s : NineScan}
    (ha : a + n < lim.space) (hp : s.pos < n) (hcell : μ (a + s.pos) = dg) (hlo : lo ≤ n)
    (hbefore : s.before ≤ n) :
    needStmt.Runs lim ⟨scanFrame a n lo hi i s dg', μ⟩
      (· = ⟨frame [a, n, lo, hi, i, s.found, s.pos, s.before, s.nines, dg,
        ((lo - s.before - (if dg = 8 then 1 else 0) : ℕ) : ℤ)], μ⟩) := by
  light_facts hs
  have hcast8 : ((dg : ℤ) = 8) = (dg = 8) := by norm_cast
  have hzero₁ : (lo : ℤ) - s.before - 1 < 0 → lo - s.before - 1 = 0 := by omega
  have hcast₁ : ¬ (lo : ℤ) - s.before - 1 < 0 →
      ((lo - s.before - 1 : ℕ) : ℤ) = (lo : ℤ) - s.before - 1 := by omega
  have hzero₀ : (lo : ℤ) - s.before < 0 → lo - s.before = 0 := by omega
  have hcast₀ : ¬ (lo : ℤ) - s.before < 0 → ((lo - s.before : ℕ) : ℤ) = (lo : ℤ) - s.before := by
    omega
  simp only [needStmt, scanFrame]
  -- The tests of the program tell four cases apart: whether the digit is an 8, and whether the
  -- difference that is then formed is negative.  In each case the block is run (first goal:
  -- everything is in range; second goal: the last state is the one stated).
  have hcases : (dg = 8 ∧ (lo : ℤ) - s.before - 1 < 0) ∨ (dg = 8 ∧ ¬ (lo : ℤ) - s.before - 1 < 0) ∨
      (dg ≠ 8 ∧ (lo : ℤ) - s.before < 0) ∨ (dg ≠ 8 ∧ ¬ (lo : ℤ) - s.before < 0) := by omega
  rcases hcases with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨h₁, h⟩ | ⟨h₁, h⟩ <;> constructor <;>
    simp [Limits.Addr, abs_le, update_frame_setLocal, *] <;>
    omega

/-- The string with the digits before p kept, the digit at p raised and the least filling behind it
is `Spec.raiseAt`. -/
private theorem segN_raiseAt {μ μ' : ℕ → ℤ} {a lo p c : ℕ} {l : List ℕ} (hseg : SegN μ a l)
    (hp : p < l.length) (hkeep : ∀ b < a + p, μ' b = μ b)
    (hdigit : μ' (a + p) = (l.getD p 0 + 1 : ℕ))
    (htail : SegN μ' (a + (p + 1))
      (nineFirst (l.length - (p + 1)) (lo - c - if l.getD p 0 = 8 then 1 else 0))) :
    SegN μ' a (raiseAt lo p c l) := by
  have hlen : a + (List.map (fun x : ℕ => (x : ℤ)) (l.take p)).length = a + p := by
    rw [List.length_map, List.length_take, min_eq_left hp.le]
  rw [raiseAt, SegN, List.map_append, seg_append, List.map_cons, seg_cons, hlen, Nat.sub_sub,
    List.map_take]
  exact ⟨(hseg.take p).congr fun i hi => hkeep _ (by simp at hi; omega), hdigit, htail⟩

/-- The second pass: raise the digit at the position found, and write the least admissible filling
behind it. -/
def raiseStmt : Stmt :=
  needStmt ;;
  .store (v Str +' v Best) (v Digit +' k 1) ;;
  .set Pos (v Best +' k 1) ;;
  fillTail ;;
  .set Result (k 1)

/-- The second pass writes `Spec.raiseAt` for the position that the scan has found, and
returns 1. -/
private theorem raiseStmt_spec (hs : Std lim) {μ : ℕ → ℤ} {a lo hi dg' : ℕ} {l : List ℕ}
    (hseg : SegN μ a l) (ha : a + l.length < lim.space) (hlo : lo ≤ l.count 9)
    (hfound : (nineScan hi l l.length).found = 1) :
    Ends lim P d raiseStmt ⟨scanFrame a l.length lo hi l.length (nineScan hi l l.length) dg', μ⟩
      (15 * l.length + 46) fun σ' =>
        SegN σ'.mem a
          (raiseAt lo (nineScan hi l l.length).pos (nineScan hi l l.length).before l) ∧
        σ'.loc 0 = 1 ∧ SameOutside μ σ'.mem a l.length := by
  light_facts hs
  have hinv := nineScan_inv hi l le_rfl
  generalize nineScan hi l l.length = s at hinv hfound ⊢
  have hp := hinv.pos_lt hfound
  have hdigit_le := le_of_canRaise (hinv.canRaise hfound)
  have hfits := raise_fits hp hdigit_le hlo
  rw [← hinv.before hfound] at hfits
  have hbefore : s.before ≤ l.length := by
    rw [hinv.before hfound]
    exact List.count_le_length.trans (List.length_take_le' _ _)
  have hlon : lo ≤ l.length := hlo.trans List.count_le_length
  have hcost := needStmt_cost
  obtain ⟨dg, hdg⟩ : ∃ dg, l.getD s.pos 0 = dg := ⟨_, rfl⟩
  obtain ⟨need, hneed⟩ : ∃ need, lo - s.before - (if dg = 8 then 1 else 0) = need := ⟨_, rfl⟩
  have hneed_le : need ≤ lo - s.before := hneed ▸ Nat.sub_le _ _
  rw [hdg] at hdigit_le
  -- digit := mem[str + best]; need := max (lo - before - [digit = 8]) 0
  refine Ends.next _ (Ends.block
    ((needStmt_runs hs ha hp (hdg ▸ hseg.read hp) hlon hbefore).mono ?_) le_rfl)
  rintro _ rfl
  rw [hneed]
  -- mem[str + best] := digit + 1
  light_store (a + s.pos) (dg + 1 : ℕ)
  -- pos := best + 1
  light_set (s.pos + 1 : ℕ)
  -- fillTail
  light_piece (fillTail_spec hs (i₀ := s.pos + 1) (need := need) ha (by omega) _ rfl rfl rfl
    rfl) with ⟨_, μ'⟩ ⟨rfl, htail, hsame⟩
  -- return 1
  refine Ends.setLast ⟨segN_raiseAt hseg hp (fun b hb => ?_) ?_ (by rw [hdg, hneed]; exact htail),
    by simp, ?_⟩
  · rw [hsame b (Or.inl (by omega)), Function.update_of_ne (by omega)]
  · rw [hsame _ (Or.inl (by omega)), Function.update_self, hdg]
  · exact (SameOutside.refl.update ⟨by omega, by omega⟩ _).trans (hsame.mono (by omega) (by omega))

/-! ## The routine -/

/-- nineNext(str, len, minNines, maxNines): scan the string; if a position can be raised, write the
next string and return 1, and return 0 if not.  The locals of the scan start at 0. -/
def nineNextBody : Stmt :=
  .set Pos (k 0) ;;
  .while (v Pos <' v Len) scanRound ;;
  .ite (v Found =' k 1) raiseStmt (.set Result (k 0))

/-- **nineNext** replaces the string by the next one and returns 1, or leaves the last string and
returns 0. -/
theorem nineNext_spec (hP : P[Proc.nineNext]? = some nineNextBody) (hs : Std lim) :
    NineNextSpec lim P := by
  rintro a _ lo hi l μ hseg hmem ha
  obtain ⟨rfl, -, hlo, -⟩ := (mem_nineStrs l).1 hmem
  refine fun d _ => ⟨nineNextBody, hP, ?_⟩
  light_facts hs
  unfold tNineNext
  -- pos := 0
  light_set (0 : ℕ)
  -- while pos < len
  refine Ends.next _ (Ends.whileBlock (ScanInv a lo hi l μ) l.length ?start ?round ?done
    (hT := le_rfl)) (by simp [scanRound_cost]; omega)
  case start => exact ⟨0, congrArg (State.mk · μ) (frame_append_zeros _ 5).symm⟩
  case round =>
    rintro i _ hi' ⟨dg', rfl⟩
    have hnines : (nineScan hi l i).nines ≤ i := by
      rw [(nineScan_inv hi l hi'.le).nines]
      exact List.count_le_length.trans (List.length_take_le _ _)
    exact ⟨by simp, by simp [scanFrame]; omega,
      (scanRound_runs hs ha hi' (hseg.read hi') hnines).mono fun σ' hσ' =>
        ⟨l.getD i 0, by rw [hσ', nineScan_succ hi l hi']⟩⟩
  case done =>
    rintro _ ⟨dg', rfl⟩
    refine ⟨by simp, by simp [scanFrame], ?_⟩
    simp only [scanRound_cost]
    rw [nineNext_eq_scan]
    -- if found = 1
    refine Ends.iteLast (fun hfound => ?_) (fun hfound => ?_) (by simp; omega)
    · have hfound' : (nineScan hi l l.length).found = 1 := by
        simpa [scanFrame] using hfound
      simp only [if_pos hfound', Option.getD_some, Option.isSome_some, if_true]
      exact (raiseStmt_spec hs hseg ha hlo hfound').mono (by light_time) fun _ h => h
    · have hfound' : ¬ (nineScan hi l l.length).found = 1 := by
        simpa [scanFrame] using hfound
      simp only [if_neg hfound', Option.getD_none, Option.isSome_none]
      -- return 0
      exact Ends.setLast ⟨hseg, by simp, SameOutside.refl⟩

end Light.Sec4
