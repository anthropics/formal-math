/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Compiler.ProgramCode

/-!
# The start-up code

A compiled program may start on any memory: nothing is assumed about the cells below -2.  Its first
three instructions and its start-up code write everything that the compiled statements rely on.
`startMem F N m` is the memory in which the outermost statement starts, if the run starts in m.

* `rel_startMem`: it represents the state in which the local variables 1 and 2 hold the two
  arguments (the contents of the cells -1 and -2) and all other local variables hold 0.
* `agreeOutside_startMem`: it differs from m only in the registers for 1, 0, -1, in the pool, in FP
  and in the outermost frame.
* `steps_start`: the machine gets from position 0 to the outermost statement in N + F + 9 steps.

The code has three pieces: the numbers 1, 0, -1 (`headStraight`), the pool (`poolCode`), the
outermost frame (`frameCode`).  There is no store among them, so the cells that a piece may change
are read off its text (`agreeOutside_effects`).  What a piece writes is found by running it: the two
loops unrolled in the code are inductions (`effects_poolCode`, `effects_zeroCode`).
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

variable {W : ℕ} {F N : ℕ} {m : ℤ → BitVec W}

/-! ## The numbers 1, 0, -1 -/

private theorem effects_headStraight (m : ℤ → BitVec W) :
    effects headStraight m =
      Function.update (Function.update (Function.update m cONE (wd W 1)) cZERO (wd W 0)) cNEG
        (wd W (-1)) := by
  simp only [headStraight, effects_cons, effects_nil]
  rw [effect_one, effect_sub cZERO (by cell_read) (by cell_read),
    effect_sub cNEG (by cell_read) (by cell_read)]
  rfl

/-- The three registers after the first three instructions. -/
private theorem effects_headStraight_consts (m : ℤ → BitVec W) :
    effects headStraight m cONE = wd W 1 ∧ effects headStraight m cZERO = wd W 0 ∧
      effects headStraight m cNEG = wd W (-1) := by
  rw [effects_headStraight]
  refine ⟨?_, ?_, ?_⟩ <;> cell_read

/-! ## The pool -/

private theorem poolCode_succ (N : ℕ) :
    poolCode (N + 1) = poolCode N ++ [.add (cPool (N + 1)) (cPool N) cONE] := by
  simp [poolCode, List.range_succ]

private theorem agreeOutside_poolCode (N : ℕ) (m : ℤ → BitVec W) :
    AgreeOutside (Pool N) m (effects (poolCode N) m) := by
  refine agreeOutside_effects (l := poolCode N)
    (List.forall_mem_cons.2 ⟨?_, List.forall_mem_map.2 fun n hn => ?_⟩) m
  · show cPool 0 ∈ Pool N
    cells
  · have := List.mem_range.1 hn
    show cPool (n + 1) ∈ Pool N
    cells

/-- After `poolCode N` the pool holds the numbers 0, …, N. -/
private theorem effects_poolCode (hone : m cONE = wd W 1) (N : ℕ) :
    ∀ n ≤ N, effects (poolCode N) m (cPool n) = wd W n := by
  induction N with
  | zero =>
    intro n hn
    obtain rfl : n = 0 := by omega
    simp only [poolCode, List.range_zero, List.map_nil, effects_cons, effects_nil]
    rw [effect_sub _ hone hone, Function.update_self]
    rfl
  | succ N ih =>
    intro n hn
    rw [poolCode_succ, effects_append, effects_cons, effects_nil,
      effect_add _ (ih N le_rfl) ((agreeOutside_poolCode N m).read (by cells) hone)]
    obtain rfl | hlt := hn.eq_or_lt
    · rw [Function.update_self]
      push_cast
      rfl
    · rw [Function.update_of_ne (by cells), ih n (by omega)]

/-- The memory after the first three instructions and the code for the pool. -/
private def poolMem (N : ℕ) (m : ℤ → BitVec W) : ℤ → BitVec W :=
  effects (poolCode N) (effects headStraight m)

private theorem agreeOutside_poolMem (N : ℕ) (m : ℤ → BitVec W) :
    AgreeOutside (Constants N) m (poolMem N m) := by
  refine AgreeOutside.trans_union ?_ (agreeOutside_poolCode N _)
  rw [effects_headStraight]
  exact (((AgreeOutside.refl _ m).update (by simp) _).update (by simp) _).update (by simp) _

/-- The code for the pool leaves the numbers 1, 0, -1 in their registers. -/
private theorem poolMem_consts (N : ℕ) (m : ℤ → BitVec W) :
    poolMem N m cONE = wd W 1 ∧ poolMem N m cZERO = wd W 0 ∧ poolMem N m cNEG = wd W (-1) := by
  obtain ⟨one, zero, neg⟩ := effects_headStraight_consts m
  have keep := agreeOutside_poolCode N (effects headStraight m)
  exact ⟨keep.read (by cells) one, keep.read (by cells) zero, keep.read (by cells) neg⟩

private theorem poolMem_pool (m : ℤ → BitVec W) {n : ℕ} (hn : n ≤ N) :
    poolMem N m (cPool n) = wd W n :=
  effects_poolCode (effects_headStraight_consts m).1 N n hn

/-! ## The outermost frame -/

private theorem zeroCode_succ (F : ℕ) :
    zeroCode (F + 1) = zeroCode F ++ [.sub (cStack (mainFrame + F)) cONE cONE] := by
  simp [zeroCode, List.range_succ]

/-- The instructions of `zeroCode` write into the outermost frame. -/
private theorem writesIn_zeroCode (F : ℕ) : ∀ i ∈ zeroCode F, WritesIn (MainFrame F) i :=
  List.forall_mem_map.2 fun x hx => by
    have := List.mem_range.1 hx
    show cStack (mainFrame + x) ∈ MainFrame F
    cells

/-- The local variables of the outermost frame hold zeros. -/
private theorem effects_zeroCode (hone : m cONE = wd W 1) (F : ℕ) :
    ∀ x < F, effects (zeroCode F) m (cStack (mainFrame + x)) = wd W 0 := by
  induction F with
  | zero => exact fun x hx => absurd hx x.not_lt_zero
  | succ F ih =>
    intro x hx
    have hone' := (agreeOutside_effects (writesIn_zeroCode F) m).read (by cells) hone
    rw [zeroCode_succ, effects_append, effects_cons, effects_nil, effect_sub _ hone' hone']
    obtain rfl | hlt := (Nat.lt_succ_iff.1 hx).eq_or_lt
    · rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne (by cells), ih x hlt]

private theorem agreeOutside_frameCode (h3 : 3 ≤ F) (m : ℤ → BitVec W) :
    AgreeOutside ({cFP} ∪ MainFrame F) m (effects (frameCode F) m) := by
  refine agreeOutside_effects (l := frameCode F) (List.forall_mem_cons.2 ⟨?_,
    List.forall_mem_append.2 ⟨fun i hi => ?_, List.forall_mem_cons.2 ⟨?_,
      List.forall_mem_singleton.2 ?_⟩⟩⟩) m
  · -- FP := 0 - 2 mainFrame
    exact Or.inl rfl
  · -- the zeros
    exact (writesIn_zeroCode F i hi).mono Set.subset_union_right
  · -- local variable 1 := the first argument
    show cStack (mainFrame + 1) ∈ _
    cells
  · -- local variable 2 := the second argument
    show cStack (mainFrame + 2) ∈ _
    cells

/-- The code for the outermost frame: FP, then zeros, then the two arguments. -/
private theorem effects_frameCode {i j : ℤ} (hzero : m cZERO = wd W 0)
    (hpool : m (cPool (2 * mainFrame)) = wd W (2 * mainFrame : ℕ)) (hi : m cARG1 = wd W i)
    (hj : m cARG2 = wd W j) (F : ℕ) :
    effects (frameCode F) m =
      Function.update (Function.update
        (effects (zeroCode F) (Function.update m cFP (wd W (cStack mainFrame))))
        (cStack (mainFrame + 1)) (wd W i)) (cStack (mainFrame + 2)) (wd W j) := by
  -- what the last two instructions read has not been written since the beginning
  have read (a : ℤ) (ha : a ∉ MainFrame F) (hfp : a ≠ cFP) :
      effects (zeroCode F) (Function.update m cFP (wd W (cStack mainFrame))) a = m a :=
    ((agreeOutside_effects (writesIn_zeroCode F) _).cell ha).trans (Function.update_of_ne hfp _ _)
  have zero := (read cZERO (by cells) (by cells)).trans hzero
  have arg1 := (read cARG1 (by cells) (by cells)).trans hi
  have arg2 := (read cARG2 (by cells) (by cells)).trans hj
  simp only [frameCode, effects_cons, effects_append, effects_nil]
  -- FP := 0 - 2 mainFrame
  rw [effect_sub cFP hzero hpool, show (0 : ℤ) - (2 * mainFrame : ℕ) = cStack mainFrame from rfl]
  -- after the zeros: local variable 1 := the first argument + 0
  rw [effect_add _ arg1 zero, add_zero]
  -- local variable 2 := the second argument + 0
  rw [effect_add _ (by cell_read using arg2) (by cell_read using zero), add_zero]

/-! ## The memory in which the outermost statement starts -/

/-- The memory after the first three instructions and the start-up code. -/
def startMem (F N : ℕ) (m : ℤ → BitVec W) : ℤ → BitVec W :=
  effects (startStraight F N) (effects headStraight m)

private theorem startMem_eq (F N : ℕ) (m : ℤ → BitVec W) :
    startMem F N m = effects (frameCode F) (poolMem N m) := effects_append _ _ _

/-- The start-up code changes only the registers for 1, 0, -1, the pool, FP and the outermost
frame. -/
theorem agreeOutside_startMem (h3 : 3 ≤ F) (N : ℕ) (m : ℤ → BitVec W) :
    AgreeOutside (Constants N ∪ ({cFP} ∪ MainFrame F)) m (startMem F N m) :=
  startMem_eq F N m ▸ (agreeOutside_poolMem N m).trans_union (agreeOutside_frameCode h3 _)

/-- After the start-up code the memory represents the state in which the outermost statement
starts: the local variables 1 and 2 hold the two arguments, all others 0.  Nothing is assumed about
the cells below -2 of the initial memory. -/
theorem rel_startMem (Z : Sizes W) (h3 : 3 ≤ Z.F) (hpool : 2 * mainFrame ≤ Z.disp) {μ : ℕ → ℤ}
    {i j : ℤ} (hm : ∀ a < Z.lim.space, m (a : ℤ) = wd W (μ a)) (hi : m cARG1 = wd W i)
    (hj : m cARG2 = wd W j) :
    Rel Z ⟨frame [0, i, j], μ⟩ mainFrame (startMem Z.F Z.disp m) := by
  obtain ⟨one, zero, neg⟩ := poolMem_consts Z.disp m
  have keep₁ := agreeOutside_poolMem Z.disp m
  have keep₂ := agreeOutside_frameCode h3 (poolMem Z.disp m)
  have written := effects_frameCode zero (poolMem_pool m hpool) (keep₁.read (by cells) hi)
    (keep₁.read (by cells) hj) Z.F
  have zeros (x : ℕ) (hx : x < Z.F) (h1 : x ≠ 1) (h2 : x ≠ 2) :
      effects (frameCode Z.F) (poolMem Z.disp m) (cStack (mainFrame + x)) = wd W 0 := by
    rw [written, Function.update_of_ne (by cells), Function.update_of_ne (by cells)]
    exact effects_zeroCode (by cell_read using one) Z.F x hx
  rw [startMem_eq]
  exact {
    one := keep₂.read (by cells) one
    zero := keep₂.read (by cells) zero
    neg := keep₂.read (by cells) neg
    pool := fun n hn => keep₂.read (by cells) (poolMem_pool m hn)
    fp := by
      rw [written, Function.update_of_ne (by cells), Function.update_of_ne (by cells),
        (agreeOutside_effects (writesIn_zeroCode Z.F) _).cell (by cells), Function.update_self]
    loc := fun x hx => match x with
      | 0 => zeros 0 hx (by omega) (by omega)
      | 1 => by rw [written, Function.update_of_ne (by cells)]; exact Function.update_self ..
      | 2 => by rw [written]; exact Function.update_self ..
      | x + 3 => zeros (x + 3) hx (by omega) (by omega)
    mem := fun a ha => keep₂.read (by cells) (keep₁.read (by cells) (hm a ha)) }

/-! ## The run from the first instruction to the outermost statement -/

private theorem straight_headStraight : ∀ i ∈ headStraight, Straight i := by
  simp [headStraight, Straight]

private theorem straight_startStraight (F N : ℕ) : ∀ i ∈ startStraight F N, Straight i := by
  simp [startStraight, poolCode, frameCode, zeroCode, Straight, or_imp, forall_and]

private theorem length_startStraight (F N : ℕ) : (startStraight F N).length = N + F + 4 := by
  simp +arith [startStraight, poolCode, frameCode, zeroCode]

/-- From the first instruction to the outermost statement. -/
theorem steps_start (P : Program) (p0 : ℕ) (dec : Bool) (hneg : InRange W (-1))
    (m : ℤ → BitVec W) :
    Steps (compileProgram P p0 dec) (dispPos P dec + frameSize P + 9) ⟨0, m⟩
      ⟨mainPos, startMem (frameSize P) (dispPos P dec) m⟩ := by
  have head := codeAt_headCode P p0 dec
  have start := codeAt_startCode P p0 dec
  obtain ⟨-, -, neg₀⟩ := effects_headStraight_consts m
  obtain ⟨-, -, neg⟩ := poolMem_consts (dispPos P dec) m
  have neg₁ : startMem (frameSize P) (dispPos P dec) m cNEG = wd W (-1) := by
    rw [startMem_eq, (agreeOutside_frameCode (three_le_frameSize P) _).cell (by cells), neg]
  -- 1, 0, -1; jump to the start-up code; the start-up code; jump back
  refine ((((steps_straight _ 0 m head.left straight_headStraight).trans
    (steps_jump head.right neg₀ hneg)).trans
    (steps_straight _ _ _ start.left (straight_startStraight _ _))).trans
    (steps_jump start.right neg₁ hneg)).cast_count ?_
  rw [length_startStraight, show headStraight.length = 3 from rfl]
  omega

end Light.Compiler
