/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Compiler.Simulation
public import ThreeSumApsp.Lang.Compiler.StartUp

/-!
# The compiler is correct on whole programs

`compileProgram_correct`: if the call of procedure p0 of the light program P ends after c
steps, the compiled program gives its verdict within `ramSteps P dec c` = c₀ + K c steps, where c₀
and K depend on the text of P (and on dec) only.  If the memory of the machine held the memory of
the light program and the two arguments before (`Input`), it holds the final memory afterwards, with
the result in the cell -3 (`Outcome`).

The run of the machine has three parts.

1. The start-up code (`steps_start`) leads to a memory that represents the first state
   (`rel_startMem`).
2. The outermost statement is the call of p0.  The compiled program satisfies what the simulation
   theorem assumes (`setting`, `start_mainStmt`), so `sim` gives a run of at most K c steps to a
   memory that represents the last state.
3. The code that follows copies the result to the cell -3 and gives the verdict (`steps_tail`).

Each part comes with the set of cells that it may change.  The cells below `-lowCell` and the cells
from `lim.space` on are in none of the three sets (`not_mem_of_far`), and neither are the cells -1
and -2.

The notions of the compiler and of its proof are in the namespace `Light.Compiler`.  The statements
about programs name four of them, which are in `Light`: `compileProgram`, `mainStmt`, `verdictOf`,
`ramSteps`.  The passage to the notions of the word RAM also uses `compileProgram_correct` with
`Fits`, `Holds`, `Input` and `Outcome`, the cells `cARG1`, `cARG2`, `cRESULT`, and the numbers
`startCost`, `stepsPerStep`, `dispPos`, `frameSize`, `stackCells`, `lowCell`.
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

open EndStatement (Instr exec)

variable {W : ℕ}

/-! ## The verdict -/

/-- The verdict: accept, or, if dec is set, accept exactly if the result is positive. -/
def _root_.Light.verdictOf (dec : Bool) (r : ℤ) : Bool := !dec || decide (0 < r)

/-- What the code that follows the outermost statement leaves, if it starts in the memory m and the
result is r: the machine is about to give the verdict, the cell `cRESULT` holds the result, and only
that cell and the register D have changed. -/
private structure Verdict (code : List Instr) (dec : Bool) (r : ℤ) (m : ℤ → BitVec W)
    (cfg : Cfg W) : Prop where
  verdict : step code cfg = .inr (verdictOf dec r)
  result : cfg.mem cRESULT = wd W r
  agree : AgreeOutside {cRESULT, cD} m cfg.mem

/-- The code that follows the outermost statement gets there in at most three steps. -/
private theorem steps_tail {code : List Instr} {pos : ℕ} {dec : Bool}
    (hcode : CodeAt code pos (tailCode dec pos)) {m : ℤ → BitVec W} {r : ℤ}
    (hres : m (cStack mainFrame) = wd W r) (hzero : m cZERO = wd W 0) (hr : InRange W (-r)) :
    ∃ (n : ℕ) (cfg : Cfg W), n ≤ 3 ∧ Steps code n ⟨pos, m⟩ cfg ∧ Verdict code dec r m cfg := by
  -- the cell for the result := the result
  have copy : Steps code 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m cRESULT (wd W r)⟩ :=
    add_zero r ▸ steps_add hcode hres hzero
  cases dec with
  | false =>
    -- accept
    have read : Function.update m cRESULT (wd W r) cRESULT = wd W r := Function.update_self ..
    exact ⟨1, _, by omega, copy, step_accept hcode.tail.head, read,
      (AgreeOutside.refl _ m).update (by simp) _⟩
  | true =>
    have rest : CodeAt code (pos + 1)
      [.sub cD cZERO (cStack mainFrame), .bltz cD (pos + 4), .reject, .accept] := hcode.tail
    -- D := 0 - the result; go to accept if D < 0; reject
    have run := (copy.trans (steps_sub rest (by cell_read using hzero)
      (by cell_read using hres))).trans
      (steps_bltz rest.tail (Function.update_self ..) (by rwa [zero_sub]))
    have keep : AgreeOutside {cRESULT, cD} m
        (Function.update (Function.update m cRESULT (wd W r)) cD (wd W (0 - r))) :=
      ((AgreeOutside.refl _ m).update (by simp) _).update (by simp) _
    have read : Function.update (Function.update m cRESULT (wd W r)) cD (wd W (0 - r)) cRESULT =
        wd W r := by
      cell_read
    by_cases hpos : 0 < r
    · rw [if_pos (by omega)] at run
      exact ⟨3, _, le_rfl, run,
        (step_accept rest.tail.tail.tail.head).trans (by simp [verdictOf, hpos]), read, keep⟩
    · rw [if_neg (by omega)] at run
      exact ⟨3, _, le_rfl, run,
        (step_reject rest.tail.tail.head).trans (by simp [verdictOf, hpos]), read, keep⟩

/-! ## Time and space of the compiled program -/

/-- A bound for the number of steps of the compiled program outside the outermost statement:
`dispPos` + `frameSize` + 9 before it (`steps_start`), at most three after it (`steps_tail`), and
the verdict. -/
def startCost (P : Program) (dec : Bool) : ℕ := dispPos P dec + frameSize P + 13

/-- A bound for the number of steps of the compiled program, for c steps of the light program. -/
def _root_.Light.ramSteps (P : Program) (dec : Bool) (c : ℕ) : ℕ :=
  startCost P dec + stepsPerStep (dispPos P dec) * c

/-- The number of cells of the stack that a run within the limits needs. -/
def stackCells (P : Program) (lim : Limits) : ℕ :=
  mainFrame + (frameSize P + 1) * (lim.depth + 1)

/-- A bound for the extent of the negative cells that the compiled program uses: the stack ends
before the cell -2 · stackCells, and the pool, which reaches further down than the temporaries, ends
at the cell -(25 + 4 · dispPos). -/
def lowCell (P : Program) (dec : Bool) (lim : Limits) : ℕ :=
  max (2 * stackCells P lim) (25 + 4 * dispPos P dec)

private theorem frame_le_stackCells (P : Program) (lim : Limits) :
    mainFrame + frameSize P + 1 ≤ stackCells P lim := by
  have := Nat.le_mul_of_pos_right (frameSize P + 1) (show 0 < lim.depth + 1 by omega)
  unfold stackCells
  omega

/-! ## The setting of the simulation theorem -/

section setting

variable {lim : Limits} {P : Program} {p0 : ℕ} {dec : Bool}

/-- The compiled program, with its numbers, satisfies what the simulation theorem assumes once and
for all. -/
private def setting (P : Program) (p0 : ℕ) (dec : Bool)
    (hfit : Fits W lim (dispPos P dec) (stackCells P lim)) : Setting W where
  toCodeLayout := codeLayout P dec
  lim := lim
  Q := stackCells P lim
  fits := hfit
  offsets_le := by
    have := two_mul_frameSize_add_le_dispPos P dec
    simp only [codeLayout]
    omega
  P := P
  code := compileProgram P p0 dec
  bodyAt := codeAt_bodies (codeLayout P dec) P _ (codeAt_bodiesCode P p0 dec)
  dispatcherAt := codeAt_dispatcher_dispPos P p0 dec
  width _ hb := width_le_frameSize hb

variable (hfit : Fits W lim (dispPos P dec) (stackCells P lim))

/-- The outermost statement is at `mainPos` and runs in the frame `mainFrame`. -/
private theorem start_mainStmt {σ : State} {m : ℤ → BitVec W} (hσ : σ.Bounded lim)
    (R : Rel (setting P p0 dec hfit).toSizes σ mainFrame m) :
    Start (setting P p0 dec hfit) 0 (mainStmt p0) σ mainPos mainFrame m where
  rel := R
  low := by decide
  high := (Nat.le_succ _).trans (frame_le_stackCells P lim)
  codeAt := codeAt_mainStmt P p0 dec
  below := by
    have := two_mul_frameSize_add_le_dispPos P dec
    simp only [size_mainStmt, setting, codeLayout, mainPos]
    omega
  width := (width_mainStmt p0).trans_le (three_le_frameSize P)
  bounded := hσ
  room := by
    simp only [setting, codeLayout, stackCells, Nat.sub_zero, Nat.mul_succ]
    omega

/-- The cells below `-lowCell` and the cells from `lim.space` on are not among those that the
start-up code, the outermost statement or the code for the verdict may change. -/
private theorem not_mem_of_far {a : ℤ}
    (ha : a < -(lowCell P dec lim : ℤ) ∨ (lim.space : ℤ) ≤ a) :
    a ∉ Constants (dispPos P dec) ∪ ({cFP} ∪ MainFrame (frameSize P)) ∪
      Writable (setting P p0 dec hfit).toSizes mainFrame ∪ {cRESULT, cD} := by
  have hframe := frame_le_stackCells P lim
  have htemps := two_mul_frameSize_add_le_dispPos P dec
  have hstack : 2 * stackCells P lim ≤ lowCell P dec lim := le_max_left _ _
  have hpool : 25 + 4 * dispPos P dec ≤ lowCell P dec lim := le_max_right _ _
  simp only [Writable, setting, codeLayout]
  rcases ha with ha | ha <;> cells

end setting

/-! ## The theorem -/

/-- The cells 0, 1, 2, … of the memory m of the machine hold the memory μ of the light language,
and μ holds words. -/
structure Holds (W : ℕ) (lim : Limits) (μ : ℕ → ℤ) (m : ℤ → BitVec W) : Prop where
  rep : ∀ a : ℕ, m (a : ℤ) = wd W (μ a)
  bounded : ∀ a, |μ a| ≤ lim.word

/-- What a run of a compiled program needs in the memory m: the memory μ of the light language, and
the arguments i and j, which are words, in their two cells. -/
structure Input (lim : Limits) (μ : ℕ → ℤ) (i j : ℤ) (m : ℤ → BitVec W) : Prop
    extends Holds W lim μ m where
  arg1 : m cARG1 = wd W i
  arg2 : m cARG2 = wd W j
  arg1_le : |i| ≤ lim.word
  arg2_le : |j| ≤ lim.word

/-- What a run of a compiled program from the memory m leaves in the memory m', if the light run
ends in σ'. -/
structure Outcome (lim : Limits) (P : Program) (dec : Bool) (m : ℤ → BitVec W) (σ' : State)
    (m' : ℤ → BitVec W) : Prop where
  /-- The cells 0, 1, 2, … hold the final memory. -/
  holds : Holds W lim σ'.mem m'
  /-- The cell for the result holds the result. -/
  result : (m' cRESULT).toInt = σ'.loc 0
  /-- The first argument is still there. -/
  arg1 : m' cARG1 = m cARG1
  /-- The second argument is still there. -/
  arg2 : m' cARG2 = m cARG2
  /-- The cells far below 0 and the cells from lim.space on are unchanged. -/
  far : ∀ a : ℤ, a < -(lowCell P dec lim : ℤ) ∨ (lim.space : ℤ) ≤ a → m' a = m a

/-- **The compiler is correct.**  Let the call of procedure p0 of the program P on the arguments i,
j and the memory μ end after c steps within the limits, and let the word size fit the limits.  Then
the compiled program, started on any memory whose cells `a ≥ 0` hold the words of μ and whose
cells -1 and -2 hold i and j, gives its verdict within `startCost + stepsPerStep · c` steps.  Then
the cell -3 holds the result of the procedure and the cells `a ≥ 0` hold the final memory.  The
cells -1 and -2, the cells below `-lowCell` and the cells from `lim.space` on are unchanged.  The
two constants of the time depend on the text of P and on dec only. -/
theorem compileProgram_correct {lim : Limits} {P : Program} {p0 : ℕ} {dec : Bool} {μ : ℕ → ℤ}
    {i j : ℤ} {σ' : State} {c : ℕ} {m : ℤ → BitVec W}
    (h : Exec lim P 0 (mainStmt p0) ⟨frame [0, i, j], μ⟩ σ' c)
    (hfit : Fits W lim (dispPos P dec) (stackCells P lim)) (hm : Input lim μ i j m) :
    ∃ m' : ℤ → BitVec W, exec (compileProgram P p0 dec) (ramSteps P dec c) 0 m
        = some (verdictOf dec (σ'.loc 0), m') ∧ Outcome lim P dec m σ' m' := by
  have hF := three_le_frameSize P
  have hdisp := two_mul_frameSize_add_le_dispPos P dec
  have hσ : State.Bounded lim ⟨frame [0, i, j], μ⟩ :=
    bounded_frame (by simp [hm.arg1_le, hm.arg2_le, (abs_nonneg i).trans hm.arg1_le]) hm.bounded
  have hσ' := h.bounded hσ
  -- the start-up code
  have run₁ := steps_start P p0 dec (setting P p0 dec hfit).inRange_neg_one m
  have keep₁ := agreeOutside_startMem hF (dispPos P dec) m
  -- the outermost statement
  obtain ⟨m', n, fin⟩ := sim (setting P p0 dec hfit) h mainPos mainFrame _ (start_mainStmt hfit hσ
    (rel_startMem _ hF (by simp only [setting, codeLayout, mainFrame]; omega)
      (fun a _ => hm.rep a) hm.arg1 hm.arg2))
  have hn : n ≤ stepsPerStep (dispPos P dec) * c := fin.le
  have run₂ := fin.run.cast_pos (p' := tailPos (frameSize P))
    (by simp only [tailPos, size_mainStmt, setting, codeLayout])
  -- the verdict
  obtain ⟨k, cfg, hk, run₃, tail⟩ := steps_tail (codeAt_tailCode P p0 dec)
    (fin.rel.loc 0 (show 0 < frameSize P by omega)) fin.rel.zero
    (hfit.inRange (by rw [abs_neg]; exact hσ'.1 0))
  have run := (run₁.trans run₂).trans run₃
  have keep := (keep₁.trans_union fin.agree).trans_union tail.agree
  have far (a : ℤ) ha : cfg.mem a = m a := keep.cell (not_mem_of_far hfit ha)
  refine ⟨cfg.mem, exec_mono (c := ⟨0, m⟩) (exec_of_steps run tail.verdict) ?_,
    { holds := ⟨fun a => ?_, hσ'.2⟩
      result := tail.result ▸ toInt_wd (hfit.inRange (hσ'.1 0))
      arg1 := keep.cell (by cells)
      arg2 := keep.cell (by cells)
      far := far }⟩
  · simp only [ramSteps, startCost]
    omega
  · by_cases ha : a < lim.space
    · exact tail.agree.read (by cells) (fin.rel.mem a ha)
    · rw [far _ (Or.inr (by exact_mod_cast not_lt.1 ha)), h.mem_outside a (not_lt.1 ha)]
      exact hm.rep a

end Light.Compiler
