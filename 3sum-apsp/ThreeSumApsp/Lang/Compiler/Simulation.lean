/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Compiler.CallFrames
public import ThreeSumApsp.Lang.Compiler.Dispatcher

/-!
# The compiler is correct on statements: the simulation theorem

A run of a statement of the light language in c steps is matched by a run of its code in at most
stepsPerStep · c steps of the machine (`sim`).

What never changes (the program, its code, the numbers of `Sizes`, and the facts that the code is in
place and that a frame is wide enough for the text) forms the structure `Setting`.  The situation
before the code of a statement runs is `Start`: the code is at pos, and the memory represents the
state in the frame q, with room on the stack for the calls still allowed.  The situation afterwards
is `Finished`: the machine has reached the position after the code, the memory represents the new
state in the same frame, and only cells that the statement may write have changed.  `Simulates` says
that `Start` leads to `Finished`.

The theorem is an induction on the run, with one lemma for each rule of the semantics: `sim_skip`,
`sim_set`, `sim_store`, `sim_seq`, `sim_iteTrue`, `sim_iteFalse`, `sim_whileFalse`,
`sim_whileTrue`, `sim_call`.  Each of them first takes the code of the statement apart (`codeAt_ite`
and its like say where the parts are) and then runs the parts in turn.  A call has four parts.
Enter (`steps_callEnter`): arguments, new frame, position to return to, jump.  The body: the
induction hypothesis.  Leave (`steps_callLeave`): return sequence and dispatcher.  Store the result
in the caller's variable (`steps_setVar`).

In the proofs S is the setting and B the situation at the start; the other letters are as in the
file on the cells.
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

open EndStatement (Instr)

/-! ## Where the parts of the code of a statement are -/

section layout

variable {code : List Instr} {G : CodeLayout} {pos x p : ℕ} {e : Expr} {c : Cond} {s t : Stmt}
  {args : List Expr}

/-- The code of e, and the two instructions that store T₀ in x. -/
private theorem codeAt_set (h : CodeAt code pos (compileStmt G (.set x e) pos)) :
    CodeAt code pos (compileExpr e 0) ∧
      CodeAt code (pos + e.size) [.sub cADDR cFP (cPool (2 * x)), .store cADDR (cT 0)] :=
  ⟨h.left, h.right.cast_pos (by rw [length_compileExpr])⟩

/-- The code of s, and the code of t. -/
private theorem codeAt_seq (h : CodeAt code pos (compileStmt G (.seq s t) pos)) :
    CodeAt code pos (compileStmt G s pos) ∧
      CodeAt code (pos + s.size G.F) (compileStmt G t (pos + s.size G.F)) :=
  ⟨h.left, h.right.cast_pos (by rw [length_compileStmt])⟩

/-- The test, the first branch, the jump over the second branch, the second branch. -/
private theorem codeAt_ite (h : CodeAt code pos (compileStmt G (.ite c s t) pos)) :
    CodeAt code pos (compileCond c (pos + c.size + s.size G.F + 1)) ∧
      CodeAt code (pos + c.size) (compileStmt G s (pos + c.size)) ∧
      CodeAt code (pos + c.size + s.size G.F)
        [.bltz cNEG (pos + c.size + s.size G.F + 1 + t.size G.F)] ∧
      CodeAt code (pos + c.size + s.size G.F + 1)
        (compileStmt G t (pos + c.size + s.size G.F + 1)) := by
  rw [compileStmt] at h
  refine ⟨h.left.left.left, h.left.left.right.cast_pos ?_, h.left.right.cast_pos ?_,
    h.right.cast_pos ?_⟩ <;> simp +arith [length_compileCond, length_compileStmt]

/-- The test, the body, the jump back. -/
private theorem codeAt_while (h : CodeAt code pos (compileStmt G (.while c s) pos)) :
    CodeAt code pos (compileCond c (pos + c.size + s.size G.F + 1)) ∧
      CodeAt code (pos + c.size) (compileStmt G s (pos + c.size)) ∧
      CodeAt code (pos + c.size + s.size G.F) [.bltz cNEG pos] := by
  rw [compileStmt] at h
  refine ⟨h.left.left, h.left.right.cast_pos ?_, h.right.cast_pos ?_⟩ <;>
    simp +arith [length_compileCond, length_compileStmt]

/-- The arguments and the new frame, the jump to the procedure, and the two instructions that store
the result. -/
private theorem codeAt_call (h : CodeAt code pos (compileStmt G (.call p args x) pos)) :
    CodeAt code pos (argsCode args 0 ++ newFrame G.F args.length (pos + callSize G.F args)) ∧
      CodeAt code (pos + (argsSize args + (2 * G.F + 4))) [.bltz cNEG (G.entry.getD p 0)] ∧
      CodeAt code (pos + callSize G.F args)
        [.sub cADDR cFP (cPool (2 * x)), .store cADDR cRET] := by
  rw [compileStmt, callCode] at h
  refine ⟨h.left.left, h.left.right.cast_pos ?_, h.right.cast_pos ?_⟩ <;>
    simp +arith [length_argsCode, length_newFrame, callSize]

end layout

/-! ## The setting -/

/-- What the simulation assumes once and for all: the numbers are large enough (`Sizes`), and the
program and its code fit them. -/
structure Setting (W : ℕ) extends Sizes W where
  /-- The light program. -/
  P : Program
  /-- The code of the whole program. -/
  code : List Instr
  /-- Every procedure body is at its entry, followed by the return sequence, all before the
  dispatcher. -/
  bodyAt : ∀ (p : ℕ) (b : Stmt), P[p]? = some b → ∃ e, entry[p]? = some e ∧
    CodeAt code e (compileStmt toCodeLayout b e ++ epilogue toCodeLayout) ∧
    e + b.size F + epilogueSize ≤ disp
  /-- The dispatcher serves the positions before it. -/
  dispatcherAt : CodeAt code disp (dispatcher disp)
  /-- Every body has width at most F. -/
  width : ∀ b ∈ P, b.width ≤ F

/-- An upper bound for the number of machine steps that match one step of the light language, if the
code before the dispatcher has n instructions.  Each rule of the semantics counts at least one step
and, calls apart, runs a piece of code once, which takes at most n machine steps.  A call counts two
steps, so it has 2 stepsPerStep = 4 n: at most n for its own code, n for the return sequence, 2 n
for the dispatcher. -/
def stepsPerStep (n : ℕ) : ℕ := 2 * n

/-- At most n machine steps are within the bound for c ≥ 1 steps of the language. -/
private theorem le_stepsPerStep_mul {a c n : ℕ} (h : a ≤ n) (hc : 1 ≤ c) :
    a ≤ stepsPerStep n * c :=
  calc a ≤ stepsPerStep n * 1 := by rw [stepsPerStep]; omega
    _ ≤ stepsPerStep n * c := Nat.mul_le_mul_left _ hc

/-- At most n machine steps, followed by b machine steps that are within the bound for k steps, are
within the bound for c + k steps if c ≥ 1. -/
private theorem add_le_stepsPerStep_mul {a b c k n : ℕ} (h : a ≤ n) (hc : 1 ≤ c)
    (hb : b ≤ stepsPerStep n * k) : a + b ≤ stepsPerStep n * (c + k) :=
  Nat.mul_add _ c k ▸ Nat.add_le_add (le_stepsPerStep_mul h hc) hb

/-- The count for a call whose code is at pos and has size + 2 instructions: size steps to enter, b
for the body, r + 2 (pos + size + 1) to leave, where r is the length of the return sequence, and 2
to store the result.  The cost a of the arguments is not needed. -/
private theorem call_le_stepsPerStep_mul {pos size b r a k n : ℕ} (hpos : pos + (size + 2) ≤ n)
    (hr : r ≤ n) (hb : b ≤ stepsPerStep n * k) :
    size + b + (r + 2 * (pos + size + 1)) + 2 ≤ stepsPerStep n * (a + 2 + k) := by
  rw [Nat.mul_add (stepsPerStep n), Nat.mul_add (stepsPerStep n)]
  have hK : stepsPerStep n * 2 = 4 * n := by rw [stepsPerStep]; omega
  omega

variable {W : ℕ} (S : Setting W)

/-- The situation before the code of the statement s runs, at nesting depth d of calls: the memory m
represents the state σ in the frame q, and the following holds. -/
structure Start (d : ℕ) (s : Stmt) (σ : State) (pos q : ℕ) (m : ℤ → BitVec W) : Prop
    extends Framed S.toSizes σ q m where
  /-- The code of s is at pos. -/
  codeAt : CodeAt S.code pos (compileStmt S.toCodeLayout s pos)
  /-- It ends at or before the dispatcher. -/
  below : pos + s.size S.F ≤ S.disp
  /-- F local variables and 2 F + 1 temporaries are enough for s. -/
  width : s.width ≤ S.F
  /-- The state holds words. -/
  bounded : σ.Bounded S.lim
  /-- The stack has room for this frame and for F + 1 cells for each further level of calls. -/
  room : q + S.F + (S.F + 1) * (S.lim.depth - d) ≤ S.Q

/-- The code of s, started as in `Start`, has matched a run of c steps that ends in σ': it has
taken n machine steps and left the memory m'. -/
structure Finished (s : Stmt) (σ' : State) (c pos q : ℕ) (m m' : ℤ → BitVec W) (n : ℕ) : Prop where
  /-- The machine has reached the position after the code. -/
  run : Steps S.code n ⟨pos, m⟩ ⟨pos + s.size S.F, m'⟩
  /-- It took at most stepsPerStep machine steps for each step of the language. -/
  le : n ≤ stepsPerStep S.disp * c
  /-- The memory represents σ' in the same frame. -/
  rel : Rel S.toSizes σ' q m'
  /-- Only cells that a statement in the frame q may write have changed. -/
  agree : AgreeOutside (Writable S.toSizes q) m m'

/-- The code of s matches the run of s from σ to σ' in c steps. -/
def Simulates (d : ℕ) (s : Stmt) (σ σ' : State) (c : ℕ) : Prop :=
  ∀ (pos q : ℕ) (m : ℤ → BitVec W), Start S d s σ pos q m →
    ∃ (m' : ℤ → BitVec W) (n : ℕ), Finished S s σ' c pos q m m' n

variable {S} {d pos q : ℕ} {s s₁ s₂ : Stmt} {σ σ' σ₁ σ₂ : State} {m : ℤ → BitVec W}

/-- The situation before a part t of the statement runs, in the same frame. -/
private theorem Start.sub (B : Start S d s σ pos q m) {t : Stmt} {pos' : ℕ} {m' : ℤ → BitVec W}
    (hcode : CodeAt S.code pos' (compileStmt S.toCodeLayout t pos'))
    (hpos : pos' + t.size S.F ≤ S.disp) (hw : t.width ≤ S.F) (hσ : σ'.Bounded S.lim)
    (R : Rel S.toSizes σ' q m') : Start S d t σ' pos' q m' :=
  { rel := R, low := B.low, high := B.high, codeAt := hcode, below := hpos, width := hw,
    bounded := hσ, room := B.room }

/-- The room on the stack, seen from the frame of a procedure that is called. -/
private theorem Start.room_succ (B : Start S d s σ pos q m) (hd : d < S.lim.depth) :
    q + S.F + 1 + S.F + (S.F + 1) * (S.lim.depth - (d + 1)) ≤ S.Q := by
  have := B.room
  rw [show S.lim.depth - d = S.lim.depth - (d + 1) + 1 by omega, Nat.mul_succ] at this
  omega

/-- The test of an if or a while that is at pos. -/
private theorem Start.test (B : Start S d s σ pos q m) {c : Cond} {l : ℕ}
    (hcode : CodeAt S.code pos (compileCond c l)) (hw : c.width ≤ S.F) (hs : c.Safe S.lim σ) :
    Decides S.code S.F pos c.size l m (c.Holds σ) :=
  decides_compileCond B.toFramed B.bounded c hcode hw hs

/-! ## Statements without calls -/

/-- skip: no code, no step. -/
private theorem sim_skip : Simulates S d .skip σ σ 0 := fun _ _ m B =>
  ⟨m, 0, { run := Steps.refl _, le := Nat.zero_le _, rel := B.rel, agree := AgreeOutside.refl _ m }⟩

/-- x := e: the code of e leaves the value in T₀, and two instructions store it in x. -/
private theorem sim_set {x : ℕ} {e : Expr} (hs : e.Safe S.lim σ) :
    Simulates S d (.set x e) σ { σ with loc := Function.update σ.loc x (e.val σ) }
      (e.cost + 1) := by
  intro pos q m B
  obtain ⟨hx, he⟩ := Stmt.width_set_le_iff.1 B.width
  obtain ⟨exprCode, setCode⟩ := codeAt_set B.codeAt
  have hpos : pos + (e.size + 2) ≤ S.disp := B.below
  -- T₀ := e
  obtain ⟨val, A⟩ := effects_compileExpr_of_width B.toFramed e 0 he hs (by omega)
  have A₁ := A.mono temps_subset_scratch
  have run₁ := steps_straight _ pos m exprCode (straight_compileExpr e 0)
  rw [length_compileExpr] at run₁
  -- x := T₀
  obtain ⟨m₂, run₂, R₂, A₂⟩ := steps_setVar (B.toFramed.same A₁) hx setCode val (by cells)
  exact ⟨m₂, _, {
    run := (run₁.trans run₂).cast_pos (by rw [Stmt.size, Nat.add_assoc])
    le := le_stepsPerStep_mul (by omega) (by omega)
    rel := R₂
    agree := (A₁.mono scratch_subset_writable).trans A₂ }⟩

/-- The cell at a := e: the code of a and e leaves the values in T₀ and T₁, and one instruction
stores. -/
private theorem sim_store {a e : Expr} (hsa : a.Safe S.lim σ) (hse : e.Safe S.lim σ)
    (haddr : S.lim.Addr (a.val σ)) :
    Simulates S d (.store a e) σ
      { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) } (a.cost + e.cost + 1) := by
  intro pos q m B
  obtain ⟨ha, he⟩ := Stmt.width_store_le_iff.1 B.width
  have hpos : pos + (a.size + e.size + 1) ≤ S.disp := B.below
  -- T₀ := a; T₁ := e
  obtain ⟨m₁, run₁, va, ve, A₁⟩ := steps_pair B.toFramed B.codeAt ha he hsa hse
  -- the cell at T₀ := T₁
  have run₂ := run₁.trans (steps_store (codeAt_after_pair B.codeAt) va (S.inRange_addr haddr))
  rw [ve] at run₂
  exact ⟨_, _, {
    run := run₂.cast_pos (by rw [Stmt.size, Nat.add_assoc])
    le := le_stepsPerStep_mul (by omega) (by omega)
    rel := (B.rel.same A₁).setMem B.low haddr _
    agree := (A₁.mono scratch_subset_writable).update (mem_writable_of_addr haddr) _ }⟩

/-- s₁; s₂: the code of s₁, then the code of s₂. -/
private theorem sim_seq {c₁ c₂ : ℕ} (h₁ : Exec S.lim S.P d s₁ σ σ₁ c₁)
    (ih₁ : Simulates S d s₁ σ σ₁ c₁) (ih₂ : Simulates S d s₂ σ₁ σ₂ c₂) :
    Simulates S d (.seq s₁ s₂) σ σ₂ (c₁ + c₂) := by
  intro pos q m B
  obtain ⟨hw₁, hw₂⟩ := Stmt.width_seq_le_iff.1 B.width
  obtain ⟨firstCode, secondCode⟩ := codeAt_seq B.codeAt
  have hpos : pos + (s₁.size S.F + s₂.size S.F) ≤ S.disp := B.below
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih₁ _ _ _ (B.sub firstCode (by omega) hw₁ B.bounded B.rel)
  obtain ⟨m₂, n₂, run₂, le₂, R₂, A₂⟩ := ih₂ _ _ _
    (B.sub secondCode (by omega) hw₂ (h₁.bounded B.bounded) R₁)
  exact ⟨m₂, n₁ + n₂, {
    run := (run₁.trans run₂).cast_pos (by rw [Stmt.size, Nat.add_assoc])
    le := Nat.mul_add _ c₁ c₂ ▸ Nat.add_le_add le₁ le₂
    rel := R₂
    agree := A₁.trans A₂ }⟩

/-- if c then s₁ else s₂, when c holds: the test goes on to the code of s₁, and a jump leads over
the code of s₂. -/
private theorem sim_iteTrue {c : Cond} {k : ℕ} (hs : c.Safe S.lim σ) (holds : c.Holds σ)
    (ih : Simulates S d s₁ σ σ' k) : Simulates S d (.ite c s₁ s₂) σ σ' (c.cost + 1 + k) := by
  intro pos q m B
  obtain ⟨hwc, hw₁, -⟩ := Stmt.width_ite_le_iff.1 B.width
  obtain ⟨testCode, thenCode, jumpCode, -⟩ := codeAt_ite B.codeAt
  have hpos : pos + (c.size + s₁.size S.F + 1 + s₂.size S.F) ≤ S.disp := B.below
  -- the test
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.test testCode hwc hs).of_holds holds
  -- the first branch
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih _ _ _
    (B.sub thenCode (by omega) hw₁ B.bounded (B.rel.same A₀))
  -- the jump over the second branch
  have run₂ := (run₀.trans run₁).trans (steps_jump jumpCode R₁.neg S.inRange_neg_one)
  exact ⟨m₁, n₀ + 1 + n₁, {
    run := (run₂.cast_count (by omega)).cast_pos (by rw [Stmt.size]; omega)
    le := add_le_stepsPerStep_mul (by omega) (by omega) le₁
    rel := R₁
    agree := (A₀.mono scratch_subset_writable).trans A₁ }⟩

/-- if c then s₁ else s₂, when c fails: the test jumps to the code of s₂. -/
private theorem sim_iteFalse {c : Cond} {k : ℕ} (hs : c.Safe S.lim σ) (fails : ¬ c.Holds σ)
    (ih : Simulates S d s₂ σ σ' k) : Simulates S d (.ite c s₁ s₂) σ σ' (c.cost + 1 + k) := by
  intro pos q m B
  obtain ⟨hwc, -, hw₂⟩ := Stmt.width_ite_le_iff.1 B.width
  obtain ⟨testCode, -, -, elseCode⟩ := codeAt_ite B.codeAt
  have hpos : pos + (c.size + s₁.size S.F + 1 + s₂.size S.F) ≤ S.disp := B.below
  -- the test
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.test testCode hwc hs).of_fails fails
  -- the second branch
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih _ _ _
    (B.sub elseCode (by omega) hw₂ B.bounded (B.rel.same A₀))
  exact ⟨m₁, n₀ + n₁, {
    run := (run₀.trans run₁).cast_pos (by rw [Stmt.size]; omega)
    le := add_le_stepsPerStep_mul (by omega) (by omega) le₁
    rel := R₁
    agree := (A₀.mono scratch_subset_writable).trans A₁ }⟩

/-- while c do s, when c fails: the test jumps to the position after the loop. -/
private theorem sim_whileFalse {c : Cond} (hs : c.Safe S.lim σ) (fails : ¬ c.Holds σ) :
    Simulates S d (.while c s) σ σ (c.cost + 1) := by
  intro pos q m B
  obtain ⟨hwc, -⟩ := Stmt.width_while_le_iff.1 B.width
  obtain ⟨testCode, -, -⟩ := codeAt_while B.codeAt
  have hpos : pos + (c.size + s.size S.F + 1) ≤ S.disp := B.below
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.test testCode hwc hs).of_fails fails
  exact ⟨m₀, n₀, {
    run := run₀.cast_pos (by rw [Stmt.size]; omega)
    le := le_stepsPerStep_mul (by omega) (by omega)
    rel := B.rel.same A₀
    agree := A₀.mono scratch_subset_writable }⟩

/-- while c do s, when c holds: the test goes on to the code of s, a jump leads back to the test,
and the loop runs again. -/
private theorem sim_whileTrue {c : Cond} {k₁ k₂ : ℕ} (hs : c.Safe S.lim σ) (holds : c.Holds σ)
    (h₁ : Exec S.lim S.P d s σ σ₁ k₁) (ih₁ : Simulates S d s σ σ₁ k₁)
    (ih₂ : Simulates S d (.while c s) σ₁ σ₂ k₂) :
    Simulates S d (.while c s) σ σ₂ (c.cost + 1 + k₁ + k₂) := by
  intro pos q m B
  obtain ⟨hwc, hw⟩ := Stmt.width_while_le_iff.1 B.width
  obtain ⟨testCode, bodyCode, jumpCode⟩ := codeAt_while B.codeAt
  have hpos : pos + (c.size + s.size S.F + 1) ≤ S.disp := B.below
  -- the test
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.test testCode hwc hs).of_holds holds
  -- the body
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih₁ _ _ _
    (B.sub bodyCode (by omega) hw B.bounded (B.rel.same A₀))
  -- the jump back
  have run₂ := (run₀.trans run₁).trans (steps_jump jumpCode R₁.neg S.inRange_neg_one)
  -- the loop again
  obtain ⟨m₃, n₃, run₃, le₃, R₃, A₃⟩ := ih₂ _ _ _
    (B.sub B.codeAt B.below B.width (h₁.bounded B.bounded) R₁)
  exact ⟨m₃, n₀ + 1 + n₁ + n₃, {
    run := (run₂.trans run₃).cast_count (by omega)
    le := Nat.mul_add _ _ k₂ ▸ Nat.add_le_add (add_le_stepsPerStep_mul (by omega) (by omega) le₁)
        le₃
    rel := R₃
    agree := ((A₀.mono scratch_subset_writable).trans A₁).trans A₃ }⟩

/-! ## Calls -/

section call

variable {p x : ℕ} {args : List Expr}

/-- Entering a procedure: the arguments, the new frame with the position to return to, and the jump
to the entry e.  Afterwards the memory represents the state in which the procedure starts, in the
frame q + F + 1, and the stack cell before that frame holds the position after the jump.  Of the
stack, only cells from q + F on have changed. -/
private theorem steps_callEnter (B : Start S d (.call p args x) σ pos q m)
    (hsa : ∀ e ∈ args, e.Safe S.lim σ) (hd : d < S.lim.depth) {e : ℕ}
    (he : S.entry[p]? = some e) :
    ∃ m₂, Steps S.code (callSize S.F args) ⟨pos, m⟩ ⟨e, m₂⟩ ∧
      Rel S.toSizes ⟨frame (args.map (·.val σ)), σ.mem⟩ (q + S.F + 1) m₂ ∧
      m₂ (cStack (q + S.F)) = wd W ((pos + callSize S.F args : ℕ) : ℤ) ∧
      AgreeOutside (Writable S.toSizes (q + S.F)) m m₂ := by
  obtain ⟨-, hlen, hwa⟩ := Stmt.width_call_le_iff.1 B.width
  obtain ⟨frameCode, jumpCode, -⟩ := codeAt_call B.codeAt
  have hpos : pos + (callSize S.F args + 2) ≤ S.disp := B.below
  rw [List.getD_eq_getElem?_getD, he, Option.getD_some] at jumpCode
  -- the arguments: there are at most F of them, each of width at most F
  obtain ⟨vals, A⟩ := effects_argsCode B.toFramed args 0 hwa hsa (by omega)
  have A₁ := A.mono temps_subset_scratch
  -- the new frame
  obtain ⟨R₂, hret, A₂⟩ := effects_newFrame (B.toFramed.same A₁)
    ((Nat.le_add_right _ _).trans (B.room_succ hd)) args (by simpa using vals)
    (ret := pos + callSize S.F args) (by omega)
  have run₂ := steps_straight _ pos m frameCode
    (List.forall_mem_append.2 ⟨straight_argsCode _ _, straight_newFrame _ _ _⟩)
  rw [effects_append, List.length_append, length_argsCode, length_newFrame] at run₂
  -- the jump
  exact ⟨_, (run₂.trans (steps_jump jumpCode R₂.neg S.inRange_neg_one)).cast_count
    (by rw [callSize]; omega), R₂, hret, (A₁.mono scratch_subset_writable).trans A₂⟩

/-- Leaving a procedure whose frame is q + F + 1, when the stack cell before that frame holds the
position ret: the return sequence and the dispatcher.  The machine arrives at ret; RET holds the
result (local variable 0), FP points to the frame q, and otherwise only scratch cells have
changed. -/
private theorem steps_callLeave (S : Setting W) {ret : ℕ} (R : Rel S.toSizes σ (q + S.F + 1) m)
    (hcode : CodeAt S.code pos (epilogue S.toCodeLayout))
    (hret : m (cStack (q + S.F)) = wd W ret) (hlt : ret < S.disp) (hQ : q + S.F + 1 ≤ S.Q)
    (hF : 0 < S.F) :
    ∃ m', Steps S.code (epilogueSize + 2 * (ret + 1)) ⟨pos, m⟩ ⟨ret, m'⟩ ∧
      m' cFP = wd W (cStack q) ∧ m' cRET = wd W (σ.loc 0) ∧
      AgreeOutside (insert cFP (Scratch S.F)) m m' := by
  have hN := S.offsets_le
  -- RET := the cell at FP, which is local variable 0
  have run₁ := steps_load (i := cRET) hcode R.fp (S.inRange_stack hQ)
  rw [R.loc_zero hF] at run₁
  have A₁ := (AgreeOutside.refl (Scratch S.F) m).update (a := cRET) (by cells) (wd W (σ.loc 0))
  -- ADDR := FP + 2, the address of the stack cell before the frame
  have run₂ := run₁.trans (steps_add hcode.tail (R.same A₁).fp ((R.same A₁).pool 2 (by omega)))
  rw [cStack_succ_add] at run₂
  have A₂ := A₁.update (a := cADDR) (by cells) (wd W (cStack (q + S.F)))
  -- RR := the cell at ADDR, which holds ret
  have run₃ := run₂.trans (steps_load hcode.tail.tail (Function.update_self _ _ _)
    (S.inRange_stack (by omega)))
  rw [A₂.read (by cells) hret] at run₃
  have A₃ := A₂.update (a := cRR) (by cells) (wd W ret)
  -- FP := FP + 2 (F + 1), the frame of the caller
  have run₄ := run₃.trans (steps_add hcode.tail.tail.tail (R.same A₃).fp ((R.same A₃).pool _ hN))
  rw [Nat.add_assoc q, cStack_add] at run₄
  -- the jump to the dispatcher
  have run₅ := run₄.trans (steps_jump hcode.tail.tail.tail.tail
    (by cell_read using (R.same A₃).neg) S.inRange_neg_one)
  -- the dispatcher, which leaves -1 in RR
  have run₆ := run₅.trans (steps_dispatcher S.dispatcherAt hlt S.fits.pool_lt _
    (by cell_read using (R.same A₃).one) (by cell_read))
  exact ⟨_, run₆, by cell_read, by cell_read,
    ((A₃.mono (by cells)).update (by cells) _).update (by cells) _⟩

/-- x := p(args): enter, the body, leave, store the result. -/
private theorem sim_call {body : Stmt} {k : ℕ} (hsa : ∀ e ∈ args, e.Safe S.lim σ)
    (hp : S.P[p]? = some body) (hd : d < S.lim.depth)
    (ih : Simulates S (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ σ' k) :
    Simulates S d (.call p args x) σ ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩
      ((args.map Expr.cost).sum + 2 + k) := by
  intro pos q m B
  obtain ⟨hx, -, -⟩ := Stmt.width_call_le_iff.1 B.width
  obtain ⟨e, he, procCode, hend⟩ := S.bodyAt p body hp
  obtain ⟨-, -, resultCode⟩ := codeAt_call B.codeAt
  have hpos : pos + (callSize S.F args + 2) ≤ S.disp := B.below
  have hq := B.low
  have hroom := B.room_succ hd
  -- enter
  obtain ⟨m₁, run₁, R₁, hret, A₁⟩ := steps_callEnter B hsa hd he
  -- the body, in the frame q + F + 1
  obtain ⟨m₂, n₂, run₂, le₂, R₂, A₂⟩ := ih e (q + S.F + 1) m₁
    { rel := R₁, low := by omega, high := by omega, codeAt := procCode.left, below := by omega,
      width := S.width body (List.mem_of_getElem? hp),
      bounded := bounded_callFrame B.bounded args hsa, room := hroom }
  -- the body writes the stack only from its frame on, so the position to return to is still there
  have hret₂ := A₂.read (a := cStack (q + S.F)) (by cells) hret
  -- leave
  obtain ⟨m₃, run₃, hfp, hres, A₃⟩ := steps_callLeave S R₂
    (procCode.right.cast_pos (by rw [length_compileStmt])) hret₂ (by omega) (by omega)
    (Nat.zero_lt_of_lt hx)
  -- since the call began, the stack has changed only from cell q + F on: the local variables of the
  -- caller are as before, and the memory is as the procedure left it
  have A : AgreeOutside (Writable S.toSizes (q + S.F)) m m₃ :=
    (A₁.trans (A₂.mono (writable_subset_writable (by omega)))).trans
      (A₃.mono (Set.insert_subset (by cells) scratch_subset_writable))
  have I₃ : Framed S.toSizes ⟨σ.loc, σ'.mem⟩ q m₃ := ⟨R₂.of_agreeOutside A₃ (by cells) hfp
    (fun y hy => A.read (by cells) (B.rel.loc y hy))
    fun a ha => A₃.read (by cells) (R₂.mem a ha), hq, B.high⟩
  -- store the result
  obtain ⟨m₄, run₄, R₄, A₄⟩ := steps_setVar I₃ hx resultCode hres (by cells)
  exact ⟨m₄, _, {
    run := (((run₁.trans run₂).trans run₃).trans run₄).cast_pos (by rw [Stmt.size, Nat.add_assoc])
    le := call_le_stepsPerStep_mul hpos (by omega) le₂
    rel := R₄
    agree := (A.mono (writable_subset_writable (by omega))).trans A₄ }⟩

end call

/-! ## The theorem -/

/-- **The simulation theorem.**  The code of a statement matches every run of the statement. -/
theorem sim (S : Setting W) {c : ℕ} (h : Exec S.lim S.P d s σ σ' c) :
    Simulates S d s σ σ' c := by
  induction h with
  | skip => exact sim_skip
  | set hs => exact sim_set hs
  | store hsa hse haddr => exact sim_store hsa hse haddr
  | seq h₁ _ ih₁ ih₂ => exact sim_seq h₁ ih₁ ih₂
  | iteTrue hs holds _ ih => exact sim_iteTrue hs holds ih
  | iteFalse hs fails _ ih => exact sim_iteFalse hs fails ih
  | whileFalse hs fails => exact sim_whileFalse hs fails
  | whileTrue hs holds h₁ _ ih₁ ih₂ => exact sim_whileTrue hs holds h₁ ih₁ ih₂
  | call hsa hp hd _ ih => exact sim_call hsa hp hd ih

end Light.Compiler
