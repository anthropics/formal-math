/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Compiler.Dispatcher

/-!
# The code of a whole program

`compileProgram P p0 dec` is the program of the word RAM that runs procedure p0 of the light
program P.  With dec = false it accepts at the end of the run; with dec = true it accepts if the
result of the procedure is positive and rejects if not.  It has five parts:

| position | part |
|---|---|
| 0 | `headCode`: the numbers 1, 0, -1, and a jump to the start-up code |
| `mainPos` | `mainCode`: the outermost statement `mainStmt p0`, then the verdict (`tailCode`) |
| `firstBody` | `bodiesCode`: the bodies of the procedures, each with its return sequence |
| `dispPos` | the dispatcher for the positions below `dispPos` |
| `3 * dispPos` | `startCode`: the pool, the outermost frame, and a jump back to `mainPos` |

The start-up code comes last so that no position in the rest of the code depends on its length.

The number `frameSize` of local variables of every frame is read off the text of P: it is the width
of the text.  The pool holds the numbers up to `dispPos`: every position to return to, and with them
the smaller numbers that the code needs (`two_mul_frameSize_add_le_dispPos`).

The facts proved here are about positions only: each part is where the table says
(`codeAt_headCode`, …, `codeAt_startCode`), and every body is at its entry (`codeAt_bodies`).
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

open EndStatement (Instr)

/-! ## The number read off the text -/

/-- The number of local variables of every frame: the width of the text, and at least 3 for the
outermost frame. -/
def frameSize (P : Program) : ℕ := max 3 (maxOf Stmt.width P)

/-- The outermost frame has room for the result and the two arguments. -/
theorem three_le_frameSize (P : Program) : 3 ≤ frameSize P := le_max_left _ _

/-- Every body fits into a frame. -/
theorem width_le_frameSize {P : Program} {b : Stmt} (hb : b ∈ P) : b.width ≤ frameSize P :=
  (maxOf_le_iff.1 le_rfl b hb).trans (le_max_right _ _)

/-! ## The parts of the code -/

/-- The outermost statement: procedure p0 is called on the local variables 1 and 2 of the outermost
frame, and its result goes to local variable 0. -/
def _root_.Light.mainStmt (p0 : ℕ) : Stmt := .call p0 [.var 1, .var 2] 0

/-- What follows the outermost statement, from position pos on: the result, which is local
variable 0 of the outermost frame, goes to the cell `cRESULT`; then the machine accepts, or, if dec
is set, it accepts if the result is positive and rejects if not. -/
def tailCode (dec : Bool) (pos : ℕ) : List Instr :=
  .add cRESULT (cStack mainFrame) cZERO ::
    (if dec then [.sub cD cZERO (cStack mainFrame), .bltz cD (pos + 4), .reject, .accept]
      else [.accept])

/-- The position of the outermost statement: after the four instructions of `headCode`. -/
def mainPos : ℕ := 4

/-- The position of the code that follows the outermost statement. -/
def tailPos (F : ℕ) : ℕ := mainPos + (mainStmt 0).size F

/-- The position of the first body: after the outermost statement and what follows it. -/
def firstBody (F : ℕ) (dec : Bool) : ℕ := tailPos F + (tailCode dec 0).length

/-- The positions of the bodies, the first of them at pos.  A body is followed by the return
sequence. -/
def entries (F : ℕ) : List Stmt → ℕ → List ℕ
  | [], _ => []
  | b :: bs, pos => pos :: entries F bs (pos + b.size F + epilogueSize)

/-- The position after the bodies, the first of them at pos. -/
def endPos (F : ℕ) : List Stmt → ℕ → ℕ
  | [], pos => pos
  | b :: bs, pos => endPos F bs (pos + b.size F + epilogueSize)

/-- The position after the last body, which is the position of the dispatcher.  It is also the
largest number in the pool. -/
def dispPos (P : Program) (dec : Bool) : ℕ := endPos (frameSize P) P (firstBody (frameSize P) dec)

/-- What the code of the statements of P needs to know about the whole code. -/
def codeLayout (P : Program) (dec : Bool) : CodeLayout :=
  ⟨frameSize P, entries (frameSize P) P (firstBody (frameSize P) dec), dispPos P dec⟩

/-- The bodies with their return sequences, the first of them at pos. -/
def bodiesCode (G : CodeLayout) : List Stmt → ℕ → List Instr
  | [], _ => []
  | b :: bs, pos =>
    (compileStmt G b pos ++ epilogue G) ++ bodiesCode G bs (pos + b.size G.F + epilogueSize)

/-- The first three instructions: the numbers 1, 0, -1. -/
def headStraight : List Instr := [.one cONE, .sub cZERO cONE cONE, .sub cNEG cZERO cONE]

/-- The code that fills the pool with the numbers 0, …, N. -/
def poolCode (N : ℕ) : List Instr :=
  .sub (cPool 0) cONE cONE :: (List.range N).map fun n => .add (cPool (n + 1)) (cPool n) cONE

/-- The code that puts zeros into the local variables of the outermost frame. -/
def zeroCode (F : ℕ) : List Instr :=
  (List.range F).map fun x => .sub (cStack (mainFrame + x)) cONE cONE

/-- The code that sets up the outermost frame: FP, zeros in its local variables, and then the two
arguments in its local variables 1 and 2. -/
def frameCode (F : ℕ) : List Instr :=
  .sub cFP cZERO (cPool (2 * mainFrame)) ::
    (zeroCode F ++
      [.add (cStack (mainFrame + 1)) cARG1 cZERO, .add (cStack (mainFrame + 2)) cARG2 cZERO])

/-- The start-up code without its last jump. -/
def startStraight (F N : ℕ) : List Instr := poolCode N ++ frameCode F

/-- The first part: the numbers 1, 0, -1, and the jump to the start-up code. -/
def headCode (P : Program) (dec : Bool) : List Instr :=
  headStraight ++ [.bltz cNEG (3 * dispPos P dec)]

/-- The second part: the outermost statement and the verdict. -/
def mainCode (P : Program) (p0 : ℕ) (dec : Bool) : List Instr :=
  compileStmt (codeLayout P dec) (mainStmt p0) mainPos ++ tailCode dec (tailPos (frameSize P))

/-- The last part: the start-up code and the jump back to the outermost statement. -/
def startCode (P : Program) (dec : Bool) : List Instr :=
  startStraight (frameSize P) (dispPos P dec) ++ [.bltz cNEG mainPos]

/-- **The code of a program.**  With dec = false the machine accepts at the end of the run; with
dec = true it accepts if the result of procedure p0 is positive and rejects if not. -/
def _root_.Light.compileProgram (P : Program) (p0 : ℕ) (dec : Bool) : List Instr :=
  headCode P dec ++ mainCode P p0 dec ++ bodiesCode (codeLayout P dec) P
      (firstBody (frameSize P) dec) ++
    dispatcher (dispPos P dec) ++ startCode P dec

/-! ## Lengths and positions -/

private theorem le_endPos (F : ℕ) : ∀ (bs : List Stmt) (pos : ℕ), pos ≤ endPos F bs pos
  | [], _ => le_rfl
  | b :: bs, pos => le_trans (by omega) (le_endPos F bs (pos + b.size F + epilogueSize))

/-- The length of the outermost statement. -/
theorem size_mainStmt (p0 F : ℕ) : (mainStmt p0).size F = 2 * F + 11 := by
  simp +arith [mainStmt, Stmt.size, callSize, argsSize, Expr.size]

/-- The outermost statement uses the local variables 0, 1, 2. -/
theorem width_mainStmt (p0 : ℕ) : (mainStmt p0).width = 3 := rfl

private theorem length_tailCode (dec : Bool) (pos : ℕ) :
    (tailCode dec pos).length = if dec then 5 else 2 := by
  cases dec <;> rfl

/-- The dispatcher comes after four instructions, the 2 F + 11 instructions of the outermost
statement and at least two for the verdict.  So the pool also holds the distance 2 (F + 1) between
two frames and the number 2 · `mainFrame` from which the start-up code forms the first frame
pointer, and it reaches further down than the 2 F + 1 temporaries. -/
theorem two_mul_frameSize_add_le_dispPos (P : Program) (dec : Bool) :
    2 * frameSize P + 17 ≤ dispPos P dec := by
  have : firstBody (frameSize P) dec ≤ dispPos P dec := le_endPos _ _ _
  have htail : 2 ≤ if dec then 5 else 2 := by split_ifs <;> omega
  simp only [firstBody, tailPos, mainPos, size_mainStmt, length_tailCode] at this
  omega

private theorem length_bodiesCode (G : CodeLayout) :
    ∀ (bs : List Stmt) (pos : ℕ), pos + (bodiesCode G bs pos).length = endPos G.F bs pos
  | [], _ => rfl
  | b :: bs, pos => by
    have ih := length_bodiesCode G bs (pos + b.size G.F + epilogueSize)
    simp only [bodiesCode, endPos, List.length_append, length_compileStmt, length_epilogue]
    omega

section parts

variable (P : Program) (p0 : ℕ) (dec : Bool)

private theorem length_through_mainCode :
    (headCode P dec ++ mainCode P p0 dec).length = firstBody (frameSize P) dec := by
  simp only [headCode, headStraight, mainCode, List.length_append, length_compileStmt,
    size_mainStmt, length_tailCode, firstBody, tailPos, mainPos, codeLayout, List.length_cons,
    List.length_nil]
  omega

private theorem length_through_bodiesCode :
    (headCode P dec ++ mainCode P p0 dec ++
      bodiesCode (codeLayout P dec) P (firstBody (frameSize P) dec)).length = dispPos P dec := by
  rw [List.length_append, length_through_mainCode]
  exact length_bodiesCode (codeLayout P dec) P _

private theorem length_through_dispatcher :
    (headCode P dec ++ mainCode P p0 dec ++
      bodiesCode (codeLayout P dec) P (firstBody (frameSize P) dec) ++
      dispatcher (dispPos P dec)).length = 3 * dispPos P dec := by
  rw [List.length_append, length_through_bodiesCode, length_dispatcher]
  omega

/-- The first part is at position 0. -/
theorem codeAt_headCode : CodeAt (compileProgram P p0 dec) 0 (headCode P dec) :=
  (codeAt_self _).left.left.left.left

private theorem codeAt_mainCode : CodeAt (compileProgram P p0 dec) mainPos (mainCode P p0 dec) :=
  (codeAt_self _).left.left.left.right

/-- The outermost statement is at `mainPos`. -/
theorem codeAt_mainStmt :
    CodeAt (compileProgram P p0 dec) mainPos
      (compileStmt (codeLayout P dec) (mainStmt p0) mainPos) :=
  (codeAt_mainCode P p0 dec).left

/-- The code for the verdict follows the outermost statement. -/
theorem codeAt_tailCode :
    CodeAt (compileProgram P p0 dec) (tailPos (frameSize P))
      (tailCode dec (tailPos (frameSize P))) :=
  (codeAt_mainCode P p0 dec).right.cast_pos (by
    simp only [length_compileStmt, size_mainStmt, tailPos, codeLayout])

/-- The bodies begin at `firstBody`. -/
theorem codeAt_bodiesCode :
    CodeAt (compileProgram P p0 dec) (firstBody (frameSize P) dec)
      (bodiesCode (codeLayout P dec) P (firstBody (frameSize P) dec)) :=
  (codeAt_self _).left.left.right.cast_pos (by rw [length_through_mainCode, Nat.zero_add])

/-- The dispatcher is at `dispPos`. -/
theorem codeAt_dispatcher_dispPos :
    CodeAt (compileProgram P p0 dec) (dispPos P dec) (dispatcher (dispPos P dec)) :=
  (codeAt_self _).left.right.cast_pos (by rw [length_through_bodiesCode, Nat.zero_add])

/-- The start-up code follows the dispatcher. -/
theorem codeAt_startCode :
    CodeAt (compileProgram P p0 dec) (3 * dispPos P dec) (startCode P dec) :=
  (codeAt_self _).right.cast_pos (by rw [length_through_dispatcher, Nat.zero_add])

end parts

/-- Every body is at its entry, followed by the return sequence, and ends at or before the position
after the bodies. -/
theorem codeAt_bodies {code : List Instr} (G : CodeLayout) :
    ∀ (bs : List Stmt) (pos : ℕ), CodeAt code pos (bodiesCode G bs pos) →
      ∀ (p : ℕ) (b : Stmt), bs[p]? = some b → ∃ e, (entries G.F bs pos)[p]? = some e ∧
        CodeAt code e (compileStmt G b e ++ epilogue G) ∧
        e + b.size G.F + epilogueSize ≤ endPos G.F bs pos
  | [], _, _, p, b, h => by simp at h
  | b₀ :: bs, pos, hc, 0, b, h => by
    obtain rfl : b₀ = b := by simpa using h
    exact ⟨pos, rfl, hc.left, le_endPos _ _ _⟩
  | b₀ :: bs, pos, hc, p + 1, b, h =>
    codeAt_bodies G bs _
      (hc.right.cast_pos (by
        rw [List.length_append, length_compileStmt, length_epilogue, Nat.add_assoc])) p b
      (by simpa using h)

end Light.Compiler
