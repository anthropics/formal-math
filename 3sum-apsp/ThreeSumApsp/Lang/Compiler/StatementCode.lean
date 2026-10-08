/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Syntax
public import ThreeSumApsp.Machine.Steps
public import Mathlib.Data.Nat.Digits.Defs

/-!
# The compiler from the light language to the word RAM: cells, and the code of statements

This file holds the definitions: the cells, the code of expressions, tests, statements, calls and
returns, the length of each piece of code, and the one condition on the text of a program (its
width).  The code of a whole program, `compileProgram`, puts these pieces together.

**Cells.**  A memory cell a of the light language is the cell a ≥ 0 of the machine.  Everything else
lives in negative cells.  A whole program takes two arguments from the cells -1 and -2 (`cARG1`,
`cARG2`) and puts its result into the cell -3 (`cRESULT`); the cell -4 is not used.  Odd cells from
-5 down hold the registers of the compiled code, the temporaries T₀, T₁, … for the evaluation of
expressions, and a pool of numbers: the cell `cPool n` holds the number n, for all n up to the
largest position to return to.  Even cells hold the call stack: stack cell j is the cell -2 j
(`cStack`).  The outermost frame of a whole program begins at stack cell `mainFrame` = 4, so the
code of its statements writes no stack cell before the cell -8 and leaves the cells -1, …, -4
alone.  The lemmas about pieces of code ask less: only that a frame begins after stack cell 0.

**Numbers.**  The constants of the program text are built from their binary digits where they are
needed.  The numbers that the compiled code itself needs, offsets in a frame and positions to return
to, come from the pool: the length of the code that builds a number from its digits depends on the
number, and a position to return to depends on the lengths.

**Frames.**  With F local variables per procedure, the frame of a running procedure is given by a
number q: local variable x is the cell -2 (q + x), the position to return to is in the
cell -2 (q - 1), and the register FP holds -2 q.  A call moves q to q + F + 1.

**Jumps.**  The machine only has "branch if negative" to a fixed position.  An unconditional jump
tests a register that holds -1.  A return loads the position r to return to into the register RR and
jumps to the dispatcher, the code "RR := RR - 1; if RR < 0 go to j" for j = 0, 1, 2, …, which
arrives at position r after 2 (r + 1) steps: a constant for a fixed program.

**Calls.**  The caller evaluates the arguments into temporaries, computes the address of the new
frame, fills its local variables (arguments first, then zeros), stores the position to return to,
moves FP and jumps to the procedure.  The procedure ends with its return sequence: result into RET,
position into RR, FP back to the caller's frame, jump to the dispatcher.  Back in the caller, RET is
stored into the variable that receives the result.

**Lengths.**  A jump forward needs the length of code that is not yet written, so the lengths are
defined on the text (`Expr.size`, `Cond.size`, `Stmt.size`) and then shown to be the lengths of the
code (`length_compileExpr`, `length_compileCond`, `length_compileStmt`).
-/

@[expose] public section

namespace Light.Compiler

open EndStatement (Instr)

/-! ## Cells

The names of the registers are written in capitals, as in the comments on the code. -/

/-- The cell from which a whole program takes its first argument. -/
def cARG1 : ℤ := -1
/-- The cell from which a whole program takes its second argument. -/
def cARG2 : ℤ := -2
/-- The cell into which a whole program puts its result. -/
def cRESULT : ℤ := -3
/-- The register that holds 1. -/
def cONE : ℤ := -5
/-- The register that holds 0. -/
def cZERO : ℤ := -7
/-- The register that holds -1; an unconditional jump branches on it. -/
def cNEG : ℤ := -9
/-- The frame pointer FP: the address of local variable 0 of the running procedure. -/
def cFP : ℤ := -11
/-- The register ADDR: the address for the next load or store of a local variable. -/
def cADDR : ℤ := -13
/-- The register RET: the result of the procedure that has just returned. -/
def cRET : ℤ := -15
/-- The register RR: the position to return to, counted down by the dispatcher. -/
def cRR : ℤ := -17
/-- The register NFP: the frame pointer of the procedure that is about to be called. -/
def cNFP : ℤ := -19
/-- The register D: the difference that a test branches on. -/
def cD : ℤ := -21
/-- The temporaries. -/
def cT (k : ℕ) : ℤ := -(23 + 4 * (k : ℤ))
/-- The pool of numbers. -/
def cPool (n : ℕ) : ℤ := -(25 + 4 * (n : ℤ))
/-- The cell number j of the stack. -/
def cStack (j : ℕ) : ℤ := -(2 * (j : ℤ))
/-- The frame of the outermost statement of a whole program: the first whose cells lie beyond the
cells of the arguments and the result. -/
def mainFrame : ℕ := 4

/-! ## Expressions and tests -/

/-- The instruction of the machine for an operation. -/
def _root_.Light.Op.instr : Op → ℤ → ℤ → ℤ → Instr
  | .add => .add
  | .sub => .sub
  | .mul => .mul

/-- Code that builds in the cell c the number with the given binary digits, least significant digit
first: the number of the higher digits, doubled, plus the lowest digit. -/
def digitsCode (c : ℤ) : List ℕ → List Instr
  | [] => [.sub c c c]
  | d :: L => digitsCode c L ++ [.add c c c] ++ (if d = 0 then [] else [.add c c cONE])

/-- The length of `digitsCode c L`. -/
def digitsLen : List ℕ → ℕ
  | [] => 1
  | d :: L => digitsLen L + 1 + (if d = 0 then 0 else 1)

/-- Code that leaves the value of the expression in the temporary T_k, using only T_k, T_{k+1}, …
and ADDR.  A constant is built from its binary digits, in at most 2 log₂ n + 3 instructions. -/
def compileExpr : Expr → ℕ → List Instr
  | .const n, k => digitsCode (cT k) (Nat.digits 2 n)
  | .var x, k => [.sub cADDR cFP (cPool (2 * x)), .load (cT k) cADDR]
  | .op o a b, k => compileExpr a k ++ compileExpr b (k + 1) ++ [o.instr (cT k) (cT k) (cT (k + 1))]
  | .load a, k => compileExpr a k ++ [.load (cT k) (cT k)]

/-- The length of the code of an expression. -/
def _root_.Light.Expr.size : Expr → ℕ
  | .const n => digitsLen (Nat.digits 2 n)
  | .var _ => 2
  | .op _ a b => a.size + b.size + 1
  | .load a => a.size + 1

/-- Code that goes on to the next position if the test holds and jumps to the position l if it does
not.  Both tests evaluate a into T₀ and b into T₁.  For a < b the code forms D = b - a - 1 and
leaves if D < 0.  For a = b it forms D = a - b and leaves if D < 0, then forms -D and leaves if that
is negative. -/
def compileCond : Cond → ℕ → List Instr
  | .lt a b, l =>
    compileExpr a 0 ++ compileExpr b 1 ++ [.sub cD (cT 1) (cT 0), .sub cD cD cONE, .bltz cD l]
  | .eq a b, l =>
    compileExpr a 0 ++ compileExpr b 1 ++
      [.sub cD (cT 0) (cT 1), .bltz cD l, .sub cD cZERO cD, .bltz cD l]

/-- The length of the code of a test. -/
def _root_.Light.Cond.size : Cond → ℕ
  | .lt a b => a.size + b.size + 3
  | .eq a b => a.size + b.size + 4

/-! ## Statements -/

/-- What the code of a statement needs to know about the whole program. -/
structure CodeLayout : Type where
  /-- The number of local variables of every frame. -/
  F : ℕ
  /-- The positions of the procedures. -/
  entry : List ℕ
  /-- The position of the dispatcher. -/
  disp : ℕ

/-- The arguments of a call, evaluated into T_k, T_{k+1}, …. -/
def argsCode : List Expr → ℕ → List Instr
  | [], _ => []
  | e :: es, k => compileExpr e k ++ argsCode es (k + 1)

/-- The length of the code for the arguments of a call. -/
def argsSize : List Expr → ℕ
  | [] => 0
  | e :: es => e.size + argsSize es

/-- The local variables of the new frame: the first n from the temporaries, the others 0. -/
def frameInit (F n : ℕ) : List Instr :=
  (List.range F).flatMap fun i =>
    [.sub cADDR cNFP (cPool (2 * i)), .store cADDR (if i < n then cT i else cZERO)]

/-- The code of a call between the arguments and the jump to the procedure: the address of the new
frame into NFP, its local variables, the position ret to return to, and FP := NFP. -/
def newFrame (F n ret : ℕ) : List Instr :=
  [.sub cNFP cFP (cPool (2 * (F + 1)))] ++ frameInit F n ++
    [.add cADDR cNFP (cPool 2), .store cADDR (cPool ret), .add cFP cNFP cZERO]

/-- A call up to and including the jump to the procedure; ret is the position after the jump. -/
def callCode (G : CodeLayout) (p : ℕ) (args : List Expr) (ret : ℕ) : List Instr :=
  argsCode args 0 ++ newFrame G.F args.length ret ++ [.bltz cNEG (G.entry.getD p 0)]

/-- The length of a call up to and including the jump. -/
def callSize (F : ℕ) (args : List Expr) : ℕ := argsSize args + 1 + 2 * F + 4

/-- The length of the code of a statement. -/
def _root_.Light.Stmt.size (F : ℕ) : Stmt → ℕ
  | .skip => 0
  | .set _ e => e.size + 2
  | .store a e => a.size + e.size + 1
  | .seq s t => s.size F + t.size F
  | .ite c s t => c.size + s.size F + 1 + t.size F
  | .while c s => c.size + s.size F + 1
  | .call _ args _ => callSize F args + 2

/-- The code of a statement, for the position pos. -/
def compileStmt (G : CodeLayout) : Stmt → ℕ → List Instr
  | .skip, _ => []
  | .set x e, _ => compileExpr e 0 ++ [.sub cADDR cFP (cPool (2 * x)), .store cADDR (cT 0)]
  | .store a e, _ => compileExpr a 0 ++ compileExpr e 1 ++ [.store (cT 0) (cT 1)]
  | .seq s t, pos => compileStmt G s pos ++ compileStmt G t (pos + s.size G.F)
  | .ite c s t, pos =>
    compileCond c (pos + c.size + s.size G.F + 1) ++ compileStmt G s (pos + c.size) ++
      [.bltz cNEG (pos + c.size + s.size G.F + 1 + t.size G.F)] ++
      compileStmt G t (pos + c.size + s.size G.F + 1)
  | .while c s, pos =>
    compileCond c (pos + c.size + s.size G.F + 1) ++ compileStmt G s (pos + c.size) ++
      [.bltz cNEG pos]
  | .call p args x, pos =>
    callCode G p args (pos + callSize G.F args) ++
      [.sub cADDR cFP (cPool (2 * x)), .store cADDR cRET]

/-- The return sequence of a procedure: the result (local variable 0) into RET, the position to
return to into RR, the frame of the caller, and the jump to the dispatcher. -/
def epilogue (G : CodeLayout) : List Instr :=
  [.load cRET cFP, .add cADDR cFP (cPool 2), .load cRR cADDR,
    .add cFP cFP (cPool (2 * (G.F + 1))), .bltz cNEG G.disp]

/-- The length of the return sequence. -/
def epilogueSize : ℕ := 5

/-- The dispatcher for the positions below n. -/
def dispatcher (n : ℕ) : List Instr :=
  (List.range n).flatMap fun j => [.sub cRR cRR cONE, .bltz cRR j]

/-! ## Lengths -/

private theorem length_digitsCode (c : ℤ) (L : List ℕ) : (digitsCode c L).length = digitsLen L := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    simp only [digitsCode, digitsLen, List.length_append, ih, List.length_singleton]
    split_ifs <;> rfl

/-- The code of an expression has the length defined on the text. -/
theorem length_compileExpr (e : Expr) (k : ℕ) : (compileExpr e k).length = e.size := by
  induction e generalizing k with
  | const n => exact length_digitsCode _ _
  | var x => rfl
  | op o a b iha ihb => simp +arith [compileExpr, Expr.size, iha, ihb]
  | load a ih => simp [compileExpr, Expr.size, ih]

/-- The code of a test has the length defined on the text. -/
theorem length_compileCond (c : Cond) (l : ℕ) : (compileCond c l).length = c.size := by
  cases c <;> simp +arith [compileCond, Cond.size, length_compileExpr]

/-- The code for the arguments of a call has the length defined on the text. -/
theorem length_argsCode (es : List Expr) (k : ℕ) : (argsCode es k).length = argsSize es := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih => simp [argsCode, argsSize, length_compileExpr, ih]

/-- Two instructions for each local variable of the new frame. -/
private theorem length_frameInit (F n : ℕ) : (frameInit F n).length = 2 * F := by
  simp [frameInit, List.length_flatMap, Nat.mul_comm]

/-- The code between the arguments and the jump has 2 F + 4 instructions. -/
theorem length_newFrame (F n ret : ℕ) : (newFrame F n ret).length = 2 * F + 4 := by
  simp +arith [newFrame, length_frameInit]

/-- A call up to its jump has the length defined on the text. -/
private theorem length_callCode (G : CodeLayout) (p : ℕ) (args : List Expr) (ret : ℕ) :
    (callCode G p args ret).length = callSize G.F args := by
  simp +arith [callCode, callSize, length_argsCode, length_newFrame]

theorem length_epilogue (G : CodeLayout) : (epilogue G).length = epilogueSize := rfl

/-- The code of a statement has the length defined on the text. -/
theorem length_compileStmt (G : CodeLayout) (s : Stmt) (pos : ℕ) :
    (compileStmt G s pos).length = s.size G.F := by
  induction s generalizing pos with
  | skip => rfl
  | set x e => simp [compileStmt, Stmt.size, length_compileExpr]
  | store a e => simp +arith [compileStmt, Stmt.size, length_compileExpr]
  | seq s t ihs iht => simp [compileStmt, Stmt.size, ihs, iht]
  | ite c s t ihs iht => simp +arith [compileStmt, Stmt.size, ihs, iht, length_compileCond]
  | «while» c s ih => simp +arith [compileStmt, Stmt.size, ih, length_compileCond]
  | call p args x => simp [compileStmt, Stmt.size, length_callCode]

end Compiler

/-! ## The width of a text

The compiled code gives every frame the same number F of local variables.  That is enough if F is at
least the width of every body: a number that bounds the variables, the arguments of each call, and
the temporaries that each expression needs.  Then 2 F + 1 temporaries are enough too: up to F
arguments of a call wait in temporaries while the last one is evaluated in up to F more.  "The width
is at most F" is taken apart by one lemma for each construct. -/

/-- One more than the largest variable of an expression. -/
def Expr.vars : Expr → ℕ
  | .const _ => 0
  | .var x => x + 1
  | .op _ a b => max a.vars b.vars
  | .load a => a.vars

/-- The number of temporaries that the code of an expression uses. -/
def Expr.height : Expr → ℕ
  | .const _ => 1
  | .var _ => 1
  | .op _ a b => max a.height (b.height + 1)
  | .load a => a.height

/-- The width of an expression: at least its variables and its temporaries. -/
def Expr.width (e : Expr) : ℕ := max e.vars e.height

/-- The width of a test: that of its two sides. -/
def Cond.width : Cond → ℕ
  | .lt a b => max a.width b.width
  | .eq a b => max a.width b.width

/-- The largest value of f on a list. -/
def maxOf {α : Type} (f : α → ℕ) : List α → ℕ
  | [] => 0
  | x :: l => max (f x) (maxOf f l)

/-- The width of a statement: at least the width of its expressions, one more than each variable
that it writes, and the number of arguments of each of its calls. -/
def Stmt.width : Stmt → ℕ
  | .skip => 0
  | .set x e => max (x + 1) e.width
  | .store a e => max a.width e.width
  | .seq s t => max s.width t.width
  | .ite c s t => max c.width (max s.width t.width)
  | .while c s => max c.width s.width
  | .call _ args x => max (x + 1) (max args.length (maxOf Expr.width args))

section width

variable {F x p : ℕ} {o : Op} {a b e : Expr} {c : Cond} {s t : Stmt} {args : List Expr}

theorem maxOf_le_iff {α : Type} {f : α → ℕ} {l : List α} : maxOf f l ≤ F ↔ ∀ y ∈ l, f y ≤ F := by
  induction l <;> simp [maxOf, *]

theorem Expr.vars_op_le_iff : (Expr.op o a b).vars ≤ F ↔ a.vars ≤ F ∧ b.vars ≤ F := max_le_iff

theorem Expr.width_le_iff : e.width ≤ F ↔ e.vars ≤ F ∧ e.height ≤ F := max_le_iff

theorem Cond.width_lt_le_iff : (Cond.lt a b).width ≤ F ↔ a.width ≤ F ∧ b.width ≤ F := max_le_iff

theorem Cond.width_eq_le_iff : (Cond.eq a b).width ≤ F ↔ a.width ≤ F ∧ b.width ≤ F := max_le_iff

theorem Stmt.width_set_le_iff : (Stmt.set x e).width ≤ F ↔ x < F ∧ e.width ≤ F := max_le_iff

theorem Stmt.width_store_le_iff : (Stmt.store a e).width ≤ F ↔ a.width ≤ F ∧ e.width ≤ F :=
  max_le_iff

theorem Stmt.width_seq_le_iff : (Stmt.seq s t).width ≤ F ↔ s.width ≤ F ∧ t.width ≤ F := max_le_iff

theorem Stmt.width_ite_le_iff :
    (Stmt.ite c s t).width ≤ F ↔ c.width ≤ F ∧ s.width ≤ F ∧ t.width ≤ F := by
  simp only [Stmt.width, max_le_iff]

theorem Stmt.width_while_le_iff : (Stmt.while c s).width ≤ F ↔ c.width ≤ F ∧ s.width ≤ F :=
  max_le_iff

theorem Stmt.width_call_le_iff :
    (Stmt.call p args x).width ≤ F ↔ x < F ∧ args.length ≤ F ∧ ∀ e ∈ args, e.width ≤ F := by
  simp only [Stmt.width, max_le_iff, maxOf_le_iff, Nat.succ_le_iff]

end width

end Light
