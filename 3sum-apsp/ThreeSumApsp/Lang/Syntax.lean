/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Group.Unbundled.Abs

/-!
# The light language

A small imperative language with procedures and recursion, in which the paper's procedures can be
written almost as printed.  It is a proof device: a program of this language is compiled
(`compileProgram`) to the word RAM of the end statement, and the compiler is proved to keep results
and, up to a constant factor that depends on the program text only, step counts.

* A program is a finite piece of data: a list of procedure bodies.  It contains no Lean functions.
* The memory is an array of integers addressed by natural numbers.  Each running procedure has local
  variables 0, 1, 2, ….
* Arithmetic: +, −, ×.  There is no division.  Comparisons (<, =) occur as the tests of if and
  while.
* Every executed operation costs one step: each constant, variable, operation and load of an
  expression, each comparison, assignment, store, branch, call and return.
* A run is subject to limits: it forms no value of absolute value above `word`, touches no cell at
  an address ≥ `space`, and nests calls at most `depth` deep.  A run that would break a limit does
  not exist.
-/

@[expose] public section

namespace Light

/-- The operations on two words. -/
inductive Op : Type
  | add | sub | mul
  deriving DecidableEq, Repr

/-- The result of an operation. -/
def Op.eval : Op → ℤ → ℤ → ℤ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

/-- Expressions: constants, local variables, operations, and the content of the memory cell at an
address. -/
inductive Expr : Type
  | const (n : ℕ)
  | var (x : ℕ)
  | op (o : Op) (a b : Expr)
  | load (a : Expr)
  deriving Repr

/-- Tests. -/
inductive Cond : Type
  | lt (a b : Expr)
  | eq (a b : Expr)
  deriving Repr

/-- Statements.  `call p args x` runs procedure number p on the values of args and puts its result
into x. -/
inductive Stmt : Type
  | skip
  | set (x : ℕ) (e : Expr)
  | store (a e : Expr)
  | seq (s₁ s₂ : Stmt)
  | ite (c : Cond) (s₁ s₂ : Stmt)
  | while (c : Cond) (s : Stmt)
  | call (p : ℕ) (args : List Expr) (x : ℕ)
  deriving Repr

/-- A program: the bodies of its procedures, numbered from 0. -/
abbrev Program : Type := List Stmt

/-- What a running procedure sees: its local variables and the memory. -/
structure State : Type where
  loc : ℕ → ℤ
  mem : ℕ → ℤ

/-- The limits on a run: largest absolute value of a word, number of memory cells, nesting depth of
calls. -/
structure Limits : Type where
  word : ℤ
  space : ℕ
  depth : ℕ

/-- The value of an expression. -/
def Expr.val (s : State) : Expr → ℤ
  | .const n => n
  | .var x => s.loc x
  | .op o a b => o.eval (a.val s) (b.val s)
  | .load a => s.mem (a.val s).toNat

/-- The number of steps that evaluating an expression takes: one for each of its constants,
variables, operations, loads. -/
def Expr.cost : Expr → ℕ
  | .const _ => 1
  | .var _ => 1
  | .op _ a b => a.cost + b.cost + 1
  | .load a => a.cost + 1

/-- An address within the limits. -/
def Limits.Addr (lim : Limits) (a : ℤ) : Prop := 0 ≤ a ∧ a < lim.space

/-- The evaluation of an expression stays within the limits: every value that is formed fits in a
word, and every address that is read is within the memory. -/
def Expr.Safe (lim : Limits) (s : State) : Expr → Prop
  | .const n => (n : ℤ) ≤ lim.word
  | .var _ => True
  | .op o a b => a.Safe lim s ∧ b.Safe lim s ∧ |o.eval (a.val s) (b.val s)| ≤ lim.word
  | .load a => a.Safe lim s ∧ lim.Addr (a.val s)

/-- Whether a test holds. -/
def Cond.Holds (s : State) : Cond → Prop
  | .lt a b => a.val s < b.val s
  | .eq a b => a.val s = b.val s

/-- The number of steps of a test: its two sides and the comparison. -/
def Cond.cost : Cond → ℕ
  | .lt a b => a.cost + b.cost + 1
  | .eq a b => a.cost + b.cost + 1

/-- The evaluation of a test stays within the limits. -/
def Cond.Safe (lim : Limits) (s : State) : Cond → Prop
  | .lt a b => a.Safe lim s ∧ b.Safe lim s
  | .eq a b => a.Safe lim s ∧ b.Safe lim s

/-- The local variables of a procedure that has just been called: the arguments in 0, 1, …, and 0 in
all others. -/
def frame (args : List ℤ) : ℕ → ℤ := fun i => args.getD i 0

/-- The memory that holds the list ws in the cells 0, 1, 2, … and 0 elsewhere. -/
def memOf (ws : List ℤ) : ℕ → ℤ := fun a => ws.getD a 0

/-- `Exec lim P d s σ σ' c`: within the limits lim, and at nesting depth d of calls, the statement
s of the program P, started in the state σ, ends in the state σ' after exactly c steps. -/
inductive Exec (lim : Limits) (P : Program) : ℕ → Stmt → State → State → ℕ → Prop
  | skip {d σ} : Exec lim P d .skip σ σ 0
  | set {d σ x e} : e.Safe lim σ →
      Exec lim P d (.set x e) σ { σ with loc := Function.update σ.loc x (e.val σ) } (e.cost + 1)
  | store {d σ a e} : a.Safe lim σ → e.Safe lim σ → lim.Addr (a.val σ) →
      Exec lim P d (.store a e) σ { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }
        (a.cost + e.cost + 1)
  | seq {d σ σ' σ'' s₁ s₂ c₁ c₂} : Exec lim P d s₁ σ σ' c₁ → Exec lim P d s₂ σ' σ'' c₂ →
      Exec lim P d (.seq s₁ s₂) σ σ'' (c₁ + c₂)
  | iteTrue {d σ σ' c s₁ s₂ k} : c.Safe lim σ → c.Holds σ → Exec lim P d s₁ σ σ' k →
      Exec lim P d (.ite c s₁ s₂) σ σ' (c.cost + 1 + k)
  | iteFalse {d σ σ' c s₁ s₂ k} : c.Safe lim σ → ¬ c.Holds σ → Exec lim P d s₂ σ σ' k →
      Exec lim P d (.ite c s₁ s₂) σ σ' (c.cost + 1 + k)
  | whileFalse {d σ c s} : c.Safe lim σ → ¬ c.Holds σ → Exec lim P d (.while c s) σ σ (c.cost + 1)
  | whileTrue {d σ σ' σ'' c s k₁ k₂} : c.Safe lim σ → c.Holds σ → Exec lim P d s σ σ' k₁ →
      Exec lim P d (.while c s) σ' σ'' k₂ → Exec lim P d (.while c s) σ σ'' (c.cost + 1 + k₁ + k₂)
  | call {d σ σ' p args x body k} : (∀ e ∈ args, e.Safe lim σ) → P[p]? = some body → d < lim.depth →
      Exec lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ σ' k →
      Exec lim P d (.call p args x) σ ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩
        ((args.map Expr.cost).sum + 2 + k)

/-- Everything held in a variable or in a cell fits in a word. -/
def State.Bounded (lim : Limits) (σ : State) : Prop :=
  (∀ x, |σ.loc x| ≤ lim.word) ∧ ∀ a, |σ.mem a| ≤ lim.word

end Light
