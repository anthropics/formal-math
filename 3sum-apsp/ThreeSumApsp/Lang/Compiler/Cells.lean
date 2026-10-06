/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Compiler.StatementCode

/-!
# The cells of the compiled code, and the memories that represent a state

The memory of the machine is one array indexed by the integers, and the compiled code keeps its
registers, temporaries, pool, stack and the memory of the light language in different parts of it.
Every proof about compiled code has to know that a write to one cell leaves the others alone.  This
file settles that once.

* Sets of cells: `Temps k F` (what evaluating an expression into T_k may change), `Scratch F` (what
  any compiled code uses freely), `Constants N` (what no compiled statement changes), `Writable Z q`
  (what a statement that runs in the frame q may change), and two parts of the memory, `Stack q Q`
  and `Pool N`.  "The memories m and m' differ only inside s" is `AgreeOutside s m m'`.
* The tactic `cells` proves that two cells are different, that a cell is or is not in one of these
  sets, or that one of these sets lies in another.  The tactic `cell_read` reads a cell of a memory
  that is given by writes.
* `Sizes W` collects the numbers that never change, with the assumptions on them: the layout of the
  code, the limits, the number of stack cells, and a word size W that fits them (`Fits`).
* `Rel Z σ q m`: the memory m represents the state σ in the frame q.  The relation survives changes
  of scratch cells (`Rel.same`) and of the stack beyond the frame (`Rel.beyond`); a write to the
  cell of a local variable or to a memory cell is the same write in the state (`Rel.setLoc`,
  `Rel.setMem`).  All four come from `Rel.of_agreeOutside`.  `Framed` adds that the frame lies
  within the stack.
* Two pieces of code that occur everywhere: the jump (`steps_jump`) and the two instructions that
  store a cell in a local variable (`steps_setVar`).

**Letters**, in this file and in the files on expressions, tests, calls and the simulation.
Numbers: W is the word size, F the number of local variables of a frame, N the largest number in the
pool, Q the number of stack cells, q a frame, pos a position in the code.  The temporaries are
written T₀, T₁, …, T_j; there are 2 F + 1 of them.
Facts: m, m₁, m₂, … are memories in the order in which they arise.  Z is a `Sizes`.  R says that a
memory represents a state (`Rel`), I the same with the frame inside the stack (`Framed`).  A says
that two memories agree outside a set of cells (`AgreeOutside`); A₂ speaks of m₂.  run is a run of
the machine (`Steps`).  val, va, vb say which number a cell holds.  hcode and names that end in Code
say where a piece of code is (`CodeAt`).
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

open EndStatement (Instr)

/-! ## The numbers that never change -/

/-- The word size is large enough for the limits: words hold 2 · word + 2 (so the difference of two
values, and one less, is in range), all addresses of the memory, all addresses of a stack of Q
cells, and all numbers 0, …, N of the pool. -/
structure Fits (W : ℕ) (lim : Limits) (N Q : ℕ) : Prop where
  word : 2 * (2 * lim.word + 2) < (2 : ℤ) ^ W
  space : 2 * (lim.space : ℤ) < (2 : ℤ) ^ W
  stack : 2 * (2 * (Q : ℤ)) < (2 : ℤ) ^ W
  pool_lt : 2 * (N : ℤ) < (2 : ℤ) ^ W

/-- A number within the limit on words is in the range of words. -/
theorem Fits.inRange {W : ℕ} {lim : Limits} {N Q : ℕ} (hfit : Fits W lim N Q) {v : ℤ}
    (h : |v| ≤ lim.word) : InRange W v :=
  inRange_of_abs_le (by have := hfit.word; have := (abs_nonneg v).trans h; omega) h

/-- The numbers on which the proofs about compiled code depend: the layout of the code, the limits
on the runs of the light program, and the number of stack cells.  The pool holds the numbers from 0
to the position of the dispatcher. -/
structure Sizes (W : ℕ) extends CodeLayout where
  /-- The limits on the runs of the light program. -/
  lim : Limits
  /-- The number of stack cells. -/
  Q : ℕ
  /-- The word size fits the limits, the pool and the stack. -/
  fits : Fits W lim disp Q
  /-- The pool holds the numbers up to 2 (F + 1), which are the offsets in a frame. -/
  offsets_le : 2 * (F + 1) ≤ disp

/-! ## Sets of cells -/

/-- What the evaluation of an expression into T_k may change: ADDR and the temporaries T_j with
k ≤ j ≤ 2 F. -/
def Temps (k F : ℕ) : Set ℤ := {a | a = cADDR ∨ ∃ j, k ≤ j ∧ j ≤ 2 * F ∧ a = cT j}

/-- The stack cells j with q ≤ j < Q. -/
def Stack (q Q : ℕ) : Set ℤ := {a | ∃ j, q ≤ j ∧ j < Q ∧ a = cStack j}

/-- The cells of the local variables of the outermost frame. -/
def MainFrame (F : ℕ) : Set ℤ := Stack mainFrame (mainFrame + F)

/-- The cells of the pool that hold the numbers 0, …, N. -/
def Pool (N : ℕ) : Set ℤ := {a | ∃ n, n ≤ N ∧ a = cPool n}

/-- The cells that the start-up code fills and no compiled statement changes: the registers for 1,
0, -1 and the pool. -/
def Constants (N : ℕ) : Set ℤ := {cONE, cZERO, cNEG} ∪ Pool N

/-- The cells that compiled code uses freely: the registers D, RET, RR, NFP, ADDR and the
temporaries. -/
def Scratch (F : ℕ) : Set ℤ := {cD, cRET, cRR, cNFP} ∪ Temps 0 F

/-- What the code of a statement that runs in the frame q may change: scratch cells, FP, the stack
cells from q on, and the memory cells within the limits. -/
def Writable {W : ℕ} (Z : Sizes W) (q : ℕ) : Set ℤ :=
  Scratch Z.F ∪ {cFP} ∪ Stack q Z.Q ∪ {a | 0 ≤ a ∧ a < Z.lim.space}

/-! The temporaries, the stack and the pool are arithmetic progressions of cells. -/

theorem mem_temps_iff {k F : ℕ} {a : ℤ} :
    a ∈ Temps k F ↔ a = cADDR ∨ cT (2 * F) ≤ a ∧ a ≤ cT k ∧ 4 ∣ cT 0 - a := by
  simp only [Temps, cT, Set.mem_ofPred_eq]
  refine or_congr_right ⟨?_, fun h => ⟨((-23 - a) / 4).toNat, ?_⟩⟩
  · rintro ⟨j, hk, hj, rfl⟩
    omega
  · omega

theorem mem_stack_iff {q Q : ℕ} {a : ℤ} :
    a ∈ Stack q Q ↔ cStack Q < a ∧ a ≤ cStack q ∧ 2 ∣ a := by
  simp only [Stack, cStack, Set.mem_ofPred_eq]
  refine ⟨?_, fun h => ⟨(-a / 2).toNat, ?_⟩⟩
  · rintro ⟨j, hq, hj, rfl⟩
    omega
  · omega

theorem mem_pool_iff {N : ℕ} {a : ℤ} :
    a ∈ Pool N ↔ cPool N ≤ a ∧ a ≤ cPool 0 ∧ 4 ∣ cPool 0 - a := by
  simp only [Pool, cPool, Set.mem_ofPred_eq]
  refine ⟨?_, fun h => ⟨((-25 - a) / 4).toNat, ?_⟩⟩
  · rintro ⟨n, hn, rfl⟩
    omega
  · omega

/-- Proves that two cells of the compiled code are different, that a cell is or is not in one of the
sets above, or that one of these sets lies in another or in its complement.  A cell is given by its
name (cFP, cT j, cStack j, …) or is an integer that the context bounds.  The names and the sets are
replaced by their definitions; what remains are inequalities between integers, which follow from
those of the context, such as 1 ≤ q. -/
macro "cells" : tactic =>
  `(tactic| (simp only [Set.subset_def, Set.mem_compl_iff, Constants, Scratch, Writable, MainFrame,
               Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq,
               mem_temps_iff, mem_stack_iff, mem_pool_iff, cARG1, cARG2, cRESULT, cONE, cZERO, cNEG,
               cFP, cADDR, cRET, cRR, cNFP, cD, cT, cPool, cStack, mainFrame, ne_eq, true_or,
               or_true, false_or, or_false] <;>
             intros <;> omega))

/-- Reads a cell of a memory that is given by writes: it goes through the writes from the last to
the first, until it meets a write to the cell itself or no write is left. -/
macro "cell_read" : tactic =>
  `(tactic| repeat (first | rw [Function.update_self] | rw [Function.update_of_ne (by cells)]))

/-- Reads a cell of a memory that is given by writes to other cells of a memory in which, by h, the
cell holds the number in question. -/
macro "cell_read" " using " h:term : tactic => `(tactic| (cell_read; exact $h))

variable {W : ℕ} {Z : Sizes W} {F : ℕ}

/-- What an expression may change is scratch. -/
theorem temps_subset_scratch {k : ℕ} : Temps k F ⊆ Scratch F := by cells

/-- A statement may change scratch cells. -/
theorem scratch_subset_writable {q : ℕ} : Scratch Z.F ⊆ Writable Z q :=
  (Set.subset_union_left.trans Set.subset_union_left).trans Set.subset_union_left

/-- A statement may change the stack from its frame on. -/
theorem stack_subset_writable {q : ℕ} : Stack q Z.Q ⊆ Writable Z q :=
  Set.subset_union_right.trans Set.subset_union_left

/-- A statement in a later frame may change less. -/
theorem writable_subset_writable {q q' : ℕ} (h : q ≤ q') : Writable Z q' ⊆ Writable Z q :=
  Set.union_subset_union_left _ (Set.union_subset_union_right _ (by cells))

/-- A statement may change the memory cells within the limits. -/
theorem mem_writable_of_addr {q : ℕ} {a : ℤ} (h : Z.lim.Addr a) : a ∈ Writable Z q :=
  Set.mem_union_right _ h

/-! ## Addresses, and numbers that fit in a word -/

/-- The cell of the local variable x of the frame q, computed from FP and the pool. -/
theorem cStack_sub (q x : ℕ) : cStack q - ((2 * x : ℕ) : ℤ) = cStack (q + x) := by
  simp only [cStack]
  push_cast
  ring

/-- Back from the frame q + x to the frame q. -/
theorem cStack_add (q x : ℕ) : cStack (q + x) + ((2 * x : ℕ) : ℤ) = cStack q := by
  simp only [cStack]
  push_cast
  ring

/-- The stack cell before the cell q + 1. -/
theorem cStack_succ_add (q : ℕ) : cStack (q + 1) + ((2 : ℕ) : ℤ) = cStack q := cStack_add q 1

/-- The addresses of the stack fit in a word. -/
theorem Sizes.inRange_stack (Z : Sizes W) {j : ℕ} (hj : j ≤ Z.Q) : InRange W (cStack j) := by
  have hjQ : (j : ℤ) ≤ Z.Q := by exact_mod_cast hj
  constructor <;> simp only [cStack] <;> linarith [Z.fits.stack]

/-- The addresses of the memory fit in a word. -/
theorem Sizes.inRange_addr (Z : Sizes W) {a : ℤ} (h : Z.lim.Addr a) : InRange W a := by
  constructor <;> linarith [Z.fits.space, h.1, h.2]

/-- The number -1, on which every jump branches, fits in a word. -/
theorem Sizes.inRange_neg_one (Z : Sizes W) : InRange W (-1) := by
  have hN : (2 : ℤ) ≤ Z.disp := by
    exact_mod_cast (Nat.le_mul_of_pos_right 2 Z.F.succ_pos).trans Z.offsets_le
  constructor <;> linarith [Z.fits.pool_lt]

/-! ## The relation between a state of the light language and a memory of the machine -/

/-- The memory m of the machine represents the state σ of a procedure whose frame is at q. -/
structure Rel (Z : Sizes W) (σ : State) (q : ℕ) (m : ℤ → BitVec W) : Prop where
  one : m cONE = wd W 1
  zero : m cZERO = wd W 0
  neg : m cNEG = wd W (-1)
  pool : ∀ n ≤ Z.disp, m (cPool n) = wd W n
  fp : m cFP = wd W (cStack q)
  loc : ∀ x < Z.F, m (cStack (q + x)) = wd W (σ.loc x)
  mem : ∀ a < Z.lim.space, m (a : ℤ) = wd W (σ.mem a)

section Rel

variable {σ σ' : State} {q q' : ℕ} {m m' : ℤ → BitVec W}

/-- After a change that spares the numbers 1, 0, -1 and the pool, the new memory represents a state
as soon as FP, the local variables and the memory cells are right. -/
theorem Rel.of_agreeOutside {s : Set ℤ} (R : Rel Z σ q m) (A : AgreeOutside s m m')
    (hs : s ⊆ (Constants Z.disp)ᶜ) (hfp : m' cFP = wd W (cStack q'))
    (hloc : ∀ x < Z.F, m' (cStack (q' + x)) = wd W (σ'.loc x))
    (hmem : ∀ a < Z.lim.space, m' (a : ℤ) = wd W (σ'.mem a)) : Rel Z σ' q' m' := by
  have keep {a : ℤ} (ha : a ∈ Constants Z.disp) : m' a = m a := A.cell fun h => hs h ha
  exact {
    one := (keep (by cells)).trans R.one
    zero := (keep (by cells)).trans R.zero
    neg := (keep (by cells)).trans R.neg
    pool := fun n hn => (keep (by cells)).trans (R.pool n hn)
    fp := hfp
    loc := hloc
    mem := hmem }

/-- A memory that differs only in scratch cells represents the same state. -/
theorem Rel.same (R : Rel Z σ q m) (A : AgreeOutside (Scratch Z.F) m m') : Rel Z σ q m' :=
  R.of_agreeOutside A (by cells) (A.read (by cells) R.fp)
    (fun x hx => A.read (by cells) (R.loc x hx)) fun a ha => A.read (by cells) (R.mem a ha)

/-- A memory that differs only in scratch cells and in the stack beyond the frame represents the
same state.  (Here and below 1 ≤ q is needed because stack cell 0 is memory cell 0.) -/
theorem Rel.beyond (R : Rel Z σ q m) (hq : 1 ≤ q)
    (A : AgreeOutside (Scratch Z.F ∪ Stack (q + Z.F) Z.Q) m m') : Rel Z σ q m' :=
  R.of_agreeOutside A (by cells) (A.read (by cells) R.fp)
    (fun x hx => A.read (by cells) (R.loc x hx)) fun a ha => A.read (by cells) (R.mem a ha)

/-- Writing a local variable. -/
private theorem Rel.setLoc (R : Rel Z σ q m) (hq : 1 ≤ q) (x : ℕ) (v : ℤ) :
    Rel Z { σ with loc := Function.update σ.loc x v } q
      (Function.update m (cStack (q + x)) (wd W v)) := by
  refine R.of_agreeOutside ((AgreeOutside.refl {cStack (q + x)} m).update rfl _) (by cells)
    (by cell_read using R.fp) (fun y hy => ?_) fun a ha => by cell_read using R.mem a ha
  obtain rfl | hxy := eq_or_ne y x
  · simp
  · rw [Function.update_of_ne (by cells)]
    exact (R.loc y hy).trans (by simp [hxy])

/-- Writing a memory cell. -/
theorem Rel.setMem (R : Rel Z σ q m) (hq : 1 ≤ q) {a : ℤ} (ha : Z.lim.Addr a) (v : ℤ) :
    Rel Z { σ with mem := Function.update σ.mem a.toNat v } q (Function.update m a (wd W v)) := by
  -- the address is not negative, so it is no register and no stack cell of the frame
  have hnonneg : 0 ≤ a := ha.1
  refine R.of_agreeOutside ((AgreeOutside.refl {a} m).update rfl _) (by cells)
    (by cell_read using R.fp) (fun x hx => by cell_read using R.loc x hx) fun b hb => ?_
  obtain rfl | hab := eq_or_ne b a.toNat
  · simp [Int.toNat_of_nonneg hnonneg]
  · rw [Function.update_of_ne (by omega)]
    exact (R.mem b hb).trans (by simp [hab])

/-- Reading a memory cell. -/
theorem Rel.read (R : Rel Z σ q m) {a : ℤ} (ha : Z.lim.Addr a) : m a = wd W (σ.mem a.toNat) := by
  have := R.mem a.toNat (by have := ha.1; have := ha.2; omega)
  rwa [Int.toNat_of_nonneg ha.1] at this

/-- The cell to which FP points is local variable 0. -/
theorem Rel.loc_zero (R : Rel Z σ q m) (hF : 0 < Z.F) : m (cStack q) = wd W (σ.loc 0) :=
  R.loc 0 hF

end Rel

/-- The memory m represents the state σ in the frame q, and the frame lies within the stack: after
stack cell 0 and before stack cell Q. -/
structure Framed (Z : Sizes W) (σ : State) (q : ℕ) (m : ℤ → BitVec W) : Prop where
  rel : Rel Z σ q m
  low : 1 ≤ q
  high : q + Z.F ≤ Z.Q

/-! ## Two pieces of code that occur everywhere -/

section code

variable {σ : State} {q pos : ℕ} {m m' : ℤ → BitVec W} {code rest : List Instr}

/-- A memory that differs only in scratch cells represents the same state in the same frame. -/
theorem Framed.same (I : Framed Z σ q m) (A : AgreeOutside (Scratch Z.F) m m') : Framed Z σ q m' :=
  ⟨I.rel.same A, I.low, I.high⟩

/-- An unconditional jump. -/
theorem steps_jump {l : ℕ} (hcode : CodeAt code pos (.bltz cNEG l :: rest))
    (hneg : m cNEG = wd W (-1)) (hr : InRange W (-1)) : Steps code 1 ⟨pos, m⟩ ⟨l, m⟩ := by
  simpa using steps_bltz hcode hneg hr

/-- The two instructions that put the content v of the cell c into the local variable x. -/
theorem steps_setVar {x : ℕ} {c v : ℤ} (I : Framed Z σ q m) (hx : x < Z.F)
    (hcode : CodeAt code pos (.sub cADDR cFP (cPool (2 * x)) :: .store cADDR c :: rest))
    (hc : m c = wd W v) (hne : c ≠ cADDR) :
    ∃ m', Steps code 2 ⟨pos, m⟩ ⟨pos + 2, m'⟩ ∧
      Rel Z { σ with loc := Function.update σ.loc x v } q m' ∧
      AgreeOutside (Writable Z q) m m' := by
  have hN := Z.offsets_le
  have hQ := I.high
  -- ADDR := FP - 2 x
  have run₁ := steps_sub (i := cADDR) hcode I.rel.fp (I.rel.pool (2 * x) (by omega))
  rw [cStack_sub] at run₁
  have A₁ := (AgreeOutside.refl (Scratch Z.F) m).update (a := cADDR) (by cells)
    (wd W (cStack (q + x)))
  -- the cell at ADDR := c
  have run₂ := run₁.trans (steps_store hcode.tail (Function.update_self _ _ _)
    (Z.inRange_stack (by omega)))
  rw [Function.update_of_ne hne, hc] at run₂
  exact ⟨_, run₂, (I.rel.same A₁).setLoc I.low x v,
    (A₁.mono scratch_subset_writable).update (by cells) _⟩

end code

end Light.Compiler
