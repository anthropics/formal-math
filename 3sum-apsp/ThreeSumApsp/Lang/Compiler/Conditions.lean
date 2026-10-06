/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Compiler.Expressions
public import ThreeSumApsp.Lang.RunsStayInLimits

/-!
# The compiler is correct on tests

The code of a test goes on to the next position if the test holds and jumps to a given position if
it does not, in at most as many steps as it has instructions, and it changes scratch cells only.
This behaviour is called `Decides`, and `decides_compileCond` proves it.

Both tests first evaluate a into T₀ and b into T₁ (`steps_pair`, which also serves the statement
that stores into the memory).  For a < b the code forms D = b - a - 1 and leaves if D < 0
(`decides_lt`).  For a = b it forms D = a - b and leaves if D < 0, then forms -D and leaves if that
is negative (`decides_eq`).  No difference overflows, because words hold twice the largest value and
one more (`inRange_sub`).
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

open EndStatement (Instr)

variable {W : ℕ} {Z : Sizes W} {code rest : List Instr} {σ : State} {q pos l : ℕ}
  {m : ℤ → BitVec W} {a b : Expr}

/-! ## Two expressions -/

/-- What follows the code of two expressions. -/
theorem codeAt_after_pair (hcode : CodeAt code pos (compileExpr a 0 ++ compileExpr b 1 ++ rest)) :
    CodeAt code (pos + (a.size + b.size)) rest :=
  hcode.right.cast_pos (by rw [List.length_append, length_compileExpr, length_compileExpr])

/-- The code of two expressions, one after the other, leaves their values in T₀ and T₁ and changes
scratch cells only. -/
theorem steps_pair (I : Framed Z σ q m)
    (hcode : CodeAt code pos (compileExpr a 0 ++ compileExpr b 1 ++ rest)) (hwa : a.width ≤ Z.F)
    (hwb : b.width ≤ Z.F) (hsa : a.Safe Z.lim σ) (hsb : b.Safe Z.lim σ) :
    ∃ m', Steps code (a.size + b.size) ⟨pos, m⟩ ⟨pos + (a.size + b.size), m'⟩ ∧
      m' (cT 0) = wd W (a.val σ) ∧ m' (cT 1) = wd W (b.val σ) ∧
      AgreeOutside (Scratch Z.F) m m' := by
  obtain ⟨va, Aa⟩ := effects_compileExpr_of_width I a 0 hwa hsa (by omega)
  have Aa' := Aa.mono temps_subset_scratch
  obtain ⟨vb, Ab⟩ := effects_compileExpr_of_width (I.same Aa') b 1 hwb hsb (by omega)
  have run := steps_straight _ pos m hcode.left
    (List.forall_mem_append.2 ⟨straight_compileExpr a 0, straight_compileExpr b 1⟩)
  rw [List.length_append, length_compileExpr, length_compileExpr, effects_append] at run
  exact ⟨_, run, Ab.read (by cells) va, vb, Aa'.trans (Ab.mono temps_subset_scratch)⟩

/-! ## Tests -/

/-- What the code of a test does, if it has size instructions, begins at pos, and tests p: in at
most size steps the machine reaches the position after the code if p holds, and the position l if
not.  Only scratch cells change. -/
def Decides (code : List Instr) (F pos size l : ℕ) (m : ℤ → BitVec W) (p : Prop) : Prop :=
  ∃ (m' : ℤ → BitVec W) (n : ℕ), n ≤ size ∧ AgreeOutside (Scratch F) m m' ∧
    (p → Steps code n ⟨pos, m⟩ ⟨pos + size, m'⟩) ∧ (¬ p → Steps code n ⟨pos, m⟩ ⟨l, m'⟩)

/-- The test holds. -/
theorem Decides.of_holds {F size : ℕ} {p : Prop} (h : Decides code F pos size l m p) (hp : p) :
    ∃ (m' : ℤ → BitVec W) (n : ℕ), n ≤ size ∧ AgreeOutside (Scratch F) m m' ∧
      Steps code n ⟨pos, m⟩ ⟨pos + size, m'⟩ :=
  let ⟨m', n, le, A, run, _⟩ := h
  ⟨m', n, le, A, run hp⟩

/-- The test fails. -/
theorem Decides.of_fails {F size : ℕ} {p : Prop} (h : Decides code F pos size l m p) (hp : ¬ p) :
    ∃ (m' : ℤ → BitVec W) (n : ℕ), n ≤ size ∧ AgreeOutside (Scratch F) m m' ∧
      Steps code n ⟨pos, m⟩ ⟨l, m'⟩ :=
  let ⟨m', n, le, A, _, run⟩ := h
  ⟨m', n, le, A, run hp⟩

/-- No overflow: the difference of two values fits in a word, and so does one less. -/
private theorem inRange_sub (Z : Sizes W) {x y : ℤ} (hx : |x| ≤ Z.lim.word)
    (hy : |y| ≤ Z.lim.word) : InRange W (x - y) ∧ InRange W (x - y - 1) := by
  obtain ⟨⟨hx₁, hx₂⟩, hy₁, hy₂⟩ := And.intro (abs_le.1 hx) (abs_le.1 hy)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [Z.fits.word]

/-- The test a < b. -/
private theorem decides_lt (I : Framed Z σ q m) (hσ : σ.Bounded Z.lim)
    (hcode : CodeAt code pos (compileCond (.lt a b) l)) (hw : (Cond.lt a b).width ≤ Z.F)
    (hs : (Cond.lt a b).Safe Z.lim σ) :
    Decides code Z.F pos (Cond.lt a b).size l m (a.val σ < b.val σ) := by
  obtain ⟨hwa, hwb⟩ := Cond.width_lt_le_iff.1 hw
  obtain ⟨hsa, hsb⟩ := hs
  obtain ⟨m₁, run₁, va, vb, A₁⟩ := steps_pair I hcode hwa hwb hsa hsb
  have restCode := codeAt_after_pair hcode
  -- D := b - a
  have run₂ := run₁.trans (steps_sub restCode vb va)
  -- D := D - 1
  have run₃ := run₂.trans (steps_sub restCode.tail (Function.update_self _ _ _)
    (by cell_read using (I.rel.same A₁).one))
  -- leave if D < 0
  have run₄ := run₃.trans (steps_bltz restCode.tail.tail (Function.update_self _ _ _)
    (inRange_sub Z (Expr.abs_val_le hσ b hsb) (Expr.abs_val_le hσ a hsa)).2)
  exact ⟨_, _, by rw [Cond.size], (A₁.update (by cells) _).update (by cells) _,
    run₄.branch (by omega) (by rw [Cond.size]; omega)⟩

/-- The test a = b. -/
private theorem decides_eq (I : Framed Z σ q m) (hσ : σ.Bounded Z.lim)
    (hcode : CodeAt code pos (compileCond (.eq a b) l)) (hw : (Cond.eq a b).width ≤ Z.F)
    (hs : (Cond.eq a b).Safe Z.lim σ) :
    Decides code Z.F pos (Cond.eq a b).size l m (a.val σ = b.val σ) := by
  obtain ⟨hwa, hwb⟩ := Cond.width_eq_le_iff.1 hw
  obtain ⟨hsa, hsb⟩ := hs
  have ha := Expr.abs_val_le hσ a hsa
  have hb := Expr.abs_val_le hσ b hsb
  obtain ⟨m₁, run₁, va, vb, A₁⟩ := steps_pair I hcode hwa hwb hsa hsb
  have restCode := codeAt_after_pair hcode
  -- D := a - b
  have run₂ := run₁.trans (steps_sub restCode va vb)
  have A₂ := A₁.update (a := cD) (by cells) (wd W (a.val σ - b.val σ))
  -- leave if D < 0
  have run₃ := run₂.trans (steps_bltz restCode.tail (Function.update_self _ _ _)
    (inRange_sub Z ha hb).1)
  by_cases hlt : a.val σ - b.val σ < 0
  · rw [if_pos hlt] at run₃
    exact ⟨_, _, by rw [Cond.size]; omega, A₂, fun h => absurd h (by omega), fun _ => run₃⟩
  rw [if_neg hlt] at run₃
  -- D := 0 - D
  have run₄ := run₃.trans (steps_sub restCode.tail.tail
    (by cell_read using (I.rel.same A₁).zero)
    (Function.update_self _ _ _))
  rw [zero_sub, neg_sub] at run₄
  -- leave if D < 0
  have run₅ := run₄.trans (steps_bltz restCode.tail.tail.tail (Function.update_self _ _ _)
    (inRange_sub Z hb ha).1)
  exact ⟨_, _, by rw [Cond.size], A₂.update (by cells) _,
    run₅.branch (by omega) (by rw [Cond.size]; omega)⟩

/-- The code of a test decides the test. -/
theorem decides_compileCond (I : Framed Z σ q m) (hσ : σ.Bounded Z.lim) (c : Cond)
    (hcode : CodeAt code pos (compileCond c l)) (hw : c.width ≤ Z.F) (hs : c.Safe Z.lim σ) :
    Decides code Z.F pos c.size l m (c.Holds σ) := by
  cases c with
  | lt a b => exact decides_lt I hσ hcode hw hs
  | eq a b => exact decides_eq I hσ hcode hw hs

end Light.Compiler
