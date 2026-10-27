/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Lib.Nat2

/-! Polynomial time: integers, as a sign and an absolute value. The word of an integer is the word
of the pair
(negative?, absolute value), so every operation on integers is an operation on such pairs. -/

@[expose] public section

namespace Groundwork.PolyT

variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

/-- Is the integer negative? -/
def sgn (z : ℤ) : Bool := decide (z < 0)

/-- The integer with the given sign (true: negative) and absolute value. -/
def mkZ (s : Bool) (n : ℕ) : ℤ := bif s then -(n : ℤ) else (n : ℤ)

/-- The sign of `mkZ s n`: zero is not negative. -/
theorem sgn_mkZ (s : Bool) (n : ℕ) : sgn (mkZ s n) = (s && decide (n ≠ 0)) := by
  cases s
  · have h : ¬ (mkZ false n < 0) := by
      simp only [mkZ, cond_false]
      omega
    simp only [sgn, h, decide_false, Bool.false_and]
  · by_cases h : n = 0
    · subst h
      have h' : ¬ (mkZ true 0 < 0) := by
        simp only [mkZ, cond_true]
        omega
      simp only [sgn, h', decide_false, Bool.true_and, ne_eq, not_true_eq_false]
    · have h' : mkZ true n < 0 := by
        simp only [mkZ, cond_true]
        omega
      simp only [sgn, h', decide_true, Bool.true_and, ne_eq, h, not_false_eq_true]

/-- The absolute value of `mkZ s n`. -/
theorem natAbs_mkZ (s : Bool) (n : ℕ) : (mkZ s n).natAbs = n := by
  cases s <;> simp [mkZ]

/-- An integer as the pair of its sign and its absolute value. -/
theorem rep {f : α → ℤ} (hf : PolyT f) : PolyT (fun x => (sgn (f x), (f x).natAbs)) :=
  of_wd hf id (fun _ => rfl) fun _ => rfl

/-- The sign of an integer in polynomial time. -/
@[fun_prop] theorem sgn' {f : α → ℤ} (hf : PolyT f) : PolyT (fun x => sgn (f x)) :=
  (rep hf).fst

/-- The absolute value of an integer in polynomial time. -/
@[fun_prop] theorem natAbs {f : α → ℤ} (hf : PolyT f) :
    PolyT (fun x => (f x).natAbs) :=
  (rep hf).snd

/-- An integer from its sign and absolute value in polynomial time. -/
@[fun_prop] theorem mkZ' {s : α → Bool} {n : α → ℕ} (hs : PolyT s) (hn : PolyT n) :
    PolyT (fun x => mkZ (s x) (n x)) := by
  have h : PolyT (fun x => (s x && decide (n x ≠ 0), n x)) := by fun_prop
  refine of_wd h id (fun _ => rfl) fun x => ?_
  rw [wd_int]
  change wd (sgn (mkZ (s x) (n x)), (mkZ (s x) (n x)).natAbs) = _
  rw [sgn_mkZ, natAbs_mkZ]
  rfl

/-- A natural number as an integer in polynomial time. -/
@[fun_prop] theorem natCast {f : α → ℕ} (hf : PolyT f) :
    PolyT (fun x => (f x : ℤ)) :=
  (mkZ' (const false) hf).congr fun _ => rfl

/-- `Int.toNat` (a negative integer goes to 0) in polynomial time. -/
@[fun_prop] theorem toNat {f : α → ℤ} (hf : PolyT f) :
    PolyT (fun x => (f x).toNat) := by
  have h : PolyT (fun x => bif sgn (f x) then 0 else (f x).natAbs) := by fun_prop
  refine h.congr fun x => ?_
  by_cases h0 : f x < 0 <;> simp only [sgn, h0, decide_true, decide_false, cond_true, cond_false] <;> omega

/-- The negation of an integer in polynomial time. -/
@[fun_prop] theorem negZ {f : α → ℤ} (hf : PolyT f) :
    PolyT (fun x => - f x) := by
  have h : PolyT (fun x => mkZ (!sgn (f x)) (f x).natAbs) := by fun_prop
  refine h.congr fun x => ?_
  by_cases h0 : f x < 0 <;>
    simp only [sgn, mkZ, h0, decide_true, decide_false, Bool.not_true, Bool.not_false, cond_true, cond_false] <;> omega

/-- The sum of two integers from their signs and absolute values. -/
theorem add_eq (z w : ℤ) :
    (bif sgn z ^^ sgn w then
      (bif decide (w.natAbs ≤ z.natAbs) then mkZ (sgn z) (z.natAbs - w.natAbs) else mkZ (sgn w) (w.natAbs - z.natAbs))
    else mkZ (sgn z) (z.natAbs + w.natAbs)) = z + w := by
  by_cases h0 : z < 0 <;> by_cases h1 : w < 0 <;> by_cases h2 : w.natAbs ≤ z.natAbs <;>
    simp only [sgn, mkZ, h0, h1, h2, decide_true, decide_false, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false,
      cond_true, cond_false] <;> omega

/-- The sum of two integers in polynomial time. -/
@[fun_prop] theorem addZ {f g : α → ℤ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x + g x) := by
  have h : PolyT (fun x => bif sgn (f x) ^^ sgn (g x) then
      (bif decide ((g x).natAbs ≤ (f x).natAbs) then mkZ (sgn (f x)) ((f x).natAbs - (g x).natAbs)
        else mkZ (sgn (g x)) ((g x).natAbs - (f x).natAbs))
      else mkZ (sgn (f x)) ((f x).natAbs + (g x).natAbs)) := by fun_prop
  exact h.congr fun x => add_eq _ _

/-- The difference of two integers in polynomial time. -/
@[fun_prop] theorem subZ {f g : α → ℤ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x - g x) :=
  (addZ hf (negZ hg)).congr fun x => (sub_eq_add_neg (f x) (g x)).symm

/-- The product of two integers from their signs and absolute values. -/
theorem mul_eq (z w : ℤ) : mkZ (sgn z ^^ sgn w) (z.natAbs * w.natAbs) = z * w := by
  by_cases h0 : z < 0 <;> by_cases h1 : w < 0 <;>
    simp only [sgn, mkZ, h0, h1, decide_true, decide_false, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false,
      cond_true, cond_false, Nat.cast_mul]
  · rw [show (z.natAbs : ℤ) = -z by omega, show (w.natAbs : ℤ) = -w by omega]
    ring
  · rw [show (z.natAbs : ℤ) = -z by omega, show (w.natAbs : ℤ) = w by omega]
    ring
  · rw [show (z.natAbs : ℤ) = z by omega, show (w.natAbs : ℤ) = -w by omega]
    ring
  · rw [show (z.natAbs : ℤ) = z by omega, show (w.natAbs : ℤ) = w by omega]

/-- The product of two integers in polynomial time. -/
@[fun_prop] theorem mulZ {f g : α → ℤ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x * g x) := by
  have h : PolyT (fun x => mkZ (sgn (f x) ^^ sgn (g x)) ((f x).natAbs * (g x).natAbs)) := by fun_prop
  exact h.congr fun x => mul_eq _ _

/-- The test `<` on integers in polynomial time: the sign of the difference. -/
@[fun_prop] theorem decide_ltZ {f g : α → ℤ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => decide (f x < g x)) :=
  (sgn' (subZ hf hg)).congr fun x => by
    simp only [sgn, decide_eq_decide]
    omega

/-- The test `≤` on integers in polynomial time: the sign of the difference. -/
@[fun_prop] theorem decide_leZ {f g : α → ℤ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => decide (f x ≤ g x)) :=
  (not' (sgn' (subZ hg hf))).congr fun x => by
    by_cases h : f x ≤ g x
    · have h' : ¬ (g x - f x < 0) := by omega
      simp [sgn, h, h']
    · have h' : g x - f x < 0 := by omega
      simp [sgn, h, h']

/-- The test of equality on integers in polynomial time: compare signs and absolute values. -/
instance : EqT ℤ := ⟨by
  have h : PolyT (fun p : ℤ × ℤ => decide ((sgn p.1, p.1.natAbs) = (sgn p.2, p.2.natAbs))) := by fun_prop
  refine h.congr fun p => ?_
  simp only [sgn, Prod.mk.injEq, decide_eq_decide]
  omega⟩

end Groundwork.PolyT
