/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Compiler.Cells

/-!
# The compiler is correct on expressions

The code of an expression e, compiled for the temporary T_k, only changes the memory
(`straight_compileExpr`).  Run in a memory that represents the state σ, it leaves the value of e in
T_k and changes nothing but ADDR and the temporaries from T_k on.  That is `effects_compileExpr`,
for an expression that needs no more temporaries than there are from T_k on, and
`effects_compileExpr_of_width`, the form that the other files use, for an expression of width at
most F.

The proof is an induction on e; in each case the instructions are run one after the other.  A
constant is built from its binary digits (`effects_digitsCode`).  For an operation, the value of the
left side waits in T_k while the right side is evaluated into T_{k+1}, which does not touch T_k.
-/

public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

variable {W : ℕ} {F : ℕ}

/-- Every expression uses at least one temporary. -/
private theorem _root_.Light.Expr.height_pos (e : Expr) : 0 < e.height := by
  induction e with
  | const n => simp [Expr.height]
  | var x => simp [Expr.height]
  | op o a b iha _ => exact lt_of_lt_of_le iha (le_max_left _ _)
  | load a ih => exact ih

/-- The temporary that receives the value of an expression is one of those that its code may
change. -/
private theorem cT_mem_temps_of_height (e : Expr) {k : ℕ} (hT : k + e.height ≤ 2 * F + 1) :
    cT k ∈ Temps k F := by
  have := e.height_pos
  cells

/-! ## Constants -/

private theorem straight_digitsCode (c : ℤ) : ∀ L : List ℕ, ∀ i ∈ digitsCode c L, Straight i
  | [] => by simp [digitsCode, Straight]
  | d :: L => by
    have := straight_digitsCode c L
    by_cases hd : d = 0 <;> simpa [digitsCode, hd, Straight, or_imp, forall_and] using this

/-- The code for a constant: the cell c receives the number with the given binary digits, and
nothing else changes. -/
private theorem effects_digitsCode {c : ℤ} (hc : cONE ≠ c) (L : List ℕ) (hL : ∀ d ∈ L, d < 2)
    (m : ℤ → BitVec W) (hone : m cONE = wd W 1) :
    effects (digitsCode c L) m c = wd W (Nat.ofDigits 2 L : ℕ) ∧
      AgreeOutside {c} m (effects (digitsCode c L) m) := by
  induction L with
  | nil =>
    -- c := c - c
    rw [digitsCode, effects_cons, effects_nil,
      effect_sub c (wd_toInt (m c)).symm (wd_toInt (m c)).symm, sub_self]
    exact ⟨by simp, (AgreeOutside.refl _ m).update (Set.mem_singleton c) _⟩
  | cons d L ih =>
    obtain ⟨val, A⟩ := ih fun x hx => hL x (by simp [hx])
    -- c := c + c
    rw [digitsCode, effects_append, effects_append, effects_cons, effects_nil, effect_add c val val]
    have hd : d = 0 ∨ d = 1 := by have := hL d (by simp); omega
    obtain rfl | rfl := hd
    · refine ⟨?_, A.update (Set.mem_singleton c) _⟩
      rw [if_pos rfl, effects_nil, Function.update_self, Nat.ofDigits_cons]
      congr 1
      push_cast
      ring
    · -- c := c + 1
      rw [if_neg one_ne_zero, effects_cons, effects_nil, effect_add c (Function.update_self _ _ _)
        ((Function.update_of_ne hc _ _).trans (A.read hc hone))]
      refine ⟨?_, (A.update (Set.mem_singleton c) _).update (Set.mem_singleton c) _⟩
      rw [Function.update_self, Nat.ofDigits_cons]
      congr 1
      push_cast
      ring

/-! ## Expressions -/

private theorem straight_instr (o : Op) (i j k : ℤ) : Straight (o.instr i j k) := by
  cases o <;> trivial

/-- The code of an expression only changes the memory. -/
theorem straight_compileExpr : ∀ (e : Expr) (k : ℕ), ∀ i ∈ compileExpr e k, Straight i
  | .const _, _ => straight_digitsCode _ _
  | .var _, _ => by simp [compileExpr, Straight]
  | .op o a b, k => List.forall_mem_append.2 ⟨List.forall_mem_append.2
      ⟨straight_compileExpr a k, straight_compileExpr b (k + 1)⟩, by simp [straight_instr]⟩
  | .load a, k => List.forall_mem_append.2 ⟨straight_compileExpr a k, by simp [Straight]⟩

/-- The instruction of an operation, on cells that hold known numbers. -/
private theorem effect_instr (o : Op) {m : ℤ → BitVec W} {j k a b : ℤ} (i : ℤ) (hj : m j = wd W a)
    (hk : m k = wd W b) : effect (o.instr i j k) m = Function.update m i (wd W (o.eval a b)) := by
  cases o
  exacts [effect_add i hj hk, effect_sub i hj hk, effect_mul i hj hk]

variable {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}

/-- The code of an expression leaves its value in T_k and changes nothing but ADDR and the
temporaries from T_k on. -/
private theorem effects_compileExpr (I : Framed Z σ q m) (e : Expr) (k : ℕ) (hvars : e.vars ≤ Z.F)
    (hs : e.Safe Z.lim σ) (hT : k + e.height ≤ 2 * Z.F + 1) :
    effects (compileExpr e k) m (cT k) = wd W (e.val σ) ∧
      AgreeOutside (Temps k Z.F) m (effects (compileExpr e k) m) := by
  induction e generalizing k m with
  | const n =>
    have hk := cT_mem_temps_of_height _ hT
    obtain ⟨val, A⟩ := effects_digitsCode (c := cT k) (by cells) (Nat.digits 2 n)
      (fun d hd => Nat.digits_lt_base (by norm_num) hd) m I.rel.one
    rw [Nat.ofDigits_digits] at val
    exact ⟨val, A.mono (Set.singleton_subset_iff.2 hk)⟩
  | var x =>
    have hk := cT_mem_temps_of_height _ hT
    have hx : x < Z.F := hvars
    have hN := Z.offsets_le
    have hQ := I.high
    -- ADDR := FP - 2 x; T_k := the cell at ADDR
    rw [compileExpr, effects_cons, effects_cons, effects_nil,
      effect_sub cADDR I.rel.fp (I.rel.pool (2 * x) (by omega)), cStack_sub,
      effect_load (cT k) (Function.update_self _ _ _) (Z.inRange_stack (by omega))]
    refine ⟨?_, ((AgreeOutside.refl _ m).update (by cells) _).update hk _⟩
    rw [Function.update_self, Function.update_of_ne (by cells), I.rel.loc x hx, Expr.val]
  | op o a b iha ihb =>
    have hk := cT_mem_temps_of_height _ hT
    have hha : a.height ≤ (Expr.op o a b).height := le_max_left _ _
    have hhb : b.height + 1 ≤ (Expr.op o a b).height := le_max_right _ _
    obtain ⟨hwa, hwb⟩ := Expr.vars_op_le_iff.1 hvars
    obtain ⟨hsa, hsb, -⟩ := hs
    obtain ⟨va, Aa⟩ := iha I k hwa hsa (by omega)
    obtain ⟨vb, Ab⟩ := ihb (I.same (Aa.mono temps_subset_scratch)) (k + 1) hwb hsb (by omega)
    -- T_k := T_k o T_{k+1}
    rw [compileExpr, effects_append, effects_append, effects_cons, effects_nil,
      effect_instr o (cT k) (Ab.read (by cells) va) vb]
    exact ⟨Function.update_self _ _ _,
      (Aa.trans (Ab.mono (by cells))).update hk _⟩
  | load a ih =>
    have hk := cT_mem_temps_of_height _ hT
    obtain ⟨hsa, haddr⟩ := hs
    obtain ⟨va, Aa⟩ := ih I k hvars hsa hT
    -- the address is not negative, so it is neither ADDR nor a temporary
    have hnonneg : 0 ≤ a.val σ := haddr.1
    -- T_k := the cell at T_k
    rw [compileExpr, effects_append, effects_cons, effects_nil,
      effect_load (cT k) va (Z.inRange_addr haddr), Aa.cell (by cells), I.rel.read haddr]
    exact ⟨Function.update_self _ _ _, Aa.update hk _⟩

/-- The code of an expression of width at most F, when there are F temporaries from T_k on, leaves
its value in T_k and changes nothing but ADDR and the temporaries from T_k on. -/
theorem effects_compileExpr_of_width (I : Framed Z σ q m) (e : Expr) (k : ℕ) (hw : e.width ≤ Z.F)
    (hs : e.Safe Z.lim σ) (hk : k ≤ Z.F + 1) :
    effects (compileExpr e k) m (cT k) = wd W (e.val σ) ∧
      AgreeOutside (Temps k Z.F) m (effects (compileExpr e k) m) :=
  effects_compileExpr I e k (Expr.width_le_iff.1 hw).1 hs
    (by have := (Expr.width_le_iff.1 hw).2; omega)

end Light.Compiler
