/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Poly.Comb
public import ToTuring.Poly.Range
public import ToTuring.Lib.Table
public import StepMachines.Prog.CutProg

/-! Every step of the procedure of one rectangle is polynomial-time (`IsPolyT`): every plain
function
in one of its steps is polynomial-time, and the procedure is built from these functions by
combinators that keep `IsPolyT`. -/

@[expose] public section

namespace Groundwork.Prog

open Stepped
open Groundwork.Grid (sideCnt topTerm botTerm)

variable {α : Type} [Enc α]

/-! ### The tables of one bit: functions on finite types -/

@[fun_prop] theorem top_polyT (c : BitCut) {h : α → Bell} {p q : α → Bool} (hh : PolyT h) (hp : PolyT p) (hq : PolyT q) :
    PolyT fun x => c.top (h x) (p x) (q x) :=
  PolyT.table₃ c.top hh hp hq

@[fun_prop] theorem bot0_polyT (c : BitCut) {h : α → Bell} {p q : α → Bool} (hh : PolyT h) (hp : PolyT p) (hq : PolyT q) :
    PolyT fun x => c.bot0 (h x) (p x) (q x) :=
  PolyT.table₃ c.bot0 hh hp hq

@[fun_prop] theorem bot1_polyT (c : BitCut) {h : α → Bell} {p q : α → Bool} (hh : PolyT h) (hp : PolyT p) (hq : PolyT q) :
    PolyT fun x => c.bot1 (h x) (p x) (q x) :=
  PolyT.table₃ c.bot1 hh hp hq

/-! ### Names of strings of values of type `Bell` -/

@[fun_prop] theorem oth_polyT {s₀ : α → Bell} {d : α → ℕ} (hs : PolyT s₀) (hd : PolyT d) :
    PolyT fun x => oth (s₀ x) (d x) := by
  unfold oth; fun_prop

@[fun_prop] theorem symAt_polyT {s₀ : α → Bell} {n k : α → ℕ} {w : α → List Bool} (hs : PolyT s₀) (hn : PolyT n)
    (hw : PolyT w) (hk : PolyT k) : PolyT fun x => symAt (s₀ x) (n x) (w x) (k x) := by
  unfold symAt; fun_prop

@[fun_prop] theorem validW_polyT {n c : α → ℕ} {w : α → List Bool} (hn : PolyT n) (hc : PolyT c) (hw : PolyT w) :
    PolyT fun x => validW (n x) (c x) (w x) := by
  unfold validW; fun_prop

@[fun_prop] theorem sideCnt_polyT (tr : Bool) {n i : α → ℕ} (hn : PolyT n) (hi : PolyT i) :
    PolyT fun x => sideCnt tr (n x) (i x) := by
  unfold sideCnt; fun_prop

/-- The word of a number, as long as a given word. -/
@[fun_prop] theorem toWordL_polyT {w : α → List Bool} {y : α → ℕ} (hw : PolyT w) (hy : PolyT y) :
    PolyT fun x => toWord (w x).length (y x) :=
  PolyT.toWord' (Unary.of_length hw) hy

/-! ### One rectangle -/

@[fun_prop] theorem topTerm_polyT (tr : Bool) {x y w : α → List Bool} {k : α → ℕ} (hx : PolyT x) (hy : PolyT y)
    (hw : PolyT w) (hk : PolyT k) : PolyT fun a => topTerm tr (x a) (y a) (w a) (k a) := by
  unfold topTerm; fun_prop

@[fun_prop] theorem botTerm_polyT (tr : Bool) {x y w : α → List Bool} {s k : α → ℕ} (hx : PolyT x) (hy : PolyT y)
    (hw : PolyT w) (hs : PolyT s) (hk : PolyT k) : PolyT fun a => botTerm tr (x a) (y a) (w a) (s a) (k a) := by
  unfold botTerm; fun_prop

theorem cutLen_polyT : PolyT cutLen := by unfold cutLen; fun_prop

theorem cutValid_polyT (tr : Bool) : PolyT (cutValid tr) := by unfold cutValid; fun_prop

theorem cutTop_polyT : PolyT cutTop := by unfold cutTop; fun_prop

theorem topE_polyT (tr : Bool) : PolyT (topE tr) := by unfold topE; fun_prop

theorem cutPow_polyT : PolyT cutPow := PolyT.two_pow (e := fun q : CutQ => q.2.1.length) (Unary.of_length (by fun_prop))

theorem cutPop_polyT : PolyT cutPop := by unfold cutPop; fun_prop

theorem cutLen'_polyT : PolyT cutLen' := by unfold cutLen'; fun_prop

theorem botE_polyT (tr : Bool) : PolyT (botE tr) := by unfold botE; fun_prop

/-- Every step of the procedure of one rectangle is polynomial-time. -/
@[instance_reducible] def IsPolyT.cutP (tr : Bool) : IsPolyT (cutP tr) :=
  haveI := IsPolyT.ofFun (topE_polyT tr)
  haveI := IsPolyT.prodRange (M := ofFun (topE tr)) cutLen_polyT
  haveI := IsPolyT.ofFun (botE_polyT tr)
  haveI := IsPolyT.prodRange (M := ofFun (botE tr)) cutLen'_polyT
  haveI : IsPolyT (Stepped.const 0 : Stepped (CutQ × ℕ) ℤ) := IsPolyT.const 0
  haveI := IsPolyT.ite (M := prodRange cutLen' (ofFun (botE tr))) (N := Stepped.const 0) cutPop_polyT
  haveI := IsPolyT.sumRange (M := Stepped.ite cutPop (prodRange cutLen' (ofFun (botE tr))) (Stepped.const 0)) cutPow_polyT
  haveI := IsPolyT.ite (M := prodRange cutLen (ofFun (topE tr)))
    (N := sumRange cutPow (Stepped.ite cutPop (prodRange cutLen' (ofFun (botE tr))) (Stepped.const 0))) cutTop_polyT
  haveI : IsPolyT (Stepped.const 0 : Stepped CutQ ℤ) := IsPolyT.const 0
  IsPolyT.ite (cutValid_polyT tr)

end Groundwork.Prog
