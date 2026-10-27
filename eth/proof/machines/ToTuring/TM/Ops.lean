/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.TM.Move

/-! The operations on the items on top of the main stack from which the fragments of Closure/ are
built, with bounds on their
numbers of steps: drop, duplicate, swap, make a pair, take a pair apart, push a constant,
park an item on stack a or b and fetch it back. The parking stacks are used above their contents and
left as they were. -/

@[expose] public section

namespace Groundwork.TM

open Turing

/-- Push the symbols of a word on the main stack, one after the other. -/
def pushSeq : List Sym → TM2.Stmt (fun _ : Stk => Sym) Empty (Option Sym)
  | [] => .halt
  | s :: w => .push .main (fun _ => s) (pushSeq w)

/-- Push a fixed word: afterwards it lies on top of the main stack, its first symbol on top. -/
def pushW (w : List Sym) : Fr := Frag.ofStmt (pushSeq w.reverse)

/-- Pop one symbol off the main stack and forget it. -/
def pop1 : Fr := Frag.ofStmt (.pop .main (fun _ _ => none) .halt)

/-- Drop the item on top. -/
def dropF : Fr := drp .main

/-- Duplicate the item on top. -/
def dupF : Fr := ((mv2 .main .a .b).seq (mv .a .main)).seq (mv .b .main)

/-- Exchange the two items on top. -/
def swapF : Fr := (((mv .main .a).seq (mv .main .b)).seq (mv .a .main)).seq (mv .b .main)

/-- The two items on top become one: their pair. -/
def consF : Fr :=
  (((((mv .main .a).seq (mv .main .b)).seq (pushW [.R])).seq (mv .b .main)).seq (mv .a .main)).seq (pushW [.L])

/-- A pair on top becomes its two items. -/
def unconsF : Fr :=
  (((((pop1).seq (mv .main .a)).seq (mv .main .b)).seq pop1).seq (mv .b .main)).seq (mv .a .main)

section
variable (x y : V) (M A B N : List Sym)

/-- What the pushing statement does: the word arrives reversed. -/
private theorem stepAux_pushSeq (w : List Sym) (v : Option Sym) :
    TM2.stepAux (pushSeq w) v (st M A B N) = ⟨none, v, st (w.reverse ++ M) A B N⟩ := by
  induction w generalizing M with
  | nil => rfl
  | cons s w ih => simp [pushSeq, TM2.stepAux, ih]

theorem pushW_within (w : List Sym) : (pushW w).Within (st M A B N) 1 (st (w ++ M) A B N) := by
  refine Frag.Within.of_runs (Frag.ofStmt_runs ?_)
  rw [stepAux_pushSeq, List.reverse_reverse]

theorem pop1_within (s : Sym) : pop1.Within (st (s :: M) A B N) 1 (st M A B N) := by
  refine Frag.Within.of_runs (Frag.ofStmt_runs ?_)
  simp [TM2.stepAux]

theorem dropF_within : dropF.Within (st (code x ++ M) A B N) ((code x).length + 1) (st M A B N) := by
  simpa [dropF] using Frag.Within.of_runs
    (drp_runs (i := .main) (by decide) x (S := st (code x ++ M) A B N) (W := M) rfl)

/-- Park the item on top of main on stack a (mirrored). -/
theorem toA_within : (mv .main .a).Within (st (code x ++ M) A B N) ((code x).length + 1)
    (st M (mirror (code x) ++ A) B N) := by
  simpa using Frag.Within.of_runs
    (mv_runs (i := .main) (j := .a) (by decide) (by decide) (by decide) x (S := st (code x ++ M) A B N) (W := M) rfl)

/-- Park the item on top of main on stack b (mirrored). -/
theorem toB_within : (mv .main .b).Within (st (code x ++ M) A B N) ((code x).length + 1)
    (st M A (mirror (code x) ++ B) N) := by
  simpa using Frag.Within.of_runs
    (mv_runs (i := .main) (j := .b) (by decide) (by decide) (by decide) x (S := st (code x ++ M) A B N) (W := M) rfl)

/-- Fetch an item back from stack a. -/
theorem fromA_within : (mv .a .main).Within (st M (mirror (code x) ++ A) B N) ((code x).length + 1)
    (st (code x ++ M) A B N) := by
  simpa using Frag.Within.of_runs
    (mv_runs' (i := .a) (j := .main) (by decide) (by decide) (by decide) x
      (S := st M (mirror (code x) ++ A) B N) (W := A) rfl)

/-- Fetch an item back from stack b. -/
theorem fromB_within : (mv .b .main).Within (st M A (mirror (code x) ++ B) N) ((code x).length + 1)
    (st (code x ++ M) A B N) := by
  simpa using Frag.Within.of_runs
    (mv_runs' (i := .b) (j := .main) (by decide) (by decide) (by decide) x
      (S := st M A (mirror (code x) ++ B) N) (W := B) rfl)

theorem dupF_within :
    dupF.Within (st (code x ++ M) A B N) (3 * (code x).length + 3) (st (code x ++ (code x ++ M)) A B N) := by
  have h1 : (mv2 .main .a .b).Within (st (code x ++ M) A B N) ((code x).length + 1)
      (st M (mirror (code x) ++ A) (mirror (code x) ++ B) N) := by
    simpa using Frag.Within.of_runs
      (mv2_runs (i := .main) (j := .a) (k := .b) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) x
        (S := st (code x ++ M) A B N) (W := M) rfl)
  have h2 := fromA_within x M A (mirror (code x) ++ B) N
  have h3 := fromB_within x (code x ++ M) A B N
  exact ((h1.seq h2).seq h3).mono (by omega)

theorem swapF_within : swapF.Within (st (code x ++ (code y ++ M)) A B N) (2 * ((code x).length + (code y).length) + 4)
    (st (code y ++ (code x ++ M)) A B N) := by
  have h1 := toA_within x (code y ++ M) A B N
  have h2 := toB_within y M (mirror (code x) ++ A) B N
  have h3 := fromA_within x M A (mirror (code y) ++ B) N
  have h4 := fromB_within y (code x ++ M) A B N
  exact (((h1.seq h2).seq h3).seq h4).mono (by omega)

theorem consF_within : consF.Within (st (code x ++ (code y ++ M)) A B N) (2 * ((code x).length + (code y).length) + 6)
    (st (code (.cons x y) ++ M) A B N) := by
  have h1 := toA_within x (code y ++ M) A B N
  have h2 := toB_within y M (mirror (code x) ++ A) B N
  have h3 := pushW_within M (mirror (code x) ++ A) (mirror (code y) ++ B) N [.R]
  have h4 := fromB_within y ([.R] ++ M) (mirror (code x) ++ A) B N
  have h5 := fromA_within x (code y ++ ([.R] ++ M)) A B N
  have h6 := pushW_within (code x ++ (code y ++ ([.R] ++ M))) A B N [.L]
  have e : [Sym.L] ++ (code x ++ (code y ++ ([.R] ++ M))) = code (.cons x y) ++ M := by simp [code]
  rw [e] at h6
  exact (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).mono (by omega)

theorem unconsF_within : unconsF.Within (st (code (.cons x y) ++ M) A B N) (2 * ((code x).length + (code y).length) + 6)
    (st (code x ++ (code y ++ M)) A B N) := by
  have h1 := pop1_within (code x ++ (code y ++ (.R :: M))) A B N .L
  have e : Sym.L :: (code x ++ (code y ++ (.R :: M))) = code (.cons x y) ++ M := by simp [code]
  rw [e] at h1
  have h2 := toA_within x (code y ++ (.R :: M)) A B N
  have h3 := toB_within y (.R :: M) (mirror (code x) ++ A) B N
  have h4 := pop1_within M (mirror (code x) ++ A) (mirror (code y) ++ B) N .R
  have h5 := fromB_within y M (mirror (code x) ++ A) B N
  have h6 := fromA_within x (code y ++ M) A B N
  exact (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).mono (by omega)

end

end Groundwork.TM
