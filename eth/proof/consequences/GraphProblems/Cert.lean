/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GraphProblems.Interfaces
public import ToTuring.Poly.Sat
public import CountKSat.Poly

/-! # Corollary 7: the programs are polynomial-time

The readers of the input, the formulas of the problems and the step of the tree for Dominating Set
are `PolyT`, and so are `digit` and `blockCl`. The numbers n come in unary, so the lists
`List.range n`
are no longer than the input. Everything is put together from the closure lemmas of
proof/machines/ToTuring/Lib/. -/

@[expose] public section

namespace GraphProblems

open Groundwork Groundwork.Prog CountKSat

variable {α : Type} [Enc α]

@[fun_prop] theorem ones_polyT {x : α → List Bool} (hx : PolyT x) : PolyT fun a => ones (x a) := by unfold ones; fun_prop

@[fun_prop] theorem rest_polyT {x : α → List Bool} (hx : PolyT x) : PolyT fun a => rest (x a) := by unfold rest; fun_prop

theorem ones_unary {x : α → List Bool} (hx : PolyT x) : Unary fun a => ones (x a) := by
  unfold ones
  exact Unary.of_length (by fun_prop)

theorem stCertRead : StCertRead := by
  have h1 : PolyT fun x : List Bool => List.replicate (ones x) () := ones_unary PolyT.id'
  constructor
  · unfold read1; fun_prop
  · unfold read2; fun_prop

@[fun_prop] theorem adjB_polyT {n u v : α → ℕ} {m : α → List Bool} (hn : PolyT n) (hm : PolyT m) (hu : PolyT u) (hv : PolyT v) :
    PolyT fun a => adjB (n a) (m a) (u a) (v a) := by unfold adjB; fun_prop

theorem pairs_polyT {n : α → ℕ} (hn : Unary n) : PolyT fun a => pairs (n a) := by
  have hr : PolyT fun a => List.range (n a) := PolyT.range hn
  unfold pairs; fun_prop

theorem stCertForm : StCertForm := by
  have hu : Unary fun a : List Unit × List Bool => a.1.length := Unary.of_length (by fun_prop)
  have hr : PolyT fun a : List Unit × List Bool => List.range a.1.length := PolyT.range hu
  have hp : PolyT fun a : List Unit × List Bool => pairs a.1.length := pairs_polyT hu
  refine ⟨?_, ?_, ?_, fun k => ?_⟩
  · unfold indepF; fun_prop
  · unfold cliqueF; fun_prop
  · unfold coverF; fun_prop
  · unfold colorF; fun_prop

theorem nBlocks_unary (b : ℕ) {n : α → ℕ} (hn : Unary n) : Unary fun a => nBlocks b (n a) := by
  unfold nBlocks
  exact Unary.of_le (hn.add (Unary.const 1)) (by have := hn.poly; fun_prop) fun a => Nat.add_le_add_right (Nat.div_le_self _ _) 1

@[fun_prop] theorem digit_polyT (b : ℕ) {y i : α → ℕ} (hy : PolyT y) (hi : PolyT i) : PolyT fun a => digit b (y a) (i a) := by
  unfold digit; fun_prop

@[fun_prop] theorem blockCl_polyT (b : ℕ) {i d : α → ℕ} (hi : PolyT i) (hd : PolyT d) : PolyT fun a => blockCl b (i a) (d a) := by
  unfold blockCl; fun_prop

@[fun_prop] theorem posC_polyT {D : α → List ℕ} (hD : PolyT D) : PolyT fun a => posC (D a) := by unfold posC; fun_prop

theorem nbhd_polyT {n : α → ℕ} {m : α → List Bool} (hn : Unary n) (hm : PolyT m) : PolyT fun a => nbhd (n a) (m a) := by
  have hr : PolyT fun a => List.range (n a) := PolyT.range hn
  have hr2 : PolyT fun p : α × ℕ => List.range (n p.1) := PolyT.range (hn.comp (by fun_prop))
  have hn' := hn.poly
  unfold nbhd; fun_prop

theorem stCertDom : StCertDom := by
  refine ⟨fun w => ?_, ?_, ?_⟩
  · unfold stepD; fun_prop
  · have h := nbhd_polyT (α := List Unit × ℕ × List Bool) (n := fun a => a.1.length) (m := fun a => a.2.2)
      (Unary.of_length (by fun_prop)) (by fun_prop)
    unfold rootD; fun_prop
  · unfold leafD; fun_prop

end GraphProblems
