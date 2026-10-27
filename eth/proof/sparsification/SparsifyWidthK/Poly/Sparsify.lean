/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsifyWidthK.Interfaces

/-! The functions of `SparsifyWidthK/DefsProg.lean`, which compute the two children of a node of the
sparsification tree of a k-CNF, are polynomial-time
(`PolyT`). The last theorem, `certStep`, proves `StCertStep`, one of the interface statements of
`SparsifyWidthK/Interfaces.lean`. The proofs use the closure
lemmas for list functions in `proof/machines/ToTuring/Lib` and the certificates of `overP`, `minusP`
and `addP` in `proof/machines/ToTuring/Poly/Sparsify.lean`, whose pattern
this file follows: every certificate is stated for arguments that depend on a context x, the form in
which the tactic `fun_prop` can use it.
The width k and the thresholds θ do not depend on the input, and nothing is assumed about them. -/

@[expose] public section

namespace WidthK.Prog

open Groundwork Groundwork.Sparsify

variable {α : Type} [Enc α]

/-- Picking the sublist of a clause given by a mask is polynomial-time. -/
@[fun_prop] theorem polyT_maskP {m : α → List Bool} {C : α → PCl} (hm : PolyT m) (hC : PolyT C) :
    PolyT fun x => maskP (m x) (C x) := by
  unfold maskP; fun_prop

/-- Listing the candidate hearts is polynomial-time. The list `masks k`, of length 2^k, does not
depend on the input. -/
@[fun_prop] theorem polyT_heartsP (k : ℕ) {s : α → PFml} {j h : α → ℕ} (hs : PolyT s) (hj : PolyT j) (hh : PolyT h) :
    PolyT fun x => heartsP k (s x) (j x) (h x) := by
  unfold heartsP; fun_prop

/-- `tryP` with the threshold given as a number c.2 beside the pair c.1 = (j, h) of a clause size j
and a heart size h. -/
def tryT (k : ℕ) (s : PFml) (c : (ℕ × ℕ) × ℕ) : Option (PCl × PFml) :=
  ((heartsP k s c.1.1 c.1.2).find? fun H => decide (c.2 ≤ (overP s c.1.1 H).length)).map fun H =>
    (H, (overP s c.1.1 H).map (minusP H))

/-- The search for a heart of a given size that reaches a given threshold is polynomial-time. -/
@[fun_prop] theorem polyT_tryT (k : ℕ) {s : α → PFml} {c : α → (ℕ × ℕ) × ℕ} (hs : PolyT s) (hc : PolyT c) :
    PolyT fun x => tryT k (s x) (c x) := by
  unfold tryT; fun_prop

/-- `pickK` as a search along the list of the pairs (j, h) of a clause size j and a heart size h,
each with its threshold θ (j - h). This list does not depend on the input, so θ, an arbitrary
function, is never applied to a value computed from the input. -/
theorem pickK_eq (θ : ℕ → ℕ) (k : ℕ) (s : PFml) :
    pickK θ k s = (((pairsK k).map fun jh => (jh, θ (jh.1 - jh.2))).filterMap (tryT k s)).head? := by
  rw [List.filterMap_map]; rfl

/-- The choice of the heart and its petals at a node is polynomial-time. -/
@[fun_prop] theorem polyT_pickK (θ : ℕ → ℕ) (k : ℕ) {s : α → PFml} (hs : PolyT s) : PolyT fun x => pickK θ k (s x) := by
  simp only [pickK_eq]; fun_prop

/-- The two children of a node of the sparsification tree are computed in polynomial time. -/
@[fun_prop] theorem polyT_stepK (θ : ℕ → ℕ) (k : ℕ) {s : α → PFml} (hs : PolyT s) : PolyT fun x => stepK θ k (s x) := by
  unfold stepK; fun_prop

/-- The same for `stepK θ k` as a function of the node alone: the interface statement `StCertStep`. -/
theorem certStep : StCertStep := fun θ k => polyT_stepK θ k PolyT.id'

end WidthK.Prog
