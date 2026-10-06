/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Seg
public import ThreeSumApsp.Lang.Rules

/-!
# Arrays in the memory

A routine assumes the same facts about each of its arrays: which list it holds, how long the list
is, and that it lies below some address `top`, from which on the routine writes: the free pointer,
the place of the result, the scratch space.  `ListAt μ a l N top` is the record of these three
facts, and `ArrayAt μ a l N U top` adds a bound `U` on the entries.  `IndexAt μ a l N p top` is the
record for a list of natural numbers below `p`.  What a routine assumes is then a record with one
field for each array.

* `ListAt.keep`, `ArrayAt.keep`: an array stays in place when its cells do not change.
* `ListAt.mono`, `ArrayAt.mono`: `top` and `U` may grow.
* `ListAt.read`, `ArrayAt.read`, `ArrayAt.abs_read_le`: what a cell holds, and how large it is.
* `ListAt.drop_take`, `ArrayAt.drop_take`: a piece of an array is an array.
* `IndexAt.keep`, `IndexAt.read`, `IndexAt.getD_lt`: the same for natural numbers.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}

/-- The list `l` stands at address `a`: it has `N` entries, and its cells lie below `top`. -/
structure ListAt (μ : ℕ → ℤ) (a : ℕ) (l : List ℤ) (N top : ℕ) : Prop where
  len : l.length = N
  seg : Seg μ a l
  below : a + N ≤ top := by light_arith

/-- The list `l` stands at address `a`: it has `N` entries, each of absolute value at most `U`, and
its cells lie below `top`. -/
structure ArrayAt (μ : ℕ → ℤ) (a : ℕ) (l : List ℤ) (N : ℕ) (U : ℤ) (top : ℕ) : Prop where
  len : l.length = N
  seg : Seg μ a l
  bound : AbsLe l U
  below : a + N ≤ top := by light_arith

namespace ListAt

/-- A list stays in place when its cells do not change.  That they lie below `top` is said again in
the description of the cells: so the promise `Kept μ μ' top` of a callee is enough as it stands. -/
theorem keep (h : ListAt μ a l N top)
    (hs : SameOn (fun b => Inside a N b ∧ b < top) μ μ' := by light_keep) : ListAt μ' a l N top :=
  { h with seg := h.seg.congr fun i hi => hs _ (by have := h.len; have := h.below; omega) }

/-- The address `top` may grow. -/
theorem mono (h : ListAt μ a l N top) (ht : top ≤ top' := by light_arith) : ListAt μ a l N top' :=
  { h with below := h.below.trans ht }

/-- Reading a cell. -/
theorem read (h : ListAt μ a l N top) (hi : i < N) : μ (a + i) = l.getD i 0 :=
  h.seg.getD (h.len ▸ hi) 0

/-- The `n` entries from place `k` on. -/
theorem drop_take (h : ListAt μ a l N top) (hk : k + n ≤ N) :
    ListAt μ (a + k) ((l.drop k).take n) n top where
  len := by rw [List.length_take, List.length_drop, h.len]; omega
  seg := (h.seg.drop k).take n
  below := by have := h.below; omega

end ListAt

namespace ArrayAt

/-- An array without the bound on its entries. -/
theorem listAt (h : ArrayAt μ a l N U top) : ListAt μ a l N top := { h with }

/-- An array stays in place when its cells do not change. -/
theorem keep (h : ArrayAt μ a l N U top)
    (hs : SameOn (fun b => Inside a N b ∧ b < top) μ μ' := by light_keep) :
    ArrayAt μ' a l N U top :=
  { h with seg := (h.listAt.keep hs).seg }

/-- The bound `U` on the entries and the address `top` may grow. -/
theorem mono (h : ArrayAt μ a l N U top) (hU : U ≤ U' := by light_arith)
    (ht : top ≤ top' := by light_arith) : ArrayAt μ a l N U' top' :=
  { h with bound := fun x hx => (h.bound x hx).trans hU, below := h.below.trans ht }

/-- Reading a cell. -/
theorem read (h : ArrayAt μ a l N U top) (hi : i < N) : μ (a + i) = l.getD i 0 := h.listAt.read hi

/-- A cell of an array holds a number of absolute value at most `U`. -/
theorem abs_read_le (h : ArrayAt μ a l N U top) (hi : i < N) : |μ (a + i)| ≤ U := by
  rw [h.seg i (h.len ▸ hi)]
  exact h.bound.getElem _

/-- The `n` entries from place `k` on. -/
theorem drop_take (h : ArrayAt μ a l N U top) (hk : k + n ≤ N) :
    ArrayAt μ (a + k) ((l.drop k).take n) n U top :=
  { h.listAt.drop_take hk with
    bound := fun x hx => h.bound x (List.mem_of_mem_drop (List.mem_of_mem_take hx)) }

end ArrayAt

/-- The list `l` of natural numbers stands at address `a`: it has `N` entries, each below `p`, and
its cells lie below `top`. -/
structure IndexAt (μ : ℕ → ℤ) (a : ℕ) (l : List ℕ) (N p top : ℕ) : Prop where
  len : l.length = N
  seg : SegN μ a l
  lt : ∀ x ∈ l, x < p
  below : a + N ≤ top := by light_arith

namespace IndexAt

variable {l : List ℕ} {p : ℕ}

/-- A list of natural numbers stays in place when its cells do not change. -/
theorem keep (h : IndexAt μ a l N p top)
    (hs : SameOn (fun b => Inside a N b ∧ b < top) μ μ' := by light_keep) :
    IndexAt μ' a l N p top :=
  { h with
    seg := Seg.congr h.seg fun i hi => hs _ (by
      have := h.len
      have := h.below
      rw [List.length_map] at hi
      omega) }

/-- Reading a cell. -/
theorem read (h : IndexAt μ a l N p top) (hi : i < N) : μ (a + i) = (l.getD i 0 : ℕ) :=
  h.seg.read (h.len ▸ hi)

/-- An entry is below `p`. -/
theorem getD_lt (h : IndexAt μ a l N p top) (hi : i < N) : l.getD i 0 < p := by
  have hl : i < l.length := h.len ▸ hi
  rw [List.getD_eq_getElem _ 0 hl]
  exact h.lt _ (List.getElem_mem hl)

end IndexAt

end Light
