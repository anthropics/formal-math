/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.Theorem30.Areas

/-!
# The cells of the directory, by name

The routines of Section 4 find the sizes and the addresses of the tables in the directory, the
first cells of the block.  `DirCells p b0 μ` says what the cells that they read hold, one equation
for each cell, under the name that the cell has in the program texts (`Dir.bands`, `Dir.encA`, …).
A proof that treats `x := mem[b0 + Dir.bands]` names the equation `bands`.  The shared stage
establishes all of them (`SharedReady.dirCells`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp

/-- What the cells of the directory that the routines of Section 4 read hold. -/
structure DirCells (p : Sec2.Par) (b0 : ℕ) (μ : ℕ → ℤ) : Prop where
  levels : μ b0 = (p.L : ℕ)
  inner : μ (b0 + 1) = (p.m : ℕ)
  outer : μ ((b0 : ℤ) + 4).toNat = (p.Lo : ℕ)
  blocks : μ ((b0 : ℤ) + 7).toNat = (p.K0 : ℕ)
  bands : μ ((b0 : ℤ) + 9).toNat = (p.nB : ℕ)
  leaves : μ ((b0 : ℤ) + 10).toNat = (p.T : ℕ)
  mask : μ ((b0 : ℤ) + 21).toNat = (p.aMASK b0 : ℕ)
  band : μ ((b0 : ℤ) + 22).toNat = (p.aBAND b0 : ℕ)
  block : μ ((b0 : ℤ) + 23).toNat = (p.aBLOCK b0 : ℕ)
  digits : μ ((b0 : ℤ) + 24).toNat = (p.aDIG3 b0 : ℕ)
  encA : μ ((b0 : ℤ) + 26).toNat = (p.aENCA b0 : ℕ)
  encB : μ ((b0 : ℤ) + 27).toNat = (p.aENCB b0 : ℕ)
  sharedEnd : μ ((b0 : ℤ) + 30).toNat = (aWD p b0 : ℕ)

/-- After the shared stage the directory holds what `DirCells` says. -/
theorem _root_.Light.Sec2.SharedReady.dirCells {p : Sec2.Par} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
    {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {μ : ℕ → ℤ}
    (h : Sec2.SharedReady p hmL aX aY b0 X Y μ) : DirCells p b0 μ where
  levels := dir_cell h (j := Dir.levels) (by norm_num)
  inner := dir_cell h (j := Dir.inner) (by norm_num)
  outer := h.dir_read (j := Dir.outer) (by norm_num)
  blocks := h.dir_read (j := Dir.blocks) (by norm_num)
  bands := h.dir_read (j := Dir.bands) (by norm_num)
  leaves := h.dir_read (j := Dir.leaves) (by norm_num)
  mask := h.dir_read (j := Dir.mask) (by norm_num)
  band := h.dir_read (j := Dir.band) (by norm_num)
  block := h.dir_read (j := Dir.block) (by norm_num)
  digits := h.dir_read (j := Dir.digits) (by norm_num)
  encA := h.dir_read (j := Dir.encA) (by norm_num)
  encB := h.dir_read (j := Dir.encB) (by norm_num)
  sharedEnd := h.dir_read (j := Dir.sharedEnd) (by norm_num)

end Light.Sec4
