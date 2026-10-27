/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Boson.Dual
public import ClauseBound.Boson.Defs2
public import ClauseBound.Boson.WickPlus
public import ClauseBound.Boson.Basic
public import ClauseBound.Boson.Scalars
public import ClauseBound.Boson.Defs

/-! # Facts on the list of the parts of a partition

Facts on the list of the parts of a partition of h: as a multiset it is the multiset of the parts,
its sum is h, its entries are positive, and 0 is not a part. -/

public section

namespace ClauseBound.Boson.HalfSum

open Finset

/-- The list of the parts, as a multiset, is the multiset of the parts. -/
theorem coe_lst {h : ℕ} (q : Nat.Partition h) : ((lst q : List ℕ) : Multiset ℕ) = q.parts := Multiset.coe_toList _

/-- The parts add up to h. -/
theorem sum_lst {h : ℕ} (q : Nat.Partition h) : (lst q).sum = h := by
  rw [lst, Multiset.sum_toList, q.parts_sum]

/-- The parts are positive. -/
theorem pos_lst {h : ℕ} (q : Nat.Partition h) : Pos (lst q) := fun _ hn => q.parts_pos (Multiset.mem_toList.1 hn)

/-- 0 is not a part. -/
theorem zero_notMem_parts {h : ℕ} (q : Nat.Partition h) : 0 ∉ q.parts := fun h0 => lt_irrefl 0 (q.parts_pos h0)

variable {lam h : ℕ} (enc : Pieces.Bits lam → Nat.Partition h)

end ClauseBound.Boson.HalfSum
