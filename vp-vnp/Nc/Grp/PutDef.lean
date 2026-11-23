/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Lists

/-!
# Writing units: definitions
-/

namespace Nc.Grp

open NS1 NS1.Tree

/-- The first `ub` bits, filled with zeros. -/
def padTake (ub : ℕ) (r : List Bool) : List Bool := r.take ub ++ List.replicate (ub - r.length) false

/-- Write the units of a string (with its final 1) at the keys; fail if the number of keys is wrong. -/
def putL (ub : ℕ) : List (List Bool) → List Bool → Tree → List Tree
  | [], r, t => if r = [] then [t] else []
  | k :: ks, r, t => if r = [] then [] else putL ub ks (r.drop ub) (tset k (ofBits (padTake ub r)) t)

/-- Write contents at keys. -/
def putAll : List (List Bool) → (ℕ → List Bool) → Tree → Tree
  | [], _, t => t
  | k :: ks, u, t => putAll ks (fun i => u (i + 1)) (tset k (ofBits (u 0)) t)

/-- Write several strings. -/
def putsL (ub : ℕ) : List (List (List Bool)) → List (List Bool) → Tree → List Tree
  | [], _, t => [t]
  | ks :: kss, strs, t => (putL ub ks (strs.headD []) t).flatMap (putsL ub kss strs.tail)

end Nc.Grp
