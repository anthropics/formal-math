/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Dl.Tab
import Nc.Plus.Interface

/-!
# The copies and the zeros of a group
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

open Finset Nc.G

variable {A : Type} [CommRing A] {K A' E U0 U1 mm : ℕ} {M : Sys A (K + K + A') E}

open Classical in
/-- The number of copies of units that the parties of a group ever hold. -/
noncomputable def evG (grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm) (n : NN K U0) (o : M.N → Fin U1)
    (g : Fin mm) : ℕ :=
  ∑ p ∈ univ.filter (fun p => grp n o p = g),
    ((Plan.seenAt n o E : Finset (Uid (K + K) U0 M.N U1)).filter (Holds (hold0 M.np) (hold1 M.np) p)).card

open Classical in
/-- The number of units of zeros and of counts of a group. -/
noncomputable def pdG (P : G.Plan M U0 U1) (grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm) (n : NN K U0)
    (o : M.N → Fin U1) (g : Fin mm) : ℕ :=
  ∑ r ∈ univ.filter (fun r : M.R => grp n o (M.rp r) = g),
    (1 + Fintype.card ((M.kind r.1).SlAt r.2)) * P.num n o r.1

end Nc.Dl
