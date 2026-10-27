/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Defs
import SparsificationLemma.Bound
import UniformInK.Spars.Step
import SparsifyWidthK.Step
import SparsifyWidthK.SetAlg

/-! # The facts on finite sets that the walk of the tree needs, for thresholds with `ThrC`

This file proves `StIfaceC`: it collects the structure `Iface` of
proof/sparsification/SparsifyWidthK/Interfaces.lean. That the root and both children of a node are
nodes is proved in proof/sparsification/UniformInK/Spars/Step.lean, and the bound on the size of a
leaf, the two children computed and the equivalence of a node with its children in
proof/sparsification/SparsifyWidthK, all for thresholds that are at least 1; the bounds on the two
counters are `stBoundC`. It is the twin of proof/sparsification/UniformInK/Spars/Iface.lean. -/

public section

namespace SparsificationLemma

open Finset Groundwork Groundwork.Sparsify WidthK WidthK.Prog WidthK.ProgMain UniformInK

/-- All that the walk of the tree needs to know about the rule on finite sets, for thresholds with
`ThrC` and any D ≥ (β 0 + … + β (k-1))·n. -/
theorem stIfaceC : StIfaceC := fun k τ n D θ β hT hD =>
  { root := fun F₀ h => ⟨h, stNodeRootU _ _ _ _ _⟩
    step := fun F₀ F p t j H hN hR => by
      obtain ⟨a, b⟩ := stNodeStepU _ _ _ _ _ _ _ _ _ _ hT.pos hN.2 hR
      exact ⟨⟨hN.1, a⟩, ⟨hN.1, b⟩⟩
    bound := fun F₀ F p t hN => by
      obtain ⟨a, b⟩ := stBoundC _ θ β k τ n F₀ F (litsBelow n) p t hT (card_litsBelow n) (fun C hC => (hN.1 C hC).1) hN.2
      exact ⟨a.trans hD, b⟩
    clause := fun F₀ F p t hN C hC => by
      obtain ⟨C', hC', hs, -⟩ := hN.2.1 C hC
      exact ⟨C', hC', hs⟩
    leaf := fun F₀ F p t hN hL => by
      refine stLeafCard _ θ k n F (litsBelow n) hT.pos (card_litsBelow n) (fun C hC => ?_) hL
      obtain ⟨C', hC', hs, hne⟩ := hN.2.1 C hC
      obtain ⟨a, b, c⟩ := hN.1 C' hC'
      exact ⟨hs.trans a, hne b, (card_le_card hs).trans c⟩
    sat := fun F₀ F p t j H v _ _ => stSatIff _ _ _ _ _
    light_eq := fun F₀ F p t j H hN hR => by
      obtain ⟨-, N, a, h, hI, -⟩ := hN.2
      exact stLightEq _ _ _ _ _ hT.pos hI.red hR.heart
    heavy_eq := fun F₀ F p t j H hN hR => by
      obtain ⟨-, N, a, h, hI, -⟩ := hN.2
      exact stHeavyEq _ _ _ _ _ hI.red hR.heart }

end SparsificationLemma
