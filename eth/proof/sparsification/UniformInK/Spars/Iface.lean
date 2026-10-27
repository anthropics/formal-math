/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Spars.Defs
import SparsifyWidthK.Step
import SparsifyWidthK.SetAlg

/-! # The facts on finite sets that the walk of the tree needs, for the thresholds `thetaU τ`

This file collects the structure `Iface` of proof/sparsification/SparsifyWidthK/Interfaces.lean from
the interface statements of proof/sparsification/UniformInK/Spars/Defs.lean. The bound on the size
of a leaf, the two children computed and the
equivalence of a node with its children are proved in proof/sparsification/SparsifyWidthK for any
thresholds, and are used here with the thresholds `thetaU τ`. It is the counterpart of
`WidthK.ProgMain.iface` in proof/sparsification/SparsifyWidthK/ProgMain.lean. -/

public section

namespace UniformInK

open Finset Groundwork Groundwork.Sparsify WidthK WidthK.Prog WidthK.ProgMain

/-- `StIfaceU` from the statements on nodes and on thresholds. -/
theorem ifaceU (h1 : StNodeRootU) (h2 : StNodeStepU) (h3 : StNodeBoundU) (h8 : StThrU) (h9 : StBetaSumU) : StIfaceU := fun τ k n hk hτ =>
  { root := fun F₀ h => ⟨h, h1 _ _ _ _ _⟩
    step := fun F₀ F p t j H hN hR => by
      obtain ⟨a, b⟩ := h2 _ _ _ _ _ _ _ _ _ _ (h8 k τ hk hτ).pos hN.2 hR
      exact ⟨⟨hN.1, a⟩, ⟨hN.1, b⟩⟩
    bound := fun F₀ F p t hN => by
      obtain ⟨a, b⟩ := h3 _ (thetaU τ) (betaSU τ) k τ n F₀ F (litsBelow n) p t (h8 k τ hk hτ) (card_litsBelow n) (fun C hC => (hN.1 C hC).1) hN.2
      exact ⟨a.trans (Nat.mul_le_mul_right _ (h9 τ k (by omega))), b⟩
    clause := fun F₀ F p t hN C hC => by
      obtain ⟨C', hC', hs, -⟩ := hN.2.1 C hC
      exact ⟨C', hC', hs⟩
    leaf := fun F₀ F p t hN hL => by
      refine stLeafCard _ (thetaU τ) k n F (litsBelow n) (h8 k τ hk hτ).pos (card_litsBelow n) (fun C hC => ?_) hL
      obtain ⟨C', hC', hs, hne⟩ := hN.2.1 C hC
      obtain ⟨a, b, c⟩ := hN.1 C' hC'
      exact ⟨hs.trans a, hne b, (card_le_card hs).trans c⟩
    sat := fun F₀ F p t j H v _ _ => stSatIff _ _ _ _ _
    light_eq := fun F₀ F p t j H hN hR => by
      obtain ⟨-, N, a, h, hI, -⟩ := hN.2
      exact stLightEq _ _ _ _ _ (h8 k τ hk hτ).pos hI.red hR.heart
    heavy_eq := fun F₀ F p t j H hN hR => by
      obtain ⟨-, N, a, h, hI, -⟩ := hN.2
      exact stHeavyEq _ _ _ _ _ hI.red hR.heart }

end UniformInK
