/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.ViaGrouping.Level
public import Eight.ViaGrouping.LevelCert
public import Eight.ViaGrouping.Bridge
public import Eight.ViaGrouping.GridPsi
public import Eight.Level.End

/-! # One level of the recursion on an algorithm for networks in the printed form, with the hypotheses filled in

proof/networks/Eight/ViaGrouping/LevelNet.lean, Level.lean and LevelCert.lean take interface
statements as hypotheses. Here they are filled in: Lemma 2 and its programs (`Eight.stPieces`, and
`Eight.stKeeps`, which is about the pieces and is not `Eight.ViaGrouping.stKeeps`) and the
procedures that present the two networks of ι (`Eight.Level.stPresents_of`).
Then the two functions for Ψ are taken to be the program `gridPsi` of
proof/networks/Eight/ViaGrouping/GridPsiDefs.lean. In the four theorems `…_gridPsi…` what is asked
of that program (`StGridPsi`, `StGridPsiPoly`) is a hypothesis; it is proved in
proof/networks/Eight/ViaGrouping/GridPsi.lean. The last
theorem is the sentence «Both networks satisfy Definition 2 …» of the proof of Proposition 3 for the
procedures that Algorithm 1 runs, without hypotheses. -/

public section

namespace Eight.ViaGrouping

open Groundwork Groundwork.Prog Eight.SecNetworks Eight.Level

/-- The cost of one level (the paragraph «Cost» of the proof of Proposition 3): if NA evaluates
networks on [g], in the printed form, with the exponent e·U + (e + 2)·gP/K of Lemma 1, and psiR,
psiC compute the functions Ψ of the row and of the column networks, then
`levelAlgP g psiR psiC NA` evaluates (g², λ)-cliques with the exponent (ρ + 2/K)e + 2/K, ρ = 11/12. -/
theorem stLevelP : StLevelP := stLevelP_of (stPresents_of stPieces)

/-- The algorithm of one level has polynomial-time steps, if NA has (for P in unary) and psiR, psiC
are polynomial-time functions. -/
theorem stLevelKeepsP : StLevelKeepsP := stLevelKeepsP_of stKeeps

/-- The program `gridPsi` computes Ψ in the form that the level asks for. -/
theorem stPsiOK_gridPsi (h : StGridPsi) (g : ℕ) (tr : Bool) : StPsiOK g tr (gridPsi g tr) := fun lam y Rm hl _ => h g tr lam y Rm hl

/-- The program `gridPsi` is polynomial-time in the form that the level asks for. -/
theorem stPsiPoly_gridPsi (h : StGridPsiPoly) (g : ℕ) (tr : Bool) : StPsiPoly (gridPsi g tr) := h g tr

/-- «Cost» of the proof of Proposition 3, with the program `gridPsi` for Ψ: an algorithm for
networks on [g], in the printed form, with the exponent of Lemma 1 gives an algorithm for cliques on
g² nodes with the exponent (ρ + 2/K)e + 2/K. -/
theorem levelAlgP_gridPsi_correct (h : StGridPsi) {K g : ℕ} {e : ℝ} {NA : NetAlg} (hK : 2 ≤ K) (hg : K ≤ g) (h0 : 0 ≤ e) (hN : Correct NA g K e (e + 2)) :
    (levelAlgP g (gridPsi g false) (gridPsi g true) NA).Correct (g * g) ((rho + 2 / K) * e + 2 / K) :=
  stLevelP K g e _ _ NA hK hg h0 (stPsiOK_gridPsi h g false) (stPsiOK_gridPsi h g true) hN

/-- With the program `gridPsi` for Ψ, the algorithm of one level has polynomial-time steps if the
algorithm for networks has. -/
theorem levelAlgP_gridPsi_keeps (h : StGridPsiPoly) (g : ℕ) {NA : NetAlg} (hN : AlgKeeps NA) : (levelAlgP g (gridPsi g false) (gridPsi g true) NA).Keeps :=
  stLevelKeepsP g _ _ NA (stPsiPoly_gridPsi h g false) (stPsiPoly_gridPsi h g true) hN

/-- **«Both networks satisfy Definition 2 with P = g³λ (so gP = N), with B₁ = gB + g²λ + 1 in the
role of B, and with τ = poly(B + λ)»** (proof of Proposition 3), for the procedures that CLIQUE of
Algorithm 1 hands to NETWORK (Ψ by the program `gridPsi`). What
differs from the paper is said at `levelNetP_isNetworkP_printed_of`. -/
theorem levelNetP_isNetworkP (g : ℕ) (hg : 1 ≤ g) : ∃ a : ℕ, ∀ (tr : Bool) (C : Type) [HasSize C] (lam : C → ℕ) (R : Stepped (C × IQ) ℤ) (c : C) (B t S : ℕ)
    (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ), 1 ≤ lam c → 1 ≤ t → y < (tOf (lam c) + 1) ^ nRect g → ServesInst R c (lam c) B t S Rm →
    IsNetworkP (levelProcs g tr (gridPsi g tr) lam R) (c, y) (levelNetP g tr (lam c) y Rm) (g ^ 3 * lam c) (g * B + g ^ 2 * lam c + 1)
      (a * (B + lam c) ^ a * t) (S + a * (size c + B + lam c) ^ a + 2) :=
  let ⟨a, ha⟩ := levelNetP_isNetworkP_printed_of (stPresents_of stPieces) g hg
  ⟨a, fun tr => ha tr _ (stPsiOK g tr)⟩

end Eight.ViaGrouping
