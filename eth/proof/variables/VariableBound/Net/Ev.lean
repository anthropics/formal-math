/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Net.Defs
import Mathlib.Tactic.Positivity

/-! # Step 3 of Appendix D: the programs for X(𝓛) and F(𝓛) are right

Proves `VariableBound.Net.StEvD` and `VariableBound.Net.StEvXF` from statements on the parts.

* One evaluation `evD` adds, over the admissible profiles, the numbers that the clique solver
  returns for their networks. The solver returns the value of the network
  (`ClauseBound.Alg.StValS`), because the functions `netD` present it
  (`StPresents`), its parameters and its total are within the bounds `PbD`, `BbD`, `UbD` (`StSize`)
  and the pad, the string of ones by which, as Appendix E says, the Lean proofs render a number of
  operations as time, is long enough. The sum of the values is the right side of display (65)
  (`StTotal`).
* By display (65) the right sides are congruent to X(𝓛) modulo 2^β and to F(𝓛) modulo 2^(n+1), and
  «the residues determine the numbers»: 0 ≤ X(𝓛) ≤ 2^n·C(m, n̄+1) ≤ 2^(β−1), and 0 ≤ F(𝓛) ≤ 2^n if
  X(𝓛) = 0. -/

public section

namespace VariableBound.Net.Ev

open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg
open ClauseBound.ParityChecks (Vof)

/-- The functions `netD` present the network of the profile y on g nodes, given `StPresents`. -/
theorem presents (hPr : StPresents) (g n : ℕ) (D : Dat) (y : ℕ) (fl : Bool) : netD.toP.Presents (ctx g n D y fl) (netDN g (ctx g n D y fl)) 0 0 := by
  have h := hPr (ctx g n D y fl)
  have e : (ctx g n D y fl).1.1.length = g := List.length_replicate
  rw [e] at h
  exact h

/-- Step 3 and Step 4: one evaluation is the right side of display (65). Hypotheses of the statement
(`StEvD`): the solver is right at the indices with `ok`, ok i, K ≥ 2, the list is fit for an
evaluation (`Fit`), and the pad is at least as long as the number `nPr` of numbers tried as profiles
and as 2^`needNet` for the bounds `UbD`, `PbD`, `BbD`. Derived from: the solver returns the value of
a network that is presented and within the bounds (`ClauseBound.Alg.StValS`), and the statements
`StPresents`, `StTotal` and `StSize` on the networks of the profiles. -/
theorem stEvD (hV : ClauseBound.Alg.StValS) (hPr : StPresents) (hT : StTotal) (hS : StSize) : StEvD := by
  intro Idx _ S ok hC k pad i n Δ nb M fl D hok hK hF hprof hnet
  have hK0 : 0 < S.K i := by omega
  have hg : 0 < 3 * S.K i ^ 8 := by positivity
  unfold evD
  rw [sumF_eq hprof, ← hT k (3 * S.K i ^ 8) n nb M D fl hg hF.wf]
  refine Finset.sum_congr rfl fun y _ => ?_
  cases hy : admD k (3 * S.K i ^ 8) n nb M D fl y with
  | false => simp
  | true =>
    obtain ⟨h1, h2⟩ := hS k (S.K i) n Δ nb M D fl y hK0 hF hy
    rw [cond_true, if_pos rfl]
    exact hV Idx S ok hC DCtx netD (ctx (3 * S.K i ^ 8) n D y fl) pad i _ _ _ _ hok hK (presents hPr _ n D y fl) h1 h2 hnet

/-- A number in [0, N) is the remainder modulo N of every number congruent to it. -/
theorem emod_eq_of_modEq {a b N : ℤ} (h : a ≡ b [ZMOD N]) (h0 : 0 ≤ a) (h1 : a < N) : b % N = a := by
  rw [← h.eq]; exact Int.emod_eq_of_lt h0 h1

/-- Step 1, display (65) and «the residues determine the numbers», for the programs: they compute
X(𝓛), and F(𝓛) if X(𝓛) = 0. Hypotheses of the statement (`StEvXF`): those of `StEvD` (solver right,
ok i, K ≥ 2, `Fit`, the two conditions on the pad), M ≥ β − 1 + r and M ≥ n + r, with β = n + ⌈log
C(m, n̄ + 1)⌉ + 1. Derived from: one evaluation is the right side of display (65) (`StEvD`), display (65)
(`AppVariables.XFStmt`), the bounds on X and F (`AppVariables.ResiduesStmt`), and that the list of
sets has as many checks as the list of lists (`StChks`). -/
theorem stEvXF (h : StEvD) (hXF : AppVariables.XFStmt) (hR : AppVariables.ResiduesStmt) (hC : StChks) : StEvXF := by
  intro Idx _ S ok hCor k pad i n Δ nb M D hok hK hF hprof hnet h1 h2
  have hlen : (chks D).length = D.2.length := (hC k n D hF.wf).1
  have hβ : 1 ≤ AppVariables.beta n D.1.length nb := by unfold AppVariables.beta; omega
  obtain ⟨hx, hf⟩ := hXF (Fin n → Bool) (Fin D.1.length) (Vof (n := n) D.1) nb (chks D) (AppVariables.beta n D.1.length nb) n M hβ (by rw [hlen]; exact h1) (by rw [hlen]; exact h2)
  obtain ⟨⟨hx0, hx1, hx2⟩, hf01⟩ := hR (Fin n → Bool) (Fin D.1.length) (Vof (n := n) D.1) nb (chks D) n (by simp)
  refine ⟨?_, fun h0 => ?_⟩
  · unfold evX
    rw [h Idx S ok hCor k pad i n Δ nb M false D hok hK hF hprof hnet]
    refine emod_eq_of_modEq hx hx0 (lt_of_le_of_lt (hx1.trans hx2) ?_)
    rw [Fintype.card_fin]
    have e : AppVariables.beta n D.1.length nb = n + Nat.clog 2 (D.1.length.choose (nb + 1)) + 1 := rfl
    have h4 : (0 : ℤ) < 2 ^ (n + Nat.clog 2 (D.1.length.choose (nb + 1))) := by positivity
    rw [e, pow_succ]; linarith
  · unfold evF
    rw [h Idx S ok hCor k pad i n Δ nb M true D hok hK hF hprof hnet]
    obtain ⟨hf0, hf1⟩ := hf01 h0
    refine emod_eq_of_modEq hf hf0 (lt_of_le_of_lt hf1 ?_)
    have h4 : (0 : ℤ) < 2 ^ n := by positivity
    rw [pow_succ]; linarith

end VariableBound.Net.Ev
