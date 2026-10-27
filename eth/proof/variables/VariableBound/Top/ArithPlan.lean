/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Top.ArithDefs
import Mathlib.Tactic.SplitIfs

/-! # The exponent of a plan

Two interface statements are proved. `StPlanLeD`: the exponent of a plan, or else n, is at most n.
`StPlanNeedD`: it is at most `needD` if the three tests of the plan are passed and the solver is
polynomial-time.
The first bound needs nothing of the solver. The second uses that the solver's bounded computation
of its exponent gives the exponent, and gives a value whenever the
exponent is at most the bound n. -/

public section

namespace VariableBound

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.Mark CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound.Net

/-- The exponent of a plan, or else n, is at most n. -/
theorem stPlanLeD : StPlanLeD := by
  intro Idx _ S k n i s
  unfold planAtD
  split_ifs with hc
  · cases needNetC S (List.replicate n ()) i (UbD k (S.K i) n (blockU k n s)) (PbD (S.K i) n (blockU k n s)) (BbD k n) with
    | none => simp
    | some v =>
      simp only [Option.bind_some]
      split_ifs with h1
      · simpa using h1
      · simp
  · simp

/-- The exponent of a plan, or else n, is at most `needD` if the three tests are passed and the
solver is polynomial-time. -/
theorem stPlanNeedD : StPlanNeedD := by
  intro Idx _ S hS k n i s t1 t2 t3
  unfold planAtD needNetC needD needNet
  set x : Idx × U × U := (i, List.replicate (lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n (blockU k n s)) (PbD (S.K i) n (blockU k n s))) (),
    List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) (PbD (S.K i) n (blockU k n s)) (BbD k n)) ()) with hx
  set u := max (3 * S.K i ^ 8 * Nat.size (S.K i)) (PbD (S.K i) n (blockU k n s) * (2 * (3 * S.K i ^ 8) / S.K i + 1))
  set d := (S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n (blockU k n s)) (PbD (S.K i) n (blockU k n s))
  set r := restD k (S.K i) n s
  rw [if_pos ⟨t1, t2, t3⟩]
  cases h : S.needC (List.replicate n (), x) with
  | none =>
    simp only [Option.map_none, Option.bind_none, Option.getD_none]
    by_contra hlt
    have h1 : S.need x ≤ (List.replicate n ()).length := by
      have : S.need x ≤ max u (max d (S.need x)) := (le_max_right _ _).trans (le_max_right _ _)
      simp only [List.length_replicate]
      omega
    rw [hS.needC_some _ x h1] at h
    cases h
  | some v =>
    have hv := hS.needC_eq _ x v h
    subst hv
    simp only [Option.map_some, Option.bind_some]
    split_ifs with h1
    · simp
    · simpa using (not_le.1 h1).le

end VariableBound
