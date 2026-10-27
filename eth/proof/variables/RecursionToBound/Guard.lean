/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import RecursionToBound.Cert.Numbers
import ToTuring.Poly.NetFun
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra

/-! # The guard of the plan

The function of Theorem D (a) (proof/variables/RecursionToBound/Defs.lean) has a guard that the
paper (Step 5 of Appendix D) does not have: if the exponent of the padding string, computed from the
input, exceeds n, the function tries all assignments. The guard cannot be dropped, because a
solver's exponent can be computed only under a bound given in unary.

**What is proved.** `planFailsOnlyAboveN : PlanFailsOnlyAboveN`: for a polynomial-time solver and
all n₁, k, n, i, r: if the plan is `some v`, then n₁ ≤ n, v = `needOutputs` + `needWalk` and v ≤ n;
if the plan is `none` and n₁ ≤ n, then n < `needOutputs` + `needWalk`. So for n ≥ n₁ the guard is
the only reason for which the function does not sparsify.

**How.** A polynomial-time solver has two properties (`ClauseBound.Alg.Solver.Poly.needC_eq`,
`ClauseBound.Alg.Solver.Poly.needC_some`): the exponent computed under a bound, if there is one, is
the exponent; and there is one whenever the exponent is at most the bound. They are carried upwards
to the exponent of the networks (`needNetC`), to the exponent for one Δ (`needAtC`), and to the
maximum over all Δ (`needOutputsC`, by `foldr_bind_max`), each time as a pair of lemmas: if the
value computed under the bound is there, it is the exact value; if it is missing, the exact value
exceeds the bound. -/

public section

namespace RecursionToBound

open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.TopN VariableBound.Net

variable {Idx : Type} [Enc Idx] {S : Solver Idx}

/-- The exponent of the networks computed under a bound, if there is one, is the exponent of the
networks. -/
theorem needNetC_eq_some (hS : S.Poly) {b : U} {i : Idx} {Ub P B w : ℕ} (h : needNetC S b i Ub P B = some w) : w = needNet S i Ub P B := by
  unfold needNetC at h
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [hS.needC_eq _ _ _ hv]
  rfl

/-- If the exponent of the networks computed under a bound is missing, the exponent of the networks
exceeds the bound. -/
theorem lt_needNet_of_none (hS : S.Poly) {b : U} {i : Idx} {Ub P B : ℕ} (h : needNetC S b i Ub P B = none) : b.length < needNet S i Ub P B := by
  unfold needNetC at h
  have h1 := Option.map_eq_none_iff.1 h
  by_contra hc
  have h2 : S.need (i, List.replicate (lamS (S.K i) (3 * S.K i ^ 8) Ub P) (), List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) P B) ()) ≤ b.length :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (not_lt.1 hc)
  rw [hS.needC_some b _ h2] at h1
  exact Option.some_ne_none _ h1

/-- The exponent for one Δ computed under a bound, if there is one, is the exponent for this Δ. -/
theorem needAtC_eq_some (hS : S.Poly) {b : U} {k : ℕ} {i : Idx} {n Δ w : ℕ} (h : needAtC S b k i n Δ = some w) : w = needAt S k i n Δ := by
  unfold needAtC at h
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [needNetC_eq_some hS hv]
  rfl

/-- If the exponent for one Δ computed under a bound is missing, the exponent for this Δ exceeds the
bound. -/
theorem lt_needAt_of_none (hS : S.Poly) {b : U} {k : ℕ} {i : Idx} {n Δ : ℕ} (h : needAtC S b k i n Δ = none) : b.length < needAt S k i n Δ := by
  unfold needAtC at h
  have h1 := lt_needNet_of_none hS (Option.map_eq_none_iff.1 h)
  unfold needAt
  omega

/-- The maximum over Δ computed under a bound, if there is one, is the maximum over Δ. -/
theorem needOutputsC_eq_some (hS : S.Poly) {b : U} {k : ℕ} {r : ℕ × ℕ} {i : Idx} {n w : ℕ} (h : needOutputsC S b k r i n = some w) : w = needOutputs S k r i n := by
  unfold needOutputsC at h
  have h1 : ∀ Δ ∈ deltas k r n, needAtC S b k i n Δ = some (needAt S k i n Δ) := fun Δ hΔ => by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (isSome_of_foldr_bind_max h Δ hΔ)
    rw [hv, needAtC_eq_some hS hv]
  rw [foldr_bind_max_of_some h1] at h
  exact (Option.some.inj h).symm

/-- If the maximum over Δ computed under a bound is missing, the maximum over Δ exceeds the bound. -/
theorem lt_needOutputs_of_none (hS : S.Poly) {b : U} {k : ℕ} {r : ℕ × ℕ} {i : Idx} {n : ℕ} (h : needOutputsC S b k r i n = none) : b.length < needOutputs S k r i n := by
  unfold needOutputsC at h
  obtain ⟨Δ, hΔ, hn⟩ := exists_none_of_foldr_bind_max h
  exact (lt_needAt_of_none hS hn).trans_le (NetE.le_foldr_max (List.mem_map_of_mem hΔ))

/-- For n ≥ n₁ the function sparsifies unless the exponent exceeds n; and where there is a plan, it
is the sum of the exponent for the outputs and the exponent for the walk. -/
theorem planFailsOnlyAboveN : PlanFailsOnlyAboveN := by
  intro Idx _ S hS n₁ k n i r
  constructor
  · intro v h
    unfold planAt at h
    split_ifs at h with hn
    obtain ⟨w, hw, h2⟩ := Option.bind_eq_some_iff.1 h
    split_ifs at h2 with hc
    have e := Option.some.inj h2
    rw [needOutputsC_eq_some hS hw] at e hc
    exact ⟨hn, e.symm, e ▸ hc⟩
  · intro h hn
    unfold planAt at h
    rw [if_pos hn] at h
    cases hw : needOutputsC S (List.replicate n ()) k r i n with
    | none =>
      have h1 := lt_needOutputs_of_none hS hw
      rw [List.length_replicate] at h1
      omega
    | some w =>
      rw [hw, Option.bind_some] at h
      split_ifs at h with hc
      rw [← needOutputsC_eq_some hS hw]
      omega

end RecursionToBound
