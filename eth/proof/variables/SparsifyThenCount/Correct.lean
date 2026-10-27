/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsifyThenCount.Defs
import CountKSatRate.Leaf
import all CountKSat.Top.Count
import all UniformInK.Top.Correct
import all VariableBound.Top.Correct

/-! # Correctness of the function `ADG`

`stCorrectDG : StCorrectDG` says that the function `ADG` is right, for any family of thresholds Θ
that serves with the bound Lc on the occurrences. The width k and the formula are read from the
input (`StDecM`). If the
plan is `none`, the exponent is n and the function counts exhaustively (`StBruteC`). Otherwise the
plan says that s ≥ s0U k, that Δ = 2^β ≤ n + 1, that n ≥ 29·⌈log₂(2Δ)⌉ + 19, and that the exponent
is `needD` and at most n. The plan, its tests and the
exponent are those of the namespace `VariableBound` and do not name the thresholds, so the lemma on
them, `planAtD_some`, serves here unchanged. Three things depend on the thresholds. The bound Lc k s +
2 ≤ Δ on the clauses per variable of
a leaf comes from `StepSparsify.Serves.par`. The pad suffices for the rounds of the walk because the
tree has at most 2^(⌊n/2^s⌋+1) leaves (`StRoundsDG`). The walk starts from the formula without the
clauses that contain a variable together with
its negation, and returns the number of satisfying assignments by `StepSparsify.StWalkCountG`. Every
leaf is counted by `VariableBound.countD`, which is right by `VariableBound.StCountD`. -/

namespace SparsifyThenCount

open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK UniformInK.Correct VariableBound VariableBound.Correct VariableBound.Net
open PaddedDescent.F.Mark (WfL occ nSat)

/-- A number F ≥ 2^(`VariableBound.restD` k K n s) is at least 2·2^(⌊n/2^s⌋+1) − 1, which suffices
for the rounds of the walk: ⌊n/2^s⌋ + 2 is one of the four summands of `restD`. -/
public theorem stRoundsDG : StRoundsDG := by
  intro k K n s F hF
  have h1 : n / 2 ^ s + 1 + 1 ≤ restD k K n s := by unfold restD; omega
  have h2 : 2 ^ (n / 2 ^ s + 1 + 1) ≤ F := (Nat.pow_le_pow_right (by norm_num) h1).trans hF
  rw [pow_succ] at h2
  omega

/-- The function for the bound in n, run with thresholds that serve, is right on every k-CNF, for
every k ≥ 1 and every n, when the pad has length at least 2^(eD …); given the count of a sparse
formula (`VariableBound.StCountD`), the budgets
(`VariableBound.StBudgetD`, `StRoundsDG`), the walk through the counting tree
(`StepSparsify.StWalkCountG`), the decoders and exhaustive counting. -/
public theorem stCorrectDG (hC : StCountD) (hB : StBudgetD) (hR : StRoundsDG) (hWC : StepSparsify.StWalkCountG) (hD : StDecM) (hBr : StBruteC) (hDU : StDecU) : StCorrectDG := by
  intro Θ Lc hSv Idx _ S e C₀ Q hS slU k n φ hk h3 pad hpad
  obtain ⟨hdk, hdec⟩ := hD k n φ hk h3.1
  have hkU : kU (SatM.enc k φ) = k := by rw [kU, hdk, List.length_replicate]
  have hn : nU (SatM.enc k φ) = n := by rw [nU, hdec, List.length_replicate]
  obtain ⟨i, hi⟩ : ∃ i, i = idxU Q.pick (SatM.enc k φ) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = precU Q.pick slU (SatM.enc k φ) := ⟨_, rfl⟩
  have hplan : planD S Q.pick slU (SatM.enc k φ) = planAtD S k n i s := by rw [planD, hkU, hn, hi, hs]
  have hnum : (bif (planD S Q.pick slU (SatM.enc k φ)).isNone then bruteU (SatM.enc k φ, pad)
      else numDG Θ S (kcU (kU (SatM.enc k φ)) (nU (SatM.enc k φ))) (idxU Q.pick (SatM.enc k φ)) (precU Q.pick slU (SatM.enc k φ)) (fmlOf (SatM.enc k φ)) pad) = SatK.numSat φ := by
    rw [eD, hplan, hn] at hpad
    rw [hplan, ← hi, ← hs, hkU, hn, hdec]
    cases hpl : planAtD S k n i s with
    | none =>
      rw [hpl, Option.getD_none] at hpad
      simp only [Option.isNone_none, cond_true, bruteU, hdec, List.length_replicate]
      exact brute_eq hBr hDU φ hk h3 pad hpad
    | some v =>
      rw [hpl, Option.getD_some] at hpad
      obtain ⟨⟨c1, c2, c3⟩, c6⟩ := planAtD_some hS hpl
      have hblock : blockU k n s = 2 ^ betaU k s := min_eq_left c2
      obtain ⟨Δ, hΔ⟩ : ∃ Δ, Δ = blockU k n s := ⟨_, rfl⟩
      rw [← hblock, ← hΔ] at c3
      rw [c6, needD, pow_add, ← hΔ] at hpad
      have hp1 : 2 ^ needNet S i (UbD k (S.K i) n Δ) (PbD (S.K i) n Δ) (BbD k n) ≤ pad.length :=
        le_trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) hpad
      have hp2 : 2 ^ restD k (S.K i) n s ≤ pad.length := le_trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)) hpad
      obtain ⟨b1, b2, -, b4⟩ := hB k (S.K i) n s pad.length hk c1 hp2
      have b3 := hR k (S.K i) n s pad.length hp2
      rw [← hΔ] at b1 b2
      have q1 : Lc k s + 2 ≤ Δ := by rw [hΔ, hblock]; exact hSv.par k s hk c1
      have hΔ2 : 2 ≤ Δ := by omega
      have hoki : ∃ l, i = Q.idx l := ⟨_, hi.trans (Q.pick_idx _)⟩
      have hK2 : 2 ≤ S.K i := by obtain ⟨l, rfl⟩ := hoki; exact Q.K_two l
      simp only [Option.isNone_some, cond_false, numDG, kcU_eq c2, List.length_replicate]
      refine hWC Θ Lc hSv k s n φ pad _ hk h3 c1 b3 b4 fun x hxl hx1 ho hs' => ?_
      obtain ⟨m1, m2, m3, m4⟩ := Leaf.spec hk hx1 ho hs'
      have hlen : (leafM x).length ≤ Δ * n := (m1.trans hxl).trans (Nat.mul_le_mul_right _ q1)
      unfold valD
      rw [← hΔ, hC Idx S (fun i => ∃ l, i = Q.idx l) Q.correct k pad i n Δ (leafM x) hoki hK2 m2 (fun v => (m3 v).trans q1) hlen hΔ2 c3 ⟨hp1, b1, b2⟩, m4]
  unfold ADG
  dsimp only
  rw [hnum, hdec]
  exact CountTop.outW_eq _ _ _

end SparsifyThenCount
