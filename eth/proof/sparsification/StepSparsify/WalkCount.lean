/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepSparsify.Defs
import StepSparsify.Walk
import SparsificationLemma.One
import UniformInK.Tree.Stack
import CountKSat.InOut
import all CountKSatRate.Top
import all CountKSat.Top.Count

/-! # The walk through the counting tree, for any thresholds that serve

This file proves `StWalkCountG` of proof/sparsification/StepSparsify/Defs.lean. Two points deserve
note. What is known of the tree comes from the
hypothesis `Serves Θ Lc` (its field `tree`), not from `StTreeU`. And the root of the tree is the
formula without the clauses that contain a variable together with its negation. By
`SparsificationLemma.stNoTaut`,
deleting them keeps the width and the satisfying assignments, hence their number (`cntN_noTaut`),
and leaves no such clause, as `tree` asks; it does not make the formula longer (`length_noTaut_le`).
The facts on the walk are used as proved in their own files: `stWalkSG`, `stRoundS` and
`stRoundSEnd` on the walk and its rounds, `stStateLenU` on the length of its states, `stCntToN` on
the count of a formula read with natural numbers as variables. -/

public section

namespace StepSparsify

open Finset Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Top ClauseBound.TopN UniformInK SparsificationLemma
open Groundwork.Sparsify (PFml leaves round)

/-- Deleting the clauses that contain a variable together with its negation does not change the
number of satisfying assignments. -/
theorem cntN_noTaut (n : ℕ) (ψ : PFml) : cntN n (noTaut ψ) = cntN n ψ := by
  unfold cntN
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (stNoTaut ψ).1 (ext a)

/-- Deleting clauses does not make the formula longer. -/
theorem length_noTaut_le (ψ : PFml) : (noTaut ψ).length ≤ ψ.length := List.length_filter_le _ _

/-- The walk returns the number of satisfying assignments, if the thresholds serve, `val` is right
on every node that has the properties of a leaf, and the pad suffices for the rounds and the stack. -/
theorem stWalkCountG : StWalkCountG := by
  intro Θ Lc hS k s n φ pad val hk h3 hs a3 a4 hvalx
  have hnilψ : hasNil (Decode.toN φ) = true ↔ [] ∈ φ := by
    rw [← Decode.nil_mem_toN]
    simp [hasNil, List.any_eq_true]
  by_cases hnil : [] ∈ φ
  · rw [hnilψ.2 hnil, cond_true, CountTop.numSat_of_nil hnil]
  · have hn' : hasNil (Decode.toN φ) = false := by
      rw [← Bool.not_eq_true]; exact fun h => hnil (hnilψ.1 h)
    rw [hn', cond_false]
    have hm : φ.length ≤ inLen k n := by
      have h := DecodeK.length_enc k φ
      have h' := DecodeK.length_enc_succ_le (φ := φ) h3
      have hB : 0 < k * (Nat.log2 (2 * n) + 1) := Nat.mul_pos hk (Nat.succ_pos _)
      have := Nat.le_mul_of_pos_right φ.length hB
      unfold inLen
      omega
    obtain ⟨m, hmdef⟩ : ∃ m, m = inLen k n := ⟨_, rfl⟩
    rw [← hmdef] at hm a4
    have hψ0 : IsKCNF k n (Decode.toN φ) := by
      intro D hD'
      obtain ⟨⟨C, hC, hl⟩, h⟩ := Decode.mem_toN hD'
      refine ⟨?_, hl ▸ h3.1 C hC, h⟩
      rintro rfl
      exact hnil ((Decode.nil_mem_toN φ).1 hD')
    have hcnt : cntN n (noTaut (Decode.toN φ)) = SatK.numSat φ := by rw [cntN_noTaut, stCntToN n φ]
    have hψl0 : (noTaut (Decode.toN φ)).length ≤ m := (length_noTaut_le _).trans (by rw [Decode.length_toN]; exact hm)
    have hψne0 : IsKCNF k n (noTaut (Decode.toN φ)) := (stNoTaut _).2.1 k n hψ0
    have hψnt0 : ∀ C ∈ noTaut (Decode.toN φ), ∀ l ∈ C, (l.1, !l.2) ∉ C := (stNoTaut _).2.2
    obtain ⟨ψ, hψ⟩ : ∃ ψ : PFml, ψ = noTaut (Decode.toN φ) := ⟨_, rfl⟩
    rw [← hψ] at hcnt hψl0 hψne0 hψnt0 ⊢
    obtain ⟨t1, t2, t3, t4⟩ := hS.tree k n s hk hs ψ hψne0 hψnt0
    obtain ⟨θ, hθ⟩ : ∃ θ, θ = Θ k s := ⟨_, rfl⟩
    obtain ⟨τ, hτ⟩ : ∃ τ, τ = tauOf s := ⟨_, rfl⟩
    rw [← hθ, ← hτ] at t1 t2 t3 t4
    rw [← hθ]
    rw [← hτ] at a4
    obtain ⟨r, hr⟩ : ∃ r, r = rootC (List.replicate n (), ψ) := ⟨_, rfl⟩
    rw [← hr] at t1 t2 t3 t4 ⊢
    obtain ⟨L, hL⟩ : ∃ L, L = leaves (stepC θ k) (bsumU τ k * n) r := ⟨_, rfl⟩
    have hleaf : ∀ x ∈ leaves (stepC θ k) (bsumU τ k * n) r, stepC θ k x = none := fun x hx => (t2 x hx).1
    have hval : ∀ x ∈ L, val x = cntN n (leafF x) := by
      intro x hx
      obtain ⟨-, hxl, hx1, ho, hs'⟩ := t2 x (hL ▸ hx)
      exact hvalx x hxl hx1 ho hs'
    have hsum : (L.map val).sum = SatK.numSat φ := by
      rw [List.map_congr_left hval, ← hcnt, t3, hL]
    rw [← hL] at t1
    rw [stWalkSG θ k pad val r (bsumU τ k * n) hleaf (by rw [← hL]; omega) fun i => ?_, ← hL, hsum]
    refine le_trans ?_ a4
    obtain ⟨s1, s2⟩ := t4 i
    have hc : ((roundS (stepC θ k) val)^[i] ([r], 0)).2 < 2 ^ (n + 1) := by
      have h1 := iterate_le_sum stRoundSEnd (stepC θ k) val (bsumU τ k * n) r hleaf i
      rw [← hL, hsum] at h1
      have h2 := CountTop.numSat_le φ
      have h4 : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have e := stRoundS _ (stepC θ k) val i [r] []
    rw [List.map_nil, List.sum_nil] at e
    rw [e] at hc ⊢
    exact stStateLenU k τ n m _ _ s1 (fun x hx => ⟨(s2 x hx).1.trans (Nat.mul_le_mul_right _ hψl0), (s2 x hx).2⟩) hc

end StepSparsify
