/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.TopN.Defs
import all CountKSatRate.Top
import all CountKSat.Top.Count

/-! # The walk through the counting tree, for any way to count a leaf

`stWalkCount : StWalkCount`. The proof takes as hypotheses a statement on `val` at the leaves, the
threshold τ and the two budgets of the walk. -/

namespace ClauseBound.TopN

open Finset Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Top
open Groundwork.Sparsify (PFml leaves round)
open WidthK (theta bsum leafC)

/-- The walk returns the number of satisfying assignments, if `val` is right at the leaves and the
pad suffices for the rounds and the stack. -/
public theorem stWalkCount (hT : StTreeK) (hW : StWalkS) (hR : StRoundS) (hE : StRoundSEnd) (hSL : StStateLen) (hN : StCntToN) (hD : StDecU) : StWalkCount := by
  intro k τ n φ pad val hk h3 hτk a3 a4 hvalx
  have hdec : decU k (SatK.enc k φ) = (List.replicate n (), Decode.toN φ) := hD k n φ hk h3.1
  have hnilψ : hasNil (Decode.toN φ) = true ↔ [] ∈ φ := by
    rw [← Decode.nil_mem_toN]
    simp [hasNil, List.any_eq_true]
  simp only [hdec]
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
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Fml, ψ = Decode.toN φ := ⟨_, rfl⟩
    rw [← hψ]
    have hψl : ψ.length ≤ m := by rw [hψ, Decode.length_toN]; exact hm
    have hψne : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := by
      intro D hD'
      obtain ⟨⟨C, hC, hl⟩, h⟩ := Decode.mem_toN (hψ ▸ hD')
      refine ⟨?_, hl ▸ h3.1 C hC, h⟩
      rintro rfl
      exact hnil ((Decode.nil_mem_toN φ).1 (hψ ▸ hD'))
    obtain ⟨t1, t2, t3, t4⟩ := hT k τ n hk hτk ψ hψne
    obtain ⟨r, hr⟩ : ∃ r, r = rootC (List.replicate n (), ψ) := ⟨_, rfl⟩
    rw [← hr] at t1 t2 t3 t4 ⊢
    obtain ⟨L, hL⟩ : ∃ L, L = leaves (stepC (theta τ) k) (bsum τ k * n) r := ⟨_, rfl⟩
    have hleaf : ∀ x ∈ leaves (stepC (theta τ) k) (bsum τ k * n) r, stepC (theta τ) k x = none := fun x hx => (t2 x hx).1
    have hval : ∀ x ∈ L, val x = cntN n (leafF x) := by
      intro x hx
      obtain ⟨-, hxl, hx1, ho, hs'⟩ := t2 x (hL ▸ hx)
      exact hvalx x hxl hx1 ho hs'
    have hsum : (L.map val).sum = SatK.numSat φ := by
      rw [List.map_congr_left hval, ← hN n φ, ← hψ, t3, hL]
    rw [← hL] at t1
    rw [hW k pad τ val r (bsum τ k * n) hleaf (by rw [← hL]; omega) fun i => ?_, ← hL, hsum]
    refine le_trans ?_ a4
    obtain ⟨s1, s2⟩ := t4 i
    have hc : ((roundS (stepC (theta τ) k) val)^[i] ([r], 0)).2 < 2 ^ (n + 1) := by
      have h1 := iterate_le_sum hE (stepC (theta τ) k) val (bsum τ k * n) r hleaf i
      rw [← hL, hsum] at h1
      have h2 := CountTop.numSat_le φ
      have h4 : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have e := hR _ (stepC (theta τ) k) val i [r] []
    rw [List.map_nil, List.sum_nil] at e
    rw [e] at hc ⊢
    exact hSL k τ n m _ _ s1 (fun x hx => ⟨(s2 x hx).1.trans (Nat.mul_le_mul_right _ hψl), (s2 x hx).2⟩) hc

end ClauseBound.TopN
