/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.RecursionDefs
public import ClauseBound.Gen.Rate
import Mathlib.Tactic

/-! # The crude bounds

Proof of Theorem A (b), the step from ℓ to ℓ + 1: crude bounds give L ≤ N + 1, B' ≤ N + g²B₁, g(P +
B₁) ≤ Ξ^{c+4} and K(L + B') ≤ Ξ^{c+5}. Here N = g⁴λ, P = g³λ, B₁ = gB + g²(2λ)^c, B' = ⌈2gP/K⌉ +
g²B₁, Ξ = g²(λ + B).
* `crude_plain`: the last three, for all numbers 3 ≤ K ≤ g and every L ≤ N + 1. With s = λ + B: each
  of the three terms of g(P + B₁) is at most Ξ^c·g⁴s, and 3 ≤ g⁴s³; each of the five terms of g(2N +
  1 + g²B₁) is at most Ξ^c·g⁵s, and 5 ≤ g⁵s⁴.
* `crudeBounds : CrudeBounds`: at K = K_ℓ, g = g_ℓ. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-- B' ≤ N + g²B₁: ⌈2N/K⌉ ≤ N. -/
theorem crude_first (K g lam B₁ : ℕ) (hK : 3 ≤ K) (hg : 3 ≤ g) (hlam : 1 ≤ lam) : bitsOut K g (g ^ 3 * lam) B₁ ≤ g ^ 4 * lam + g ^ 2 * B₁ := by
  have hN : 2 ≤ g ^ 4 * lam := by
    have h1 : 3 ^ 4 ≤ g ^ 4 := Nat.pow_le_pow_left hg 4
    nlinarith
  unfold bitsOut
  refine Nat.add_le_add_right (Nat.div_le_of_le_mul ?_) _
  have e : g * (g ^ 3 * lam) = g ^ 4 * lam := by ring
  rw [e]
  generalize g ^ 4 * lam = N at hN ⊢
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 3 := ⟨K - 3, by omega⟩
  have h := Nat.mul_le_mul_left (k + 1) hN
  change 2 * N + (k + 2) ≤ (k + 3) * N
  nlinarith

/-- g(P + B₁) in plain variables: s is λ + B, T is (2λ)^c, E is Ξ^c. -/
theorem crude_second (g lam B s T E : ℕ) (hg : 3 ≤ g) (hl : lam ≤ s) (hB : B ≤ s) (hs : 2 ≤ s) (hT : T ≤ E) (hE : 1 ≤ E) :
    g * (g ^ 3 * lam + (g * B + g ^ 2 * T)) ≤ E * (g ^ 2 * s) ^ 4 := by
  have hg1 : 1 ≤ g := by omega
  have t1 : g ^ 4 * lam ≤ E * (g ^ 4 * s) := (Nat.mul_le_mul_left _ hl).trans (Nat.le_mul_of_pos_left _ hE)
  have t2 : g ^ 2 * B ≤ E * (g ^ 4 * s) := (Nat.mul_le_mul (Nat.pow_le_pow_right hg1 (by norm_num)) hB).trans (Nat.le_mul_of_pos_left _ hE)
  have t3 : g ^ 3 * T ≤ E * (g ^ 4 * s) := by
    calc g ^ 3 * T ≤ g ^ 4 * s * E := Nat.mul_le_mul ((Nat.pow_le_pow_right hg1 (by norm_num)).trans (Nat.le_mul_of_pos_right _ (by omega))) hT
      _ = E * (g ^ 4 * s) := Nat.mul_comm _ _
  have big : 3 ≤ g ^ 4 * s ^ 3 := by
    calc 3 ≤ 3 ^ 4 * 2 ^ 3 := by norm_num
      _ ≤ g ^ 4 * s ^ 3 := Nat.mul_le_mul (Nat.pow_le_pow_left hg 4) (Nat.pow_le_pow_left hs 3)
  calc g * (g ^ 3 * lam + (g * B + g ^ 2 * T)) = g ^ 4 * lam + g ^ 2 * B + g ^ 3 * T := by ring
    _ ≤ 3 * (E * (g ^ 4 * s)) := by omega
    _ ≤ g ^ 4 * s ^ 3 * (E * (g ^ 4 * s)) := Nat.mul_le_mul_right _ big
    _ = E * (g ^ 2 * s) ^ 4 := by ring

/-- g(2N + 1 + g²B₁) in plain variables. -/
theorem crude_third (g lam B s T E : ℕ) (hg : 3 ≤ g) (hl : lam ≤ s) (hB : B ≤ s) (hs : 2 ≤ s) (hT : T ≤ E) (hE : 1 ≤ E) :
    g * (g ^ 4 * lam + 1 + (g ^ 4 * lam + g ^ 2 * (g * B + g ^ 2 * T))) ≤ E * (g ^ 2 * s) ^ 5 := by
  have hg1 : 1 ≤ g := by omega
  have u1 : g ^ 5 * lam ≤ E * (g ^ 5 * s) := (Nat.mul_le_mul_left _ hl).trans (Nat.le_mul_of_pos_left _ hE)
  have u2 : g ≤ E * (g ^ 5 * s) :=
    ((Nat.le_self_pow (by norm_num) g).trans (Nat.le_mul_of_pos_right _ (by omega))).trans (Nat.le_mul_of_pos_left _ hE)
  have u3 : g ^ 4 * B ≤ E * (g ^ 5 * s) := (Nat.mul_le_mul (Nat.pow_le_pow_right hg1 (by norm_num)) hB).trans (Nat.le_mul_of_pos_left _ hE)
  have u4 : g ^ 5 * T ≤ E * (g ^ 5 * s) := by
    calc g ^ 5 * T ≤ g ^ 5 * s * E := Nat.mul_le_mul (Nat.le_mul_of_pos_right _ (by omega)) hT
      _ = E * (g ^ 5 * s) := Nat.mul_comm _ _
  have big : 5 ≤ g ^ 5 * s ^ 4 := by
    calc 5 ≤ 3 ^ 5 * 2 ^ 4 := by norm_num
      _ ≤ g ^ 5 * s ^ 4 := Nat.mul_le_mul (Nat.pow_le_pow_left hg 5) (Nat.pow_le_pow_left hs 4)
  calc g * (g ^ 4 * lam + 1 + (g ^ 4 * lam + g ^ 2 * (g * B + g ^ 2 * T))) = g ^ 5 * lam + g ^ 5 * lam + g + g ^ 4 * B + g ^ 5 * T := by ring
    _ ≤ 5 * (E * (g ^ 5 * s)) := by omega
    _ ≤ g ^ 5 * s ^ 4 * (E * (g ^ 5 * s)) := Nat.mul_le_mul_right _ big
    _ = E * (g ^ 2 * s) ^ 5 := by ring

/-- The crude bounds for all numbers 3 ≤ K ≤ g. -/
theorem crude_plain (c K g lam B L : ℕ) (hK : 3 ≤ K) (hKg : K ≤ g) (hlam : 1 ≤ lam) (hB : 1 ≤ B) (hL : L ≤ g ^ 4 * lam + 1) :
    bitsOut K g (g ^ 3 * lam) (bitsOne c g lam B) ≤ g ^ 4 * lam + g ^ 2 * bitsOne c g lam B ∧
    g * (g ^ 3 * lam + bitsOne c g lam B) ≤ Xi g lam B ^ (c + 4) ∧
    K * (L + bitsOut K g (g ^ 3 * lam) (bitsOne c g lam B)) ≤ Xi g lam B ^ (c + 5) := by
  have hg : 3 ≤ g := hK.trans hKg
  have h1 := crude_first K g lam (bitsOne c g lam B) hK hg hlam
  have hX : 2 * lam ≤ g ^ 2 * (lam + B) := Nat.mul_le_mul ((by norm_num : 2 ≤ 3 ^ 2).trans (Nat.pow_le_pow_left hg 2)) (Nat.le_add_right _ _)
  have hT : (2 * lam) ^ c ≤ (g ^ 2 * (lam + B)) ^ c := Nat.pow_le_pow_left hX c
  have hE : 1 ≤ (g ^ 2 * (lam + B)) ^ c := Nat.one_le_pow _ _ (by omega)
  refine ⟨h1, ?_, ?_⟩
  · unfold Xi bitsOne
    rw [pow_add]
    exact crude_second g lam B (lam + B) _ _ hg (Nat.le_add_right _ _) (Nat.le_add_left _ _) (by omega) hT hE
  · refine (Nat.mul_le_mul hKg (Nat.add_le_add hL h1)).trans ?_
    unfold Xi bitsOne
    rw [pow_add]
    exact crude_third g lam B (lam + B) _ _ hg (Nat.le_add_right _ _) (Nat.le_add_left _ _) (by omega) hT hE

/-- **Crude bounds give L ≤ N + 1, B' ≤ N + g²B₁, g(P + B₁) ≤ Ξ^{c+4} and K(L + B') ≤ Ξ^{c+5}**: the
last three, for every L ≤ N + 1. -/
theorem crudeBounds : CrudeBounds := by
  intro c x₀ l lam B L hx hlam hB hL
  have hK := ClauseBound.Gen.Rate.big_le_K hx l
  exact crude_plain c _ _ lam B L (by omega) (ClauseBound.Gen.Rate.K_le_g x₀ l) hlam hB hL

end ExplicitCost
