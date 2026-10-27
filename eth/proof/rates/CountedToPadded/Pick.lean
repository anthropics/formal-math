/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedToPadded.Defs
import PaddedDescent.F.FuelCert
import ToTuring.Lib.List2

/-! # The program that picks the level

Proof of `PickOfFacts` (Defs.lean). The list of the entries that `kf` finds is followed from ℓ = 0
upwards: after the first m numbers its last entry belongs to the largest ℓ < m with K_ℓ within the
bound. -/

public section

namespace QueryMachines.Bridge.Proof

open Groundwork Groundwork.PolyT PaddedDescent.F Printed CliqueLevels

/-- A list of units is its length in unary. -/
theorem eq_unary (b : U) : b = unary b.length := List.eq_replicate_of_mem fun _ _ => rfl

/-- The first ℓ units of b are ℓ in unary, for ℓ within the length of b. -/
theorem take_unary (b : U) {l : ℕ} (h : l ≤ b.length) : b.take l = unary l := by
  rw [eq_unary (b.take l), List.length_take, min_eq_left h]

/-- K_ℓ ≥ ℓ + 2. -/
theorem add_two_le_K {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ} (hL : Levels K e C₀) : ∀ l : ℕ, l + 2 ≤ K l
  | 0 => hL.K_two 0
  | l + 1 => by have := add_two_le_K hL l; have := hL.K_lt l; omega

/-- The entry for ℓ: (ℓ, (ℓ, K_ℓ)), all in unary, if `kf` finds K_ℓ within the bound b; else
nothing. -/
@[expose] def cand (kf : U × U → Option U) (b : U) (l : ℕ) : Option (U × (U × U)) := (kf (b.take l, b)).map fun k => (b.take l, (b.take l, k))

/-- The entry for ℓ within the length of b, by what `kf` computes. -/
theorem cand_eq {K : ℕ → ℕ} {kf : U × U → Option U} (hk : ComputesLevels K kf) (b : U) {l : ℕ} (h : l ≤ b.length) :
    cand kf b l = if K l ≤ b.length then some (unary l, (unary l, unary (K l))) else none := by
  unfold cand
  rw [take_unary b h]
  conv_lhs => rw [eq_unary b]
  rw [hk.2 l b.length]
  split <;> rfl

/-- The last entry among the first m + 1 numbers is that of m, if there is one, else the last among
the first m. -/
theorem last_succ (kf : U × U → Option U) (b : U) (m : ℕ) :
    ((List.range (m + 1)).filterMap (cand kf b)).getLast? = (cand kf b m).or ((List.range m).filterMap (cand kf b)).getLast? := by
  rw [List.range_succ, List.filterMap_append]
  cases h : cand kf b m with
  | none => simp [h]
  | some y => simp [h]

/-- After the first m numbers: nothing, if no K_ℓ with ℓ < m is within the bound; else the entry of
the largest such ℓ. -/
theorem last_spec {K : ℕ → ℕ} {kf : U × U → Option U} (hk : ComputesLevels K kf) (b : U) : ∀ m : ℕ, m ≤ b.length + 1 →
    (((List.range m).filterMap (cand kf b)).getLast? = none ∧ ∀ l < m, b.length < K l) ∨
    ∃ l < m, ((List.range m).filterMap (cand kf b)).getLast? = some (unary l, (unary l, unary (K l))) ∧ K l ≤ b.length ∧ ∀ l', l < l' → l' < m → b.length < K l' := by
  intro m
  induction m with
  | zero => intro _; exact Or.inl ⟨rfl, fun l h => absurd h (Nat.not_lt_zero l)⟩
  | succ m ih =>
    intro hm
    rw [last_succ, cand_eq hk b (by omega : m ≤ b.length)]
    by_cases hK : K m ≤ b.length
    · rw [if_pos hK]
      exact Or.inr ⟨m, Nat.lt_succ_self m, rfl, hK, fun l' h1 h2 => by omega⟩
    · rw [if_neg hK]
      rcases ih (by omega) with ⟨h1, h2⟩ | ⟨l, hl, h1, h2, h3⟩
      · refine Or.inl ⟨by rw [h1]; rfl, fun l hl => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | rfl
        · exact h2 l h
        · omega
      · refine Or.inr ⟨l, by omega, by rw [h1]; rfl, h2, fun l' g1 g2 => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 g2 with h | rfl
        · exact h3 l' g1 h
        · omega

/-- The program, written with `cand`. -/
theorem pickOf_eq (kf : U × U → Option U) (K₀ : ℕ) (b : U) : pickOf kf K₀ b = (((List.range (b.length + 1)).filterMap (cand kf b)).getLast?).getD ([], ([], unary K₀)) := rfl

end QueryMachines.Bridge.Proof

namespace QueryMachines.Bridge

open Groundwork Groundwork.PolyT PaddedDescent.F Printed CliqueLevels Proof

/-- The program that picks the level is polynomial-time and returns the index of the largest level
within the bound. -/
theorem pickOfFacts : PickOfFacts := by
  intro K e C₀ kf hL hk
  refine ⟨?_, fun b => ?_⟩
  · have := hk.1
    unfold pickOf; fun_prop
  · rw [pickOf_eq]
    rcases last_spec hk b (b.length + 1) le_rfl with ⟨h1, h2⟩ | ⟨l, hl, h1, h2, h3⟩
    · rw [h1]
      have h0 := h2 0 (Nat.succ_pos _)
      have h01 := hL.K_lt 0
      refine ⟨rfl, fun h => ?_, ?_⟩
      · omega
      · show b.length < K (0 + 1)
        omega
    · rw [h1]
      have e1 : (unary l).length = l := List.length_replicate
      simp only [Option.getD_some, e1]
      refine ⟨trivial, fun _ => h2, ?_⟩
      by_cases h : l + 1 < b.length + 1
      · exact h3 (l + 1) (Nat.lt_succ_self l) h
      · have := add_two_le_K hL (l + 1); omega

end QueryMachines.Bridge
