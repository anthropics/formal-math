/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.PatternValues
import Mathlib.Tactic

/-! # «Definition 2 holds with B₁ = gB + g²(2λ)^c in the role of B»

Proof of Theorem A (b): in the display of c_{a,a'} we have c^row_{ι(q)} ≤ 2λ, so P = g³λ, gP = N,
and moreover c_{a,a'} ≤ g²λ = P/g; by Definition 7 (c), Definition 2 holds with B₁ = gB + g²(2λ)^c
in the role of B.
* `pattern_c_le`: c_{a,a'} ≤ g²λ;
* `abs_weight_lt`, `abs_factor_lt`, `abs_pair_lt`: all values are below 2^{B₁}, strictly: a weight
  is a product of g entries below 2^B; the other values do not depend on the tables, so the bound
  for tables that are 0 (`sized_zero`) applies to them; the bound then holds with room to spare,
  since gB ≥ 1;
* `pattern_is`: the network is a network with the parameters P = g³λ and B₁. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

/-- «c_{a,a'} ≤ g²λ». -/
theorem pattern_c_le (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) (a b : Fin (nParts g g tr)) : (patternNet D c g tr lam y W).c a b ≤ g ^ 2 * lam := by
  have h := gridN_c_le (cutsOK_piecesOf hS hlam [()]) g g tr y (fun w θ => W w.val (List.ofFn θ).flatten) a b
  rw [nMemb_self] at h
  exact h.trans (le_of_eq (by change g ^ 2 * (1 * lam) = _; rw [Nat.one_mul]))

/-- The network for tables that are 0: its sizes, from `gridN_sized`. -/
theorem sized_zero (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) :
    (gridN (piecesOf D c) [()] g g tr 0 lam y fun _ _ => 0).Sized (1 * (nParts g g tr * nMemb g g tr ^ 2 * lam)) (nMemb g g tr * 0 + nMemb g g tr ^ 2 * (2 * lam) ^ c) :=
  gridN_sized (cutsOK_piecesOf hS hlam [()]) g g tr y (B := 0) fun _ _ _ _ => by simp

/-- 2^{g²(2λ)^c} is below 2^{B₁}. -/
theorem pow_lt_bitsOne (hg : 1 ≤ g) (hB : 1 ≤ B) : (2 : ℤ) ^ (nMemb g g tr * 0 + nMemb g g tr ^ 2 * (2 * lam) ^ c) < 2 ^ bitsOne c g lam B := by
  refine pow_lt_pow_right₀ (by norm_num) ?_
  rw [nMemb_self]
  unfold bitsOne
  have : 1 ≤ g * B := Nat.mul_pos hg hB
  omega

/-- |f_{a,a'}| < 2^{B₁}. -/
theorem abs_factor_lt (hS : Setting ρ c x₀ D) (hg : 1 ≤ g) (hlam : 1 ≤ lam) (hB : 1 ≤ B) {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z θ : List Bool}
    (hz : z.length = nMemb g g tr * (g * g) * lam) (hθ : θ.length = capG (piecesOf D c) g g tr 0 lam y a b) : |(patternNet D c g tr lam y W).f a b z θ| < 2 ^ bitsOne c g lam B := by
  have e : (patternNet D c g tr lam y W).f a b z θ = (gridN (piecesOf D c) [()] g g tr 0 lam y fun _ _ => 0).f a b z θ :=
    (gridN_f (piecesOf D c) [()] g g tr 0 lam y _ hab hz hθ).trans (gridN_f (piecesOf D c) [()] g g tr 0 lam y _ hab hz hθ).symm
  rw [e]
  exact ((sized_zero hS hlam).abs_f a b z θ).trans_lt (pow_lt_bitsOne hg hB)

/-- Ψ is the sum over θ ∈ {0,1}^{c_{a,a'}} of the products of the two functions of the
factorization. -/
theorem pair_fact {a b : Fin (nParts g g tr)} (hab : a ≠ b) (z z' : List Bool) :
    (patternNet D c g tr lam y W).Ψ a b z z' = ∑ θ ∈ words ((patternNet D c g tr lam y W).c a b), (patternNet D c g tr lam y W).f a b z θ * (patternNet D c g tr lam y W).f b a z' θ := by
  change (gridOf D c g tr lam y W).Ψ a b z z' = _
  unfold Network.Ψ
  rw [gridN_lab _ _ _ _ _ _ _ _ _ hab, c_eq hab]
  rfl

/-- |Ψ_{a,a'}| < 2^{B₁}. -/
theorem abs_pair_lt (hS : Setting ρ c x₀ D) (hg : 1 ≤ g) (hlam : 1 ≤ lam) (hB : 1 ≤ B) {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z z' : List Bool}
    (hz : z.length = nMemb g g tr * (g * g) * lam) (hz' : z'.length = nMemb g g tr * (g * g) * lam) : |(patternNet D c g tr lam y W).Ψ a b z z'| < 2 ^ bitsOne c g lam B := by
  have e : (patternNet D c g tr lam y W).Ψ a b z z' = (patternNet D c g tr lam y fun _ _ => 0).Ψ a b z z' := by
    rw [pair_fact hab, pair_fact hab, c_eq hab, c_eq hab]
    refine Finset.sum_congr rfl fun θ hθ => ?_
    have hθ' : θ.length = capG (piecesOf D c) g g tr 0 lam y b a := by
      rw [mem_words.1 hθ]
      unfold capG
      rw [min_comm, max_comm]
    rw [factor_eq hab hz (mem_words.1 hθ), factor_eq hab.symm hz' hθ', factor_eq hab hz (mem_words.1 hθ), factor_eq hab.symm hz' hθ']
  rw [e]
  exact ((sized_zero hS hlam).abs_Ψ a b z z' hab).trans_lt (pow_lt_bitsOne hg hB)

/-- |W_a| < 2^{B₁}: a product of g entries below 2^B. -/
theorem abs_weight_lt (hg : 1 ≤ g) (hlam : 1 ≤ lam) (hW : ∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B) (a : Fin (nParts g g tr)) {z : List Bool}
    (hz : z.length = nMemb g g tr * (g * g) * lam) : |(patternNet D c g tr lam y W).W a z| < 2 ^ bitsOne c g lam B := by
  have h1 : |(patternNet D c g tr lam y W).W a z| ≤ (2 ^ B) ^ g := by
    rw [weight_eq a hz]
    split_ifs
    · rw [Finset.abs_prod]
      refine (Finset.prod_le_prod (g := fun _ => (2 : ℤ) ^ B) (fun i _ => abs_nonneg _) fun i hi => ?_).trans (le_of_eq ?_)
      · obtain ⟨q1, q2⟩ := pointQuery_ok a hz (Finset.mem_range.1 hi)
        exact (hW _ q1 _ (mem_words.2 q2)).le
      · rw [Finset.prod_const, Finset.card_range, nMemb_self]
    · rw [abs_zero]
      positivity
  refine h1.trans_lt ?_
  rw [← pow_mul]
  refine pow_lt_pow_right₀ (by norm_num) ?_
  unfold bitsOne
  have : 1 ≤ g ^ 2 * (2 * lam) ^ c := Nat.mul_pos (by positivity) (by positivity)
  rw [Nat.mul_comm B g]
  omega

/-- **The network is a network with the parameters P = g³λ and B₁ = gB + g²(2λ)^c.** -/
theorem pattern_is (hS : Setting ρ c x₀ D) (hg : 1 ≤ g) (hlam : 1 ≤ lam) (hB : 1 ≤ B) (hW : ∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B) :
    (patternNet D c g tr lam y W).Is (g ^ 3 * lam) (bitsOne c g lam B) where
  P_pos := Nat.mul_pos (by positivity) hlam
  B_pos := by
    unfold bitsOne
    have : 1 ≤ g * B := Nat.mul_pos hg hB
    omega
  len_S a z hz := by
    rw [(mem_S_iff a z).1 hz, nMemb_self]
    change _ = g ^ 3 * lam
    ring
  len_le _ := le_rfl
  Ψ_symm a b _ z _ z' _ := Network.Ψ_comm (gridOf D c g tr lam y W) b a z' z
  c_symm a b := (sized_zero (y := y) hS hlam).c_symm a b
  fact a b hab z _ z' _ := pair_fact hab z z'
  i a := by
    refine ((sized_zero (y := y) hS hlam).sum_c a).trans (le_of_eq ?_)
    rw [nMemb_self, nParts_self]
    ring
  ii_W a z hz := abs_weight_lt hg hlam hW a ((mem_S_iff a z).1 hz)
  ii_Ψ a b hab z hz z' hz' := abs_pair_lt hS hg hlam hB hab ((mem_S_iff a z).1 hz) ((mem_S_iff b z').1 hz')
  ii_f a b hab z hz θ hθ := abs_factor_lt hS hg hlam hB hab ((mem_S_iff a z).1 hz) ((mem_words.1 hθ).trans (c_eq hab))

end ExplicitCost
