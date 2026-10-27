/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Prog.Side
public import StepMachines.Prog.SideBasics
public import StepMachines.Prog.GridCount

/-! One level of the recursion (Section 5): in one term of the expansion all rows or all columns
(the flag `tr`) of the g × g grid are merged, which
gives a network `sideN` on g nodes: weights W at the nodes, factors f of the interaction of every
pair. This file shows
that what sideWP and sideFP compute on bit strings are these weights and factors, and that the sizes
for the weights stay within
S + a·(size c + B + λ)^a, where a = `sideA g` and B, S are bounds assumed of the procedure of the
instance on the grid. -/

@[expose] public section

namespace Groundwork.Prog

open Finset Stepped
open Groundwork.Grid (he node c2 sideN sideCap)

/-! ### Booleans and products of indicators -/

private theorem all_range_fin (n : ℕ) (p : ℕ → Bool) : (List.range n).all p = true ↔ ∀ i : Fin n, p i = true := by
  rw [List.all_eq_true]
  exact ⟨fun h i => h i (List.mem_range.2 i.2), fun h i hi => h ⟨i, List.mem_range.1 hi⟩⟩

private theorem prod_ind_range (n : ℕ) (p : ℕ → Bool) :
    ∏ i : Fin n, (if p i = true then (1 : ℤ) else 0) = if (List.range n).all p = true then 1 else 0 := by
  rw [Finset.prod_boole]
  simp only [mem_univ, true_imp_iff, all_range_fin]

/-- The product over the counter j < g·g, with 1 off the pairs i < i', is the product over the pairs
i < i'. -/
theorem prod_counter_pairs (g : ℕ) (F : ℕ → ℕ → ℤ) :
    ∏ j ∈ range (g * g), (if j / g < j % g then F (j / g) (j % g) else 1) =
      ∏ k : Fin g × Fin g with k.1 < k.2, F k.1 k.2 := by
  rw [Finset.prod_filter, Finset.prod_range, ← Equiv.prod_comp finProdFinEquiv]
  refine Finset.prod_congr rfl ?_
  rintro ⟨a, b⟩ -
  have hg : 0 < g := a.pos
  have hy : (finProdFinEquiv (a, b)).val = b.val + g * a.val := rfl
  have h1 : (b.val + g * a.val) / g = a.val := by
    rw [Nat.add_mul_div_left _ _ hg, Nat.div_eq_of_lt b.2, Nat.zero_add]
  have h2 : (b.val + g * a.val) % g = b.val := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.2]
  rw [hy, h1, h2]
  rfl

/-! ### The weights -/

/-- The test of sideWP, spelled out. -/
theorem sideChk_iff {C : Type} {g : ℕ} {tr : Bool} {lam : C → ℕ} (x : (C × ℕ) × WQ) :
    sideChk g tr lam x = true ↔
      (∀ i : Fin g, (he g (lam x.1.1) x.2.2 i (node g tr x.2.1 i)).all (!·) = true) ∧
      ∀ q ∈ pairs (Fin g),
        he g (lam x.1.1) x.2.2 q.1 (node g tr x.2.1 q.2) = he g (lam x.1.1) x.2.2 q.2 (node g tr x.2.1 q.1) := by
  unfold sideChk
  rw [Bool.and_eq_true, all_range_fin,
    all_pairs_iff g fun i i' =>
      he g (lam x.1.1) x.2.2 i (node g tr x.2.1 i') == he g (lam x.1.1) x.2.2 i' (node g tr x.2.1 i)]
  simp only [beq_iff_eq]

/-- What sideWP computes is the weight of the network. -/
theorem sideN_W_eq {C : Type} {g : ℕ} {tr : Bool} {lam : C → ℕ} (Rm : Inst (Fin (g * g)) (List Bool)) (c : C) (y : ℕ)
    (a : Fin g) {z : List Bool} (hz : z.length = g ^ 3 * lam c) :
    (sideN g tr (lam c) Rm y).W a z = sideWv g tr (lam c) Rm (sideChk g tr lam ((c, y), (a.val, z))) a z := by
  rw [Grid.sideN_W g tr (lam c) Rm y a hz, sideWv]
  by_cases hc : sideChk g tr lam ((c, y), (a.val, z)) = true
  · obtain ⟨h1, h2⟩ := (sideChk_iff _).1 hc
    rw [if_pos hc, Finset.prod_eq_one (s := pairs (Fin g)) fun q hq => if_pos (h2 q hq), mul_one, Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [if_pos (h1 i), dif_pos (Grid.node_lt tr a.2 i.2)]
    have e : (Grid.gridE g tr).symm (a, i) = ⟨node g tr a i, Grid.node_lt tr a.2 i.2⟩ :=
      Fin.ext (Grid.gridE_symm_val g tr (a, i))
    rw [e]
    congr 1
    funext u
    simp only [sideLabels, Fin.ext_iff]
  · rw [if_neg hc]
    rw [sideChk_iff, not_and_or] at hc
    rcases hc with h | h
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Finset.prod_eq_zero (mem_univ i) (if_neg hi), zero_mul]
    · push Not at h
      obtain ⟨q, hq, hne⟩ := h
      rw [Finset.prod_eq_zero hq (if_neg hne), mul_zero]

/-! ### The factors -/

/-- The test of sideFP, as a product of indicators. -/
theorem prod_sideEdges {C : Type} {g : ℕ} {tr : Bool} {lam : C → ℕ} (x : (C × ℕ) × FQ) :
    ∏ i : Fin g,
        (if he g (lam x.1.1) x.2.2.1 i (node g tr x.2.1.2 i) = block (lam x.1.1) i x.2.2.2 then (1 : ℤ) else 0) =
      if sideEdges g tr lam x = true then 1 else 0 := by
  unfold sideEdges
  rw [← prod_ind_range]
  simp only [beq_iff_eq]

/-- What sideFP computes is the factor of the network. -/
theorem sideN_f_eq {C : Type} {g : ℕ} {tr : Bool} {lam : C → ℕ} (Rm : Inst (Fin (g * g)) (List Bool)) (c : C) (y : ℕ)
    {a b : Fin g} (hab : a ≠ b) {z θ : List Bool} (hz : z.length = g ^ 3 * lam c)
    (hθ : θ.length = sideCap g tr (lam c) y a b) :
    (sideN g tr (lam c) Rm y).f a b z θ =
      sideFv g tr (lam c) y (sideEdges g tr lam ((c, y), ((a.val, b.val), (z, θ)))) a b z θ := by
  rw [Grid.sideN_f g tr (lam c) Rm y hab hz hθ,
    prod_sideEdges (g := g) (tr := tr) (lam := lam) ((c, y), ((a.val, b.val), (z, θ))), sideFv,
    prod_counter_pairs g fun i i' => Grid.sideItem g tr (lam c) y a b z θ i i']
  split_ifs <;> simp

/-! ### The arithmetic of the bounds -/

/-- The constant a of the bounds. -/
def sideA (g : ℕ) : ℕ := 4 * g ^ 4 + 8 * g ^ 3 + 20 * g ^ 2 + 20 * g + 1000

theorem sideA_mul (g X : ℕ) :
    sideA g * X = 4 * (g ^ 4 * X) + 8 * (g ^ 3 * X) + 20 * (g ^ 2 * X) + 20 * (g * X) + 1000 * X := by
  unfold sideA; ring

/-- A size that is linear in size c + B + λ, beside S, is within the bound. -/
theorem side_size_of {g S X Z : ℕ} (h : Z ≤ S + sideA g * X) : Z ≤ S + sideA g * X ^ sideA g :=
  h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_self_pow (by unfold sideA; omega) X)) _)

/-- The size of the number y that encodes the pattern ι ∈ {0,…,n}^R of one level of the recursion,
with R = `nRect g` rectangles. -/
theorem size_pattern_le {g n y : ℕ} (hy : y < (n + 1) ^ nRect g) : size y ≤ g ^ 4 * n + 1 := by
  rw [size_nat]
  refine Nat.succ_le_succ (Nat.size_le.2 (hy.trans_le ?_))
  have hR : nRect g ≤ g ^ 4 := by
    have := GridArith.four_mul_choose_sq_le g
    unfold nRect
    omega
  calc (n + 1) ^ nRect g ≤ (2 ^ n) ^ nRect g := Nat.pow_le_pow_left Nat.lt_two_pow_self _
    _ = 2 ^ (n * nRect g) := (Nat.pow_mul 2 n _).symm
    _ ≤ 2 ^ (g ^ 4 * n) := Nat.pow_le_pow_right (by omega) (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hR)

/-- The sizes of the weights. -/
theorem side_size_W {C : Type} [HasSize C] (g B S lm : ℕ) (hl : 1 ≤ lm) (c : C) {y a : ℕ} {z : List Bool}
    (hy : y < (lm + 1) ^ nRect g) (ha : a < g) (hz : z.length = g ^ 3 * lm) :
    size ((c, y), (a, z)) + size g + (B * g + 2) + S + 3 ≤ S + sideA g * (size c + B + lm) ^ sideA g := by
  refine side_size_of ?_
  have h3 := sideA_mul g (size c + B + lm)
  have hY := size_pattern_le hy
  have e4 : g ^ 4 * (size c + B + lm) = g ^ 4 * size c + g ^ 4 * B + g ^ 4 * lm := by ring
  have e3 : g ^ 3 * (size c + B + lm) = g ^ 3 * size c + g ^ 3 * B + g ^ 3 * lm := by ring
  have e1 : g * (size c + B + lm) = g * size c + B * g + g * lm := by ring
  have hg : g ≤ g * lm := Nat.le_mul_of_pos_right _ hl
  have s1 := size_nat_le a
  have s2 := size_nat_le g
  simp only [size_prod, size_bools, hz]
  omega

end Groundwork.Prog
