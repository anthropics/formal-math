/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Rec.Blocks
public import ClauseBound.Rec.Tail

/-! # The mean number of blocks with an odd number of entries 11

For a label β on n positions that are cut into δ blocks, odd(β) is the number of blocks with an odd
number of entries 11, and μ is the mean of odd(β) over all β, rounded down.
This file shows 2μ ≤ δ (`two_mul_mu_le`) and a closed form of μ (`mu_eq`).

A label is the family of its parts in the blocks, so odd(β) is the number of marked places of a
choice of one element from each of δ finite sets, where the marked elements of
the set of block b are the labels on b with an odd number of entries 11. At most half of the labels
on a block are marked, which gives the bound on the mean.
The auxiliary statements are in the namespace `ClauseBound.Rec.CountRow`. -/

public section

namespace ClauseBound.Rec

open Finset Polynomial Pieces

namespace CountRow

/-! ### The mean of the number of marked places -/

section Product

variable {δ : ℕ} (Ω : Fin δ → Type) [∀ b, Fintype (Ω b)] [∀ b, Nonempty (Ω b)] [∀ b, DecidableEq (Ω b)] (S : ∀ b, Finset (Ω b))

/-- The share of the choices that are marked at the place b is |S b|/|Ω b|. -/
theorem card_marked (b : Fin δ) :
    (#{ω : ∀ b, Ω b | ω b ∈ S b} : ℝ) = (Fintype.card (∀ b, Ω b) : ℝ) * ((#(S b) : ℝ) / Fintype.card (Ω b)) := by
  have h1 : #{ω : ∀ b, Ω b | ω b ∈ S b} = #(S b) * Fintype.card (∀ j : {j // j ≠ b}, Ω j) := by
    rw [← Finset.card_univ (α := ∀ j : {j // j ≠ b}, Ω j), ← Finset.card_product,
      ← Finset.card_map (Equiv.piSplitAt b Ω).toEmbedding]
    congr 1
    ext ⟨a, g⟩
    simp [Finset.mem_map_equiv]
  have h2 : Fintype.card (∀ b, Ω b) = Fintype.card (Ω b) * Fintype.card (∀ j : {j // j ≠ b}, Ω j) := by
    rw [Fintype.card_congr (Equiv.piSplitAt b Ω), Fintype.card_prod]
  have hc : (0 : ℝ) < Fintype.card (Ω b) := by exact_mod_cast Fintype.card_pos
  rw [h1, h2]
  push_cast
  field_simp

/-- The sum of the number of marked places over all choices is the number of choices times Σ_b |S
b|/|Ω b|. -/
theorem sum_marked :
    ∑ ω : ∀ b, Ω b, (#{b | ω b ∈ S b} : ℝ) = (Fintype.card (∀ b, Ω b) : ℝ) * ∑ b, (#(S b) : ℝ) / Fintype.card (Ω b) := by
  have h (ω : ∀ b, Ω b) : (#{b | ω b ∈ S b} : ℝ) = ∑ b, if ω b ∈ S b then (1 : ℝ) else 0 := (Finset.sum_boole _ _).symm
  rw [Finset.sum_congr rfl fun ω _ => h ω, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_boole, card_marked]

end Product

/-! ### At most half of the labels on a set of positions have an odd number of entries 11 -/

/-- The product of the signs of a label is −1 if the number of entries 11 is odd, and 1 otherwise. -/
theorem prod_sg {ι : Type} [Fintype ι] (γ : ι → Bool × Bool) :
    ∏ k, sg (γ k) = if Odd #{k | γ k = (true, true)} then -1 else 1 := by
  have h : ∏ k, sg (γ k) = (-1) ^ #{k | γ k = (true, true)} := by
    unfold sg
    rw [Finset.prod_ite]
    simp
  rw [h]
  split_ifs with ho
  · exact ho.neg_one_pow
  · exact (Nat.not_odd_iff_even.1 ho).neg_one_pow

/-- On a set of N positions, twice the number of labels with an odd number of entries 11, plus 2^N,
is the number of all labels. -/
theorem two_mul_card_odd_add (ι : Type) [Fintype ι] [DecidableEq ι] :
    2 * #{γ : ι → Bool × Bool | Odd #{k | γ k = (true, true)}} + 2 ^ Fintype.card ι = Fintype.card (ι → Bool × Bool) := by
  have h1 : ∑ γ : ι → Bool × Bool, ∏ k, sg (γ k) = 2 ^ Fintype.card ι := by
    have h0 : ∑ e : Bool × Bool, sg e = 2 := by decide
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ => univ) fun _ e => sg e]
    simp [h0]
  have h2 : ∑ γ : ι → Bool × Bool, ∏ k, sg (γ k)
      = (Fintype.card (ι → Bool × Bool) : ℤ) - 2 * #{γ : ι → Bool × Bool | Odd #{k | γ k = (true, true)}} := by
    have h (γ : ι → Bool × Bool) : ∏ k, sg (γ k) = 1 - 2 * if Odd #{k | γ k = (true, true)} then (1 : ℤ) else 0 := by
      rw [prod_sg]; split_ifs <;> norm_num
    rw [Finset.sum_congr rfl fun γ _ => h γ, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
    simp
  rw [h2] at h1
  have h3 : ((2 * #{γ : ι → Bool × Bool | Odd #{k | γ k = (true, true)}} + 2 ^ Fintype.card ι : ℕ) : ℤ)
      = (Fintype.card (ι → Bool × Bool) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast h3

/-- Twice the number of labels with an odd number of entries 11 is at most the number of all labels. -/
theorem two_mul_card_odd_le (ι : Type) [Fintype ι] [DecidableEq ι] :
    2 * #{γ : ι → Bool × Bool | Odd #{k | γ k = (true, true)}} ≤ Fintype.card (ι → Bool × Bool) :=
  (Nat.le_add_right _ _).trans (two_mul_card_odd_add ι).le

/-! ### A label as a choice of one label on every block -/

variable {n h : ℕ}

/-- The labels on block b with an odd number of entries 11. -/
def oddSet (n h : ℕ) (b : Fin (nblk n h)) : Finset (BLab n h b) := {γ | Odd #{k | γ k = (true, true)}}

/-- The mean of odd(β) over all β. -/
noncomputable def mean (n h : ℕ) : ℝ := ∑ b, (#(oddSet n h b) : ℝ) / Fintype.card (BLab n h b)

/-- The number of entries 11 of β in block b, counted in the part of β in that block. -/
theorem card_blk_filter (hh : 1 ≤ h) (β : Lab n) (b : Fin (nblk n h)) :
    #{k ∈ blk n h b.val | β k = (true, true)} = #{k | split hh β b k = (true, true)} := by
  simp only [split_apply]
  have h1 : ({k : {k : Fin n // k.val / h = b.val} | β k.1 = (true, true)} : Finset _)
      = ({k : Fin n | β k = (true, true)} : Finset _).subtype fun k => k.val / h = b.val := by
    ext k; simp
  rw [h1, Finset.card_subtype, blk, Finset.filter_filter, Finset.filter_filter]
  congr 1
  ext k
  simp [and_comm]

/-- odd(β) is the number of blocks in which the part of β is marked. -/
theorem odd_eq (hh : 1 ≤ h) (β : Lab n) : odd h β = #{b | split hh β b ∈ oddSet n h b} := by
  unfold odd oddSet
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [mem_filter, mem_univ, true_and, card_blk_filter hh]

/-- There are 4^n labels. -/
theorem card_lab (n : ℕ) : Fintype.card (Lab n) = 4 ^ n := by
  rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]

/-- There are 4^n choices of one label on every block. -/
theorem card_choices (hh : 1 ≤ h) : Fintype.card (∀ b : Fin (nblk n h), BLab n h b) = 4 ^ n := by
  rw [← Fintype.card_congr (split hh), card_lab]

/-- The sum of odd(β) over all β is 4^n times the mean. -/
theorem sum_odd (n : ℕ) (hh : 1 ≤ h) : ((∑ β : Lab n, odd h β : ℕ) : ℝ) = 4 ^ n * mean n h := by
  have h1 := sum_marked (fun b : Fin (nblk n h) => BLab n h b) (oddSet n h)
  rw [card_choices hh, ← Equiv.sum_comp (split hh)] at h1
  push_cast at h1 ⊢
  rw [mean, ← h1]
  exact Finset.sum_congr rfl fun β _ => by rw [odd_eq hh]

/-- μ is at most the mean. -/
theorem mu_le_mean (n : ℕ) (hh : 1 ≤ h) : (mu n h : ℝ) ≤ mean n h := by
  have h1 : (mu n h : ℝ) ≤ ((∑ β : Lab n, odd h β : ℕ) : ℝ) / ((4 ^ n : ℕ) : ℝ) := Nat.cast_div_le
  rw [sum_odd n hh] at h1
  push_cast at h1
  rwa [mul_div_cancel_left₀ _ (by positivity)] at h1

/-- The mean is below μ + 1. -/
theorem mean_lt (n : ℕ) (hh : 1 ≤ h) : mean n h < mu n h + 1 := by
  have h1 : (∑ β : Lab n, odd h β) < 4 ^ n * (mu n h + 1) := Nat.lt_mul_div_succ _ (by positivity)
  have h2 : ((∑ β : Lab n, odd h β : ℕ) : ℝ) < ((4 ^ n * (mu n h + 1) : ℕ) : ℝ) := by exact_mod_cast h1
  rw [sum_odd n hh] at h2
  push_cast at h2
  exact lt_of_mul_lt_mul_left h2 (by positivity)

/-- The mean is at most δ/2. -/
theorem mean_le (n h : ℕ) : mean n h ≤ (nblk n h : ℝ) / 2 := by
  have h1 (b : Fin (nblk n h)) : (#(oddSet n h b) : ℝ) / Fintype.card (BLab n h b) ≤ 1 / 2 := by
    have h2 : 2 * #(oddSet n h b) ≤ Fintype.card (BLab n h b) := two_mul_card_odd_le _
    have h3 : (2 : ℝ) * #(oddSet n h b) ≤ Fintype.card (BLab n h b) := by exact_mod_cast h2
    have hc : (0 : ℝ) < Fintype.card (BLab n h b) := by exact_mod_cast Fintype.card_pos
    rw [div_le_div_iff₀ hc (by norm_num)]
    linarith
  calc mean n h ≤ ∑ _b : Fin (nblk n h), (1 / 2 : ℝ) := Finset.sum_le_sum fun b _ => h1 b
    _ = (nblk n h : ℝ) / 2 := by simp; ring

/-- The share of the marked labels on a block of N ≤ h positions is (1 − 2^{−N})/2, written with the
denominator 2^{h+1}. -/
theorem share_eq (hh : 1 ≤ h) (b : Fin (nblk n h)) :
    (#(oddSet n h b) : ℝ) / Fintype.card (BLab n h b)
      = (((2 ^ #(blk n h b.val) - 1) * 2 ^ (h - #(blk n h b.val)) : ℕ) : ℝ) / ((2 ^ (h + 1) : ℕ) : ℝ) := by
  have e0 : Fintype.card {k : Fin n // k.val / h = b.val} = #(blk n h b.val) := Fintype.card_subtype _
  have e1 : 2 * #(oddSet n h b) + 2 ^ #(blk n h b.val) = Fintype.card (BLab n h b) := by
    rw [← e0]
    exact two_mul_card_odd_add _
  have e3 : #(blk n h b.val) ≤ h := card_blk_le hh _
  rw [card_BLab b] at e1
  rw [card_BLab b]
  generalize #(blk n h b.val) = N at e1 e3
  generalize #(oddSet n h b) = s at e1
  have c1 : ((2 ^ N - 1 : ℕ) : ℝ) = 2 ^ N - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    ring
  have c2 : (2 : ℝ) ^ (h + 1) = 2 * (2 ^ (h - N) * 2 ^ N) := by
    rw [← pow_add, Nat.sub_add_cancel e3, pow_succ]
    ring
  have c3 : (4 : ℝ) ^ N = (2 ^ N) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have e1' : 2 * (s : ℝ) + 2 ^ N = (2 ^ N) ^ 2 := by
    rw [← c3]
    exact_mod_cast e1
  rw [Nat.cast_mul, c1]
  push_cast
  rw [c2, c3]
  have ha : (0 : ℝ) < 2 ^ N := by positivity
  have hc : (0 : ℝ) < 2 ^ (h - N) := by positivity
  generalize (2 : ℝ) ^ N = a at e1' ha
  generalize (2 : ℝ) ^ (h - N) = c at hc
  have hs : (s : ℝ) = (a ^ 2 - a) / 2 := by linarith
  rw [hs, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- The mean with the denominator 2^{h+1}. -/
theorem mean_eq (n : ℕ) (hh : 1 ≤ h) :
    mean n h = ((∑ b ∈ range (nblk n h), (2 ^ #(blk n h b) - 1) * 2 ^ (h - #(blk n h b)) : ℕ) : ℝ) / ((2 ^ (h + 1) : ℕ) : ℝ) := by
  rw [Finset.sum_range, Nat.cast_sum, Finset.sum_div, mean]
  exact Finset.sum_congr rfl fun b _ => share_eq hh b

end CountRow

open CountRow

variable {n h : ℕ}

/-- 2μ ≤ δ. -/
theorem two_mul_mu_le (n : ℕ) (hh : 1 ≤ h) : 2 * mu n h ≤ nblk n h := by
  have h1 := (mu_le_mean n hh).trans (mean_le n h)
  have h2 : ((2 * mu n h : ℕ) : ℝ) ≤ (nblk n h : ℝ) := by push_cast; linarith
  exact_mod_cast h2

/-- μ in closed form: the sum of (2^{n_b} − 1)·2^{h − n_b} over the blocks b, where n_b is the
number of positions of b, divided by 2^{h+1} and rounded down. -/
theorem mu_eq (n : ℕ) (hh : 1 ≤ h) :
    mu n h = (∑ b ∈ range (nblk n h), (2 ^ #(blk n h b) - 1) * 2 ^ (h - #(blk n h b))) / 2 ^ (h + 1) := by
  have h1 := mu_le_mean n hh
  have h2 := mean_lt n hh
  rw [mean_eq n hh] at h1 h2
  have h3 := (Nat.floor_eq_iff (by positivity)).2 ⟨h1, h2⟩
  rw [Nat.floor_div_eq_div] at h3
  exact h3.symm

end ClauseBound.Rec
