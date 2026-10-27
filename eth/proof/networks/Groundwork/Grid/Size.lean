/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Groundwork.Grid.RowNet
public import Groundwork.Grid.Expand

/-! Counts for one level of the recursion, for the network in which the rows of the grid are merged:
its size is g³λ; its bits are the g²(g−1)λ of the vertical
edges plus what the rectangles cost, each rectangle counted twice; and bounds on the magnitudes of
its functions. -/

@[expose] public section

namespace Groundwork.Grid

open Finset

/-! ### Helpers -/

/-- An indicator is 0 or 1. -/
private theorem abs_boole_le (p : Prop) [Decidable p] : |if p then (1 : ℤ) else 0| ≤ 1 := by
  split_ifs <;> simp

/-- A product of integers of absolute value at most 2^B. -/
private theorem abs_prod_le_pow {ι : Type} (s : Finset ι) (f : ι → ℤ) (B : ℕ) (h : ∀ i ∈ s, |f i| ≤ 2 ^ B) :
    |∏ i ∈ s, f i| ≤ 2 ^ (#s * B) := by
  calc |∏ i ∈ s, f i| = ∏ i ∈ s, |f i| := abs_prod _ _
    _ ≤ ∏ _i ∈ s, (2 : ℤ) ^ B := prod_le_prod (fun _ _ => abs_nonneg _) h
    _ = 2 ^ (#s * B) := by rw [prod_const, ← pow_mul, Nat.mul_comm]

/-- Factors 0, ±1 times factors of absolute value at most 2^b. -/
private theorem abs_mul_prod_le {ι κ : Type} (s : Finset ι) (e : ι → ℤ) (t : Finset κ) (f : κ → ℤ) {b m : ℕ}
    (he : ∀ i, |e i| ≤ 1) (hf : ∀ k, |f k| ≤ 2 ^ b) (hm : #t * b ≤ m) :
    |(∏ i ∈ s, e i) * ∏ k ∈ t, f k| ≤ 2 ^ m := by
  rw [abs_mul]
  calc |∏ i ∈ s, e i| * |∏ k ∈ t, f k| ≤ 1 * 2 ^ (#t * b) :=
        mul_le_mul (abs_prod_le_one s e he) (abs_prod_le_pow t f b fun k _ => hf k) (abs_nonneg _) zero_le_one
    _ = 2 ^ (#t * b) := one_mul _
    _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm

/-- A sum of numbers that are at most c is at most their number times c. -/
private theorem sum_le_card_mul {ι : Type} (s : Finset ι) (f : ι → ℕ) (c : ℕ) (h : ∀ i ∈ s, f i ≤ c) :
    ∑ i ∈ s, f i ≤ #s * c :=
  (Finset.sum_le_sum h).trans (Finset.sum_const_nat fun _ _ => rfl).le

/-- 2·#{a < b} = g(g−1). -/
private theorem two_mul_pairs (X : Type) [Fintype X] [LinearOrder X] :
    2 * #(pairs X) = Fintype.card X * (Fintype.card X - 1) := by
  rw [card_pairs, Nat.choose_two_right, Nat.mul_div_cancel' (even_iff_two_dvd.1 (Nat.even_mul_pred_self _))]

/-- There are at most g² pairs of columns. -/
private theorem card_lt_le {g : ℕ} (X : Type) [Fintype X] [LinearOrder X] (hX : Fintype.card X = g) :
    #(univ.filter fun k : X × X => k.1 < k.2) ≤ g ^ 2 :=
  (card_le_univ _).trans_eq (by rw [Fintype.card_prod, hX, sq])

/-- gL + (at most 2mL for each rectangle of two rows) ≤ g²mL. -/
private theorem cap_bound {g L m : ℕ} (hm : 1 ≤ m) (X : Type) [Fintype X] [LinearOrder X] (hX : Fintype.card X = g)
    (F : X × X → ℕ) (hF : ∀ k, F k ≤ 2 * m * L) :
    g * L + ∑ k : X × X with k.1 < k.2, F k ≤ g ^ 2 * (m * L) := by
  have h1 : ∑ k : X × X with k.1 < k.2, F k ≤ #(pairs X) * (2 * m * L) := sum_le_card_mul _ _ _ fun k _ => hF k
  have h2 := two_mul_pairs X
  rw [hX] at h2
  have h3 : #(pairs X) * (2 * m * L) = g * (g - 1) * (m * L) := by rw [← h2]; ring
  rw [h3] at h1
  have h4 : g * L ≤ g * (m * L) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hm)
  refine (Nat.add_le_add h4 h1).trans (le_of_eq ?_)
  clear h1 h2 h3 h4 hX
  rcases g with _ | n
  · simp
  · simp only [Nat.add_sub_cancel]; ring

/-- A sum over the g − 1 other elements of numbers that are at most g²c is at most g³c. -/
private theorem sum_erase_le {g c : ℕ} (X : Type) [Fintype X] [DecidableEq X] (hX : Fintype.card X = g) (F : X → ℕ)
    (hF : ∀ b, F b ≤ g ^ 2 * c) (a : X) : ∑ b ∈ univ.erase a, F b ≤ g ^ 3 * c := by
  refine (sum_le_card_mul _ _ _ fun b _ => hF b).trans ?_
  rw [Finset.card_erase_of_mem (mem_univ a), Finset.card_univ, hX, ← Nat.mul_assoc]
  refine Nat.mul_le_mul_right _ ?_
  calc (g - 1) * g ^ 2 ≤ g * g ^ 2 := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ = g ^ 3 := by ring

/-- A sum over ordered pairs of distinct elements of a function of the unordered pair counts each
pair a < b twice. -/
private theorem sum_erase_eq {X : Type} [Fintype X] [LinearOrder X] (h : X × X → ℕ) :
    ∑ a, ∑ b ∈ univ.erase a, h (min a b, max a b) = 2 * ∑ p ∈ pairs X, h p := by
  have h0 : ∀ a b : X, (if b ≠ a then h (min a b, max a b) else 0) =
      (if a < b then h (a, b) else 0) + (if b < a then h (b, a) else 0) := by
    intro a b
    rcases lt_trichotomy a b with hab | hab | hab
    · simp [hab, hab.ne', hab.le, not_lt.2 hab.le]
    · simp [hab]
    · simp [hab, hab.ne, hab.le, not_lt.2 hab.le]
  have h1 : ∑ p ∈ pairs X, h p = ∑ a, ∑ b, if a < b then h (a, b) else 0 := by
    rw [pairs, Finset.sum_filter, Fintype.sum_prod_type]
  have h2 : ∑ a : X, ∑ b : X, (if b < a then h (b, a) else 0) = ∑ a, ∑ b, if a < b then h (a, b) else 0 :=
    Finset.sum_comm
  calc ∑ a, ∑ b ∈ univ.erase a, h (min a b, max a b)
      = ∑ a, ∑ b, if b ≠ a then h (min a b, max a b) else 0 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.filter_ne' univ a, Finset.sum_filter]
    _ = 2 * ∑ p ∈ pairs X, h p := by
        simp only [h0, Finset.sum_add_distrib]
        rw [h2, h1, two_mul]

variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- A row has g·g² half-edges. -/
private theorem card_state {g L : ℕ} (hρ : Fintype.card ρ = g) (hγ : Fintype.card γ = g) (hα : Fintype.card α = 2 ^ L) :
    Fintype.card (RowSt ρ γ α) = 2 ^ (g ^ 3 * L) := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_prod, hα, hρ, hγ, ← pow_mul, ← pow_mul]
  congr 1
  ring

omit [DecidableEq α] in
/-- The number of labels of two rows. -/
private theorem card_labels_le {g L : ℕ} (hγ : Fintype.card γ = g) (hα : Fintype.card α = 2 ^ L)
    (S : γ × γ → Finset τ) (e : γ × γ → ℕ) (h : ∀ k, #(S k) ≤ 2 ^ e k) (t₀ : τ) :
    #((univ : Finset (γ → α)) ×ˢ tuples (fun k : γ × γ => k.1 < k.2) S t₀) ≤
      2 ^ (g * L + ∑ k : γ × γ with k.1 < k.2, e k) := by
  rw [card_product, card_univ, Fintype.card_fun, hα, hγ, ← pow_mul, card_tuples, pow_add, ← prod_pow_eq_pow_sum,
    Nat.mul_comm L g]
  exact Nat.mul_le_mul_left _ (prod_le_prod (fun _ _ => Nat.zero_le _) fun k _ => h k)

omit [Fintype α] [DecidableEq α] in
/-- A sum over the rectangles of the transposed grid. -/
theorem sum_Ω_swap (F : Rect ρ γ → ℕ) : ∑ ω ∈ Ω γ ρ, F (ω.2, ω.1) = ∑ ω ∈ Ω ρ γ, F ω := by
  refine Finset.sum_nbij' (fun ω => (ω.2, ω.1)) (fun ω => (ω.2, ω.1)) ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl
  · intro ω hω
    simp only [Ω, mem_filter, mem_univ, true_and] at hω ⊢
    exact ⟨hω.2, hω.1⟩
  · intro ω hω
    simp only [Ω, mem_filter, mem_univ, true_and] at hω ⊢
    exact ⟨hω.2, hω.1⟩

omit [Fintype α] [DecidableEq α] in
/-- 4R ≤ g⁴. -/
theorem four_mul_card_Ω_le {g : ℕ} (hρ : Fintype.card ρ = g) (hγ : Fintype.card γ = g) : 4 * #(Ω ρ γ) ≤ g ^ 4 := by
  rw [card_Ω hρ hγ]
  have h : 2 * g.choose 2 ≤ g ^ 2 := by
    rw [Nat.choose_two_right]
    calc 2 * (g * (g - 1) / 2) ≤ g * (g - 1) := Nat.mul_div_le _ _
      _ ≤ g * g := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = g ^ 2 := (sq g).symm
  calc 4 * g.choose 2 ^ 2 = (2 * g.choose 2) ^ 2 := by ring
    _ ≤ (g ^ 2) ^ 2 := Nat.pow_le_pow_left h 2
    _ = g ^ 4 := by ring

/-! ### The row network -/

/-- Two rows have capacity at most g²mL if every rectangle is charged at most 2mL bits. -/
theorem rowNet_c_le {g L m : ℕ} (hm : 1 ≤ m) (hγ : Fintype.card γ = g) (R : Inst (ρ × γ) α) (C : Rect ρ γ → Cut α τ)
    (t₀ : τ) (hcap : ∀ ω, (C ω).cap ≤ 2 * m * L) (a b : ρ) : (rowNet R C t₀ L).c a b ≤ g ^ 2 * (m * L) := by
  simp only [rowNet, hγ]
  exact cap_bound hm γ hγ _ fun k => hcap _

/-- The shape of the row network when every rectangle is charged at most 2mL bits, m ≥ 1. -/
theorem rowNet_shaped' {g L m : ℕ} (hm : 1 ≤ m) (hρ : Fintype.card ρ = g) (hγ : Fintype.card γ = g)
    (hα : Fintype.card α = 2 ^ L) (R : Inst (ρ × γ) α) (C : Rect ρ γ → Cut α τ) (t₀ : τ)
    (hcard : ∀ ω, #(C ω).lab ≤ 2 ^ (C ω).cap) (hcap : ∀ ω, (C ω).cap ≤ 2 * m * L) :
    (rowNet R C t₀ L).Shaped (m * (g ^ 3 * L)) where
  card_S a := by
    simp only [rowNet, Finset.card_univ]
    rw [card_state hρ hγ hα]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ hm)
  c_symm a b := by simp only [rowNet, min_comm, max_comm]
  sum_c a := by
    rw [Nat.mul_left_comm]
    exact sum_erase_le ρ hρ _ (fun b => rowNet_c_le hm hγ R C t₀ hcap a b) a
  card_lab a b hab := by
    simp only [Network.lab, rowNet, if_pos (min_lt_max.2 hab), rowΘ, hγ]
    exact card_labels_le hγ hα _ _ (fun k => hcard _) t₀

/-- The interaction of two rows is a product of at most g² values of the functions at the
rectangles. -/
private theorem abs_rowNet_Ψ_lt {g L b m : ℕ} (hγ : Fintype.card γ = g) (R : Inst (ρ × γ) α)
    {G : Rect ρ γ → α → α → α → α → ℤ} (C : Rect ρ γ → Cut α τ) (t₀ : τ) (hF : ∀ ω, (C ω).Factors (G ω))
    (hG : ∀ ω x y u v, |G ω x y u v| ≤ 2 ^ b) (hm : g ^ 2 * b ≤ m) {a c : ρ} (h : a < c) (z z' : RowSt ρ γ α) :
    |(rowNet R C t₀ L).Ψ a c z z'| ≤ 2 ^ m := by
  rw [rowNet_Ψ hF R t₀ L h]
  exact abs_mul_prod_le _ _ _ _ (fun _ => abs_boole_le _) (fun _ => hG _ _ _ _ _)
    ((Nat.mul_le_mul_right _ (card_lt_le γ hγ)).trans hm)

/-- The shape and the magnitudes of the row network when every rectangle is charged at most 2mL
bits, m ≥ 1. -/
theorem rowNet_sized' {g L m B b : ℕ} (hm : 1 ≤ m) (hρ : Fintype.card ρ = g) (hγ : Fintype.card γ = g)
    (hα : Fintype.card α = 2 ^ L) (R : Inst (ρ × γ) α) (hR : ∀ w h, |R w h| ≤ 2 ^ B)
    {G : Rect ρ γ → α → α → α → α → ℤ} (C : Rect ρ γ → Cut α τ) (t₀ : τ)
    (hF : ∀ ω, (C ω).Factors (G ω)) (hcard : ∀ ω, #(C ω).lab ≤ 2 ^ (C ω).cap) (hcap : ∀ ω, (C ω).cap ≤ 2 * m * L)
    (htop : ∀ ω x y θ, |(C ω).top x y θ| ≤ 2 ^ b) (hbot : ∀ ω u v θ, |(C ω).bot u v θ| ≤ 2 ^ b)
    (hG : ∀ ω x y u v, |G ω x y u v| ≤ 2 ^ b) :
    (rowNet R C t₀ L).Sized (m * (g ^ 3 * L)) (g * B + g ^ 2 * b) where
  toShaped := rowNet_shaped' hm hρ hγ hα R C t₀ hcard hcap
  abs_W a z := by
    simp only [rowNet, rowW]
    rw [mul_comm]
    refine abs_mul_prod_le _ _ _ _ (fun _ => abs_boole_le _) (fun _ => hR _ _) ?_
    rw [Finset.card_univ, hγ]
    exact Nat.le_add_right _ _
  abs_f a c z θ := by
    have hm : #(univ.filter fun k : γ × γ => k.1 < k.2) * b ≤ g * B + g ^ 2 * b :=
      (Nat.mul_le_mul_right _ (card_lt_le γ hγ)).trans (Nat.le_add_left _ _)
    simp only [rowNet]
    split_ifs
    · exact abs_mul_prod_le _ _ _ _ (fun _ => abs_boole_le _) (fun _ => htop _ _ _ _) hm
    · exact abs_mul_prod_le _ _ _ _ (fun _ => abs_boole_le _) (fun _ => hbot _ _ _ _) hm
  abs_Ψ a c z z' hac := by
    rcases lt_or_gt_of_ne hac with h | h
    · exact abs_rowNet_Ψ_lt hγ R C t₀ hF hG (Nat.le_add_left _ _) h z z'
    · rw [Network.Ψ_comm]
      exact abs_rowNet_Ψ_lt hγ R C t₀ hF hG (Nat.le_add_left _ _) h z' z

/-- U counts ordered pairs, so every rectangle counts twice. -/
theorem U_rowNet {g L : ℕ} (hρ : Fintype.card ρ = g) (hγ : Fintype.card γ = g) (R : Inst (ρ × γ) α)
    (C : Rect ρ γ → Cut α τ) (t₀ : τ) :
    (rowNet R C t₀ L).U = g ^ 2 * (g - 1) * L + 2 * ∑ ω ∈ Ω ρ γ, (C ω).cap := by
  have h := sum_erase_eq (X := ρ) fun p => Fintype.card γ * L + ∑ k : γ × γ with k.1 < k.2, (C (p, k)).cap
  rw [Network.U]
  simp only [rowNet]
  rw [h, Finset.sum_add_distrib, ← sum_Ω_rows (fun ω => (C ω).cap), Finset.sum_const, smul_eq_mul, mul_add,
    ← mul_assoc, two_mul_pairs, hρ, hγ]
  ring


omit [Fintype α] [DecidableEq α]

end Groundwork.Grid
