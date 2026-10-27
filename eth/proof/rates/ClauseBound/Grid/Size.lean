/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Groundwork.Grid.Size

/-! # Sizes of the row network of a grid with p rows and d columns

The file proof/networks/Groundwork/Grid/Size.lean counts the rectangles of a square grid and bounds
the size of its row network. Here the same is done for a grid
whose number p of rows and number d of columns may differ:

* there are C(p,2)·C(d,2) rectangles (`card_Ω_pd`);
* two rows share at most d²·mL bits if every rectangle is charged at most 2mL bits
  (`rowNet_c_le_pd`);
* the row network is a network of size m·(p·d²·L) whose values are at most 2^(dB + d²b) in absolute
  value (`rowNet_shaped_pd`, `rowNet_sized_pd`);
* its total U, which counts ordered pairs of rows, is p(p−1)·d·L plus twice the bits charged for the
  rectangles (`U_rowNet_pd`).

L is the number of bits of a label (λ in the paper). The paper has m = 1. The column network is the
row network of the transposed grid, that is, with p and d
exchanged, so only rows are treated. -/

public section

namespace ClauseBound.Grid

open Finset Groundwork Groundwork.Grid

/-! ### Helpers -/

/-- An indicator is 0 or 1. -/
theorem abs_boole_le (q : Prop) [Decidable q] : |if q then (1 : ℤ) else 0| ≤ 1 := by
  split_ifs <;> simp

/-- A product of integers of absolute value at most 2^B. -/
theorem abs_prod_le_pow {ι : Type} (s : Finset ι) (f : ι → ℤ) (B : ℕ) (h : ∀ i ∈ s, |f i| ≤ 2 ^ B) :
    |∏ i ∈ s, f i| ≤ 2 ^ (#s * B) := by
  calc |∏ i ∈ s, f i| = ∏ i ∈ s, |f i| := abs_prod _ _
    _ ≤ ∏ _i ∈ s, (2 : ℤ) ^ B := prod_le_prod (fun _ _ => abs_nonneg _) h
    _ = 2 ^ (#s * B) := by rw [prod_const, ← pow_mul, Nat.mul_comm]

/-- Factors 0, ±1 times factors of absolute value at most 2^b. -/
theorem abs_mul_prod_le {ι κ : Type} (s : Finset ι) (e : ι → ℤ) (t : Finset κ) (f : κ → ℤ) {b n : ℕ}
    (he : ∀ i, |e i| ≤ 1) (hf : ∀ k, |f k| ≤ 2 ^ b) (hn : #t * b ≤ n) :
    |(∏ i ∈ s, e i) * ∏ k ∈ t, f k| ≤ 2 ^ n := by
  rw [abs_mul]
  calc |∏ i ∈ s, e i| * |∏ k ∈ t, f k| ≤ 1 * 2 ^ (#t * b) :=
        mul_le_mul (abs_prod_le_one s e he) (abs_prod_le_pow t f b fun k _ => hf k) (abs_nonneg _) zero_le_one
    _ = 2 ^ (#t * b) := one_mul _
    _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn

/-- A sum of numbers that are at most c is at most their number times c. -/
theorem sum_le_card_mul {ι : Type} (s : Finset ι) (f : ι → ℕ) (c : ℕ) (h : ∀ i ∈ s, f i ≤ c) :
    ∑ i ∈ s, f i ≤ #s * c :=
  (Finset.sum_le_sum h).trans (Finset.sum_const_nat fun _ _ => rfl).le

/-- Twice the number of pairs a < b of a set of n elements is n(n−1). -/
theorem two_mul_pairs (X : Type) [Fintype X] [LinearOrder X] :
    2 * #(pairs X) = Fintype.card X * (Fintype.card X - 1) := by
  rw [card_pairs, Nat.choose_two_right, Nat.mul_div_cancel' (even_iff_two_dvd.1 (Nat.even_mul_pred_self _))]

/-- There are at most d² pairs of columns. -/
theorem card_lt_le {d : ℕ} (X : Type) [Fintype X] [LinearOrder X] (hX : Fintype.card X = d) :
    #(univ.filter fun k : X × X => k.1 < k.2) ≤ d ^ 2 :=
  (card_le_univ _).trans_eq (by rw [Fintype.card_prod, hX, sq])

/-- A sum over the p − 1 other elements of numbers that are at most c is at most pc. -/
theorem sum_erase_le {p c : ℕ} (X : Type) [Fintype X] [DecidableEq X] (hX : Fintype.card X = p) (F : X → ℕ)
    (hF : ∀ b, F b ≤ c) (a : X) : ∑ b ∈ univ.erase a, F b ≤ p * c := by
  refine (sum_le_card_mul _ _ _ fun b _ => hF b).trans ?_
  rw [Finset.card_erase_of_mem (mem_univ a), Finset.card_univ, hX]
  exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)

/-- A sum over ordered pairs of distinct elements of a function of the unordered pair counts each
pair a < b twice. -/
theorem sum_erase_eq {X : Type} [Fintype X] [LinearOrder X] (h : X × X → ℕ) :
    ∑ a, ∑ b ∈ univ.erase a, h (min a b, max a b) = 2 * ∑ q ∈ pairs X, h q := by
  have h0 : ∀ a b : X, (if b ≠ a then h (min a b, max a b) else 0) =
      (if a < b then h (a, b) else 0) + (if b < a then h (b, a) else 0) := by
    intro a b
    rcases lt_trichotomy a b with hab | hab | hab
    · simp [hab, hab.ne', hab.le, not_lt.2 hab.le]
    · simp [hab]
    · simp [hab, hab.ne, hab.le, not_lt.2 hab.le]
  have h1 : ∑ q ∈ pairs X, h q = ∑ a, ∑ b, if a < b then h (a, b) else 0 := by
    rw [pairs, Finset.sum_filter, Fintype.sum_prod_type]
  have h2 : ∑ a : X, ∑ b : X, (if b < a then h (b, a) else 0) = ∑ a, ∑ b, if a < b then h (a, b) else 0 :=
    Finset.sum_comm
  calc ∑ a, ∑ b ∈ univ.erase a, h (min a b, max a b)
      = ∑ a, ∑ b, if b ≠ a then h (min a b, max a b) else 0 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.filter_ne' univ a, Finset.sum_filter]
    _ = 2 * ∑ q ∈ pairs X, h q := by
        simp only [h0, Finset.sum_add_distrib]
        rw [h2, h1, two_mul]

variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- A row has d nodes with pd half-edges each, so its states are the strings of p·d²·L bits. -/
theorem card_state_pd {p d L : ℕ} (hρ : Fintype.card ρ = p) (hγ : Fintype.card γ = d) (hα : Fintype.card α = 2 ^ L) :
    Fintype.card (RowSt ρ γ α) = 2 ^ (p * d ^ 2 * L) := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_prod, hα, hρ, hγ, ← pow_mul, ← pow_mul]
  congr 1
  ring

omit [DecidableEq α] in
/-- The number of labels of two rows. -/
theorem card_labels_le {d L : ℕ} (hγ : Fintype.card γ = d) (hα : Fintype.card α = 2 ^ L)
    (S : γ × γ → Finset τ) (e : γ × γ → ℕ) (h : ∀ k, #(S k) ≤ 2 ^ e k) (t₀ : τ) :
    #((univ : Finset (γ → α)) ×ˢ tuples (fun k : γ × γ => k.1 < k.2) S t₀) ≤
      2 ^ (d * L + ∑ k : γ × γ with k.1 < k.2, e k) := by
  rw [card_product, card_univ, Fintype.card_fun, hα, hγ, ← pow_mul, card_tuples, pow_add, ← prod_pow_eq_pow_sum,
    Nat.mul_comm L d]
  exact Nat.mul_le_mul_left _ (prod_le_prod (fun _ _ => Nat.zero_le _) fun k _ => h k)

/-! ### The rectangles -/

omit [Fintype α] [DecidableEq α] in
/-- The number of rectangles of a grid with p rows and d columns is C(p,2)·C(d,2). -/
theorem card_Ω_pd {p d : ℕ} (hρ : Fintype.card ρ = p) (hγ : Fintype.card γ = d) : #(Ω ρ γ) = p.choose 2 * d.choose 2 := by
  rw [Ω_eq_product, Finset.card_product]
  change #(pairs ρ) * #(pairs γ) = _
  rw [card_pairs, card_pairs, hρ, hγ]

/-! ### The row network -/

/-- Two rows have capacity at most d²·mL if every rectangle is charged at most 2mL bits. -/
theorem rowNet_c_le_pd {d L m : ℕ} (hm : 1 ≤ m) (hγ : Fintype.card γ = d) (R : Inst (ρ × γ) α) (C : Rect ρ γ → Cut α τ)
    (t₀ : τ) (hcap : ∀ ω, (C ω).cap ≤ 2 * m * L) (a b : ρ) : (rowNet R C t₀ L).c a b ≤ d ^ 2 * (m * L) :=
  rowNet_c_le hm hγ R C t₀ hcap a b

/-- The shape of the row network when every rectangle is charged at most 2mL bits, m ≥ 1: its size
is m·(p·d²·L). -/
theorem rowNet_shaped_pd {p d L m : ℕ} (hm : 1 ≤ m) (hρ : Fintype.card ρ = p) (hγ : Fintype.card γ = d)
    (hα : Fintype.card α = 2 ^ L) (R : Inst (ρ × γ) α) (C : Rect ρ γ → Cut α τ) (t₀ : τ)
    (hcard : ∀ ω, #(C ω).lab ≤ 2 ^ (C ω).cap) (hcap : ∀ ω, (C ω).cap ≤ 2 * m * L) :
    (rowNet R C t₀ L).Shaped (m * (p * d ^ 2 * L)) where
  card_S a := by
    simp only [rowNet, Finset.card_univ]
    rw [card_state_pd hρ hγ hα]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ hm)
  c_symm a b := by simp only [rowNet, min_comm, max_comm]
  sum_c a := by
    refine (sum_erase_le ρ hρ _ (fun b => rowNet_c_le_pd hm hγ R C t₀ hcap a b) a).trans (le_of_eq ?_)
    ring
  card_lab a b hab := by
    simp only [Network.lab, rowNet, if_pos (min_lt_max.2 hab), rowΘ, hγ]
    exact card_labels_le hγ hα _ _ (fun k => hcard _) t₀

/-- The interaction of two rows is a product of at most d² values of the functions at the
rectangles. -/
theorem abs_rowNet_Ψ_lt {d L b n : ℕ} (hγ : Fintype.card γ = d) (R : Inst (ρ × γ) α)
    {G : Rect ρ γ → α → α → α → α → ℤ} (C : Rect ρ γ → Cut α τ) (t₀ : τ) (hF : ∀ ω, (C ω).Factors (G ω))
    (hG : ∀ ω x y u v, |G ω x y u v| ≤ 2 ^ b) (hn : d ^ 2 * b ≤ n) {a c : ρ} (h : a < c) (z z' : RowSt ρ γ α) :
    |(rowNet R C t₀ L).Ψ a c z z'| ≤ 2 ^ n := by
  rw [rowNet_Ψ hF R t₀ L h]
  exact abs_mul_prod_le _ _ _ _ (fun _ => abs_boole_le _) (fun _ => hG _ _ _ _ _)
    ((Nat.mul_le_mul_right _ (card_lt_le γ hγ)).trans hn)

/-- The shape and the magnitudes of the row network when every rectangle is charged at most 2mL
bits, m ≥ 1. -/
theorem rowNet_sized_pd {p d L m B b : ℕ} (hm : 1 ≤ m) (hρ : Fintype.card ρ = p) (hγ : Fintype.card γ = d)
    (hα : Fintype.card α = 2 ^ L) (R : Inst (ρ × γ) α) (hR : ∀ w h, |R w h| ≤ 2 ^ B)
    {G : Rect ρ γ → α → α → α → α → ℤ} (C : Rect ρ γ → Cut α τ) (t₀ : τ)
    (hF : ∀ ω, (C ω).Factors (G ω)) (hcard : ∀ ω, #(C ω).lab ≤ 2 ^ (C ω).cap) (hcap : ∀ ω, (C ω).cap ≤ 2 * m * L)
    (htop : ∀ ω x y θ, |(C ω).top x y θ| ≤ 2 ^ b) (hbot : ∀ ω u v θ, |(C ω).bot u v θ| ≤ 2 ^ b)
    (hG : ∀ ω x y u v, |G ω x y u v| ≤ 2 ^ b) :
    (rowNet R C t₀ L).Sized (m * (p * d ^ 2 * L)) (d * B + d ^ 2 * b) where
  toShaped := rowNet_shaped_pd hm hρ hγ hα R C t₀ hcard hcap
  abs_W a z := by
    simp only [rowNet, rowW]
    rw [mul_comm]
    refine abs_mul_prod_le _ _ _ _ (fun _ => abs_boole_le _) (fun _ => hR _ _) ?_
    rw [Finset.card_univ, hγ]
    exact Nat.le_add_right _ _
  abs_f a c z θ := by
    have hn : #(univ.filter fun k : γ × γ => k.1 < k.2) * b ≤ d * B + d ^ 2 * b :=
      (Nat.mul_le_mul_right _ (card_lt_le γ hγ)).trans (Nat.le_add_left _ _)
    simp only [rowNet]
    split_ifs
    · exact abs_mul_prod_le _ _ _ _ (fun _ => abs_boole_le _) (fun _ => htop _ _ _ _) hn
    · exact abs_mul_prod_le _ _ _ _ (fun _ => abs_boole_le _) (fun _ => hbot _ _ _ _) hn
  abs_Ψ a c z z' hac := by
    rcases lt_or_gt_of_ne hac with h | h
    · exact abs_rowNet_Ψ_lt hγ R C t₀ hF hG (Nat.le_add_left _ _) h z z'
    · rw [Network.Ψ_comm]
      exact abs_rowNet_Ψ_lt hγ R C t₀ hF hG (Nat.le_add_left _ _) h z' z

/-- The total U of the row network: it counts ordered pairs of rows, so every vertical edge and
every rectangle counts twice. -/
theorem U_rowNet_pd {p d L : ℕ} (hρ : Fintype.card ρ = p) (hγ : Fintype.card γ = d) (R : Inst (ρ × γ) α)
    (C : Rect ρ γ → Cut α τ) (t₀ : τ) :
    (rowNet R C t₀ L).U = p * (p - 1) * d * L + 2 * ∑ ω ∈ Ω ρ γ, (C ω).cap := by
  have h := sum_erase_eq (X := ρ) fun q => Fintype.card γ * L + ∑ k : γ × γ with k.1 < k.2, (C (q, k)).cap
  rw [Network.U]
  simp only [rowNet]
  rw [h, Finset.sum_add_distrib, ← sum_Ω_rows (fun ω => (C ω).cap), Finset.sum_const, smul_eq_mul, mul_add,
    ← mul_assoc, two_mul_pairs, hρ, hγ]
  ring

end ClauseBound.Grid
