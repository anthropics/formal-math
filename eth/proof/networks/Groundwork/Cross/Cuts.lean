/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import NetworkStatements
public import Groundwork.Cross.Bit

/-! The pieces A_i of the decomposition of the crossing bit by bit, a variant that the paper does
not state (Section 4 of the paper uses blocks of three bits): A_i factors across rows through the
strings with at least i singlets, and across
columns through the strings with at most i states other than Φ⁺. Here the factorisations are over ℤ
with no factor 2^λ: in
place of the (orthogonal) Bell basis we use a basis of integer vectors that contains the singlet (rows)
or Φ⁺ (columns),
and its dual basis. The label sets `rowLabels` and `colLabels`, and hence the numbers of bits of the
two factorisations, are those of this bit-by-bit decomposition. These are the factorisations the
networks use. -/

@[expose] public section

namespace Groundwork

open Finset

/-- Three tables for a cut of one bit. They are meant to factor the two one-bit functions that are
multiplied out, D⁰ (here I)
and D¹ (here −s⊗s): D⁰ = Σ_h top_h ⊗ bot0_h and D¹ = Σ_h top_h ⊗ bot1_h. The structure does not ask
this: it is the hypothesis of
`BitCut.expand`, and `A_rows`, `A_cols` check it for the tables `rowBit`, `colBit`. -/
structure BitCut where
  top : Bell → Bool → Bool → ℤ
  bot0 : Bell → Bool → Bool → ℤ
  bot1 : Bell → Bool → Bool → ℤ

/-- The part of a string β on the first side of the cut. -/
def BitCut.Top (c : BitCut) {n : ℕ} (β : Fin n → Bell) (p q : Bits n) : ℤ := ∏ k, c.top (β k) (p k) (q k)

/-- The part of a string β on the second side of the cut, for the term with i factors D¹. -/
def BitCut.Bot (c : BitCut) {n : ℕ} (i : ℕ) (β : Fin n → Bell) (p q : Bits n) : ℤ :=
  ∑ S ∈ powersetCard i (univ : Finset (Fin n)),
    (∏ k ∈ S, c.bot1 (β k) (p k) (q k)) * ∏ k ∈ Sᶜ, c.bot0 (β k) (p k) (q k)

/-- [p = a][q = b]. -/
def ind (a b p q : Bool) : ℤ := if p = a ∧ q = b then 1 else 0

/-- Rows, cut (x,y | u,v). Basis e₀₀, e₁₁, e₁₀, s named Φ⁺, Φ⁻, Ψ⁺, singlet; dual basis e₀₀, e₁₁,
[u≠v], e₀₁. -/
def rowBit : BitCut where
  top h p q := match h with
    | (false, false) => ind false false p q
    | (false, true) => ind true true p q
    | (true, false) => ind true false p q
    | (true, true) => s p q
  bot0 h p q := match h with
    | (false, false) => ind false false p q
    | (false, true) => ind true true p q
    | (true, false) => if p = q then 0 else 1
    | (true, true) => ind false true p q
  bot1 h p q := match h with
    | (true, true) => -s p q
    | _ => 0

/-- Columns, cut (x,u | y,v). Basis φ = e₀₀+e₁₁, e₁₁, e₀₁, e₁₀ named Φ⁺, Φ⁻, Ψ⁺, singlet. -/
def colBit : BitCut where
  top h p q := match h with
    | (false, false) => if p = q then 1 else 0
    | (false, true) => ind true true p q
    | (true, false) => ind false true p q
    | (true, true) => ind true false p q
  bot0 h p q := match h with
    | (false, false) => if p = q then 1 else 0
    | _ => 0
  bot1 h p q := match h with
    | (false, false) => -ind true true p q
    | (false, true) => ind true true p q - ind false false p q
    | (true, false) => ind true false p q
    | (true, true) => ind false true p q

/-- A product over S times a product over the complement of S, as one product over all positions. -/
theorem prod_mul_prod_compl_eq_ite {n : ℕ} (S : Finset (Fin n)) (g1 g0 : Fin n → ℤ) :
    (∏ k ∈ S, g1 k) * ∏ k ∈ Sᶜ, g0 k = ∏ k, if k ∈ S then g1 k else g0 k := by
  rw [← prod_mul_prod_compl S]
  congr 1
  · exact prod_congr rfl fun k hk => by rw [if_pos hk]
  · exact prod_congr rfl fun k hk => by rw [if_neg (mem_compl.1 hk)]

/-- Multiplying out: one lemma for both cuts (and for the Bell basis). a, b are the two ends on one
side, c', d those
on the other. -/
theorem BitCut.expand (c : BitCut) (D0 D1 : Bool → Bool → Bool → Bool → ℤ)
    (h0 : ∀ a b c' d, D0 a b c' d = ∑ h, c.top h a b * c.bot0 h c' d)
    (h1 : ∀ a b c' d, D1 a b c' d = ∑ h, c.top h a b * c.bot1 h c' d) {n : ℕ} (i : ℕ) (a b c' d : Bits n) :
    ∑ S ∈ powersetCard i (univ : Finset (Fin n)),
        (∏ k ∈ S, D1 (a k) (b k) (c' k) (d k)) * ∏ k ∈ Sᶜ, D0 (a k) (b k) (c' k) (d k)
      = ∑ β : Fin n → Bell, c.Top β a b * c.Bot i β c' d := by
  simp only [BitCut.Top, BitCut.Bot, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun S _ => ?_
  have h : ∀ k, (if k ∈ S then D1 (a k) (b k) (c' k) (d k) else D0 (a k) (b k) (c' k) (d k))
      = ∑ h, c.top h (a k) (b k) * (if k ∈ S then c.bot1 h (c' k) (d k) else c.bot0 h (c' k) (d k)) := by
    intro k
    split_ifs
    · exact h1 _ _ _ _
    · exact h0 _ _ _ _
  simp only [prod_mul_prod_compl_eq_ite, ← prod_mul_distrib]
  simp_rw [h]
  rw [prod_univ_sum, Fintype.piFinset_univ]

/-- With fewer than i singlets in β, every set of i positions has one where β is no singlet, and the
term vanishes. -/
theorem rowBot_eq_zero {n i : ℕ} {β : Fin n → Bell} (h : singlets β < i) (p q : Bits n) : rowBit.Bot i β p q = 0 := by
  have hz : ∀ h : Bell, h ≠ (true, true) → ∀ p q, rowBit.bot1 h p q = 0 := by decide
  refine sum_eq_zero fun S hS => ?_
  have hc := (mem_powersetCard.1 hS).2
  have hex : ∃ k ∈ S, β k ≠ (true, true) := by
    by_contra hcon
    push Not at hcon
    have hsub : S ⊆ univ.filter fun k => β k = (true, true) := fun k hk => by simp [hcon k hk]
    have := card_le_card hsub
    unfold singlets at h
    omega
  obtain ⟨k, hk, hne⟩ := hex
  rw [prod_eq_zero hk (hz _ hne _ _), zero_mul]

/-- With more than i states other than Φ⁺ in β, every set of i positions misses one of them, and the
term vanishes. -/
theorem colBot_eq_zero {n i : ℕ} {β : Fin n → Bell} (h : i < others β) (p q : Bits n) : colBit.Bot i β p q = 0 := by
  have hz : ∀ h : Bell, h ≠ (false, false) → ∀ p q, colBit.bot0 h p q = 0 := by decide
  refine sum_eq_zero fun S hS => ?_
  have hc := (mem_powersetCard.1 hS).2
  have hex : ∃ k ∈ Sᶜ, β k ≠ (false, false) := by
    by_contra hcon
    push Not at hcon
    have hsub : (univ.filter fun k => β k ≠ (false, false)) ⊆ S := fun k hk => by
      by_contra hkS
      exact (mem_filter.1 hk).2 (hcon k (mem_compl.2 hkS))
    have := card_le_card hsub
    unfold others at h
    omega
  obtain ⟨k, hk, hne⟩ := hex
  rw [prod_eq_zero hk (hz _ hne _ _), mul_zero]

/-- Across rows, over ℤ: A_i factors through the strings with at least i singlets. -/
theorem A_rows (n i : ℕ) (x y u v : Bits n) :
    A n i x y u v = ∑ β ∈ rowLabels n i, rowBit.Top β x y * rowBit.Bot i β u v := by
  have h := rowBit.expand (fun a b c' d => I₁ a b c' d) (fun a b c' d => -(s a b * s c' d))
    (by decide) (by decide) i x y u v
  refine (h.trans (sum_subset (subset_univ _) fun β _ hβ => ?_).symm)
  rw [rowBot_eq_zero (by simpa [rowLabels] using hβ), mul_zero]

/-- Across columns, over ℤ: A_i factors through the strings with at most i states other than Φ⁺. -/
theorem A_cols (n i : ℕ) (x y u v : Bits n) :
    A n i x y u v = ∑ β ∈ colLabels n i, colBit.Top β x u * colBit.Bot i β y v := by
  have h := colBit.expand (fun a b c' d => I₁ a c' b d) (fun a b c' d => -(s a c' * s b d))
    (by decide) (by decide) i x u y v
  refine (h.trans (sum_subset (subset_univ _) fun β _ hβ => ?_).symm)
  rw [colBot_eq_zero (by simpa [colLabels] using hβ), mul_zero]

/-- Across rows, the factors on the first side of the cut are 0 or ±1. -/
theorem abs_rowTop_le {n : ℕ} (β : Fin n → Bell) (p q : Bits n) : |rowBit.Top β p q| ≤ 1 := by
  have h : ∀ (h : Bell) (p q : Bool), |rowBit.top h p q| ≤ 1 := by decide
  exact abs_prod_le_one _ _ fun k => h _ _ _

/-- Across columns, the factors on the first side of the cut are 0 or ±1. -/
theorem abs_colTop_le {n : ℕ} (β : Fin n → Bell) (p q : Bits n) : |colBit.Top β p q| ≤ 1 := by
  have h : ∀ (h : Bell) (p q : Bool), |colBit.top h p q| ≤ 1 := by decide
  exact abs_prod_le_one _ _ fun k => h _ _ _

/-- Across rows, the factors on the second side of the cut have absolute value at most 2^λ. -/
theorem abs_rowBot_le {n : ℕ} (i : ℕ) (β : Fin n → Bell) (p q : Bits n) : |rowBit.Bot i β p q| ≤ 2 ^ n := by
  have h1 : ∀ (h : Bell) (p q : Bool), |rowBit.bot1 h p q| ≤ 1 := by decide
  have h0 : ∀ (h : Bell) (p q : Bool), |rowBit.bot0 h p q| ≤ 1 := by decide
  exact abs_sum_powersetCard_le i _ _ (fun k => h1 _ _ _) fun k => h0 _ _ _

/-- Across columns, the factors on the second side of the cut have absolute value at most 2^λ. -/
theorem abs_colBot_le {n : ℕ} (i : ℕ) (β : Fin n → Bell) (p q : Bits n) : |colBit.Bot i β p q| ≤ 2 ^ n := by
  have h1 : ∀ (h : Bell) (p q : Bool), |colBit.bot1 h p q| ≤ 1 := by decide
  have h0 : ∀ (h : Bell) (p q : Bool), |colBit.bot0 h p q| ≤ 1 := by decide
  exact abs_sum_powersetCard_le i _ _ (fun k => h1 _ _ _) fun k => h0 _ _ _

end Groundwork
