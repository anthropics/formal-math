/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Boson.WickPlus
public import ClauseBound.Boson.Basic
public import ClauseBound.Boson.Scalars
public import ClauseBound.Boson.Defs
public import ClauseBound.Boson.Dual

/-! # The matrices `op` and the operators a[r] of the paper

This file shows that the matrices `op`, defined by recursion, are those of the operators a[r] that
Appendix B of the paper defines on the polynomial ring: the entry `op a r π σ` is the coefficient of
t^π in a[r]·t^σ. -/

public section

namespace ClauseBound.Boson

open Finset

end ClauseBound.Boson

/-! # The matrices are those of the operators of the paper

The ring is ℤ[t₀, t₁, …] (the paper: ℚ[t₁, t₂, …]; t₀ is not used, and all coefficients are
integers). ∇₋ₗ is the multiplication by t_l and ∇ₖ = k·∂/∂t_k. For a tuple of nonzero integers,
`nord` is the product of the ∇ with negative index times the product of the ∇ with positive index,
the latter applied first. The paper defines a[r], for a monomial a with the parts a₁, …, a_q, as the
sum over
all tuples (k₁, …, k_q) of nonzero integers with sum −r of ∏ C(−k_i − 1, a_i − 1) times this
product. For every M that is at least the weights of π and σ, the sum over the tuples with entries
between
−M and M, applied to t^σ, has as its coefficient of t^π the entry `op a r π σ` of the matrix that
was defined by recursion (`op_eq_sum`). -/

namespace ClauseBound.Boson

open Finset MvPolynomial

/-- The ring. -/
abbrev Rg : Type := MvPolynomial ℕ ℤ

/-- The monomial t^μ. -/
@[expose] noncomputable def mon (μ : Multiset ℕ) : Rg := monomial (Multiset.toFinsupp μ) 1

/-- The coefficient of t^μ. -/
@[expose] noncomputable def coef (μ : Multiset ℕ) (f : Rg) : ℤ := f.coeff (Multiset.toFinsupp μ)

/-- ∇ₖ = k·∂/∂t_k for k ≥ 1. -/
@[expose] noncomputable def nabPos (k : ℤ) (f : Rg) : Rg := k • pderiv k.toNat f

/-- ∏_{k_i < 0} ∇_{k_i} · ∏_{k_i > 0} ∇_{k_i}, applied to f. -/
@[expose] noncomputable def nord (ks : List ℤ) (f : Rg) : Rg :=
  ((ks.filter fun k => decide (k < 0)).map fun k => (X (-k).toNat : Rg)).prod * (ks.filter fun k => decide (0 < k)).foldl (fun g k => nabPos k g) f

/-- ∏_i C(−k_i − 1, a_i − 1). -/
@[expose] def wt (a : List ℕ) (ks : List ℤ) : ℤ := (List.zipWith (fun (n : ℕ) (k : ℤ) => Ring.choose (-k - 1) (n - 1)) a ks).prod

/-- The nonzero integers between −M and M. -/
@[expose] def win (M : ℕ) : Finset ℤ := ((Icc 1 M).image fun l : ℕ => -(l : ℤ)) ∪ (Icc 1 M).image fun k : ℕ => (k : ℤ)

/-- The tuples of q nonzero integers between −M and M. -/
@[expose] def tup (M : ℕ) : ℕ → Finset (List ℤ)
  | 0 => {[]}
  | q + 1 => (win M ×ˢ tup M q).image fun p => p.1 :: p.2

namespace Text

theorem mem_win {M : ℕ} {k : ℤ} : k ∈ win M ↔ k ≠ 0 ∧ -(M : ℤ) ≤ k ∧ k ≤ M := by
  simp only [win, mem_union, mem_image, mem_Icc]
  constructor
  · rintro (⟨l, ⟨h1, h2⟩, rfl⟩ | ⟨l, ⟨h1, h2⟩, rfl⟩) <;> omega
  · rintro ⟨h0, h1, h2⟩
    rcases lt_or_gt_of_ne h0 with h | h
    · exact Or.inl ⟨(-k).toNat, by omega, by omega⟩
    · exact Or.inr ⟨k.toNat, by omega, by omega⟩

theorem mem_tup {M : ℕ} : ∀ {q : ℕ} {ks : List ℤ}, ks ∈ tup M q ↔ ks.length = q ∧ ∀ k ∈ ks, k ≠ 0 ∧ -(M : ℤ) ≤ k ∧ k ≤ M
  | 0, ks => by
    simp only [tup, mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact List.length_eq_zero_iff.1 h
  | q + 1, ks => by
    simp only [tup, mem_image, mem_product, Prod.exists]
    constructor
    · rintro ⟨k, ks', ⟨h1, h2⟩, rfl⟩
      obtain ⟨h3, h4⟩ := mem_tup.1 h2
      refine ⟨by simp [h3], fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact mem_win.1 h1
      · exact h4 x hx
    · rintro ⟨h1, h2⟩
      rcases ks with _ | ⟨k, ks'⟩
      · simp at h1
      · exact ⟨k, ks', ⟨mem_win.2 (h2 k (by simp)), mem_tup.2 ⟨by simpa using h1, fun x hx => h2 x (by simp [hx])⟩⟩, rfl⟩

/-- A sum over the window. -/
theorem sum_win (M : ℕ) (G : ℤ → ℤ) : ∑ k ∈ win M, G k = ∑ l ∈ Icc 1 M, G (-(l : ℤ)) + ∑ k ∈ Icc 1 M, G (k : ℤ) := by
  unfold win
  rw [sum_union, sum_image, sum_image]
  · intro x _ y _ h; simpa using h
  · intro x _ y _ h; simpa using h
  · rw [disjoint_left]
    intro x hx hy
    obtain ⟨l, hl, rfl⟩ := mem_image.1 hx
    obtain ⟨k, hk, h⟩ := mem_image.1 hy
    have := (mem_Icc.1 hl).1
    have := (mem_Icc.1 hk).1
    omega

/-- A sum over the tuples of length q + 1. -/
theorem sum_tup_succ (M q : ℕ) (G : List ℤ → ℤ) : ∑ ks ∈ tup M (q + 1), G ks = ∑ k ∈ win M, ∑ ks ∈ tup M q, G (k :: ks) := by
  rw [tup, sum_image, sum_product]
  rintro ⟨k, ks⟩ _ ⟨k', ks'⟩ _ h
  simp only [List.cons.injEq] at h
  exact Prod.ext h.1 h.2

theorem toFinsupp_erase (π : Multiset ℕ) (l : ℕ) : Multiset.toFinsupp (π.erase l) = Multiset.toFinsupp π - Finsupp.single l 1 := by
  ext x
  rw [Finsupp.coe_tsub, Pi.sub_apply, Multiset.toFinsupp_apply, Multiset.toFinsupp_apply]
  by_cases h : x = l
  · subst h
    rw [Multiset.count_erase_self, Finsupp.single_eq_same]
  · rw [Multiset.count_erase_of_ne h, Finsupp.single_eq_of_ne h, Nat.sub_zero]

/-- The coefficients of t_l·f. -/
theorem coef_X_mul (π : Multiset ℕ) (l : ℕ) (f : Rg) : coef π (X l * f) = if l ∈ π then coef (π.erase l) f else 0 := by
  unfold coef
  rw [coeff_X_mul', Multiset.toFinsupp_support, toFinsupp_erase]
  simp only [Multiset.mem_toFinset]

/-- ∇ₖ on a monomial. -/
theorem nabPos_mon (k : ℕ) (σ : Multiset ℕ) : nabPos (k : ℤ) (mon σ) = ((k : ℤ) * σ.count k) • mon (σ.erase k) := by
  unfold nabPos mon
  rw [Int.toNat_natCast, pderiv_monomial, toFinsupp_erase, Multiset.toFinsupp_apply, smul_monomial, smul_monomial]
  simp

theorem coef_mon (π σ : Multiset ℕ) : coef π (mon σ) = if π = σ then 1 else 0 := by
  unfold coef mon
  rw [coeff_monomial]
  by_cases h : π = σ
  · simp [h]
  · rw [if_neg h, if_neg]
    intro h'
    exact h (Multiset.toFinsupp.injective h'.symm)

theorem nabPos_smul (k c : ℤ) (f : Rg) : nabPos k (c • f) = c • nabPos k f := by
  unfold nabPos
  rw [Derivation.map_smul, smul_comm]

theorem foldl_smul (ks : List ℤ) : ∀ (c : ℤ) (f : Rg), ks.foldl (fun g k => nabPos k g) (c • f) = c • ks.foldl (fun g k => nabPos k g) f := by
  induction ks with
  | nil => intro c f; rfl
  | cons k ks ih => intro c f; rw [List.foldl_cons, List.foldl_cons, nabPos_smul, ih]

theorem nord_smul (ks : List ℤ) (c : ℤ) (f : Rg) : nord ks (c • f) = c • nord ks f := by
  unfold nord
  rw [foldl_smul, mul_smul_comm]

theorem nord_nil (f : Rg) : nord [] f = f := by simp [nord]

/-- A negative index: one more multiplication, on the left. -/
theorem nord_cons_neg {k : ℤ} (hk : k < 0) (ks : List ℤ) (f : Rg) : nord (k :: ks) f = X (-k).toNat * nord ks f := by
  unfold nord
  rw [List.filter_cons_of_pos (by simpa using hk), List.filter_cons_of_neg (by simp; omega), List.map_cons, List.prod_cons, mul_assoc]

/-- A positive index: one more differentiation, applied first. -/
theorem nord_cons_pos {k : ℤ} (hk : 0 < k) (ks : List ℤ) (f : Rg) : nord (k :: ks) f = nord ks (nabPos k f) := by
  unfold nord
  rw [List.filter_cons_of_neg (by simp; omega), List.filter_cons_of_pos (by simpa using hk), List.foldl_cons]

theorem sum_erase_le (π : Multiset ℕ) (l : ℕ) : (π.erase l).sum ≤ π.sum := by
  by_cases h : l ∈ π
  · have := Multiset.sum_erase h
    omega
  · rw [Multiset.erase_of_notMem h]

theorem coef_smul (π : Multiset ℕ) (c : ℤ) (f : Rg) : coef π (c • f) = c * coef π f := by
  unfold coef
  rw [coeff_smul, smul_eq_mul]

theorem wt_cons (n : ℕ) (a : List ℕ) (k : ℤ) (ks : List ℤ) : wt (n :: a) (k :: ks) = Ring.choose (-k - 1) (n - 1) * wt a ks := by
  simp [wt]

end Text

open Text

/-- The entry of the matrix defined by recursion is the coefficient of t^π in a[r]·t^σ, with a[r]
the sum over tuples of the paper. -/
theorem op_eq_sum (a : List ℕ) : ∀ (r : ℤ) (π σ : Multiset ℕ) (M : ℕ), 0 ∉ π → 0 ∉ σ → π.sum ≤ M → σ.sum ≤ M →
    op a r π σ = ∑ ks ∈ tup M a.length with ks.sum = -r, wt a ks * coef π (nord ks (mon σ)) := by
  induction a with
  | nil =>
    intro r π σ M _ _ _ _
    show (if r = 0 then one else 0) π σ = _
    rw [sum_filter]
    simp only [List.length_nil, tup, sum_singleton, List.sum_nil, nord_nil, coef_mon]
    by_cases hr : r = 0
    · subst hr
      simp [one, wt]
    · rw [if_neg hr, if_neg (by omega)]
      rfl
  | cons n a ih =>
    intro r π σ M hπ hσ hπM hσM
    show nop n (op a) r π σ = _
    rw [nop_eq_sum n (op a) r π σ (WickPlus.toFinset_subset_Icc hπ hπM) (WickPlus.toFinset_subset_Icc hσ hσM), sum_filter,
      List.length_cons, sum_tup_succ, sum_win]
    congr 1
    · refine sum_congr rfl fun l hl => ?_
      have hl1 := (mem_Icc.1 hl).1
      have hb : bet n l = Ring.choose (-(-(l : ℤ)) - 1) (n - 1) := by rw [bet, if_neg (by omega), neg_neg]
      have hN : (-(-(l : ℤ))).toNat = l := by simp
      unfold cre
      by_cases hlπ : l ∈ π
      · rw [if_pos hlπ, ih (r - l) (π.erase l) σ M (fun h => hπ (Multiset.mem_of_mem_erase h)) hσ (le_trans (sum_erase_le π l) hπM) hσM,
          sum_filter, mul_sum]
        refine sum_congr rfl fun ks _ => ?_
        have hc : (-(l : ℤ) :: ks).sum = -r ↔ ks.sum = -(r - l) := by
          rw [List.sum_cons]; constructor <;> intro h <;> omega
        rw [if_congr hc rfl rfl, nord_cons_neg (by omega), coef_X_mul, hN, if_pos hlπ, wt_cons, hb]
        split_ifs
        · ring
        · ring
      · rw [if_neg hlπ, mul_zero]
        symm
        refine sum_eq_zero fun ks _ => ?_
        rw [nord_cons_neg (by omega), coef_X_mul, hN, if_neg hlπ, mul_zero, ite_self]
    · refine sum_congr rfl fun k hk => ?_
      have hk1 := (mem_Icc.1 hk).1
      have hb : bet n (-(k : ℤ)) = Ring.choose (-(k : ℤ) - 1) (n - 1) := by rw [bet, if_neg (by omega)]
      unfold ann
      rw [ih (r + k) π (σ.erase k) M hπ (fun h => hσ (Multiset.mem_of_mem_erase h)) hπM (le_trans (sum_erase_le σ k) hσM), sum_filter,
        mul_sum, mul_sum]
      refine sum_congr rfl fun ks _ => ?_
      have hc : ((k : ℤ) :: ks).sum = -r ↔ ks.sum = -(r + k) := by
        rw [List.sum_cons]; constructor <;> intro h <;> omega
      rw [if_congr hc rfl rfl, nord_cons_pos (by omega), nabPos_mon, nord_smul, coef_smul, wt_cons, hb]
      split_ifs
      · ring
      · ring

end ClauseBound.Boson
